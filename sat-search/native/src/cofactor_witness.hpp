#pragma once
// Constructive AIG upper bounds by cofactor two-signal decomposition (native port of ChatGPT's
// cofactor_witness bundle, generalized from the fixed four-input library to any target on 3..6 inputs
// with an optional care set).
//
// Identity used everywhere: if (f|x=0, f|x=1) is constant on every fiber of (a(Y), b(Y)), then
// f(x, Y) = d(a(Y), b(Y), x) for a three-input function d, so C(f) <= M(a, b) + C_partial(d).
//
// Levels (m = number of variables the current subfunction may depend on):
//   m = 3  exact: minimum-cost completion of the partial three-input table.
//   m = 4  the bundle's search: for every split variable, Shannon with separate cofactors, the exact joint
//          recipe of both cofactors, and every exact three-input pair (a, b) whose fibers respect the
//          cofactors on the care rows ("cut" mode). Upstream pair costs are exact (BFS over normalized
//          column sets); the decoder is the minimum-cost completion of the induced partial table.
//   m >= 5 recursive and heuristic: (a, b) in {(g0, g1)} and, on fully specified cofactors, also
//          {(g0, g0^g1), (g1, g0^g1)}; each signal is solved at level m-1.
// Only upper bounds come out of this file. The builder hashes columns, so the built count never exceeds the
// planned estimate. Every chain is pruned to the output cone and re-simulated row by row.
//
// Literal convention (matches percy_run --upper-witness): literal 2w+p, wire 0 constant zero, wires 1..n the
// inputs (row r has x_i = bit i of r), wire n+1+j gate j = AND of its two literals.
#include <algorithm>
#include <array>
#include <bit>
#include <climits>
#include <cstdint>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

namespace cofactor {

using u64 = std::uint64_t;
inline int norm8(int x) { return std::min(x, 255 ^ x); }
inline constexpr std::array<int, 3> kInputs8{170, 204, 240};  // x0, x1, x2 on eight rows

struct Op { int z, a, b; bool inv; };  // signed 8-bit operands a, b; norm8(a & b) == z

// Exact single and joint costs of normalized three-input columns (pair_recipes.cpp, in memory).
class PairTable {
 public:
  struct Pair { int cost, a, b; u64 code; std::array<int, 4> fibers; };
  std::array<std::array<std::uint8_t, 128>, 128> cost{};
  std::array<std::array<u64, 128>, 128> code{};
  std::vector<Pair> pairs;                               // attained pairs a <= b, sorted by (cost, a, b)
  std::vector<std::pair<std::uint8_t, std::uint8_t>> part;  // [pos*256 + neg] -> (cost, completion)
  std::uint64_t transitions = 0;

  explicit PairTable(int depth = 7) {
    if (depth < 6 || depth > 9) throw std::invalid_argument("pair table depth must be in 6..9");
    for (auto& row : cost) row.fill(255);
    auto record = [&](int a, int b, u64 c, int k) {
      if (cost[a][b] > k) { cost[a][b] = cost[b][a] = std::uint8_t(k); code[a][b] = code[b][a] = c; }
    };
    for (int a : {0, 15, 51, 85}) for (int b : {0, 15, 51, 85}) record(a, b, 0, 0);
    Set init; for (int x : {15, 51, 85}) init.put(x);
    std::unordered_map<Set, u64, SetHash> layer{{init, 0}};
    std::vector<int> v, zs;
    for (int k = 1; k <= depth; ++k) {
      std::unordered_map<Set, u64, SetHash> next;
      for (auto& [st, cd] : layer) {
        vals(st, v);
        Set cand;
        for (std::size_t i = 0; i < v.size(); ++i)
          for (std::size_t j = i + 1; j < v.size(); ++j)
            for (int p : {0, 255}) for (int q : {0, 255}) cand.put(norm8((v[i] ^ p) & (v[j] ^ q)));
        cand.lo &= ~st.lo & ~1ull; cand.hi &= ~st.hi;
        vals(cand, zs);
        for (int z : zs) {
          ++transitions;
          u64 nc = cd | (u64(z) << (7 * (k - 1)));
          for (int a : v) record(z, a, nc, k);
          record(z, 0, nc, k); record(z, z, nc, k);
          if (k < depth) { Set ns = st; ns.put(z); next.emplace(ns, nc); }
        }
      }
      layer = std::move(next);
    }
    for (int a = 0; a < 128; ++a) if (cost[a][a] == 255) throw std::logic_error("single cost missing");
    for (int a = 0; a < 128; ++a)
      for (int b = a; b < 128; ++b) {
        if (cost[a][b] == 255) continue;
        Pair p{cost[a][b], a, b, code[a][b], {0, 0, 0, 0}};
        for (int r = 0; r < 8; ++r) p.fibers[((a >> r) & 1) | (((b >> r) & 1) << 1)] |= 1 << r;
        pairs.push_back(p);
      }
    std::stable_sort(pairs.begin(), pairs.end(), [](const Pair& x, const Pair& y) {
      return std::tie(x.cost, x.a, x.b) < std::tie(y.cost, y.a, y.b);
    });
    part.assign(65536, {std::uint8_t(255), std::uint8_t(0)});
    for (int f = 0; f < 256; ++f) {
      int c = single(f);
      for (int care = 0; care < 256; ++care) {
        auto& e = part[(f & care) * 256 + ((f ^ 255) & care)];
        if (c < e.first) e = {std::uint8_t(c), std::uint8_t(f)};
      }
    }
  }
  int single(int f) const { return cost[norm8(f)][norm8(f)]; }
  const std::pair<std::uint8_t, std::uint8_t>& completion(int f, int care) const {
    return part[(f & care) * 256 + ((~f) & care & 255)];
  }
  // Signed operations of a recipe, recovered from its column sequence (as cofactor_witness.ops).
  const std::vector<Op>& ops(int k, u64 c) const {
    auto key = std::make_pair(k, c);
    auto it = ops_cache_.find(key);
    if (it != ops_cache_.end()) return it->second;
    std::vector<int> avail{0, 85, 51, 15};
    std::vector<Op> out;
    for (int i = 0; i < k; ++i) {
      int z = int((c >> (7 * i)) & 127);
      bool found = false;
      for (std::size_t x = 0; x < avail.size() && !found; ++x)
        for (std::size_t y = x + 1; y < avail.size() && !found; ++y)
          for (int p : {0, 255}) {
            for (int q : {0, 255}) {
              int A = avail[x] ^ p, B = avail[y] ^ q;
              if (norm8(A & B) == z) { out.push_back({z, A, B, (A & B) != z}); found = true; break; }
            }
            if (found) break;
          }
      if (!found || std::find(avail.begin(), avail.end(), z) != avail.end())
        throw std::logic_error("unreplayable recipe");
      avail.push_back(z);
    }
    return ops_cache_.emplace(key, std::move(out)).first->second;
  }

 private:
  struct Set {
    u64 lo = 0, hi = 0;
    bool operator==(const Set&) const = default;
    void put(int x) { if (x < 64) lo |= 1ull << x; else hi |= 1ull << (x - 64); }
  };
  struct SetHash {
    std::size_t operator()(const Set& s) const {
      return s.lo * 0x9e3779b97f4a7c15ull ^ (s.hi + 0x85ebca6bull + (s.lo << 6) + (s.lo >> 2));
    }
  };
  static void vals(Set s, std::vector<int>& v) {
    v.clear();
    while (s.lo) { v.push_back(std::countr_zero(s.lo)); s.lo &= s.lo - 1; }
    while (s.hi) { v.push_back(64 + std::countr_zero(s.hi)); s.hi &= s.hi - 1; }
  }
  mutable std::map<std::pair<int, u64>, std::vector<Op>> ops_cache_;
};

inline u64 full_mask(int n) { return n == 6 ? ~0ull : (1ull << (1 << n)) - 1; }
inline u64 var_column(int n, int i) {
  u64 c = 0;
  for (int r = 0; r < (1 << n); ++r) if ((r >> i) & 1) c |= 1ull << r;
  return c;
}

// Column-hashed AIG builder: a gate is added only when its column is new.
class Builder {
 public:
  explicit Builder(int n) : n_(n), full_(full_mask(n)) {
    lit_[0] = 0; lit_[full_] = 1;
    for (int i = 0; i < n; ++i) { u64 c = var_column(n, i); lit_[c] = 2 * (i + 1); lit_[c ^ full_] = 2 * (i + 1) + 1; }
  }
  u64 gate(u64 a, u64 b) {
    u64 z = a & b;
    if (lit_.count(z)) return z;
    int la = lit_.at(a), lb = lit_.at(b);
    gates_.push_back({la, lb});
    int w = n_ + int(gates_.size());
    lit_[z] = 2 * w; lit_[z ^ full_] = 2 * w + 1;
    return z;
  }
  // Replay a three-input recipe on full columns in[0..2] (for 8-bit inputs 170, 204, 240).
  std::array<u64, 256> replay(const PairTable& T, int k, u64 code, const std::array<u64, 3>& in) {
    std::array<u64, 256> val{};
    val[0] = 0; val[255] = full_;
    for (int t = 0; t < 3; ++t) { val[kInputs8[t]] = in[t]; val[kInputs8[t] ^ 255] = in[t] ^ full_; }
    for (const Op& op : T.ops(k, code)) {
      u64 r = gate(val[op.a], val[op.b]);
      if (op.inv) r ^= full_;
      val[op.z] = r; val[op.z ^ 255] = r ^ full_;
    }
    return val;
  }
  // Output cone of column f, renumbered topologically.
  std::pair<std::vector<std::array<int, 2>>, int> extract(u64 f) const {
    int out = lit_.at(f);
    std::vector<char> need(gates_.size(), 0);
    auto mark = [&](int l) { int w = l / 2 - n_ - 1; if (w >= 0) need[w] = 1; };
    mark(out);
    for (int j = int(gates_.size()) - 1; j >= 0; --j) if (need[j]) { mark(gates_[j][0]); mark(gates_[j][1]); }
    std::vector<int> wire(n_ + 1 + gates_.size());
    for (int w = 0; w <= n_; ++w) wire[w] = w;
    std::vector<std::array<int, 2>> g;
    auto ren = [&](int l) { return 2 * wire[l / 2] + (l & 1); };
    for (std::size_t j = 0; j < gates_.size(); ++j)
      if (need[j]) { g.push_back({ren(gates_[j][0]), ren(gates_[j][1])}); wire[n_ + 1 + j] = n_ + int(g.size()); }
    return {g, ren(out)};
  }

 private:
  int n_;
  u64 full_;
  std::unordered_map<u64, int> lit_;
  std::vector<std::array<int, 2>> gates_;
};

// Independent row-by-row evaluation of an indexed chain.
inline u64 simulate(int n, const std::vector<std::array<int, 2>>& gates, int out) {
  u64 tt = 0;
  std::vector<int> v;
  for (int r = 0; r < (1 << n); ++r) {
    v.assign(1, 0);
    for (int i = 0; i < n; ++i) v.push_back((r >> i) & 1);
    for (auto [a, b] : gates) {
      if (a / 2 >= int(v.size()) || b / 2 >= int(v.size())) throw std::logic_error("forward reference");
      v.push_back((v[a / 2] ^ (a & 1)) & (v[b / 2] ^ (b & 1)));
    }
    if (out / 2 >= int(v.size())) throw std::logic_error("bad output");
    tt |= u64(v[out / 2] ^ (out & 1)) << r;
  }
  return tt;
}

struct Plan {
  int est = INT_MAX, m = 0, split = -1;
  u64 col = 0;                        // completed function the plan builds
  std::array<int, 3> Y{};             // m <= 4: the three upstream variables (m == 3: the variables)
  int a = 0, b = 0, k = 0, d = 0;     // m == 4: normalized 8-bit signals, joint recipe, decoder
  u64 code = 0;
  bool separate = false;
  std::shared_ptr<const Plan> pa, pb; // m >= 5
};

class Synth {
 public:
  Synth(const PairTable& T, int n) : T_(T), n_(n), full_(full_mask(n)) {
    if (n < 3 || n > 6) throw std::invalid_argument("n must be in 3..6");
    for (int i = 0; i < n; ++i) X_[i] = var_column(n, i);
  }
  std::shared_ptr<const Plan> solve(u64 f, u64 care) { return solve(f & full_, care & full_, (1 << n_) - 1); }
  u64 build(const Plan& p, Builder& B) const {
    u64 r;
    if (p.m == 3) {
      int d = p.d;
      r = B.replay(T_, T_.cost[norm8(d)][norm8(d)], T_.code[norm8(d)][norm8(d)], {X_[p.Y[0]], X_[p.Y[1]], X_[p.Y[2]]})[d];
    } else {
      u64 A, H;
      if (p.m == 4) {
        std::array<u64, 3> in{X_[p.Y[0]], X_[p.Y[1]], X_[p.Y[2]]};
        if (p.separate) {
          A = B.replay(T_, T_.cost[p.a][p.a], T_.code[p.a][p.a], in)[p.a];
          H = B.replay(T_, T_.cost[p.b][p.b], T_.code[p.b][p.b], in)[p.b];
        } else {
          auto val = B.replay(T_, p.k, p.code, in);
          A = val[p.a]; H = val[p.b];
        }
      } else {
        A = build(*p.pa, B); H = build(*p.pb, B);
      }
      int nd = norm8(p.d);
      r = B.replay(T_, T_.cost[nd][nd], T_.code[nd][nd], {A, H, X_[p.split]})[p.d];
    }
    if (r != p.col) throw std::logic_error("built column differs from plan");
    return r;
  }

 private:
  struct Key {
    u64 f, care; int W;
    bool operator==(const Key&) const = default;
  };
  struct KeyHash {
    std::size_t operator()(const Key& k) const {
      return k.f * 0x9e3779b97f4a7c15ull ^ (k.care + 0x85ebca6bull + (k.f << 6)) ^ (u64(k.W) << 57);
    }
  };
  u64 cof(u64 g, int i, int v) const {
    int s = 1 << i;
    if (v == 0) { u64 x = g & ~X_[i]; return x | (x << s); }
    u64 x = g & X_[i]; return x | (x >> s);
  }
  int proj(u64 g, const std::array<int, 3>& Y) const {
    int c = 0;
    for (int t = 0; t < 8; ++t) {
      int r = 0;
      for (int j = 0; j < 3; ++j) r |= ((t >> j) & 1) << Y[j];
      c |= int((g >> r) & 1) << t;
    }
    return c;
  }
  // Column of d(a(Y), b(Y), x_split) for 8-bit a, b over Y and 8-bit d over (a, b, x).
  u64 compose4(int a, int b, int d, const std::array<int, 3>& Y, int split) const {
    u64 c = 0;
    for (int r = 0; r < (1 << n_); ++r) {
      int t = ((r >> Y[0]) & 1) | (((r >> Y[1]) & 1) << 1) | (((r >> Y[2]) & 1) << 2);
      int idx = ((a >> t) & 1) | (((b >> t) & 1) << 1) | (((r >> split) & 1) << 2);
      c |= u64((d >> idx) & 1) << r;
    }
    return c;
  }
  // Partial decoder table induced by eight-row cofactors on fibers; -1 when some fiber is inconsistent.
  int decoder8(int f0, int c0, int f1, int c1, const std::array<int, 4>& fibers) const {
    int p = 0, n = 0;
    for (int j = 0; j < 4; ++j)
      for (int v = 0; v < 2; ++v) {
        int m = fibers[j] & (v ? c1 : c0);
        if (!m) continue;
        int x = (v ? f1 : f0) & m;
        if (x && x != m) return -1;
        (x ? p : n) |= 1 << (j + 4 * v);
      }
    return p * 256 + n;
  }
  int decoder_full(u64 f, u64 care, u64 A, u64 H, int split) const {
    int p = 0, n = 0;
    for (int r = 0; r < (1 << n_); ++r) {
      if (!((care >> r) & 1)) continue;
      int idx = int((A >> r) & 1) | int(((H >> r) & 1) << 1) | (((r >> split) & 1) << 2);
      ((f >> r) & 1 ? p : n) |= 1 << idx;
    }
    if (p & n) return -1;
    return p * 256 + n;
  }

  std::shared_ptr<const Plan> solve(u64 f, u64 care, int W) {
    Key key{f & care, care, W};
    if (auto it = memo_.find(key); it != memo_.end()) return it->second;
    auto best = std::make_shared<Plan>();
    int m = std::popcount(unsigned(W));
    std::vector<int> vars;
    for (int i = 0; i < n_; ++i) if ((W >> i) & 1) vars.push_back(i);
    if (m <= 3) {
      while (vars.size() < 3) vars.push_back(vars.empty() ? 0 : vars.back() == n_ - 1 ? 0 : vars.back() + 1);
      std::array<int, 3> Y{vars[0], vars[1], vars[2]};
      auto [c, d] = T_.completion(proj(f, Y), proj(care, Y));
      best->m = 3; best->Y = Y; best->d = d; best->est = c;
      best->col = compose3(d, Y);
    } else if (m == 4) {
      solve4(f, care, vars, *best);
    } else {
      for (int i : vars) {
        u64 g0 = cof(f, i, 0), g1 = cof(f, i, 1), c0 = cof(care, i, 0), c1 = cof(care, i, 1);
        std::vector<std::array<u64, 4>> cands{{g0, c0, g1, c1}};
        if (c0 == full_ && c1 == full_) {
          cands.push_back({g0, full_, g0 ^ g1, full_});
          cands.push_back({g1, full_, g0 ^ g1, full_});
        }
        for (auto& [ta, ca, tb, cb] : cands) {
          auto pa = solve(ta, ca, W & ~(1 << i)), pb = solve(tb, cb, W & ~(1 << i));
          int dk = decoder_full(f, care, pa->col, pb->col, i);
          if (dk < 0) throw std::logic_error("decoder inconsistent");
          auto [dc, d] = T_.part[dk];
          int est = pa->est + (pa == pb ? 0 : pb->est) + dc;
          if (est >= best->est) continue;
          best->est = est; best->m = m; best->split = i; best->pa = pa; best->pb = pb; best->d = d;
        }
      }
      best->col = compose_full(best->pa->col, best->pb->col, best->d, best->split);
    }
    memo_.emplace(key, best);
    return best;
  }
  u64 compose3(int d, const std::array<int, 3>& Y) const {
    u64 c = 0;
    for (int r = 0; r < (1 << n_); ++r) {
      int t = ((r >> Y[0]) & 1) | (((r >> Y[1]) & 1) << 1) | (((r >> Y[2]) & 1) << 2);
      c |= u64((d >> t) & 1) << r;
    }
    return c;
  }
  u64 compose_full(u64 A, u64 H, int d, int split) const {
    u64 c = 0;
    for (int r = 0; r < (1 << n_); ++r) {
      int idx = int((A >> r) & 1) | int(((H >> r) & 1) << 1) | (((r >> split) & 1) << 2);
      c |= u64((d >> idx) & 1) << r;
    }
    return c;
  }
  void solve4(u64 f, u64 care, const std::vector<int>& vars, Plan& best) const {
    best.m = 4;
    auto consider = [&](int i, const std::array<int, 3>& Y, int a, int b, int k, u64 code, int dk, bool sep) {
      auto [dc, d] = T_.part[dk];
      if (k + dc >= best.est) return;
      best.est = k + dc; best.split = i; best.Y = Y; best.a = a; best.b = b; best.k = k; best.code = code;
      best.d = d; best.separate = sep;
    };
    for (int i : vars) {
      std::array<int, 3> Y{};
      int t = 0;
      for (int j : vars) if (j != i) Y[t++] = j;
      int f0 = proj(cof(f, i, 0), Y), f1 = proj(cof(f, i, 1), Y);
      int c0 = proj(cof(care, i, 0), Y), c1 = proj(cof(care, i, 1), Y);
      int a = norm8(T_.completion(f0, c0).second), b = norm8(T_.completion(f1, c1).second);
      std::array<int, 4> fib{0, 0, 0, 0};
      for (int r = 0; r < 8; ++r) fib[((a >> r) & 1) | (((b >> r) & 1) << 1)] |= 1 << r;
      int dk = decoder8(f0, c0, f1, c1, fib);
      if (dk < 0) throw std::logic_error("separate decoder inconsistent");
      consider(i, Y, a, b, T_.cost[a][a] + (a != b ? T_.cost[b][b] : 0), 0, dk, true);
      if (T_.cost[a][b] != 255) consider(i, Y, a, b, T_.cost[a][b], T_.code[a][b], dk, false);
      for (const auto& P : T_.pairs) {
        if (P.cost >= best.est) break;
        int pk = decoder8(f0, c0, f1, c1, P.fibers);
        if (pk >= 0) consider(i, Y, P.a, P.b, P.cost, P.code, pk, false);
      }
    }
    best.col = compose4(best.a, best.b, best.d, best.Y, best.split);
  }

  const PairTable& T_;
  int n_;
  u64 full_;
  std::array<u64, 6> X_{};
  std::unordered_map<Key, std::shared_ptr<const Plan>, KeyHash> memo_;
};

struct Witness {
  int n = 0, estimate = 0;
  u64 target = 0, care = 0;
  std::vector<std::array<int, 2>> gates;
  int output = 0;
  std::string spec() const {
    std::string s;
    for (std::size_t j = 0; j < gates.size(); ++j)
      s += (j ? ";" : "") + std::to_string(gates[j][0]) + "," + std::to_string(gates[j][1]);
    return s + "|" + std::to_string(output);
  }
};

// Synthesize, build, prune and independently verify on the care set.
inline Witness synthesize(const PairTable& T, int n, u64 f, u64 care) {
  Synth S(T, n);
  auto plan = S.solve(f, care);
  Builder B(n);
  u64 col = S.build(*plan, B);
  auto [gates, out] = B.extract(col);
  u64 full = full_mask(n);
  if (((simulate(n, gates, out) ^ f) & care & full) != 0) throw std::logic_error("witness fails on the care set");
  if (int(gates.size()) > plan->est) throw std::logic_error("built count exceeds the plan estimate");
  return {n, plan->est, f & full, care & full, gates, out};
}

}  // namespace cofactor
