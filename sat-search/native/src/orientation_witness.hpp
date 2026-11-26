// Target-directed encoder orientations for constructive AIG upper bounds, n <= 8.
//
// Port of the research prototype target_directed_encoder_research/orientation.py (and the base.py helpers it
// uses). For a split of the inputs into X (one or two decoder inputs) and Y, the residual labels are the X-cofactor
// patterns of each Y assignment. A first encoder a (from a bank of cheap Y-signals) and an optional context
// variable R in Y partition the Y assignments into buckets (R, a). A bucket with more than two distinct labels
// rejects a; a bucket with exactly two labels forces opposite second-encoder values b on its two classes; a
// one-class bucket leaves b free. Enumerating one polarity per two-class bucket, modulo global complement, gives
// every feasible partial obligation for b (exhaustively checked in the bundle's verify.py, and here by
// --selftest). b is then built target-directed on that partial table (partial Shannon recursion), optionally
// with a as an extra input ("reuse"); the decoder over (X, R, a, b) is completed on its reachable rows and the
// candidate is scored by the live shared gate count of the final output cone. Partial synthesis is heuristic:
// every number this produces is a verified upper bound, never a minimum.
//
// Literal convention (shared with cofactor_witness.hpp and percy_run --upper-witness): 0/1 constants, input i is
// 2(i+1), gate j is 2(n+1+j), odd literals are complemented; truth-table row r assigns input i bit i of r.
#pragma once

#include <algorithm>
#include <array>
#include <bit>
#include <climits>
#include <functional>
#include <cstdint>
#include <map>
#include <optional>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

#include "feature_quotient.hpp"

namespace orient {

using u64 = std::uint64_t;

// Truth table on up to 8 variables (256 rows); bits beyond the active row count are kept zero.
struct TT {
  std::array<u64, 4> w{};
  bool operator==(const TT&) const = default;
  auto operator<=>(const TT&) const = default;
  TT operator&(const TT& o) const { TT r; for (int i = 0; i < 4; ++i) r.w[i] = w[i] & o.w[i]; return r; }
  TT operator|(const TT& o) const { TT r; for (int i = 0; i < 4; ++i) r.w[i] = w[i] | o.w[i]; return r; }
  TT operator^(const TT& o) const { TT r; for (int i = 0; i < 4; ++i) r.w[i] = w[i] ^ o.w[i]; return r; }
  TT operator~() const { TT r; for (int i = 0; i < 4; ++i) r.w[i] = ~w[i]; return r; }
  bool any() const { return (w[0] | w[1] | w[2] | w[3]) != 0; }
  bool get(int r) const { return (w[r >> 6] >> (r & 63)) & 1; }
  void set(int r) { w[r >> 6] |= 1ull << (r & 63); }
  int count() const { return std::popcount(w[0]) + std::popcount(w[1]) + std::popcount(w[2]) + std::popcount(w[3]); }
  TT shl(int s) const {  // s is a multiple of a power of two <= 128; generic bit shift
    TT r;
    for (int i = 255; i >= s; --i) if (get(i - s)) r.set(i);
    return r;
  }
};

inline TT full_tt(int k) {
  TT r;
  int rows = 1 << k;
  for (int i = 0; i < 4; ++i) {
    int lo = i * 64;
    if (rows >= lo + 64) r.w[i] = ~0ull;
    else if (rows > lo) r.w[i] = (1ull << (rows - lo)) - 1;
  }
  return r;
}
inline TT col_tt(int k, int i) {
  TT r;
  for (int row = 0; row < (1 << k); ++row) if ((row >> i) & 1) r.set(row);
  return r;
}
// Cofactor x_i = b of a table over k variables, as a table over the remaining k-1 variables (order kept).
inline TT cut(const TT& t, int k, int i, int b) {
  TT r;
  int low = (1 << i) - 1;
  for (int row = 0; row < (1 << (k - 1)); ++row) {
    int src = (row & low) | (b << i) | ((row & ~low) << 1);
    if (t.get(src)) r.set(row);
  }
  return r;
}
inline std::string hex_tt(const TT& t, int n) {
  int digits = std::max(1, (1 << n) / 4);
  std::string s;
  for (int d = digits - 1; d >= 0; --d) {
    int v = 0;
    for (int b = 0; b < 4; ++b) if (d * 4 + b < (1 << n) && t.get(d * 4 + b)) v |= 1 << b;
    s += "0123456789abcdef"[v];
  }
  return s;
}
inline TT parse_hex(const std::string& h0, int n) {
  std::string h = h0;
  if (h.size() > 1 && h[0] == '0' && (h[1] == 'x' || h[1] == 'X')) h = h.substr(2);
  TT t;
  int bit = 0;
  for (int i = int(h.size()) - 1; i >= 0; --i, bit += 4) {
    char c = h[i];
    int v = c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1;
    if (v < 0) throw std::invalid_argument("bad hex truth table");
    for (int b = 0; b < 4; ++b)
      if ((v >> b) & 1) {
        if (bit + b >= (1 << n)) throw std::invalid_argument("truth table wider than 2^n bits");
        t.set(bit + b);
      }
  }
  return t;
}

struct Witness {
  int n = 0;
  std::vector<std::array<int, 2>> gates;
  int out = 0;
  std::string spec() const {
    std::string s;
    for (std::size_t j = 0; j < gates.size(); ++j)
      s += (j ? ";" : "") + std::to_string(gates[j][0]) + "," + std::to_string(gates[j][1]);
    return s + "|" + std::to_string(out);
  }
};

inline Witness parse_spec(int n, const std::string& spec) {
  Witness w;
  w.n = n;
  auto bar = spec.find('|');
  if (bar == std::string::npos) throw std::invalid_argument("spec needs '|out'");
  std::string body = spec.substr(0, bar);
  w.out = std::stoi(spec.substr(bar + 1));
  std::size_t pos = 0;
  while (pos < body.size()) {
    auto semi = body.find(';', pos);
    std::string g = body.substr(pos, semi == std::string::npos ? std::string::npos : semi - pos);
    auto comma = g.find(',');
    if (comma == std::string::npos) throw std::invalid_argument("bad gate in spec");
    w.gates.push_back({std::stoi(g.substr(0, comma)), std::stoi(g.substr(comma + 1))});
    if (semi == std::string::npos) break;
    pos = semi + 1;
  }
  return w;
}

// Independent row-by-row evaluation; no AIG helpers involved.
inline TT simulate(const Witness& w) {
  TT t;
  std::vector<int> v;
  for (int r = 0; r < (1 << w.n); ++r) {
    v.assign(1, 0);
    for (int i = 0; i < w.n; ++i) v.push_back((r >> i) & 1);
    auto read = [&](int l) {
      if (l < 0 || l / 2 >= int(v.size())) throw std::logic_error("forward or bad reference");
      return v[l / 2] ^ (l & 1);
    };
    for (auto [a, b] : w.gates) v.push_back(read(a) & read(b));
    if (read(w.out)) t.set(r);
  }
  return t;
}

// Structurally hashed AIG with live cone-union cost.
class AIG {
 public:
  explicit AIG(int n) : n_(n), full_(full_tt(n)) {
    ops_.assign(n + 1, {-1, -1});
    tt_.push_back(TT{});
    for (int i = 0; i < n; ++i) tt_.push_back(col_tt(n, i));
  }
  int n() const { return n_; }
  int lit(int i) const { return 2 * (i + 1); }
  TT truth(int a) const { return (a & 1) ? tt_[a / 2] ^ full_ : tt_[a / 2]; }
  int AND(int a, int b) {
    if (a == 0 || b == 0 || a == (b ^ 1)) return 0;
    if (a == 1 || a == b) return b;
    if (b == 1) return a;
    if (a > b) std::swap(a, b);
    u64 key = (u64(unsigned(a)) << 32) | unsigned(b);
    auto it = hash_.find(key);
    if (it != hash_.end()) return it->second;
    int j = int(ops_.size());
    ops_.push_back({a, b});
    tt_.push_back(truth(a) & truth(b));
    stamp_.push_back(0);
    hash_.emplace(key, 2 * j);
    return 2 * j;
  }
  int OR(int a, int b) { return AND(a ^ 1, b ^ 1) ^ 1; }
  int mux(int x, int a, int b) {  // x ? b : a
    if (a == b) return a;
    return OR(AND(x ^ 1, a), AND(x, b));
  }
  // Number of distinct gates in the union of the cones of the given literals.
  int cost(std::initializer_list<int> lits) {
    ++epoch_;
    int c = 0;
    for (int l : lits) c += mark(l / 2);
    return c;
  }
  int cost1(int a) { return cost({a}); }
  // Partial-function synthesis by Shannon/merge recursion (base.py AIG.solve), memoized per (p, care, vars).
  int solve(TT p, const TT& c, const std::vector<int>& vs) {
    p = p & c;
    int k = int(vs.size());
    if (!p.any()) return 0;
    if (p == c) return 1;
    if (p.get(0)) return solve(c ^ p, c, vs) ^ 1;
    Key key{p, c, vs};
    if (auto it = cache_.find(key); it != cache_.end()) return it->second;
    for (int i = 0; i < k; ++i) {
      TT a = col_tt(k, i) & c;
      if (p == a) return vs[i];
      if (p == (c ^ a)) return vs[i] ^ 1;
    }
    int best = -1, bc = INT_MAX;
    for (int i = 0; i < k; ++i) {
      TT p0 = cut(p, k, i, 0), p1 = cut(p, k, i, 1), c0 = cut(c, k, i, 0), c1 = cut(c, k, i, 1);
      std::vector<int> w = vs;
      w.erase(w.begin() + i);
      if (!((p0 ^ p1) & c0 & c1).any()) {
        int q = solve(p0 | p1, c0 | c1, w);
        int kq = cost1(q);
        if (kq < bc) { best = q; bc = kq; }
      }
      int a = solve(p0, c0, w), b = solve(p1, c1, w);
      int q = mux(vs[i], a, b);
      int kq = cost1(q);
      if (kq < bc) { best = q; bc = kq; }
    }
    cache_.emplace(std::move(key), best);
    return best;
  }
  // Gates of the cone of each node, ascending (topological).
  std::vector<int> cone(int a) {
    ++epoch_;
    std::vector<int> out;
    collect(a / 2, out);
    std::sort(out.begin(), out.end());
    return out;
  }
  Witness export_cone(int out) {
    Witness w;
    w.n = n_;
    std::vector<int> c = cone(out);
    std::unordered_map<int, int> id;
    for (int i = 0; i <= n_; ++i) id[i] = i;
    for (int j : c) {
      auto [a, b] = ops_[j];
      id[j] = n_ + 1 + int(w.gates.size());
      w.gates.push_back({2 * id.at(a / 2) + (a & 1), 2 * id.at(b / 2) + (b & 1)});
    }
    w.out = 2 * id.at(out / 2) + (out & 1);
    return w;
  }
  // Import an indexed chain (re-hashed); returns the output literal. `inputs` maps chain input i to a literal of
  // this AIG (default: input i itself).
  int import(const Witness& w, const std::vector<int>& inputs = {}) {
    std::vector<int> v(w.n + 1);
    v[0] = 0;
    for (int i = 0; i < w.n; ++i) v[i + 1] = inputs.empty() ? 2 * (i + 1) : inputs.at(i);
    if (inputs.empty() && w.n != n_) throw std::invalid_argument("imported witness has a different input count");
    auto read = [&](int l) {
      if (l < 0 || l / 2 >= int(v.size())) throw std::invalid_argument("bad imported witness");
      return v[l / 2] ^ (l & 1);
    };
    for (auto [a, b] : w.gates) v.push_back(AND(read(a), read(b)));
    return read(w.out);
  }
  int import_lits(const Witness& w, const std::vector<int>& inputs) { return import(w, inputs); }

 private:
  struct Key {
    TT p, c;
    std::vector<int> vs;
    bool operator==(const Key&) const = default;
  };
  struct KeyHash {
    std::size_t operator()(const Key& k) const {
      u64 h = 0x9e3779b97f4a7c15ull;
      for (u64 x : k.p.w) h = (h ^ x) * 0x100000001b3ull;
      for (u64 x : k.c.w) h = (h ^ (x + 0x51ed27ull)) * 0x100000001b3ull;
      for (int v : k.vs) h = (h ^ u64(v + 7)) * 0x100000001b3ull;
      return std::size_t(h ^ (h >> 29));
    }
  };
  int mark(int j) {
    if (j <= n_) return 0;
    std::size_t s = std::size_t(j - n_ - 1);
    if (stamp_[s] == epoch_) return 0;
    stamp_[s] = epoch_;
    return 1 + mark(ops_[j].first / 2) + mark(ops_[j].second / 2);
  }
  void collect(int j, std::vector<int>& out) {
    if (j <= n_) return;
    std::size_t s = std::size_t(j - n_ - 1);
    if (stamp_[s] == epoch_) return;
    stamp_[s] = epoch_;
    out.push_back(j);
    collect(ops_[j].first / 2, out);
    collect(ops_[j].second / 2, out);
  }

  int n_;
  TT full_;
  std::vector<std::pair<int, int>> ops_;
  std::vector<TT> tt_;
  std::vector<unsigned> stamp_;
  unsigned epoch_ = 0;
  std::unordered_map<u64, int> hash_;
  std::unordered_map<Key, int, KeyHash> cache_;
};

// Residual labels: labels[y] has bit i = t at the row combining X-assignment i and Y-assignment y.
inline std::vector<unsigned> residual(const TT& t, const std::vector<int>& X, const std::vector<int>& Y) {
  auto embed = [](int a, const std::vector<int>& inds) {
    int r = 0;
    for (std::size_t i = 0; i < inds.size(); ++i) r |= ((a >> i) & 1) << inds[i];
    return r;
  };
  std::vector<unsigned> out(std::size_t(1) << Y.size(), 0);
  for (int y = 0; y < (1 << Y.size()); ++y)
    for (int i = 0; i < (1 << X.size()); ++i)
      if (t.get(embed(i, X) | embed(y, Y))) out[y] |= 1u << i;
  return out;
}

// Partial obligations for b (orientation.py `obligations`). Returns nullopt when some (R, a) bucket holds more
// than two distinct labels; otherwise every orientation of the two-class buckets with the first bucket's first
// class fixed to b = 1 (one representative per global complement), each as (positive rows, care rows).
inline std::optional<std::vector<std::pair<TT, TT>>> obligations(const std::vector<unsigned>& labels, const TT& qa,
                                                                 int r) {
  struct Bucket { int key; std::vector<std::pair<unsigned, TT>> cls; };
  std::vector<Bucket> buckets;
  for (int y = 0; y < int(labels.size()); ++y) {
    int key = ((r < 0 ? 0 : (y >> r) & 1) << 1) | int(qa.get(y));
    auto it = std::find_if(buckets.begin(), buckets.end(), [&](const Bucket& b) { return b.key == key; });
    if (it == buckets.end()) { buckets.push_back({key, {}}); it = buckets.end() - 1; }
    auto& cls = it->cls;
    auto jt = std::find_if(cls.begin(), cls.end(), [&](const auto& c) { return c.first == labels[y]; });
    if (jt == cls.end()) { cls.push_back({labels[y], TT{}}); jt = cls.end() - 1; }
    jt->second.set(y);
    if (cls.size() > 2) return std::nullopt;
  }
  std::vector<std::pair<TT, TT>> pairs;
  for (auto& b : buckets) if (b.cls.size() == 2) pairs.push_back({b.cls[0].second, b.cls[1].second});
  if (pairs.empty()) return std::vector<std::pair<TT, TT>>{{TT{}, TT{}}};
  TT care;
  for (auto& [u, v] : pairs) care = care | u | v;
  std::vector<std::pair<TT, TT>> out;
  for (unsigned t = 0; t < (1u << (pairs.size() - 1)); ++t) {
    TT p = pairs[0].first;
    for (std::size_t j = 1; j < pairs.size(); ++j) p = p | (((t >> (j - 1)) & 1) ? pairs[j].second : pairs[j].first);
    out.push_back({p, care});
  }
  return out;
}

// The two-class (R, a) buckets as (class 0 rows, class 1 rows); assumes obligations(labels, qa, r) is feasible.
inline std::vector<std::pair<TT, TT>> bucket_pairs(const std::vector<unsigned>& labels, const TT& qa, int r) {
  std::map<int, std::vector<std::pair<unsigned, TT>>> buckets;
  std::vector<int> order;
  for (int y = 0; y < int(labels.size()); ++y) {
    int key = ((r < 0 ? 0 : (y >> r) & 1) << 1) | int(qa.get(y));
    if (!buckets.count(key)) order.push_back(key);
    auto& cls = buckets[key];
    auto jt = std::find_if(cls.begin(), cls.end(), [&](const auto& c) { return c.first == labels[y]; });
    if (jt == cls.end()) { cls.push_back({labels[y], TT{}}); jt = cls.end() - 1; }
    jt->second.set(y);
  }
  std::vector<std::pair<TT, TT>> out;
  for (int k : order) if (buckets[k].size() == 2) out.push_back({buckets[k][0].second, buckets[k][1].second});
  return out;
}

// Feature-quotient view of the second encoder over the Y literals: rows are the Y assignments (signature = the
// assignment itself), conflict edges join the two classes of every two-class bucket (orientation free), or the
// positive and negative rows of one oriented obligation (fixed target).
inline fq::Support y_support(int m, const std::vector<std::pair<TT, TT>>& sides) {
  std::vector<fq::u64> rows(m);
  for (int y = 0; y < m; ++y) rows[y] = fq::u64(y);
  std::vector<fq::Edge> edges;
  for (auto& [u, v] : sides)
    for (int i = 0; i < m; ++i)
      if (u.get(i))
        for (int j = 0; j < m; ++j) if (v.get(j)) edges.push_back({i, j});
  return fq::min_support(rows, edges);
}

// Per feasible first encoder (within first_cap) when Options::audit is set: orientation-free and per-orientation
// minimum Y-supports, and the standalone and marginal gate costs of the b chains built for each kept orientation.
struct Audit {
  int ky = 0, buckets = 0, orientations = 0, kept = 0;
  fq::Support free;                  // orientation-free minimum support (all two-class buckets)
  std::vector<int> fixed_s;          // per orientation: fixed-target minimum support
  std::vector<int> b_cost, b_marginal, b_support;  // per kept orientation: cost1(b), cost({a,b}) - cost1(a), |supp b|
  int a_cost = 0;
  // Root-partition screen (all bucket orientations, both phases) for b = op(Y_A) AND op(Y_B) over every split of
  // Y into two nonempty disjoint groups: pass / reject / unknown counts. Passing does not bound the size.
  int root_splits = 0, root_pass = 0, root_unknown = 0;
};

// cost_aware.py Marginal: synthesize a partial Y-table from a list of available signals (features), scoring every
// candidate by its marginal cost |cone(h) \ cone(a)| = cost({a, h}) - cost1(a) over an already-paid first encoder a.
// Features are deduplicated by Y-column modulo complement (cheaper marginal cost kept, first-seen order kept);
// constant columns are dropped. cheap() is an exact search over at most two new gates on the signed features;
// solve() is a feature-split recursion (complement normalized by the lowest cared row, memoized) joining with mux
// and keeping the best of the top `branch` splits by marginal cost. Any returned literal agrees with p on c.
class Marginal {
 public:
  Marginal(AIG& aig, int a, const std::vector<int>& avail, const std::vector<TT>& cols, const TT& full, int branch)
      : aig_(aig), a_(a), ka_(aig.cost1(a)), full_(full), branch_(branch) {
    std::map<TT, std::size_t> pos;
    for (std::size_t i = 0; i < avail.size(); ++i) {
      int h = avail[i];
      TT q = cols[i];
      if (q.get(0)) { h ^= 1; q = q ^ full; }
      auto it = pos.find(q);
      if (it == pos.end()) { pos.emplace(q, feat_.size()); feat_.push_back({h, q}); }
      else if (cost(h) < cost(feat_[it->second].first)) feat_[it->second].first = h;
    }
    std::vector<std::pair<int, TT>> kept;
    for (auto& f : feat_) if (f.second.any()) kept.push_back(f);
    feat_ = std::move(kept);
    for (auto& [h, q] : feat_) { sgn_.push_back({h, q}); sgn_.push_back({h ^ 1, q ^ full}); }
  }
  int cost(int h) { return aig_.cost({a_, h}) - ka_; }
  int calls() const { return calls_; }
  // Exact search over at most maxg marginal gates (signed root); -1 when none is found.
  int cheap(TT p, const TT& c, int maxg = 2) {
    p = p & c;
    if (!p.any()) return 0;
    if (p == c) return 1;
    for (auto& [h, q] : sgn_) if ((q & c) == p) return h;
    if (maxg == 0) return -1;
    for (int s = 0; s < 2; ++s) {
      TT T = s ? c ^ p : p, N = c ^ T;
      std::vector<std::pair<int, TT>> good;
      for (auto& f : sgn_) if ((f.second & T) == T) good.push_back(f);
      for (std::size_t i = 0; i < good.size(); ++i)
        for (std::size_t j = i; j < good.size(); ++j)
          if (!(good[i].second & good[j].second & N).any()) return aig_.AND(good[i].first, good[j].first) ^ s;
    }
    if (maxg == 1) return -1;
    for (int s = 0; s < 2; ++s) {
      TT T = s ? c ^ p : p, N = c ^ T;
      std::vector<std::pair<int, TT>> good;
      for (auto& f : sgn_) if ((f.second & T) == T) good.push_back(f);
      for (std::size_t i = 0; i < sgn_.size(); ++i)
        for (std::size_t j = i; j < sgn_.size(); ++j) {
          TT z = sgn_[i].second & sgn_[j].second;
          for (int neg = 0; neg < 2; ++neg) {
            TT zz = neg ? z ^ full_ : z;
            if ((zz & T) != T) continue;
            for (auto& [k, w] : good)
              if (!(zz & w & N).any()) return aig_.AND(aig_.AND(sgn_[i].first, sgn_[j].first) ^ neg, k) ^ s;
          }
        }
    }
    return -1;
  }
  int solve(TT p, const TT& c) {
    p = p & c;
    if (!p.any()) return 0;
    if (p == c) return 1;
    int low = 0;
    while (!c.get(low)) ++low;
    if (p.get(low)) return solve(c ^ p, c) ^ 1;
    auto key = std::make_pair(p, c);
    if (auto it = cache_.find(key); it != cache_.end()) return it->second;
    ++calls_;
    for (auto& [h, q] : sgn_)
      if ((q & c) == p) { cache_.emplace(key, h); return h; }
    using Opt = std::tuple<int, int, int, TT, TT>;
    std::vector<Opt> opts;
    for (auto& [h, q] : feat_) {
      TT c1 = c & q, c0 = c ^ c1;
      if (!c0.any() || !c1.any()) continue;
      int a = (p & c0).count(), b = (p & c1).count(), d = c0.count() - a, e = c1.count() - b;
      opts.push_back({std::min(a, d) + std::min(b, e), std::max(c0.count(), c1.count()), h, c0, c1});
    }
    if (opts.empty()) throw std::logic_error("inconsistent feature obligations");
    std::sort(opts.begin(), opts.end());
    int best = -1, bc = INT_MAX;
    for (std::size_t i = 0; i < opts.size() && int(i) < branch_; ++i) {
      auto& [sc, mx, h, c0, c1] = opts[i];
      int u = solve(p & c0, c0), v = solve(p & c1, c1), z = aig_.mux(h, u, v), k = cost(z);
      if (k < bc) { best = z; bc = k; }
    }
    cache_.emplace(key, best);
    return best;
  }

 private:
  AIG& aig_;
  int a_, ka_;
  TT full_;
  int branch_;
  std::vector<std::pair<int, TT>> feat_, sgn_;
  std::map<std::pair<TT, TT>, int> cache_;
  int calls_ = 0;
};

struct Options {
  // Opt-in cost-aware second encoders (cost_aware.py): 0 off; 1 = the reference construction (mode 0: Marginal over
  // Y + a, mode 1: Marginal over Y + a + every node of a's cone; first encoders with cost(a) >= cost(fallback)
  // skipped; native b and reuse not built); 2 = portfolio (native modes unchanged, plus both Marginal candidates in
  // a third decoded pool that feeds the reuse result).
  int cost_aware = 0;
  int ca_branch = 2;
  int first_cap = 6;      // feasible first encoders tested per (partition, context)
  int pair_cap = 8;       // decoded (a, b) pairs per mode per (partition, context)
  bool reuse = true;      // also build b with a as an extra input
  int max_x = 2;          // decoder inputs |X| in 1..max_x
  // Optional partial-function oracle (e.g. the native cofactor constructor) for 3..6 variables: given (positive,
  // care, k) it returns a chain over k inputs agreeing on care, or nullopt. Used at the sites in partial_sites
  // (1 = first-encoder bank, 2 = second encoder b, 4 = decoder); the cheaper of oracle and Shannon is kept.
  std::function<std::optional<Witness>(const TT&, const TT&, int)> partial;
  int partial_sites = 7;
  // Opt-in minimum-support orientation filter: compute the orientation-free minimum Y-support s* of b over the
  // two-class buckets (quotient theorem, conflict-directed search) and build b only for orientations whose own
  // fixed-target minimum support equals s* (a nonempty subset; all orientations when the search is not feasible).
  bool min_support_orient = false;
  // Opt-in (implies min_support_orient): build each kept b over its own minimum Y-support only, projecting the
  // obligation onto those |Z| = s* variables (a smaller partial-oracle / Shannon instance).
  bool support_project = false;
  std::function<void(const Audit&)> audit;
};

struct Stats {
  long first = 0, feasible = 0, orientations = 0, reuse = 0, decoded = 0, partial_calls = 0, partial_wins = 0;
  // cost-aware: Marginal obligations, cheap hits / solve calls per Marginal mode, mode-1 better / worse than mode 0
  long ca_obligations = 0, ca_skipped = 0, ca_cheap[2] = {0, 0}, ca_calls[2] = {0, 0}, ca_better = 0, ca_worse = 0,
       ca_savings = 0;
};

struct Result {
  Witness fallback, orient, reuse;  // fallback import; best orientation (mode 0); best incl. reuse portfolio
  int fallback_size = 0, orient_size = 0, reuse_size = 0;
  int mode1_size = 0;  // best of decoded pools 1 and 2 alone (before taking the minimum with mode 0)
  Stats stats;
  std::string win;  // description of the last improving candidate
};

// search_new from orientation.py. `fallback` must compute t; it is imported first, so its gates are shareable.
inline Result search(const TT& t, int n, const Witness& fallback, const Options& opt) {
  if (n < 3 || n > 8) throw std::invalid_argument("orientation search needs 3 <= n <= 8");
  if (simulate(fallback) != t) throw std::invalid_argument("fallback witness does not compute the target");
  AIG aig(n);
  std::vector<int> vs;
  for (int i = 0; i < n; ++i) vs.push_back(aig.lit(i));
  Result res;
  int fb = aig.import(fallback);
  auto synth = [&](int site, const TT& p, const TT& c, const std::vector<int>& lits) {
    int q = aig.solve(p, c, lits);
    int k = int(lits.size());
    if (opt.partial && (opt.partial_sites & site) && k >= 3 && k <= 6 && (p & c).any() && (p & c) != c) {
      if (auto w = opt.partial(p & c, c, k)) {
        if (w->n != k) throw std::logic_error("partial oracle returned a chain of the wrong width");
        int q2 = aig.import(*w, lits);
        if (aig.cost1(q2) < aig.cost1(q)) { q = q2; ++res.stats.partial_wins; }
        ++res.stats.partial_calls;
      }
    }
    return q;
  };
  std::array<int, 2> best{fb, fb};
  res.fallback = aig.export_cone(fb);
  for (int nx = 1; nx <= opt.max_x; ++nx) {
    std::vector<int> sel(nx);
    for (int i = 0; i < nx; ++i) sel[i] = i;
    while (true) {
      std::vector<int> X = sel, Y;
      for (int i = 0; i < n; ++i) if (std::find(X.begin(), X.end(), i) == X.end()) Y.push_back(i);
      int ky = int(Y.size()), m = 1 << ky;
      TT full = full_tt(ky);
      std::vector<int> yv, xv;
      for (int i : Y) yv.push_back(vs[i]);
      for (int i : X) xv.push_back(vs[i]);
      auto labels = residual(t, X, Y);
      std::vector<int> contexts;
      for (int r = -1; r < ky; ++r) {
        bool ok = true;
        for (int b = 0; b < 2 && ok; ++b) {
          std::set<unsigned> d;
          for (int i = 0; i < m; ++i) if (r < 0 || ((i >> r) & 1) == b) d.insert(labels[i]);
          ok = d.size() <= 4;
        }
        if (ok) contexts.push_back(r);
      }
      if (!contexts.empty()) {
        std::vector<TT> cof, classes;
        for (int i = 0; i < (1 << nx); ++i) {
          TT c;
          for (int j = 0; j < m; ++j) if ((labels[j] >> i) & 1) c.set(j);
          cof.push_back(c);
        }
        std::set<unsigned> distinct(labels.begin(), labels.end());
        for (unsigned v : distinct) {
          TT c;
          for (int j = 0; j < m; ++j) if (labels[j] == v) c.set(j);
          classes.push_back(c);
        }
        std::vector<TT> pats = cof;
        pats.insert(pats.end(), classes.begin(), classes.end());
        // Bank: literals, cofactors, class indicators, affine cofactor pairs, signed literal conjunctions,
        // cone nodes of the cofactor/class signals and contextual partial completions.
        std::set<int> bank{0};
        for (int y : yv) bank.insert(y);
        std::vector<int> roots;
        for (auto& p : pats) roots.push_back(synth(1, p, full, yv));
        bank.insert(roots.begin(), roots.end());
        for (std::size_t a = 0; a < cof.size(); ++a)
          for (std::size_t b = a + 1; b < cof.size(); ++b) bank.insert(synth(1, cof[a] ^ cof[b], full, yv));
        for (std::size_t a = 0; a < yv.size(); ++a)
          for (std::size_t b = a + 1; b < yv.size(); ++b)
            for (int s = 0; s < 2; ++s)
              for (int u = 0; u < 2; ++u) bank.insert(aig.AND(yv[a] ^ s, yv[b] ^ u));
        for (int h : roots) for (int j : aig.cone(h)) bank.insert(2 * j);
        for (int r : contexts) {
          if (r < 0) continue;
          for (int b = 0; b < 2; ++b) {
            TT care = col_tt(ky, r) ^ (b == 0 ? full : TT{});
            for (auto& p : pats) bank.insert(synth(1, p & care, care, yv));
          }
        }
        auto projected = [&](int h) {
          TT tt = aig.truth(h), q;
          for (int r = 0; r < m; ++r) {
            int row = 0;
            for (int i = 0; i < ky; ++i) row |= ((r >> i) & 1) << Y[i];
            if (tt.get(row)) q.set(r);
          }
          return q;
        };
        std::map<TT, int> unique;  // one cheapest representative per Y-column modulo complement
        for (int h0 : bank) {
          int h = h0;
          TT q = projected(h);
          if (q.get(0)) { h ^= 1; q = q ^ full; }
          auto it = unique.find(q);
          if (it == unique.end()) unique.emplace(q, h);
          else if (aig.cost1(h) < aig.cost1(it->second)) it->second = h;
        }
        for (int r : contexts) {
          struct Feas { int cost; std::size_t nobs; int a; TT qa; std::vector<std::pair<TT, TT>> obs; };
          std::vector<Feas> feasible;
          for (auto& [qa, a] : unique) {
            ++res.stats.first;
            auto obs = obligations(labels, qa, r);
            if (!obs) continue;
            ++res.stats.feasible;
            feasible.push_back({aig.cost1(a), obs->size(), a, qa, std::move(*obs)});
          }
          std::sort(feasible.begin(), feasible.end(), [](const Feas& x, const Feas& y) {
            return std::tie(x.cost, x.nobs, x.a) < std::tie(y.cost, y.nobs, y.a);
          });
          using Cand = std::tuple<int, int, int, TT, TT>;  // cost(a, b), a, b, qa, qb
          std::array<std::map<std::pair<int, int>, Cand>, 3> opts;
          for (std::size_t f = 0; f < feasible.size() && int(f) < opt.first_cap; ++f) {
            const Feas& F = feasible[f];
            std::vector<std::pair<TT, TT>> kept_obs = F.obs;
            std::vector<fq::u64> kept_z(kept_obs.size(), fq::u64((1u << ky) - 1));
            Audit au;
            if (opt.min_support_orient || opt.support_project || opt.audit) {
              auto sides = bucket_pairs(labels, F.qa, r);
              au.ky = ky; au.buckets = int(sides.size()); au.orientations = int(F.obs.size());
              au.free = y_support(m, sides);
              if (opt.audit && !sides.empty()) {
                std::vector<fq::u64> rows(m);
                for (int y = 0; y < m; ++y) rows[y] = fq::u64(y);
                std::vector<fq::Edge> edges;
                for (auto& [u, v] : sides)
                  for (int i = 0; i < m; ++i)
                    if (u.get(i))
                      for (int j = 0; j < m; ++j) if (v.get(j)) edges.push_back({i, j});
                fq::Partition P = fq::components(m, edges);
                const fq::u64 all = (fq::u64(1) << ky) - 1;
                for (fq::u64 A = 1; A < all; ++A) {
                  if (!(A & 1)) continue;  // splits up to swapping the groups
                  fq::Screen sc = fq::root_partition(rows, P, A, all & ~A);
                  ++au.root_splits;
                  au.root_pass += sc == fq::Screen::pass;
                  au.root_unknown += sc == fq::Screen::unknown;
                }
              }
              au.a_cost = aig.cost1(F.a);
              std::vector<std::pair<TT, TT>> keep;
              std::vector<fq::u64> keep_z;
              for (auto& [p, c] : F.obs) {
                fq::Support fs = y_support(m, {{p, c & ~p}});
                au.fixed_s.push_back(fs.s);
                if (au.free.status == fq::Status::feasible && fs.s < au.free.s)
                  throw std::logic_error("fixed-orientation support below the orientation-free minimum");
                if (au.free.status != fq::Status::feasible || fs.status != fq::Status::feasible || fs.s == au.free.s) {
                  keep.push_back({p, c});
                  keep_z.push_back(fs.status == fq::Status::feasible ? fs.support : fq::u64((1u << ky) - 1));
                }
              }
              if (keep.empty()) throw std::logic_error("no orientation attains the minimum support");
              if (opt.min_support_orient || opt.support_project) { kept_obs = keep; kept_z = keep_z; }
              au.kept = int(kept_obs.size());
            }
            // Cost-aware Marginal solvers over Y + a (mode 0) and Y + a + cone(a) (mode 1).
            std::vector<Marginal> ca;
            if (opt.cost_aware && aig.cost1(F.a) < aig.cost1(fb)) {
              std::vector<int> av0 = yv;
              if (std::find(av0.begin(), av0.end(), F.a) == av0.end()) av0.push_back(F.a);
              std::vector<int> av1 = av0;
              for (int j : aig.cone(F.a))
                if (std::find(av1.begin(), av1.end(), 2 * j) == av1.end()) av1.push_back(2 * j);
              for (auto* av : {&av0, &av1}) {
                std::vector<TT> cols;
                for (int h : *av) cols.push_back(projected(h));
                ca.emplace_back(aig, F.a, *av, cols, full, opt.ca_branch);
              }
            } else if (opt.cost_aware) {
              ++res.stats.ca_skipped;
            }
            for (std::size_t oi = 0; oi < kept_obs.size(); ++oi) {
              const auto& [p, c] = kept_obs[oi];
              if (!ca.empty()) {
                ++res.stats.ca_obligations;
                int k[2];
                for (int md = 0; md < 2; ++md) {
                  int b = ca[md].cheap(p, c, 2);
                  if (b >= 0) ++res.stats.ca_cheap[md];
                  else b = ca[md].solve(p, c);
                  TT qb = projected(b);
                  if (((p ^ qb) & c).any()) throw std::logic_error("cost-aware b violates its obligation");
                  k[md] = aig.cost({F.a, b});
                  int pool = opt.cost_aware == 1 ? md : 2;
                  opts[pool][{F.a, b}] = Cand{k[md], F.a, b, F.qa, qb};
                }
                if (k[1] < k[0]) { ++res.stats.ca_better; res.stats.ca_savings += k[0] - k[1]; }
                if (k[1] > k[0]) ++res.stats.ca_worse;
              }
              if (opt.cost_aware == 1) continue;
              ++res.stats.orientations;
              int b;
              if (opt.support_project && kept_z[oi] != fq::u64((1u << ky) - 1)) {
                // Project the obligation onto the support Z (consistent by the quotient test).
                std::vector<int> zi, yz;
                for (int i = 0; i < ky; ++i) if ((kept_z[oi] >> i) & 1) { zi.push_back(i); yz.push_back(yv[i]); }
                TT pz, cz;
                for (int y = 0; y < m; ++y) {
                  if (!c.get(y)) continue;
                  int row = 0;
                  for (std::size_t k = 0; k < zi.size(); ++k) row |= ((y >> zi[k]) & 1) << k;
                  if (cz.get(row) && pz.get(row) != p.get(y)) throw std::logic_error("support projection inconsistent");
                  cz.set(row);
                  if (p.get(y)) pz.set(row);
                }
                b = yz.empty() ? (pz.any() ? 1 : 0) : synth(2, pz, cz, yz);
              } else {
                b = synth(2, p, c, yv);
              }
              TT qb = projected(b);
              if (((p ^ qb) & c).any()) throw std::logic_error("b violates its obligation");
              opts[0][{F.a, b}] = Cand{aig.cost({F.a, b}), F.a, b, F.qa, qb};
              if (opt.audit) {
                au.b_cost.push_back(aig.cost1(b));
                au.b_marginal.push_back(aig.cost({F.a, b}) - au.a_cost);
                int sup = 0;
                for (int i = 0; i < ky; ++i) {
                  bool dep = false;
                  for (int y = 0; y < m && !dep; ++y)
                    if (!((y >> i) & 1) && qb.get(y) != qb.get(y | (1 << i))) dep = true;
                  sup += dep;
                }
                au.b_support.push_back(sup);
              }
              bool literal = F.a == 0 || F.a == 1 ||
                             std::find(yv.begin(), yv.end(), F.a) != yv.end() ||
                             std::find(yv.begin(), yv.end(), F.a ^ 1) != yv.end();
              if (opt.reuse && !literal) {
                TT pp = (p & ~F.qa) | (p & F.qa).shl(m), cc = (c & ~F.qa) | (c & F.qa).shl(m);
                std::vector<int> ya = yv;
                ya.push_back(F.a);
                int br = synth(2, pp, cc, ya);
                TT qbr = projected(br);
                if (((p ^ qbr) & c).any()) throw std::logic_error("reuse b violates its obligation");
                ++res.stats.reuse;
                opts[1][{F.a, br}] = Cand{aig.cost({F.a, br}), F.a, br, F.qa, qbr};
              }
            }
            if (opt.audit) opt.audit(au);
            for (auto& m2 : ca) {
              std::size_t md = std::size_t(&m2 - ca.data());
              res.stats.ca_calls[md] += m2.calls();
            }
          }
          for (int mode = 0; mode < 3; ++mode) {
            std::vector<Cand> cs;
            for (auto& [k, v] : opts[mode]) cs.push_back(v);
            std::sort(cs.begin(), cs.end());
            for (std::size_t i = 0; i < cs.size() && int(i) < opt.pair_cap; ++i) {
              auto& [cst, a, b, qa, qb] = cs[i];
              ++res.stats.decoded;
              int hasr = r >= 0;
              TT P, C;
              for (int j = 0; j < m; ++j) {
                int code = int(qa.get(j)) | (int(qb.get(j)) << 1);
                int high = (code << (nx + hasr)) | (hasr ? (((j >> r) & 1) << nx) : 0);
                for (int x = 0; x < (1 << nx); ++x) {
                  int bit = high | x;
                  bool val = (labels[j] >> x) & 1;
                  if (C.get(bit) && P.get(bit) != val) throw std::logic_error("decoder table inconsistent");
                  C.set(bit);
                  if (val) P.set(bit);
                }
              }
              std::vector<int> dv = xv;
              if (hasr) dv.push_back(yv[r]);
              dv.push_back(a);
              dv.push_back(b);
              int out = synth(4, P, C, dv);
              if (aig.truth(out) != t) throw std::logic_error("decoded candidate differs from the target");
              int slot = mode == 2 ? 1 : mode;
              if (aig.cost1(out) < aig.cost1(best[slot])) {
                best[slot] = out;
                res.win = "X=" + std::to_string(X[0]) + (nx > 1 ? "," + std::to_string(X[1]) : "") +
                          " R=" + (hasr ? std::to_string(Y[r]) : "none") + " mode=" + std::to_string(mode);
              }
            }
          }
        }
      }
      int i = nx - 1;
      while (i >= 0 && sel[i] == n - nx + i) --i;
      if (i < 0) break;
      ++sel[i];
      for (int j = i + 1; j < nx; ++j) sel[j] = sel[j - 1] + 1;
    }
  }
  res.mode1_size = aig.cost1(best[1]);
  if (aig.cost1(best[0]) < aig.cost1(best[1])) best[1] = best[0];
  res.orient = aig.export_cone(best[0]);
  res.reuse = aig.export_cone(best[1]);
  for (const Witness* w : {&res.fallback, &res.orient, &res.reuse})
    if (simulate(*w) != t) throw std::logic_error("exported witness fails independent simulation");
  res.fallback_size = int(res.fallback.gates.size());
  res.orient_size = int(res.orient.gates.size());
  res.reuse_size = int(res.reuse.gates.size());
  return res;
}

// Shannon lift of a small-function constructor to n > base inputs: for every split variable i, synthesize both
// cofactors (recursively), import them into one hashed AIG (shared gates count once) and join with a mux; keep the
// split with the smallest live cone. `base(f, k)` returns a verified witness for a k-input table (k <= base_n).
template <class Base>
class Lift {
 public:
  Lift(int base_n, Base base) : base_n_(base_n), base_(std::move(base)) {}
  Witness operator()(const TT& f, int n) {
    if (n <= base_n_) return base_(f, n);
    auto key = std::make_pair(n, f);
    if (auto it = memo_.find(key); it != memo_.end()) return it->second;
    Witness best;
    bool have = false;
    for (int i = 0; i < n; ++i) {
      Witness w0 = (*this)(cut(f, n, i, 0), n - 1), w1 = (*this)(cut(f, n, i, 1), n - 1);
      AIG aig(n);
      std::vector<int> map;
      for (int j = 0; j < n; ++j) if (j != i) map.push_back(aig.lit(j));
      int a = aig.import_lits(w0, map), b = aig.import_lits(w1, map);
      int out = aig.mux(aig.lit(i), a, b);
      Witness w = aig.export_cone(out);
      if (!have || w.gates.size() < best.gates.size()) { best = w; have = true; }
    }
    if (simulate(best) != f) throw std::logic_error("lifted witness fails independent simulation");
    memo_.emplace(key, best);
    return best;
  }

 private:
  int base_n_;
  Base base_;
  std::map<std::pair<int, TT>, Witness> memo_;
};

// Plain partial Shannon/merge recursion on the whole target (base.py `search` stage 0), as a fallback.
inline Witness shannon(const TT& t, int n) {
  AIG aig(n);
  std::vector<int> vs;
  for (int i = 0; i < n; ++i) vs.push_back(aig.lit(i));
  return aig.export_cone(aig.solve(t, full_tt(n), vs));
}

}  // namespace orient
