// tree_dp: exact small-excess decision for desk rect units (monotone AND/OR, fan-in 2, partial label on
// the cared rows). Opt-in companion to template_synth; same input lines: ID N GENERAL START BUDGET hexrow:t,...
// Only monotone units (GENERAL = 0) whose N inputs are all essential are decided; others print "skip".
//
// Decomposition (see sat-search/results/templates_native/rect_2026-11-27/TREE_DP.md for the proof).
// A minimum circuit reads every non-output gate and has no gate constant on the cared rows. Let H be the
// gates read at least twice, p = |H|, f_h the fanout of h. Every other non-output gate has exactly one
// reader, so the gates split into p+1 binary trees, rooted at H and at the output, whose leaves are input
// reads and H reads. A tree with L leaves has L-1 gates, so with every input read (all essential)
//     k = n - 1 + s,   s = e + sum_h (f_h - 1),   e = input reads beyond the first.
// Gates act bitwise on the cared-row vectors, so a tree whose leaves include placeholders h1, h2 is a table
// of 4 vectors, one per (h1, h2) value; AND/OR act entrywise. R(key) is the set of tables of trees with
// exactly the leaf multiset `key` (inputs with multiplicities, placeholder counts), dropping tables that are
// constant in every entry. The structures with s <= 2 are
//     s=0: p=0, read-once                         s=1: p=0, e=1  |  p=1, f=2
//     s=2: p=0, e=2  |  p=1, e=1, f=2  |  p=1, f=3  |  p=2, f=(2,2), h2 independent of h1 or reading it
// and each is checked exactly (h1 is a source of H, so its tree has input leaves only).
//
// usage: tree_dp.exe [--smax S] [--to-budget] [--threads T] [--heavy H] < units.txt   (S in 0..2, default 2)
// --to-budget stops each unit at its budget; --heavy caps concurrent shared-gate tasks (memory).
// The tables do not depend on the target, so units with the same wires share one DP per structure, and
// each p=2 case is its own DP (about 20 GB peak for 4x6 with --heavy 4).
// output: one JSON line per unit, printed when its level finishes: min_k (n-1+s for the least feasible s),
// or min_k null and gt = n-1+cap when no circuit of size <= n-1+cap exists (cap = smax, or the budget).
#include <algorithm>
#include <atomic>
#include <bit>
#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <cstdio>
#include <iostream>
#include <mutex>
#include <map>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

typedef uint32_t V;
struct Tab { V e[4]; };  // e[a], a = h1 + 2*h2

static inline uint64_t mix(uint64_t x) {
  x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33;
  return x;
}

// open-addressing set of tables; the all-zero table never occurs (constant tables are dropped)
struct TabSet {
  std::vector<uint64_t> lo, hi;
  size_t cnt = 0, mask = 0;
  explicit TabSet(size_t cap = 64) { size_t c = 64; while (c < cap * 2) c <<= 1; lo.assign(c, 0); hi.assign(c, 0); mask = c - 1; }
  void grow() {
    std::vector<uint64_t> ol, oh; ol.swap(lo); oh.swap(hi);
    lo.assign(ol.size() * 2, 0); hi.assign(oh.size() * 2, 0); mask = lo.size() - 1; cnt = 0;
    for (size_t i = 0; i < ol.size(); ++i) if (ol[i] | oh[i]) put(ol[i], oh[i]);
  }
  void put(uint64_t a, uint64_t b) {
    size_t i = mix(a ^ mix(b)) & mask;
    while (lo[i] | hi[i]) { if (lo[i] == a && hi[i] == b) return; i = (i + 1) & mask; }
    lo[i] = a; hi[i] = b;
    if (++cnt * 2 > lo.size()) grow();
  }
  void insert(const Tab& t) { put(t.e[0] | (uint64_t)t.e[1] << 32, t.e[2] | (uint64_t)t.e[3] << 32); }
  std::vector<Tab> list() const {
    std::vector<Tab> out; out.reserve(cnt);
    for (size_t i = 0; i < lo.size(); ++i) if (lo[i] | hi[i])
      out.push_back(Tab{{(V)lo[i], (V)(lo[i] >> 32), (V)hi[i], (V)(hi[i] >> 32)}});
    return out;
  }
};

struct Unit {
  std::string id;
  int n = 0, general = 0, start = 1, budget = 0, rows = 0;
  V T = 0, FULL = 0;
  std::vector<V> wire;
  std::vector<unsigned long long> row;
};

static bool parse(const std::string& line, Unit& u) {
  std::istringstream in(line);
  std::string rows;
  if (!(in >> u.id >> u.n >> u.general >> u.start >> u.budget >> rows)) return false;
  std::stringstream rs(rows);
  std::string item;
  while (std::getline(rs, item, ',')) {
    size_t c = item.find(':');
    if (c == std::string::npos) return false;
    u.row.push_back(std::stoull(item.substr(0, c), nullptr, 16));
    if (std::stoi(item.substr(c + 1))) u.T |= V(1) << (u.row.size() - 1);
  }
  u.rows = (int)u.row.size();
  if (u.rows > 32 || u.n > 16 || u.n < 2) return false;
  u.FULL = u.rows == 32 ? ~V(0) : (V(1) << u.rows) - 1;
  u.wire.assign(u.n, 0);
  for (int j = 0; j < u.rows; ++j)
    for (int i = 0; i < u.n; ++i) if (u.row[j] >> i & 1) u.wire[i] |= V(1) << j;
  return true;
}

// monotone partial label: input i is essential iff some T=1 row a and T=0 row b have a \ {i} inside b
static bool all_essential(const Unit& u) {
  for (int i = 0; i < u.n; ++i) {
    bool ess = false;
    for (int a = 0; a < u.rows && !ess; ++a) if (u.T >> a & 1)
      for (int b = 0; b < u.rows && !ess; ++b) if (!(u.T >> b & 1))
        if (((u.row[a] & ~(1ULL << i)) & ~u.row[b]) == 0) ess = true;
    if (!ess) return false;
  }
  return true;
}

// DP over sub-multisets of (inputs with multiplicity mult[i], pc1 copies of h1, pc2 copies of h2)
struct DP {
  const Unit& u;
  int nc;                      // components: n inputs, then h1, h2
  std::vector<int> cap, stride;
  int nkeys = 0;
  int max_inputs_with_ph;      // keys with placeholders and more input leaves than this are not needed
  int maxin[3][3];             // per (h1 count, h2 count); overrides max_inputs_with_ph when set (>= -1)
  std::vector<std::vector<Tab>> R;
  std::vector<char> done;

  DP(const Unit& un, const std::vector<int>& mult, int pc1, int pc2, int maxin)
      : u(un), nc(un.n + 2), max_inputs_with_ph(maxin) {
    for (auto& r : this->maxin) for (int& x : r) x = -2;
    cap = mult; cap.push_back(pc1); cap.push_back(pc2);
    stride.assign(nc, 1);
    for (int c = 1; c < nc; ++c) stride[c] = stride[c - 1] * (cap[c - 1] + 1);
    nkeys = stride[nc - 1] * (cap[nc - 1] + 1);
    R.assign(nkeys, {});
    done.assign(nkeys, 0);
  }
  void digits(int k, std::vector<int>& d) const {
    d.resize(nc);
    for (int c = 0; c < nc; ++c) { d[c] = k / stride[c] % (cap[c] + 1); }
  }
  bool needed(const std::vector<int>& d) const {
    int in = 0;
    for (int c = 0; c < u.n; ++c) in += d[c];
    if (d[u.n] == 0 && d[u.n + 1] == 0) return true;
    int m = maxin[d[u.n]][d[u.n + 1]];
    return in <= (m >= -1 ? m : max_inputs_with_ph);
  }
  bool constant(const Tab& t) const {
    return (t.e[0] == 0 && t.e[1] == 0 && t.e[2] == 0 && t.e[3] == 0) ||
           (t.e[0] == u.FULL && t.e[1] == u.FULL && t.e[2] == u.FULL && t.e[3] == u.FULL);
  }
  void run() {
    std::vector<int> order(nkeys), tot(nkeys);
    std::vector<int> d;
    for (int k = 0; k < nkeys; ++k) {
      digits(k, d); int s = 0; for (int c = 0; c < nc; ++c) s += d[c];
      tot[k] = s; order[k] = k;
    }
    std::stable_sort(order.begin(), order.end(), [&](int a, int b) { return tot[a] < tot[b]; });
    std::vector<int> db;
    for (int K : order) {
      if (tot[K] == 0) continue;
      digits(K, d);
      if (!needed(d)) continue;
      done[K] = 1;
      if (tot[K] == 1) {
        int c = 0; while (d[c] == 0) ++c;
        Tab t;
        if (c < u.n) t = Tab{{u.wire[c], u.wire[c], u.wire[c], u.wire[c]}};
        else if (c == u.n) t = Tab{{0, u.FULL, 0, u.FULL}};
        else t = Tab{{0, 0, u.FULL, u.FULL}};
        R[K].push_back(t);
        continue;
      }
      TabSet set(1024);
      // enumerate B <= K componentwise (odometer), C = K - B
      db.assign(nc, 0);
      while (true) {
        int c = 0;
        while (c < nc && db[c] == d[c]) { db[c] = 0; ++c; }
        if (c == nc) break;
        ++db[c];
        int B = 0; for (int x = 0; x < nc; ++x) B += db[x] * stride[x];
        int C = K - B;
        if (B == K || B > C) continue;
        const std::vector<Tab>& RB = R[B];
        const std::vector<Tab>& RC = R[C];
        for (const Tab& a : RB) for (const Tab& b : RC) {
          Tab x{{a.e[0] & b.e[0], a.e[1] & b.e[1], a.e[2] & b.e[2], a.e[3] & b.e[3]}};
          Tab y{{a.e[0] | b.e[0], a.e[1] | b.e[1], a.e[2] | b.e[2], a.e[3] | b.e[3]}};
          if (!constant(x)) set.insert(x);
          if (!constant(y)) set.insert(y);
        }
      }
      R[K] = set.list();
    }
  }
  int key(const std::vector<int>& in, int a, int b) const {
    int k = 0; for (int c = 0; c < u.n; ++c) k += in[c] * stride[c];
    return k + a * stride[u.n] + b * stride[u.n + 1];
  }
};

// dedupe the D sets (inclusion-minimal reduction was quadratic; plain dedupe keeps the check exact)
static void minimize(std::vector<V>& D) {
  std::sort(D.begin(), D.end());
  D.erase(std::unique(D.begin(), D.end()), D.end());
}

// is there v in vs with v == T on every bit of some D in Ds? Direct scan, or a subset-sum bitmap
// (Y[y] = some v^T inside y; then ask Y[~D]) when the scan would cost more than building the bitmap.
static int g_rows = 0;
static bool meet(const std::vector<V>& vs, const std::vector<V>& Ds, V T) {
  if (vs.empty() || Ds.empty()) return false;
  double scan = (double)vs.size() * Ds.size(), build = (double)(1u << g_rows) * g_rows;
  if (scan <= 4 * build) {
    for (V v : vs) { V x = v ^ T; for (V D : Ds) if ((x & D) == 0) return true; }
    return false;
  }
  const V FULL = g_rows == 32 ? ~V(0) : (V(1) << g_rows) - 1;
  std::vector<uint8_t> Y((size_t)1 << g_rows, 0);
  for (V v : vs) Y[(v ^ T) & FULL] = 1;
  for (int b = 0; b < g_rows; ++b)
    for (size_t y = 0; y < Y.size(); ++y) if (y >> b & 1) Y[y] |= Y[y ^ ((size_t)1 << b)];
  for (V D : Ds) if (Y[~D & FULL]) return true;
  return false;
}

// odometer over sub-multisets S <= M of the inputs
static bool next_sub(std::vector<int>& S, const std::vector<int>& M) {
  for (size_t c = 0; c < M.size(); ++c) { if (S[c] < M[c]) { ++S[c]; return true; } S[c] = 0; }
  return false;
}
static int total(const std::vector<int>& S) { int t = 0; for (int x : S) t += x; return t; }

static std::vector<V> vecs(const std::vector<Tab>& R) { std::vector<V> v; v.reserve(R.size()); for (auto& t : R) v.push_back(t.e[0]); return v; }

// The DP tables depend only on the input wires (n, cared rows), not on the target T. Each check builds
// its DP once and tests every unit in `us`, which must all share u.n and u.wire; it returns one flag per unit.
using Units = std::vector<const Unit*>;

// p = 0: one tree over multiset M
static std::vector<char> check_p0(const Units& us, const std::vector<int>& M) {
  DP dp(*us[0], M, 0, 0, -1); dp.run();
  std::vector<char> ok(us.size(), 0);
  const std::vector<Tab>& R = dp.R[dp.key(M, 0, 0)];
  for (size_t j = 0; j < us.size(); ++j)
    for (auto& t : R) if (t.e[0] == us[j]->T) { ok[j] = 1; break; }
  return ok;
}

// p = 1: h1 = tree on S1 (inputs), output tree on M - S1 plus f copies of h1
static bool g_verbose = false;
static bool check_p1_one(const Unit& u, const DP& dp, const std::vector<int>& M, int f);
static std::vector<char> check_p1(const Units& us, const std::vector<int>& M, int f) {
  const Unit& u = *us[0];
  auto t0 = std::chrono::steady_clock::now();
  DP dp(u, M, f, 0, total(M) - 2); dp.run();  // |S1| >= 2, so the output tree has at most |M|-2 input leaves
  if (g_verbose) {
    size_t tot = 0, mx = 0; for (auto& r : dp.R) { tot += r.size(); mx = std::max(mx, r.size()); }
    std::fprintf(stderr, "p1 f=%d dp %.2fs tables %zu max %zu\n", f,
                 std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(), tot, mx);
  }
  std::vector<char> ok(us.size(), 0);
  for (size_t j = 0; j < us.size(); ++j) ok[j] = check_p1_one(*us[j], dp, M, f);
  return ok;
}
static bool check_p1_one(const Unit& u, const DP& dp, const std::vector<int>& M, int f) {
  std::vector<int> S(u.n, 0), C(u.n);
  while (next_sub(S, M)) {
    if (total(S) < 2) continue;
    for (int c = 0; c < u.n; ++c) C[c] = M[c] - S[c];
    std::vector<V> Ds;
    for (auto& t : dp.R[dp.key(C, f, 0)])
      if ((t.e[0] & ~u.T) == 0 && (u.T & ~t.e[1]) == 0) Ds.push_back(t.e[1] & ~t.e[0]);
    if (Ds.empty()) continue;
    minimize(Ds);
    if (meet(vecs(dp.R[dp.key(S, 0, 0)]), Ds, u.T)) return true;
  }
  return false;
}

// p = 2, f = (2, 2), each input once. h1 a source of H (input leaves only). h2 reads h1 c times (0..2),
// the output tree reads h1 2-c times and h2 twice.
static bool check_p2_one(const Unit& u, const DP& dp, int cc0);
static std::vector<char> check_p2(const Units& us, int only_cc) {
  const Unit& u = *us[0];
  std::vector<int> M(u.n, 1);
  auto t0 = std::chrono::steady_clock::now();
  // one DP per case cc (h2 reads h1 cc times): output trees (C, 2-cc, 2) with |C| <= n-4+cc
  // (S1 >= 2 inputs, S2 >= 2-cc inputs), h2 trees (S2, cc, 0) with |S2| <= n-2
  const int cc0 = only_cc;
  DP dp(u, M, std::max(cc0, 2 - cc0), 2, u.n - 2);
  // needed keys: h2 trees (S2, c, 0) with |S2| <= n-2; output trees (C, a, 2) with |C| <= n-2-a
  // (S1 >= 2 inputs, and S2 >= 2-c inputs with c = 2-a); sub-keys of these have no more inputs
  for (int a = 0; a <= 2; ++a) {
    dp.maxin[a][0] = (a <= cc0) ? u.n - 2 : (a <= 2 - cc0 ? u.n - 4 + cc0 : -1);
    dp.maxin[a][1] = dp.maxin[a][2] = (a <= 2 - cc0) ? u.n - 4 + cc0 : -1;
  }
  dp.run();
  if (g_verbose) {
    size_t tot = 0, mx = 0; for (auto& r : dp.R) { tot += r.size(); mx = std::max(mx, r.size()); }
    std::fprintf(stderr, "p2 dp %.2fs tables %zu max %zu\n",
                 std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(), tot, mx);
  }
  std::vector<char> ok(us.size(), 0);
  for (size_t j = 0; j < us.size(); ++j) ok[j] = check_p2_one(*us[j], dp, cc0);
  return ok;
}
static bool check_p2_one(const Unit& u, const DP& dp, int cc0) {
  std::vector<int> M(u.n, 1);
  // output tables with t(0,0) inside T inside t(1,1), cached per key
  std::vector<std::vector<Tab>> Fc(dp.nkeys);
  std::vector<char> Fdone(dp.nkeys, 0);
  std::vector<int> S1(u.n, 0), S2(u.n), C(u.n), rest(u.n);
  while (next_sub(S1, M)) {
    if (total(S1) < 2) continue;
    std::vector<V> v1s = vecs(dp.R[dp.key(S1, 0, 0)]);
    if (v1s.empty()) continue;
    for (int c = 0; c < u.n; ++c) rest[c] = M[c] - S1[c];
    std::fill(S2.begin(), S2.end(), 0);
    bool first = true;
    while (first || next_sub(S2, rest)) {
      first = false;
      for (int c = 0; c < u.n; ++c) C[c] = rest[c] - S2[c];
      int s2 = total(S2);
      for (int cc = cc0; cc <= cc0; ++cc) {
        if (s2 + cc < 2) continue;
        int kC = dp.key(C, 2 - cc, 2);
        if (!dp.done[kC]) continue;
        if (!Fdone[kC]) {
          Fdone[kC] = 1;
          for (auto& t : dp.R[kC]) if ((t.e[0] & ~u.T) == 0 && (u.T & ~t.e[3]) == 0) Fc[kC].push_back(t);
        }
        const std::vector<Tab>& F = Fc[kC];
        if (F.empty()) continue;
        const std::vector<Tab>& G = dp.R[dp.key(S2, cc, 0)];
        if (G.empty()) continue;
        if (cc == 0) {
          // independent: v2 from R(S2); D-sets from (F, v1)
          std::vector<V> Ds;
          for (V v1 : v1s) for (auto& t : F) {
            V lo = t.e[0] | (t.e[1] & v1), hi = t.e[2] | (t.e[3] & v1);
            if ((lo & ~u.T) == 0 && (u.T & ~hi) == 0) Ds.push_back(hi & ~lo);
          }
          if (Ds.empty()) continue;
          minimize(Ds);
          if (meet(vecs(G), Ds, u.T)) return true;
        } else {
          for (V v1 : v1s) {
            std::vector<V> v2s;
            for (auto& g : G) { V v2 = g.e[0] | (g.e[1] & v1); if (v2 != 0 && v2 != u.FULL) v2s.push_back(v2); }
            if (v2s.empty()) continue;
            std::vector<V> Ds;
            for (auto& t : F) {
              V lo = t.e[0] | (t.e[1] & v1), hi = t.e[2] | (t.e[3] & v1);
              if ((lo & ~u.T) == 0 && (u.T & ~hi) == 0) Ds.push_back(hi & ~lo);
            }
            if (Ds.empty()) continue;
            minimize(Ds);
            if (meet(v2s, Ds, u.T)) return true;
          }
        }
      }
    }
  }
  return false;
}

struct Task { int unit, s; int kind; int a, b; };  // kind 0: p0 (extras a,b; -1 none), 1: p1 f=a extra b, 2: p2 with h2 reading h1 a times

int main(int argc, char** argv) {
  int smax = 2, threads = 11, heavy = 4;
  bool to_budget = false;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--smax" && i + 1 < argc) smax = std::atoi(argv[++i]);
    else if (a == "--threads" && i + 1 < argc) threads = std::atoi(argv[++i]);
    else if (a == "--heavy" && i + 1 < argc) heavy = std::atoi(argv[++i]);  // max concurrent p>=1 tasks
    else if (a == "--to-budget") to_budget = true;  // per unit, stop at s = BUDGET - (n-1)
    else if (a == "--verbose") g_verbose = true;
  }
  if (smax < 0 || smax > 2 || heavy < 1) { std::fprintf(stderr, "--smax must be 0..2, --heavy >= 1\n"); return 2; }
  std::vector<Unit> units;
  std::vector<char> skip;
  std::string line;
  while (std::getline(std::cin, line)) {
    if (line.find_first_not_of(" \t\r") == std::string::npos) continue;
    Unit u;
    if (!parse(line, u)) { std::fprintf(stderr, "bad line: %s\n", line.c_str()); return 2; }
    if (g_rows && g_rows != u.rows) { std::fprintf(stderr, "all units must have the same row count\n"); return 2; }
    g_rows = u.rows;
    skip.push_back(u.general != 0 || !all_essential(u));
    units.push_back(u);
  }
  std::vector<int> ucap(units.size(), smax), found(units.size(), -1);
  for (size_t i = 0; i < units.size(); ++i)
    if (to_budget) ucap[i] = std::max(-1, std::min(smax, units[i].budget - (units[i].n - 1)));
  std::vector<double> secs(units.size(), 0);
  std::vector<char> printed(units.size(), 0);
  for (size_t i = 0; i < units.size(); ++i)
    if (skip[i]) std::printf("{\"id\":\"%s\",\"status\":\"skip\"}\n", units[i].id.c_str());
  std::mutex mu;
  std::condition_variable cv;
  int heavy_running = 0;
  // levels s = 0, 1, 2: a unit enters level s only if no smaller s was feasible; inside a level a unit's
  // remaining tasks are skipped once one succeeds. Heavy (p >= 1) tasks are limited to `heavy` at a time.
  // units with the same n and cared-row wires share every DP: one task per (group, structure)
  std::map<std::vector<V>, std::vector<int>> gmap;
  for (int i = 0; i < (int)units.size(); ++i) if (!skip[i]) {
    std::vector<V> key = units[i].wire; key.push_back((V)units[i].n);
    gmap[key].push_back(i);
  }
  std::vector<std::vector<int>> groups;
  for (auto& kv : gmap) groups.push_back(kv.second);
  if (g_verbose) std::fprintf(stderr, "%zu units in %zu wire groups\n", units.size(), groups.size());
  for (int s = 0; s <= smax; ++s) {
    std::vector<Task> tasks;
    for (int gi = 0; gi < (int)groups.size(); ++gi) {
      bool any = false;
      for (int i : groups[gi]) if (found[i] < 0 && s <= ucap[i]) any = true;
      if (!any) continue;
      int n = units[groups[gi][0]].n;
      if (s == 0) tasks.push_back({gi, 0, 0, -1, -1});
      if (s == 1) {
        tasks.push_back({gi, 1, 1, 2, -1});
        for (int x = 0; x < n; ++x) tasks.push_back({gi, 1, 0, x, -1});
      }
      if (s == 2) {
        for (int c = 0; c <= 2; ++c) tasks.push_back({gi, 2, 2, c, 0});
        tasks.push_back({gi, 2, 1, 3, -1});
        for (int x = 0; x < n; ++x) tasks.push_back({gi, 2, 1, 2, x});
        for (int x = 0; x < n; ++x) for (int y = x; y < n; ++y) tasks.push_back({gi, 2, 0, x, y});
      }
    }
    std::stable_sort(tasks.begin(), tasks.end(), [](const Task& a, const Task& b) { return a.kind > b.kind; });
    std::atomic<size_t> next{0};
    auto worker = [&]() {
      for (size_t t; (t = next++) < tasks.size();) {
        const Task& k = tasks[t];
        bool hv = k.kind >= 1;
        std::vector<int> mem;
        Units us;
        {
          std::unique_lock<std::mutex> g(mu);
          for (int i : groups[k.unit]) if (found[i] < 0 && k.s <= ucap[i]) { mem.push_back(i); us.push_back(&units[i]); }
          if (mem.empty()) continue;
          if (hv) { cv.wait(g, [&] { return heavy_running < heavy; }); ++heavy_running; }
        }
        auto t0 = std::chrono::steady_clock::now();
        std::vector<int> M(us[0]->n, 1);
        std::vector<char> ok;
        if (k.kind == 0) { if (k.a >= 0) ++M[k.a]; if (k.b >= 0) ++M[k.b]; ok = check_p0(us, M); }
        else if (k.kind == 1) { if (k.b >= 0) ++M[k.b]; ok = check_p1(us, M, k.a); }
        else ok = check_p2(us, k.a);
        double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        {
          std::lock_guard<std::mutex> g(mu);
          if (hv) --heavy_running;
          for (size_t j = 0; j < mem.size(); ++j) {
            if (ok[j] && found[mem[j]] < 0) found[mem[j]] = k.s;
            secs[mem[j]] += dt / mem.size();  // shared DP time split evenly
          }
        }
        if (hv) cv.notify_all();
      }
    };
    std::vector<std::thread> pool;
    for (int i = 0; i < threads; ++i) pool.emplace_back(worker);
    for (auto& th : pool) th.join();
    if (g_verbose) std::fprintf(stderr, "level s=%d done (%zu tasks)\n", s, tasks.size());
    // print every unit whose answer is now final, so a stopped run keeps its finished units
    for (size_t i = 0; i < units.size(); ++i) {
      if (printed[i] || skip[i]) continue;
      const Unit& u = units[i];
      if (found[i] >= 0) std::printf("{\"id\":\"%s\",\"n\":%d,\"min_k\":%d,\"cpu_seconds\":%.2f}\n", u.id.c_str(), u.n, u.n - 1 + found[i], secs[i]);
      else if (s >= ucap[i]) std::printf("{\"id\":\"%s\",\"n\":%d,\"min_k\":null,\"gt\":%d,\"cpu_seconds\":%.2f}\n", u.id.c_str(), u.n, u.n - 1 + ucap[i], secs[i]);
      else continue;
      printed[i] = 1;
    }
    std::fflush(stdout);
  }
  return 0;
}
