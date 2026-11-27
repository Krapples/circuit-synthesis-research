// tree_dp: exact small-excess decision for desk rect units (monotone AND/OR, fan-in 2, partial label on
// the cared rows). Opt-in companion to template_synth; same input lines: ID N GENERAL START BUDGET hexrow:t,...
// Only monotone units (GENERAL = 0) whose N inputs are all essential are decided; others print "skip".
//
// Decomposition (proof: sat-search/results/templates_native/rect_2026-11-27/TREE_DP.md). A minimum circuit
// reads every non-output gate and has no gate constant on the cared rows. Let H be the gates read at least
// twice, p = |H|, f_h the fanout of h. Every other non-output gate has one reader, so the gates split into
// p+1 binary trees rooted at H and at the output, whose leaves are input reads and H reads. A tree with L
// leaves has L-1 gates, so with every input read (all essential)
//     k = n - 1 + s,   s = e + sum_h (f_h - 1),   e = input reads beyond the first.
// Order H topologically (h_0, ..., h_{p-1}); the tree of h_t reads only inputs and h_j with j < t. A shape
// fixes p, the input multiset M (e extra copies) and r[t][j] = reads of h_j by tree t (t < p: tree of h_t,
// t = p: output tree), sum_t r[t][j] = f_j >= 2. All shapes with s <= 3 are enumerated.
// Gates act bitwise on cared-row vectors, so a tree with placeholder leaves h_0..h_{p-1} is a table of 2^p
// vectors, one per placeholder assignment, monotone in the index bits; AND/OR act entrywise. R(key) is the
// set of tables of trees with exactly the leaf multiset `key`, minus tables constant in every entry. A shape
// is feasible iff some split of M into the trees' input multisets and tables give values v_t = tree_t(v_<t),
// none constant, with output tree(v) = T. The last value is matched by lo/hi sets (agree with T on hi & ~lo).
//
// usage: tree_dp.exe [--smax S] [--to-budget] [--threads T] [--heavy H] [--prune] [--verbose] < units.txt
//   S in 0..3 (default 2). --to-budget stops each unit at its budget; --heavy caps concurrent shapes with
//   shared gates (memory). --prune drops redundant gates (sound for minimum circuits).
// Tables depend only on the wires, so units with the same wires share one DP per shape.
// output: one JSON line per unit, printed when its level finishes: min_k = n-1+s for the least feasible s,
// with a witness ("gates": [op, left, right], 0 = AND, 1 = OR, gate j writes wire n+j; "output"), checked by
// simulation on the cared rows; or min_k null and gt = n-1+cap when no circuit of size <= n-1+cap exists
// (cap = smax, or the budget with --to-budget).
#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <iostream>
#include <map>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

typedef uint32_t V;
static bool g_verbose = false, g_prune = false;
// --sym: store R only for one key per orbit of the twin-input group (see TREE_DP_MEMORY.md, method 1)
static bool g_sym = false;
static bool g_fold = false;  // --fold: fold placeholder values into the output-tree tables per depth (exact; opt-in)
static bool g_foldcheck = false;  // TREE_DP_FOLDCHECK: cross-check the window filter against the direct fold filter
// TREE_DP_DUMP=<file>: write per-key table counts after each DP (measurement only)
static FILE* g_dump = nullptr;
static std::mutex g_dump_mu;
static std::atomic<int> g_dump_id{0};
static int g_rows = 0;
// opt-in check-phase profile (TREE_DP_PROF=1): per-thread counters, printed per shape with --verbose
static bool g_prof = false;
struct Prof { double tF = 0, tG = 0, tM = 0, tMid = 0, tFold = 0; uint64_t folds = 0, foldemp = 0, lastc = 0, Fscan = 0, Ds = 0, Gev = 0, vs = 0, mscan = 0, mbit = 0, midc = 0, midev = 0, mids = 0, splits = 0; };
static thread_local Prof g_pf;
static inline double pnow() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

template <int NE> struct TabT { V e[NE]; };
template <int NE> static inline bool tab_eq(const TabT<NE>& a, const TabT<NE>& b) {
  for (int i = 0; i < NE; ++i) if (a.e[i] != b.e[i]) return false;
  return true;
}

static inline uint64_t mix(uint64_t x) {
  x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33;
  return x;
}

// open-addressing set of tables; the all-zero table never occurs (constant tables are dropped)
template <int NE> struct TabSetT {
  static constexpr int W = (NE + 1) / 2;
  std::vector<uint64_t> k;
  size_t cnt = 0, slots = 0;
  explicit TabSetT(size_t cap = 64) { slots = 64; while (slots < cap * 2) slots <<= 1; k.assign(slots * W, 0); }
  static bool empty(const uint64_t* s) { for (int j = 0; j < W; ++j) if (s[j]) return false; return true; }
  void put(const uint64_t* w) {
    uint64_t h = 0; for (int j = 0; j < W; ++j) h = mix(h ^ w[j]);
    size_t m = slots - 1, i = h & m;
    while (true) {
      uint64_t* s = &k[i * W];
      if (empty(s)) { std::memcpy(s, w, W * 8); break; }
      if (std::memcmp(s, w, W * 8) == 0) return;
      i = (i + 1) & m;
    }
    if (++cnt * 2 > slots) grow();
  }
  void grow() {
    std::vector<uint64_t> old; old.swap(k);
    size_t os = slots; slots *= 2; k.assign(slots * W, 0); cnt = 0;
    for (size_t i = 0; i < os; ++i) if (!empty(&old[i * W])) put(&old[i * W]);
  }
  void insert(const TabT<NE>& t) {
    uint64_t w[W];
    for (int j = 0; j < W; ++j) w[j] = t.e[2 * j] | (2 * j + 1 < NE ? (uint64_t)t.e[2 * j + 1] << 32 : 0);
    put(w);
  }
  std::vector<TabT<NE>> list() const {
    std::vector<TabT<NE>> out; out.reserve(cnt);
    for (size_t i = 0; i < slots; ++i) {
      const uint64_t* s = &k[i * W];
      if (empty(s)) continue;
      TabT<NE> t;
      for (int j = 0; j < NE; ++j) t.e[j] = (V)(s[j / 2] >> (32 * (j & 1)));
      out.push_back(t);
    }
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

// p shared gates, input multiset M, r[t][j] = reads of h_j by tree t (t < p: tree of h_t; t = p: output)
struct Shape {
  int p = 0, s = 0;
  std::vector<int> M;
  int r[4][3] = {};
  int tot() const { int t = 0; for (int x : M) t += x; return t; }
  int reads(int t) const { int x = 0; for (int j = 0; j < p; ++j) x += r[t][j]; return x; }
  int min_inputs(int t) const { return std::max(0, 2 - reads(t)); }  // every tree has >= 2 leaves
  std::string str() const {
    std::string o = "p" + std::to_string(p) + " M";
    for (int x : M) o += std::to_string(x);
    for (int t = 0; t <= p && p > 0; ++t) {
      o += " r" + std::to_string(t) + "=";
      for (int j = 0; j < p; ++j) o += std::to_string(r[t][j]);
    }
    return o;
  }
};

// all shapes with excess exactly s for n inputs (p <= 3, so s <= 3 is complete)
static std::vector<Shape> shapes_for(int n, int s) {
  std::vector<Shape> out;
  for (int p = 0; p <= 3 && p <= s; ++p) {
    std::vector<std::vector<int>> fans;
    std::vector<int> f(p, 2);
    std::function<void(int, int)> fan = [&](int j, int used) {
      if (j == p) { fans.push_back(f); return; }
      for (int x = 2; used + x - 1 <= s; ++x) { f[j] = x; fan(j + 1, used + x - 1); }
    };
    fan(0, 0);
    for (auto& fv : fans) {
      int e = s;
      for (int x : fv) e -= x - 1;
      std::vector<std::vector<int>> Ms;
      std::vector<int> M(n, 1);
      std::function<void(int, int)> ext = [&](int from, int left) {
        if (left == 0) { Ms.push_back(M); return; }
        for (int i = from; i < n; ++i) { ++M[i]; ext(i, left - 1); --M[i]; }
      };
      ext(0, e);
      // reads of h_j go to trees t in j+1..p (topological order)
      std::vector<Shape> rs;
      Shape base; base.p = p; base.s = s;
      std::function<void(int, int, int)> dist = [&](int j, int t, int left) {
        if (t == p) {
          base.r[p][j] = left;
          if (j + 1 < p) dist(j + 1, j + 2, fv[j + 1]); else rs.push_back(base);
          base.r[p][j] = 0;
          return;
        }
        for (int c = 0; c <= left; ++c) { base.r[t][j] = c; dist(j, t + 1, left - c); }
        base.r[t][j] = 0;
      };
      if (p == 0) rs.push_back(base); else dist(0, 1, fv[0]);
      for (auto& M2 : Ms) for (auto sh : rs) {
        sh.M = M2;
        int need = 0;
        for (int t = 0; t <= p; ++t) need += sh.min_inputs(t);
        if (need > sh.tot()) continue;
        out.push_back(sh);
      }
    }
  }
  return out;
}

template <int NE> struct DPT {
  using Tab = TabT<NE>;
  static constexpr int NP = NE == 1 ? 0 : NE == 2 ? 1 : NE == 4 ? 2 : 3;
  const Unit& u;
  int nc;
  std::vector<int> cap, stride;
  int nkeys = 0;
  std::vector<int> maxin;  // by placeholder counts (base 5): max input leaves of a needed key, -1 = none
  std::vector<std::vector<Tab>> R;
  std::vector<char> done;
  // --sym. Inputs i, j are twins when swapping them maps the cared-row set onto itself; twins with equal
  // multiplicity in M form a class, and the classes generate a group G that fixes M and the wires. A tree with
  // leaf multiset K relabelled by g in G has leaf multiset gK and the row-permuted table, so R(gK) = g R(K).
  // Only the representative of each key orbit (class counts in descending order) stores R; every other key
  // reads its representative through a row-permutation lookup table.
  using Lut = std::array<std::array<V, 256>, 4>;
  std::vector<int> repk, lutk;  // per key: representative key, index into luts (-1 = identity)
  std::vector<Lut> luts;

  DPT(const Unit& un, const Shape& sh) : u(un), nc(un.n + NP), maxin(125, -1) {
    cap = sh.M;
    for (int j = 0; j < NP; ++j) { int c = 0; for (int t = 0; t <= sh.p; ++t) c = std::max(c, sh.r[t][j]); cap.push_back(c); }
    stride.assign(nc, 1);
    for (int c = 1; c < nc; ++c) stride[c] = stride[c - 1] * (cap[c - 1] + 1);
    nkeys = stride[nc - 1] * (cap[nc - 1] + 1);
    R.assign(nkeys, {});
    done.assign(nkeys, 0);
    // a key is needed iff it is a sub-multiset of some tree's key (S_t, r[t]): placeholder counts a <= r[t]
    // and at most |M| minus the other trees' minimum input counts
    int tot = sh.tot(), summin = 0;
    for (int t = 0; t <= sh.p; ++t) summin += sh.min_inputs(t);
    for (int a = 0; a < 125; ++a) {
      int av[3] = {a % 5, a / 5 % 5, a / 25};
      for (int t = 0; t <= sh.p; ++t) {
        bool dom = true;
        for (int j = 0; j < 3; ++j) if (av[j] > (j < NP ? sh.r[t][j] : 0)) dom = false;
        if (dom) maxin[a] = std::max(maxin[a], tot - (summin - sh.min_inputs(t)));
      }
    }
    repk.resize(nkeys);
    lutk.assign(nkeys, -1);
    for (int k = 0; k < nkeys; ++k) repk[k] = k;
    if (g_sym) init_sym(sh);
  }
  void init_sym(const Shape& sh) {
    const int n = u.n;
    std::map<unsigned long long, int> rowidx;
    for (int r = 0; r < u.rows; ++r) rowidx[u.row[r]] = r;
    auto swapped = [&](unsigned long long m, int i, int j) {
      unsigned long long bi = m >> i & 1, bj = m >> j & 1;
      m &= ~((1ULL << i) | (1ULL << j));
      return m | (bi << j) | (bj << i);
    };
    auto twins = [&](int i, int j) {
      for (int r = 0; r < u.rows; ++r) if (!rowidx.count(swapped(u.row[r], i, j))) return false;
      return true;
    };
    // classes: twin and same multiplicity (twin-ness is an equivalence: (ik) = (ij)(jk)(ij))
    std::vector<int> cl(n, -1);
    std::vector<std::vector<int>> cls;
    for (int i = 0; i < n; ++i) {
      if (cl[i] >= 0) continue;
      cl[i] = (int)cls.size();
      cls.push_back({i});
      for (int j = i + 1; j < n; ++j)
        if (cl[j] < 0 && sh.M[j] == sh.M[i] && twins(i, j)) { cl[j] = cl[i]; cls.back().push_back(j); }
    }
    std::map<std::vector<int>, int> lutid;
    std::vector<int> d, rd(nc), pi(n);
    for (int k = 0; k < nkeys; ++k) {
      digits(k, d);
      rd = d;
      for (int i = 0; i < n; ++i) pi[i] = i;
      for (auto& c : cls) {
        if (c.size() < 2) continue;
        // members of K by count descending (stable); the representative puts those counts on c in index order
        std::vector<int> byc(c);
        std::stable_sort(byc.begin(), byc.end(), [&](int a, int b) { return d[a] > d[b]; });
        for (size_t q = 0; q < c.size(); ++q) { rd[c[q]] = d[byc[q]]; pi[c[q]] = byc[q]; }
      }
      int rk = 0;
      for (int c = 0; c < nc; ++c) rk += rd[c] * stride[c];
      repk[k] = rk;
      bool id = true;
      for (int i = 0; i < n; ++i) id &= pi[i] == i;
      if (id) continue;
      auto it = lutid.find(pi);
      if (it == lutid.end()) {
        // row r of the representative goes to the row with the relabelled input set
        std::vector<int> sigma(u.rows);
        for (int r = 0; r < u.rows; ++r) {
          unsigned long long m = 0;
          for (int i = 0; i < n; ++i) if (u.row[r] >> i & 1) m |= 1ULL << pi[i];
          sigma[r] = rowidx.at(m);
        }
        Lut L{};
        for (int b = 0; b < 4; ++b)
          for (int x = 0; x < 256; ++x) {
            V o = 0;
            for (int t = 0; t < 8; ++t) if ((x >> t & 1) && 8 * b + t < u.rows) o |= V(1) << sigma[8 * b + t];
            L[b][x] = o;
          }
        it = lutid.emplace(pi, (int)luts.size()).first;
        luts.push_back(L);
      }
      lutk[k] = it->second;
    }
  }
  static V pv(V v, const Lut& L) { return L[0][v & 255] | L[1][v >> 8 & 255] | L[2][v >> 16 & 255] | L[3][v >> 24]; }
  Tab pt(const Tab& t, int K) const {
    if (lutk[K] < 0) return t;
    const Lut& L = luts[lutk[K]];
    Tab o;
    for (int i = 0; i < NE; ++i) o.e[i] = pv(t.e[i], L);
    return o;
  }
  // the tables of key K: R[K] itself, or its representative's tables permuted into buf
  const std::vector<Tab>& view(int K, std::vector<Tab>& buf) const {
    if (repk[K] == K) return R[K];
    const std::vector<Tab>& src = R[repk[K]];
    buf.resize(src.size());
    for (size_t i = 0; i < src.size(); ++i) buf[i] = pt(src[i], K);
    return buf;
  }
  size_t count(int K) const { return R[repk[K]].size(); }
  void digits(int k, std::vector<int>& d) const {
    d.resize(nc);
    for (int c = 0; c < nc; ++c) d[c] = k / stride[c] % (cap[c] + 1);
  }
  bool needed(const std::vector<int>& d) const {
    int in = 0, a = 0, m = 1;
    for (int c = 0; c < u.n; ++c) in += d[c];
    for (int j = 0; j < NP; ++j) { a += d[u.n + j] * m; m *= 5; }
    return in <= maxin[a];
  }
  Tab leaf(int c) const {
    Tab t;
    for (int i = 0; i < NE; ++i) t.e[i] = c < u.n ? u.wire[c] : ((i >> (c - u.n) & 1) ? u.FULL : 0);
    return t;
  }
  bool constant(const Tab& t) const {
    bool z = true, f = true;
    for (int i = 0; i < NE; ++i) { z &= t.e[i] == 0; f &= t.e[i] == u.FULL; }
    return z || f;
  }
  // --prune (sound for minimum circuits): a gate equal on the cared rows to one of its operands, to an input
  // or to a placeholder can be bypassed, and a subtree whose table does not depend on a placeholder it reads
  // can drop those reads (monotone: the root is constant on the box between the two settings). Tables are
  // compared entrywise, which implies equality at the actual placeholder values.
  bool redundant(const Tab& x, const Tab& a, const Tab& b, const std::vector<int>& d) const {
    if (tab_eq(x, a) || tab_eq(x, b)) return true;
    bool flat = true;
    for (int i = 1; i < NE; ++i) flat &= x.e[i] == x.e[0];
    if (flat) for (int i = 0; i < u.n; ++i) if (x.e[0] == u.wire[i]) return true;
    for (int j = 0; j < NP; ++j) {
      if (tab_eq(x, leaf(u.n + j))) return true;
      if (d[u.n + j] == 0) continue;
      bool indep = true;
      for (int i = 0; i < NE; ++i) if (!(i >> j & 1) && x.e[i] != x.e[i | 1 << j]) { indep = false; break; }
      if (indep) return true;
    }
    return false;
  }
  // iterate the proper splits K = B + C with B <= C (as integers); calls fn(B, C), stops when fn returns true
  template <class F> bool splits(const std::vector<int>& d, int K, F fn) const {
    std::vector<int> db(nc, 0);
    while (true) {
      int c = 0;
      while (c < nc && db[c] == d[c]) { db[c] = 0; ++c; }
      if (c == nc) return false;
      ++db[c];
      int B = 0;
      for (int x = 0; x < nc; ++x) B += db[x] * stride[x];
      int C = K - B;
      if (B == K || B > C) continue;
      if (fn(B, C)) return true;
    }
  }
  void run() {
    std::vector<int> order(nkeys), tot(nkeys), d;
    for (int k = 0; k < nkeys; ++k) {
      digits(k, d);
      int s = 0;
      for (int c = 0; c < nc; ++c) s += d[c];
      tot[k] = s; order[k] = k;
    }
    std::stable_sort(order.begin(), order.end(), [&](int a, int b) { return tot[a] < tot[b]; });
    for (int K : order) {
      if (tot[K] == 0) continue;
      digits(K, d);
      if (!needed(d)) continue;
      done[K] = 1;
      if (repk[K] != K) continue;  // --sym: read through the representative (built in this size band)
      if (tot[K] == 1) { int c = 0; while (d[c] == 0) ++c; R[K].push_back(leaf(c)); continue; }
      TabSetT<NE> set(1024);
      std::vector<Tab> bufB, bufC;
      splits(d, K, [&](int B, int C) {
        const std::vector<Tab>& RB = view(B, bufB);
        const std::vector<Tab>& RC = view(C, bufC);
        for (const Tab& a : RB) for (const Tab& b : RC) {
          Tab x, y;
          for (int i = 0; i < NE; ++i) { x.e[i] = a.e[i] & b.e[i]; y.e[i] = a.e[i] | b.e[i]; }
          if (!constant(x) && !(g_prune && redundant(x, a, b, d))) set.insert(x);
          if (!constant(y) && !(g_prune && redundant(y, a, b, d))) set.insert(y);
        }
        return false;
      });
      R[K] = set.list();
    }
    if (g_dump) {
      std::lock_guard<std::mutex> lk(g_dump_mu);
      int id = g_dump_id++;
      std::fprintf(g_dump, "S %d %d %d NE %d cap", id, u.n, nc, NE);
      for (int c = 0; c < nc; ++c) std::fprintf(g_dump, " %d", cap[c]);
      std::fputc('\n', g_dump);
      for (int k = 0; k < nkeys; ++k) if (done[k]) std::fprintf(g_dump, "K %d %d %zu%c", id, k, R[k].size(), '\n');
      std::fflush(g_dump);
    }
  }
  int key(const std::vector<int>& in, const int* ph) const {
    int k = 0;
    for (int c = 0; c < u.n; ++c) k += in[c] * stride[c];
    for (int j = 0; j < NP; ++j) k += ph[j] * stride[u.n + j];
    return k;
  }
  // witness: append the gates of a tree with key K and table t (t in R[K]); returns the root operand
  // (input i -> i, placeholder j -> -1-j, local gate g -> 1000000+g)
  int build(int K, const Tab& t, std::vector<std::array<int, 3>>& g) const {
    std::vector<int> d;
    digits(K, d);
    int s = 0;
    for (int x : d) s += x;
    if (s == 1) { int c = 0; while (d[c] == 0) ++c; return c < u.n ? c : -1 - (c - u.n); }
    int out = -1000000000;
    std::vector<Tab> bufB, bufC;
    splits(d, K, [&](int B, int C) {
      const std::vector<Tab>& RB = view(B, bufB);
      const std::vector<Tab>& RC = view(C, bufC);
      for (const Tab& a : RB) for (const Tab& b : RC) {
        bool isand = true, isor = true;
        for (int i = 0; i < NE; ++i) { isand &= (a.e[i] & b.e[i]) == t.e[i]; isor &= (a.e[i] | b.e[i]) == t.e[i]; }
        if (!isand && !isor) continue;
        int l = build(B, a, g), r = build(C, b, g);
        g.push_back({isand ? 0 : 1, l, r});
        out = 1000000 + (int)g.size() - 1;
        return true;
      }
      return false;
    });
    return out;
  }
  // table at placeholder values: OR over entries i of e[i] AND (v_j for j in i)
  V eval(const Tab& t, const V* v) const {
    V out = 0;
    for (int i = 0; i < NE; ++i) {
      V x = t.e[i];
      for (int j = 0; j < NP; ++j) if (i >> j & 1) x &= v[j];
      out |= x;
    }
    return out;
  }
};

// is there v in vs with v == T on every bit of some D in Ds? Direct scan, or a subset-sum bitmap
// (Y[y] = 1 + index of some v with v^T inside y; then ask Y[~D]) when the scan would cost more than the bitmap.
static bool meet(const std::vector<V>& vs, const std::vector<V>& Ds, V T, int* vi, int* di) {
  if (vs.empty() || Ds.empty()) return false;
  double scan = (double)vs.size() * Ds.size(), build = (double)(1u << g_rows) * g_rows;
  if (scan <= 4 * build) {
    if (g_prof) g_pf.mscan += (uint64_t)scan;
    for (size_t a = 0; a < vs.size(); ++a) {
      V x = vs[a] ^ T;
      for (size_t b = 0; b < Ds.size(); ++b) if ((x & Ds[b]) == 0) { *vi = (int)a; *di = (int)b; return true; }
    }
    return false;
  }
  if (g_prof) ++g_pf.mbit;
  const V FULL = g_rows == 32 ? ~V(0) : (V(1) << g_rows) - 1;
  std::vector<uint32_t> Y((size_t)1 << g_rows, 0);
  for (size_t a = 0; a < vs.size(); ++a) { V y = (vs[a] ^ T) & FULL; if (!Y[y]) Y[y] = (uint32_t)a + 1; }
  for (int b = 0; b < g_rows; ++b)
    for (size_t y = 0; y < Y.size(); ++y) if ((y >> b & 1) && !Y[y]) Y[y] = Y[y ^ ((size_t)1 << b)];
  for (size_t b = 0; b < Ds.size(); ++b)
    if (uint32_t w = Y[~Ds[b] & FULL]) { *vi = (int)w - 1; *di = (int)b; return true; }
  return false;
}

static bool next_sub(std::vector<int>& S, const std::vector<int>& M) {
  for (size_t c = 0; c < M.size(); ++c) { if (S[c] < M[c]) { ++S[c]; return true; } S[c] = 0; }
  return false;
}
static int total(const std::vector<int>& S) { int t = 0; for (int x : S) t += x; return t; }

struct Witness { std::vector<std::array<int, 3>> gates; int output = -1; };

// check one unit against a built DP; with w, also extract a witness circuit
template <int NE> static bool check_one(const Unit& u, const DPT<NE>& dp, const Shape& sh, Witness* w) {
  using Tab = TabT<NE>;
  const int p = sh.p, n = u.n;
  if (p == 0) {
    int K = dp.key(sh.M, nullptr);
    std::vector<Tab> buf;
    for (auto& t : dp.view(K, buf)) if (t.e[0] == u.T) {
      if (w) {
        int root = dp.build(K, t, w->gates);
        for (auto& g : w->gates)
          for (int q = 1; q <= 2; ++q) if (g[q] >= 1000000) g[q] = n + (g[q] - 1000000);
        w->output = n + (root - 1000000);
      }
      return true;
    }
    return false;
  }
  // output tables with t(all 0) inside T inside t(all 1), cached per key
  std::vector<std::vector<Tab>> Fc(dp.nkeys);
  std::vector<char> Fdone(dp.nkeys, 0);
  auto filtered = [&](int K) -> const std::vector<Tab>& {
    if (!Fdone[K]) {
      Fdone[K] = 1;
      for (auto& t0 : dp.R[dp.repk[K]]) {
        Tab t = dp.pt(t0, K);
        if ((t.e[0] & ~u.T) == 0 && (u.T & ~t.e[NE - 1]) == 0) Fc[K].push_back(t);
      }
    }
    return Fc[K];
  };
  std::vector<std::vector<int>> S(p + 1, std::vector<int>(n, 0));
  int keys[4] = {0, 0, 0, 0};
  const int last = p - 1;
  const bool indep_last = sh.reads(last) == 0;  // h_last reads no placeholders: its values are fixed
  V vals[3] = {0, 0, 0};
  int pick[4] = {-1, -1, -1, -1};  // witness: table index per tree (output: index into filtered list)
  const size_t LIM = (size_t)1 << 22;
  std::vector<V> Dacc, vsL;
  std::vector<int> giL;
  std::vector<std::array<int, 4>> Dsrc;  // witness: (F index, pick0, pick1, pick2) per D in Dacc

  // indep_last: the union of all D sets is met against the fixed values of h_last (in chunks)
  auto flush = [&]() -> bool {
    if (Dacc.empty()) return false;
    if (!w) { std::sort(Dacc.begin(), Dacc.end()); Dacc.erase(std::unique(Dacc.begin(), Dacc.end()), Dacc.end()); }
    int vi, di;
    bool ok = meet(vsL, Dacc, u.T, &vi, &di);
    if (ok && w) {
      pick[last] = giL[vi]; pick[p] = Dsrc[di][0];
      for (int q = 0; q < last; ++q) pick[q] = Dsrc[di][1 + q];
    }
    Dacc.clear(); Dsrc.clear();
    return ok;
  };

  std::function<bool(int)> values = [&](int j) -> bool {
    if (j == last) {
      double pt0 = g_prof ? pnow() : 0;
      if (g_prof) ++g_pf.lastc;
      const std::vector<Tab>& F = filtered(keys[p]);
      if (g_prof) g_pf.Fscan += F.size();
      std::vector<V> Ds;
      std::vector<std::array<int, 4>> src;
      for (size_t fi = 0; fi < F.size(); ++fi) {
        const Tab& t = F[fi];
        V lo = 0, hi = 0;
        for (int i = 0; i < NE; ++i) {
          V x = t.e[i];
          for (int q = 0; q < last; ++q) if (i >> q & 1) x &= vals[q];
          hi |= x;
          if (!(i >> last & 1)) lo |= x;
        }
        if ((lo & ~u.T) == 0 && (u.T & ~hi) == 0) {
          Ds.push_back(hi & ~lo);
          if (w) src.push_back({(int)fi, pick[0], pick[1], pick[2]});
        }
      }
      if (g_prof) { double t = pnow(); g_pf.tF += t - pt0; pt0 = t; g_pf.Ds += Ds.size(); }
      if (Ds.empty()) return false;
      if (indep_last) {
        Dacc.insert(Dacc.end(), Ds.begin(), Ds.end());
        if (w) Dsrc.insert(Dsrc.end(), src.begin(), src.end());
        return Dacc.size() > LIM && flush();
      }
      if (!w) { std::sort(Ds.begin(), Ds.end()); Ds.erase(std::unique(Ds.begin(), Ds.end()), Ds.end()); }
      const std::vector<Tab>& G = dp.R[dp.repk[keys[last]]];
      std::vector<V> vs;
      std::vector<int> gi;
      for (size_t a = 0; a < G.size(); ++a) {
        V v = dp.eval(dp.pt(G[a], keys[last]), vals);
        if (v != 0 && v != u.FULL) { vs.push_back(v); gi.push_back((int)a); }
      }
      if (g_prof) { double t = pnow(); g_pf.tG += t - pt0; pt0 = t; g_pf.Gev += G.size(); g_pf.vs += vs.size(); }
      int vi, di;
      bool mok = meet(vs, Ds, u.T, &vi, &di);
      if (g_prof) g_pf.tM += pnow() - pt0;
      if (!mok) return false;
      if (w) { pick[last] = gi[vi]; pick[p] = src[di][0]; }
      return true;
    }
    double pm0 = g_prof ? pnow() : 0;
    const std::vector<Tab>& G = dp.R[dp.repk[keys[j]]];
    std::vector<std::pair<V, int>> vs;
    for (size_t a = 0; a < G.size(); ++a) {
      V v = dp.eval(dp.pt(G[a], keys[j]), vals);
      if (v != 0 && v != u.FULL) vs.push_back({v, (int)a});
    }
    std::sort(vs.begin(), vs.end(), [](const std::pair<V, int>& x, const std::pair<V, int>& y) { return x.first < y.first; });
    vs.erase(std::unique(vs.begin(), vs.end(),
                         [](const std::pair<V, int>& x, const std::pair<V, int>& y) { return x.first == y.first; }),
             vs.end());
    if (g_prof) { g_pf.tMid += pnow() - pm0; ++g_pf.midc; g_pf.midev += G.size(); g_pf.mids += vs.size(); }
    for (auto& pr : vs) {
      vals[j] = pr.first; pick[j] = pr.second;
      if (values(j + 1)) return true;
    }
    vals[j] = 0;
    return false;
  };

  // --fold (exact, opt-in): FL[j] holds the output-tree tables with v_0..v_{j-1} folded into the entries
  // without those placeholder bits, kept only if t(rest = 0) inside T inside t(rest = all ones) (monotone, so
  // necessary for every later choice of values). GL[j] does the same for h_last's tables
  // (no filter). Folding preserves eval at any later values, so each v_last check sees the same lo/hi/D as
  // values(); the inner loops scan the short folded lists instead of every table.
  struct FT { Tab t; int i; };
  std::vector<std::vector<FT>> FL(p + 1), GL(p + 1);
  auto fold = [&](const std::vector<FT>& in, int j, V v, bool filt, std::vector<FT>& out) {
    out.clear();
    for (const FT& f : in) {
      FT g = f;
      for (int i = 0; i < NE; ++i)
        if (i >> j & 1) { g.t.e[i ^ (1 << j)] |= g.t.e[i] & v; g.t.e[i] = 0; }
      if (filt) {
        V hi = 0;
        for (int i = 0; i < NE; ++i) hi |= g.t.e[i];
        if ((g.t.e[0] & ~u.T) != 0 || (u.T & ~hi) != 0) continue;
      }
      out.push_back(g);
    }
  };
  // the filter after folding v into placeholder j, as a window on v: with A (B) the OR of the entries without
  // (with) bit j, fold(t)[0] = e[0] | (e[1<<j] & v) must lie inside T and T inside A | (B & v), i.e.
  // need = T & ~A inside v (and inside B) and forbid = e[1<<j] & ~T disjoint from v. v is never 0, so
  // forbid = all ones rejects the table for every v.
  struct Win { V need, forbid; };
  std::vector<std::vector<Win>> WL(p + 1);
  auto windows = [&](const std::vector<FT>& in, int j, std::vector<Win>& out) {
    out.resize(in.size());
    for (size_t a = 0; a < in.size(); ++a) {
      const Tab& t = in[a].t;
      V A = 0, B = 0;
      for (int i = 0; i < NE; ++i) { if (i >> j & 1) B |= t.e[i]; else A |= t.e[i]; }
      V need = u.T & ~A, forbid = t.e[1 << j] & ~u.T;
      if ((need & ~B) != 0 || (t.e[0] & ~u.T) != 0) forbid = ~V(0);
      out[a] = {need, forbid};
    }
  };
  auto fold_win = [&](const std::vector<FT>& in, const std::vector<Win>& wn, int j, V v, std::vector<FT>& out) {
    out.clear();
    for (size_t a = 0; a < in.size(); ++a) {
      if ((wn[a].need & ~v) != 0 || (wn[a].forbid & v) != 0) continue;
      FT g = in[a];
      for (int i = 0; i < NE; ++i)
        if (i >> j & 1) { g.t.e[i ^ (1 << j)] |= g.t.e[i] & v; g.t.e[i] = 0; }
      out.push_back(g);
    }
  };
  // buffers reused across calls (the last level is a leaf, and each middle depth owns its own list)
  std::vector<V> fDs, fvs;
  std::vector<std::array<int, 4>> fsrc;
  std::vector<int> fgi;
  std::vector<std::vector<std::pair<V, int>>> fmid(p + 1);
  std::function<bool(int)> values_fold = [&](int j) -> bool {
    if (j == last) {
      double pt0 = g_prof ? pnow() : 0;
      const std::vector<FT>& F = FL[j];
      if (g_prof) { ++g_pf.lastc; g_pf.Fscan += F.size(); }
      std::vector<V>& Ds = fDs;
      std::vector<std::array<int, 4>>& src = fsrc;
      Ds.clear(); src.clear();
      for (const FT& f : F) {
        V lo = 0, hi = 0;
        for (int i = 0; i < NE; ++i) { hi |= f.t.e[i]; if (!(i >> last & 1)) lo |= f.t.e[i]; }
        if ((lo & ~u.T) == 0 && (u.T & ~hi) == 0) {
          Ds.push_back(hi & ~lo);
          if (w) src.push_back({f.i, pick[0], pick[1], pick[2]});
        }
      }
      if (g_prof) { double t = pnow(); g_pf.tF += t - pt0; pt0 = t; g_pf.Ds += Ds.size(); }
      if (Ds.empty()) return false;
      if (indep_last) {
        Dacc.insert(Dacc.end(), Ds.begin(), Ds.end());
        if (w) Dsrc.insert(Dsrc.end(), src.begin(), src.end());
        return Dacc.size() > LIM && flush();
      }
      if (!w) { std::sort(Ds.begin(), Ds.end()); Ds.erase(std::unique(Ds.begin(), Ds.end()), Ds.end()); }
      std::vector<V>& vs = fvs;
      std::vector<int>& gi = fgi;
      vs.clear(); gi.clear();
      for (const FT& g : GL[j]) {  // every placeholder h_last reads is folded: its value is entry 0
        V v = g.t.e[0];
        if (v != 0 && v != u.FULL) { vs.push_back(v); gi.push_back(g.i); }
      }
      if (g_prof) { double t = pnow(); g_pf.tG += t - pt0; pt0 = t; g_pf.Gev += GL[j].size(); g_pf.vs += vs.size(); }
      int vi, di;
      bool mok = meet(vs, Ds, u.T, &vi, &di);
      if (g_prof) g_pf.tM += pnow() - pt0;
      if (!mok) return false;
      if (w) { pick[last] = gi[vi]; pick[p] = src[di][0]; }
      return true;
    }
    double pm0 = g_prof ? pnow() : 0;
    const std::vector<Tab>& G = dp.R[dp.repk[keys[j]]];
    std::vector<std::pair<V, int>>& vs = fmid[j];
    vs.clear();
    for (size_t a = 0; a < G.size(); ++a) {
      V v = dp.eval(dp.pt(G[a], keys[j]), vals);
      if (v != 0 && v != u.FULL) vs.push_back({v, (int)a});
    }
    std::sort(vs.begin(), vs.end(), [](const std::pair<V, int>& x, const std::pair<V, int>& y) { return x.first < y.first; });
    vs.erase(std::unique(vs.begin(), vs.end(),
                         [](const std::pair<V, int>& x, const std::pair<V, int>& y) { return x.first == y.first; }),
             vs.end());
    if (g_prof) { g_pf.tMid += pnow() - pm0; ++g_pf.midc; g_pf.midev += G.size(); g_pf.mids += vs.size(); }
    if (!vs.empty()) windows(FL[j], j, WL[j]);
    for (auto& pr : vs) {
      vals[j] = pr.first; pick[j] = pr.second;
      double pf0 = g_prof ? pnow() : 0;
      if (g_foldcheck) {  // debug: the window filter must keep exactly the tables the direct filter keeps
        std::vector<FT> ref;
        fold(FL[j], j, pr.first, true, ref);
        fold_win(FL[j], WL[j], j, pr.first, FL[j + 1]);
        bool same = ref.size() == FL[j + 1].size();
        for (size_t a = 0; same && a < ref.size(); ++a) same = ref[a].i == FL[j + 1][a].i && tab_eq(ref[a].t, FL[j + 1][a].t);
        if (!same) { std::fprintf(stderr, "FOLD WINDOW MISMATCH %s\n", sh.str().c_str()); std::abort(); }
      } else
        fold_win(FL[j], WL[j], j, pr.first, FL[j + 1]);
      bool emp = FL[j + 1].empty();
      if (!emp && !indep_last) fold(GL[j], j, pr.first, false, GL[j + 1]);
      if (g_prof) { g_pf.tFold += pnow() - pf0; ++g_pf.folds; g_pf.foldemp += emp; }
      if (emp) continue;
      if (values_fold(j + 1)) return true;
    }
    vals[j] = 0;
    return false;
  };

  std::vector<int> mins(p + 1), restmin(p + 2, 0);
  for (int t = 0; t <= p; ++t) mins[t] = sh.min_inputs(t);
  for (int t = p; t >= 0; --t) restmin[t] = restmin[t + 1] + mins[t];
  // split the input multiset over trees 0..p (the output tree p takes the remainder)
  std::function<bool(int, const std::vector<int>&)> assign = [&](int t, const std::vector<int>& left) -> bool {
    if (t == p) {
      S[p] = left;
      if (total(left) < mins[p]) return false;
      keys[p] = dp.key(S[p], sh.r[p]);
      if (!dp.done[keys[p]] || filtered(keys[p]).empty()) return false;
      if (g_prof) ++g_pf.splits;
      Dacc.clear(); Dsrc.clear();
      if (indep_last) {
        vsL.clear(); giL.clear();
        const std::vector<Tab>& G = dp.R[dp.repk[keys[last]]];
        for (size_t a = 0; a < G.size(); ++a) {
          V v = dp.pt(G[a], keys[last]).e[0];
          if (v != 0 && v != u.FULL) { vsL.push_back(v); giL.push_back((int)a); }
        }
      }
      if (g_fold) {
        const std::vector<Tab>& F0 = filtered(keys[p]);
        FL[0].clear();
        for (size_t fi = 0; fi < F0.size(); ++fi) FL[0].push_back({F0[fi], (int)fi});
        if (!indep_last) {
          GL[0].clear();
          const std::vector<Tab>& G = dp.R[dp.repk[keys[last]]];
          for (size_t a = 0; a < G.size(); ++a) GL[0].push_back({dp.pt(G[a], keys[last]), (int)a});
        }
        if (values_fold(0)) return true;
        return indep_last && flush();
      }
      if (values(0)) return true;
      return indep_last && flush();
    }
    std::vector<int>& St = S[t];
    std::fill(St.begin(), St.end(), 0);
    int lt = total(left);
    std::vector<int> nl(n);
    do {
      int st = total(St);
      if (st < mins[t] || lt - st < restmin[t + 1]) continue;
      keys[t] = dp.key(St, sh.r[t]);
      if (!dp.done[keys[t]] || dp.count(keys[t]) == 0) continue;
      for (int c = 0; c < n; ++c) nl[c] = left[c] - St[c];
      if (assign(t + 1, nl)) return true;
    } while (next_sub(St, left));
    return false;
  };
  if (!assign(0, sh.M)) return false;
  if (w) {
    // trees h_0..h_{p-1} in order, then the output tree; placeholder j -> root wire of h_j
    std::vector<int> rootw(p, -1);
    for (int t = 0; t <= p; ++t) {
      const Tab tab = t < p ? dp.pt(dp.R[dp.repk[keys[t]]][pick[t]], keys[t]) : filtered(keys[p])[pick[p]];
      std::vector<std::array<int, 3>> lg;
      int root = dp.build(keys[t], tab, lg);
      int base = n + (int)w->gates.size();
      auto mapop = [&](int o) { return o >= 1000000 ? base + (o - 1000000) : o >= 0 ? o : rootw[-1 - o]; };
      for (auto& g : lg) w->gates.push_back({g[0], mapop(g[1]), mapop(g[2])});
      int rw = mapop(root);
      if (t < p) rootw[t] = rw; else w->output = rw;
    }
  }
  return true;
}

template <int NE> static std::vector<char> check_shape(const std::vector<const Unit*>& us, const Shape& sh,
                                                       std::vector<Witness>& wit) {
  auto t0 = std::chrono::steady_clock::now();
  DPT<NE> dp(*us[0], sh);
  dp.run();
  double tdp = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  std::vector<char> ok(us.size(), 0);
  wit.assign(us.size(), {});
  g_pf = Prof();
  for (size_t j = 0; j < us.size(); ++j)
    if (check_one<NE>(*us[j], dp, sh, nullptr)) { ok[j] = 1; check_one<NE>(*us[j], dp, sh, &wit[j]); }
  if (g_verbose && (sh.p >= 1 || tdp > 5)) {
    size_t tot = 0, mx = 0;
    for (auto& r : dp.R) { tot += r.size(); mx = std::max(mx, r.size()); }
    int nok = 0;
    for (char c : ok) nok += c;
    std::fprintf(stderr, "shape %s dp %.2fs total %.2fs tables %zu max %zu sat %d/%zu\n", sh.str().c_str(), tdp,
                 std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(), tot, mx, nok,
                 us.size());
    if (g_prof && sh.p >= 1)
      std::fprintf(stderr,
                   "  prof %s: splits %llu | mid calls %llu evals %llu distinct %llu %.2fs | last calls %llu Fscan %llu "
                   "Ds %llu %.2fs | Gevals %llu vs %llu %.2fs | meet %.2fs scanops %llu bitmaps %llu | folds %llu empty %llu %.2fs%c",
                   sh.str().c_str(), (unsigned long long)g_pf.splits, (unsigned long long)g_pf.midc,
                   (unsigned long long)g_pf.midev, (unsigned long long)g_pf.mids, g_pf.tMid,
                   (unsigned long long)g_pf.lastc, (unsigned long long)g_pf.Fscan, (unsigned long long)g_pf.Ds, g_pf.tF,
                   (unsigned long long)g_pf.Gev, (unsigned long long)g_pf.vs, g_pf.tG, g_pf.tM,
                   (unsigned long long)g_pf.mscan, (unsigned long long)g_pf.mbit, (unsigned long long)g_pf.folds, (unsigned long long)g_pf.foldemp, g_pf.tFold, '\n');
  }
  return ok;
}

static std::vector<char> check(const std::vector<const Unit*>& us, const Shape& sh, std::vector<Witness>& wit) {
  switch (sh.p) {
    case 0: return check_shape<1>(us, sh, wit);
    case 1: return check_shape<2>(us, sh, wit);
    case 2: return check_shape<4>(us, sh, wit);
    default: return check_shape<8>(us, sh, wit);
  }
}

// simulate a witness on the cared rows: AND/OR gates reading earlier wires, output == T, size == k
static bool verify(const Unit& u, const Witness& w, int k) {
  if ((int)w.gates.size() != k) return false;
  std::vector<V> val(u.wire);
  for (auto& g : w.gates) {
    int l = g[1], r = g[2];
    if (l < 0 || r < 0 || l >= (int)val.size() || r >= (int)val.size() || (g[0] != 0 && g[0] != 1)) return false;
    val.push_back(g[0] == 0 ? (val[l] & val[r]) : (val[l] | val[r]));
  }
  return w.output >= 0 && w.output < (int)val.size() && val[w.output] == u.T;
}

struct Task { int group, s, shape; };

int main(int argc, char** argv) {
  if (const char* dp = std::getenv("TREE_DP_DUMP")) g_dump = std::fopen(dp, "w");
  g_prof = std::getenv("TREE_DP_PROF") != nullptr;
  g_foldcheck = std::getenv("TREE_DP_FOLDCHECK") != nullptr;
  const char* only_shape = std::getenv("TREE_DP_SHAPE");  // profiling: run only the shape with this str()
  int smax = 2, threads = 11, heavy = 4;
  bool to_budget = false;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--smax" && i + 1 < argc) smax = std::atoi(argv[++i]);
    else if (a == "--threads" && i + 1 < argc) threads = std::atoi(argv[++i]);
    else if (a == "--heavy" && i + 1 < argc) heavy = std::atoi(argv[++i]);  // max concurrent p >= 1 shapes
    else if (a == "--to-budget") to_budget = true;  // per unit, stop at s = BUDGET - (n-1)
    else if (a == "--verbose") g_verbose = true;
    else if (a == "--prune") g_prune = true;  // drop redundant gates (sound for minimum circuits; opt-in)
    else if (a == "--sym") g_sym = true;  // store one key per twin-input orbit (memory; opt-in)
    else if (a == "--fold") g_fold = true;  // fold and filter output tables per placeholder value (time; opt-in)
  }
  if (smax < 0 || smax > 3 || heavy < 1) { std::fprintf(stderr, "--smax must be 0..3, --heavy >= 1\n"); return 2; }
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
  std::vector<Witness> wits(units.size());
  for (size_t i = 0; i < units.size(); ++i)
    if (skip[i]) std::printf("{\"id\":\"%s\",\"status\":\"skip\"}\n", units[i].id.c_str());
  // units with the same n and cared-row wires share every DP: one task per (group, shape)
  std::map<std::vector<V>, std::vector<int>> gmap;
  for (int i = 0; i < (int)units.size(); ++i) if (!skip[i]) {
    std::vector<V> key = units[i].wire;
    key.push_back((V)units[i].n);
    gmap[key].push_back(i);
  }
  std::vector<std::vector<int>> groups;
  for (auto& kv : gmap) groups.push_back(kv.second);
  if (g_verbose) std::fprintf(stderr, "%zu units in %zu wire groups\n", units.size(), groups.size());
  std::mutex mu;
  std::condition_variable cv;
  int heavy_running = 0;
  for (int s = 0; s <= smax; ++s) {
    std::vector<std::vector<Shape>> gshapes(groups.size());
    std::vector<Task> tasks;
    for (int gi = 0; gi < (int)groups.size(); ++gi) {
      bool any = false;
      for (int i : groups[gi]) if (found[i] < 0 && s <= ucap[i]) any = true;
      if (!any) continue;
      gshapes[gi] = shapes_for(units[groups[gi][0]].n, s);
      for (int k = 0; k < (int)gshapes[gi].size(); ++k)
        if (!only_shape || gshapes[gi][k].str() == only_shape) tasks.push_back({gi, s, k});
    }
    // heavy shapes first (largest p, then fewest extra inputs = most shared reads)
    std::stable_sort(tasks.begin(), tasks.end(), [&](const Task& a, const Task& b) {
      return gshapes[a.group][a.shape].p > gshapes[b.group][b.shape].p;
    });
    if (g_verbose) std::fprintf(stderr, "level s=%d: %zu tasks\n", s, tasks.size());
    std::atomic<size_t> next{0};
    auto worker = [&]() {
      for (size_t t; (t = next++) < tasks.size();) {
        const Task& k = tasks[t];
        const Shape& sh = gshapes[k.group][k.shape];
        bool hv = sh.p >= 1;
        std::vector<int> mem;
        std::vector<const Unit*> us;
        {
          std::unique_lock<std::mutex> g(mu);
          if (hv) { cv.wait(g, [&] { return heavy_running < heavy; }); ++heavy_running; }
          for (int i : groups[k.group]) if (found[i] < 0 && k.s <= ucap[i]) { mem.push_back(i); us.push_back(&units[i]); }
          if (mem.empty()) { if (hv) { --heavy_running; cv.notify_all(); } continue; }
        }
        auto t0 = std::chrono::steady_clock::now();
        std::vector<Witness> w;
        std::vector<char> ok = check(us, sh, w);
        double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        {
          std::lock_guard<std::mutex> g(mu);
          if (hv) --heavy_running;
          for (size_t j = 0; j < mem.size(); ++j) {
            int i = mem[j];
            if (ok[j] && found[i] < 0) {
              if (!verify(units[i], w[j], units[i].n - 1 + k.s))
                std::fprintf(stderr, "WITNESS CHECK FAILED %s %s\n", units[i].id.c_str(), sh.str().c_str());
              else { found[i] = k.s; wits[i] = w[j]; }
            }
            secs[i] += dt / mem.size();  // shared DP time split evenly
          }
        }
        if (hv) cv.notify_all();
      }
    };
    std::vector<std::thread> pool;
    for (int i = 0; i < threads; ++i) pool.emplace_back(worker);
    for (auto& th : pool) th.join();
    if (g_verbose) std::fprintf(stderr, "level s=%d done\n", s);
    // print every unit whose answer is now final, so a stopped run keeps its finished units
    for (size_t i = 0; i < units.size(); ++i) {
      if (printed[i] || skip[i]) continue;
      const Unit& u = units[i];
      if (found[i] >= 0) {
        std::string g = "[";
        for (size_t q = 0; q < wits[i].gates.size(); ++q)
          g += (q ? ",[" : "[") + std::to_string(wits[i].gates[q][0]) + "," + std::to_string(wits[i].gates[q][1]) +
               "," + std::to_string(wits[i].gates[q][2]) + "]";
        g += "]";
        std::printf("{\"id\":\"%s\",\"n\":%d,\"min_k\":%d,\"cpu_seconds\":%.2f,\"gates\":%s,\"output\":%d}\n",
                    u.id.c_str(), u.n, u.n - 1 + found[i], secs[i], g.c_str(), wits[i].output);
      } else if (s >= ucap[i]) {
        std::printf("{\"id\":\"%s\",\"n\":%d,\"min_k\":null,\"gt\":%d,\"cpu_seconds\":%.2f}\n", u.id.c_str(), u.n,
                    u.n - 1 + ucap[i], secs[i]);
      } else continue;
      printed[i] = 1;
    }
    std::fflush(stdout);
  }
  return 0;
}
