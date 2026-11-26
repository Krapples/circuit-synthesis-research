// Feature-quotient bipartiteness, conflict-directed minimum support, and root-partition screening for residual
// distinction problems over correlated available signals (port of quotient_completion_research/quotient.py and the
// root-partition theorem of slack_one_completion_research).
//
// Problem: rows u carry signatures w(u) over m available feature columns (bit i = value of feature i on row u);
// a set E of conflict edges requires one additional signal to differ on each edge. Features are correlated (they
// are the actual observed values on the rows, not independent inputs).
//
// * Quotient theorem. A signal that is a Boolean function of the features in Z exists iff the graph obtained by
//   identifying rows with equal Z-signatures (keeping loops) is bipartite. Equivalently, the signed graph with
//   conflict edges (parity 1) and equality edges inside each Z-class (parity 0) is balanced.
// * Walk certificate. An unbalanced signed graph has a closed walk of odd total parity. If B is the union of
//   w(i) XOR w(j) over its parity-0 edges, every feasible support must intersect B (otherwise all those equality
//   edges survive and the walk forces a bit to equal its complement). B = 0 means no completion from these features.
// * Minimum support s*: exact minimum hitting set over pairwise difference masks plus learned walk masks, repeated
//   until the hitting set is feasible. Each learned mask is necessary and excludes the candidate that produced it.
// * Conditional bound: a trimmed completion from these sources with g binary AND gates (free complements) reads
//   s >= s* distinct sources and g >= s - 1, so g >= max(0, s* - 1). This is a fixed-interface bound for the given
//   available signals and conflicts only; it is NOT an unrestricted circuit lower bound.
// * Fixed-target remark. When E is all (positive, negative) pairs of a fixed target, the quotient is bipartite iff no
//   Z-class mixes the labels, i.e. iff Z covers every pairwise difference: parity adds nothing over pair cover.
// * Root partition. For source groups A, B (possibly overlapping, correlated) and an orientation (positive T, negative
//   F) of every active component, arbitrary operands a(A), c(B) realize the oriented target as a AND c iff
//   F & L_A(T) & L_B(T) = 0, where L_A(T) is the set of active rows sharing an A-signature with a row of T. Both
//   orientations of every component are enumerated (this includes both global output phases); above the component
//   cap the screen returns unknown. Passing says nothing about a bounded-size realization.
#pragma once

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <deque>
#include <map>
#include <optional>
#include <stdexcept>
#include <tuple>
#include <utility>
#include <vector>

namespace fq {

using u64 = std::uint64_t;
using Edge = std::pair<int, int>;

struct WalkStep { int from, to, parity; };
struct Obstruction { u64 mask = 0; std::vector<WalkStep> walk; };

// Signed-graph balance test for support z. Returns nullopt when the quotient is bipartite, else an odd closed walk
// and its equality-edge difference mask (which never meets z).
inline std::optional<Obstruction> certificate(const std::vector<u64>& rows, const std::vector<Edge>& edges, u64 z) {
  const int n = int(rows.size());
  std::vector<std::vector<std::pair<int, int>>> adj(n);
  auto add = [&](int u, int v, int p) { adj[u].push_back({v, p}); adj[v].push_back({u, p}); };
  for (auto [u, v] : edges) add(u, v, 1);
  std::map<u64, int> seen;
  for (int u = 0; u < n; ++u) {
    u64 s = rows[u] & z;
    auto it = seen.find(s);
    if (it != seen.end()) add(u, it->second, 0);
    else seen.emplace(s, u);
  }
  std::vector<int> val(n, -1);
  std::vector<std::pair<int, int>> par(n, {-1, 0});
  for (int root = 0; root < n; ++root) {
    if (val[root] >= 0) continue;
    val[root] = 0;
    std::deque<int> q{root};
    while (!q.empty()) {
      int u = q.front(); q.pop_front();
      for (auto [v, p] : adj[u]) {
        if (val[v] < 0) { val[v] = val[u] ^ p; par[v] = {u, p}; q.push_back(v); continue; }
        if ((val[u] ^ val[v]) == p) continue;
        auto path = [&](int x) {  // x -> root
          std::vector<WalkStep> a;
          while (par[x].first >= 0) { a.push_back({x, par[x].first, par[x].second}); x = par[x].first; }
          return a;
        };
        Obstruction ob;
        ob.walk = path(u);
        auto pv = path(v);
        for (auto it = pv.rbegin(); it != pv.rend(); ++it) ob.walk.push_back({it->to, it->from, it->parity});
        ob.walk.push_back({v, u, p});
        for (auto& s : ob.walk) if (s.parity == 0) ob.mask |= rows[s.from] ^ rows[s.to];
        if (ob.mask & z) throw std::logic_error("walk mask meets the support");
        return ob;
      }
    }
  }
  return std::nullopt;
}

// Independent quotient coloring on signatures (no signed equality edges).
inline bool quotient_bipartite(const std::vector<u64>& rows, const std::vector<Edge>& edges, u64 z) {
  std::map<u64, std::vector<u64>> d;
  for (auto [u, v] : edges) {
    u64 a = rows[u] & z, b = rows[v] & z;
    if (a == b) return false;
    d[a].push_back(b); d[b].push_back(a);
  }
  std::map<u64, int> c;
  for (auto& [a, _] : d) {
    if (c.count(a)) continue;
    c[a] = 0;
    std::vector<u64> todo{a};
    while (!todo.empty()) {
      u64 u = todo.back(); todo.pop_back();
      for (u64 v : d[u]) {
        auto it = c.find(v);
        if (it == c.end()) { c[v] = 1 ^ c[u]; todo.push_back(v); }
        else if (it->second == c[u]) return false;
      }
    }
  }
  return true;
}

// Independent replay of a learned obstruction: the walk is closed, its parity-1 steps are conflict edges, its
// parity-0 steps join rows, the total parity is odd, and the mask is the union of parity-0 differences. Then every
// support disjoint from the mask keeps all parity-0 steps as equalities and is infeasible.
inline bool replay(const std::vector<u64>& rows, const std::vector<Edge>& edges, const Obstruction& ob) {
  if (ob.walk.empty()) return false;
  int parity = 0;
  u64 mask = 0;
  for (std::size_t i = 0; i < ob.walk.size(); ++i) {
    const auto& s = ob.walk[i];
    if (s.from < 0 || s.to < 0 || s.from >= int(rows.size()) || s.to >= int(rows.size())) return false;
    if (ob.walk[(i + 1) % ob.walk.size()].from != s.to) return false;
    if (s.parity == 1) {
      bool found = std::find(edges.begin(), edges.end(), Edge{s.from, s.to}) != edges.end() ||
                   std::find(edges.begin(), edges.end(), Edge{s.to, s.from}) != edges.end();
      if (!found) return false;
    } else if (s.parity == 0) {
      mask |= rows[s.from] ^ rows[s.to];
    } else {
      return false;
    }
    parity ^= s.parity;
  }
  return parity == 1 && mask == ob.mask;
}

inline std::vector<u64> minimize_masks(std::vector<u64> cs) {
  std::sort(cs.begin(), cs.end(), [](u64 a, u64 b) {
    return std::make_pair(std::popcount(a), a) < std::make_pair(std::popcount(b), b);
  });
  cs.erase(std::unique(cs.begin(), cs.end()), cs.end());
  std::vector<u64> out;
  for (u64 c : cs) {
    bool dominated = false;
    for (u64 b : out) if ((c & b) == b) { dominated = true; break; }
    if (!dominated) out.push_back(c);
  }
  return out;
}

// Exact minimum-cardinality hitting set (ties: smallest mask value). nullopt: impossible (an empty set) or the work
// limit was exhausted (`exhausted` tells which).
class HittingSet {
 public:
  explicit HittingSet(long work_limit) : work_(work_limit) {}
  bool exhausted = false;
  std::optional<u64> solve(const std::vector<u64>& cs) {
    if (cs.empty()) return u64{0};
    if (cs[0] == 0) return std::nullopt;
    if (auto it = memo_.find(cs); it != memo_.end()) return it->second;
    if (--work_ < 0) { exhausted = true; return std::nullopt; }
    std::optional<u64> best;
    for (u64 c = cs[0]; c; c &= c - 1) {
      u64 b = c & (0 - c);
      std::vector<u64> rest;
      for (u64 x : cs) if (!(x & b)) rest.push_back(x);
      auto z = solve(rest);
      if (exhausted) return std::nullopt;
      if (z) {
        u64 zz = *z | b;
        if (!best || std::make_pair(std::popcount(zz), zz) < std::make_pair(std::popcount(*best), *best)) best = zz;
      }
    }
    memo_.emplace(cs, best);
    return best;
  }

 private:
  long work_;
  std::map<std::vector<u64>, std::optional<u64>> memo_;
};

enum class Status { constant, feasible, impossible, unknown };
inline const char* name(Status s) {
  return s == Status::constant ? "constant" : s == Status::feasible ? "feasible" : s == Status::impossible ? "impossible" : "unknown";
}

struct Support {
  Status status = Status::unknown;
  u64 support = 0;          // a minimum feasible support (status feasible)
  int s = -1;               // its size; constant: 0
  u64 pair_support = 0;     // minimum pair-cover hitting set (ignores parity)
  int pair_s = -1;
  int calls = 0;            // quotient tests
  std::vector<Obstruction> learned;
  // Conditional additional-gate lower bound at this fixed interface; -1 when none follows (unknown/impossible).
  int gate_bound() const { return status == Status::constant ? 0 : status == Status::feasible ? std::max(0, s - 1) : -1; }
};

inline Support min_support(const std::vector<u64>& rows, const std::vector<Edge>& edges, int max_calls = 1 << 16,
                           long hs_work = 1 << 20) {
  Support r;
  if (edges.empty()) { r.status = Status::constant; r.s = 0; r.pair_s = 0; return r; }
  std::vector<u64> cs;
  for (auto [u, v] : edges) cs.push_back(rows[u] ^ rows[v]);
  cs = minimize_masks(cs);
  HittingSet hs(hs_work);
  auto z = hs.solve(cs);
  if (!z) { r.status = hs.exhausted ? Status::unknown : Status::impossible; return r; }
  r.pair_support = *z; r.pair_s = std::popcount(*z);
  while (true) {
    if (++r.calls > max_calls) { r.status = Status::unknown; return r; }
    auto ob = certificate(rows, edges, *z);
    if (!ob) { r.status = Status::feasible; r.support = *z; r.s = std::popcount(*z); return r; }
    cs.push_back(ob->mask);
    r.learned.push_back(std::move(*ob));
    cs = minimize_masks(cs);
    HittingSet h2(hs_work);
    z = h2.solve(cs);
    if (!z) { r.status = h2.exhausted ? Status::unknown : Status::impossible; return r; }
  }
}

// Root-partition screen for an AND root with operand source groups A, B (feature masks).
struct Partition {
  bool consistent = true;                  // conflict graph bipartite on rows
  std::vector<std::array<std::vector<int>, 2>> components;  // both sides of each active component
  std::vector<int> active;
};
inline Partition components(int nrows, const std::vector<Edge>& edges) {
  Partition P;
  std::vector<std::vector<int>> adj(nrows);
  for (auto [u, v] : edges) { adj[u].push_back(v); adj[v].push_back(u); }
  std::vector<int> side(nrows, -1);
  for (int i = 0; i < nrows; ++i) {
    if (adj[i].empty() || side[i] >= 0) continue;
    std::array<std::vector<int>, 2> comp;
    side[i] = 0;
    std::vector<int> todo{i};
    while (!todo.empty()) {
      int u = todo.back(); todo.pop_back();
      comp[side[u]].push_back(u);
      P.active.push_back(u);
      for (int v : adj[u]) {
        if (side[v] < 0) { side[v] = side[u] ^ 1; todo.push_back(v); }
        else if (side[v] == side[u]) P.consistent = false;
      }
    }
    P.components.push_back(std::move(comp));
  }
  return P;
}

enum class Screen { pass, reject, unknown };
inline const char* name(Screen s) { return s == Screen::pass ? "pass" : s == Screen::reject ? "reject" : "unknown"; }

inline Screen root_partition(const std::vector<u64>& rows, const Partition& P, u64 A, u64 B, int component_cap = 8) {
  if (!P.consistent) return Screen::reject;  // no signal at all satisfies the conflicts
  if (int(P.components.size()) > component_cap) return Screen::unknown;
  const int c = int(P.components.size());
  std::vector<char> pos(rows.size(), 0);
  for (u64 o = 0; o < (u64(1) << c); ++o) {
    std::fill(pos.begin(), pos.end(), char(0));
    for (int j = 0; j < c; ++j) for (int u : P.components[j][(o >> j) & 1]) pos[u] = 1;
    // L_G(T): signatures (restricted to G) carried by positive rows.
    std::map<u64, char> la, lb;
    for (int u : P.active) if (pos[u]) { la[rows[u] & A] = 1; lb[rows[u] & B] = 1; }
    bool ok = true;
    for (int u : P.active)
      if (!pos[u] && la.count(rows[u] & A) && lb.count(rows[u] & B)) { ok = false; break; }
    if (ok) return Screen::pass;
  }
  return Screen::reject;
}

}  // namespace fq
