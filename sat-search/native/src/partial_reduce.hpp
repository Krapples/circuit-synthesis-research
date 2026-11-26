// Exact standalone partial-AIG reductions and incomplete signed-permutation normalization (native follow-up handoff,
// reduce.py / canonical()). A partial function (p, c, n): positive rows p within care rows c, little-endian rows.
// K = minimum standalone AND count over independent primary inputs (free complements and constants).
//
// Rules, each removing input i (the handoff's proofs; audited here by exhaustive checks through 3 inputs):
//   zero   cofactors consistent on their overlap and some constant or signed surviving literal s covers the merged
//          care, ((c0 & ~s) | (c1 & s)) == c0 | c1: K(f) = K(merged).  (Consistency alone is only an upper bound.)
//   peel   i mandatory (conflicting aligned cared rows), neutral slice g nonconstant on care, opposite slice
//          constant v on care: K(f) = 1 + K(g); f = g AND/OR the literal of i.
//   module i mandatory, g nonconstant, and the opposite slice with its two x_j slices merged is consistent and covered
//          by the x_j = v slice of g with equal labels: K(f) = 1 + K(g); x_j is replaced by x_j AND/OR literal(i).
// The offsets are identities for standalone exact minima only; they say nothing about a heuristic witness or about
// cost over shared paid gates. A core result of UNKNOWN or a heuristic bound keeps that status after lifting.
#pragma once

#include <algorithm>
#include <array>
#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

#include "orientation_witness.hpp"

namespace preduce {

using orient::TT;

// Numeric (big-integer) comparison of tables, matching Python int ordering.
inline int cmp_num(const TT& a, const TT& b) {
  for (int i = 3; i >= 0; --i)
    if (a.w[i] != b.w[i]) return a.w[i] < b.w[i] ? -1 : 1;
  return 0;
}

inline bool consistent(const TT& p0, const TT& c0, const TT& p1, const TT& c1) { return !((p0 ^ p1) & c0 & c1).any(); }

enum Kind { kModule = 0, kPeel = 1, kZero = 2 };  // alphabetical, as Python orders the kind strings

struct Rule {
  Kind kind;
  int i;            // removed input (index in the current table)
  TT p, c;          // reduced table on n-1 inputs
  int cost;         // 0 (zero) or 1
  int neutral = 0;  // peel / module: neutral value of x_i
  int v = 0;        // peel: forced constant on the opposite slice; module: constant x_j takes there
  int j = -1;       // module: replaced surviving input (index among the n-1 survivors)
  int tag = -1;     // zero: covering section, 0 = const0, 1 = const1, 2 + 2j + ph = literal x_j xor ph
};

// Zero rule for input i: returns (merged p, merged c, tag) when a covering section exists.
inline std::optional<std::tuple<TT, TT, int>> zero_section(const TT& p, const TT& c, int n, int i) {
  TT p0 = orient::cut(p, n, i, 0), c0 = orient::cut(c, n, i, 0), p1 = orient::cut(p, n, i, 1),
     c1 = orient::cut(c, n, i, 1);
  if (!consistent(p0, c0, p1, c1)) return std::nullopt;
  TT pc = p0 | p1, cc = c0 | c1, full = orient::full_tt(n - 1);
  auto covers = [&](const TT& s) { return ((c0 & ~s) | (c1 & s)) == cc; };
  if (covers(TT{})) return std::make_tuple(pc, cc, 0);
  if (covers(full)) return std::make_tuple(pc, cc, 1);
  for (int j = 0; j < n - 1; ++j)
    for (int ph = 0; ph < 2; ++ph) {
      TT s = orient::col_tt(n - 1, j);
      if (ph) s = s ^ full;
      if (covers(s)) return std::make_tuple(pc, cc, 2 + 2 * j + ph);
    }
  return std::nullopt;
}

// Every applicable rule, in the reference generation order.
inline std::vector<Rule> reductions(const TT& p, const TT& c, int n) {
  if ((p & ~c).any()) throw std::invalid_argument("positive rows outside care");
  std::vector<Rule> out;
  for (int i = 0; i < n; ++i) {
    if (auto z = zero_section(p, c, n, i)) {
      Rule r{kZero, i, std::get<0>(*z), std::get<1>(*z), 0};
      r.tag = std::get<2>(*z);
      out.push_back(r);
    }
    std::array<TT, 2> ps{orient::cut(p, n, i, 0), orient::cut(p, n, i, 1)},
        cs{orient::cut(c, n, i, 0), orient::cut(c, n, i, 1)};
    if (consistent(ps[0], cs[0], ps[1], cs[1])) continue;  // x_i not mandatory
    for (int neutral = 0; neutral < 2; ++neutral) {
      const TT &pn = ps[neutral], &cn = cs[neutral], &po = ps[1 - neutral], &co = cs[1 - neutral];
      if (!pn.any() || pn == cn) continue;  // neutral slice constant on care
      if (!po.any() || po == co) {
        Rule r{kPeel, i, pn, cn, 1};
        r.neutral = neutral;
        r.v = po.any() ? 1 : 0;
        out.push_back(r);
      }
      for (int j = 0; j < n - 1; ++j) {
        TT a0 = orient::cut(po, n - 1, j, 0), b0 = orient::cut(co, n - 1, j, 0), a1 = orient::cut(po, n - 1, j, 1),
           b1 = orient::cut(co, n - 1, j, 1);
        if (!consistent(a0, b0, a1, b1)) continue;
        TT pp = a0 | a1, cp = b0 | b1;
        for (int v = 0; v < 2; ++v) {
          TT pg = orient::cut(pn, n - 1, j, v), cg = orient::cut(cn, n - 1, j, v);
          if ((cp & ~cg).any() || ((pp ^ pg) & cp).any()) continue;
          Rule r{kModule, i, pn, cn, 1};
          r.neutral = neutral;
          r.j = j;
          r.v = v;
          out.push_back(r);
        }
      }
    }
  }
  return out;
}

// Reference rule order: (cost, kind, i, p, c, meta) with numeric table comparison.
inline bool rule_less(const Rule& a, const Rule& b) {
  if (a.cost != b.cost) return a.cost < b.cost;
  if (a.kind != b.kind) return a.kind < b.kind;
  if (a.i != b.i) return a.i < b.i;
  if (int k = cmp_num(a.p, b.p)) return k < 0;
  if (int k = cmp_num(a.c, b.c)) return k < 0;
  if (a.kind == kPeel) return std::tie(a.neutral, a.v) < std::tie(b.neutral, b.v);
  if (a.kind == kModule) return std::tie(a.neutral, a.j, a.v) < std::tie(b.neutral, b.j, b.v);
  return false;  // at most one zero rule per input
}

struct Core {
  int n0 = 0, n = 0;  // original and core widths
  TT p0, c0, p, c;    // original and core tables
  std::vector<Rule> steps;
  int offset() const {
    int s = 0;
    for (auto& r : steps) s += r.cost;
    return s;
  }
  bool trivial() const { return !(p & c).any() || (p & c) == c; }
};

// Deterministic greedy reduction (reference greedy): repeat the least rule until none applies or the table is
// constant on care. Not claimed optimal for the core width.
inline Core greedy(TT p, TT c, int n) {
  Core k;
  k.n0 = n;
  k.p0 = p & c;
  k.c0 = c;
  p = p & c;
  while (n > 0 && p.any() && p != c) {
    auto rs = reductions(p, c, n);
    if (rs.empty()) break;
    const Rule& r = *std::min_element(rs.begin(), rs.end(), rule_less);
    k.steps.push_back(r);
    p = r.p;
    c = r.c;
    --n;
  }
  k.n = n;
  k.p = p;
  k.c = c;
  return k;
}

// Reconstruction (construct() of the handoff): `vs` maps current formal inputs to literals of `aig`; `core(aig, p,
// c, vs)` builds the core table over the final formal inputs. A module adds its gate before the core, a peel after;
// a zero rule only removes the input (its covering section is a lower-bound argument, never inserted).
template <class CoreFn>
int construct(orient::AIG& aig, const Core& k, std::size_t at, std::vector<int> vs, CoreFn&& core) {
  if (at == k.steps.size()) return core(aig, k.p, k.c, vs);
  const Rule& r = k.steps[at];
  int x = vs[r.i];
  vs.erase(vs.begin() + r.i);
  int l = x ^ (1 - r.neutral);  // true iff x_i takes its neutral value
  if (r.kind == kModule) vs[r.j] = r.v == 0 ? aig.AND(vs[r.j], l) : aig.OR(vs[r.j], l ^ 1);
  int z = construct(aig, k, at + 1, vs, core);
  if (r.kind == kPeel) z = r.v == 0 ? aig.AND(z, l) : aig.OR(z, l ^ 1);
  return z;
}

// ---- incomplete signed-permutation / output-phase normalization (canonical()) ----
struct Canon {
  TT q, d;                 // canonical table
  std::vector<int> order;  // canonical input i = original input order[i] xor bit i of flip
  unsigned flip = 0;
  int phase = 0;           // canonical positive = original positive xor phase (on care)
};

inline std::pair<TT, TT> transform(const TT& p, const TT& c, int n, const std::vector<int>& order, unsigned flip) {
  TT a, b;
  for (int r = 0; r < (1 << n); ++r) {
    if (!c.get(r)) continue;
    int s = 0;
    for (int i = 0; i < n; ++i) s |= ((r >> order[i]) & 1) << i;
    s ^= int(flip);
    b.set(s);
    if (p.get(r)) a.set(s);
  }
  return {a, b};
}

inline Canon canonical(const TT& p0, const TT& c, int n) {
  TT p = p0 & c;
  int np = p.count(), nn = c.count() - np;
  std::optional<Canon> best;
  for (int phase = 0; phase < 2; ++phase) {
    if ((np < nn && phase == 1) || (np > nn && phase == 0)) continue;
    TT q = phase ? c ^ p : p, neg = c ^ q;
    using Axis = std::tuple<std::pair<int, int>, std::pair<int, int>, int, int>;
    std::vector<Axis> axes;
    for (int i = 0; i < n; ++i) {
      TT x = orient::col_tt(n, i);
      std::pair<int, int> a{(q & ~x).count(), (neg & ~x).count()}, b{(q & x).count(), (neg & x).count()};
      if (a > b) axes.push_back({b, a, i, 1});
      else axes.push_back({a, b, i, 0});
    }
    std::sort(axes.begin(), axes.end());
    Canon k;
    k.phase = phase;
    for (int i = 0; i < n; ++i) {
      k.order.push_back(std::get<2>(axes[i]));
      k.flip |= unsigned(std::get<3>(axes[i])) << i;
    }
    std::tie(k.q, k.d) = transform(q, c, n, k.order, k.flip);
    // min over (key, order, flip, phase) as Python tuples; keys compared numerically
    auto less = [](const Canon& x, const Canon& y) {
      if (int t = cmp_num(x.q, y.q)) return t < 0;
      if (int t = cmp_num(x.d, y.d)) return t < 0;
      return std::tie(x.order, x.flip, x.phase) < std::tie(y.order, y.flip, y.phase);
    };
    if (!best || less(k, *best)) best = k;
  }
  return *best;
}

inline std::pair<TT, TT> inverse(const TT& q, const TT& d, int n, const Canon& k) {
  TT a, b;
  for (int s = 0; s < (1 << n); ++s) {
    if (!d.get(s)) continue;
    int r = 0;
    for (int i = 0; i < n; ++i) r |= (((s ^ int(k.flip)) >> i) & 1) << k.order[i];
    b.set(r);
    if (int(q.get(s)) ^ k.phase) a.set(r);
  }
  return {a, b};
}

// Literals for importing a canonical-variable chain: canonical input i reads original input order[i], complemented
// when bit i of flip is set; the caller complements the output by phase.
inline std::vector<int> canon_inputs(const Canon& k, const std::vector<int>& vs) {
  std::vector<int> out;
  for (std::size_t i = 0; i < k.order.size(); ++i) out.push_back(vs[k.order[i]] ^ int((k.flip >> i) & 1));
  return out;
}

}  // namespace preduce
