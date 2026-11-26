// Exact standalone AIG decisions through four AND gates for partial tables (free complements and constants), by
// budget-aware support projection (handoff 2026-11-26, section 1).
//
// Theorem used: a trimmed single-output AIG with g gates reads at most g + 1 inputs. With g <= 4 a solution either
// reads <= 4 inputs (some complete 4-input function of cost <= 4 agrees with the projection of the partial table onto
// that support), or reads 5 inputs, has exactly 4 gates and is a tree: a signed read-once formula over those 5 inputs.
// A support missing a mandatory input (two oppositely labelled cared rows differing only there) is rejected, and a
// projection with a positive and a negative row in the same fibre is infeasible. So `solve` returns the exact minimum
// when it is <= 4 and std::nullopt only after the complete search, which proves K >= 5. Scope: independent formal
// primary inputs, standalone gate count; not a bound on a live cone that imports shared or paid gates.
#pragma once
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <stdexcept>
#include <vector>

#include "orientation_witness.hpp"

namespace exact4 {

using u32 = std::uint32_t;
using u64 = std::uint64_t;

struct Record {
  int cost = 0;
  u32 t = 0;          // complete column over `width` formal inputs
  orient::Witness w;  // chain over `width` formal inputs computing t
};

inline u32 full(int n) { return n >= 5 ? 0xffffffffu : (1u << (1 << n)) - 1; }
inline u32 col(int n, int i) {
  u32 r = 0;
  for (int row = 0; row < (1 << n); ++row) if ((row >> i) & 1) r |= 1u << row;
  return r;
}

// Records sorted by (cost, column); per row, a bitset of records whose column is 1 there.
struct Index {
  int n = 0, words = 0;
  std::vector<Record> rec;
  std::vector<std::vector<u64>> ones;
  std::vector<u64> all;
  void build() {
    std::sort(rec.begin(), rec.end(), [](const Record& a, const Record& b) {
      return a.cost != b.cost ? a.cost < b.cost : a.t < b.t;
    });
    words = int((rec.size() + 63) / 64);
    all.assign(words, 0);
    for (std::size_t j = 0; j < rec.size(); ++j) all[j >> 6] |= 1ull << (j & 63);
    ones.assign(std::size_t(1) << n, std::vector<u64>(words, 0));
    for (std::size_t j = 0; j < rec.size(); ++j)
      for (int r = 0; r < (1 << n); ++r)
        if ((rec[j].t >> r) & 1) ones[r][j >> 6] |= 1ull << (j & 63);
  }
  // Cheapest record (lowest index) agreeing with positive set p on care set c, or nullptr.
  const Record* best(u32 p, u32 c) const {
    std::vector<u64> s = all;
    for (int r = 0; r < (1 << n); ++r) {
      if (!((c >> r) & 1)) continue;
      const auto& o = ones[r];
      bool any = false;
      if ((p >> r) & 1) for (int i = 0; i < words; ++i) any |= (s[i] &= o[i]) != 0;
      else for (int i = 0; i < words; ++i) any |= (s[i] &= ~o[i]) != 0;
      if (!any) return nullptr;
    }
    for (int i = 0; i < words; ++i)
      if (s[i]) return &rec[std::size_t(i) * 64 + std::countr_zero(s[i])];
    return nullptr;
  }
};

// All complete functions of n <= 4 inputs with AIG cost <= cap, each with a minimum chain. Depth-first enumeration of
// gate sequences over distinct complement-normalized columns; the minimum-cost record has no dead gates.
inline Index aig_library(int n, int cap = 4) {
  const u32 F = full(n);
  auto norm = [&](u32 x) { return (x & 1) ? x ^ F : x; };
  std::map<u32, Record> out;
  auto add = [&](u32 v, int k, const std::vector<std::array<int, 2>>& gates, int lit) {
    for (int ph = 0; ph < 2; ++ph) {
      u32 t = ph ? v ^ F : v;
      auto it = out.find(t);
      if (it != out.end() && it->second.cost <= k) continue;
      Record r;
      r.cost = k;
      r.t = t;
      r.w.n = n;
      r.w.gates = gates;
      r.w.out = lit ^ ph;
      out[t] = r;
    }
  };
  add(0, 0, {}, 0);
  std::vector<u32> cols{0};     // node columns (normalized), node 0 = constant 0
  std::vector<int> lits{0};     // literal of each node's normalized column
  for (int i = 0; i < n; ++i) { cols.push_back(col(n, i)); lits.push_back(2 * (i + 1)); add(col(n, i), 0, {}, 2 * (i + 1)); }
  std::vector<std::array<int, 2>> gates;
  auto dfs = [&](auto&& self, int k) -> void {
    if (k > cap) return;
    int m = int(cols.size());
    for (int a = 1; a < m; ++a)
      for (int b = a + 1; b < m; ++b)
        for (int pa = 0; pa < 2; ++pa)
          for (int pb = 0; pb < 2; ++pb) {
            u32 v = (cols[a] ^ (pa ? F : 0)) & (cols[b] ^ (pb ? F : 0)), t = norm(v);
            if (!t || std::find(cols.begin(), cols.end(), t) != cols.end()) continue;
            int id = n + 1 + int(gates.size());
            gates.push_back({lits[a] ^ pa, lits[b] ^ pb});
            int lit = 2 * id + (v != t);
            add(t, k, gates, lit);
            if (k < cap) {
              cols.push_back(t);
              lits.push_back(lit);
              self(self, k + 1);
              cols.pop_back();
              lits.pop_back();
            }
            gates.pop_back();
          }
  };
  dfs(dfs, 1);
  Index idx;
  idx.n = n;
  for (auto& [t, r] : out) idx.rec.push_back(r);
  idx.build();
  return idx;
}

// Signed read-once formulas over subset S of 5 inputs: column -> chain (first expression found, as in the reference).
inline const std::map<u32, orient::Witness>& formulas(u32 S) {
  static std::map<u32, std::map<u32, orient::Witness>> memo;
  if (auto it = memo.find(S); it != memo.end()) return it->second;
  const u32 F = full(5);
  std::map<u32, orient::Witness> out;
  auto put = [&](u32 v, const orient::Witness& w) {
    out.emplace(v, w);
    orient::Witness c = w;
    c.out ^= 1;
    out.emplace(v ^ F, c);
  };
  if (!(S & (S - 1))) {
    int i = std::countr_zero(S);
    orient::Witness w;
    w.n = 5;
    w.out = 2 * (i + 1);
    put(col(5, i), w);
  } else {
    u32 anchor = S & (~S + 1);
    for (u32 A = (S - 1) & S; A; A = (A - 1) & S) {
      if (!(A & anchor)) continue;
      u32 B = S ^ A;
      const auto& fa = formulas(A);
      const auto& fb = formulas(B);
      for (const auto& [a, wa] : fa)
        for (const auto& [b, wb] : fb) {
          u32 v = a & b;
          if (out.count(v) && out.count(v ^ F)) continue;
          orient::Witness w;
          w.n = 5;
          w.gates = wa.gates;
          int shift = int(wa.gates.size());
          auto remap = [&](int l) { return l / 2 > 5 ? l + 2 * shift : l; };
          for (auto g : wb.gates) w.gates.push_back({remap(g[0]), remap(g[1])});
          w.gates.push_back({wa.out, remap(wb.out)});
          w.out = 2 * (5 + int(w.gates.size()));
          if (!out.count(v)) out.emplace(v, w);
          if (!out.count(v ^ F)) { orient::Witness c = w; c.out ^= 1; out.emplace(v ^ F, c); }
        }
    }
  }
  return memo.emplace(S, std::move(out)).first->second;
}

inline const Index& library(int n) {
  static std::array<std::unique_ptr<Index>, 6> lib;
  if (n < 1 || n > 5) throw std::invalid_argument("exact4 library width");
  if (!lib[n]) {
    if (n <= 4) {
      lib[n] = std::make_unique<Index>(aig_library(n, 4));
    } else {
      auto idx = std::make_unique<Index>();
      idx->n = 5;
      for (const auto& [t, w] : formulas(0x1f)) idx->rec.push_back(Record{4, t, w});
      idx->build();
      lib[n] = std::move(idx);
    }
  }
  return *lib[n];
}

// Mandatory inputs of a partial table: two oppositely labelled cared rows differing only in input i.
inline int mandatory(const orient::TT& p, const orient::TT& c, int n) {
  int M = 0;
  for (int i = 0; i < n; ++i)
    for (int r = 0; r < (1 << n) && !((M >> i) & 1); ++r) {
      if ((r >> i) & 1) continue;
      int s = r | (1 << i);
      if (c.get(r) && c.get(s) && p.get(r) != p.get(s)) M |= 1 << i;
    }
  return M;
}

// Projection onto support V (|V| <= 5): (positive, care) over |V| inputs, or nullopt on an opposite-label collision.
inline std::optional<std::pair<u32, u32>> project(const orient::TT& p, const orient::TT& c, int n,
                                                  const std::vector<int>& V) {
  u32 pos = 0, neg = 0;
  for (int r = 0; r < (1 << n); ++r) {
    if (!c.get(r)) continue;
    int s = 0;
    for (std::size_t j = 0; j < V.size(); ++j) s |= ((r >> V[j]) & 1) << j;
    (p.get(r) ? pos : neg) |= 1u << s;
  }
  if (pos & neg) return std::nullopt;
  return std::make_pair(pos, pos | neg);
}

struct Hit {
  int cost = 0;
  std::vector<int> vars;  // original inputs read by formal inputs 0..|vars|-1 of rec->w
  const Record* rec = nullptr;
};

// Exact minimum <= 4 (with the support and chain), or nullopt proving K >= 5. Same search order and early stop as the
// Python reference exact4: widths min(n,4) then 5 (only if nothing found), supports in lexicographic order.
inline std::optional<Hit> solve(const orient::TT& p0, const orient::TT& c, int n, long* projections = nullptr) {
  if (n < 1 || n > 8) throw std::invalid_argument("exact4 input count");
  orient::TT p = p0 & c;
  int M = mandatory(p, c, n), mc = std::popcount(unsigned(M));
  std::optional<Hit> best;
  if (mc > 5) return best;
  for (int width : {std::min(n, 4), 5}) {
    if (width > n || (width == 5 && best)) continue;
    if (mc > width) continue;
    const Index& idx = library(width);
    std::vector<int> V(width);
    for (int j = 0; j < width; ++j) V[j] = j;
    while (true) {
      int mask = 0;
      for (int v : V) mask |= 1 << v;
      if (!(M & ~mask)) {
        if (projections) ++*projections;
        if (auto pc = project(p, c, n, V)) {
          if (const Record* r = idx.best(pc->first, pc->second)) {
            if (!best || r->cost < best->cost) best = Hit{r->cost, V, r};
            if (r->cost <= std::max(0, mc - 1)) return best;
          }
        }
      }
      int j = width - 1;
      while (j >= 0 && V[j] == n - width + j) --j;
      if (j < 0) break;
      ++V[j];
      for (int k = j + 1; k < width; ++k) V[k] = V[k - 1] + 1;
    }
  }
  return best;
}

}  // namespace exact4
