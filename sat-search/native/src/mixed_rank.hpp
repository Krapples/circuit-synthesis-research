#pragma once
// Mixed-rank cuts: a floor on structurally mixed AND gates of a COMPLETE Boolean function (native port of
// sat-search/mixed_rank_cuts.py, which stays the reference).
//
// Theorem (scalar mixed-rank ceiling; paper proof by square-zero first-gate induction in
// sat-search/chatgpt_handoff/first_gate_translation_proof_handoff.md, not Lean checked): split the inputs into a
// side X and its complement Q, H(x, q) = f(x, q) ^ f(x, 0) ^ f(0, q) ^ f(0, 0), R = rank_GF(2) of the matrix H.
// In any circuit with free affine wiring (so any AIG, NOTs free), if t AND gates read both sides structurally
// (pure gates read one side only), then R <= 2^(t+1) - 2 for t >= 1 and R = 0 for t = 0. Hence
// t >= floor(R) = bit_width(R + 1) - 1. Partial tables have no fixed completion rank: callers must not apply this
// to a table with don't-cares.
//
// Rank is invariant under input/output negation and permutations within a side. Inputs that are pairwise
// swap-symmetric in f form classes; a cut's rank only depends on the per-class counts on the X side (cache key).
#include <algorithm>
#include <bit>
#include <cstdint>
#include <map>
#include <vector>

namespace mixed_rank {

struct Cut {
    int floor = 0;
    int rank = 0;
    uint32_t side = 0;  // X side as an input mask; the rest is Q
};

inline int floor_of(long long rank) { return int(std::bit_width(static_cast<unsigned long long>(rank + 1))) - 1; }

// Table: bit r of the function on row r, input i = bit i of r.
using Table = std::vector<uint8_t>;

// GF(2) rank of rows given as little-endian word vectors of equal length.
inline int gf2_rank(std::vector<std::vector<uint64_t>> rows) {
    if (rows.empty()) return 0;
    const size_t W = rows[0].size();
    int rank = 0;
    for (size_t w = W; w-- > 0;) {
        for (int b = 63; b >= 0; --b) {
            const uint64_t bit = uint64_t(1) << b;
            size_t piv = size_t(rank);
            while (piv < rows.size() && !(rows[piv][w] & bit)) ++piv;
            if (piv == rows.size()) continue;
            std::swap(rows[size_t(rank)], rows[piv]);
            for (size_t r = size_t(rank) + 1; r < rows.size(); ++r)
                if (rows[r][w] & bit)
                    for (size_t k = 0; k <= w; ++k) rows[r][k] ^= rows[size_t(rank)][k];
            if (size_t(++rank) == rows.size()) return rank;
        }
    }
    return rank;
}

inline std::vector<uint32_t> pattern_rows(int n, uint32_t mask) {
    std::vector<int> pos;
    for (int v = 0; v < n; ++v) if (mask >> v & 1) pos.push_back(v);
    std::vector<uint32_t> out(size_t(1) << pos.size());
    for (size_t p = 0; p < out.size(); ++p) {
        uint32_t r = 0;
        for (size_t k = 0; k < pos.size(); ++k) if (p >> k & 1) r |= 1u << pos[k];
        out[p] = r;
    }
    return out;
}

inline int anchored_rank(int n, const Table& f, uint32_t side) {
    const uint32_t full = (n >= 32 ? ~0u : (1u << n) - 1);
    side &= full;
    if (!side || side == full) return 0;
    const auto xs = pattern_rows(n, side), qs = pattern_rows(n, full & ~side);
    const size_t W = (qs.size() + 63) / 64;
    std::vector<std::vector<uint64_t>> rows;
    rows.reserve(xs.size() - 1);
    const uint8_t f00 = f[0];
    for (size_t a = 1; a < xs.size(); ++a) {
        std::vector<uint64_t> row(W, 0);
        const uint8_t fx0 = f[xs[a]];
        bool any = false;
        for (size_t b = 0; b < qs.size(); ++b)
            if (f[xs[a] | qs[b]] ^ fx0 ^ f[qs[b]] ^ f00) { row[b >> 6] |= uint64_t(1) << (b & 63); any = true; }
        if (any) rows.push_back(std::move(row));
    }
    return gf2_rank(std::move(rows));
}

inline std::vector<int> essential_inputs(int n, const Table& f) {
    std::vector<int> ess;
    for (int v = 0; v < n; ++v)
        for (uint32_t r = 0; r < (1u << n); ++r)
            if (!(r >> v & 1) && f[r] != f[r | 1u << v]) { ess.push_back(v); break; }
    return ess;
}

inline bool swap_symmetric(int n, const Table& f, int u, int v) {
    for (uint32_t r = 0; r < (1u << n); ++r) {
        const uint32_t bu = r >> u & 1, bv = r >> v & 1;
        if (bu == bv) continue;
        const uint32_t s = (r & ~((1u << u) | (1u << v))) | (bv << u) | (bu << v);
        if (f[r] != f[s]) return false;
    }
    return true;
}

struct Stats { int cuts = 0, ranked = 0; };

// All proper cuts of the essential inputs with floor >= 1 (one per complementary pair: the side holding the
// lowest essential input; inessential inputs stay on Q), sorted by floor, rank (descending), then side.
inline std::vector<Cut> cut_floors(int n, const Table& f, bool use_symmetry = true, Stats* stats = nullptr) {
    const auto ess = essential_inputs(n, f);
    std::vector<Cut> out;
    if (ess.size() < 2) return out;
    std::vector<std::vector<int>> classes;
    for (int v : ess) {
        bool placed = false;
        if (use_symmetry)
            for (auto& c : classes)
                if (swap_symmetric(n, f, c[0], v)) { c.push_back(v); placed = true; break; }
        if (!placed) classes.push_back({v});
    }
    uint32_t all = 0;
    for (int v : ess) all |= 1u << v;
    const int m = int(ess.size()) - 1;
    std::map<std::vector<int>, int> cache;
    Stats st;
    for (uint32_t bits = 0; bits < (1u << m); ++bits) {
        uint32_t side = 1u << ess[0];
        for (int k = 0; k < m; ++k) if (bits >> k & 1) side |= 1u << ess[size_t(k) + 1];
        if (side == all) continue;
        std::vector<int> key;
        for (const auto& c : classes) {
            int cnt = 0;
            for (int v : c) cnt += int(side >> v & 1);
            key.push_back(cnt);
        }
        auto it = cache.find(key);
        if (it == cache.end()) { it = cache.emplace(key, anchored_rank(n, f, side)).first; ++st.ranked; }
        ++st.cuts;
        if (it->second) out.push_back({floor_of(it->second), it->second, side});
    }
    std::sort(out.begin(), out.end(), [](const Cut& a, const Cut& b) {
        if (a.floor != b.floor) return a.floor > b.floor;
        if (a.rank != b.rank) return a.rank > b.rank;
        return a.side < b.side;
    });
    if (stats) *stats = st;
    return out;
}

inline std::vector<Cut> select_cuts(int n, const Table& f, size_t limit = 8, int min_floor = 2) {
    std::vector<Cut> out;
    for (const auto& c : cut_floors(n, f))
        if (c.floor >= min_floor && out.size() < limit) out.push_back(c);
    return out;
}

}  // namespace mixed_rank
