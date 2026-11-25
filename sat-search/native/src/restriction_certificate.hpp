#pragma once
// Restriction (gate-elimination) certificates for fixed-budget free-NOT AIG synthesis.
//
// Statement. Let C be any B-gate free-NOT AIG computing f (no minimality, order or reapplication
// assumption) and pi a primary substitution: x_i := constant, or x_j := x_i XOR b. Under pi a gate
// is deletable if it equals a constant or (up to complement) an earlier wire. Deleting D such gates
// leaves a (B - D)-gate circuit for f o pi, so B >= L(f o pi) + D, where L is the exact restricted
// cost (or any certified lower bound).
//
// Certificate. analyze() propagates constants, aliases, equal/complementary operands and structural
// hashing under pi, and records for each deletion a Proof: the steps whose fanin pair ("pairs") or
// fanin pair plus operand/output phases ("typed") establish it. A deletion with a constant operand,
// or with equal/complementary operands, needs only the pair of its own step: whatever the phases,
// the gate is a constant or an earlier wire. Values propagated to later steps keep typed proofs.
// If more than B - L(f o pi) deletions exist, conflict_core() picks a small Proof covering
// B - L + 1 of them; every B-gate circuit that agrees with it on those steps has at least that many
// deletions under pi, so it cannot compute f, and the negated choices are a valid clause for budget B.
//
// Ported from the supplied restriction_certificate_native reference (analyze, conflict_core, fix,
// identify are unchanged in logic). Additions: restricted-target lower bounds (exact three-input
// costs, minimised over don't-care completions; an essential-variable bound for larger
// restrictions), core selection across restrictions, and a semantic self-check of each deletion.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <map>
#include <stdexcept>
#include <utility>
#include <vector>

namespace restriction_certificate {
using Mask = std::uint64_t;
// AND of operand a (positive iff pa) and operand b (positive iff pb), complemented iff inv.
struct Gate { unsigned a, b; bool pa, pb; bool inv = false; };
struct Proof {
    Mask pairs = 0, typed = 0;  // typed implies pairs; pair-only permits any gate phase
    bool covers(Proof p) const { return (p.pairs & ~pairs) == 0 && (p.typed & ~typed) == 0; }
    unsigned cost() const { return unsigned(std::popcount(pairs) + std::popcount(typed)); }
    bool operator==(const Proof&) const = default;
};
inline Proof join(Proof a, Proof b) { return {a.pairs | b.pairs, a.typed | b.typed}; }
struct Event { unsigned step; Proof proof; };
// refs: 0/1 constants, 2*(wire+1) positive wire, XOR 1 complement.
struct Analysis { std::vector<Event> events; std::vector<unsigned> refs; };

inline Analysis analyze(const std::vector<unsigned>& primary, const std::vector<Gate>& gates, bool hashing = true) {
    if (gates.size() > 64) throw std::invalid_argument("at most 64 gates");
    Analysis out; out.refs = primary; const unsigned n = unsigned(primary.size());
    std::vector<Proof> alias(n);
    std::map<std::pair<unsigned, unsigned>, std::pair<unsigned, Proof>> hashes;
    for (unsigned t = 0; t < gates.size(); ++t) {
        const auto g = gates[t];
        if (g.a >= n + t || g.b >= n + t || g.a == g.b) throw std::invalid_argument("invalid fanins");
        const unsigned x = out.refs[g.a] ^ unsigned(!g.pa), y = out.refs[g.b] ^ unsigned(!g.pb), ref = 2 * (n + t + 1);
        unsigned z = ref;
        const Proof p = alias[g.a], q = alias[g.b];
        Proof why{}, del{};
        const Mask bit = Mask(1) << t;
        const Proof own{bit, bit}, pair{bit, 0};
        if (x == 0 || y == 0) {
            z = 0; why = join(own, x == 0 ? p : q);
            if (x == 0 && y == 0 && join(own, q).cost() < why.cost()) why = join(own, q);
        } else if (x == 1) { z = y; why = join(own, join(p, q)); }
        else if (y == 1) { z = x; why = join(own, join(p, q)); }
        else if (x == y) { z = x; why = join(own, join(p, q)); }
        else if (x == (y ^ 1)) { z = 0; why = join(own, join(p, q)); }
        else {
            const auto key = std::minmax(x, y);
            const auto k = std::make_pair(key.first, key.second);
            const auto it = hashes.find(k);
            if (hashing && it != hashes.end()) {
                z = it->second.first; why = join(own, join(join(p, q), it->second.second)); del = why;
            } else {
                hashes.emplace(k, std::make_pair(ref ^ unsigned(g.inv), join(own, join(p, q))));
                z = ref ^ unsigned(g.inv);
            }
        }
        z ^= unsigned(g.inv);
        if (z != ref) {
            // Operator-independent deletion: one constant operand, or equal/complementary operands.
            if (x < 2 || y < 2) {
                del = join(pair, x < 2 ? p : q);
                if (x < 2 && y < 2 && join(pair, q).cost() < del.cost()) del = join(pair, q);
            } else if (x == y || x == (y ^ 1)) del = join(pair, join(p, q));
            else del = why;
            out.events.push_back({t, del});
        }
        out.refs.push_back(z); alias.push_back(why);
    }
    return out;
}

inline unsigned covered(const std::vector<Event>& e, Proof c) {
    unsigned n = 0;
    for (auto v : e) n += c.covers(v.proof);
    return n;
}

inline Proof conflict_core(const std::vector<Event>& e, unsigned need) {
    if (need > e.size()) throw std::invalid_argument("insufficient events");
    Proof c{};
    while (covered(e, c) < need) {
        Proof best{}; unsigned score = ~0u; bool found = false;
        for (auto v : e)
            if (!c.covers(v.proof)) {
                const Proof d = join(c, v.proof);
                const unsigned s = d.cost();
                if (s < score) { best = d; score = s; found = true; }
            }
        if (!found) throw std::logic_error("no event");
        c = best;
    }
    // Relax typed steps to pair-only, then drop pairs, whenever the cover survives.
    for (unsigned i = 0; i < 64; ++i) {
        const Mask b = Mask(1) << i;
        if (c.typed & b) { const Proof d{c.pairs, c.typed ^ b}; if (covered(e, d) >= need) c = d; }
    }
    for (unsigned i = 0; i < 64; ++i) {
        const Mask b = Mask(1) << i;
        if ((c.pairs & b) && !(c.typed & b)) { const Proof d{c.pairs ^ b, c.typed}; if (covered(e, d) >= need) c = d; }
    }
    return c;
}

inline std::vector<unsigned> fix(unsigned n, unsigned i, bool b) {
    std::vector<unsigned> v;
    for (unsigned j = 0; j < n; ++j) v.push_back(j == i ? unsigned(b) : 2 * (j + 1));
    return v;
}
inline std::vector<unsigned> identify(unsigned n, unsigned i, unsigned j, bool b) {
    std::vector<unsigned> v;
    for (unsigned k = 0; k < n; ++k) v.push_back(k == j ? (2 * (i + 1)) ^ unsigned(b) : 2 * (k + 1));
    return v;
}

// Exact free-NOT AIG gate counts of all three-input functions (truth table bit r = f(row r),
// x0 least significant). Computed with Percy and checked against the reference brute force.
inline constexpr std::array<std::uint8_t, 256> kCost3{
    0,2,2,1,2,1,4,2,2,4,1,2,1,2,2,0,2,1,4,2,4,2,6,4,5,4,4,3,4,3,4,2,2,4,1,2,5,4,4,3,4,6,2,4,4,4,3,2,
    1,2,2,0,4,3,4,2,4,4,3,2,3,4,4,1,2,4,5,4,1,2,4,3,4,6,4,4,2,4,3,2,1,2,4,3,2,0,4,2,4,4,3,4,3,2,4,1,
    4,6,4,4,4,4,3,4,6,6,4,6,4,6,4,4,2,4,3,2,3,2,4,1,4,6,4,4,4,4,5,2,2,5,4,4,4,4,6,4,1,4,2,3,2,3,4,2,
    4,4,6,4,6,4,6,6,4,3,4,4,4,4,6,4,1,4,2,3,4,3,4,4,2,4,0,2,3,4,2,1,2,3,4,2,4,4,6,4,3,4,2,1,4,5,4,2,
    1,4,4,3,2,3,4,4,2,4,3,4,0,2,2,1,2,3,4,4,4,2,6,4,3,4,4,5,2,1,4,2,2,4,3,4,3,4,4,5,4,6,2,4,2,4,1,2,
    0,2,2,1,2,1,4,2,2,4,1,2,1,2,2,0};

struct Restriction {
    std::vector<unsigned> primary;  // initial refs for analyze()
    unsigned lower = 0;             // certified lower bound on L(f o pi)
    bool exact = false;             // lower is the exact cost (some completion attains it)
};

// Lower bound for a restricted partial function on m variables, given as row value and care bits.
inline std::pair<unsigned, bool> restricted_lower(unsigned m, Mask value, Mask care) {
    const unsigned rows = 1u << m;
    if (m <= 3) {
        // Pad to three variables (the padded function ignores the extra variables).
        Mask v3 = 0, c3 = 0;
        for (unsigned r = 0; r < 8; ++r) {
            const unsigned s = r & (rows - 1);
            v3 |= (value >> s & 1) << r; c3 |= (care >> s & 1) << r;
        }
        unsigned best = ~0u;
        for (unsigned g = 0; g < 256; ++g)
            if (((g ^ v3) & c3) == 0) best = std::min<unsigned>(best, kCost3[g]);
        return {best, true};
    }
    // Every completion depends on each variable with a cared, differing neighbouring row pair; a
    // free-NOT AIG reading e distinct variables has at least e - 1 gates.
    unsigned essential = 0;
    for (unsigned v = 0; v < m; ++v) {
        bool dep = false;
        for (unsigned r = 0; r < rows && !dep; ++r) {
            const unsigned s = r ^ (1u << v);
            dep = (care >> r & 1) && (care >> s & 1) && ((value >> r & 1) != (value >> s & 1));
        }
        essential += dep;
    }
    return {essential ? essential - 1 : 0, false};
}

// All constant and (complementary) identification restrictions of an n-input target given as
// truth table and care mask (row r = assignment with x_i = bit i of r).
inline std::vector<Restriction> restrictions(unsigned n, Mask value, Mask care) {
    if (n < 2 || n > 6) throw std::invalid_argument("restrictions need 2-6 inputs");
    std::vector<Restriction> out;
    const auto add = [&](std::vector<unsigned> primary, auto row_of) {
        const unsigned m = n - 1;
        Mask v = 0, c = 0;
        for (unsigned s = 0; s < (1u << m); ++s) {
            const unsigned r = row_of(s);
            v |= (value >> r & 1) << s; c |= (care >> r & 1) << s;
        }
        const auto [lower, exact] = restricted_lower(m, v, c);
        out.push_back({std::move(primary), lower, exact});
    };
    // Spread the m remaining-variable bits of s over the variables other than `skip`.
    const auto spread = [n](unsigned s, unsigned skip) {
        unsigned r = 0, k = 0;
        for (unsigned v = 0; v < n; ++v) if (v != skip) r |= (s >> k++ & 1) << v;
        return r;
    };
    for (unsigned i = 0; i < n; ++i)
        for (unsigned b = 0; b < 2; ++b)
            add(fix(n, i, b), [&](unsigned s) { return spread(s, i) | (b << i); });
    for (unsigned i = 0; i < n; ++i)
        for (unsigned j = i + 1; j < n; ++j)
            for (unsigned b = 0; b < 2; ++b)
                add(identify(n, i, j, b), [&](unsigned s) {
                    const unsigned r = spread(s, j);
                    return r | (((r >> i & 1) ^ b) << j);
                });
    return out;
}

// Semantic check of one analysis: under the restriction, every recorded deletion is a constant or
// (up to complement) an earlier wire. Rows are the 2^n assignments of the restricted inputs.
inline bool deletions_hold(unsigned n, const std::vector<unsigned>& primary, const std::vector<Gate>& gates,
                           const std::vector<Event>& events) {
    const unsigned rows = 1u << n;
    const Mask all = rows == 64 ? ~Mask(0) : (Mask(1) << rows) - 1;
    std::vector<Mask> raw(n), wire;
    for (unsigned i = 0; i < n; ++i)
        for (unsigned r = 0; r < rows; ++r) raw[i] |= Mask(r >> i & 1) << r;
    const auto col = [&](unsigned ref) {
        const Mask base = ref < 2 ? 0 : raw[ref / 2 - 1];
        return (base ^ ((ref & 1) ? all : 0)) & all;
    };
    for (unsigned i = 0; i < n; ++i) wire.push_back(col(primary[i]));
    for (const auto& g : gates)
        wire.push_back(((wire[g.a] ^ (g.pa ? 0 : all)) & (wire[g.b] ^ (g.pb ? 0 : all)) ^ (g.inv ? all : 0)) & all);
    for (const auto& e : events) {
        const Mask w = wire[n + e.step];
        bool ok = w == 0 || w == all;
        for (unsigned j = 0; j < n + e.step && !ok; ++j) ok = w == wire[j] || w == (wire[j] ^ all);
        if (!ok) return false;
    }
    return true;
}

struct Certificate { Proof core; unsigned restriction = 0, deletions = 0, need = 0; };

// Every restriction whose deletions exceed budget - lower yields a core. With best_only, return
// the single cheapest one; otherwise one per violating restriction (duplicates removed).
inline std::vector<Certificate> certify(const std::vector<Restriction>& rs, const std::vector<Gate>& gates,
                                        bool best_only, bool self_check, bool* check_failed = nullptr) {
    std::vector<Certificate> out;
    const unsigned budget = unsigned(gates.size());
    for (unsigned i = 0; i < rs.size(); ++i) {
        const auto& r = rs[i];
        if (r.lower > budget) {  // B < L(f o pi): no B-gate circuit exists; the empty core refutes B
            out = {Certificate{Proof{}, i, 0, 0}};
            return out;
        }
        const unsigned allow = budget - r.lower;
        const auto a = analyze(r.primary, gates);
        if (a.events.size() <= allow) continue;
        if (self_check && !deletions_hold(unsigned(r.primary.size()), r.primary, gates, a.events)) {
            if (check_failed) *check_failed = true;
            continue;
        }
        const Certificate c{conflict_core(a.events, allow + 1), i, unsigned(a.events.size()), allow + 1};
        if (std::any_of(out.begin(), out.end(), [&](const Certificate& o) { return o.core == c.core; })) continue;
        out.push_back(c);
    }
    if (best_only && out.size() > 1) {
        const auto best = std::min_element(out.begin(), out.end(), [](const Certificate& a, const Certificate& b) {
            return a.core.cost() + std::popcount(a.core.typed) < b.core.cost() + std::popcount(b.core.typed);
        });
        out = {*best};
    }
    return out;
}
}  // namespace restriction_certificate
