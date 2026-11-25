#pragma once
// Last-provider decoder phase screen for residual_slack_two::Engine (opt-in, use_decoder 1|2).
//
// At the LAST shared-provider allocation the remaining region is the final decoder: a free-NOT
// AND tree over the remaining wire occurrences plus >= 2 occurrences of the new provider p.
// Let S be the remaining wires read once and R those read more than once. A tree reads each
// wire of S once, so the decoder is unate in S with some phase vector t. For a positive row a
// and a negative row b that agree on R, either a literal of S separates them in the decoder's
// direction (some i with a_i != b_i and a_i != t_i), or p(a) != p(b). The provider is a
// function of its inside wires, so it is constant on inside fibers; the existing parity
// components write p(row) = orientation(component) XOR side(row) for every provider allowed by
// the base distinction test. Hence for each pair the subcube of t with a_i == t_i on all
// differing singletons D forces:
//   same component, same side          -> that phase subcube is impossible;
//   same component, opposite sides     -> nothing;
//   different components               -> orientation(a) XOR orientation(b) = 1 ^ side(a) ^ side(b).
// A candidate provider column fixes the orientations, and is kept iff some phase survives all
// active edges. Mode 2 also checks each phase's edge system for parity consistency before any
// candidate. The screen is a relaxation (arbitrary decoder unate in S): it never decides
// read-once realizability, so exact recognition still runs on every surviving candidate.
// Earlier singletons may feed later providers, so this is applied only at the last provider.
// Skipped (no rejection) when S has more than six wires.
//
// Adapted from the residual_decoder_phase_native reference: work is charged while building
// through the Engine's tick (which also polls the deadline), not after the fact.
#include "residual_directed.hpp"
#include "residual_parity_filter.hpp"

#include <array>
#include <bit>
#include <map>
#include <tuple>
#include <vector>

namespace residual_decoder_phase {
using residual_directed::Leaf;
using residual_directed::U;
using residual_filter::ParityComponents;

struct Edge {
    unsigned a, b, want;
    U phases;
};

struct Screen {
    bool enabled = false;
    U allowed = 0;            // phase vectors t (bit t) not yet excluded
    std::vector<U> reps;      // one row of side 0 per component
    std::vector<Edge> edges;  // conditional orientation relations, merged by (a, b, want)
    bool accepts(U c) const {
        if (!enabled) return true;
        U mask = allowed;
        for (const auto& e : edges)
            if ((bool(c & reps[e.a]) ^ bool(c & reps[e.b])) != e.want) {
                mask &= ~e.phases;
                if (!mask) return false;
            }
        return mask != 0;
    }
};

// rest: the remaining decoder wire occurrences (without the new provider). pc: the provider
// parity components after any unate refinement. p, n: positive and negative cared rows.
// charge(units) must account work and may throw to abandon the query.
template <class Charge>
Screen build(const std::vector<Leaf>& rest, const ParityComponents& pc, U p, U n, bool full_parity,
             Charge&& charge) {
    Screen out;
    if (!pc.consistent) {
        out.enabled = true;
        return out;
    }
    charge(rest.size() + 1);
    std::map<unsigned, std::pair<unsigned, U>> wires;
    for (const auto& l : rest) {
        ++wires[l.wire].first;
        wires[l.wire].second = l.column;
    }
    std::vector<U> singles, repeats;
    for (const auto& [wire, x] : wires) (x.first == 1 ? singles : repeats).push_back(x.second);
    if (singles.size() > 6) return out;
    const unsigned phases = 1u << singles.size();
    out.enabled = true;
    out.allowed = phases == 64 ? ~U(0) : (U(1) << phases) - 1;
    std::array<unsigned, 64> sp{}, rp{}, comp{}, side{};
    std::array<U, 6> phase_one{};
    charge(singles.size() + 1);
    for (unsigned i = 0; i < singles.size(); ++i)
        for (unsigned t = 0; t < phases; ++t)
            if (t & (1u << i)) phase_one[i] |= U(1) << t;
    charge(std::popcount(p | n) * (wires.size() + 1) + pc.sides.size());
    for (unsigned i = 0; i < singles.size(); ++i)
        for (U a = singles[i] & (p | n); a; a &= a - 1) sp[std::countr_zero(a)] |= 1u << i;
    for (unsigned i = 0; i < repeats.size(); ++i)
        for (U a = repeats[i] & (p | n); a; a &= a - 1) rp[std::countr_zero(a)] |= 1u << i;
    for (unsigned i = 0; i < pc.sides.size(); ++i) {
        auto z = pc.sides[i];
        if (!z[0]) std::swap(z[0], z[1]);
        out.reps.push_back(z[0] & -z[0]);
        for (unsigned j = 0; j < 2; ++j)
            for (U a = z[j]; a; a &= a - 1) {
                const unsigned r = std::countr_zero(a);
                comp[r] = i;
                side[r] = j;
            }
    }
    std::map<std::tuple<unsigned, unsigned, unsigned>, U> edges;
    for (U pp = p; pp; pp &= pp - 1)
        for (U nn = n; nn; nn &= nn - 1) {
            const unsigned a = std::countr_zero(pp), b = std::countr_zero(nn);
            charge(1);
            if (rp[a] != rp[b]) continue;
            unsigned ca = comp[a], cb = comp[b];
            const unsigned want = 1 ^ side[a] ^ side[b];
            if (ca == cb && !want) continue;
            U bad = out.allowed;
            for (unsigned d = sp[a] ^ sp[b]; d && bad; d &= d - 1) {
                const unsigned i = std::countr_zero(d);
                bad &= (sp[a] & (1u << i)) ? phase_one[i] : ~phase_one[i];
            }
            if (!bad) continue;
            if (ca == cb) {
                out.allowed &= ~bad;
                if (!out.allowed) return out;
            } else {
                if (ca > cb) std::swap(ca, cb);
                edges[{ca, cb, want}] |= bad;
            }
        }
    charge(edges.size() + 1);
    for (const auto& [key, mask] : edges) {
        const auto [a, b, want] = key;
        out.edges.push_back({a, b, want, mask});
    }
    if (full_parity)
        for (U m = out.allowed; m; m &= m - 1) {
            const U bit = m & -m;
            charge(out.edges.size() + 1);
            residual_filter::ParityDSU d(unsigned(pc.sides.size()));
            for (const auto& e : out.edges) {
                if (!(e.phases & bit)) continue;
                auto [a, x] = d.find(e.a);
                auto [b, y] = d.find(e.b);
                if (a == b) {
                    if ((x ^ y) != e.want) {
                        out.allowed &= ~bit;
                        break;
                    }
                    continue;
                }
                d.parent[b] = a;
                d.parity[b] = x ^ y ^ e.want;
            }
        }
    return out;
}
}  // namespace residual_decoder_phase
