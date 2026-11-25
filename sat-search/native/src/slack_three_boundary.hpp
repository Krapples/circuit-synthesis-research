#pragma once

// Slack-three boundary recognizer for Percy's first-layer cut (opt-in).
//
// A boundary with h typed first-layer occurrences and m distinct mixed primaries in a k-gate
// free-NOT AIG has slack s = k + 1 - (2h + m) = 3. A chain that agrees with the boundary may add
// an extension E of cost 2 * gates + mixed <= 3; its residual then has exact slack 3 - cost(E).
// Each extension is decided by an existing lower-slack recognizer:
//   cost 3: three mixed, or one gate plus one mixed      -> residual_zero (tight)
//   cost 2: two mixed, or one first-layer gate            -> slack_one_residual
//   cost 1: one mixed                                     -> residual_slack_two::Engine(., 2)
// The exact boundary is residual_slack_two::Engine(., 3). Unknown answers are always retained.
// An extension whose elements are already all in the retained union is not tested (subsumed):
// it cannot change the consequent of the boundary clause.

//
// Lazy weighted cuts (opt-in policies). Let W = 2h + m be a model's boundary weight and w the
// weight of the excluded boundary B. Under the antecedent A (B's first-layer gates and mixed
// primaries are present) a model's boundary is B + E with cost(E) = W - w. If every extension E
// with cost(E) < d is excluded or contains an element of the retained union R, then
//     NOT A  OR  (W >= w + d)  OR  R
// is valid. With d = 4 no threshold is needed (W <= k + 1 = w + 3). `lift` reports d.
//   full     : the eager recognizer above (every extension, all-element subsumption), d = 4.
//   exact    : no extension checks; d is the first nonempty cost level (d = 2 when every
//              primary is already mixed, because no cost-one extension then exists).
//   lift1    : decide only the cost-one extensions (one new mixed primary); d = 2 unless the
//              deadline cut that level short (then d = 1 and R is empty).
//   adaptive : walk cost levels upward, reuse decided answers from a cross-query memo, and skip
//              an extension that meets an already retained element; the first level reached
//              with an untested extension (deadline) sets d and contributes nothing to R.
// Unknown answers returned before the deadline are retained.

#include "residual_slack_two.hpp"
#include "tight_residual.hpp"

#include <algorithm>
#include <array>
#include <map>

namespace synthesis {

enum class SlackThreePolicy : unsigned { full = 0, exact = 1, lift1 = 2, adaptive = 3 };

// Decided residual answers keyed by (gate-leaf count, exact slack, sorted gate columns, sorted
// primary columns), all columns masked by care. Valid for one (target, care) pair; the residual
// query does not depend on the gate budget, so one memo serves every budget.
struct ResidualMemo {
    uint64_t target = 0, care = 0;
    std::map<std::vector<uint64_t>, bool> decided;  // true = feasible
    uint64_t hits = 0, inserts = 0;

    void bind(uint64_t t, uint64_t c) {
        if (t != target || c != care) {
            decided.clear();
            target = t;
            care = c;
        }
    }
    std::vector<uint64_t> key(std::span<const uint64_t> wires, unsigned first, unsigned slack) const {
        std::vector<uint64_t> k{first, slack};
        for (const uint64_t wire : wires) k.push_back(wire & care);
        std::sort(k.begin() + 2, k.begin() + 2 + first);
        std::sort(k.begin() + 2 + first, k.end());
        return k;
    }
    // 0 infeasible, 1 feasible, -1 not decided.
    int find(std::span<const uint64_t> wires, unsigned first, unsigned slack) {
        const auto entry = decided.find(key(wires, first, slack));
        if (entry == decided.end()) return -1;
        ++hits;
        return entry->second ? 1 : 0;
    }
    bool insert(std::span<const uint64_t> wires, unsigned first, unsigned slack, bool feasible) {
        const bool fresh = decided.emplace(key(wires, first, slack), feasible).second;
        inserts += fresh;
        return fresh;
    }
};

struct SlackThreeBoundary {
    residual_slack_two::Answer exact{};
    uint64_t gate_extensions = 0;
    unsigned mixed_extensions = 0;
    unsigned feasible = 0, unknown = 0, excluded = 0, subsumed = 0;
    unsigned tight_calls = 0, slack_one_calls = 0, slack_two_calls = 0;
    uint64_t slack_two_work = 0;
    unsigned lift = 0;             // d of the weighted clause (0 unless the exact query is UNSAT)
    unsigned extension_total = 0;  // number of extensions of cost <= 3
    unsigned covered = 0;          // adaptive: skipped because an element is already retained
    unsigned memo_hits = 0, memo_inserts = 0;
    bool exact_cached = false;
};

inline SlackThreeBoundary slack_three_boundary(
    std::vector<uint64_t> columns, unsigned h, std::span<const uint64_t> primaries,
    unsigned mixed, std::span<const uint64_t> gate_columns, uint64_t target, uint64_t care,
    unsigned work_limit, residual_detail::Clock::time_point deadline, unsigned mode,
    bool symmetric, SlackThreePolicy policy = SlackThreePolicy::full,
    ResidualMemo* memo = nullptr) {
    using Status = residual_directed::Status;
    using Clock = residual_detail::Clock;
    SlackThreeBoundary result;
    result.exact.status = Status::unknown;
    if (columns.size() < 2 || columns.size() > 8 || h == 0 || h > columns.size() || !care ||
        primaries.size() > 6 || gate_columns.size() > 64)
        return result;
    const auto engine = [&](std::vector<uint64_t> wires, unsigned first, unsigned slack) {
        std::vector<residual_directed::Leaf> leaves;
        for (unsigned i = 0; i < wires.size(); ++i) leaves.push_back({i, wires[i], i >= first});
        return residual_slack_two::Engine(
            care, target, work_limit, deadline, mode >= 1, mode >= 1, mode >= 2, mode >= 3,
            mode >= 4, mode >= 5, symmetric)
            .run(std::move(leaves), slack);
    };
    const bool adaptive = policy == SlackThreePolicy::adaptive;
    if (!adaptive) memo = nullptr;
    if (memo) memo->bind(target, care);
    const auto memo_find = [&](const std::vector<uint64_t>& wires, unsigned first, unsigned slack) {
        if (!memo) return -1;
        const int found = memo->find(wires, first, slack);
        result.memo_hits += found >= 0;
        return found;
    };
    const auto memo_insert = [&](const std::vector<uint64_t>& wires, unsigned first, unsigned slack,
                                 bool feasible) {
        if (memo) result.memo_inserts += memo->insert(wires, first, slack, feasible);
    };
    if (const int cached = memo_find(columns, h, 3); cached >= 0) {
        result.exact_cached = true;
        result.exact.status = cached ? Status::sat : Status::unsat;
    } else {
        result.exact = engine(columns, h, 3);
        if (result.exact.status != Status::unknown)
            memo_insert(columns, h, 3, result.exact.status == Status::sat);
    }
    if (result.exact.status != Status::unsat) return result;

    const auto retain = [&](ResidualStatus status) {
        if (status == ResidualStatus::infeasible) {
            ++result.excluded;
            return false;
        }
        if (status == ResidualStatus::feasible) ++result.feasible;
        else ++result.unknown;
        return true;
    };
    const auto covered = [&](unsigned mixed_bits, uint64_t gate_bits) {
        if ((result.mixed_extensions & mixed_bits) == mixed_bits &&
            (result.gate_extensions & gate_bits) == gate_bits) {
            ++result.subsumed;
            return true;
        }
        return false;
    };
    const auto keep = [&](unsigned mixed_bits, uint64_t gate_bits) {
        result.mixed_extensions |= mixed_bits;
        result.gate_extensions |= gate_bits;
    };
    const auto tight = [&](const std::vector<uint64_t>& wires, unsigned first) {
        if (Clock::now() >= deadline) return ResidualStatus::unknown;
        ++result.tight_calls;
        return residual_zero(wires, first, target, care, 4096, ResidualFilterMode::direct,
                             deadline, ResidualBackend::directed);
    };
    const auto slack_one = [&](const std::vector<uint64_t>& wires, unsigned first) {
        if (Clock::now() >= deadline) return ResidualStatus::unknown;
        ++result.slack_one_calls;
        SlackOneStats stats;
        return slack_one_residual(wires, first, target, care, 100000, stats, deadline,
                                  ResidualFilterMode::direct, ResidualBackend::directed);
    };
    const auto slack_two = [&](const std::vector<uint64_t>& wires, unsigned first) {
        if (Clock::now() >= deadline || wires.size() > 8) return ResidualStatus::unknown;
        ++result.slack_two_calls;
        const auto answer = engine(wires, first, 2);
        result.slack_two_work += answer.work;
        return answer.status == Status::sat     ? ResidualStatus::feasible
               : answer.status == Status::unsat ? ResidualStatus::infeasible
                                                : ResidualStatus::unknown;
    };
    std::vector<unsigned> free;
    for (unsigned i = 0; i < primaries.size(); ++i)
        if (!(mixed & (1u << i))) free.push_back(i);
    const auto with_mixed = [&](std::vector<uint64_t> wires, std::initializer_list<unsigned> add) {
        for (const unsigned i : add) wires.push_back(primaries[i]);
        return wires;
    };
    auto with_gate = [&](unsigned gate) {
        auto wires = columns;
        wires.insert(wires.begin() + h, gate_columns[gate]);
        return wires;
    };

    // Unsigned products with a zero factor vanish, so these are C(f,1), C(f,2) + g, C(f,3) + g*f.
    const unsigned f = unsigned(free.size()), g = unsigned(gate_columns.size());
    const std::array<unsigned, 5> level_size{
        0, f, f * (f - 1) / 2 + g, f * (f - 1) * (f - 2) / 6 + g * f, 0};
    result.extension_total = level_size[1] + level_size[2] + level_size[3];
    const auto first_nonempty = [&](unsigned from) {
        while (from <= 3 && !level_size[from]) ++from;
        return from;
    };
    if (policy == SlackThreePolicy::exact) {
        result.lift = first_nonempty(1);
        return result;
    }
    if (policy == SlackThreePolicy::lift1 || adaptive) {
        struct Extension {
            unsigned mixed_bits;
            uint64_t gate_bits;
            std::vector<uint64_t> wires;
            unsigned first, slack;
        };
        const unsigned top = adaptive ? 3 : 1;
        for (unsigned cost = 1; cost <= top; ++cost) {
            std::vector<Extension> level;
            if (cost == 1) {
                for (const unsigned i : free) level.push_back({1u << i, 0, with_mixed(columns, {i}), h, 2});
            } else if (cost == 2) {
                for (unsigned a = 0; a < f; ++a)
                    for (unsigned b = a + 1; b < f; ++b)
                        level.push_back({(1u << free[a]) | (1u << free[b]), 0,
                                         with_mixed(columns, {free[a], free[b]}), h, 1});
                for (unsigned gate = 0; gate < g; ++gate)
                    level.push_back({0, uint64_t{1} << gate, with_gate(gate), h + 1, 1});
            } else {
                for (unsigned a = 0; a < f; ++a)
                    for (unsigned b = a + 1; b < f; ++b)
                        for (unsigned c = b + 1; c < f; ++c)
                            level.push_back({(1u << free[a]) | (1u << free[b]) | (1u << free[c]), 0,
                                             with_mixed(columns, {free[a], free[b], free[c]}), h, 0});
                for (unsigned gate = 0; gate < g; ++gate)
                    for (const unsigned i : free)
                        level.push_back({1u << i, uint64_t{1} << gate,
                                         with_mixed(with_gate(gate), {i}), h + 1, 0});
            }
            const unsigned saved_mixed = result.mixed_extensions;
            const uint64_t saved_gates = result.gate_extensions;
            for (const auto& extension : level) {
                if (adaptive && ((result.mixed_extensions & extension.mixed_bits) ||
                                 (result.gate_extensions & extension.gate_bits))) {
                    ++result.covered;  // any retained element already satisfies the clause
                    continue;
                }
                ResidualStatus status;
                if (const int cached = memo_find(extension.wires, extension.first, extension.slack);
                    cached >= 0) {
                    status = cached ? ResidualStatus::feasible : ResidualStatus::infeasible;
                } else {
                    status = Clock::now() >= deadline ? ResidualStatus::unknown
                             : extension.slack == 0   ? tight(extension.wires, extension.first)
                             : extension.slack == 1   ? slack_one(extension.wires, extension.first)
                                                      : slack_two(extension.wires, extension.first);
                    if (status == ResidualStatus::unknown && Clock::now() >= deadline) {
                        // Untested: this level is incomplete. Drop what it retained.
                        result.mixed_extensions = saved_mixed;
                        result.gate_extensions = saved_gates;
                        result.lift = cost;
                        return result;
                    }
                    if (status != ResidualStatus::unknown)
                        memo_insert(extension.wires, extension.first, extension.slack,
                                    status == ResidualStatus::feasible);
                }
                if (retain(status)) keep(extension.mixed_bits, extension.gate_bits);
            }
        }
        result.lift = first_nonempty(top + 1);
        return result;
    }

    // Cost three first: these extensions carry the most elements, so retaining them early lets
    // more of the costlier lower-cost recognizers be skipped as subsumed.
    for (unsigned a = 0; a < free.size(); ++a)
        for (unsigned b = a + 1; b < free.size(); ++b)
            for (unsigned c = b + 1; c < free.size(); ++c) {
                const unsigned bits = (1u << free[a]) | (1u << free[b]) | (1u << free[c]);
                if (!covered(bits, 0) &&
                    retain(tight(with_mixed(columns, {free[a], free[b], free[c]}), h)))
                    keep(bits, 0);
            }
    for (unsigned gate = 0; gate < gate_columns.size(); ++gate) {
        const uint64_t gate_bit = uint64_t{1} << gate;
        const auto wires = with_gate(gate);
        for (const unsigned i : free)
            if (!covered(1u << i, gate_bit) && retain(tight(with_mixed(wires, {i}), h + 1)))
                keep(1u << i, gate_bit);
    }
    // Cost two.
    for (unsigned a = 0; a < free.size(); ++a)
        for (unsigned b = a + 1; b < free.size(); ++b) {
            const unsigned bits = (1u << free[a]) | (1u << free[b]);
            if (!covered(bits, 0) && retain(slack_one(with_mixed(columns, {free[a], free[b]}), h)))
                keep(bits, 0);
        }
    // A new occurrence of an already present type still consumes two units.
    for (unsigned gate = 0; gate < gate_columns.size(); ++gate) {
        const uint64_t gate_bit = uint64_t{1} << gate;
        if (!covered(0, gate_bit) && retain(slack_one(with_gate(gate), h + 1)))
            keep(0, gate_bit);
    }
    // Cost one.
    for (const unsigned i : free)
        if (!covered(1u << i, 0) && retain(slack_two(with_mixed(columns, {i}), h)))
            keep(1u << i, 0);
    result.lift = 4;
    return result;
}

}  // namespace synthesis
