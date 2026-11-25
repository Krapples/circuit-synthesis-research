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

#include "residual_slack_two.hpp"
#include "tight_residual.hpp"

namespace synthesis {

struct SlackThreeBoundary {
    residual_slack_two::Answer exact{};
    uint64_t gate_extensions = 0;
    unsigned mixed_extensions = 0;
    unsigned feasible = 0, unknown = 0, excluded = 0, subsumed = 0;
    unsigned tight_calls = 0, slack_one_calls = 0, slack_two_calls = 0;
    uint64_t slack_two_work = 0;
};

inline SlackThreeBoundary slack_three_boundary(
    std::vector<uint64_t> columns, unsigned h, std::span<const uint64_t> primaries,
    unsigned mixed, std::span<const uint64_t> gate_columns, uint64_t target, uint64_t care,
    unsigned work_limit, residual_detail::Clock::time_point deadline, unsigned mode,
    bool symmetric) {
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
    result.exact = engine(columns, h, 3);
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
    return result;
}

}  // namespace synthesis
