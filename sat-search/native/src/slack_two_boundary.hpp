#pragma once

#include "residual_slack_two.hpp"
#include "tight_residual.hpp"

namespace synthesis {

struct SlackTwoBoundary {
    residual_slack_two::Answer exact{};
    uint64_t gate_extensions = 0;
    unsigned mixed_extensions = 0;
    unsigned feasible = 0, unknown = 0, excluded = 0;
};

inline SlackTwoBoundary slack_two_boundary(
    std::vector<uint64_t> columns, unsigned h, std::span<const uint64_t> primaries,
    unsigned mixed, std::span<const uint64_t> gate_columns, uint64_t target, uint64_t care,
    unsigned work_limit, residual_detail::Clock::time_point deadline, unsigned mode,
    unsigned decoder = 0) {
    using Status = residual_directed::Status;
    SlackTwoBoundary result;
    result.exact.status = Status::unknown;
    if (columns.size() < 2 || columns.size() > 8 || h == 0 || h > columns.size() || !care ||
        primaries.size() > 6 || gate_columns.size() > 64)
        return result;
    std::vector<residual_directed::Leaf> leaves;
    for (unsigned i = 0; i < columns.size(); ++i) leaves.push_back({i, columns[i], i >= h});
    result.exact = residual_slack_two::Engine(
        care, target, work_limit, deadline, mode >= 1, mode >= 1, mode >= 2, mode >= 3,
        mode >= 4, mode >= 5, false, decoder)
        .run(std::move(leaves), 2);
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
    const auto tight = [&](unsigned first) {
        if (residual_detail::Clock::now() >= deadline) return ResidualStatus::unknown;
        return residual_zero(columns, first, target, care, 4096, ResidualFilterMode::direct,
                             deadline, ResidualBackend::directed);
    };
    for (unsigned i = 0; i < primaries.size(); ++i) {
        const unsigned first = 1u << i;
        if (mixed & first) continue;
        columns.push_back(primaries[i]);
        SlackOneStats stats;
        const auto single = residual_detail::Clock::now() >= deadline ? ResidualStatus::unknown
            : slack_one_residual(columns, h, target, care, 100000, stats, deadline,
                                 ResidualFilterMode::direct, ResidualBackend::directed);
        if (retain(single)) result.mixed_extensions |= first;
        for (unsigned j = i + 1; j < primaries.size(); ++j) {
            const unsigned second = 1u << j;
            if (mixed & second) continue;
            columns.push_back(primaries[j]);
            if (retain(tight(h))) result.mixed_extensions |= first | second;
            columns.pop_back();
        }
        columns.pop_back();
    }
    // A new occurrence of an already present type still consumes two units.
    columns.insert(columns.begin() + h, 0);
    for (unsigned gate = 0; gate < gate_columns.size(); ++gate) {
        columns[h] = gate_columns[gate];
        if (retain(tight(h + 1))) result.gate_extensions |= uint64_t{1} << gate;
    }
    return result;
}

}  // namespace synthesis
