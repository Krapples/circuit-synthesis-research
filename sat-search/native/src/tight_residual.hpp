#pragma once

#include <array>
#include <bit>
#include <cstdint>
#include <span>
#include <unordered_set>

namespace synthesis {

enum class ResidualStatus { infeasible, feasible, unknown };

// Columns are packed on the original cared rows. The first h columns are
// first-layer occurrences, and the rest are directly read primaries.
inline ResidualStatus tight_residual(std::span<const uint64_t> columns, unsigned h,
                                     uint64_t target, uint64_t care, unsigned work_limit) {
    constexpr unsigned max_leaves = 6;
    if (columns.empty() || columns.size() > max_leaves || h == 0 || h > columns.size())
        return ResidualStatus::unknown;
    const unsigned all = (1u << columns.size()) - 1;
    const unsigned gate_leaves = (1u << h) - 1;
    target &= care;
    std::array<std::unordered_set<uint64_t>, 1u << max_leaves> values;
    for (unsigned mask = 1; mask <= all; ++mask) {
        auto& reachable = values[mask];
        if (std::has_single_bit(mask)) {
            const uint64_t column = columns[std::countr_zero(mask)] & care;
            reachable.insert(column);
            reachable.insert(column ^ care);
            if (mask == all && reachable.contains(target)) return ResidualStatus::feasible;
            continue;
        }
        // Every nontrivial subtree must contain an internal wire. A subtree
        // on primary leaves alone would contain an additional first-layer gate.
        if (!(mask & gate_leaves)) continue;
        const unsigned anchor = mask & (0u - mask);
        for (unsigned left = (mask - 1) & mask; left; left = (left - 1) & mask) {
            if (!(left & anchor)) continue;
            for (uint64_t x : values[left])
                for (uint64_t y : values[mask ^ left]) {
                    if (work_limit == 0) return ResidualStatus::unknown;
                    --work_limit;
                    const uint64_t and_value = x & y, or_value = x | y;
                    if (mask == all) {
                        if (and_value == target || or_value == target) return ResidualStatus::feasible;
                    } else {
                        reachable.insert(and_value);
                        reachable.insert(or_value);
                    }
                }
        }
    }
    return ResidualStatus::infeasible;
}

}  // namespace synthesis
