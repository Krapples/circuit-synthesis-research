#pragma once

#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <span>
#include <unordered_set>
#include <vector>

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

struct SlackOneStats {
    unsigned work = 0, providers = 0, filtered = 0, decoders = 0;
    unsigned completion_case = 0;  // 1: boundary repeated, 2: provider repeated
};

namespace residual_detail {

using Clock = std::chrono::steady_clock;
constexpr unsigned max_boundary = 6;

struct Search {
    uint64_t target, care;
    unsigned work_limit;
    Clock::time_point deadline;
    SlackOneStats& stats;

    bool charge() {
        if (stats.work == work_limit) return false;
        if ((stats.work & 255u) == 0 && Clock::now() >= deadline) return false;
        ++stats.work;
        return true;
    }
};

// Each bit denotes an occurrence. If a signal is repeated, twins contains
// its two occurrence bits. Other equal truth columns are still distinct wires.
class TreeTables {
    using Columns = std::unordered_set<uint64_t>;
    std::array<Columns, 1u << (max_boundary + 1)> columns;
    std::array<bool, 1u << (max_boundary + 1)> ready{};
    Search& search;
    unsigned raw, twins;

    bool valid(unsigned mask) const {
        return std::has_single_bit(mask) || ((mask & ~raw) && mask != twins);
    }

public:
    TreeTables(Search& search, std::span<const uint64_t> signals, unsigned raw, unsigned twins = 0)
        : search(search), raw(raw), twins(twins) {
        for (unsigned i = 0; i < signals.size(); ++i) {
            const unsigned leaf = 1u << i;
            const uint64_t value = signals[i] & search.care;
            columns[leaf].insert(value);
            columns[leaf].insert(value ^ search.care);
            ready[leaf] = true;
        }
    }

    const Columns* table(unsigned mask) {
        auto& out = columns[mask];
        if (ready[mask] || !valid(mask)) return &out;
        const unsigned anchor = mask & (0u - mask);
        for (unsigned left = (mask - 1) & mask; left; left = (left - 1) & mask) {
            if (!(left & anchor)) continue;
            const unsigned right = mask ^ left;
            if (!valid(left) || !valid(right)) continue;
            const auto* a = table(left);
            const auto* b = a ? table(right) : nullptr;
            if (!b) return nullptr;
            for (uint64_t x : *a)
                for (uint64_t y : *b) {
                    if (!search.charge()) return nullptr;
                    const uint64_t value = x & y;
                    out.insert(value);
                    out.insert(value ^ search.care);
                }
        }
        ready[mask] = true;
        return &out;
    }

    ResidualStatus find(unsigned mask) {
        if (!search.charge()) return ResidualStatus::unknown;
        if (!valid(mask)) return ResidualStatus::infeasible;
        if (std::has_single_bit(mask))
            return columns[mask].contains(search.target) ? ResidualStatus::feasible : ResidualStatus::infeasible;
        const unsigned anchor = mask & (0u - mask);
        for (unsigned left = (mask - 1) & mask; left; left = (left - 1) & mask) {
            if (!(left & anchor)) continue;
            const unsigned right = mask ^ left;
            if (!valid(left) || !valid(right)) continue;
            const auto* a = table(left);
            const auto* b = a ? table(right) : nullptr;
            if (!b) return ResidualStatus::unknown;
            for (uint64_t wanted : {search.target, search.target ^ search.care}) {
                std::vector<uint64_t> eligible;
                for (uint64_t x : *a) {
                    if (!search.charge()) return ResidualStatus::unknown;
                    if ((x & wanted) == wanted) eligible.push_back(x);
                }
                if (eligible.empty()) continue;
                for (uint64_t y : *b) {
                    if (!search.charge()) return ResidualStatus::unknown;
                    if ((y & wanted) != wanted) continue;
                    for (uint64_t x : eligible) {
                        if (!search.charge()) return ResidualStatus::unknown;
                        if ((x & y) == wanted) return ResidualStatus::feasible;
                    }
                }
            }
        }
        return ResidualStatus::infeasible;
    }
};

inline std::vector<std::pair<uint64_t, uint64_t>> mixed_label_groups(
    std::span<const uint64_t> signals, uint64_t target, uint64_t care) {
    std::array<uint64_t, 1u << max_boundary> groups{};
    for (uint64_t rows = care; rows; rows &= rows - 1) {
        const uint64_t row = rows & (0u - rows);
        unsigned signature = 0;
        for (uint64_t signal : signals) signature = (signature << 1) | ((signal & row) != 0);
        groups[signature] |= row;
    }
    std::vector<std::pair<uint64_t, uint64_t>> obligations;
    for (uint64_t group : groups)
        if ((group & target) && (group & ~target))
            obligations.emplace_back(group & target, group & ~target);
    return obligations;
}

}  // namespace residual_detail

inline ResidualStatus slack_one_residual(
    std::span<const uint64_t> boundary, unsigned h, uint64_t target, uint64_t care,
    unsigned work_limit, SlackOneStats& stats,
    residual_detail::Clock::time_point deadline = residual_detail::Clock::time_point::max()) {
    using namespace residual_detail;
    stats = {};
    if (boundary.empty() || boundary.size() > max_boundary || h == 0 || h > boundary.size())
        return ResidualStatus::unknown;
    Search search{target & care, care, work_limit, deadline, stats};
    const unsigned next_leaf = 1u << boundary.size();
    const unsigned all = next_leaf - 1;
    const unsigned raw = all ^ ((1u << h) - 1);

    std::vector<uint64_t> signals(boundary.begin(), boundary.end());
    signals.push_back(0);
    for (unsigned i = 0; i < boundary.size(); ++i) {
        const unsigned leaf = 1u << i;
        signals.back() = boundary[i];
        TreeTables trees(search, signals, raw | ((raw & leaf) ? next_leaf : 0), leaf | next_leaf);
        const auto status = trees.find(all | next_leaf);
        if (status == ResidualStatus::feasible) stats.completion_case = 1;
        if (status != ResidualStatus::infeasible) return status;
    }

    TreeTables providers(search, boundary, raw);
    const uint64_t first_row = care & (0u - care);
    for (unsigned inside = 1; inside < all; ++inside) {
        if (std::has_single_bit(inside) || !(inside & ~raw)) continue;
        signals.clear();
        unsigned decoder_raw = 0;
        for (unsigned i = 0; i < boundary.size(); ++i)
            if (!(inside & (1u << i))) {
                if (i >= h) decoder_raw |= 1u << signals.size();
                signals.push_back(boundary[i]);
            }
        const auto groups = mixed_label_groups(signals, search.target, care);
        const unsigned provider_bit = 1u << signals.size();
        signals.resize(signals.size() + 2);
        const auto* candidates = providers.table(inside);
        if (!candidates) return ResidualStatus::unknown;
        for (uint64_t provider : *candidates) {
            // A decoder is free to complement this wire, so check each phase
            // class once. Group obligations may choose different phases.
            if (provider & first_row) continue;
            if (!search.charge()) return ResidualStatus::unknown;
            ++stats.providers;
            bool compatible = true;
            for (auto [ones, zeros] : groups) {
                const bool direct = (provider & ones) == ones && !(provider & zeros);
                const bool inverse = (provider & zeros) == zeros && !(provider & ones);
                if (!direct && !inverse) {
                    compatible = false;
                    break;
                }
            }
            if (!compatible) {
                ++stats.filtered;
                continue;
            }
            ++stats.decoders;
            signals[signals.size() - 2] = signals.back() = provider;
            const unsigned twins = provider_bit | (provider_bit << 1);
            TreeTables decoder(search, signals, decoder_raw, twins);
            const auto status = decoder.find((1u << signals.size()) - 1);
            if (status == ResidualStatus::feasible) stats.completion_case = 2;
            if (status != ResidualStatus::infeasible) return status;
        }
    }
    return ResidualStatus::infeasible;
}

struct SlackOneExtension {
    ResidualStatus exact;
    unsigned feasible = 0, unknown = 0;
};

inline SlackOneExtension slack_one_extensions(
    std::vector<uint64_t> boundary, unsigned h, std::span<const uint64_t> primaries, unsigned mixed,
    uint64_t target, uint64_t care, unsigned work_limit, unsigned tight_work_limit, SlackOneStats& stats,
    residual_detail::Clock::time_point deadline = residual_detail::Clock::time_point::max()) {
    SlackOneExtension result{slack_one_residual(boundary, h, target, care, work_limit, stats, deadline)};
    if (result.exact != ResidualStatus::infeasible) return result;
    boundary.push_back(0);
    for (unsigned i = 0; i < primaries.size(); ++i) {
        const unsigned bit = 1u << i;
        if (mixed & bit) continue;
        boundary.back() = primaries[i];
        const auto status = residual_detail::Clock::now() >= deadline ? ResidualStatus::unknown
            : tight_residual(boundary, h, target, care, tight_work_limit);
        if (status == ResidualStatus::feasible) result.feasible |= bit;
        if (status == ResidualStatus::unknown) result.unknown |= bit;
    }
    return result;
}

}  // namespace synthesis
