#pragma once

#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <span>
#include <unordered_set>
#include <vector>

#include "residual_parity_filter.hpp"
#include "residual_directed.hpp"

namespace synthesis {

enum class ResidualStatus { infeasible, feasible, unknown };
enum class ResidualFilterMode { off, root, parity, direct };
enum class ResidualBackend { columns, directed, dominance };

struct ResidualWitness {
    unsigned repeated = 0, provider_leaves = 0;
    uint64_t provider_column = 0;
    residual_directed::Witness provider, decoder;
};

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
    unsigned joins = 0, root_splits = 0, root_rejected = 0;
    unsigned allocations = 0, parity_rejected = 0, direct_queries = 0;
    unsigned directed_states = 0;
};

namespace residual_detail {

using Clock = std::chrono::steady_clock;
constexpr unsigned max_boundary = 6;

struct Search {
    uint64_t target, care;
    unsigned work_limit;
    Clock::time_point deadline;
    SlackOneStats& stats;
    ResidualFilterMode mode;
    ResidualBackend backend;

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
    std::span<const uint64_t> signals;
    unsigned raw, twins;

    bool valid(unsigned mask) const {
        return std::has_single_bit(mask) || ((mask & ~raw) && mask != twins);
    }

    ResidualStatus directed(unsigned mask, uint64_t target, residual_directed::Witness* witness) {
        std::vector<residual_directed::Leaf> leaves;
        for (; mask; mask &= mask - 1) {
            const unsigned i = std::countr_zero(mask);
            const unsigned bit = 1u << i;
            const unsigned wire = (twins & bit) ? std::countr_zero(twins) : i;
            leaves.push_back({wire, signals[i] & search.care, bool(raw & bit)});
        }
        // A dummy zero row leaves only the structural question when care is empty.
        const uint64_t care = search.care ? search.care : 1;
        auto result = residual_directed::Solver(
            std::move(leaves), care, search.work_limit - search.stats.work, search.deadline,
            search.backend == ResidualBackend::dominance).run(target, care ^ target);
        search.stats.work += unsigned(result.work);
        search.stats.joins += unsigned(result.joins);
        search.stats.directed_states += unsigned(result.states);
        if (result.status == residual_directed::Status::unknown) return ResidualStatus::unknown;
        if (result.status == residual_directed::Status::unsat) return ResidualStatus::infeasible;
        if (witness) *witness = std::move(result.witness);
        return ResidualStatus::feasible;
    }

public:
    TreeTables(Search& search, std::span<const uint64_t> signals, unsigned raw, unsigned twins = 0)
        : search(search), signals(signals), raw(raw), twins(twins) {
        for (unsigned i = 0; i < signals.size(); ++i) {
            const unsigned leaf = 1u << i;
            const uint64_t value = signals[i] & search.care;
            columns[leaf].insert(value);
            columns[leaf].insert(value ^ search.care);
            ready[leaf] = true;
        }
    }

    residual_filter::Fibers projection(unsigned mask) const {
        std::array<uint64_t, max_boundary + 1> selected;
        unsigned count = 0;
        for (; mask; mask &= mask - 1) selected[count++] = signals[std::countr_zero(mask)];
        return residual_filter::fibers(std::span(selected).first(count), search.care);
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
                    ++search.stats.joins;
                    const uint64_t value = x & y;
                    out.insert(value);
                    out.insert(value ^ search.care);
                }
        }
        ready[mask] = true;
        return &out;
    }

    ResidualStatus find(unsigned mask, uint64_t target, residual_directed::Witness* witness = nullptr) {
        if (!search.charge()) return ResidualStatus::unknown;
        if (!valid(mask)) return ResidualStatus::infeasible;
        if (search.backend != ResidualBackend::columns) return directed(mask, target, witness);
        if (std::has_single_bit(mask))
            return columns[mask].contains(target) ? ResidualStatus::feasible : ResidualStatus::infeasible;
        const unsigned anchor = mask & (0u - mask);
        for (unsigned left = (mask - 1) & mask; left; left = (left - 1) & mask) {
            if (!(left & anchor)) continue;
            const unsigned right = mask ^ left;
            if (!valid(left) || !valid(right)) continue;
            ++search.stats.root_splits;
            std::array<bool, 2> possible{true, true};
            if (search.mode != ResidualFilterMode::off) {
                if (!search.charge()) return ResidualStatus::unknown;
                const auto a = projection(left), b = projection(right);
                possible = {residual_filter::root_and_possible(a, b, target),
                            residual_filter::root_and_possible(a, b, target ^ search.care)};
                search.stats.root_rejected += unsigned(!possible[0]) + unsigned(!possible[1]);
                if (!possible[0] && !possible[1]) continue;
            }
            const auto* a = table(left);
            const auto* b = a ? table(right) : nullptr;
            if (!b) return ResidualStatus::unknown;
            for (unsigned phase = 0; phase < 2; ++phase) {
                if (!possible[phase]) continue;
                const uint64_t wanted = target ^ (phase ? search.care : 0);
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
                        ++search.stats.joins;
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

inline ResidualStatus residual_zero(
    std::span<const uint64_t> columns, unsigned h, uint64_t target, uint64_t care,
    unsigned work_limit, ResidualFilterMode mode,
    residual_detail::Clock::time_point deadline = residual_detail::Clock::time_point::max(),
    ResidualBackend backend = ResidualBackend::columns, ResidualWitness* witness = nullptr) {
    using namespace residual_detail;
    if (mode == ResidualFilterMode::off && backend == ResidualBackend::columns)
        return tight_residual(columns, h, target, care, work_limit);
    if (columns.empty() || columns.size() > max_boundary || h == 0 || h > columns.size())
        return ResidualStatus::unknown;
    SlackOneStats stats;
    Search search{target & care, care, work_limit, deadline, stats, mode, backend};
    const unsigned all = (1u << columns.size()) - 1;
    TreeTables trees(search, columns, all ^ ((1u << h) - 1));
    return trees.find(all, search.target, witness ? &witness->decoder : nullptr);
}

inline ResidualStatus slack_one_residual(
    std::span<const uint64_t> boundary, unsigned h, uint64_t target, uint64_t care,
    unsigned work_limit, SlackOneStats& stats,
    residual_detail::Clock::time_point deadline = residual_detail::Clock::time_point::max(),
    ResidualFilterMode mode = ResidualFilterMode::off,
    ResidualBackend backend = ResidualBackend::columns, ResidualWitness* witness = nullptr) {
    using namespace residual_detail;
    stats = {};
    if (boundary.empty() || boundary.size() > max_boundary || h == 0 || h > boundary.size())
        return ResidualStatus::unknown;
    Search search{target & care, care, work_limit, deadline, stats, mode, backend};
    const unsigned next_leaf = 1u << boundary.size();
    const unsigned all = next_leaf - 1;
    const unsigned raw = all ^ ((1u << h) - 1);

    std::vector<uint64_t> signals(boundary.begin(), boundary.end());
    signals.push_back(0);
    for (unsigned i = 0; i < boundary.size(); ++i) {
        const unsigned leaf = 1u << i;
        signals.back() = boundary[i];
        TreeTables trees(search, signals, raw | ((raw & leaf) ? next_leaf : 0), leaf | next_leaf);
        const auto status = trees.find(all | next_leaf, search.target, witness ? &witness->decoder : nullptr);
        if (status == ResidualStatus::feasible) {
            stats.completion_case = 1;
            if (witness) witness->repeated = i;
        }
        if (status != ResidualStatus::infeasible) return status;
    }

    TreeTables providers(search, boundary, raw);
    const uint64_t first_row = care & (0u - care);
    for (unsigned inside = 1; inside < all; ++inside) {
        if (std::has_single_bit(inside) || !(inside & ~raw)) continue;
        ++stats.allocations;
        residual_filter::ParityComponents components;
        if (mode >= ResidualFilterMode::parity) {
            if (!search.charge()) return ResidualStatus::unknown;
            components = residual_filter::provider_components(
                providers.projection(inside), providers.projection(all ^ inside), search.target, care);
            if (!components.consistent) {
                ++stats.parity_rejected;
                continue;
            }
        }
        signals.clear();
        unsigned decoder_raw = 0;
        for (unsigned i = 0; i < boundary.size(); ++i)
            if (!(inside & (1u << i))) {
                if (i >= h) decoder_raw |= 1u << signals.size();
                signals.push_back(boundary[i]);
            }
        const unsigned provider_bit = 1u << signals.size();
        const auto groups = mixed_label_groups(signals, search.target, care);
        signals.resize(signals.size() + 2);
        const unsigned twins = provider_bit | (provider_bit << 1);
        const auto try_decoder = [&](uint64_t provider, residual_directed::Witness provider_tree = {}) {
            ++stats.decoders;
            signals[signals.size() - 2] = signals.back() = provider;
            TreeTables decoder(search, signals, decoder_raw, twins);
            const auto status = decoder.find((1u << signals.size()) - 1, search.target,
                                             witness ? &witness->decoder : nullptr);
            if (status != ResidualStatus::feasible) return status;
            if (witness) {
                if (!provider_tree) {
                    const auto found = providers.find(inside, provider, &provider_tree);
                    if (found != ResidualStatus::feasible) return ResidualStatus::unknown;
                }
                witness->provider = std::move(provider_tree);
                witness->provider_leaves = inside;
                witness->provider_column = provider;
            }
            stats.completion_case = 2;
            return status;
        };
        // Anchor one component to quotient by global complement. Only use
        // this route when at most four exact provider queries are needed.
        const auto count = components.sides.size();
        if (mode == ResidualFilterMode::direct && count > 0 && count <= 3) {
            for (unsigned flip = 0; flip < (1u << (count - 1)); ++flip) {
                ++stats.direct_queries;
                uint64_t provider = components.sides[0][0];
                for (unsigned i = 1; i < count; ++i)
                    provider |= components.sides[i][(flip >> (i - 1)) & 1];
                residual_directed::Witness provider_tree;
                const auto status = providers.find(inside, provider, witness ? &provider_tree : nullptr);
                if (status == ResidualStatus::unknown) return status;
                if (status == ResidualStatus::infeasible) continue;
                ++stats.providers;
                const auto decoded = try_decoder(provider, std::move(provider_tree));
                if (decoded != ResidualStatus::infeasible) return decoded;
            }
            continue;
        }
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
            const auto status = try_decoder(provider);
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
    residual_detail::Clock::time_point deadline = residual_detail::Clock::time_point::max(),
    ResidualFilterMode mode = ResidualFilterMode::off,
    ResidualBackend backend = ResidualBackend::columns, ResidualWitness* witness = nullptr) {
    SlackOneExtension result{
        slack_one_residual(boundary, h, target, care, work_limit, stats, deadline, mode, backend, witness)};
    if (result.exact != ResidualStatus::infeasible) return result;
    boundary.push_back(0);
    for (unsigned i = 0; i < primaries.size(); ++i) {
        const unsigned bit = 1u << i;
        if (mixed & bit) continue;
        boundary.back() = primaries[i];
        const auto status = residual_detail::Clock::now() >= deadline ? ResidualStatus::unknown
            : residual_zero(boundary, h, target, care, tight_work_limit, mode, deadline, backend);
        if (status == ResidualStatus::feasible) result.feasible |= bit;
        if (status == ResidualStatus::unknown) result.unknown |= bit;
    }
    return result;
}

}  // namespace synthesis
