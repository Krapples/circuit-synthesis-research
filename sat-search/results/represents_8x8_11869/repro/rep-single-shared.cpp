#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>

using Rows = std::uint64_t;
using Relation = std::array<Rows, 64>;
constexpr unsigned n = 15;
constexpr unsigned all_inputs = (1u << n) - 1;
constexpr unsigned shared_bit = 1u << n;
constexpr Rows positive = 7583035862004050432ull;
constexpr Rows negative = ~positive;

Rows compatible(const Relation& a, const Relation& b, unsigned row, Rows opposite) {
    return (a[row] & opposite) && (b[row] & opposite);
}

bool works(const std::vector<Relation>& map, unsigned shared, unsigned left, unsigned right,
           Rows required, Rows opposite) {
    Rows forced = 0;
    Rows closure = 0;
    for (Rows scan = required; scan; scan &= scan - 1) {
        const auto row = std::countr_zero(scan);
        if (compatible(map[left], map[right], row, opposite)) {
            forced |= Rows{1} << row;
            closure |= map[shared][row];
        }
    }
    for (; forced; forced &= forced - 1) {
        const auto row = std::countr_zero(forced);
        if (compatible(map[left], map[right], row, opposite & closure)) {
            return false;
        }
    }
    return true;
}

Rows possibilities(const std::vector<Relation>& map, unsigned mask, Rows shared_column,
                   bool upward, Rows required, Rows opposite) {
    Rows possible = 0;
    for (auto remaining = required; remaining; remaining &= remaining - 1) {
        const auto row = std::countr_zero(remaining);
        const auto row_bit = Rows{1} << row;
        Rows conflicts = map[mask & all_inputs][row] & opposite;
        if (mask & shared_bit) {
            const bool value = (shared_column & row_bit) != 0;
            if (upward && value) conflicts &= shared_column;
            if (!upward && !value) conflicts &= ~shared_column;
        }
        if (!conflicts) possible |= row_bit;
    }
    return possible;
}

bool top_split(const std::vector<Relation>& upper, const std::vector<Relation>& lower,
               unsigned support, Rows shared_column, Rows pos, Rows neg) {
    if (std::has_single_bit(support)) {
        return possibilities(upper, support, shared_column, true, pos, neg) == pos;
    }
    for (unsigned left = (support - 1) & support; left; left = (left - 1) & support) {
        const auto right = left ^ support;
        if (left > right) continue;
        if ((possibilities(upper, left, shared_column, true, pos, neg) |
             possibilities(upper, right, shared_column, true, pos, neg)) == pos) return true;
        if ((possibilities(lower, left, shared_column, false, neg, pos) |
             possibilities(lower, right, shared_column, false, neg, pos)) == neg) return true;
    }
    return false;
}

bool root_and_children(const std::vector<Relation>& upper, const std::vector<Relation>& lower,
                       unsigned left, unsigned right, Rows shared_column, bool upward) {
    const auto& map = upward ? upper : lower;
    const auto required = upward ? positive : negative;
    const auto opposite = upward ? negative : positive;
    const auto lmask = left | shared_bit;
    const auto rmask = right | shared_bit;
    const auto lposs = possibilities(map, lmask, shared_column, upward, required, opposite);
    const auto rposs = possibilities(map, rmask, shared_column, upward, required, opposite);
    if ((lposs | rposs) != required) return false;
    const auto lneed = required & ~rposs;
    const auto rneed = required & ~lposs;
    if (upward) {
        return top_split(upper, lower, lmask, shared_column, lneed, negative) &&
               top_split(upper, lower, rmask, shared_column, rneed, negative);
    }
    return top_split(upper, lower, lmask, shared_column, positive, lneed) &&
           top_split(upper, lower, rmask, shared_column, positive, rneed);
}

int main() {
    std::array<unsigned, 64> input{};
    std::array<Rows, n> ones{};
    for (unsigned u = 0; u < 8; ++u) {
        for (unsigned v = 0; v < 8; ++v) {
            auto index = 8 * u + v;
            input[index] = (u ? 1u << (u - 1) : 0u) | (1u << (7 + v));
            for (unsigned bit = 0; bit < n; ++bit) {
                if (input[index] & (1u << bit)) ones[bit] |= Rows{1} << index;
            }
        }
    }
    std::vector<Relation> upper(1u << n);
    std::vector<Relation> lower(1u << n);
    upper[0].fill(~Rows{0});
    lower[0].fill(~Rows{0});
    for (unsigned mask = 1; mask <= all_inputs; ++mask) {
        const auto bit = std::countr_zero(mask);
        const auto rest = mask & (mask - 1);
        for (unsigned point = 0; point < 64; ++point) {
            const bool high = (input[point] & (1u << bit)) != 0;
            upper[mask][point] = upper[rest][point] & (high ? ones[bit] : ~Rows{0});
            lower[mask][point] = lower[rest][point] & (high ? ~Rows{0} : ~ones[bit]);
        }
    }
    std::array<unsigned, n + 1> or_feasible{};
    std::array<unsigned, n + 1> and_feasible{};
    unsigned or_with_children = 0;
    unsigned and_with_children = 0;
    for (unsigned shared = 0; shared < all_inputs; ++shared) {
        const auto private_inputs = all_inputs ^ shared;
        const auto count = std::popcount(shared);
        for (unsigned left = private_inputs;; left = (left - 1) & private_inputs) {
            const auto right = left ^ private_inputs;
            if (left < right && (shared || left)) {
                const auto can_or = works(upper, shared, left, right, positive, negative);
                const auto can_and = works(lower, shared, left, right, negative, positive);
                or_feasible[count] += can_or;
                and_feasible[count] += can_and;
                if ((can_or || can_and) && count && count <= 2) {
                    auto a = ones[std::countr_zero(shared)];
                    auto b = ones[std::countr_zero(shared & (shared - 1) ? shared & (shared - 1) : shared)];
                    for (auto column : {a & b, a | b}) {
                        if (can_or && root_and_children(upper, lower, left, right, column, true)) {
                            ++or_with_children;
                            std::cout << "OR survivor " << shared << ' ' << left << ' ' << right << ' ' << column << '\n';
                        }
                        if (can_and && root_and_children(upper, lower, left, right, column, false)) {
                            ++and_with_children;
                            std::cout << "AND survivor " << shared << ' ' << left << ' ' << right << ' ' << column << '\n';
                        }
                        if (a == b) break;
                    }
                }
            }
            if (!left) break;
        }
    }
    for (unsigned count = 0; count <= n; ++count) {
        std::cout << count << ' ' << or_feasible[count] << ' ' << and_feasible[count] << '\n';
    }
    std::cout << "With necessary child splits: " << or_with_children << ' ' << and_with_children << '\n';
}
