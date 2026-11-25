#pragma once

#include <algorithm>
#include <bit>
#include <cstdint>
#include <set>
#include <vector>

namespace synthesis {

enum class PairScope { none, edges, all };

struct FirstLayerGate {
    int first;
    int second;
    unsigned table;
};

// Literal positions follow the supplied gate order, then primary input order.
// Targets supply only cared rows. Operator tables use first operand as bit zero.
inline std::vector<uint64_t> distinction_masks(const std::vector<FirstLayerGate>& gates,
                                               const std::vector<int>& zeros, const std::vector<int>& ones,
                                               PairScope scope) {
    if (scope == PairScope::none) return {};
    const auto boundary = [&](int row) {
        uint64_t signature = uint64_t(row) << gates.size();
        for (size_t i = 0; i < gates.size(); ++i) {
            const auto [a, b, table] = gates[i];
            const int index = ((row >> a) & 1) | (((row >> b) & 1) << 1);
            signature |= uint64_t((table >> index) & 1) << i;
        }
        return signature;
    };
    std::vector<uint64_t> zero_signatures, one_signatures;
    for (int row : zeros) zero_signatures.push_back(boundary(row));
    for (int row : ones) one_signatures.push_back(boundary(row));

    std::set<uint64_t> unique;
    for (size_t i = 0; i < zeros.size(); ++i)
        for (size_t j = 0; j < ones.size(); ++j) {
            if (scope == PairScope::edges && std::popcount(unsigned(zeros[i] ^ ones[j])) != 1) continue;
            unique.insert(zero_signatures[i] ^ one_signatures[j]);
        }

    std::vector<uint64_t> ordered(unique.begin(), unique.end()), minimal;
    std::sort(ordered.begin(), ordered.end(), [](uint64_t a, uint64_t b) {
        const int na = std::popcount(a), nb = std::popcount(b);
        return na != nb ? na < nb : a < b;
    });
    for (uint64_t mask : ordered) {
        if (std::none_of(minimal.begin(), minimal.end(), [mask](uint64_t m) { return (m & mask) == m; }))
            minimal.push_back(mask);
    }
    return minimal;
}

}  // namespace synthesis
