#pragma once

// Fully reified sequential counter (opt-in companion of Percy's one-way Sinz counter).
//
// For literals x_0..x_{n-1} and a cap K >= 1, s[i][j] <=> |{l <= i : x_l}| >= j + 1 for j < K.
// Both directions are encoded, so every s is a function of x:
//   row 0      : s[0][0] <=> x_0, s[0][j] false for j >= 1
//   row i >= 1 : s[i][j] <=> s[i-1][j] OR (x_i AND s[i-1][j-1])   (s[i-1][-1] = true)
// The cap is the usual overflow clause NOT x_i OR NOT s[i-1][K-1]. thresholds[t] (1 <= t <= K)
// is s[n-1][t-1] <=> count >= t; thresholds[0] is unused (-1). A one-way register may be true
// while the count is low, so only a reified threshold can be falsified by a model and used
// positively in a learned clause.
//
// Literals use ABC's encoding (2 * var + negated). `fresh()` returns a new positive literal and
// `add(clause)` takes a std::vector<int>.

#include <vector>

namespace synthesis {

template <class Fresh, class Add>
std::vector<int> reified_at_most(const std::vector<int>& x, int K, Fresh&& fresh, Add&& add) {
    const int n = int(x.size());
    std::vector<int> thresholds(size_t(K < 0 ? 1 : K + 1), -1);
    if (K < 0) {
        add(std::vector<int>{});
        return thresholds;
    }
    if (n == 0 || K == 0) {
        for (const int l : x) add(std::vector<int>{l ^ 1});
        for (int t = 1; t <= K; ++t) {
            thresholds[t] = fresh();
            add(std::vector<int>{thresholds[t] ^ 1});
        }
        return thresholds;
    }
    std::vector<std::vector<int>> s(static_cast<size_t>(n), std::vector<int>(static_cast<size_t>(K)));
    for (auto& row : s)
        for (auto& v : row) v = fresh();
    add({x[0] ^ 1, s[0][0]});
    add({s[0][0] ^ 1, x[0]});
    for (int j = 1; j < K; ++j) add({s[0][j] ^ 1});
    for (int i = 1; i < n; ++i) {
        // j = 0: s[i][0] <=> s[i-1][0] OR x_i.
        add({s[i - 1][0] ^ 1, s[i][0]});
        add({x[i] ^ 1, s[i][0]});
        add({s[i][0] ^ 1, s[i - 1][0], x[i]});
        for (int j = 1; j < K; ++j) {
            add({s[i - 1][j] ^ 1, s[i][j]});
            add({x[i] ^ 1, s[i - 1][j - 1] ^ 1, s[i][j]});
            add({s[i][j] ^ 1, s[i - 1][j], x[i]});
            add({s[i][j] ^ 1, s[i - 1][j], s[i - 1][j - 1]});
        }
        add({x[i] ^ 1, s[i - 1][K - 1] ^ 1});
    }
    for (int t = 1; t <= K; ++t) thresholds[t] = s[n - 1][t - 1];
    return thresholds;
}

}  // namespace synthesis
