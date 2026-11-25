// Exhaustive check of synthesis::reified_at_most (native/src/reified_counter.hpp).
// For every small (n, K) and every assignment of x, the counter clauses must have exactly one
// satisfying assignment of the auxiliary variables when count(x) <= K and none otherwise, and in
// that assignment thresholds[t] must equal [count(x) >= t].
#include <bit>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include "../src/reified_counter.hpp"

int main() {
    unsigned long long cases = 0, assignments = 0;
    for (int n = 1; n <= 6; ++n)
        for (int K = 0; K <= n + 1; ++K) {
            int next = n;  // vars 0..n-1 are x
            std::vector<int> x;
            for (int i = 0; i < n; ++i) x.push_back(2 * i);
            std::vector<std::vector<int>> clauses;
            const auto thresholds = synthesis::reified_at_most(
                x, K, [&] { return 2 * next++; }, [&](std::vector<int> c) { clauses.push_back(std::move(c)); });
            const int aux = next - n;
            if (aux > 20) continue;  // keep the exhaustive auxiliary enumeration small
            for (unsigned xs = 0; xs < (1u << n); ++xs) {
                const int count = std::popcount(xs);
                unsigned solutions = 0;
                for (unsigned long long as = 0; as < (1ull << aux); ++as) {
                    const auto value = [&](int lit) {
                        const int var = lit >> 1;
                        const bool v = var < n ? (xs >> var & 1) : (as >> (var - n) & 1);
                        return v != bool(lit & 1);
                    };
                    bool ok = true;
                    for (const auto& c : clauses) {
                        bool sat = false;
                        for (const int l : c) sat = sat || value(l);
                        if (!sat) { ok = false; break; }
                    }
                    if (!ok) continue;
                    ++solutions;
                    for (int t = 1; t <= K; ++t)
                        if (value(thresholds[t]) != (count >= t)) {
                            std::printf("threshold mismatch n=%d K=%d x=%u t=%d\n", n, K, xs, t);
                            return 1;
                        }
                }
                if (solutions != (count <= K ? 1u : 0u)) {
                    std::printf("solution count %u for n=%d K=%d x=%u count=%d\n", solutions, n, K, xs, count);
                    return 1;
                }
                ++assignments;
            }
            ++cases;
        }
    std::printf("{\"counter_shapes\":%llu,\"x_assignments\":%llu}\n", cases, assignments);
    return 0;
}
