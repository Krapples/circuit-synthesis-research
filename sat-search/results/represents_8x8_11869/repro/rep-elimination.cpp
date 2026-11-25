#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

using Bits = std::uint64_t;
constexpr Bits target = 7583035862004050432ull;
using Clock = std::chrono::steady_clock;

struct State {
    Bits pos, neg;
    std::vector<Bits> cols;
    bool operator==(const State&) const = default;
};

struct Key {
    State state;
    int budget;
    int depth;
    bool operator==(const Key&) const = default;
};

struct Hash {
    std::size_t operator()(const Key& key) const {
        std::size_t out = key.budget ^ (key.depth << 8);
        auto mix = [&out](Bits x) { out ^= static_cast<std::size_t>(x) + 0x9e3779b97f4a7c15ull + (out << 6) + (out >> 2); };
        mix(key.state.pos);
        mix(key.state.neg);
        for (const auto column : key.state.cols) mix(column);
        return out;
    }
};

State canonical(Bits pos, Bits neg, std::vector<Bits> cols) {
    const auto known = pos | neg;
    for (auto& column : cols) column &= known;
    std::erase_if(cols, [known](auto c) { return c == 0 || c == known; });
    std::sort(cols.begin(), cols.end());
    cols.erase(std::unique(cols.begin(), cols.end()), cols.end());
    return {pos, neg, std::move(cols)};
}

State restrict_input(const State& state, std::size_t feature, bool value) {
    const auto col = state.cols[feature];
    const auto keep = value ? col : ~col;
    return canonical(state.pos & keep, state.neg & keep, state.cols);
}

State merge_pair(const State& state, std::size_t a, std::size_t b, Bits output) {
    auto cols = state.cols;
    cols[a] = output;
    cols.erase(cols.begin() + b);
    return canonical(state.pos, state.neg, std::move(cols));
}

enum class Result { excluded, open, deadline };

bool joins_all(unsigned essential, const std::array<unsigned, 64>& groups) {
    unsigned component = essential & (0u - essential);
    unsigned old = 0;
    while (component != old) {
        old = component;
        for (auto group : groups) {
            if (group & component) component |= group;
        }
    }
    return component == essential;
}

bool no_tight_formula(const State& state, const std::array<unsigned, 64>& masks, unsigned essential) {
    std::array<unsigned, 64> per_positive{}, per_negative{};
    for (auto p = state.pos; p; p &= p - 1) {
        const auto a = std::countr_zero(p);
        for (auto q = state.neg; q; q &= q - 1) {
            const auto b = std::countr_zero(q);
            const auto delta = masks[a] & ~masks[b] & essential;
            if (!delta) return true;
            if (std::has_single_bit(delta)) {
                per_positive[a] |= delta;
                per_negative[b] |= delta;
            }
        }
    }
    return joins_all(essential, per_positive) && joins_all(essential, per_negative);
}

class Elimination {
    const Clock::time_point end;
    std::unordered_map<Key, bool, Hash> cache;
    std::uint64_t nodes = 0;

public:
    explicit Elimination(Clock::time_point deadline) : end(deadline) {}
    std::uint64_t visited() const { return nodes; }

    Result prove(const State& state, int budget, int depth) {
        if (budget < 0) return Result::excluded;
        if (!state.pos || !state.neg) return Result::open;
        if (state.pos & state.neg) return Result::excluded;
        if ((++nodes & 4095) == 0 && Clock::now() >= end) return Result::deadline;
        const auto width = state.cols.size();
        const auto all = static_cast<unsigned>((1u << width) - 1);
        std::array<unsigned, 64> row_masks{};
        for (std::size_t bit = 0; bit < width; ++bit) {
            for (auto col = state.cols[bit]; col; col &= col - 1) {
                row_masks[std::countr_zero(col)] |= 1u << bit;
            }
        }
        std::array<std::vector<std::pair<Bits, Bits>>, 15> single;
        std::array<std::array<std::vector<std::pair<Bits, Bits>>, 15>, 15> double_diff;
        unsigned essential = 0;
        for (auto p = state.pos; p; p &= p - 1) {
            const auto a = std::countr_zero(p);
            for (auto q = state.neg; q; q &= q - 1) {
                const auto b = std::countr_zero(q);
                const auto delta = row_masks[a] & (all ^ row_masks[b]);
                if (!delta) return Result::excluded;
                if (std::has_single_bit(delta)) {
                    essential |= delta;
                    single[std::countr_zero(delta)].emplace_back(Bits{1} << a, Bits{1} << b);
                } else {
                    const auto rest = delta & (delta - 1);
                    if (std::has_single_bit(rest)) {
                        double_diff[std::countr_zero(delta)][std::countr_zero(rest)]
                            .emplace_back(Bits{1} << a, Bits{1} << b);
                    }
                }
            }
        }
        const auto base = std::popcount(essential) - 1;
        if (base > budget) return Result::excluded;
        if (base == budget && base >= 1 && no_tight_formula(state, row_masks, essential)) return Result::excluded;
        if (!depth || base < 2) return Result::open;
        Key key{state, budget, depth};
        if (const auto hit = cache.find(key); hit != cache.end()) {
            return hit->second ? Result::excluded : Result::open;
        }
        std::array<std::array<std::array<int, 4>, 2>, 15> restricted{};
        auto check_restriction = [&](unsigned input, bool value, unsigned cost) {
            auto& entry = restricted[input][value][cost];
            if (!entry) {
                const auto verdict = prove(restrict_input(state, input, value), budget - cost, depth - 1);
                if (verdict == Result::deadline) return verdict;
                entry = verdict == Result::excluded ? 1 : -1;
            }
            return entry > 0 ? Result::excluded : Result::open;
        };
        auto loses = [](const auto& comparisons, const Bits col) {
            return std::any_of(comparisons.begin(), comparisons.end(),
                               [col](auto pair) { return !(pair.first & col) || (pair.second & col); });
        };
        const auto done = [&](bool excluded) {
            cache.emplace(std::move(key), excluded);
            return excluded ? Result::excluded : Result::open;
        };
        for (unsigned a = 0; a < width; ++a) {
            for (unsigned b = a + 1; b < width; ++b) {
                for (bool op_or : {true, false}) {
                    const auto col = op_or ? state.cols[a] | state.cols[b] : state.cols[a] & state.cols[b];
                    if (col == 0 || col == (state.pos | state.neg) ||
                        std::binary_search(state.cols.begin(), state.cols.end(), col)) continue;
                    const bool needs_a = loses(single[a], col);
                    const bool needs_b = loses(single[b], col);
                    const bool needs_either = loses(double_diff[a][b], col);
                    for (unsigned repeated = 0; repeated < 4; ++repeated) {
                        if ((needs_a && !(repeated & 1)) || (needs_b && !(repeated & 2)) ||
                            (needs_either && !repeated)) continue;
                        bool excluded = false;
                        for (bool controlling : {true, false}) {
                            for (unsigned side = 0; side < 2; ++side) {
                                const auto input = side ? b : a;
                                const auto paid = 1 + ((repeated >> side) & 1) + controlling;
                                const auto check = check_restriction(input, controlling == op_or, paid);
                                if (check == Result::deadline) return check;
                                if (check == Result::excluded) { excluded = true; break; }
                            }
                            if (excluded) break;
                        }
                        if (!excluded && !repeated) {
                            const auto check = prove(merge_pair(state, a, b, col), budget - 1, depth - 1);
                            if (check == Result::deadline) return check;
                            excluded = check == Result::excluded;
                        }
                        if (!excluded) return done(false);
                    }
                }
            }
        }
        return done(true);
    }
};

void enumerate_three(std::array<int, 256>& costs, std::vector<unsigned>& signals, int gates) {
    if (gates == 4) return;
    const auto width = signals.size();
    for (std::size_t a = 0; a < width; ++a) {
        for (std::size_t b = a + 1; b < width; ++b) {
            for (auto word : {signals[a] & signals[b], signals[a] | signals[b]}) {
                if (std::find(signals.begin(), signals.end(), word) != signals.end()) continue;
                costs[word] = std::min(costs[word], gates + 1);
                signals.push_back(word);
                enumerate_three(costs, signals, gates + 1);
                signals.pop_back();
            }
        }
    }
}

int validate_three() {
    std::array<int, 256> costs;
    costs.fill(100);
    std::vector<unsigned> signals{0, 255, 170, 204, 240};
    for (auto word : signals) costs[word] = 0;
    enumerate_three(costs, signals, 0);
    Elimination check(Clock::now() + std::chrono::seconds(30));
    int tested = 0;
    for (unsigned labels = 0; labels < 6561; ++labels) {
        Bits pos = 0, neg = 0;
        auto packed = labels;
        for (unsigned row = 0; row < 8; ++row) {
            const auto value = packed % 3;
            packed /= 3;
            if (value == 1) neg |= Bits{1} << row;
            if (value == 2) pos |= Bits{1} << row;
        }
        int known = 100;
        for (unsigned word = 0; word < costs.size(); ++word) {
            if ((word & pos) == pos && !(word & neg)) known = std::min(known, costs[word]);
        }
        if (known == 100) continue;
        const auto verdict = check.prove(canonical(pos, neg, {170, 204, 240}), known, 3);
        if (verdict != Result::open) {
            std::cerr << "Unexpected result for " << pos << ' ' << neg << " at " << known << '\n';
            return 1;
        }
        ++tested;
    }
    std::cout << tested << " satisfiable three-input partial labelings checked at their exact size\n";
    return 0;
}

int main(int argc, char** argv) {
    if (argc == 2 && std::string_view(argv[1]) == "--validate") return validate_three();
    std::vector<Bits> cols(15);
    for (unsigned u = 0; u < 8; ++u) {
        for (unsigned v = 0; v < 8; ++v) {
            const auto point = Bits{1} << (8 * u + v);
            if (u) cols[u - 1] |= point;
            cols[7 + v] |= point;
        }
    }
    const auto initial = canonical(target, ~target, std::move(cols));
    const auto end = Clock::now() + std::chrono::seconds(95);
    Elimination solver(end);
    for (int budget = 14; budget <= 20; ++budget) {
        const auto result = solver.prove(initial, budget, 15);
        std::cout << budget << ' ' << (result == Result::excluded ? "conditional-exclusion" :
                                      result == Result::deadline ? "timeout" : "open")
                  << " nodes=" << solver.visited() << std::endl;
        if (result != Result::excluded) break;
    }
}
