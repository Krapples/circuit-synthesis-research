#pragma once

#include "residual_directed.hpp"

#include <array>
#include <span>

namespace residual_phase_screen {

using residual_directed::Leaf;
using residual_directed::U;

struct Wires {
    std::vector<U> columns;
    unsigned repeated = 0;
};

inline Wires collect(std::span<const Leaf> leaves) {
    // Wire IDs determine multiplicity even when distinct wires have equal columns.
    std::array<Leaf, 12> ordered;
    if (leaves.size() > ordered.size()) throw std::invalid_argument("phase occurrence limit");
    std::copy(leaves.begin(), leaves.end(), ordered.begin());
    const auto end = ordered.begin() + leaves.size();
    std::sort(ordered.begin(), end, [](const Leaf& a, const Leaf& b) {
        if (a.column != b.column) return a.column < b.column;
        return a.wire < b.wire;
    });
    Wires result;
    for (auto it = ordered.begin(); it != end;) {
        const auto next = std::find_if(it + 1, end, [it](const Leaf& leaf) { return leaf.wire != it->wire; });
        if (next - it > 1) result.repeated |= 1u << result.columns.size();
        result.columns.push_back(it->column);
        it = next;
    }
    return result;
}

// Assignments numbered 0..63 whose coordinates in fixed equal value.
inline U pattern_mask(unsigned fixed, unsigned value) {
    constexpr std::array<U, 6> ones{
        0xaaaaaaaaaaaaaaaaULL, 0xccccccccccccccccULL, 0xf0f0f0f0f0f0f0f0ULL,
        0xff00ff00ff00ff00ULL, 0xffff0000ffff0000ULL, 0xffffffff00000000ULL,
    };
    U rows = ~U{0};
    for (; fixed; fixed &= fixed - 1) {
        const unsigned i = std::countr_zero(fixed);
        rows &= (value & (1u << i)) ? ones[i] : ~ones[i];
    }
    return rows;
}

// Only tests whether some phase admits a monotone completion in each repeated-wire
// fiber. An exact signed tree must still be checked. Poll can throw on a limit.
template<class Poll>
bool feasible(const Wires& wires, U positive, U negative, Poll&& poll) {
    unsigned pending = 1;
    const auto step = [&] {
        if (++pending == 64) {
            poll(pending);
            pending = 0;
        }
    };
    const auto finish = [&](bool result) {
        poll(pending);
        return result;
    };
    if (positive & negative) return finish(false);
    if (!positive || !negative) return finish(true);

    std::array<unsigned, 64> singleton{}, repeated{};
    unsigned singles = 0;
    for (unsigned i = 0; i < wires.columns.size(); ++i) {
        const bool repeats = wires.repeated & (1u << i);
        const auto bit = 1u << (repeats ? i : singles++);
        auto& patterns = repeats ? repeated : singleton;
        for (U rows = wires.columns[i] & (positive | negative); rows; rows &= rows - 1) {
            step();
            patterns[std::countr_zero(rows)] |= bit;
        }
    }

    // At most 32*32 opposing pairs on 64 disjoint cared rows.
    struct Forbidden { unsigned differing, value; };
    std::array<Forbidden, 1024> forbidden;
    unsigned clauses = 0, fixed = 0, phase = 0;
    for (U p = positive; p; p &= p - 1) {
        const unsigned a = std::countr_zero(p);
        for (U n = negative; n; n &= n - 1) {
            step();
            const unsigned b = std::countr_zero(n);
            if (repeated[a] != repeated[b]) continue;
            const unsigned differing = singleton[a] ^ singleton[b];
            const unsigned value = singleton[a] & differing;
            if (!differing) return finish(false);
            if (std::has_single_bit(differing)) {
                if ((fixed & differing) && (phase & differing) == value) return finish(false);
                fixed |= differing;
                phase |= differing ^ value;
            } else {
                forbidden[clauses++] = {differing, value};
            }
        }
    }

    // One word packs the lowest six phase bits. The high bits select a word.
    const unsigned words = 1u << (singles > 6 ? singles - 6 : 0);
    const U word_mask = words == 64 ? ~U{0} : (U{1} << words) - 1;
    U live = word_mask & pattern_mask(fixed >> 6, phase >> 6);
    const U low_mask = singles >= 6 ? ~U{0} : (U{1} << (1u << singles)) - 1;
    const U initial = low_mask & pattern_mask(fixed & 63, phase);
    std::array<U, 64> allowed;
    allowed.fill(initial);
    for (unsigned i = 0; i < clauses && live; ++i) {
        step();
        const auto [differing, value] = forbidden[i];
        if ((value ^ phase) & differing & fixed) continue;
        const U keep = ~pattern_mask(differing & 63, value);
        for (U matches = live & pattern_mask(differing >> 6, value >> 6); matches; matches &= matches - 1) {
            step();
            const unsigned word = std::countr_zero(matches);
            allowed[word] &= keep;
            if (!allowed[word]) live &= ~(U{1} << word);
        }
    }
    return finish(live != 0);
}

}  // namespace residual_phase_screen
