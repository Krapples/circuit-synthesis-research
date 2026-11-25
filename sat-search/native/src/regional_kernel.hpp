// Native port of theory/regional_block_completion.local_blocks with the production flags
// (port_first=True, witness_cover=True, row_filter/endpoint_branches/dominance_branches=True, optional
// row_quotient, optional module_filter, PackedTables, no block_order, no root_relaxation).
//
// Same algorithm and search order as the Python reference: identical partition enumeration order,
// identical bounded LRU memoization of `complete` (8192) and of the row quotient (4096), identical
// witness-cover branching (visited cap 4096).  The Python prelude (read-once recognition of the targets,
// learned phases and forced &/| adjacency) is computed by the caller and passed in.
//
// Python-independent: deadlines and interrupts go through Query::poll, called every POLL_INTERVAL work units.
#pragma once
#include <array>
#include <cstdint>
#include <functional>
#include <stdexcept>
#include <string>
#include <vector>

namespace regional {

constexpr int MAX_M = 8;          // private variables: truth tables of up to 256 bits
constexpr int MAX_PROVIDERS = 32; // distinct providers (compact indices 0..P-1); phase-first virtual ports included
constexpr int MAX_ROWS = 64;      // observed provider patterns (row bitsets are uint64)
constexpr int64_t POLL_INTERVAL = 1024;

struct Query {
    int m = 0;
    std::vector<int> provider_ids;      // original provider ids, sorted ascending (leaf id = m + provider_ids[p])
    std::vector<int> counts;            // occurrences per provider (same order)
    std::vector<uint32_t> pats;         // per row: compact provider pattern (bit p = provider p)
    std::vector<uint8_t> target_any;    // per row: 1 if ANY
    std::vector<uint64_t> target_words; // per row: 4 words (little endian), zero if ANY
    bool is_signed = false;
    bool module_filter = true;
    bool row_quotient = true;
    std::vector<int8_t> phase;          // per private variable: -1 unknown, else 0/1 (learned from targets)
    std::vector<uint32_t> forced_and;   // per private variable: forced['&'][i]
    std::vector<uint32_t> forced_or;    // per private variable: forced['|'][i]
    int64_t work_limit = -1;            // as local_blocks(work_limit=...); -1 = none
    std::function<bool()> poll;         // return true to abort (deadline / interrupt)
};

struct Node {
    char op;      // 'x', '&', '|'
    int a, b;     // leaf: a = leaf id, b = negated; internal: child node ids
    uint64_t lo, hi;
};

struct Stats {
    int64_t rec = 0, row_reject = 0, module_reject = 0, port_allocations = 0, port_allocation_reject = 0,
            partition_checks = 0, endpoint_split_reject = 0, dominance_split_reject = 0, obligation_partitions = 0,
            cover_nodes = 0, quotient_conflicts = 0, quotient_dropped = 0, work = 0, complete_cache_hits = 0,
            peak_cache_entries = 0;
    // stage B (prelude + phase-first + adaptive routing)
    int64_t local = 0, phase_first_calls = 0, phase_clauses = 0, phase_nodes = 0, phase_classes = 0,
            monotone_calls = 0, phase_reject = 0;
    void add(const Stats& o);
};

enum class Status { UNSAT = 0, SAT = 1, ABORTED = 2, WORK_LIMIT = 3 };

struct Result {
    Status status = Status::UNSAT;
    std::vector<Node> nodes;
    int root = -1;
    Stats stats;
};

// Stage A: one local_blocks query with the prelude supplied by the caller (phase / forced in Query).
Result solve(const Query& q);

// Read-once prelude of local_blocks (one_sharing_core.tree + learn) for the distinct exact targets.
// Returns false when local_blocks returns None before searching.
bool prelude(int m, const std::vector<uint8_t>& target_any, const std::vector<uint64_t>& target_words, bool is_signed,
             std::vector<int8_t>& phase, std::vector<uint32_t>& forced_and, std::vector<uint32_t>& forced_or);

// Stage B: regional_phase_first.adaptive_completion with local_blocks (production flags) natively, i.e. the full
// completion-solver call behind ObligationCache.  Query.phase/forced are ignored (computed by prelude).
// adaptive=false: plain local_blocks (prelude + kernel), no phase-first routing.
// Result.stats.phase_first_calls tells whether the phase-first path ran (the caller then re-checks the witness, as
// the reference does).
Result solve_completion(const Query& q, bool adaptive);

}  // namespace regional
