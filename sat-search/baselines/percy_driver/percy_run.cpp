// Command-line driver for Percy exact synthesis restricted to AIGs (spec.set_primitive(AIG), SSV encoder).
// Reproduces percy::std_synthesize / std_cegar_synthesize one budget at a time so that every budget's SAT/UNSAT
// time is reported, and prints the witness chain for independent verification by the harness.
//
// usage: percy_run --n N --tt HEX [--dc HEX] [--solver bsat|satoko|bmcg] [--method std|cegar]
//                  [--start K] [--budget K] [--max K] [--conflicts C] [--nosym]
//   --tt   truth table, hex, most significant nibble first (kitty::create_from_hex_string convention)
//   --dc   don't-care mask, same format (1 = don't care)
//   --budget K : decide only "exactly K steps" (Percy's fixed-step semantics, all steps used)
//   --first-layer edges|all : cared-pair distinction constraints, up to five inputs
//   --first-layer-budget : optional trimmed boundary cardinality constraint
//   --tight-residual : optional bounded exact regional exclusions during CEGAR
//   --tight-residual-set-cuts : use feature presence for exclusions with distinct first-layer types
//   --slack-one-residual : check slack-one boundaries and learn extension clauses (requires --first-layer)
//   --trace-slack-one : emit the boundaries and their verdicts as JSON events
//   --residual-filter off|root|parity|direct : choose the residual completion ablation
//   --residual-backend columns|directed|dominance : choose the exact tree completion backend
//   --slack-two-residual memo|unate|phase|phase-cache : opt-in exact slack-two completion and cuts
//   --slack-two-set-cuts : use position-independent pure cuts for distinct first-layer types
//   --trace-slack-two : record slack-two candidates, including in the slack-one control
//   --restriction-cuts trace|cut|all|rows : restriction (gate-elimination) certificates on every CEGAR model;
//                    trace only measures, cut learns the cheapest core, all learns one per violating restriction
//                    rows learns the cheapest core and still simulates the model and adds its CEGAR row
//   --restriction-burst M : with cut/all, after M consecutive certificate cuts also simulate the next model
//                    and add its CEGAR row (0, the default, never does)
//   --capture-models PATH : write every CEGAR candidate model (chain) as JSON lines to a new file
//   --restriction-counters zero|const|anchor : eager constant-only restriction counters in the CNF. For each
//                    constant restriction pi (x_i := 0 for zero; both constants for const; per input the constant
//                    with the larger restricted cost for anchor) the gates with a provably constant operand
//                    are counted and capped at K - L(f o pi); a negative cap is UNSAT without solving
//   --restriction-live all|N : with --restriction-counters, replace the deletion cap of all (or the N strongest)
//                    counters by the restricted-output cone cap: gates reached from the output under pi with no
//                    provably constant operand are at least L(f o pi)
//   --restriction-essential : with --restriction-counters, every input essential in all completions of f o pi
//                    must be reached from the output through gates that are not provably constant
//   --restriction-cone-slice S : guard the cone caps and essential units by a literal a (live counters keep their
//                    deletion cap unguarded) and alternate every SAT call between slices assuming a and assuming !a,
//                    S conflicts each, doubling after each pair; both phases share learned clauses
//   --hybrid-witness W : separate witness discovery from lower-bound proofs. Pass 1 runs the budgets upward with
//                    the cone constraints off (the plain counters), each budget capped at W conflicts; a capped
//                    budget is skipped until a verified witness gives an upper bound U. Pass 2 then proves the
//                    skipped budgets below U in increasing order with the cone constraints on (a new encoding
//                    per budget). Without a witness up to --max, pass 2 runs the skipped budgets cone-free
//                    and uncapped (the unrestricted fallback).
//   --upper-witness "a,b;...|out" : an external chain (literal 2*w+p; wire 0 = constant 0, 1..n inputs, n+1+j
//                    gate j = AND of its literals) simulated against the target; its size U is a verified upper
//                    bound, so only the budgets below U are run, each with the full (proof) configuration and
//                    no witness pass. All UNSAT: U is the minimum and the external chain is reported. A SAT
//                    budget gives a better solver witness; a timeout leaves the interval [k, U-1] open.
//   --mixed-rank-cuts F : opt-in, complete tables only. For up to 8 input cuts (X, Q) whose anchored GF(2) mixed
//                    rank R has floor(R) = bit_width(R + 1) - 1 >= F, at least floor(R) steps of the output cone read
//                    both sides (scalar 2^(t+1) - 2 mixed-rank ceiling; native/src/mixed_rank.hpp)
//   --complement-inputs auto : synthesize f with every input complemented whose x_i := 1 cofactor costs more than
//                    its x_i := 0 cofactor (puts the stronger bound at zero); the chain is mapped back
//   otherwise  : increasing K from --start (default 1) until SAT or --max
// output: one JSON object per line: {"k":K,"status":"SAT|UNSAT|TIMEOUT","seconds":s} per budget, then a final line
//   {"final":..., "steps":K, "seconds":total, "chain":[[op,f0,f1],...], "out":[var,inv], "aig":bool, "verified":bool}
#include <algorithm>
#include <array>
#include <atomic>
#include <bit>
#include <chrono>
#include <condition_variable>
#include <cstdio>
#include <cstring>
#include <memory>
#include <mutex>
#include <new>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <thread>
#include <vector>
#include "first_layer.hpp"
#include "tight_residual.hpp"
#include "slack_two_boundary.hpp"
#include "slack_three_boundary.hpp"
#include "reified_counter.hpp"
#include "restriction_certificate.hpp"
#include "conditional_cost3.hpp"
#include "mixed_rank.hpp"
// Optional extra constraints need the SSV encoder's variable layout (svar_map, nr_svar_map, get_*_var), which Percy
// keeps private; open it for this driver only.
#define private public
#include <percy/percy.hpp>
#undef private

using namespace percy;
using clk = std::chrono::steady_clock;

// Why an inner residual query returned unknown: 0 deadline, 1 work allowance, 2 capacity (the
// boundary shape is outside the recognizer's range, so no work was done). Classified after the
// call: the Engine throws before a tick would exceed the allowance, and nested solvers receive the
// remaining allowance, so a work exit can report less than the full allowance. A query that ran
// out of work just as the deadline passed counts as a deadline.
static int unknown_cause(clk::time_point deadline, uint64_t work) {
    if (clk::now() >= deadline) return 0;
    return work ? 1 : 2;
}

static double since(clk::time_point t0) {
    return std::chrono::duration<double>(clk::now() - t0).count();
}

// ---------------------------------------------------------------- optional minimum-preserving constraints
// Both are valid only inside the increasing search from a proved lower bound (their UNSAT means "no minimum circuit
// with exactly k steps"), never for exact-size or pinned-prefix claims.
//   noreapply_full : no step reads (g, x) with x a fanin of step g. Percy's own create_noreapply_clauses rule for
//                    fanin 2, which Percy disables whenever a primitive set (AIG) is used.
//   reader caps    : theory/primary_reader_caps.py. For input i with cofactor bounds L0, L1 (free-NOT binary lower
//                    bounds of f|x_i=0, f|x_i=1; constants cost 0): at most k - max(L0, L1) readers; at most
//                    k - L_a - 1 readers if some reader absorbs at x_i = a and f|x_i=a is nonconstant. Requires
//                    noreapply_full and all steps used (alonce, Percy's default).
struct Extra {
    bool noreapply_full = false;
    std::vector<std::array<int, 4>> cof;   // per input: L0, L1, nonconst0, nonconst1 (empty = no caps)
    synthesis::PairScope pairs = synthesis::PairScope::none;
    bool first_layer_budget = false;
    bool tight_residual = false;
    bool residual_set_cuts = false;
    bool slack_one = false, trace_slack_one = false;
    int slack_two_mode = -1;
    bool slack_two_set_cuts = false;
    bool trace_slack_two = false;
    int slack_three_mode = -1;          // opt-in slack-three boundary cuts (Engine modes 2..5)
    bool slack_three_set_cuts = false;
    bool slack_three_symmetric = false; // occurrence-symmetric tree solver inside the Engine
    bool trace_slack_three = false;
    int slack_two_ms = 25;              // slack-two boundary query: deadline and Engine work allowance
    unsigned slack_two_work = 100000;
    int slack_three_ms = 25;
    unsigned slack_three_work = 2000000;
    // Last-provider decoder phase screen inside the slack-two and slack-three Engines (0 off,
    // 1 forced-equality phases + candidate columns, 2 also per-phase parity systems).
    unsigned decoder_phase = 0;
    // Lazy weighted slack-three cuts (slack_three_boundary.hpp). Non-full policies replace the
    // boundary's one-way counter by a reified one and add its threshold literal to the clause.
    synthesis::SlackThreePolicy slack_three_policy = synthesis::SlackThreePolicy::full;
    synthesis::ResidualFilterMode residual_filter = synthesis::ResidualFilterMode::off;
    synthesis::ResidualBackend residual_backend = synthesis::ResidualBackend::columns;
    // Restriction certificates (restriction_certificate.hpp): 0 off, 1 trace, 2 cheapest core, 3 all cores.
    int restriction_cuts = 0;
    unsigned restriction_burst = 0;  // cut/all: after this many consecutive cuts the next model also gets its row (0 = never)
    std::string capture_models;
    // Eager restriction counters: 0 off, 1 zero, 2 const, 3 anchor; the restrictions they encode.
    int restriction_counters = 0;
    std::vector<restriction_certificate::Restriction> counters;
    // Per counter: cone cap instead of the deletion cap (--restriction-live), essential inputs to reach.
    int restriction_live = 0;  // 0 off, N > 0: the N counters with the largest lower bounds, -1 all
    bool restriction_essential = false;
    std::vector<bool> counter_live;
    std::vector<std::vector<int>> counter_essential;
    int cone_slice = 0;  // > 0: guard the cone constraints and alternate guarded / unguarded solve slices
    int hybrid_witness = 0;  // > 0: per-budget conflict cap of the cone-free witness pass (see --hybrid-witness)
    // Conditional singleton counters (--restriction-conditional): per counter, the restricted three-input target
    // f o pi (bit s = value on the s-th free row, free inputs in increasing order), or -1 when not applicable.
    bool restriction_conditional = false;
    std::vector<int> counter_f3;
    bool complement_inputs = false;
    int mixed_rank_min = 0;                      // --mixed-rank-cuts F (0 = off)
    std::vector<mixed_rank::Cut> mixed_cuts;     // selected cuts for the (complete) synthesized table
};

// Per-budget restriction counter encoding size (set by encode_counters).
struct CounterStats { int restrictions = 0, live = 0, essential = 0, vars = 0, clauses = 0, negative_cap = 0;
                      int conditional = 0, conditional_clauses = 0; double seconds = 0; };
static CounterStats g_counter;
// Per-budget mixed-rank cut encoding size (set by encode_mixed_rank).
struct MixedStats { int cuts = 0, vars = 0, clauses = 0; double seconds = 0; };
static MixedStats g_mixed;
// Guard literal a of the cone constraints when --restriction-cone-slice is on (else -1), and per-budget slice
// statistics: slices run, and the phase (cone on / off) that decided each SAT or UNSAT answer.
static int g_cone_guard = -1;
struct SliceStats { int slices = 0, on_sat = 0, on_unsat = 0, off_sat = 0, off_unsat = 0; };
static SliceStats g_slice;

// Per-budget restriction certificate counters.
struct RestrictionStats {
    unsigned models = 0, rejects = 0, cuts = 0, literals = 0, pair_only = 0, typed = 0, repeats = 0;
    unsigned subsumed = 0, subsumes = 0, empty = 0, trace_rows = 0, trace_residual = 0;
    std::array<unsigned, 17> width{};  // clause literals, 16 = 16 or more
    double seconds = 0;
    std::set<std::vector<int>> seen;
    std::vector<std::vector<int>> stored;  // first 4096 distinct clauses, for subsumption counts
};

struct ClauseSink {
    solver_wrapper& s;
    int next;
    std::vector<std::vector<int>> clauses;
    int var() { return next++; }
    void add(std::vector<int> c) { clauses.push_back(std::move(c)); }
    // Sinz sequential counter: at most K of lits true; every clause gets the optional guard literal prepended.
    void at_most(const std::vector<int>& x, int K, int guard = -1) {
        int n = (int)x.size();
        auto G = [&](std::vector<int> c) { if (guard >= 0) c.insert(c.begin(), guard); add(c); };
        if (K >= n) return;
        if (K < 0) { G({}); return; }
        if (K == 0) { for (int l : x) G({l ^ 1}); return; }
        std::vector<std::vector<int>> sv(n - 1, std::vector<int>(K));
        for (auto& row : sv) for (auto& v : row) v = pabc::Abc_Var2Lit(var(), 0);
        G({x[0] ^ 1, sv[0][0]});
        for (int j = 1; j < K; j++) G({sv[0][j] ^ 1});
        for (int i = 1; i < n - 1; i++) {
            G({x[i] ^ 1, sv[i][0]}); G({sv[i - 1][0] ^ 1, sv[i][0]});
            for (int j = 1; j < K; j++) { G({x[i] ^ 1, sv[i - 1][j - 1] ^ 1, sv[i][j]}); G({sv[i - 1][j] ^ 1, sv[i][j]}); }
            G({x[i] ^ 1, sv[i - 1][K - 1] ^ 1});
        }
        G({x[n - 1] ^ 1, sv[n - 2][K - 1] ^ 1});
    }
    // at_most(x, K), plus: literal g implies at most K - 1 of x. When the Sinz counter is built (1 <= K < n), the
    // conditional cap reads its threshold literals: sv[i-1][K-2] is forced true once K - 1 of x_0..x_{i-1} hold, so
    // !g | !x_i | !sv[i-1][K-2] forbids the K-th true literal. Returns the number of conditional clauses.
    int at_most_cond(const std::vector<int>& x, int K, int g) {
        const int n = (int)x.size();
        if (K < 0) { add({}); return 0; }
        if (K == 0) { at_most(x, 0); add({g ^ 1}); return 1; }
        if (K >= n) {
            if (K == n) { std::vector<int> c{g ^ 1}; for (int l : x) c.push_back(l ^ 1); add(std::move(c)); return 1; }
            return 0;
        }
        const int first = next;
        at_most(x, K);
        // sv rows are allocated row by row: sv[i][j] = first + i * K + j (all positive literals)
        const auto sv = [&](int i, int j) { return pabc::Abc_Var2Lit(first + i * K + j, 0); };
        const size_t main = clauses.size();
        for (int i = (K == 1 ? 0 : 1); i < n; ++i) {
            if (K == 1) add({g ^ 1, x[i] ^ 1});
            else add({g ^ 1, x[i] ^ 1, sv(i - 1, K - 2) ^ 1});
        }
        return int(clauses.size() - main);
    }
};

static void equivalent_or(ClauseSink& cs, int output, std::vector<int> inputs) {
    for (int input : inputs) cs.add({input ^ 1, output});
    inputs.push_back(output ^ 1);
    cs.add(std::move(inputs));
}

// Cache target-side clauses across budgets. These masks refer only to boundary features.
struct FirstLayer {
    static constexpr std::array<unsigned, 4> aigs{2, 4, 8, 14};
    std::vector<synthesis::FirstLayerGate> gates;
    std::vector<uint64_t> clauses;

    FirstLayer(const kitty::dynamic_truth_table& target, const kitty::dynamic_truth_table& dc, const Extra& ex) {
        if (ex.pairs == synthesis::PairScope::none) return;
        const int n = target.num_vars();
        for (int b = 1; b < n; ++b)
            for (int a = 0; a < b; ++a)
                for (unsigned op : aigs) gates.push_back({a, b, op});
        std::vector<int> zeros, ones;
        for (int row = 0; row < (1 << n); ++row)
            if (!kitty::get_bit(dc, row))
                (kitty::get_bit(target, row) ? ones : zeros).push_back(row);
        clauses = synthesis::distinction_masks(gates, zeros, ones, ex.pairs);
    }

    std::vector<int> encode(ClauseSink& cs, ssv_encoder& enc, const spec& sp, const std::vector<int>& start,
                            bool budget, bool slack_two, std::vector<int>& typed_steps,
                            std::vector<int>* thresholds = nullptr) const {
        const int n = sp.get_nr_in(), k = sp.nr_steps;
        const auto fresh = [&] { return pabc::Abc_Var2Lit(cs.var(), 0); };
        std::vector<std::vector<int>> typed(gates.size()), mixed(n);
        if (slack_two) typed_steps.assign(k * gates.size(), -1);
        std::vector<int> boundary;
        for (int step = 0; step < k; ++step) {
            std::vector<int> primary_pairs;
            std::array<int, 4> ops{};
            if (!gates.empty()) {
                for (size_t op = 0; op < aigs.size(); ++op) {
                    ops[op] = fresh();
                    std::vector<int> match{ops[op]};
                    for (int bit = 1; bit <= 3; ++bit) {
                        const int lit = pabc::Abc_Var2Lit(enc.get_op_var(sp, step, bit), !(aigs[op] >> bit & 1));
                        cs.add({ops[op] ^ 1, lit});
                        match.push_back(lit ^ 1);
                    }
                    cs.add(std::move(match));
                }
            }
            for (int s = start[step]; s < start[step + 1]; ++s) {
                const int a = enc.svar_map[s][0], b = enc.svar_map[s][1];
                const int selected = pabc::Abc_Var2Lit(enc.get_sel_var(s), 0);
                if (b < n) {
                    if (budget) primary_pairs.push_back(selected);
                    const int pair = b * (b - 1) / 2 + a;
                    for (size_t op = 0; !gates.empty() && op < aigs.size(); ++op) {
                        const int occurrence = fresh();
                        cs.add({occurrence ^ 1, selected});
                        cs.add({occurrence ^ 1, ops[op]});
                        cs.add({occurrence, selected ^ 1, ops[op] ^ 1});
                        const auto type = pair * aigs.size() + op;
                        typed[type].push_back(occurrence);
                        if (slack_two) typed_steps[step * gates.size() + type] = occurrence;
                    }
                } else if (a < n) {
                    mixed[a].push_back(selected);
                }
            }
            if (budget) {
                const int is_first_layer = fresh();
                equivalent_or(cs, is_first_layer, std::move(primary_pairs));
                boundary.push_back(is_first_layer);
                boundary.push_back(is_first_layer);  // weight two, including repeated typed gates
            }
        }
        std::vector<int> features;
        for (auto& occurrences : typed) {
            features.push_back(fresh());
            equivalent_or(cs, features.back(), std::move(occurrences));
        }
        for (auto& readers : mixed) {
            features.push_back(fresh());
            equivalent_or(cs, features.back(), std::move(readers));
            if (budget) boundary.push_back(features.back());
        }
        if (budget && thresholds)
            *thresholds = synthesis::reified_at_most(boundary, k + 1, fresh,
                                                     [&](std::vector<int> c) { cs.add(std::move(c)); });
        else if (budget)
            cs.at_most(boundary, k + 1);
        for (uint64_t mask : clauses) {
            std::vector<int> clause;
            for (; mask; mask &= mask - 1) clause.push_back(features[std::countr_zero(mask)]);
            cs.add(std::move(clause));
        }
        return features;
    }
};

// Eager constant-only restriction counters. For a constant restriction pi, a gate with a selected operand that is
// provably constant under pi is deletable (it becomes a constant or a possibly complemented copy of its other
// operand), and the deletions are simultaneous, so a K-step chain of f leaves a K - D step chain of f o pi:
// D <= K - L(f o pi). Flags are one-way implications from the shared operand-selection literals, so on a
// single-selection model the least assignment is the exact propagation; models with several selected pairs per
// step only see over-approximated flags (they are excluded more often, never admitted wrongly). Normalized AIG
// gate g = AND(a ^ na, b ^ nb) ^ (na & nb) with na = op bit 2 and nb = op bit 1 (ops 2, 4, 8, 14). For x_i := 0
// every provably constant wire is 0 (each wire is 0 on row zero), so one flag per wire suffices:
// D = A | B and Z = (A & !na) | (B & !nb) | (A & B). x_i := 1 uses two flags (provably 0, provably 1).
//
// Restricted-output cone (--restriction-live) and essential-input reachability (--restriction-essential). Let K_w
// say wire w is provably constant under pi and D_g that gate g has a provably constant operand. Walk back from the
// output through the operands of visited gates that are not provably constant: reach_w. A visited gate with no
// constant operand stays a binary gate, every other gate is bypassed (alias), folded (constant) or unvisited, so f o pi
// has a chain of sum(reach_g & !D_g) gates: at most K - L(f o pi) gates have kept_g false. An input on which every
// completion of f o pi depends must be reached. Percy selects exactly one fanin pair per step (create_op_clauses
// plus create_cardinality_constraints), so every model is a chain; the one-way flags below have the exact
// propagation as their least (for K, D) or greatest (for reach, active, kept) assignment, and use[t][pos][w] is
// tied both ways to the selections when reachability is encoded.
static bool encode_counters(ClauseSink& cs, ssv_encoder& enc, const spec& sp, const std::vector<int>& start,
                            const Extra& ex) {
    const auto t0 = clk::now();
    g_counter = {};
    g_cone_guard = -1;
    const int vars0 = cs.next;
    const size_t clauses0 = cs.clauses.size();
    const int n = sp.get_nr_in(), k = sp.nr_steps;
    for (const auto& r : ex.counters)
        if (int(r.lower) > k) { g_counter.negative_cap = 1; return false; }  // negative cap: UNSAT, no clause
    const auto fresh = [&] { return pabc::Abc_Var2Lit(cs.var(), 0); };
    bool any_reach = false;
    for (size_t r = 0; r < ex.counters.size(); ++r)
        any_reach |= ex.counter_live[r] || !ex.counter_essential[r].empty();
    if (any_reach && ex.cone_slice > 0) g_cone_guard = fresh();
    const int ga = g_cone_guard >= 0 ? g_cone_guard ^ 1 : -1;  // !a, prepended to every guarded clause
    const auto guarded = [&](std::vector<int> c) { if (ga >= 0) c.insert(c.begin(), ga); cs.add(std::move(c)); };
    // use[t][pos][w] is implied by every pair of step t whose operand pos is wire w (shared by all restrictions).
    std::vector<std::array<std::vector<int>, 2>> use(k);
    for (int t = 0; t < k; ++t) {
        std::array<std::vector<std::vector<int>>, 2> back;
        for (int pos = 0; pos < 2; ++pos) { use[t][pos].assign(n + t, -1); back[pos].resize(n + t); }
        for (int s = start[t]; s < start[t + 1]; ++s) {
            const int sel = pabc::Abc_Var2Lit(enc.get_sel_var(s), 0);
            for (int pos = 0; pos < 2; ++pos) {
                const int w = enc.svar_map[s][pos];
                int& u = use[t][pos][w];
                if (u < 0) u = fresh();
                cs.add({sel ^ 1, u});
                back[pos][w].push_back(sel);
            }
        }
        if (any_reach)  // use -> some selected pair with that operand (reachability wants use true)
            for (int pos = 0; pos < 2; ++pos)
                for (int w = 0; w < n + t; ++w) {
                    if (use[t][pos][w] < 0) continue;
                    std::vector<int> c{use[t][pos][w] ^ 1};
                    c.insert(c.end(), back[pos][w].begin(), back[pos][w].end());
                    cs.add(std::move(c));
                }
    }
    const auto opv = [&](int t, int bit) { return pabc::Abc_Var2Lit(enc.get_op_var(sp, t, bit), 0); };
    std::vector<int> inv(k, -1);
    constexpr int F = -1, T = -2;  // statically false / true flags
    for (size_t ri = 0; ri < ex.counters.size(); ++ri) {
        const auto& r = ex.counters[ri];
        const bool live = ex.counter_live[ri];
        const auto& essential = ex.counter_essential[ri];
        const int cap = k - int(r.lower);
        if (cap >= k && essential.empty()) continue;
        std::vector<std::array<int, 2>> z;  // per wire: provably 0, provably 1
        bool zero = true;
        for (int i = 0; i < n; ++i) {
            z.push_back({r.primary[i] == 0 ? T : F, r.primary[i] == 1 ? T : F});
            zero &= r.primary[i] != 1;
        }
        const auto operand = [&](int t, int pos, int c) {
            const int a = fresh();
            for (int w = 0; w < n + t; ++w) {
                const int u = use[t][pos][w];
                if (u < 0 || z[w][c] == F) continue;
                if (z[w][c] == T) cs.add({u ^ 1, a});
                else cs.add({u ^ 1, z[w][c] ^ 1, a});
            }
            return a;
        };
        std::vector<int> deleted;
        for (int t = 0; t < k; ++t) {
            const int na = opv(t, 2), nb = opv(t, 1), d = fresh();
            deleted.push_back(d);
            if (zero) {
                const int A = operand(t, 0, 0), B = operand(t, 1, 0), Z = fresh();
                cs.add({A ^ 1, d}); cs.add({B ^ 1, d});
                cs.add({A ^ 1, na, Z}); cs.add({B ^ 1, nb, Z}); cs.add({A ^ 1, B ^ 1, Z});
                z.push_back({Z, F});
                continue;
            }
            const int A0 = operand(t, 0, 0), A1 = operand(t, 0, 1), B0 = operand(t, 1, 0), B1 = operand(t, 1, 1);
            for (int f : {A0, A1, B0, B1}) cs.add({f ^ 1, d});
            // operands after the normalized negations: provably 0 (az, bz) or provably 1 (ao, bo)
            const int az = fresh(), ao = fresh(), bz = fresh(), bo = fresh();
            cs.add({A0 ^ 1, na, az}); cs.add({A1 ^ 1, na ^ 1, az});
            cs.add({A1 ^ 1, na, ao}); cs.add({A0 ^ 1, na ^ 1, ao});
            cs.add({B0 ^ 1, nb, bz}); cs.add({B1 ^ 1, nb ^ 1, bz});
            cs.add({B1 ^ 1, nb, bo}); cs.add({B0 ^ 1, nb ^ 1, bo});
            if (inv[t] < 0) {
                inv[t] = fresh();
                cs.add({inv[t] ^ 1, na}); cs.add({inv[t] ^ 1, nb}); cs.add({inv[t], na ^ 1, nb ^ 1});
            }
            const int Z0 = fresh(), Z1 = fresh(), I = inv[t];
            // the AND is provably 0 if an operand is, provably 1 if both are; I complements the output
            cs.add({az ^ 1, I, Z0}); cs.add({bz ^ 1, I, Z0}); cs.add({ao ^ 1, bo ^ 1, I ^ 1, Z0});
            cs.add({ao ^ 1, bo ^ 1, I, Z1}); cs.add({az ^ 1, I ^ 1, Z1}); cs.add({bz ^ 1, I ^ 1, Z1});
            z.push_back({Z0, Z1});
        }
        if (!essential.empty()) ++g_counter.essential;
        // Deletion cap, with the conditional singleton strengthening when enabled. A first-layer gate on two free
        // primaries has no constant operand, so it survives the bypass and the simplified K - D gate circuit
        // computes both f o pi and its one-gate function h: K - D >= M(f o pi, {h}). If h is incompatible
        // (M = L + 1), presence(h) -> D <= cap - 1. Presence is read from the step's selection and op literals.
        const auto deletion_cap = [&] {
            const int f3 = ri < ex.counter_f3.size() ? ex.counter_f3[ri] : -1;
            const unsigned incompatible = f3 < 0 ? 0u : conditional_cost3::kIncompatible3[std::min(f3, 255 ^ f3)];
            if (!incompatible) { cs.at_most(deleted, cap); return; }
            int fixed = 0;
            for (int i = 0; i < n; ++i) if (r.primary[i] < 2) fixed = i;
            const auto column = [&](int v) {  // free primary v as a three-input column
                const int t = v - (v > fixed);
                return t == 0 ? 0xAA : t == 1 ? 0xCC : 0xF0;
            };
            const int g = fresh();
            int added = 0;
            for (int t = 0; t < k; ++t)
                for (int s = start[t]; s < start[t + 1]; ++s) {
                    const int a = enc.svar_map[s][0], b = enc.svar_map[s][1];
                    if (a >= n || b >= n || a == fixed || b == fixed) continue;
                    const int ca = column(a), cb = column(b), sel = pabc::Abc_Var2Lit(enc.get_sel_var(s), 0);
                    std::vector<unsigned> bad;
                    for (unsigned op : FirstLayer::aigs) {
                        int h = 0;
                        for (int row = 0; row < 8; ++row) {
                            const int j = (ca >> row & 1) | (cb >> row & 1) << 1;
                            h |= (j && (op >> j & 1)) << row;
                        }
                        h = std::min(h, 255 ^ h);
                        int idx = -1;
                        for (int q = 0; q < 12; ++q) if (conditional_cost3::kOneGate3[q] == h) idx = q;
                        if (idx < 0) { fprintf(stderr, "internal: first-layer column %d is not a one-gate function\n", h); std::abort(); }
                        if (incompatible >> idx & 1) bad.push_back(op);
                    }
                    if (bad.size() == FirstLayer::aigs.size()) { cs.add({sel ^ 1, g}); ++added; continue; }
                    for (unsigned op : bad) {
                        std::vector<int> c{sel ^ 1};
                        for (int bit = 1; bit <= 3; ++bit)  // op var literal that is true when the bit differs
                            c.push_back(pabc::Abc_Var2Lit(enc.get_op_var(sp, t, bit), (op >> bit & 1) != 0));
                        c.push_back(g);
                        cs.add(std::move(c));
                        ++added;
                    }
                }
            if (!added) { cs.at_most(deleted, cap); return; }
            added += cs.at_most_cond(deleted, cap, g);
            ++g_counter.conditional;
            g_counter.conditional_clauses += added;
        };
        if (!live && essential.empty()) {
            deletion_cap();
            ++g_counter.restrictions;
            continue;
        }
        // Reachability over the restricted output cone (backwards from the output, the last step).
        const int N = n + k;
        std::vector<int> reach(N, F), active(N, F);
        for (int w = N - 1; w >= 0; --w) {
            if (w == N - 1) reach[w] = T;
            else {
                std::vector<int> paths;
                for (int t = std::max(0, w - n + 1); t < k; ++t) {
                    const int a = active[n + t], u0 = use[t][0][w], u1 = use[t][1][w];
                    if (a == F || (u0 < 0 && u1 < 0)) continue;
                    const int p = fresh();
                    if (a != T) cs.add({p ^ 1, a});
                    std::vector<int> c{p ^ 1};
                    if (u0 >= 0) c.push_back(u0);
                    if (u1 >= 0) c.push_back(u1);
                    cs.add(std::move(c));
                    paths.push_back(p);
                }
                if (!paths.empty()) {
                    reach[w] = fresh();
                    paths.insert(paths.begin(), reach[w] ^ 1);
                    cs.add(std::move(paths));
                }
            }
            // provably constant: K = Z0 | Z1 (one-way)
            int K = F;
            if (z[w][0] == T || z[w][1] == T) K = T;
            else if (z[w][0] != F || z[w][1] != F) {
                K = fresh();
                for (int c = 0; c < 2; ++c) if (z[w][c] != F) cs.add({z[w][c] ^ 1, K});
            }
            if (reach[w] == F || K == T) active[w] = F;
            else if (reach[w] == T && K == F) active[w] = T;
            else {
                active[w] = fresh();
                if (reach[w] != T) cs.add({active[w] ^ 1, reach[w]});
                if (K != F) cs.add({active[w] ^ 1, K ^ 1});
            }
        }
        for (int j : essential) {
            if (reach[j] == F) { g_counter.negative_cap = 1; return false; }  // cannot happen: every step reads inputs
            if (reach[j] != T) guarded({reach[j]});
        }
        if (!live) { deletion_cap(); ++g_counter.restrictions; continue; }
        std::vector<int> dropped;  // !kept_g, at most cap of them
        int lost = 0;              // gates that are never kept
        for (int t = 0; t < k; ++t) {
            if (reach[n + t] == F) { ++lost; continue; }
            const int kept = fresh();
            if (reach[n + t] != T) cs.add({kept ^ 1, reach[n + t]});
            cs.add({kept ^ 1, deleted[t] ^ 1});
            dropped.push_back(kept ^ 1);
        }
        if (cap - lost < 0) { g_counter.negative_cap = 1; return false; }
        cs.at_most(dropped, cap - lost, ga);
        // The unguarded slice phase keeps the deletion cap. With --restriction-conditional the forward (deletion)
        // counter is kept beside the cone cap too: its conditional clauses use forward presence, which is sound
        // for the forward count only (a first-layer gate need not be in the restricted cone).
        if (ga >= 0 || !ex.counter_f3.empty()) deletion_cap();
        ++g_counter.restrictions;
        ++g_counter.live;
    }
    g_counter.vars = cs.next - vars0;
    g_counter.clauses = int(cs.clauses.size() - clauses0);
    g_counter.seconds = since(t0);
    return true;
}

// Mixed-rank cuts (--mixed-rank-cuts). For each cut side X: pure[0][w] / pure[1][w] = wire w reads only X / only Q
// inputs (inputs fixed, steps defined from every selected operand pair), reach[w] = w lies in the output cone (the
// last step; least fixpoint over selected pairs), and a mixed step m_t -> !pure[0] & !pure[1] & reach. At least
// floor(R) mixed steps. Several true selection variables of one step only strengthen the definitions; a circuit
// keeps a model with one selected pair per step.
static bool encode_mixed_rank(ClauseSink& cs, ssv_encoder& enc, const spec& sp, const std::vector<int>& start,
                              const Extra& ex) {
    const auto t0 = clk::now();
    g_mixed = {};
    const int vars0 = cs.next;
    const size_t clauses0 = cs.clauses.size();
    const int n = sp.get_nr_in(), k = sp.nr_steps, N = n + k;
    const auto fresh = [&] { return pabc::Abc_Var2Lit(cs.var(), 0); };
    const auto sel = [&](int s) { return pabc::Abc_Var2Lit(enc.get_sel_var(s), 0); };
    std::vector<int> step_of;
    for (int t = 0; t < k; ++t) for (int s = start[t]; s < start[t + 1]; ++s) step_of.push_back(t);
    // Output cone: the last step is reached; reach[w] -> some selected pair of a reached step reads w.
    std::vector<int> reach(N, -1);
    for (int t = 0; t < k - 1; ++t) reach[n + t] = fresh();
    std::vector<std::vector<int>> support(N);
    for (int s = 0; s < start[k]; ++s) {
        const int t = step_of[size_t(s)];
        for (int pos = 0; pos < 2; ++pos) {
            const int w = enc.svar_map[s][pos];
            if (w < n) continue;  // inputs need no reach literal
            const int p = fresh();
            cs.add({p ^ 1, sel(s)});
            if (t < k - 1) {
                cs.add({p ^ 1, reach[n + t]});
                cs.add({sel(s) ^ 1, reach[n + t] ^ 1, reach[w]});
            } else {
                cs.add({sel(s) ^ 1, reach[w]});
            }
            support[size_t(w)].push_back(p);
        }
    }
    for (int t = 0; t < k - 1; ++t) {
        std::vector<int> c{reach[n + t] ^ 1};
        c.insert(c.end(), support[size_t(n + t)].begin(), support[size_t(n + t)].end());
        cs.add(std::move(c));
    }
    constexpr int T = -2, F = -1;
    for (const auto& cut : ex.mixed_cuts) {
        if (cut.floor > k) return false;
        std::array<std::vector<int>, 2> pure;  // [0] reads only X, [1] reads only Q
        for (int side = 0; side < 2; ++side) {
            auto& p = pure[side];
            p.assign(N, F);
            for (int i = 0; i < n; ++i) p[i] = ((cut.side >> i & 1) != 0) == (side == 0) ? T : F;
            for (int t = 0; t < k; ++t) p[n + t] = fresh();
            for (int s = 0; s < start[k]; ++s) {
                const int g = p[n + step_of[size_t(s)]], a = p[enc.svar_map[s][0]], b = p[enc.svar_map[s][1]];
                // sel & a & b -> g ; sel & !a -> !g ; sel & !b -> !g
                std::vector<int> up{sel(s) ^ 1, g};
                bool up_false = false;
                for (int o : {a, b}) {
                    if (o == F) { up_false = true; cs.add({sel(s) ^ 1, g ^ 1}); }
                    else if (o != T) { up.push_back(o ^ 1); cs.add({sel(s) ^ 1, o, g ^ 1}); }
                }
                if (!up_false) cs.add(std::move(up));
            }
        }
        std::vector<int> notmixed;
        for (int t = 0; t < k; ++t) {
            const int m = fresh();
            cs.add({m ^ 1, pure[0][n + t] ^ 1});
            cs.add({m ^ 1, pure[1][n + t] ^ 1});
            if (t < k - 1) cs.add({m ^ 1, reach[n + t]});
            notmixed.push_back(m ^ 1);
        }
        cs.at_most(notmixed, k - cut.floor);  // at least floor mixed steps
        ++g_mixed.cuts;
    }
    g_mixed.vars = cs.next - vars0;
    g_mixed.clauses = int(cs.clauses.size() - clauses0);
    g_mixed.seconds = since(t0);
    return true;
}

// Returns false if the extra constraints make budget k infeasible outright; adds clauses to the solver otherwise.
static bool add_extra(ssv_encoder& enc, const spec& sp, solver_wrapper& solver, const Extra& ex,
                      const FirstLayer& layer, int& extra_clauses, std::vector<int>& layer_features,
                      std::vector<int>& typed_steps, std::vector<int>& thresholds) {
    if (!ex.noreapply_full && ex.cof.empty() && ex.pairs == synthesis::PairScope::none && !ex.first_layer_budget &&
        ex.counters.empty() && ex.mixed_cuts.empty())
        return true;
    const int n = sp.get_nr_in(), k = sp.nr_steps;
    ClauseSink cs{solver, enc.total_nr_vars, {}};
    std::vector<int> start(k + 1, 0);
    for (int i = 0; i < k; i++) start[i + 1] = start[i] + enc.nr_svar_map[i];
    auto sel = [&](int svar) { return pabc::Abc_Var2Lit(enc.get_sel_var(svar), 0); };
    auto opv = [&](int step, int j) { return pabc::Abc_Var2Lit(enc.get_op_var(sp, step, j), 0); };
    if (ex.noreapply_full) {
        for (int g = 0; g < k - 1; g++)
            for (int a = start[g]; a < start[g + 1]; a++) {
                const auto& fg = enc.svar_map[a];
                for (int ip = g + 1; ip < k; ip++)
                    for (int b = start[ip]; b < start[ip + 1]; b++) {
                        const auto& fp = enc.svar_map[b];
                        bool has_g = fp[0] == n + g || fp[1] == n + g;
                        int other = fp[0] == n + g ? fp[1] : fp[0];
                        if (has_g && (other == fg[0] || other == fg[1])) cs.add({sel(a) ^ 1, sel(b) ^ 1});
                    }
            }
    }
    for (int i = 0; i < (int)ex.cof.size() && i < n; i++) {
        const auto& c = ex.cof[i];
        int d = k - std::max(c[0], c[1]);
        if (d < 0) return false;
        std::vector<int> read;
        std::vector<std::pair<int, int>> where;   // (svar, position of input i)
        for (int st = 0; st < k; st++)
            for (int a = start[st]; a < start[st + 1]; a++) {
                const auto& f = enc.svar_map[a];
                if (f[0] == i || f[1] == i) { read.push_back(sel(a)); where.push_back({a, f[0] == i ? 0 : 1}); }
            }
        cs.at_most(read, d);
        for (int val = 0; val < 2; val++) {
            int cap = c[2 + val] ? std::min(d, k - c[val] - 1) : d;
            if (cap >= d || cap >= (int)read.size()) continue;
            int flag = pabc::Abc_Var2Lit(cs.var(), 0);
            for (auto [a, pos] : where) {
                int st = 0;
                while (a >= start[st + 1]) st++;
                int s_ = sel(a) ^ 1;
                // op var j = output on assignment (fanin0 = j & 1, fanin1 = j >> 1); f(0,0) = 0 (normal).
                // absorbing at val for operand pos: the two outputs with operand pos = val are equal.
                int j0 = pos == 0 ? val : (val << 1), j1 = pos == 0 ? (val | 2) : (val << 1) | 1;
                if (j0 == 0) cs.add({s_, opv(st, j1), flag});                       // needs out(j1) = 0
                else { cs.add({s_, opv(st, j0) ^ 1, opv(st, j1) ^ 1, flag}); cs.add({s_, opv(st, j0), opv(st, j1), flag}); }
            }
            cs.at_most(read, cap, flag ^ 1);
        }
    }
    if (ex.pairs != synthesis::PairScope::none || ex.first_layer_budget)
        layer_features = layer.encode(cs, enc, sp, start, ex.first_layer_budget,
                                      ex.slack_two_mode >= 0 || ex.slack_three_mode >= 0, typed_steps,
                                      ex.slack_three_policy != synthesis::SlackThreePolicy::full ? &thresholds
                                                                                                : nullptr);
    if (!ex.counters.empty() && !encode_counters(cs, enc, sp, start, ex)) return false;
    if (!ex.mixed_cuts.empty() && !encode_mixed_rank(cs, enc, sp, start, ex)) return false;
    solver.set_nr_vars(cs.next);
    extra_clauses = (int)cs.clauses.size();
    for (auto& cl : cs.clauses) {
        if (cl.empty()) return false;
        std::vector<pabc::lit> lits(cl.begin(), cl.end());
        if (!solver.add_clause(lits.data(), lits.data() + lits.size())) return false;
    }
    return true;
}

struct TightResidual {
    uint64_t target = 0, care = 0;
    std::array<uint64_t, 5> primaries{};
    int queries = 0, cuts = 0, unknown = 0, set_cuts = 0;
    int slack_queries = 0, slack_feasible = 0, slack_unknown = 0, slack_pure = 0, slack_conditional = 0;
    int extension_feasible = 0, extension_unknown = 0, extension_excluded = 0, slack_position_cuts = 0;
    unsigned slack_joins = 0, root_splits = 0, root_rejected = 0;
    unsigned allocations = 0, parity_rejected = 0, direct_queries = 0;
    unsigned directed_states = 0;
    double slack_seconds = 0;
    int slack_two_seen = 0, slack_two_unknown = 0, slack_two_feasible = 0;
    std::array<unsigned, 3> two_unknown_cause{}, three_unknown_cause{};  // deadline, work, capacity
    int slack_two_pure = 0, slack_two_conditional = 0;
    unsigned two_set_cuts = 0;
    unsigned two_extension_feasible = 0, two_extension_unknown = 0, two_extension_excluded = 0;
    uint64_t two_work = 0, two_allocations = 0, two_memo_hits = 0, two_unate_rejects = 0, two_unate_merges = 0;
    uint64_t two_tree_calls = 0;
    residual_slack_two::PhaseStats two_phase;
    residual_slack_two::DecoderStats two_decoder, three_decoder;
    double three_exact_seconds = 0;
    double slack_two_seconds = 0;
    int slack_three_seen = 0, slack_three_unknown = 0, slack_three_feasible = 0;
    int slack_three_pure = 0, slack_three_conditional = 0;
    unsigned three_set_cuts = 0, three_subsumed = 0;
    unsigned three_extension_feasible = 0, three_extension_unknown = 0, three_extension_excluded = 0;
    unsigned three_tight_calls = 0, three_slack_one_calls = 0, three_slack_two_calls = 0;
    uint64_t three_work = 0, three_slack_two_work = 0, three_tree_calls = 0;
    residual_slack_two::PhaseStats three_phase;
    double slack_three_seconds = 0;
    // Lazy weighted cuts: thresholds[t] <=> boundary weight >= t; the memo outlives each budget.
    const std::vector<int>* thresholds = nullptr;
    synthesis::ResidualMemo* memo = nullptr;
    std::array<unsigned, 5> three_lift{};
    unsigned three_threshold_cuts = 0, three_covered = 0, three_exact_cached = 0;
    unsigned three_memo_hits = 0, three_memo_inserts = 0, three_seed_inserts = 0;
    uint64_t three_extension_total = 0, three_clause_literals = 0;
    unsigned three_cuts = 0, three_repeats = 0;
    std::set<std::vector<int>> three_visited;

    explicit TightResidual(const kitty::dynamic_truth_table& tt) {
        const int n = tt.num_vars();
        for (int row = 0; row < (1 << n); ++row) {
            const uint64_t bit = uint64_t{1} << row;
            care |= bit;
            if (kitty::get_bit(tt, row)) target |= bit;
            for (int i = 0; i < n; ++i)
                if (row >> i & 1) primaries[i] |= bit;
        }
    }

    // An empty result leaves CEGAR on its ordinary simulation path.
    std::vector<int> slack_two_cut(const spec& sp, std::span<const int> features,
                                  std::span<const int> typed_steps,
                                  const std::vector<std::pair<int, int>>& first,
                                  std::vector<uint64_t> columns, const std::vector<int>& observed_types,
                                  unsigned mixed, std::vector<int> cut, const Extra& ex) {
        const int n = sp.get_nr_in();
        ++slack_two_seen;
        if (ex.trace_slack_two) {
            printf("{\"event\":\"slack_two\",\"k\":%d,\"mixed\":%u,\"types\":[", sp.nr_steps, mixed);
            for (size_t i = 0; i < observed_types.size(); ++i)
                printf("%s%d", i ? "," : "", observed_types[i]);
            printf("]}\n");
        }
        if (ex.slack_two_mode < 0) return {};
        const auto start = clk::now();
        std::vector<uint64_t> gate_columns;
        for (int b = 1; b < n; ++b)
            for (int a = 0; a < b; ++a) {
                const uint64_t x = primaries[a], y = primaries[b];
                gate_columns.insert(gate_columns.end(), {x & ~y, ~x & y, x & y, x | y});
            }
        const bool seed = memo && ex.slack_three_policy == synthesis::SlackThreePolicy::adaptive;
        const std::vector<uint64_t> seed_columns = seed ? columns : std::vector<uint64_t>{};
        const auto two_deadline = start + std::chrono::milliseconds(ex.slack_two_ms);
        const auto result = synthesis::slack_two_boundary(
            std::move(columns), unsigned(first.size()), std::span(primaries).first(n), mixed,
            gate_columns, target, care, ex.slack_two_work, two_deadline, unsigned(ex.slack_two_mode),
            ex.decoder_phase);
        slack_two_seconds += since(start);
        two_work += result.exact.work;
        two_allocations += result.exact.allocations;
        two_memo_hits += result.exact.memo_hits;
        two_unate_rejects += result.exact.unate_rejects;
        two_unate_merges += result.exact.unate_merges;
        two_tree_calls += result.exact.tree_calls;
        two_phase.checks += result.exact.phase.checks;
        two_phase.rejects += result.exact.phase.rejects;
        two_phase.work += result.exact.phase.work;
        two_phase.cache_hits += result.exact.phase.cache_hits;
        two_phase.dominance_hits += result.exact.phase.dominance_hits;
        two_decoder.screens += result.exact.decoder.screens;
        two_decoder.rejects += result.exact.decoder.rejects;
        two_decoder.column_rejects += result.exact.decoder.column_rejects;
        two_decoder.skipped += result.exact.decoder.skipped;
        two_decoder.work += result.exact.decoder.work;
        using Status = residual_directed::Status;
        if (seed && result.exact.status != Status::unknown) {
            // The same leaves at exact slack two are a cost-one extension of a slack-three query.
            memo->bind(target, care);
            three_seed_inserts += memo->insert(seed_columns, unsigned(first.size()), 2,
                                               result.exact.status == Status::sat);
        }
        if (result.exact.status == Status::unknown) {
            ++slack_two_unknown;
            ++two_unknown_cause[unknown_cause(two_deadline, result.exact.work)];
        }
        if (result.exact.status == Status::sat) ++slack_two_feasible;
        if (result.exact.status != Status::unsat) return {};
        two_extension_feasible += result.feasible;
        two_extension_unknown += result.unknown;
        two_extension_excluded += result.excluded;
        if (result.mixed_extensions || result.gate_extensions) {
            ++slack_two_conditional;
        } else {
            ++slack_two_pure;
            uint64_t types = 0;
            for (const int type : observed_types) types |= uint64_t{1} << type;
            if (ex.slack_two_set_cuts && size_t(std::popcount(types)) == observed_types.size()) {
                // Each distinct type guarantees a separate old occurrence;
                // every possible addition, including duplicate types, was excluded.
                cut.clear();
                for (const int type : observed_types) cut.push_back(features[type] ^ 1);
                for (unsigned mask = mixed; mask; mask &= mask - 1)
                    cut.push_back(features[features.size() - n + std::countr_zero(mask)] ^ 1);
                ++two_set_cuts;
                return cut;
            }
        }
        for (unsigned mask = result.mixed_extensions; mask; mask &= mask - 1)
            cut.push_back(features[features.size() - n + std::countr_zero(mask)]);
        for (int step = 0; result.gate_extensions && step < sp.nr_steps; ++step) {
            if (std::any_of(first.begin(), first.end(), [step](const auto& entry) { return entry.first == step; }))
                continue;
            for (uint64_t mask = result.gate_extensions; mask; mask &= mask - 1) {
                const int literal = typed_steps[step * gate_columns.size() + std::countr_zero(mask)];
                if (literal >= 0) cut.push_back(literal);
            }
        }
        return cut;
    }

    // Same clause shape as slack_two_cut; the boundary decision uses lower-slack recognizers for
    // every extension of cost <= 3 (slack_three_boundary.hpp). An empty result changes nothing.
    std::vector<int> slack_three_cut(const spec& sp, std::span<const int> features,
                                    std::span<const int> typed_steps,
                                    const std::vector<std::pair<int, int>>& first,
                                    std::vector<uint64_t> columns, const std::vector<int>& observed_types,
                                    unsigned mixed, std::vector<int> cut, const Extra& ex) {
        const int n = sp.get_nr_in();
        ++slack_three_seen;
        {
            std::vector<int> visit(observed_types);
            std::sort(visit.begin(), visit.end());
            visit.push_back(-1 - int(mixed));
            three_repeats += !three_visited.insert(std::move(visit)).second;
        }
        if (ex.trace_slack_three) {
            printf("{\"event\":\"slack_three\",\"k\":%d,\"mixed\":%u,\"types\":[", sp.nr_steps, mixed);
            for (size_t i = 0; i < observed_types.size(); ++i)
                printf("%s%d", i ? "," : "", observed_types[i]);
            printf("]}\n");
        }
        if (ex.slack_three_mode < 0) return {};
        const auto start = clk::now();
        std::vector<uint64_t> gate_columns;
        for (int b = 1; b < n; ++b)
            for (int a = 0; a < b; ++a) {
                const uint64_t x = primaries[a], y = primaries[b];
                gate_columns.insert(gate_columns.end(), {x & ~y, ~x & y, x & y, x | y});
            }
        const auto three_deadline = start + std::chrono::milliseconds(ex.slack_three_ms);
        const auto result = synthesis::slack_three_boundary(
            std::move(columns), unsigned(first.size()), std::span(primaries).first(n), mixed,
            gate_columns, target, care, ex.slack_three_work, three_deadline, unsigned(ex.slack_three_mode),
            ex.slack_three_symmetric, ex.slack_three_policy, memo, ex.decoder_phase);
        slack_three_seconds += since(start);
        three_work += result.exact.work;
        three_tree_calls += result.exact.tree_calls;
        three_phase.checks += result.exact.phase.checks;
        three_phase.rejects += result.exact.phase.rejects;
        three_phase.work += result.exact.phase.work;
        three_phase.cache_hits += result.exact.phase.cache_hits;
        three_phase.dominance_hits += result.exact.phase.dominance_hits;
        three_decoder.screens += result.exact.decoder.screens;
        three_decoder.rejects += result.exact.decoder.rejects;
        three_decoder.column_rejects += result.exact.decoder.column_rejects;
        three_decoder.skipped += result.exact.decoder.skipped;
        three_decoder.work += result.exact.decoder.work;
        three_exact_seconds += result.exact_seconds;
        using Status = residual_directed::Status;
        if (result.exact.status == Status::unknown) {
            ++slack_three_unknown;
            ++three_unknown_cause[unknown_cause(three_deadline, result.exact.work)];
        }
        if (result.exact.status == Status::sat) ++slack_three_feasible;
        if (result.exact.status != Status::unsat) return {};
        ++three_cuts;
        three_extension_total += result.extension_total;
        three_covered += result.covered;
        ++three_lift[std::min(result.lift, 4u)];
        three_extension_feasible += result.feasible;
        three_extension_unknown += result.unknown;
        three_extension_excluded += result.excluded;
        three_subsumed += result.subsumed;
        three_tight_calls += result.tight_calls;
        three_slack_one_calls += result.slack_one_calls;
        three_slack_two_calls += result.slack_two_calls;
        three_slack_two_work += result.slack_two_work;
        three_memo_hits += result.memo_hits;
        three_memo_inserts += result.memo_inserts;
        three_exact_cached += result.exact_cached;
        if (ex.slack_three_policy != synthesis::SlackThreePolicy::full) {
            auto lazy = weighted_cut(sp, features, typed_steps, first, gate_columns.size(), observed_types,
                                     mixed, std::move(cut), result, ex);
            three_clause_literals += lazy.size();
            return lazy;
        }
        if (result.mixed_extensions || result.gate_extensions) {
            ++slack_three_conditional;
        } else {
            ++slack_three_pure;
            uint64_t types = 0;
            for (const int type : observed_types) types |= uint64_t{1} << type;
            if (ex.slack_three_set_cuts && size_t(std::popcount(types)) == observed_types.size()) {
                // Distinct types give separate old occurrences; every addition of cost <= 3,
                // duplicate types included, was excluded.
                cut.clear();
                for (const int type : observed_types) cut.push_back(features[type] ^ 1);
                for (unsigned mask = mixed; mask; mask &= mask - 1)
                    cut.push_back(features[features.size() - n + std::countr_zero(mask)] ^ 1);
                ++three_set_cuts;
                return cut;
            }
        }
        for (unsigned mask = result.mixed_extensions; mask; mask &= mask - 1)
            cut.push_back(features[features.size() - n + std::countr_zero(mask)]);
        for (int step = 0; result.gate_extensions && step < sp.nr_steps; ++step) {
            if (std::any_of(first.begin(), first.end(), [step](const auto& entry) { return entry.first == step; }))
                continue;
            for (uint64_t mask = result.gate_extensions; mask; mask &= mask - 1) {
                const int literal = typed_steps[step * gate_columns.size() + std::countr_zero(mask)];
                if (literal >= 0) cut.push_back(literal);
            }
        }
        return cut;
    }

    // Lazy weighted clause NOT A OR (W >= w + d) OR R for an excluded slack-three boundary
    // (w = k - 2). R lists the retained elements: a mixed primary's feature, and a retained gate
    // type at every step outside the antecedent's first-layer steps. With distinct observed types
    // and no retained gate among them, the set antecedent (types and mixed primaries present) is
    // used and a retained gate type is its feature literal; otherwise the positional antecedent
    // fixes the boundary's own steps, which covers repeated types.
    std::vector<int> weighted_cut(const spec& sp, std::span<const int> features, std::span<const int> typed_steps,
                                  const std::vector<std::pair<int, int>>& first, size_t gate_types,
                                  const std::vector<int>& observed_types, unsigned mixed, std::vector<int> cut,
                                  const synthesis::SlackThreeBoundary& result, const Extra& ex) {
        const int n = sp.get_nr_in(), k = sp.nr_steps;
        const unsigned d = result.lift;
        uint64_t types = 0;
        for (const int type : observed_types) types |= uint64_t{1} << type;
        const bool set = ex.slack_three_set_cuts && size_t(std::popcount(types)) == observed_types.size() &&
                         !(result.gate_extensions & types);
        if (result.mixed_extensions || result.gate_extensions) ++slack_three_conditional;
        else ++slack_three_pure;
        if (set) {
            cut.clear();
            for (const int type : observed_types) cut.push_back(features[type] ^ 1);
            for (unsigned mask = mixed; mask; mask &= mask - 1)
                cut.push_back(features[features.size() - n + std::countr_zero(mask)] ^ 1);
            ++three_set_cuts;
        }
        if (d <= 3) {
            const int w = 2 * int(first.size()) + std::popcount(mixed);
            if (!thresholds || w != k - 2 || size_t(w + d) >= thresholds->size()) {
                fprintf(stderr, "slack-three weighted cut without a reified threshold\n");
                std::abort();
            }
            cut.push_back((*thresholds)[w + d]);
            ++three_threshold_cuts;
        }
        for (unsigned mask = result.mixed_extensions; mask; mask &= mask - 1)
            cut.push_back(features[features.size() - n + std::countr_zero(mask)]);
        if (set) {
            for (uint64_t mask = result.gate_extensions; mask; mask &= mask - 1)
                cut.push_back(features[std::countr_zero(mask)]);
            return cut;
        }
        for (int step = 0; result.gate_extensions && step < k; ++step) {
            if (std::any_of(first.begin(), first.end(), [step](const auto& entry) { return entry.first == step; }))
                continue;
            for (uint64_t mask = result.gate_extensions; mask; mask &= mask - 1) {
                const int literal = typed_steps[step * gate_types + std::countr_zero(mask)];
                if (literal >= 0) cut.push_back(literal);
            }
        }
        return cut;
    }

    std::vector<int> exclusion(ssv_encoder& enc, const spec& sp, solver_wrapper& solver,
                               std::span<const int> features, std::span<const int> typed_steps, const Extra& ex) {
        const bool two = (ex.slack_two_mode >= 0 || ex.trace_slack_two) && slack_two_seen < 128;
        const bool three = (ex.slack_three_mode >= 0 || ex.trace_slack_three) && slack_three_seen < 128;
        if (!two && !three && (!ex.tight_residual || queries >= 128) && (!ex.slack_one || slack_queries >= 128))
            return {};
        const int n = sp.get_nr_in(), k = sp.nr_steps;
        std::vector<std::pair<int, int>> first;  // (step, selected fanin variable)
        std::array<int, 5> mixed;
        mixed.fill(-1);
        for (int step = 0, offset = 0; step < k; ++step) {
            const int end = offset + enc.nr_svar_map[step];
            for (int s = offset; s < end; ++s) {
                if (!solver.var_value(enc.get_sel_var(s))) continue;
                const auto& pair = enc.svar_map[s];
                if (pair[1] < n) first.emplace_back(step, s);
                else if (pair[0] < n) mixed[pair[0]] = s;
                break;
            }
            offset = end;
        }
        const int h = (int)first.size();
        const int m = (int)std::count_if(mixed.begin(), mixed.end(), [](int s) { return s >= 0; });
        const int slack = k + 1 - (2 * h + m);
        const bool is_tight = slack == 0 && ex.tight_residual && queries < 128;
        const bool is_slack_one = slack == 1 && ex.slack_one && slack_queries < 128;
        const bool is_slack_two = slack == 2 && two && h + m >= 2 && h + m <= 8;
        const bool is_slack_three = slack == 3 && three && h + m >= 2 && h + m <= 8;
        const bool is_wide = is_slack_two || is_slack_three;
        if (!is_wide && ((!is_tight && !is_slack_one) || h + m > 6)) return {};

        std::vector<int> cut;
        std::vector<uint64_t> columns;
        std::vector<int> observed_types;
        uint64_t types = 0;
        bool distinct = is_slack_one || ex.residual_set_cuts;
        for (auto [step, s] : first) {
            cut.push_back(pabc::Abc_Var2Lit(enc.get_sel_var(s), 1));
            const auto& pair = enc.svar_map[s];
            const uint64_t a = primaries[pair[0]], b = primaries[pair[1]];
            const std::array<uint64_t, 4> rows{0, a & ~b, ~a & b, a & b};
            uint64_t column = 0;
            unsigned op = 0;
            for (int bit = 1; bit <= 3; ++bit) {
                const int var = enc.get_op_var(sp, step, bit);
                const bool set = solver.var_value(var);
                cut.push_back(pabc::Abc_Var2Lit(var, set));
                if (set) {
                    column |= rows[bit];
                    op |= 1u << bit;
                }
            }
            if (distinct || (is_slack_one && ex.trace_slack_one) || is_wide) {
                const auto entry = std::find(FirstLayer::aigs.begin(), FirstLayer::aigs.end(), op);
                if (entry == FirstLayer::aigs.end()) return {};
                const auto op_index = entry - FirstLayer::aigs.begin();
                const int pair_index = pair[1] * (pair[1] - 1) / 2 + pair[0];
                const int type_index = int(pair_index * FirstLayer::aigs.size() + op_index);
                const uint64_t type = uint64_t{1} << type_index;
                distinct = distinct && !(types & type);
                types |= type;
                if ((is_slack_one && ex.trace_slack_one) || is_wide) observed_types.push_back(type_index);
            }
            columns.push_back(column);
        }
        unsigned mixed_mask = 0;
        for (int i = 0; i < n; ++i)
            if (mixed[i] >= 0) {
                cut.push_back(is_wide ? features[features.size() - n + i] ^ 1
                                           : pabc::Abc_Var2Lit(enc.get_sel_var(mixed[i]), 1));
                columns.push_back(primaries[i]);
                mixed_mask |= 1u << i;
            }
        if (is_slack_two)
            return slack_two_cut(sp, features, typed_steps, first, std::move(columns), observed_types,
                                 mixed_mask, std::move(cut), ex);
        if (is_slack_three)
            return slack_three_cut(sp, features, typed_steps, first, std::move(columns), observed_types,
                                   mixed_mask, std::move(cut), ex);
        unsigned allowed_extensions = 0;
        if (is_tight) {
            ++queries;
            const auto result = synthesis::residual_zero(
                columns, h, target, care, 4096, ex.residual_filter, clk::time_point::max(), ex.residual_backend);
            if (result == synthesis::ResidualStatus::unknown) ++unknown;
            if (result != synthesis::ResidualStatus::infeasible) return {};
            ++cuts;
            if (distinct) ++set_cuts;
        } else {
            ++slack_queries;
            synthesis::SlackOneStats stats;
            const auto started = clk::now();
            const auto result = synthesis::slack_one_extensions(
                std::move(columns), h, std::span(primaries).first(n), mixed_mask, target, care,
                100000, 4096, stats, started + std::chrono::milliseconds(25),
                ex.residual_filter, ex.residual_backend);
            const double elapsed = since(started);
            slack_seconds += elapsed;
            slack_joins += stats.joins;
            root_splits += stats.root_splits;
            root_rejected += stats.root_rejected;
            allocations += stats.allocations;
            parity_rejected += stats.parity_rejected;
            direct_queries += stats.direct_queries;
            directed_states += stats.directed_states;
            if (ex.trace_slack_one) {
                printf("{\"event\":\"slack_one\",\"k\":%d,\"mixed\":%u,\"types\":[", k, mixed_mask);
                for (size_t i = 0; i < observed_types.size(); ++i)
                    printf("%s%d", i ? "," : "", observed_types[i]);
                printf("],\"exact\":%d,\"feasible_extensions\":%u,\"unknown_extensions\":%u,"
                       "\"work\":%u,\"providers\":%u,\"filtered\":%u,\"decoders\":%u,"
                       "\"joins\":%u,\"root_splits\":%u,\"root_rejected\":%u,\"allocations\":%u,"
                       "\"parity_rejected\":%u,\"direct_queries\":%u,\"directed_states\":%u,\"seconds\":%.6f}\n",
                       int(result.exact), result.feasible, result.unknown,
                       stats.work, stats.providers, stats.filtered, stats.decoders,
                       stats.joins, stats.root_splits, stats.root_rejected, stats.allocations,
                       stats.parity_rejected, stats.direct_queries, stats.directed_states, elapsed);
            }
            if (result.exact == synthesis::ResidualStatus::unknown) ++slack_unknown;
            if (result.exact == synthesis::ResidualStatus::feasible) ++slack_feasible;
            if (result.exact != synthesis::ResidualStatus::infeasible) return {};
            allowed_extensions = result.feasible | result.unknown;
            extension_feasible += std::popcount(result.feasible);
            extension_unknown += std::popcount(result.unknown);
            extension_excluded += n - m - std::popcount(allowed_extensions);
            if (allowed_extensions) ++slack_conditional;
            else ++slack_pure;
            if (!distinct) ++slack_position_cuts;
        }
        // The negative antecedent retains at least h occurrences and m mixed
        // inputs. The only possible extension under slack one is one mixed input.
        if (distinct) {
            cut.clear();
            for (; types; types &= types - 1)
                cut.push_back(features[std::countr_zero(types)] ^ 1);
            for (int i = 0; i < n; ++i)
                if (mixed[i] >= 0) cut.push_back(features[features.size() - n + i] ^ 1);
        }
        for (; allowed_extensions; allowed_extensions &= allowed_extensions - 1)
            cut.push_back(features[features.size() - n + std::countr_zero(allowed_extensions)]);
        return cut;
    }
};

// Last budget entered and the run start, for the out-of-memory record.
static int g_current_k = -1;
static clk::time_point g_run_start = clk::now();

static int run_main(int argc, char** argv) {
    int n = 0, start = 1, budget = -1, maxk = 64, conflicts = 0;
    double wall_seconds = 0;          // 0 = no driver deadline (the harness may still kill the run)
    bool budget_conflicts = false;    // false: --conflicts limits each SAT call (Percy's own meaning)
    std::string tt_hex, dc_hex, solver_name = "bsat", method = "std";
    std::string upper_witness_spec;  // --upper-witness: external chain giving a verified upper bound
    bool nosym = false;
    Extra ex;
    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        auto next = [&]() { return std::string(argv[++i]); };
        if (a == "--n") n = std::stoi(next());
        else if (a == "--tt") tt_hex = next();
        else if (a == "--dc") dc_hex = next();
        else if (a == "--solver") solver_name = next();
        else if (a == "--method") method = next();
        else if (a == "--start") start = std::stoi(next());
        else if (a == "--budget") budget = std::stoi(next());
        else if (a == "--max") maxk = std::stoi(next());
        else if (a == "--conflicts") conflicts = std::stoi(next());
        else if (a == "--seconds") wall_seconds = std::stod(next());
        else if (a == "--conflict-scope") {
            const auto scope = next();
            if (scope == "call") budget_conflicts = false;
            else if (scope == "budget") budget_conflicts = true;
            else { fprintf(stderr, "expected --conflict-scope call or budget\n"); return 2; }
        }
        else if (a == "--nosym") nosym = true;
        else if (a == "--noreapply-full") ex.noreapply_full = true;
        else if (a == "--first-layer-budget") ex.first_layer_budget = true;
        else if (a == "--tight-residual") ex.tight_residual = true;
        else if (a == "--tight-residual-set-cuts") ex.residual_set_cuts = true;
        else if (a == "--slack-one-residual") ex.slack_one = true;
        else if (a == "--trace-slack-one") ex.trace_slack_one = true;
        else if (a == "--trace-slack-two") ex.trace_slack_two = true;
        else if (a == "--slack-two-set-cuts") ex.slack_two_set_cuts = true;
        else if (a == "--trace-slack-three") ex.trace_slack_three = true;
        else if (a == "--slack-three-set-cuts") ex.slack_three_set_cuts = true;
        else if (a == "--slack-three-symmetric") ex.slack_three_symmetric = true;
        else if (a == "--decoder-phase") {
            const std::string v = next();
            if (v != "0" && v != "1" && v != "2") { fprintf(stderr, "expected --decoder-phase 0, 1 or 2\n"); return 2; }
            ex.decoder_phase = unsigned(v[0] - '0');
        }
        else if (a == "--slack-three-ms") ex.slack_three_ms = std::stoi(next());
        else if (a == "--restriction-cuts") {
            const auto mode = next();
            if (mode == "trace") ex.restriction_cuts = 1;
            else if (mode == "cut") ex.restriction_cuts = 2;
            else if (mode == "all") ex.restriction_cuts = 3;
            else if (mode == "rows") ex.restriction_cuts = 4;
            else { fprintf(stderr, "expected --restriction-cuts trace, cut, all or rows\n"); return 2; }
        }
        else if (a == "--capture-models") ex.capture_models = next();
        else if (a == "--restriction-counters") {
            const auto mode = next();
            if (mode == "zero") ex.restriction_counters = 1;
            else if (mode == "const") ex.restriction_counters = 2;
            else if (mode == "anchor") ex.restriction_counters = 3;
            else { fprintf(stderr, "expected --restriction-counters zero, const or anchor\n"); return 2; }
        }
        else if (a == "--restriction-live") {
            const auto v = next();
            ex.restriction_live = v == "all" ? -1 : std::stoi(v);
            if (ex.restriction_live == 0 || ex.restriction_live < -1) { fprintf(stderr, "expected --restriction-live all or N > 0\n"); return 2; }
        }
        else if (a == "--restriction-essential") ex.restriction_essential = true;
        else if (a == "--mixed-rank-cuts") ex.mixed_rank_min = std::stoi(next());
        else if (a == "--restriction-conditional") ex.restriction_conditional = true;
        else if (a == "--upper-witness") upper_witness_spec = next();
        else if (a == "--hybrid-witness") {
            ex.hybrid_witness = std::stoi(next());
            if (ex.hybrid_witness <= 0) { fprintf(stderr, "expected --hybrid-witness W > 0\n"); return 2; }
        }
        else if (a == "--restriction-cone-slice") {
            ex.cone_slice = std::stoi(next());
            if (ex.cone_slice <= 0) { fprintf(stderr, "expected --restriction-cone-slice S > 0\n"); return 2; }
        }
        else if (a == "--complement-inputs") {
            if (next() != "auto") { fprintf(stderr, "expected --complement-inputs auto\n"); return 2; }
            ex.complement_inputs = true;
        }
        else if (a == "--restriction-burst") ex.restriction_burst = unsigned(std::stoul(next()));
        else if (a == "--slack-two-ms") ex.slack_two_ms = std::stoi(next());
        else if (a == "--slack-two-work") ex.slack_two_work = unsigned(std::stoul(next()));
        else if (a == "--slack-three-work") ex.slack_three_work = unsigned(std::stoul(next()));
        else if (a == "--slack-three-policy") {
            const auto policy = next();
            using Policy = synthesis::SlackThreePolicy;
            if (policy == "full") ex.slack_three_policy = Policy::full;
            else if (policy == "exact") ex.slack_three_policy = Policy::exact;
            else if (policy == "lift1") ex.slack_three_policy = Policy::lift1;
            else if (policy == "adaptive") ex.slack_three_policy = Policy::adaptive;
            else { fprintf(stderr, "expected --slack-three-policy full, exact, lift1 or adaptive\n"); return 2; }
        }
        else if (a == "--slack-three-residual") {
            const auto mode = next();
            if (mode == "memo") ex.slack_three_mode = 2;
            else if (mode == "unate") ex.slack_three_mode = 3;
            else if (mode == "phase") ex.slack_three_mode = 4;
            else if (mode == "phase-cache") ex.slack_three_mode = 5;
            else { fprintf(stderr, "expected --slack-three-residual memo, unate, phase or phase-cache\n"); return 2; }
        }
        else if (a == "--slack-two-residual") {
            const auto mode = next();
            if (mode == "memo") ex.slack_two_mode = 2;
            else if (mode == "unate") ex.slack_two_mode = 3;
            else if (mode == "phase") ex.slack_two_mode = 4;
            else if (mode == "phase-cache") ex.slack_two_mode = 5;
            else { fprintf(stderr, "expected --slack-two-residual memo, unate, phase or phase-cache\n"); return 2; }
        }
        else if (a == "--residual-filter") {
            const auto mode = next();
            using Mode = synthesis::ResidualFilterMode;
            if (mode == "off") ex.residual_filter = Mode::off;
            else if (mode == "root") ex.residual_filter = Mode::root;
            else if (mode == "parity") ex.residual_filter = Mode::parity;
            else if (mode == "direct") ex.residual_filter = Mode::direct;
            else { fprintf(stderr, "expected --residual-filter off, root, parity or direct\n"); return 2; }
        }
        else if (a == "--residual-backend") {
            const auto backend = next();
            using Backend = synthesis::ResidualBackend;
            if (backend == "columns") ex.residual_backend = Backend::columns;
            else if (backend == "directed") ex.residual_backend = Backend::directed;
            else if (backend == "dominance") ex.residual_backend = Backend::dominance;
            else { fprintf(stderr, "expected --residual-backend columns, directed or dominance\n"); return 2; }
        }
        else if (a == "--first-layer") {
            const auto scope = next();
            if (scope == "edges") ex.pairs = synthesis::PairScope::edges;
            else if (scope == "all") ex.pairs = synthesis::PairScope::all;
            else { fprintf(stderr, "expected --first-layer edges or all\n"); return 2; }
        }
        else if (a == "--cofactor-lb") {          // "L0,L1,nc0,nc1;..." per input, x0 first (minimum-preserving caps)
            std::stringstream ss(next()); std::string item;
            while (std::getline(ss, item, ';')) {
                std::array<int, 4> v{}; char sep;
                std::stringstream is(item); is >> v[0] >> sep >> v[1] >> sep >> v[2] >> sep >> v[3];
                ex.cof.push_back(v);
            }
        }
        else { fprintf(stderr, "unknown argument %s\n", a.c_str()); return 2; }
    }
    if ((ex.pairs != synthesis::PairScope::none || ex.first_layer_budget) &&
        (n < 2 || n > 5 || (ex.first_layer_budget && nosym) || (!dc_hex.empty() && method == "cegar"))) {
        fprintf(stderr, "first-layer options need 2-5 inputs, alonce for the budget bound, and std for partial tables\n");
        return 2;
    }
    const bool slack_two = ex.slack_two_mode >= 0 || ex.trace_slack_two;
    const bool slack_three = ex.slack_three_mode >= 0 || ex.trace_slack_three;
    if ((ex.tight_residual || ex.slack_one || slack_two || slack_three) &&
        (n < 2 || n > 5 || nosym || method != "cegar" || !dc_hex.empty())) {
        fprintf(stderr, "residual exclusions need trimmed CEGAR and a complete 2-5 input table\n");
        return 2;
    }
    if ((ex.slack_one && ex.pairs == synthesis::PairScope::none) || (ex.trace_slack_one && !ex.slack_one)) {
        fprintf(stderr, "slack-one exclusions need --first-layer edges or all; tracing needs --slack-one-residual\n");
        return 2;
    }
    if (slack_two && ex.pairs == synthesis::PairScope::none) {
        fprintf(stderr, "slack-two completion and tracing need --first-layer edges or all\n");
        return 2;
    }
    if (ex.slack_two_set_cuts && ex.slack_two_mode < 0) {
        fprintf(stderr, "--slack-two-set-cuts needs --slack-two-residual\n");
        return 2;
    }
    if (slack_three && ex.pairs == synthesis::PairScope::none) {
        fprintf(stderr, "slack-three completion and tracing need --first-layer edges or all\n");
        return 2;
    }
    if ((ex.slack_three_set_cuts || ex.slack_three_symmetric) && ex.slack_three_mode < 0) {
        fprintf(stderr, "--slack-three-set-cuts and --slack-three-symmetric need --slack-three-residual\n");
        return 2;
    }
    if (ex.slack_three_policy != synthesis::SlackThreePolicy::full &&
        (ex.slack_three_mode < 0 || !ex.first_layer_budget)) {
        fprintf(stderr, "--slack-three-policy needs --slack-three-residual and --first-layer-budget\n");
        return 2;
    }
    if (ex.decoder_phase && ex.slack_two_mode < 1 && ex.slack_three_mode < 1) {
        fprintf(stderr, "--decoder-phase needs --slack-two-residual or --slack-three-residual with mode >= 1\n");
        return 2;
    }
    if ((ex.restriction_cuts || !ex.capture_models.empty()) && (method != "cegar" || n < 2 || n > 6)) {
        fprintf(stderr, "--restriction-cuts and --capture-models need CEGAR and 2-6 inputs\n");
        return 2;
    }
    if ((ex.restriction_counters || ex.complement_inputs) && (n < 2 || n > 6)) {
        fprintf(stderr, "--restriction-counters and --complement-inputs need 2-6 inputs\n");
        return 2;
    }
    if (ex.hybrid_witness && !ex.restriction_live && !ex.restriction_essential) {
        fprintf(stderr, "--hybrid-witness needs --restriction-live or --restriction-essential\n");
        return 2;
    }
    if (ex.hybrid_witness && budget >= 0) { fprintf(stderr, "--hybrid-witness needs a ladder, not --budget\n"); return 2; }
    if (ex.cone_slice && !ex.restriction_live && !ex.restriction_essential) {
        fprintf(stderr, "--restriction-cone-slice needs --restriction-live or --restriction-essential\n");
        return 2;
    }
    if ((ex.restriction_live || ex.restriction_essential) && !ex.restriction_counters) {
        fprintf(stderr, "--restriction-live and --restriction-essential need --restriction-counters\n");
        return 2;
    }
    if (ex.restriction_conditional && (!ex.restriction_counters || n != 4 || !dc_hex.empty())) {
        // The table is for complete three-input restricted targets; a partial target needs its own justification.
        fprintf(stderr, "--restriction-conditional needs --restriction-counters, 4 inputs and a complete table\n");
        return 2;
    }
    if (ex.mixed_rank_min < 0 || (ex.mixed_rank_min && !dc_hex.empty())) {
        // The floor needs the rank of the complete function; a partial table has no fixed completion rank.
        fprintf(stderr, "--mixed-rank-cuts needs a positive floor and a complete table (no --dc)\n");
        return 2;
    }
    if (ex.restriction_counters && ex.restriction_cuts) {
        fprintf(stderr, "--restriction-counters is not combined with --restriction-cuts\n");
        return 2;
    }
    if (ex.slack_two_ms <= 0 || ex.slack_two_work == 0) {
        fprintf(stderr, "--slack-two-ms and --slack-two-work must be positive\n");
        return 2;
    }
    if (ex.slack_three_ms <= 0 || ex.slack_three_work == 0) {
        fprintf(stderr, "--slack-three-ms and --slack-three-work must be positive\n");
        return 2;
    }
    if ((ex.residual_filter != synthesis::ResidualFilterMode::off ||
         ex.residual_backend != synthesis::ResidualBackend::columns) && !ex.tight_residual && !ex.slack_one) {
        fprintf(stderr, "residual options need --tight-residual or --slack-one-residual\n");
        return 2;
    }
    if (ex.residual_set_cuts && (!ex.tight_residual || ex.pairs == synthesis::PairScope::none)) {
        fprintf(stderr, "tight residual set cuts need --tight-residual and --first-layer edges or all\n");
        return 2;
    }
    kitty::dynamic_truth_table tt(n), dc(n);
    kitty::create_from_hex_string(tt, tt_hex);
    if (!dc_hex.empty()) kitty::create_from_hex_string(dc, dc_hex);
    const auto tt_given = tt, dc_given = dc;
    const auto pack = [&](const kitty::dynamic_truth_table& t, bool flip) {
        uint64_t m = 0;
        for (int r = 0; r < (1 << n); ++r) m |= uint64_t(kitty::get_bit(t, r) ^ flip) << r;
        return m;
    };
    // External upper bound (--upper-witness "a,b;a,b;...|out"): literal 2*w+p is wire w complemented when p,
    // wire 0 is constant zero, wires 1..n the inputs, wire n+1+j gate j = AND of its two literals. The chain is
    // simulated here against the given table on the care set; it is a feasible upper bound only, not a prefix.
    std::vector<std::array<int, 2>> ext_gates;
    int ext_out = -1, ext_size = -1;
    if (!upper_witness_spec.empty()) {
        if (n > 6 || budget >= 0 || ex.hybrid_witness) {
            fprintf(stderr, "--upper-witness needs at most 6 inputs and a ladder without --budget or --hybrid-witness\n");
            return 2;
        }
        const auto bar = upper_witness_spec.find('|');
        if (bar == std::string::npos) { fprintf(stderr, "--upper-witness: expected GATES|OUT\n"); return 2; }
        const std::string body = upper_witness_spec.substr(0, bar);
        ext_out = std::stoi(upper_witness_spec.substr(bar + 1));
        for (size_t pos = 0; pos < body.size();) {
            size_t end = body.find(';', pos);
            if (end == std::string::npos) end = body.size();
            const std::string g = body.substr(pos, end - pos);
            const auto comma = g.find(',');
            if (comma == std::string::npos) { fprintf(stderr, "--upper-witness: bad gate '%s'\n", g.c_str()); return 2; }
            ext_gates.push_back({std::stoi(g.substr(0, comma)), std::stoi(g.substr(comma + 1))});
            pos = end + 1;
        }
        const uint64_t full = n == 6 ? ~0ull : (1ull << (1 << n)) - 1;
        std::vector<uint64_t> wire{0};
        for (int i = 0; i < n; ++i) {
            uint64_t m = 0;
            for (int r = 0; r < (1 << n); ++r) m |= uint64_t(r >> i & 1) << r;
            wire.push_back(m);
        }
        const auto lit = [&](int l, bool& ok) {
            if (l < 0 || l / 2 >= int(wire.size())) { ok = false; return uint64_t(0); }
            return wire[l / 2] ^ (l & 1 ? full : 0);
        };
        bool ok = true;
        for (const auto& g : ext_gates) {
            ok &= g[0] >= 2 && g[1] >= 2;  // no constant operands (Percy steps read inputs or steps)
            wire.push_back(lit(g[0], ok) & lit(g[1], ok));
        }
        const uint64_t sim = lit(ext_out, ok);
        if (!ok || ((sim ^ pack(tt_given, false)) & pack(dc_given, true)) != 0) {
            fprintf(stderr, "--upper-witness does not compute the target on its care set\n");
            return 2;
        }
        ext_size = int(ext_gates.size());
    }
    unsigned complement_mask = 0;  // inputs complemented by --complement-inputs auto
    if (ex.complement_inputs) {
        const auto rs = restriction_certificate::restrictions(unsigned(n), pack(tt, false), pack(dc, true));
        for (int i = 0; i < n; ++i)
            if (rs[2 * i + 1].lower > rs[2 * i].lower) complement_mask |= 1u << i;
        auto t2 = tt, d2 = dc;
        for (int r = 0; r < (1 << n); ++r) {
            if (kitty::get_bit(tt, r ^ complement_mask)) kitty::set_bit(t2, r); else kitty::clear_bit(t2, r);
            if (kitty::get_bit(dc, r ^ complement_mask)) kitty::set_bit(d2, r); else kitty::clear_bit(d2, r);
        }
        tt = t2; dc = d2;
        for (int i = 0; i < (int)ex.cof.size() && i < n; ++i)
            if (complement_mask >> i & 1) {
                std::swap(ex.cof[i][0], ex.cof[i][1]);
                std::swap(ex.cof[i][2], ex.cof[i][3]);
            }
    }
    if (ex.mixed_rank_min) {  // after --complement-inputs: the table actually synthesized (rank is invariant anyway)
        mixed_rank::Table f(size_t(1) << n);
        for (int r = 0; r < (1 << n); ++r) f[size_t(r)] = kitty::get_bit(tt, r) ? 1 : 0;
        ex.mixed_cuts = mixed_rank::select_cuts(n, f, 8, ex.mixed_rank_min);
    }
    if (ex.restriction_counters) {
        const auto rs = restriction_certificate::restrictions(unsigned(n), pack(tt, false), pack(dc, true));
        for (int i = 0; i < n; ++i) {
            if (ex.restriction_counters == 1) ex.counters.push_back(rs[2 * i]);
            else if (ex.restriction_counters == 2) { ex.counters.push_back(rs[2 * i]); ex.counters.push_back(rs[2 * i + 1]); }
            else ex.counters.push_back(rs[2 * i + (rs[2 * i + 1].lower > rs[2 * i].lower)]);
        }
        const size_t m = ex.counters.size();
        if (ex.restriction_conditional) {
            ex.counter_f3.assign(m, -1);
            for (size_t c = 0; c < m; ++c) {
                int i = -1, b = 0;
                for (int v = 0; v < n; ++v) if (ex.counters[c].primary[v] < 2) { i = v; b = int(ex.counters[c].primary[v]); }
                if (i < 0) continue;
                int f3 = 0;
                for (int s = 0; s < 8; ++s) {
                    int row = b << i, t = 0;
                    for (int v = 0; v < n; ++v) if (v != i) row |= (s >> t++ & 1) << v;
                    f3 |= int(kitty::get_bit(tt, row)) << s;
                }
                // The table's empty-set cost must equal the counter's lower bound (exact kCost3 on complete tables).
                if (conditional_cost3::kCost3Normalized[std::min(f3, 255 ^ f3)] != ex.counters[c].lower) {
                    fprintf(stderr, "conditional table cost %d differs from counter bound %u\n",
                            conditional_cost3::kCost3Normalized[std::min(f3, 255 ^ f3)], ex.counters[c].lower);
                    return 2;
                }
                ex.counter_f3[c] = f3;
            }
        }
        ex.counter_live.assign(m, ex.restriction_live == -1);
        if (ex.restriction_live > 0) {
            std::vector<size_t> order(m);
            for (size_t c = 0; c < m; ++c) order[c] = c;
            std::stable_sort(order.begin(), order.end(),
                             [&](size_t x, size_t y) { return ex.counters[x].lower > ex.counters[y].lower; });
            for (size_t c = 0; c < m && c < size_t(ex.restriction_live); ++c) ex.counter_live[order[c]] = true;
        }
        ex.counter_essential.assign(m, {});
        // Input j is essential in every completion of f o (x_i := b) if two cared rows that differ only in j differ.
        for (size_t c = 0; c < m && ex.restriction_essential; ++c) {
            int i = 0, b = 0;
            for (int v = 0; v < n; ++v) if (ex.counters[c].primary[v] < 2) { i = v; b = int(ex.counters[c].primary[v]); }
            for (int j = 0; j < n; ++j) {
                if (j == i) continue;
                bool dep = false;
                for (int r = 0; r < (1 << n) && !dep; ++r) {
                    if ((r >> i & 1) != b || (r >> j & 1)) continue;
                    const int q = r | 1 << j;
                    dep = !kitty::get_bit(dc, r) && !kitty::get_bit(dc, q) && kitty::get_bit(tt, r) != kitty::get_bit(tt, q);
                }
                if (dep) ex.counter_essential[c].push_back(j);
            }
        }
    }
    if ((ex.pairs != synthesis::PairScope::none || ex.first_layer_budget) && kitty::get_bit(dc, 0)) {
        fprintf(stderr, "first-layer partial tables must label row zero (Percy normalizes to that row)\n");
        return 2;
    }

    spec sp;
    sp.set_primitive(AIG);
    sp[0] = tt;
    if (!dc_hex.empty()) sp.set_dont_care(0, dc);
    sp.conflict_limit = conflicts;
    if (nosym) {
        sp.add_alonce_clauses = sp.add_noreapply_clauses = sp.add_colex_clauses = false;
        sp.add_lex_func_clauses = sp.add_symvar_clauses = false;
    }

    std::unique_ptr<solver_wrapper> solver;
    if (solver_name == "bsat") solver.reset(new bsat_wrapper);
#ifdef USE_SATOKO
    else if (solver_name == "satoko") solver.reset(new satoko_wrapper);
#endif
    else if (solver_name == "bmcg") solver.reset(new bmcg_wrapper);
    else { fprintf(stderr, "unknown solver %s\n", solver_name.c_str()); return 2; }
    // Wall-clock deadline for the whole run (all budgets): a watcher thread raises Satoko's stop
    // flag, so the running SAT call returns unknown and the budget is reported as wall_deadline.
    int stop_flag = 0;
    std::mutex stop_mutex;
    std::condition_variable stop_cv;
    bool run_done = false;
    std::thread watcher;
    const auto wall_deadline = wall_seconds > 0
        ? g_run_start + std::chrono::duration_cast<clk::duration>(std::chrono::duration<double>(wall_seconds))
        : clk::time_point::max();
    if (wall_seconds > 0) {
#ifdef USE_SATOKO
        const auto backend = dynamic_cast<satoko_wrapper*>(solver.get());
        if (!backend) { fprintf(stderr, "--seconds needs --solver satoko\n"); return 2; }
        satoko::satoko_set_stop(backend->solver, &stop_flag);
        watcher = std::thread([&] {
            std::unique_lock lock(stop_mutex);
            if (!stop_cv.wait_until(lock, wall_deadline, [&] { return run_done; }))
                std::atomic_ref<int>(stop_flag).store(1);
        });
#else
        fprintf(stderr, "--seconds needs Satoko\n");
        return 2;
#endif
    }
    struct StopWatcher {
        std::mutex& m; std::condition_variable& cv; bool& done; std::thread& t;
        ~StopWatcher() {
            { std::lock_guard lock(m); done = true; }
            cv.notify_all();
            if (t.joinable()) t.join();
        }
    } stop_guard{stop_mutex, stop_cv, run_done, watcher};
    const auto out_of_time = [&] {
        return std::atomic_ref<int>(stop_flag).load() != 0 || clk::now() >= wall_deadline;
    };
    std::string final_reason = "unsat";
    ssv_encoder enc(*solver);
    chain c;
    const bool cegar = method == "cegar";

    auto t0 = clk::now();
    const FirstLayer layer(tt, dc, ex);
    const double target_constraints_seconds = since(t0);
    sp.preprocess();
    std::string final_status = "UNSAT";
    int found = -1;
    int upper = -1;  // hybrid: smallest budget with a verified witness so far
    if (sp.nr_triv == sp.get_nr_out()) {        // constant or projection: zero steps
        c.reset(sp.get_nr_in(), sp.get_nr_out(), 0, sp.fanin);
        c.set_output(0, (sp.triv_func(0) << 1) + (sp.out_inv & 1));
        final_status = "SAT"; found = 0;
    } else {
        if (cegar) enc.reset_sim_tts(sp.nr_in);
        int lo = budget >= 0 ? budget : start, hi = budget >= 0 ? budget : maxk;
        // An external witness of size U leaves only the budgets below U; each must be proved (or found SAT).
        if (ext_size >= 0) { upper = ext_size; hi = std::min(hi, ext_size - 1); }
        synthesis::ResidualMemo three_memo;  // decided residual answers are budget independent
        std::vector<restriction_certificate::Restriction> restrictions;
        if (ex.restriction_cuts) {
            uint64_t value = 0, care = 0;
            for (int r = 0; r < (1 << n); ++r) {
                value |= uint64_t(kitty::get_bit(tt, r)) << r;
                care |= uint64_t(!kitty::get_bit(dc, r)) << r;
            }
            restrictions = restriction_certificate::restrictions(unsigned(n), value, care);
        }
        std::unique_ptr<FILE, int (*)(FILE*)> capture(nullptr, fclose);
        if (!ex.capture_models.empty()) {
            capture.reset(fopen(ex.capture_models.c_str(), "wx"));
            if (!capture) { fprintf(stderr, "cannot create %s\n", ex.capture_models.c_str()); return 2; }
        }
        // Hybrid schedule (--hybrid-witness): pass 0 is the plain ladder; pass 1 the cone-free witness pass, pass 2
        // the cone proofs of the budgets pass 1 skipped. ex_witness is ex with every cone constraint removed.
        Extra ex_witness = ex;
        ex_witness.counter_live.assign(ex.counter_live.size(), false);
        for (auto& e : ex_witness.counter_essential) e.clear();
        ex_witness.cone_slice = 0;
        int pass = ex.hybrid_witness ? 1 : 0;
        std::vector<int> skipped;
        size_t next_skipped = 0;
        for (int k = lo;;) {
            if (pass == 2) {
                if (next_skipped == skipped.size()) break;
                k = skipped[next_skipped++];
            } else if (k > hi) {
                if (pass == 1 && !skipped.empty()) { pass = 2; continue; }
                break;
            }
            // The cone constraints are used only to prove budgets below a verified upper bound. Without one,
            // pass 2 runs the skipped budgets with the unrestricted (cone-free) fallback, uncapped.
            const bool proving = pass == 2 && upper >= 0 && k < upper;
            const Extra& exk = pass == 0 || proving ? ex : ex_witness;
            g_current_k = k;
            g_slice = {};
            auto tk = clk::now();
            sp.nr_steps = k;
            solver->restart();
            const int conflicts_before = solver->nr_conflicts();
            long decisions = 0, propagations_before = 0;
#ifdef USE_SATOKO
            const auto satoko_backend = dynamic_cast<satoko_wrapper*>(solver.get());
            if (satoko_backend)
                propagations_before = satoko::satoko_stats(satoko_backend->solver)->n_propagations_all;
#endif
            int sat_calls = 0;
            std::string reason;   // why this budget ended: sat, unsat, conflict_limit, wall_deadline
            const auto solve = [&] {
                if (out_of_time()) { reason = "wall_deadline"; return timeout; }
                int limit = sp.conflict_limit;
                if (budget_conflicts && limit > 0) {
                    limit -= solver->nr_conflicts() - conflicts_before;
                    if (limit <= 0) { reason = "conflict_limit"; return timeout; }
                }
                bool capped = false;  // the witness-pass cap is the binding limit of this call
                if (pass == 1) {
                    const int left = ex.hybrid_witness - (solver->nr_conflicts() - conflicts_before);
                    if (left <= 0) { reason = "witness_cap"; return timeout; }
                    if (limit <= 0 || left <= limit) { limit = left; capped = true; }
                }
                ++sat_calls;
                synth_result result;
                if (g_cone_guard < 0) result = solver->solve(limit);
                else {
                    // Alternate cone-on (assume a) and cone-off (assume !a) slices. UNSAT under a is UNSAT: the
                    // guarded clauses hold in every chain. Learned clauses that use them carry !a.
                    int slice = ex.cone_slice, used = 0;
                    bool on = true;
                    while (true) {
                        int lim = slice;
                        if (limit > 0) lim = std::min(lim, limit - used);
                        if (lim <= 0) { result = timeout; break; }
                        pabc::lit assume = on ? g_cone_guard : g_cone_guard ^ 1;
                        const int c0 = solver->nr_conflicts();
                        ++g_slice.slices;
                        result = solver->solve(&assume, &assume + 1, lim);
                        used += solver->nr_conflicts() - c0;
                        if (result == success) { ++(on ? g_slice.on_sat : g_slice.off_sat); break; }
                        if (result == failure) { ++(on ? g_slice.on_unsat : g_slice.off_unsat); break; }
                        if (out_of_time()) break;
                        if (!on) slice = slice > (1 << 29) ? slice : 2 * slice;
                        on = !on;
                    }
                }
                if (result != success && result != failure)
                    reason = out_of_time() ? "wall_deadline" : capped ? "witness_cap" : "conflict_limit";
#ifdef USE_SATOKO
                if (satoko_backend) decisions += satoko::satoko_stats(satoko_backend->solver)->n_decisions;
#endif
                return result;
            };
            std::string st;
            int extra_clauses = 0;
            double encoding_seconds = 0;
            int cegar_rows = 0;
            RestrictionStats rstats;
            unsigned restriction_run = 0;  // consecutive certificate cuts since the last CEGAR row
            std::vector<int> layer_features;
            std::vector<int> typed_steps, thresholds;
            const auto residual_start = clk::now();
            std::optional<TightResidual> residual;
            if (ex.tight_residual || ex.slack_one || slack_two || slack_three) {
                residual.emplace(tt);
                residual->thresholds = &thresholds;
                residual->memo = &three_memo;
            }
            double residual_seconds = residual ? since(residual_start) : 0;
            if (!cegar) {
                const bool encoded = enc.encode(sp) &&
                    add_extra(enc, sp, *solver, exk, layer, extra_clauses, layer_features, typed_steps, thresholds);
                encoding_seconds = since(tk);
                if (!encoded) st = "UNSAT";
                else {
                    auto r = solve();
                    st = r == success ? "SAT" : r == failure ? "UNSAT" : "TIMEOUT";
                    if (r == success) enc.extract_chain(sp, c);
                }
            } else {
                const bool encoded = enc.cegar_encode(sp) &&
                    add_extra(enc, sp, *solver, exk, layer, extra_clauses, layer_features, typed_steps, thresholds);
                encoding_seconds = since(tk);
                if (!encoded) st = "UNSAT";
                else {
                    int iMint = 1; st = "UNSAT";
                    while (true) {
                        if (iMint > 0) {
                            const auto row_start = clk::now();
                            ++cegar_rows;
                            const bool row_encoded = enc.create_tt_clauses(sp, iMint - 1);
                            encoding_seconds += since(row_start);
                            if (!row_encoded) { st = "UNSAT"; break; }
                        }
                        auto r = solve();
                        if (r == failure) { st = "UNSAT"; break; }
                        if (r != success) { st = "TIMEOUT"; break; }
                        if (out_of_time()) { st = "TIMEOUT"; reason = "wall_deadline"; break; }
                        bool trace_rejected = false;
                        if (ex.restriction_cuts || capture) {
                            // Read the model's chain. Percy's normalized AIG ops keep their own output phase:
                            // 8 a&b, 2 a&!b, 4 !a&b, 14 a|b = !(!a&!b) (inverted AND of complements).
                            const auto rc_start = clk::now();
                            std::vector<restriction_certificate::Gate> gates;
                            std::vector<int> selected(k), ops(k);
                            bool aig = true;
                            for (int step = 0, offset = 0; step < k; ++step) {
                                const int end = offset + enc.nr_svar_map[step];
                                int s = offset;
                                while (s < end && !solver->var_value(enc.get_sel_var(s))) ++s;
                                offset = end;
                                if (s == end) { aig = false; break; }
                                int op = 0;
                                for (int bit = 1; bit <= 3; ++bit)
                                    op |= int(solver->var_value(enc.get_op_var(sp, step, bit))) << bit;
                                selected[step] = s; ops[step] = op;
                                const unsigned fa = unsigned(enc.svar_map[s][0]), fb = unsigned(enc.svar_map[s][1]);
                                if (op == 8) gates.push_back({fa, fb, true, true, false});
                                else if (op == 2) gates.push_back({fa, fb, true, false, false});
                                else if (op == 4) gates.push_back({fa, fb, false, true, false});
                                else if (op == 14) gates.push_back({fa, fb, false, false, true});
                                else aig = false;
                            }
                            if (capture && aig) {
                                fprintf(capture.get(), "{\"k\":%d,\"row\":%d,\"chain\":[", k, cegar_rows);
                                for (int step = 0; step < k; ++step)
                                    fprintf(capture.get(), "%s[%d,%d,%d]", step ? "," : "", ops[step],
                                            enc.svar_map[selected[step]][0], enc.svar_map[selected[step]][1]);
                                fprintf(capture.get(), "]}\n");
                            }
                            std::vector<restriction_certificate::Certificate> certs;
                            if (ex.restriction_cuts && aig) {
                                ++rstats.models;
                                bool failed = false;
                                certs = restriction_certificate::certify(restrictions, gates, ex.restriction_cuts != 3,
                                                                         true, &failed);
                                if (failed) {
                                    fprintf(stderr, "restriction certificate self-check failed at k=%d\n", k);
                                    std::exit(4);
                                }
                            }
                            bool added_all = true;
                            for (const auto& cert : certs) {
                                std::vector<int> clause;
                                for (int step = 0; step < k; ++step) {
                                    const auto bit = restriction_certificate::Mask(1) << step;
                                    if (!(cert.core.pairs & bit)) continue;
                                    clause.push_back(pabc::Abc_Var2Lit(enc.get_sel_var(selected[step]), 1));
                                    // Given the AIG primitive clauses, op bits 1 and 2 identify the operator.
                                    if (cert.core.typed & bit)
                                        for (int b = 1; b <= 2; ++b)
                                            clause.push_back(pabc::Abc_Var2Lit(enc.get_op_var(sp, step, b), ops[step] >> b & 1));
                                }
                                std::sort(clause.begin(), clause.end());
                                rstats.literals += unsigned(clause.size());
                                rstats.pair_only += unsigned(std::popcount(cert.core.pairs & ~cert.core.typed));
                                rstats.typed += unsigned(std::popcount(cert.core.typed));
                                ++rstats.width[std::min<size_t>(clause.size(), 16)];
                                rstats.empty += clause.empty();
                                if (!rstats.seen.insert(clause).second) ++rstats.repeats;
                                else {
                                    for (const auto& old : rstats.stored) {
                                        rstats.subsumed += std::includes(clause.begin(), clause.end(), old.begin(), old.end());
                                        rstats.subsumes += old.size() > clause.size() &&
                                            std::includes(old.begin(), old.end(), clause.begin(), clause.end());
                                    }
                                    if (rstats.stored.size() < 4096) rstats.stored.push_back(clause);
                                }
                                if (ex.restriction_cuts >= 2) {
                                    ++rstats.cuts;
                                    // An empty core means L(f o pi) > budget: the exact restricted cost alone refutes it.
                                    if (clause.empty() || !solver->add_clause(clause.data(), clause.data() + clause.size()))
                                        added_all = false;
                                }
                            }
                            if (!certs.empty()) ++rstats.rejects;
                            rstats.seconds += since(rc_start);
                            if (!added_all) { st = "UNSAT"; break; }
                            if ((ex.restriction_cuts == 2 || ex.restriction_cuts == 3) && !certs.empty() &&
                                (!ex.restriction_burst || ++restriction_run <= ex.restriction_burst)) { iMint = 0; continue; }
                            restriction_run = 0;
                            trace_rejected = !certs.empty();
                        }
                        if (residual) {
                            const auto check_start = clk::now();
                            auto cut = residual->exclusion(enc, sp, *solver, layer_features, typed_steps, ex);
                            const bool retained = cut.empty() || solver->add_clause(cut.data(), cut.data() + cut.size());
                            residual_seconds += since(check_start);
                            if (!retained) { st = "UNSAT"; break; }
                            if (!cut.empty()) {
                                rstats.trace_residual += trace_rejected;
                                iMint = 0;
                                continue;
                            }
                        }
                        iMint = enc.simulate(sp);
                        if (trace_rejected && iMint == -1) {
                            // A certified model must fail: a correct B-gate circuit contradicts the certificate.
                            fprintf(stderr, "restriction certificate rejected a correct circuit at k=%d\n", k);
                            std::exit(4);
                        }
                        rstats.trace_rows += trace_rejected;
                        if (iMint == -1) { st = "SAT"; enc.cegar_extract_chain(sp, c); break; }
                    }
                }
            }
            if (st == "SAT") reason = "sat";
            else if (st == "UNSAT") reason = "unsat";
            else if (reason.empty()) reason = "unknown";
            printf("{\"k\":%d,\"status\":\"%s\",\"reason\":\"%s\",\"elapsed\":%.6f,\"sat_calls\":%d,"
                   "\"conflict_limit\":%d,\"conflict_scope\":\"%s\",\"wall_limit\":%.3f,",
                   k, st.c_str(), reason.c_str(), since(g_run_start), sat_calls, sp.conflict_limit,
                   budget_conflicts ? "budget" : "call", wall_seconds);
            if (ex.hybrid_witness) printf("\"phase\":\"%s\",", pass == 1 ? "witness" : proving ? "proof" : "fallback");
            printf("\"seconds\":%.6f,\"extra_clauses\":%d,"
                   "\"encoding_seconds\":%.6f,\"cegar_rows\":%d,\"conflicts\":%d,\"vars\":%d,\"clauses\":%d",
                   since(tk), extra_clauses, encoding_seconds, cegar_rows,
                   solver->nr_conflicts() - conflicts_before, solver->nr_vars(), solver->nr_clauses());
            if (residual)
                printf(",\"residual_queries\":%d,\"residual_cuts\":%d,\"residual_set_cuts\":%d,"
                       "\"residual_unknown\":%d,\"residual_seconds\":%.6f",
                       residual->queries, residual->cuts, residual->set_cuts, residual->unknown, residual_seconds);
            if (residual && (slack_two || slack_three))
                printf(",\"two_unknown_cause\":[%u,%u,%u],\"three_unknown_cause\":[%u,%u,%u]",
                       residual->two_unknown_cause[0], residual->two_unknown_cause[1],
                       residual->two_unknown_cause[2], residual->three_unknown_cause[0],
                       residual->three_unknown_cause[1], residual->three_unknown_cause[2]);
            if (ex.slack_one)
                printf(",\"slack_queries\":%d,\"slack_feasible\":%d,\"slack_unknown\":%d,\"slack_pure\":%d,"
                       "\"slack_conditional\":%d,\"extension_feasible\":%d,\"extension_unknown\":%d,"
                       "\"extension_excluded\":%d,\"slack_position_cuts\":%d,\"slack_seconds\":%.6f,"
                       "\"slack_joins\":%u,\"root_splits\":%u,\"root_rejected\":%u,\"provider_allocations\":%u,"
                       "\"parity_rejected\":%u,\"direct_queries\":%u,\"directed_states\":%u",
                       residual->slack_queries, residual->slack_feasible, residual->slack_unknown,
                       residual->slack_pure, residual->slack_conditional, residual->extension_feasible,
                       residual->extension_unknown, residual->extension_excluded, residual->slack_position_cuts,
                       residual->slack_seconds, residual->slack_joins, residual->root_splits, residual->root_rejected,
                       residual->allocations, residual->parity_rejected, residual->direct_queries,
                       residual->directed_states);
            if (slack_two)
                printf(",\"slack_two_seen\":%d,\"slack_two_unknown\":%d,\"slack_two_feasible\":%d,"
                       "\"slack_two_pure\":%d,\"slack_two_conditional\":%d,\"slack_two_seconds\":%.6f,"
                       "\"two_extension_feasible\":%u,\"two_extension_unknown\":%u,\"two_extension_excluded\":%u,"
                       "\"two_work\":%llu,\"two_allocations\":%llu,\"two_memo_hits\":%llu,"
                       "\"two_unate_rejects\":%llu,\"two_unate_merges\":%llu,"
                       "\"two_set_cuts\":%u,\"two_tree_calls\":%llu,\"two_phase_checks\":%llu,"
                       "\"two_phase_rejects\":%llu,\"two_phase_work\":%llu,"
                       "\"two_phase_cache_hits\":%llu,\"two_phase_dominance_hits\":%llu",
                       residual->slack_two_seen, residual->slack_two_unknown, residual->slack_two_feasible,
                       residual->slack_two_pure, residual->slack_two_conditional, residual->slack_two_seconds,
                       residual->two_extension_feasible, residual->two_extension_unknown,
                       residual->two_extension_excluded, static_cast<unsigned long long>(residual->two_work),
                       static_cast<unsigned long long>(residual->two_allocations),
                       static_cast<unsigned long long>(residual->two_memo_hits),
                       static_cast<unsigned long long>(residual->two_unate_rejects),
                       static_cast<unsigned long long>(residual->two_unate_merges), residual->two_set_cuts,
                       static_cast<unsigned long long>(residual->two_tree_calls),
                       static_cast<unsigned long long>(residual->two_phase.checks),
                       static_cast<unsigned long long>(residual->two_phase.rejects),
                       static_cast<unsigned long long>(residual->two_phase.work),
                       static_cast<unsigned long long>(residual->two_phase.cache_hits),
                       static_cast<unsigned long long>(residual->two_phase.dominance_hits));
            if (ex.restriction_cuts) {
                printf(",\"restriction_models\":%u,\"restriction_rejects\":%u,\"restriction_cuts\":%u,\"restriction_literals\":%u,\"restriction_pair_only\":%u,\"restriction_typed\":%u,\"restriction_repeats\":%u,\"restriction_subsumed\":%u,\"restriction_subsumes\":%u,\"restriction_empty\":%u,\"restriction_trace_rows\":%u,\"restriction_trace_residual\":%u,\"restriction_seconds\":%.6f,\"restriction_width\":[",
                       rstats.models, rstats.rejects, rstats.cuts, rstats.literals, rstats.pair_only, rstats.typed, rstats.repeats, rstats.subsumed, rstats.subsumes, rstats.empty, rstats.trace_rows, rstats.trace_residual, rstats.seconds);
                for (size_t w = 0; w < rstats.width.size(); ++w) printf("%s%u", w ? "," : "", rstats.width[w]);
                printf("]");
            }
            if (ex.restriction_counters || ex.complement_inputs)
                printf(",\"counter_restrictions\":%d,\"counter_live\":%d,\"counter_essential\":%d,\"counter_vars\":%d,"
                       "\"counter_clauses\":%d,\"counter_seconds\":%.6f,\"counter_negative_cap\":%d,\"complement_mask\":%u",
                       g_counter.restrictions, g_counter.live, g_counter.essential, g_counter.vars, g_counter.clauses,
                       g_counter.seconds, g_counter.negative_cap, complement_mask);
            if (ex.mixed_rank_min) {
                printf(",\"mixed_cuts\":%d,\"mixed_vars\":%d,\"mixed_clauses\":%d,\"mixed_seconds\":%.6f,\"mixed_floors\":[",
                       g_mixed.cuts, g_mixed.vars, g_mixed.clauses, g_mixed.seconds);
                for (size_t c = 0; c < ex.mixed_cuts.size(); ++c)
                    printf("%s[%d,%d,%u]", c ? "," : "", ex.mixed_cuts[c].floor, ex.mixed_cuts[c].rank, ex.mixed_cuts[c].side);
                printf("]");
            }
            if (ex.restriction_conditional)
                printf(",\"counter_conditional\":%d,\"counter_conditional_clauses\":%d", g_counter.conditional,
                       g_counter.conditional_clauses);
            if (ex.cone_slice)
                printf(",\"cone_slices\":%d,\"cone_on_sat\":%d,\"cone_on_unsat\":%d,\"cone_off_sat\":%d,\"cone_off_unsat\":%d",
                       g_slice.slices, g_slice.on_sat, g_slice.on_unsat, g_slice.off_sat, g_slice.off_unsat);
            if (slack_two && ex.decoder_phase)
                printf(",\"two_decoder\":[%llu,%llu,%llu,%llu,%llu]",
                       static_cast<unsigned long long>(residual->two_decoder.screens),
                       static_cast<unsigned long long>(residual->two_decoder.rejects),
                       static_cast<unsigned long long>(residual->two_decoder.column_rejects),
                       static_cast<unsigned long long>(residual->two_decoder.skipped),
                       static_cast<unsigned long long>(residual->two_decoder.work));
            if (slack_three)
                printf(",\"slack_three_seen\":%d,\"slack_three_unknown\":%d,\"slack_three_feasible\":%d,"
                       "\"slack_three_pure\":%d,\"slack_three_conditional\":%d,\"slack_three_seconds\":%.6f,"
                       "\"three_extension_feasible\":%u,\"three_extension_unknown\":%u,"
                       "\"three_extension_excluded\":%u,\"three_subsumed\":%u,\"three_set_cuts\":%u,"
                       "\"three_tight_calls\":%u,\"three_slack_one_calls\":%u,\"three_slack_two_calls\":%u,"
                       "\"three_work\":%llu,\"three_slack_two_work\":%llu,\"three_tree_calls\":%llu,"
                       "\"three_phase_checks\":%llu,\"three_phase_rejects\":%llu,\"three_phase_work\":%llu,"
                       "\"three_exact_seconds\":%.6f",
                       residual->slack_three_seen, residual->slack_three_unknown, residual->slack_three_feasible,
                       residual->slack_three_pure, residual->slack_three_conditional,
                       residual->slack_three_seconds, residual->three_extension_feasible,
                       residual->three_extension_unknown, residual->three_extension_excluded,
                       residual->three_subsumed, residual->three_set_cuts, residual->three_tight_calls,
                       residual->three_slack_one_calls, residual->three_slack_two_calls,
                       static_cast<unsigned long long>(residual->three_work),
                       static_cast<unsigned long long>(residual->three_slack_two_work),
                       static_cast<unsigned long long>(residual->three_tree_calls),
                       static_cast<unsigned long long>(residual->three_phase.checks),
                       static_cast<unsigned long long>(residual->three_phase.rejects),
                       static_cast<unsigned long long>(residual->three_phase.work), residual->three_exact_seconds);
            if (slack_three && ex.decoder_phase)
                printf(",\"three_decoder\":[%llu,%llu,%llu,%llu,%llu]",
                       static_cast<unsigned long long>(residual->three_decoder.screens),
                       static_cast<unsigned long long>(residual->three_decoder.rejects),
                       static_cast<unsigned long long>(residual->three_decoder.column_rejects),
                       static_cast<unsigned long long>(residual->three_decoder.skipped),
                       static_cast<unsigned long long>(residual->three_decoder.work));
            if (slack_three && ex.slack_three_policy != synthesis::SlackThreePolicy::full)
                printf(",\"three_policy\":%u,\"three_cuts\":%u,\"three_lift\":[%u,%u,%u,%u],"
                       "\"three_threshold_cuts\":%u,\"three_clause_literals\":%llu,\"three_covered\":%u,"
                       "\"three_extension_total\":%llu,\"three_memo_hits\":%u,\"three_memo_inserts\":%u,"
                       "\"three_seed_inserts\":%u,\"three_exact_cached\":%u,\"three_repeats\":%u,"
                       "\"three_memo_size\":%zu",
                       unsigned(ex.slack_three_policy), residual->three_cuts, residual->three_lift[1],
                       residual->three_lift[2], residual->three_lift[3], residual->three_lift[4],
                       residual->three_threshold_cuts,
                       static_cast<unsigned long long>(residual->three_clause_literals), residual->three_covered,
                       static_cast<unsigned long long>(residual->three_extension_total),
                       residual->three_memo_hits, residual->three_memo_inserts, residual->three_seed_inserts,
                       residual->three_exact_cached, residual->three_repeats, three_memo.decided.size());
            else if (slack_three)
                printf(",\"three_cuts\":%u,\"three_extension_total\":%llu,\"three_repeats\":%u",
                       residual->three_cuts, static_cast<unsigned long long>(residual->three_extension_total),
                       residual->three_repeats);
#ifdef USE_SATOKO
            if (satoko_backend) {
                const long propagations = satoko::satoko_stats(satoko_backend->solver)->n_propagations_all;
                printf(",\"decisions\":%ld,\"propagations\":%ld", decisions, propagations - propagations_before);
            }
#endif
            printf("}\n");
            fflush(stdout);
            if (pass == 1) {
                if (st == "SAT") {
                    upper = k;
                    if (skipped.empty()) { final_status = "SAT"; final_reason = "sat"; found = k; break; }
                    pass = 2;  // c keeps the witness at U unless a skipped budget turns out SAT
                    continue;
                }
                if (st == "TIMEOUT" && reason == "witness_cap") { skipped.push_back(k); ++k; continue; }
            }
            if (st == "SAT") { final_status = "SAT"; final_reason = "sat"; found = k; break; }
            if (st == "TIMEOUT") { final_status = "TIMEOUT"; final_reason = reason; break; }
            if (pass != 2) ++k;
        }
        // Every skipped budget below U is UNSAT: U is the minimum.
        if (upper >= 0 && found < 0 && final_status != "TIMEOUT") { final_status = "SAT"; final_reason = "sat"; found = upper; }
    }
    double total = since(t0);
    if (found == 0) final_reason = "sat";
    printf("{\"final\":\"%s\",\"reason\":\"%s\",\"last_k\":%d,\"steps\":%d,\"seconds\":%.6f,"
           "\"target_constraints_seconds\":%.6f,\"distinction_clauses\":%zu", final_status.c_str(),
           final_reason.c_str(), g_current_k, found, total, target_constraints_seconds, layer.clauses.size());
    if (ex.hybrid_witness || ext_size >= 0) printf(",\"upper_bound\":%d", found >= 0 ? found : upper);
    if (ext_size >= 0) printf(",\"external_upper\":%d", ext_size);
    const bool have_chain = found >= 0 || upper >= 0;
    // The external chain is reported when no budget below it was found SAT (proved minimum, or open interval).
    const bool external_chain = ext_size >= 0 && (found < 0 || found == ext_size);
    if (external_chain) {
        printf(",\"aig\":true,\"verified\":true,\"external_chain\":true,\"chain\":[");
        for (size_t j = 0; j < ext_gates.size(); ++j) {
            const int a = ext_gates[j][0], b = ext_gates[j][1];
            const unsigned op = 1u << ((a & 1 ^ 1) | (b & 1 ^ 1) << 1);  // operand index bit 0 = first fanin
            printf("%s[%u,%d,%d]", j ? "," : "", op, a / 2 - 1, b / 2 - 1);
        }
        printf("],\"out\":[%d,%d]", ext_out / 2, ext_out & 1);
    } else if (have_chain && complement_mask) {
        // Map the chain of f(x ^ mask) back to f: complementing an operand that reads a complemented input
        // permutes the operator's truth table (operand 0 = index bit 0, operand 1 = index bit 1). Verified
        // against the given table and care set; operators stay AND-type but need not be normal.
        std::vector<kitty::dynamic_truth_table> val;
        for (int i = 0; i < n; ++i) { val.emplace_back(n); kitty::create_nth_var(val.back(), i); }
        std::vector<std::array<int, 3>> mapped;
        bool and_type = true;
        for (int i = 0; i < c.get_nr_steps(); i++) {
            const auto& s = c.get_step(i);
            unsigned op = 0;
            const auto& o = c.get_operator(i);
            for (int b = 0; b < 4; b++) op |= kitty::get_bit(o, b) << b;
            unsigned flip = (s[0] < n && (complement_mask >> s[0] & 1) ? 1u : 0u) |
                            (s[1] < n && (complement_mask >> s[1] & 1) ? 2u : 0u);
            unsigned op2 = 0;
            for (unsigned j = 0; j < 4; ++j) op2 |= (op >> (j ^ flip) & 1) << j;
            and_type &= std::popcount(op2) == 1 || std::popcount(op2) == 3;
            auto v = kitty::create<kitty::dynamic_truth_table>(n);
            for (unsigned j = 0; j < 4; ++j)
                if (op2 >> j & 1) v |= ((j & 1) ? val[s[0]] : ~val[s[0]]) & ((j >> 1) ? val[s[1]] : ~val[s[1]]);
            val.push_back(v);
            mapped.push_back({int(op2), s[0], s[1]});
        }
        int out = c.get_outputs()[0];
        if ((out >> 1) >= 1 && (out >> 1) <= n && (complement_mask >> ((out >> 1) - 1) & 1)) out ^= 1;  // projection
        auto sim = (out >> 1) == 0 ? kitty::create<kitty::dynamic_truth_table>(n) : val[(out >> 1) - 1];
        if (out & 1) sim = ~sim;
        const bool ok = ((sim ^ tt_given) & ~dc_given) == kitty::create<kitty::dynamic_truth_table>(n);
        printf(",\"aig\":%s,\"verified\":%s,\"complement_mask\":%u,\"chain\":[", and_type ? "true" : "false",
               ok ? "true" : "false", complement_mask);
        for (size_t i = 0; i < mapped.size(); i++)
            printf("%s[%d,%d,%d]", i ? "," : "", mapped[i][0], mapped[i][1], mapped[i][2]);
        printf("],\"out\":[%d,%d]", out >> 1, out & 1);
    } else if (have_chain) {
        auto sim = c.simulate()[0];
        bool ok = dc_hex.empty() ? sim == tt : ((sim ^ tt) & ~dc) == kitty::create<kitty::dynamic_truth_table>(n);
        printf(",\"aig\":%s,\"verified\":%s,\"chain\":[", c.is_aig() ? "true" : "false", ok ? "true" : "false");
        for (int i = 0; i < c.get_nr_steps(); i++) {
            const auto& s = c.get_step(i);
            unsigned op = 0;
            const auto& o = c.get_operator(i);
            for (int b = 0; b < 4; b++) op |= kitty::get_bit(o, b) << b;
            printf("%s[%u,%d,%d]", i ? "," : "", op, s[0], s[1]);
        }
        int out = c.get_outputs()[0];
        printf("],\"out\":[%d,%d]", out >> 1, out & 1);
    }
    printf("}\n");
    return 0;
}

int main(int argc, char** argv) {
    g_run_start = clk::now();
    try {
        return run_main(argc, argv);
    } catch (const std::bad_alloc&) {
        // Memory is never a verdict: the open budget stays unknown.
        printf("\n{\"final\":\"UNKNOWN\",\"reason\":\"memory\",\"last_k\":%d,\"steps\":-1,\"seconds\":%.6f}\n",
               g_current_k, since(g_run_start));
        fflush(stdout);
        return 3;
    }
}
