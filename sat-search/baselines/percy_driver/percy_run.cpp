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
//   otherwise  : increasing K from --start (default 1) until SAT or --max
// output: one JSON object per line: {"k":K,"status":"SAT|UNSAT|TIMEOUT","seconds":s} per budget, then a final line
//   {"final":..., "steps":K, "seconds":total, "chain":[[op,f0,f1],...], "out":[var,inv], "aig":bool, "verified":bool}
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <memory>
#include <optional>
#include <sstream>
#include <string>
#include <vector>
#include "first_layer.hpp"
#include "tight_residual.hpp"
// Optional extra constraints need the SSV encoder's variable layout (svar_map, nr_svar_map, get_*_var), which Percy
// keeps private; open it for this driver only.
#define private public
#include <percy/percy.hpp>
#undef private

using namespace percy;
using clk = std::chrono::steady_clock;

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
                            bool budget) const {
        const int n = sp.get_nr_in(), k = sp.nr_steps;
        const auto fresh = [&] { return pabc::Abc_Var2Lit(cs.var(), 0); };
        std::vector<std::vector<int>> typed(gates.size()), mixed(n);
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
                        typed[pair * aigs.size() + op].push_back(occurrence);
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
        if (budget) cs.at_most(boundary, k + 1);
        for (uint64_t mask : clauses) {
            std::vector<int> clause;
            for (; mask; mask &= mask - 1) clause.push_back(features[std::countr_zero(mask)]);
            cs.add(std::move(clause));
        }
        return features;
    }
};

// Returns false if the extra constraints make budget k infeasible outright; adds clauses to the solver otherwise.
static bool add_extra(ssv_encoder& enc, const spec& sp, solver_wrapper& solver, const Extra& ex,
                      const FirstLayer& layer, int& extra_clauses, std::vector<int>& layer_features) {
    if (!ex.noreapply_full && ex.cof.empty() && ex.pairs == synthesis::PairScope::none && !ex.first_layer_budget)
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
        layer_features = layer.encode(cs, enc, sp, start, ex.first_layer_budget);
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
    std::vector<int> exclusion(ssv_encoder& enc, const spec& sp, solver_wrapper& solver,
                               std::span<const int> features) {
        if (queries >= 128) return {};
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
        if (2 * h + m != k + 1 || h + m > 6) return {};

        std::vector<int> cut;
        std::vector<uint64_t> columns;
        uint64_t types = 0;
        bool distinct = !features.empty();
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
            if (distinct) {
                const auto op_index = std::find(FirstLayer::aigs.begin(), FirstLayer::aigs.end(), op)
                                      - FirstLayer::aigs.begin();
                const int pair_index = pair[1] * (pair[1] - 1) / 2 + pair[0];
                const uint64_t type = uint64_t{1} << (pair_index * FirstLayer::aigs.size() + op_index);
                distinct = !(types & type);
                types |= type;
            }
            columns.push_back(column);
        }
        for (int i = 0; i < n; ++i)
            if (mixed[i] >= 0) {
                cut.push_back(pabc::Abc_Var2Lit(enc.get_sel_var(mixed[i]), 1));
                columns.push_back(primaries[i]);
            }
        ++queries;
        const auto result = synthesis::tight_residual(columns, h, target, care, 4096);
        if (result == synthesis::ResidualStatus::unknown) ++unknown;
        if (result != synthesis::ResidualStatus::infeasible) return {};
        // Any model retaining these literals retains at least these h gate
        // occurrences and m primaries. Equality and trimming forbid additions.
        ++cuts;
        if (distinct) {
            ++set_cuts;
            cut.clear();
            for (; types; types &= types - 1)
                cut.push_back(features[std::countr_zero(types)] ^ 1);
            for (int i = 0; i < n; ++i)
                if (mixed[i] >= 0) cut.push_back(features[features.size() - n + i] ^ 1);
        }
        return cut;
    }
};

int main(int argc, char** argv) {
    int n = 0, start = 1, budget = -1, maxk = 64, conflicts = 0;
    std::string tt_hex, dc_hex, solver_name = "bsat", method = "std";
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
        else if (a == "--nosym") nosym = true;
        else if (a == "--noreapply-full") ex.noreapply_full = true;
        else if (a == "--first-layer-budget") ex.first_layer_budget = true;
        else if (a == "--tight-residual") ex.tight_residual = true;
        else if (a == "--tight-residual-set-cuts") ex.residual_set_cuts = true;
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
    if (ex.tight_residual && (n < 2 || n > 5 || nosym || method != "cegar" || !dc_hex.empty())) {
        fprintf(stderr, "tight residual exclusions need trimmed CEGAR and a complete 2-5 input table\n");
        return 2;
    }
    if (ex.residual_set_cuts && (!ex.tight_residual || ex.pairs == synthesis::PairScope::none)) {
        fprintf(stderr, "tight residual set cuts need --tight-residual and --first-layer edges or all\n");
        return 2;
    }
    kitty::dynamic_truth_table tt(n), dc(n);
    kitty::create_from_hex_string(tt, tt_hex);
    if (!dc_hex.empty()) kitty::create_from_hex_string(dc, dc_hex);
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
    ssv_encoder enc(*solver);
    chain c;
    const bool cegar = method == "cegar";

    auto t0 = clk::now();
    const FirstLayer layer(tt, dc, ex);
    const double target_constraints_seconds = since(t0);
    sp.preprocess();
    std::string final_status = "UNSAT";
    int found = -1;
    if (sp.nr_triv == sp.get_nr_out()) {        // constant or projection: zero steps
        c.reset(sp.get_nr_in(), sp.get_nr_out(), 0, sp.fanin);
        c.set_output(0, (sp.triv_func(0) << 1) + (sp.out_inv & 1));
        final_status = "SAT"; found = 0;
    } else {
        if (cegar) enc.reset_sim_tts(sp.nr_in);
        int lo = budget >= 0 ? budget : start, hi = budget >= 0 ? budget : maxk;
        for (int k = lo; k <= hi; k++) {
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
            const auto solve = [&] {
                const auto result = solver->solve(sp.conflict_limit);
#ifdef USE_SATOKO
                if (satoko_backend) decisions += satoko::satoko_stats(satoko_backend->solver)->n_decisions;
#endif
                return result;
            };
            std::string st;
            int extra_clauses = 0;
            double encoding_seconds = 0;
            int cegar_rows = 0;
            std::vector<int> layer_features;
            const auto residual_start = clk::now();
            std::optional<TightResidual> residual;
            if (ex.tight_residual) residual.emplace(tt);
            double residual_seconds = residual ? since(residual_start) : 0;
            if (!cegar) {
                const bool encoded = enc.encode(sp) &&
                    add_extra(enc, sp, *solver, ex, layer, extra_clauses, layer_features);
                encoding_seconds = since(tk);
                if (!encoded) st = "UNSAT";
                else {
                    auto r = solve();
                    st = r == success ? "SAT" : r == failure ? "UNSAT" : "TIMEOUT";
                    if (r == success) enc.extract_chain(sp, c);
                }
            } else {
                const bool encoded = enc.cegar_encode(sp) &&
                    add_extra(enc, sp, *solver, ex, layer, extra_clauses, layer_features);
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
                        if (residual) {
                            const auto check_start = clk::now();
                            auto cut = residual->exclusion(enc, sp, *solver,
                                ex.residual_set_cuts ? std::span<const int>(layer_features) : std::span<const int>{});
                            const bool retained = cut.empty() || solver->add_clause(cut.data(), cut.data() + cut.size());
                            residual_seconds += since(check_start);
                            if (!retained) { st = "UNSAT"; break; }
                            if (!cut.empty()) {
                                iMint = 0;
                                continue;
                            }
                        }
                        iMint = enc.simulate(sp);
                        if (iMint == -1) { st = "SAT"; enc.cegar_extract_chain(sp, c); break; }
                    }
                }
            }
            printf("{\"k\":%d,\"status\":\"%s\",\"seconds\":%.6f,\"extra_clauses\":%d,"
                   "\"encoding_seconds\":%.6f,\"cegar_rows\":%d,\"conflicts\":%d,\"vars\":%d,\"clauses\":%d",
                   k, st.c_str(), since(tk), extra_clauses, encoding_seconds, cegar_rows,
                   solver->nr_conflicts() - conflicts_before, solver->nr_vars(), solver->nr_clauses());
            if (residual)
                printf(",\"residual_queries\":%d,\"residual_cuts\":%d,\"residual_set_cuts\":%d,"
                       "\"residual_unknown\":%d,\"residual_seconds\":%.6f",
                       residual->queries, residual->cuts, residual->set_cuts, residual->unknown, residual_seconds);
#ifdef USE_SATOKO
            if (satoko_backend) {
                const long propagations = satoko::satoko_stats(satoko_backend->solver)->n_propagations_all;
                printf(",\"decisions\":%ld,\"propagations\":%ld", decisions, propagations - propagations_before);
            }
#endif
            printf("}\n");
            fflush(stdout);
            if (st == "SAT") { final_status = "SAT"; found = k; break; }
            if (st == "TIMEOUT") { final_status = "TIMEOUT"; break; }
        }
    }
    double total = since(t0);
    printf("{\"final\":\"%s\",\"steps\":%d,\"seconds\":%.6f,\"target_constraints_seconds\":%.6f,"
           "\"distinction_clauses\":%zu", final_status.c_str(), found, total, target_constraints_seconds, layer.clauses.size());
    if (found >= 0) {
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
