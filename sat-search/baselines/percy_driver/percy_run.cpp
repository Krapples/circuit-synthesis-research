// Command-line driver for Percy exact synthesis restricted to AIGs (spec.set_primitive(AIG), SSV encoder).
// Reproduces percy::std_synthesize / std_cegar_synthesize one budget at a time so that every budget's SAT/UNSAT
// time is reported, and prints the witness chain for independent verification by the harness.
//
// usage: percy_run --n N --tt HEX [--dc HEX] [--solver bsat|satoko|bmcg] [--method std|cegar]
//                  [--start K] [--budget K] [--max K] [--conflicts C] [--nosym]
//   --tt   truth table, hex, most significant nibble first (kitty::create_from_hex_string convention)
//   --dc   don't-care mask, same format (1 = don't care)
//   --budget K : decide only "exactly K steps" (Percy's fixed-step semantics, all steps used)
//   otherwise  : increasing K from --start (default 1) until SAT or --max
// output: one JSON object per line: {"k":K,"status":"SAT|UNSAT|TIMEOUT","seconds":s} per budget, then a final line
//   {"final":..., "steps":K, "seconds":total, "chain":[[op,f0,f1],...], "out":[var,inv], "aig":bool, "verified":bool}
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <memory>
#include <sstream>
#include <string>
#include <vector>
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
        if (K <= 0) { for (int l : x) G({l ^ 1}); return; }
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

// Returns false if the extra constraints make budget k infeasible outright; adds clauses to the solver otherwise.
static bool add_extra(ssv_encoder& enc, const spec& sp, solver_wrapper& solver, const Extra& ex, int& extra_clauses) {
    if (!ex.noreapply_full && ex.cof.empty()) return true;
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
    solver.set_nr_vars(cs.next);
    for (auto& cl : cs.clauses) {
        std::vector<pabc::lit> lits(cl.begin(), cl.end());
        if (!solver.add_clause(lits.data(), lits.data() + lits.size())) return false;
    }
    extra_clauses = (int)cs.clauses.size();
    return true;
}

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
    kitty::dynamic_truth_table tt(n), dc(n);
    kitty::create_from_hex_string(tt, tt_hex);
    if (!dc_hex.empty()) kitty::create_from_hex_string(dc, dc_hex);

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
            std::string st;
            int extra_clauses = 0;
            if (!cegar) {
                if (!enc.encode(sp) || !add_extra(enc, sp, *solver, ex, extra_clauses)) st = "UNSAT";
                else {
                    auto r = solver->solve(sp.conflict_limit);
                    st = r == success ? "SAT" : r == failure ? "UNSAT" : "TIMEOUT";
                    if (r == success) enc.extract_chain(sp, c);
                }
            } else {
                if (!enc.cegar_encode(sp) || !add_extra(enc, sp, *solver, ex, extra_clauses)) st = "UNSAT";
                else {
                    int iMint = 1; st = "UNSAT";
                    while (true) {
                        if (!enc.create_tt_clauses(sp, iMint - 1)) { st = "UNSAT"; break; }
                        auto r = solver->solve(sp.conflict_limit);
                        if (r == failure) { st = "UNSAT"; break; }
                        if (r != success) { st = "TIMEOUT"; break; }
                        iMint = enc.simulate(sp);
                        if (iMint == -1) { st = "SAT"; enc.cegar_extract_chain(sp, c); break; }
                    }
                }
            }
            printf("{\"k\":%d,\"status\":\"%s\",\"seconds\":%.6f,\"extra_clauses\":%d}\n", k, st.c_str(), since(tk), extra_clauses);
            fflush(stdout);
            if (st == "SAT") { final_status = "SAT"; found = k; break; }
            if (st == "TIMEOUT") { final_status = "TIMEOUT"; break; }
        }
    }
    double total = since(t0);
    printf("{\"final\":\"%s\",\"steps\":%d,\"seconds\":%.6f", final_status.c_str(), found, total);
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
