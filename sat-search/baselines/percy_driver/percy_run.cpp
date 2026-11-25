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
#include <percy/percy.hpp>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <string>

using namespace percy;
using clk = std::chrono::steady_clock;

static double since(clk::time_point t0) {
    return std::chrono::duration<double>(clk::now() - t0).count();
}

int main(int argc, char** argv) {
    int n = 0, start = 1, budget = -1, maxk = 64, conflicts = 0;
    std::string tt_hex, dc_hex, solver_name = "bsat", method = "std";
    bool nosym = false;
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
            if (!cegar) {
                if (!enc.encode(sp)) st = "UNSAT";
                else {
                    auto r = solver->solve(sp.conflict_limit);
                    st = r == success ? "SAT" : r == failure ? "UNSAT" : "TIMEOUT";
                    if (r == success) enc.extract_chain(sp, c);
                }
            } else {
                if (!enc.cegar_encode(sp)) st = "UNSAT";
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
            printf("{\"k\":%d,\"status\":\"%s\",\"seconds\":%.6f}\n", k, st.c_str(), since(tk));
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
