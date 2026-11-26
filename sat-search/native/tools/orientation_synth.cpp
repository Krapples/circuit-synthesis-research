// Target-directed encoder orientation portfolio on top of the native cofactor constructor (src/orientation_witness.hpp).
// Usage: orientation_synth [options] --stdin       one target per line: N TT [FALLBACK_SPEC]
// Options:
//   --first-cap K   feasible first encoders per (partition, context) (default: 6 for n<=6, 3 for n=7, 2 for n=8)
//   --pair-cap K    decoded pairs per mode per (partition, context) (default 8)
//   --no-reuse      skip the reuse mode (default: reuse only for n <= 6, as in the research replay)
//   --reuse         force the reuse mode for every n
//   --no-native     do not run the native cofactor constructor (n <= 6; Shannon lift over native cofactors for n = 7, 8)
//   --root-slack K  native fallback root slack (default 2; -1 = off)
//   --depth D       native pair-table depth (default 7)
//   --native-partial S  native cofactor constructor (care sets, 3..6 inputs) as partial oracle at sites S
//                   (bitmask: 1 first-encoder bank, 2 second encoder b, 4 decoder; default 0 = off)
//   --min-support-orient  build b only for orientations attaining the orientation-free minimum Y-support
//   --support-project  build each kept b over its own minimum Y-support only (implies --min-support-orient)
//   --cost-aware M  cost-aware second encoders (cost_aware.py Marginal with full-cone reuse): 1 = reference
//                   construction only (mode 0 / mode 1 replace native b and reuse), 2 = portfolio added to the native
//                   modes (default 0 = off); --ca-branch K splits explored per Marginal.solve node (default 2)
//   --reduce        exact standalone partial reductions (zero section / literal peel / signed pair module) before the
//                   partial oracle
//   --reduce-wide   with --reduce, also pass 7..8-input queries to the oracle (used when their core has <= 6 inputs)
//   --exact4        exact <= 4-gate support-projection prepass (src/exact4.hpp) on each nontrivial core before the
//                   native constructor: a hit replaces the oracle call; a proven K >= 5 falls through to the oracle.
//                   With --reduce-wide, 7..8-input cores are also served when the prepass hits
//   --canon         cache oracle cores by incomplete signed-permutation / output-phase normalization
//   --audit         per target, aggregate the feature-quotient audit of every tested first encoder ("audit" key)
// Fallback: the smaller of FALLBACK_SPEC (verified) and the native witness (lifted for n > 6); partial Shannon if
// neither. Every emitted witness is evaluated row by row against the target before it is printed. Native,
// partial-oracle and orientation times are reported separately.
#include <chrono>
#include <climits>
#include <cstdio>
#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <sstream>
#include <tuple>

#include "../src/cofactor_witness.hpp"
#include "../src/exact4.hpp"
#include "../src/orientation_witness.hpp"
#include "../src/partial_reduce.hpp"

using Clock = std::chrono::steady_clock;
static double since(Clock::time_point t) { return std::chrono::duration<double>(Clock::now() - t).count(); }

int main(int argc, char** argv) {
  int first_cap = -1, pair_cap = 8, reuse = -1, root_slack = 2, depth = 7, partial_sites = 0, cost_aware = 0,
      ca_branch = 2;
  bool reduce = false, canon = false, reduce_wide = false, use_exact4 = false;
  bool native = true, from_stdin = false, min_support_orient = false, support_project = false, audit = false;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--first-cap" && i + 1 < argc) first_cap = std::stoi(argv[++i]);
    else if (a == "--pair-cap" && i + 1 < argc) pair_cap = std::stoi(argv[++i]);
    else if (a == "--no-reuse") reuse = 0;
    else if (a == "--reuse") reuse = 1;
    else if (a == "--no-native") native = false;
    else if (a == "--root-slack" && i + 1 < argc) root_slack = std::stoi(argv[++i]);
    else if (a == "--depth" && i + 1 < argc) depth = std::stoi(argv[++i]);
    else if (a == "--native-partial" && i + 1 < argc) partial_sites = std::stoi(argv[++i]);
    else if (a == "--min-support-orient") min_support_orient = true;
    else if (a == "--support-project") support_project = true;
    else if (a == "--audit") audit = true;
    else if (a == "--cost-aware" && i + 1 < argc) cost_aware = std::stoi(argv[++i]);
    else if (a == "--ca-branch" && i + 1 < argc) ca_branch = std::stoi(argv[++i]);
    else if (a == "--reduce") reduce = true;
    else if (a == "--canon") canon = true;
    else if (a == "--exact4") use_exact4 = true;
    else if (a == "--reduce-wide") reduce = reduce_wide = true;
    else if (a == "--stdin") from_stdin = true;
    else { std::cerr << "unknown option " << a << "\n"; return 2; }
  }
  if (!from_stdin) { std::cerr << "usage: orientation_synth [options] --stdin\n"; return 2; }
  try {
    std::unique_ptr<cofactor::PairTable> T;
    auto table = [&]() -> const cofactor::PairTable& {
      if (!T) {
        auto t0 = Clock::now();
        T = std::make_unique<cofactor::PairTable>(depth);
        std::cerr << "pair table depth " << depth << " seconds " << since(t0) << "\n";
      }
      return *T;
    };
    // Partial oracle: optional exact reductions to a core, optional normalized core cache, native constructor on the
    // core (3..6 inputs) or Shannon (<= 2 inputs), lift, and an independent care-set check of the lifted chain.
    std::map<std::tuple<int, orient::TT, orient::TT>, std::optional<orient::Witness>> partial_memo;
    std::map<std::tuple<int, orient::TT, orient::TT>, cofactor::Witness> core_cache;
    std::map<std::tuple<int, orient::TT, orient::TT>, std::optional<exact4::Hit>> e4_cache;
    double partial_seconds = 0, reduce_seconds = 0, e4_seconds = 0;
    long e4_queries = 0, e4_excluded = 0, e4_wide_hits = 0;
    std::array<long, 5> e4_cost{};
    auto exact_core = [&](const orient::TT& q, const orient::TT& d, int m) -> const std::optional<exact4::Hit>& {
      auto ck = std::make_tuple(m, q & d, d);
      auto it = e4_cache.find(ck);
      if (it == e4_cache.end()) {
        auto e0 = Clock::now();
        it = e4_cache.emplace(ck, exact4::solve(q, d, m)).first;
        e4_seconds += since(e0);
        ++e4_queries;
        if (it->second) ++e4_cost[it->second->cost]; else ++e4_excluded;
      }
      return it->second;
    };
    long rq_calls = 0, rq_reduced = 0, rq_removed = 0, rq_trivial = 0, rq_wide = 0, rq_misses = 0, rq_offset = 0;
    std::array<long, 9> rq_in{}, rq_core{};
    auto partial = [&](const orient::TT& p, const orient::TT& c, int k) -> std::optional<orient::Witness> {
      auto key = std::make_tuple(k, p & c, c);
      if (auto it = partial_memo.find(key); it != partial_memo.end()) return it->second;
      auto t0 = Clock::now();
      ++rq_calls;
      ++rq_in[k];
      preduce::Core core;
      if (reduce) {
        auto r0 = Clock::now();
        core = preduce::greedy(p, c, k);
        reduce_seconds += since(r0);
      } else {
        core.n0 = core.n = k; core.p0 = core.p = p & c; core.c0 = core.c = c;
      }
      ++rq_core[core.n];
      if (!core.steps.empty()) { ++rq_reduced; rq_removed += long(core.steps.size()); rq_offset += core.offset(); }
      if (core.trivial()) ++rq_trivial;
      std::optional<orient::Witness> res;
      if (core.n > 6 && !(use_exact4 && exact_core(core.p, core.c, core.n))) {
        ++rq_wide;
      } else {
        if (core.n > 6) ++e4_wide_hits;
        auto solve_core = [&](orient::AIG& aig, const orient::TT& q, const orient::TT& d, const std::vector<int>& vs) {
          int m = int(vs.size());
          if (m < 3 || !(q & d).any() || (q & d) == d) return aig.solve(q, d, vs);
          if (use_exact4) {
            if (const auto& h = exact_core(q, d, m)) {
              std::vector<int> in;
              for (int v : h->vars) in.push_back(vs[v]);
              return aig.import(h->rec->w, in);
            }
          }
          if (canon) {
            preduce::Canon K = preduce::canonical(q, d, m);
            auto ck = std::make_tuple(m, K.q, K.d);
            auto it = core_cache.find(ck);
            if (it == core_cache.end()) {
              ++rq_misses;
              it = core_cache.emplace(ck, cofactor::synthesize(table(), m, K.q.w[0], K.d.w[0], true, 8, root_slack)).first;
            }
            return aig.import(orient::Witness{m, it->second.gates, it->second.output}, preduce::canon_inputs(K, vs)) ^
                   K.phase;
          }
          auto ck = std::make_tuple(m, q & d, d);
          auto it = core_cache.find(ck);
          if (it == core_cache.end()) {
            ++rq_misses;
            it = core_cache.emplace(ck, cofactor::synthesize(table(), m, q.w[0], d.w[0], true, 8, root_slack)).first;
          }
          return aig.import(orient::Witness{m, it->second.gates, it->second.output}, vs);
        };
        orient::AIG aig(k);
        std::vector<int> vs;
        for (int i = 0; i < k; ++i) vs.push_back(aig.lit(i));
        int out = preduce::construct(aig, core, 0, vs, solve_core);
        orient::Witness w = aig.export_cone(out);
        if (((orient::simulate(w) ^ p) & c).any()) throw std::logic_error("lifted partial witness fails on the care set");
        res = w;
      }
      partial_seconds += since(t0);
      partial_memo.emplace(key, res);
      return res;
    };
    std::string line;
    while (std::getline(std::cin, line)) {
      std::istringstream in(line);
      int n;
      std::string tt, spec;
      if (!(in >> n >> tt)) continue;
      in >> spec;
      orient::TT t = orient::parse_hex(tt, n);
      // Fallback candidates.
      orient::Witness fb;
      std::string fb_source;
      double native_seconds = 0;
      int native_size = -1, spec_size = -1;
      if (!spec.empty()) {
        fb = orient::parse_spec(n, spec);
        if (orient::simulate(fb) != t) throw std::runtime_error("supplied fallback spec does not compute the target");
        spec_size = int(fb.gates.size());
        fb_source = "spec";
      }
      if (native && n >= 3) {
        auto base = [&](const orient::TT& f, int k) {
          cofactor::Witness w = cofactor::synthesize(table(), k, f.w[0], cofactor::full_mask(k), true, 8, root_slack);
          return orient::Witness{k, w.gates, w.output};
        };
        auto t0 = Clock::now();
        orient::Witness w;
        if (n <= 6) w = base(t, n);
        else w = orient::Lift<decltype(base)>(6, base)(t, n);  // Shannon lift over native 6-input cofactors
        native_seconds = since(t0);
        native_size = int(w.gates.size());
        if (fb_source.empty() || native_size < spec_size) {
          fb = w;
          fb_source = n <= 6 ? "native" : "native-lift";
        }
      }
      double shannon_seconds = 0;
      if (fb_source.empty()) {
        auto t0 = Clock::now();
        fb = orient::shannon(t, n);
        shannon_seconds = since(t0);
        fb_source = "shannon";
      }
      orient::Options opt;
      opt.first_cap = first_cap > 0 ? first_cap : n <= 6 ? 6 : n == 7 ? 3 : 2;
      opt.pair_cap = pair_cap;
      opt.reuse = reuse < 0 ? n <= 6 : reuse == 1;
      if (partial_sites) {
        opt.partial = partial;
        opt.partial_sites = partial_sites;
        if (reduce_wide) opt.partial_max_k = 8;
      }
      partial_seconds = 0;
      reduce_seconds = 0;
      e4_seconds = 0;
      e4_queries = e4_excluded = e4_wide_hits = 0;
      e4_cost.fill(0);
      rq_calls = rq_reduced = rq_removed = rq_trivial = rq_wide = rq_misses = rq_offset = 0;
      rq_in.fill(0);
      rq_core.fill(0);
      opt.min_support_orient = min_support_orient;
      opt.support_project = support_project;
      opt.cost_aware = cost_aware;
      opt.ca_branch = ca_branch;
      // Audit aggregates: encoders, free status counts, sum s*, sum pair, parity gaps, orientations, kept,
      // min-cost b below s*-1 (must stay 0), marginal below s*-1, support below s* (must stay 0), learned walks.
      long au_n = 0, au_feasible = 0, au_unknown = 0, au_s = 0, au_pair = 0, au_gap = 0, au_or = 0, au_kept = 0,
           au_cost_viol = 0, au_marg_below = 0, au_sup_viol = 0, au_learned = 0, au_bound = 0, au_bcost = 0,
           au_splits = 0, au_rpass = 0, au_runk = 0, au_dec = 0;
      if (audit) opt.audit = [&](const orient::Audit& A) {
        au_splits += A.root_splits; au_rpass += A.root_pass; au_runk += A.root_unknown; au_dec += A.root_pass > 0;
        ++au_n; au_or += A.orientations; au_kept += A.kept; au_learned += long(A.free.learned.size());
        if (A.free.status == fq::Status::unknown) ++au_unknown;
        if (A.free.status != fq::Status::feasible) return;
        ++au_feasible; au_s += A.free.s; au_pair += A.free.pair_s; au_gap += A.free.s > A.free.pair_s;
        int bound = A.free.gate_bound(), best = INT_MAX;
        for (std::size_t i = 0; i < A.b_cost.size(); ++i) {
          best = std::min(best, A.b_cost[i]);
          if (A.b_cost[i] < bound) ++au_cost_viol;
          if (A.b_marginal[i] < bound) ++au_marg_below;
          if (A.b_support[i] < A.free.s) ++au_sup_viol;
        }
        if (best != INT_MAX) { au_bound += bound; au_bcost += best; }
      };
      auto t0 = Clock::now();
      orient::Result r = orient::search(t, n, fb, opt);
      double orient_seconds = since(t0);
      std::cout << "{\"n\":" << n << ",\"tt\":\"" << orient::hex_tt(t, n) << "\",\"fallback_source\":\"" << fb_source
                << "\",\"spec_size\":" << spec_size << ",\"native_size\":" << native_size
                << ",\"native_seconds\":" << native_seconds << ",\"shannon_seconds\":" << shannon_seconds
                << ",\"fallback_size\":" << r.fallback_size << ",\"orient_size\":" << r.orient_size
                << ",\"reuse_size\":" << r.reuse_size << ",\"orient_seconds\":" << orient_seconds
                << ",\"first_cap\":" << opt.first_cap << ",\"pair_cap\":" << opt.pair_cap
                << ",\"reuse\":" << (opt.reuse ? "true" : "false") << ",\"stats\":{\"first\":" << r.stats.first
                << ",\"feasible\":" << r.stats.feasible << ",\"orientations\":" << r.stats.orientations
                << ",\"reuse\":" << r.stats.reuse << ",\"decoded\":" << r.stats.decoded
                << ",\"partial_calls\":" << r.stats.partial_calls << ",\"partial_wins\":" << r.stats.partial_wins
                << ",\"ca_obligations\":" << r.stats.ca_obligations << ",\"ca_skipped\":" << r.stats.ca_skipped
                << ",\"ca_cheap\":[" << r.stats.ca_cheap[0] << "," << r.stats.ca_cheap[1] << "],\"ca_calls\":["
                << r.stats.ca_calls[0] << "," << r.stats.ca_calls[1] << "],\"ca_better\":" << r.stats.ca_better
                << ",\"ca_worse\":" << r.stats.ca_worse << ",\"ca_savings\":" << r.stats.ca_savings
                << "},\"cost_aware\":" << cost_aware << ",\"mode1_size\":" << r.mode1_size << ",\"partial_sites\":" << partial_sites << ",\"partial_seconds\":" << partial_seconds
                << ",\"reduce\":" << (reduce ? "true" : "false") << ",\"canon\":" << (canon ? "true" : "false")
                << ",\"reduce_wide\":" << (reduce_wide ? "true" : "false") << ",\"exact4\":" << (use_exact4 ? "true" : "false")
                << ",\"e4\":{\"queries\":" << e4_queries << ",\"excluded\":" << e4_excluded << ",\"wide_hits\":" << e4_wide_hits
                << ",\"seconds\":" << e4_seconds << ",\"cost\":[" << e4_cost[0] << "," << e4_cost[1] << "," << e4_cost[2] << ","
                << e4_cost[3] << "," << e4_cost[4] << "]}"
                << ",\"oracle\":{\"calls\":" << rq_calls << ",\"misses\":" << rq_misses << ",\"reduced\":" << rq_reduced
                << ",\"removed\":" << rq_removed << ",\"offset\":" << rq_offset << ",\"trivial\":" << rq_trivial
                << ",\"wide\":" << rq_wide << ",\"reduce_seconds\":" << reduce_seconds << ",\"in_width\":[" << [&] {
                     std::string h;
                     for (int i = 0; i <= 8; ++i) h += (i ? "," : "") + std::to_string(rq_in[i]);
                     return h;
                   }() << "],\"core_width\":[" << [&] {
                     std::string h;
                     for (int i = 0; i <= 8; ++i) h += (i ? "," : "") + std::to_string(rq_core[i]);
                     return h;
                   }() << "]}"
                << ",\"min_support_orient\":" << (min_support_orient ? "true" : "false")
                << ",\"support_project\":" << (support_project ? "true" : "false");
      if (audit)
        std::cout << ",\"audit\":{\"encoders\":" << au_n << ",\"feasible\":" << au_feasible << ",\"unknown\":" << au_unknown
                  << ",\"sum_s\":" << au_s << ",\"sum_pair\":" << au_pair << ",\"parity_gap\":" << au_gap
                  << ",\"orientations\":" << au_or << ",\"kept\":" << au_kept << ",\"learned\":" << au_learned
                  << ",\"sum_bound\":" << au_bound << ",\"sum_best_b_cost\":" << au_bcost
                  << ",\"cost_below_bound\":" << au_cost_viol << ",\"marginal_below_bound\":" << au_marg_below
                  << ",\"support_below_s\":" << au_sup_viol << ",\"root_splits\":" << au_splits
                  << ",\"root_pass\":" << au_rpass << ",\"root_unknown\":" << au_runk
                  << ",\"encoders_with_and_split\":" << au_dec << "}";
      std::cout << ",\"win\":\"" << r.win
                << "\",\"verified\":true,\"spec\":\"" << r.reuse.spec() << "\",\"orient_spec\":\"" << r.orient.spec()
                << "\"}\n";
      std::cout.flush();
    }
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << "\n";
    return 1;
  }
  return 0;
}
