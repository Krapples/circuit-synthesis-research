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
#include "../src/orientation_witness.hpp"

using Clock = std::chrono::steady_clock;
static double since(Clock::time_point t) { return std::chrono::duration<double>(Clock::now() - t).count(); }

int main(int argc, char** argv) {
  int first_cap = -1, pair_cap = 8, reuse = -1, root_slack = 2, depth = 7, partial_sites = 0;
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
    std::map<std::tuple<int, cofactor::u64, cofactor::u64>, orient::Witness> partial_memo;
    double partial_seconds = 0;
    auto partial = [&](const orient::TT& p, const orient::TT& c, int k) -> std::optional<orient::Witness> {
      auto key = std::make_tuple(k, p.w[0], c.w[0]);
      if (auto it = partial_memo.find(key); it != partial_memo.end()) return it->second;
      auto t0 = Clock::now();
      cofactor::Witness w = cofactor::synthesize(table(), k, p.w[0], c.w[0], true, 8, root_slack);
      partial_seconds += since(t0);
      orient::Witness out{k, w.gates, w.output};
      partial_memo.emplace(key, out);
      return out;
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
      if (partial_sites) { opt.partial = partial; opt.partial_sites = partial_sites; }
      partial_seconds = 0;
      opt.min_support_orient = min_support_orient;
      opt.support_project = support_project;
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
                << "},\"partial_sites\":" << partial_sites << ",\"partial_seconds\":" << partial_seconds
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
