// Checks for src/feature_quotient.hpp.
//   fq_check --brute SEED COUNT   random small instances (self-loops, duplicate rows, empty edge sets included)
//       against brute force: support feasibility by enumerating every labelling of the Z-signature classes,
//       s* by enumerating every support, learned masks replayed and hit by every brute-feasible support, and the
//       root-partition screen against every pair of operand functions a(A-signature), c(B-signature).
//   fq_check --stdin               lines "M R r_1..r_R E u_1 v_1 .. u_E v_E"; prints one JSON record per line with
//       status, s, pair_s, calls, learned and whether every learned walk replays.
#include <cstdio>
#include <iostream>
#include <random>
#include <sstream>
#include <string>

#include "../src/feature_quotient.hpp"

using fq::u64;

// Brute force: a support Z works iff some labelling of the distinct Z-signatures separates every conflict edge.
static bool brute_feasible(const std::vector<u64>& rows, const std::vector<fq::Edge>& edges, u64 z) {
  std::map<u64, int> id;
  std::vector<int> cls(rows.size());
  for (std::size_t u = 0; u < rows.size(); ++u) cls[u] = id.emplace(rows[u] & z, int(id.size())).first->second;
  const int k = int(id.size());
  for (u64 lab = 0; lab < (u64(1) << k); ++lab) {
    bool ok = true;
    for (auto [u, v] : edges)
      if (((lab >> cls[u]) & 1) == ((lab >> cls[v]) & 1)) { ok = false; break; }
    if (ok) return true;
  }
  return false;
}

// Brute force root screen: some a over A-signatures and c over B-signatures make a AND c separate every edge.
static bool brute_root(const std::vector<u64>& rows, const std::vector<fq::Edge>& edges, u64 A, u64 B) {
  std::map<u64, int> ia, ib;
  std::vector<int> ca(rows.size()), cb(rows.size());
  for (std::size_t u = 0; u < rows.size(); ++u) {
    ca[u] = ia.emplace(rows[u] & A, int(ia.size())).first->second;
    cb[u] = ib.emplace(rows[u] & B, int(ib.size())).first->second;
  }
  for (u64 a = 0; a < (u64(1) << ia.size()); ++a)
    for (u64 c = 0; c < (u64(1) << ib.size()); ++c) {
      bool ok = true;
      for (auto [u, v] : edges) {
        int x = int((a >> ca[u]) & (c >> cb[u]) & 1), y = int((a >> ca[v]) & (c >> cb[v]) & 1);
        if (x == y) { ok = false; break; }
      }
      if (ok) return true;
    }
  return false;
}

static int brute(unsigned seed, int count) {
  std::mt19937_64 rng(seed);
  long checks = 0, learned = 0, root_checks = 0, root_pass = 0, root_unknown = 0, gaps = 0;
  long by_status[4] = {0, 0, 0, 0};
  for (int it = 0; it < count; ++it) {
    int m = 1 + int(rng() % 5), R = 1 + int(rng() % 8), E = int(rng() % 9);
    std::vector<u64> rows(R);
    for (auto& r : rows) r = rng() & ((u64(1) << m) - 1);
    std::vector<fq::Edge> edges;
    for (int e = 0; e < E; ++e) edges.push_back({int(rng() % R), int(rng() % R)});  // self-loops allowed
    fq::Support s = fq::min_support(rows, edges);
    ++by_status[int(s.status)];
    int best = -1;
    u64 full = (u64(1) << m) - 1;
    for (u64 z = 0; z <= full; ++z) {
      bool f = brute_feasible(rows, edges, z);
      if (f != fq::quotient_bipartite(rows, edges, z) && !edges.empty()) throw std::logic_error("quotient test differs");
      if (f != !fq::certificate(rows, edges, z).has_value()) throw std::logic_error("certificate differs");
      if (f && (best < 0 || std::popcount(z) < best)) best = std::popcount(z);
      if (f) for (auto& ob : s.learned) if (!(ob.mask & z)) throw std::logic_error("learned mask not necessary");
      ++checks;
    }
    for (auto& ob : s.learned) if (!fq::replay(rows, edges, ob)) throw std::logic_error("walk does not replay");
    learned += long(s.learned.size());
    if (edges.empty()) {
      if (s.status != fq::Status::constant) throw std::logic_error("empty edges not constant");
    } else if (best < 0) {
      if (s.status != fq::Status::impossible) throw std::logic_error("impossible not reported");
    } else {
      if (s.status != fq::Status::feasible || s.s != best) throw std::logic_error("s* differs");
      if (!brute_feasible(rows, edges, s.support)) throw std::logic_error("support infeasible");
      if (s.pair_s > s.s) throw std::logic_error("pair bound above s*");
      if (s.pair_s < s.s) ++gaps;
    }
    // Root-partition screen on random source groups (overlapping allowed).
    fq::Partition P = fq::components(R, edges);
    for (int t = 0; t < 4; ++t) {
      u64 A = rng() & full, B = rng() & full;
      fq::Screen sc = fq::root_partition(rows, P, A, B);
      ++root_checks;
      if (sc == fq::Screen::unknown) { ++root_unknown; continue; }
      bool b = brute_root(rows, edges, A, B);
      if (b != (sc == fq::Screen::pass)) throw std::logic_error("root screen differs");
      root_pass += b;
    }
  }
  std::printf("{\"instances\":%d,\"support_checks\":%ld,\"constant\":%ld,\"feasible\":%ld,\"impossible\":%ld,"
              "\"unknown\":%ld,\"learned\":%ld,\"parity_gap_instances\":%ld,\"root_checks\":%ld,\"root_pass\":%ld,"
              "\"root_unknown\":%ld,\"ok\":true}\n",
              count, checks, by_status[0], by_status[1], by_status[2], by_status[3], learned, gaps, root_checks,
              root_pass, root_unknown);
  return 0;
}

int main(int argc, char** argv) {
  try {
    std::string mode = argc > 1 ? argv[1] : "";
    if (mode == "--brute" && argc > 3) return brute(unsigned(std::stoul(argv[2])), std::stoi(argv[3]));
    if (mode != "--stdin") { std::cerr << "usage: fq_check --brute SEED COUNT | --stdin\n"; return 2; }
    std::string line;
    while (std::getline(std::cin, line)) {
      std::istringstream in(line);
      int m, R, E;
      if (!(in >> m >> R)) continue;
      std::vector<u64> rows(R);
      for (auto& r : rows) in >> r;
      in >> E;
      std::vector<fq::Edge> edges(E);
      for (auto& [u, v] : edges) in >> u >> v;
      fq::Support s = fq::min_support(rows, edges);
      bool replays = true;
      for (auto& ob : s.learned) replays = replays && fq::replay(rows, edges, ob);
      std::printf("{\"status\":\"%s\",\"s\":%d,\"pair_s\":%d,\"calls\":%d,\"learned\":%zu,\"replay\":%s,"
                  "\"gate_bound\":%d,\"support\":%llu}\n",
                  fq::name(s.status), s.s, s.pair_s, s.calls, s.learned.size(), replays ? "true" : "false",
                  s.gate_bound(), (unsigned long long)s.support);
    }
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << "\n";
    return 1;
  }
  return 0;
}
