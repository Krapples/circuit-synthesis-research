// Checks for src/partial_reduce.hpp.
//   preduce_check --exact3   exact standalone AIG minima of all 256 three-input functions by breadth-first search
//       over sets of computed columns (modulo complement); then, for every partial table on 1..3 inputs:
//         * every applicable rule satisfies K(f) == K(g) + offset (K = minimum over all completions);
//         * every completion of the reduced table, lifted row by row, agrees with f on its care set;
//         * the greedy core lifts (Shannon core) to a chain agreeing with f on care;
//         * canonical() round-trips and preserves K.
//   preduce_check --exact4   src/exact4.hpp: library sizes and chains, three-input library costs against exact3, the
//       exact <= 4 decision of every partial table on 1..3 inputs against the exact minimum over completions, lifted
//       witnesses on care, and the handoff regressions.
//   preduce_check --exact4-stdin  lines "N P C"; prints the exact4 decision (cost, support, column) as JSON.
//   preduce_check --stdin    lines "N P C" (hex tables); prints the greedy core and canonical core key as JSON for a
//       differential against the Python reference.
#include <cstdio>
#include <iostream>
#include <sstream>
#include <unordered_set>

#include "../src/exact4.hpp"
#include "../src/partial_reduce.hpp"

using orient::TT;


// Exact minimum AND count of every 3-input function (8-row tables), constants and literals cost 0.
static std::array<int, 256> exact3() {
  std::array<int, 256> best;
  best.fill(-1);
  auto norm = [](int x) { return std::min(x, 255 ^ x); };
  const int in[3] = {0xaa, 0xcc, 0xf0};
  best[0] = best[255] = 0;
  for (int x : in) best[x] = best[255 ^ x] = 0;
  using Key = std::array<unsigned long long, 2>;
  struct H { std::size_t operator()(const Key& k) const { return std::hash<unsigned long long>()(k[0] * 31 + k[1]); } };
  std::vector<Key> level{Key{0, 0}};
  int found = 4;  // classes 0 and the three literals
  for (int L = 1; found < 128 && L <= 12; ++L) {
    std::unordered_set<Key, H> next;
    for (const Key& s : level) {
      std::vector<int> cols{0xaa, 0xcc, 0xf0};
      for (int v = 0; v < 128; ++v) if ((s[v >> 6] >> (v & 63)) & 1) cols.push_back(v);
      for (std::size_t a = 0; a < cols.size(); ++a)
        for (std::size_t b = a + 1; b < cols.size(); ++b)
          for (int sa = 0; sa < 2; ++sa)
            for (int sb = 0; sb < 2; ++sb) {
              int z = norm((cols[a] ^ (sa ? 255 : 0)) & (cols[b] ^ (sb ? 255 : 0)));
              if (z == 0 || z == 0x55 || z == 0x33 || z == 0x0f || ((s[z >> 6] >> (z & 63)) & 1)) continue;
              Key t = s;
              t[z >> 6] |= 1ull << (z & 63);
              if (next.insert(t).second && best[z] < 0) {
                best[z] = best[255 ^ z] = L;
                ++found;
              }
            }
    }
    level.assign(next.begin(), next.end());
    std::fprintf(stderr, "level %d states %zu classes %d\n", L, level.size(), found);
  }
  for (int f = 0; f < 256; ++f) if (best[f] < 0) throw std::logic_error("exact3 incomplete");
  return best;
}

// Embed an n-input table (n <= 3) as an 8-row table independent of the extra inputs.
static int embed(const TT& t, int n) {
  int r = 0;
  for (int row = 0; row < 8; ++row) if (t.get(row & ((1 << n) - 1))) r |= 1 << row;
  return r;
}
static int kpartial(const std::array<int, 256>& K, const TT& p, const TT& c, int n) {
  if (n == 0) return 0;
  int pe = embed(p & c, n), ce = embed(c, n), best = INT_MAX;
  for (int f = 0; f < 256; ++f) if (((f ^ pe) & ce) == 0) best = std::min(best, K[f]);
  return best;
}

static int check3() {
  auto K = exact3();
  long tables = 0, rules[3] = {0, 0, 0}, lifts = 0, greedy_reduced = 0, canon = 0;
  for (int n = 1; n <= 3; ++n) {
    int rows = 1 << n;
    int total = 1;
    for (int r = 0; r < rows; ++r) total *= 3;
    for (int code = 0; code < total; ++code) {
      TT p, c;
      for (int r = 0, x = code; r < rows; ++r, x /= 3) {
        if (x % 3) c.set(r);
        if (x % 3 == 2) p.set(r);
      }
      ++tables;
      int kf = kpartial(K, p, c, n);
      for (const auto& rule : preduce::reductions(p, c, n)) {
        ++rules[rule.kind];
        int kg = kpartial(K, rule.p, rule.c, n - 1);
        if (kf != kg + rule.cost) throw std::logic_error("offset identity fails");
        // Every completion h of the reduced table lifts to a function agreeing with f on care.
        int m = n - 1, rm = 1 << m;
        for (int h = 0; h < (1 << rm); ++h) {
          bool ok = true;
          for (int r = 0; r < rm; ++r) if (rule.c.get(r) && (((h >> r) & 1) != int(rule.p.get(r)))) ok = false;
          if (!ok) continue;
          for (int row = 0; row < rows; ++row) {
            if (!c.get(row)) continue;
            int bit = (row >> rule.i) & 1;
            int r = (row & ((1 << rule.i) - 1)) | ((row >> (rule.i + 1)) << rule.i);
            int val;
            if (rule.kind == preduce::kZero) val = (h >> r) & 1;
            else if (rule.kind == preduce::kPeel) val = bit == rule.neutral ? (h >> r) & 1 : rule.v;
            else {
              if (bit != rule.neutral) r = (r & ~(1 << rule.j)) | (rule.v << rule.j);
              val = (h >> r) & 1;
            }
            if (val != int(p.get(row))) throw std::logic_error("lift disagrees on care");
            ++lifts;
          }
        }
      }
      preduce::Core core = preduce::greedy(p, c, n);
      if (!core.steps.empty()) ++greedy_reduced;
      if (kpartial(K, core.p, core.c, core.n) + core.offset() != kf) throw std::logic_error("greedy offset fails");
      orient::AIG aig(n);
      std::vector<int> vs;
      for (int i = 0; i < n; ++i) vs.push_back(aig.lit(i));
      int out = preduce::construct(aig, core, 0, vs, [](orient::AIG& a, const TT& q, const TT& d,
                                                        const std::vector<int>& v) { return a.solve(q, d, v); });
      if (((orient::simulate(aig.export_cone(out)) ^ p) & c).any()) throw std::logic_error("greedy lift fails");
      preduce::Canon C = preduce::canonical(p, c, n);
      auto [ip, ic] = preduce::inverse(C.q, C.d, n, C);
      if (!(ip == (p & c) && ic == c)) throw std::logic_error("canonical round trip fails");
      if (kpartial(K, C.q, C.d, n) != kf) throw std::logic_error("canonical changes K");
      ++canon;
    }
  }
  int maxk = 0;
  for (int f = 0; f < 256; ++f) maxk = std::max(maxk, K[f]);
  std::printf("{\"tables\":%ld,\"zero\":%ld,\"peel\":%ld,\"module\":%ld,\"lift_rows\":%ld,\"greedy_reduced\":%ld,"
              "\"canonical\":%ld,\"max_k3\":%d,\"ok\":true}\n",
              tables, rules[preduce::kZero], rules[preduce::kPeel], rules[preduce::kModule], lifts, greedy_reduced,
              canon, maxk);
  return 0;
}

// Import an exact4 hit over n inputs and check it on the care set.
static bool hit_ok(const exact4::Hit& h, const TT& p, const TT& c, int n) {
  orient::AIG aig(n);
  std::vector<int> in;
  for (int v : h.vars) in.push_back(aig.lit(v));
  int out = aig.import(h.rec->w, in);
  return !((orient::simulate(aig.export_cone(out)) ^ p) & c).any();
}

static TT from_u32(exact4::u32 x) { TT t; t.w[0] = x; return t; }

static int check4() {
  auto K = exact3();
  long recs = 0;
  std::array<std::size_t, 6> sizes{};
  for (int w = 1; w <= 5; ++w) {
    const auto& idx = exact4::library(w);
    sizes[w] = idx.rec.size();
    for (const auto& r : idx.rec) {
      TT s = orient::simulate(r.w);
      if (s.w[0] != r.t || int(r.w.gates.size()) != r.cost || (w == 5 && r.cost != 4))
        throw std::logic_error("library record chain mismatch");
      ++recs;
    }
  }
  if (sizes[4] != 3590 || sizes[5] != 15104) throw std::logic_error("library sizes differ from the reference");
  // Three-input library against the breadth-first minima.
  {
    const auto& idx = exact4::library(3);
    std::array<int, 256> L;
    L.fill(-1);
    for (const auto& r : idx.rec) L[r.t] = r.cost;
    for (int f = 0; f < 256; ++f)
      if ((K[f] <= 4 ? L[f] != K[f] : L[f] != -1)) throw std::logic_error("three-input library disagrees with exact3");
  }
  long tables = 0, hits = 0, excl = 0;
  for (int n = 1; n <= 3; ++n) {
    int rows = 1 << n, total = 1;
    for (int r = 0; r < rows; ++r) total *= 3;
    for (int code = 0; code < total; ++code) {
      TT p, c;
      for (int r = 0, x = code; r < rows; ++r, x /= 3) {
        if (x % 3) c.set(r);
        if (x % 3 == 2) p.set(r);
      }
      ++tables;
      int kf = kpartial(K, p, c, n);
      auto h = exact4::solve(p, c, n);
      if (kf <= 4) {
        if (!h || h->cost != kf) throw std::logic_error("exact4 misses a <= 4 table");
        if (!hit_ok(*h, p, c, n)) throw std::logic_error("exact4 witness fails on care");
        ++hits;
      } else {
        if (h) throw std::logic_error("exact4 hit above the exact minimum");
        ++excl;
      }
    }
  }
  // Handoff regressions.
  auto col = [](int n, int i) { return orient::col_tt(n, i); };
  if (exact4::solve(from_u32(0x18), from_u32(0x1e), 3)->cost != 2) throw std::logic_error("regression 0x18/0x1e");
  if (exact4::solve(from_u32(9), from_u32(15), 2)->cost != 3) throw std::logic_error("regression xnor");
  if (exact4::solve(col(6, 0) ^ col(6, 1) ^ col(6, 2), orient::full_tt(6), 6)) throw std::logic_error("regression xor3");
  if (exact4::project(from_u32(0x18), from_u32(0x1e), 3, {0, 2}) || exact4::project(from_u32(0x18), from_u32(0x1e), 3, {1, 2}))
    throw std::logic_error("regression projection collision");
  auto pr = exact4::project(from_u32(0x18), from_u32(0x1e), 3, {0, 1});
  if (!pr || pr->first != 9 || pr->second != 15) throw std::logic_error("regression projection");
  std::printf("{\"records\":%ld,\"lib\":[%zu,%zu,%zu,%zu,%zu],\"tables\":%ld,\"hits\":%ld,\"excluded\":%ld,\"ok\":true}\n",
              recs, sizes[1], sizes[2], sizes[3], sizes[4], sizes[5], tables, hits, excl);
  return 0;
}

static const char* kind_name(preduce::Kind k) { return k == preduce::kZero ? "zero" : k == preduce::kPeel ? "peel" : "module"; }

int main(int argc, char** argv) {
  try {
    std::string mode = argc > 1 ? argv[1] : "";
    if (mode == "--exact3") return check3();
    if (mode == "--exact4") return check4();
    if (mode == "--exact4-stdin") {
      std::string line;
      while (std::getline(std::cin, line)) {
        std::istringstream in(line);
        int n;
        std::string ph, ch;
        if (!(in >> n >> ph >> ch)) continue;
        TT p = orient::parse_hex(ph, n), c = orient::parse_hex(ch, n);
        auto h = exact4::solve(p, c, n);
        if (!h) { std::printf("null\n"); continue; }
        std::string vs;
        for (int v : h->vars) vs += (vs.empty() ? "" : ",") + std::to_string(v);
        std::printf("{\"cost\":%d,\"vars\":[%s],\"t\":%u,\"ok\":%s}\n", h->cost, vs.c_str(), h->rec->t,
                    hit_ok(*h, p, c, n) ? "true" : "false");
      }
      return 0;
    }
    if (mode != "--stdin") { std::cerr << "usage: preduce_check --exact3 | --exact4 | --exact4-stdin | --stdin\n"; return 2; }
    std::string line;
    while (std::getline(std::cin, line)) {
      std::istringstream in(line);
      int n;
      std::string ph, ch;
      if (!(in >> n >> ph >> ch)) continue;
      TT p = orient::parse_hex(ph, n), c = orient::parse_hex(ch, n);
      preduce::Core core = preduce::greedy(p, c, n);
      // Lift a Shannon core and check it on the original care set.
      orient::AIG aig(n);
      std::vector<int> vs;
      for (int i = 0; i < n; ++i) vs.push_back(aig.lit(i));
      int out = preduce::construct(aig, core, 0, vs, [](orient::AIG& a, const TT& q, const TT& d,
                                                        const std::vector<int>& v) { return a.solve(q, d, v); });
      bool lift_ok = !((orient::simulate(aig.export_cone(out)) ^ p) & c).any();
      std::string steps;
      for (auto& r : core.steps) {
        steps += (steps.empty() ? "" : ",") + std::string("[\"") + kind_name(r.kind) + "\"," + std::to_string(r.i) + "]";
      }
      std::printf("{\"n\":%d,\"core_n\":%d,\"core_p\":\"%s\",\"core_c\":\"%s\",\"offset\":%d,\"steps\":[%s],\"lift_ok\":%s",
                  n, core.n, orient::hex_tt(core.p, std::max(core.n, 0)).c_str(),
                  orient::hex_tt(core.c, std::max(core.n, 0)).c_str(), core.offset(), steps.c_str(),
                  lift_ok ? "true" : "false");
      if (core.n > 0 && !core.trivial()) {
        preduce::Canon C = preduce::canonical(core.p, core.c, core.n);
        auto [ip, ic] = preduce::inverse(C.q, C.d, core.n, C);
        std::printf(",\"canon_q\":\"%s\",\"canon_d\":\"%s\",\"canon_rt\":%s", orient::hex_tt(C.q, core.n).c_str(),
                    orient::hex_tt(C.d, core.n).c_str(), (ip == (core.p & core.c) && ic == core.c) ? "true" : "false");
      }
      std::printf("}\n");
    }
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << "\n";
    return 1;
  }
  return 0;
}
