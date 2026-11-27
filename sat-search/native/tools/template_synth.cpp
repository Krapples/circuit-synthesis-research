// Exact AND/OR(/NOT) synthesis on a list of cared rows, for pequalnp desk template units
// (RepSizeAtMost rectangles and two-lit FanInTwo / Monotone2 steps). CaDiCaL 2.2 (ABC's copy).
//
// Input, one unit per line on stdin:
//   ID N GENERAL START BUDGET ROWS
//   N        number of input wires (0..N-1)
//   GENERAL  1 = gates AND, OR, NOT (NOT counted); 0 = monotone AND/OR
//   START    first gate count to try (a proven floor, or 1)
//   BUDGET   largest gate count to try
//   ROWS     comma list of row:target, row a hex input mask (bit i = wire i), target 0/1
// Output, one JSON line per unit:
//   {"id":..,"status":"SAT|UNSAT|TIMEOUT|TRIVIAL","k":K,"gates":[[op,a,b],...],"out":W,"seconds":s,"ks":[...]}
//   op 0 = AND, 1 = OR, 2 = NOT (b = a); gate j writes wire N + j. UNSAT: no circuit of at most BUDGET gates
//   (every k from START to BUDGET refuted); k sizes are tried upward, so a SAT k is the least k >= START.
//
// Model for exactly k gates; each restriction below holds for some minimum-size circuit, so the
// refutation of every k in [START, BUDGET] in increasing order is sound:
//   * each gate is AND/OR of two different earlier wires, or (GENERAL) NOT of one earlier wire;
//   * the output is the last gate (a minimum circuit is its output cone, whose only sink is the output);
//   --no-used:     otherwise every non-output gate is read by a later gate (cone-only circuits);
//   --no-distinct: otherwise every gate differs on the cared rows from every earlier wire and from both
//                  constants (an equal gate can be replaced by that wire; a constant non-output gate can be
//                  eliminated with its reader);
//   --no-colex:    otherwise for adjacent gates g, g+1 below the output with g+1 not reading g, the choice key
//                  (b, a, op) of g is colex-smaller than that of g+1 (the lexicographically least topological
//                  order with the output fixed last satisfies it; keys of distinct gates differ).
// Every SAT model is decoded and re-simulated on all rows before it is printed.
//
// Options: --threads T (units in parallel, default 11), --seconds S (wall cap per unit, default 60),
//          --probe P (seconds on a whole size before splitting it into gate-0 cubes on the shared pool;
//          default 10, 0 = never split),
//          --no-used --no-distinct --no-colex --no-essential (ablations; all four = plain control encoding).
//   --no-essential: otherwise every input that any correct circuit must read (essential_input) is read.
//   --no-slots:     otherwise (with used and essential) at most k + 1 - E extra reads (read-slot count).
//   --split-reads:  after the probe, split a size on S = the exact set of wires with an extra read (all
//                   |S| <= k + 1 - E) instead of on gate 0; wires outside S get exactly their one read.
//   --congruence:   re-enable CaDiCaL congruence closure (off: it crashes on some cube formulas).
//   --dump DIR:     write each whole-size CNF (DIR/<id>_k<k>.cnf) and report UNSAT without solving.
//   --solve-cnf F:  solve one DIMACS file with this build (respects --seconds, --congruence); prints JSON.
#include <algorithm>
#include <atomic>
#include <condition_variable>
#include <deque>
#include <functional>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

#include "cadical.hpp"

#ifdef _WIN32
#define NOMINMAX
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <dbghelp.h>
#pragma comment(lib, "dbghelp.lib")
// Print a symbolized stack on a crash (needs the .pdb beside the exe for names).
static LONG WINAPI crash_trace(EXCEPTION_POINTERS* e) {
  static std::mutex mu;
  std::lock_guard<std::mutex> lk(mu);
  HANDLE p = GetCurrentProcess();
  SymSetOptions(SYMOPT_LOAD_LINES | SYMOPT_UNDNAME);
  SymInitialize(p, nullptr, TRUE);
  std::fprintf(stderr, "crash: code 0x%08lx at %p thread %lu\n", e->ExceptionRecord->ExceptionCode,
               e->ExceptionRecord->ExceptionAddress, GetCurrentThreadId());
  CONTEXT c = *e->ContextRecord;
  STACKFRAME64 f{};
  f.AddrPC.Offset = c.Rip; f.AddrPC.Mode = AddrModeFlat;
  f.AddrFrame.Offset = c.Rbp; f.AddrFrame.Mode = AddrModeFlat;
  f.AddrStack.Offset = c.Rsp; f.AddrStack.Mode = AddrModeFlat;
  for (int i = 0; i < 40 && StackWalk64(IMAGE_FILE_MACHINE_AMD64, p, GetCurrentThread(), &f, &c, nullptr,
                                        SymFunctionTableAccess64, SymGetModuleBase64, nullptr); ++i) {
    char buf[sizeof(SYMBOL_INFO) + 256]{};
    auto* sym = (SYMBOL_INFO*)buf; sym->SizeOfStruct = sizeof(SYMBOL_INFO); sym->MaxNameLen = 255;
    DWORD64 d = 0; IMAGEHLP_LINE64 ln{}; ln.SizeOfStruct = sizeof(ln); DWORD dl = 0;
    bool hs = SymFromAddr(p, f.AddrPC.Offset, &d, sym);
    bool hl = SymGetLineFromAddr64(p, f.AddrPC.Offset, &dl, &ln);
    std::fprintf(stderr, "  #%d %s %s:%lu\n", i, hs ? sym->Name : "?", hl ? ln.FileName : "?", hl ? ln.LineNumber : 0);
  }
  std::fflush(stderr);
  return EXCEPTION_CONTINUE_SEARCH;
}
#endif

using Clock = std::chrono::steady_clock;

static bool g_used = true, g_distinct = true, g_colex = true, g_essential = true, g_slots = true;
static double g_seconds = 60.0;

struct Unit {
  std::string id;
  int n = 0, general = 0, start = 1, budget = 0;
  std::vector<unsigned long long> rows;
  std::vector<int> target;
};

struct Choice { int op, a, b; };  // NOT: b == a

struct Deadline : CaDiCaL::Terminator {
  Clock::time_point end;
  const std::atomic<bool>* stop = nullptr;
  bool terminate() override { return (stop && stop->load()) || Clock::now() >= end; }
};

// Shared queue of cube tasks: any idle worker (and a unit waiting on its own cubes) runs them.
static std::mutex g_qmu;
static std::condition_variable g_qcv;
static std::deque<std::function<void()>> g_cubes;
static bool g_congruence = false;
static std::string g_dump;      // --dump DIR: write each whole-size CNF as DIR/<id>_k<k>.cnf instead of solving
static double g_probe = 10.0;   // seconds on the whole size before splitting it into gate-0 cubes (0 = never)
static bool g_split_reads = false;  // --split-reads: split on the set of multiply-read wires instead of gate 0

static bool run_one_cube(bool wait) {
  std::function<void()> f;
  {
    std::unique_lock<std::mutex> lk(g_qmu);
    if (g_cubes.empty()) {
      if (!wait) return false;
      g_qcv.wait_for(lk, std::chrono::milliseconds(5));
      if (g_cubes.empty()) return false;
    }
    f = std::move(g_cubes.front());
    g_cubes.pop_front();
  }
  f();
  return true;
}

static int simulate(const Unit& u, const std::vector<Choice>& gates, int out, unsigned long long row) {
  std::vector<int> w(u.n + gates.size());
  for (int i = 0; i < u.n; ++i) w[i] = (row >> i) & 1;
  for (size_t j = 0; j < gates.size(); ++j) {
    const Choice& c = gates[j];
    w[u.n + j] = c.op == 0 ? (w[c.a] & w[c.b]) : c.op == 1 ? (w[c.a] | w[c.b]) : !w[c.a];
  }
  return w[out];
}

// Input w must be read by every circuit that is right on the cared rows (so by some gate):
//  * two rows differing only in bit w have different targets (any basis), or
//  * (monotone) rows r1, r2 with target(r1) = 1, target(r2) = 0 and (r1 without w) <= r2 bitwise: an
//    unread w gives C(r1) = C(r1 without w) <= C(r2) by monotonicity, a contradiction.
static bool essential_input(const Unit& u, int w) {
  const unsigned long long bit = 1ull << w;
  for (size_t a = 0; a < u.rows.size(); ++a)
    for (size_t b = 0; b < u.rows.size(); ++b) {
      if (u.target[a] != 1 || u.target[b] != 0) continue;
      if ((u.rows[a] ^ u.rows[b]) == bit) return true;
      if (!u.general && ((u.rows[a] & ~bit) & ~u.rows[b]) == 0) return true;
    }
  return false;
}

// Returns 10 SAT (gates filled), 20 UNSAT, 0 timeout.
static int solve_k(const Unit& u, int k, const Clock::time_point& end, std::vector<Choice>& gates,
                   int cube = -1, const std::atomic<bool>* stop = nullptr,
                   const std::vector<int>* multi = nullptr) {
  if ((stop && stop->load()) || Clock::now() >= end) return 0;
  const int n = u.n, R = (int)u.rows.size(), W = n + k;
  CaDiCaL::Solver s;
  // CaDiCaL 2.2's congruence closure segfaults on some cube formulas (Closure::find_gate_lits,
  // cadical_congruence.cpp:2906, seen on rect46 k=9 cubes); off unless --congruence.
  if (!g_congruence) s.set("congruence", 0);
  int nv = 0;
  auto fresh = [&] { return ++nv; };
  auto cl = [&](std::initializer_list<int> lits) { for (int l : lits) s.add(l); s.add(0); };
  std::vector<std::vector<int>> v(W, std::vector<int>(R));
  for (int w = 0; w < W; ++w)
    for (int r = 0; r < R; ++r) v[w][r] = fresh();
  for (int i = 0; i < n; ++i)
    for (int r = 0; r < R; ++r) cl({(u.rows[r] >> i & 1) ? v[i][r] : -v[i][r]});
  std::vector<std::vector<Choice>> ch(k);
  std::vector<std::vector<int>> sel(k);
  std::vector<std::vector<int>> reads(k, std::vector<int>(W, 0));  // reads[g][w] var (w < n + g)
  for (int g = 0; g < k; ++g) {
    int gw = n + g;
    for (int b = 0; b < gw; ++b) {
      if (u.general) ch[g].push_back({2, b, b});
      for (int a = 0; a < b; ++a) { ch[g].push_back({0, a, b}); ch[g].push_back({1, a, b}); }
    }
    for (auto& c : ch[g]) {
      int x = fresh();
      sel[g].push_back(x);
      for (int r = 0; r < R; ++r) {
        int o = v[gw][r], p = v[c.a][r], q = v[c.b][r];
        if (c.op == 0) { cl({-x, -o, p}); cl({-x, -o, q}); cl({-x, o, -p, -q}); }
        else if (c.op == 1) { cl({-x, o, -p}); cl({-x, o, -q}); cl({-x, -o, p, q}); }
        else { cl({-x, o, p}); cl({-x, -o, -p}); }
      }
    }
    for (int x : sel[g]) s.add(x);
    s.add(0);
    if (g_used || g_colex || g_essential) {
      for (int w = 0; w < gw; ++w) reads[g][w] = fresh();
      std::vector<std::vector<int>> by(gw);
      for (size_t c = 0; c < ch[g].size(); ++c) {
        by[ch[g][c].a].push_back(sel[g][c]);
        if (ch[g][c].b != ch[g][c].a) by[ch[g][c].b].push_back(sel[g][c]);
      }
      for (int w = 0; w < gw; ++w) {
        for (int x : by[w]) cl({-x, reads[g][w]});
        s.add(-reads[g][w]);
        for (int x : by[w]) s.add(x);
        s.add(0);
      }
    }
  }
  // output = last gate
  for (int r = 0; r < R; ++r) cl({u.target[r] ? v[W - 1][r] : -v[W - 1][r]});
  if (g_essential)
    for (int w = 0; w < n; ++w)
      if (essential_input(u, w)) {
        for (int g = 0; g < k; ++g) s.add(reads[g][w]);
        s.add(0);
      }
  if (g_used)
    for (int g = 0; g + 1 < k; ++g) {
      for (int h = g + 1; h < k; ++h) s.add(reads[h][n + g]);
      s.add(0);
    }
  if (g_slots && g_essential && g_used) {
    // Read-slot count: k gates read at most 2k (gate, wire) pairs. Every essential input (E of them) and
    // every non-output gate (k - 1) is read at least once, so the extra reads -- a second or later reader
    // of an input or gate, or any reader of a non-essential input -- number at most k + 1 - E.
    std::vector<int> ess(n, 0);
    int E = 0;
    for (int w = 0; w < n; ++w) E += ess[w] = essential_input(u, w);
    int slack = k + 1 - E;
    if (slack < 0) return 20;
    std::vector<int> extra;
    std::vector<std::vector<int>> mx(W - 1);  // per wire: its extra-read vars
    for (int w = 0; w < W - 1; ++w) {
      int first = w < n ? 0 : w - n + 1;  // first gate that may read wire w
      int prev = 0;                       // var: some gate before h reads w
      for (int h = first; h < k; ++h) {
        int rd = reads[h][w];
        if (!rd) continue;
        if (w < n && !ess[w]) { extra.push_back(rd); mx[w].push_back(rd); continue; }
        if (prev) {
          int x = fresh();
          cl({-rd, -prev, x});
          if (multi) { cl({-x, rd}); cl({-x, prev}); }  // x <-> (h reads w and an earlier gate does)
          extra.push_back(x);
          mx[w].push_back(x);
        }
        int p = fresh();
        cl({-rd, p});
        if (prev) cl({-prev, p});
        prev = p;
      }
    }
    if (multi) {
      // Cube: S = *multi is exactly the set of wires with an extra read (a second reader of an essential
      // input or gate, or any reader of a non-essential input). Every other wire has no extra read.
      std::vector<char> in(W - 1, 0);
      for (int w : *multi) in[w] = 1;
      for (int w = 0; w < W - 1; ++w) {
        if (in[w]) {
          if (mx[w].empty()) return 20;
          for (int x : mx[w]) s.add(x);
          s.add(0);
        } else {
          for (int x : mx[w]) cl({-x});
        }
      }
    }
    // at most `slack` of `extra` true (sequential counter)
    if (slack == 0) {
      for (int x : extra) cl({-x});
    } else if ((int)extra.size() > slack) {
      int m = (int)extra.size();
      std::vector<std::vector<int>> c(m, std::vector<int>(slack));
      for (int i = 0; i < m; ++i)
        for (int j = 0; j < slack; ++j) c[i][j] = fresh();
      for (int i = 0; i < m; ++i) {
        cl({-extra[i], c[i][0]});
        if (i > 0) {
          for (int j = 0; j < slack; ++j) cl({-c[i - 1][j], c[i][j]});
          for (int j = 1; j < slack; ++j) cl({-extra[i], -c[i - 1][j - 1], c[i][j]});
          cl({-extra[i], -c[i - 1][slack - 1]});
        }
      }
    }
  }
  if (g_distinct)
    for (int g = 0; g < k; ++g) {
      int gw = n + g;
      if (g + 1 < k) {  // non-output gates are not constant on the cared rows
        for (int r = 0; r < R; ++r) s.add(v[gw][r]);
        s.add(0);
        for (int r = 0; r < R; ++r) s.add(-v[gw][r]);
        s.add(0);
      }
      for (int w = 0; w < gw; ++w) {
        std::vector<int> d(R);
        for (int r = 0; r < R; ++r) {
          d[r] = fresh();
          cl({-d[r], v[gw][r], v[w][r]});
          cl({-d[r], -v[gw][r], -v[w][r]});
        }
        for (int x : d) s.add(x);
        s.add(0);
      }
    }
  if (g_colex)
    for (int g = 0; g + 2 < k; ++g) {  // pairs (g, g+1) strictly below the output gate
      auto key = [](const Choice& c) { return (long long)c.b * 1000000 + (long long)c.a * 10 + c.op; };
      int dep = reads[g + 1][n + g];
      for (size_t c = 0; c < ch[g].size(); ++c) {
        long long kc = key(ch[g][c]);
        for (size_t d = 0; d < ch[g + 1].size(); ++d) {
          const Choice& e = ch[g + 1][d];
          if (e.a == n + g || e.b == n + g) continue;  // dependent choice: no ordering
          if (key(e) < kc) cl({-sel[g][c], -sel[g + 1][d], dep});
        }
      }
    }
  if (cube >= 0) {
    if (cube >= (int)sel[0].size()) return 20;
    cl({sel[0][cube]});
  }
  if (!g_dump.empty() && cube < 0) {
    std::string path = g_dump + "/" + u.id + "_k" + std::to_string(k) + ".cnf";
    if (const char* err = s.write_dimacs(path.c_str())) std::fprintf(stderr, "dump %s: %s\n", path.c_str(), err);
    return 20;  // keep going to the budget
  }
  Deadline t;
  t.end = end;
  t.stop = stop;
  s.connect_terminator(&t);
  int res = s.solve();
  s.disconnect_terminator();
  if (res != 10) return res;
  gates.clear();
  for (int g = 0; g < k; ++g) {
    size_t c = 0;
    while (c < ch[g].size() && s.val(sel[g][c]) <= 0) ++c;
    if (c == ch[g].size()) { std::fprintf(stderr, "decode failed\n"); std::abort(); }
    gates.push_back(ch[g][c]);
  }
  return 10;
}

// Split size k on the choice of gate 0 (every circuit makes one): SAT if some cube is SAT, UNSAT if all are.
// With --split-reads, split instead on S = the set of wires with an extra read (see the read-slot count):
// every circuit has exactly one such S, |S| <= slack = k + 1 - E, so the cubes partition the size.
static int solve_cubes(const Unit& u, int k, const Clock::time_point& end, std::vector<Choice>& gates) {
  std::vector<std::vector<int>> subsets;
  if (g_split_reads) {
    int E = 0;
    for (int w = 0; w < u.n; ++w) E += essential_input(u, w);
    int slack = k + 1 - E, nw = u.n + k - 1;  // wires 0..nw-1 (all but the output)
    if (slack < 0) return 20;
    std::vector<int> cur;
    std::function<void(int)> rec = [&](int from) {
      subsets.push_back(cur);
      if ((int)cur.size() == slack) return;
      for (int w = from; w < nw; ++w) { cur.push_back(w); rec(w + 1); cur.pop_back(); }
    };
    rec(0);
    // larger S first: fewer forced-single wires, usually the slowest cubes
    std::stable_sort(subsets.begin(), subsets.end(),
                     [](const std::vector<int>& a, const std::vector<int>& b) { return a.size() > b.size(); });
  }
  int n0 = g_split_reads ? (int)subsets.size()
                         : (u.general ? u.n : 0) + u.n * (u.n - 1);  // gate-0 choices, in solve_k's order
  std::atomic<bool> stop{false};
  std::atomic<int> remaining{n0};
  std::vector<int> res(n0, 0);
  std::vector<std::vector<Choice>> wit(n0);
  {
    std::lock_guard<std::mutex> lk(g_qmu);
    for (int c = 0; c < n0; ++c)
      g_cubes.push_back([&, c] {
        res[c] = g_split_reads ? solve_k(u, k, end, wit[c], -1, &stop, &subsets[c])
                               : solve_k(u, k, end, wit[c], c, &stop);
        if (res[c] == 10) stop = true;
        --remaining;
      });
  }
  g_qcv.notify_all();
  while (remaining.load() > 0) run_one_cube(true);
  bool timeout = false;
  for (int c = 0; c < n0; ++c) {
    if (res[c] == 10) { gates = wit[c]; return 10; }
    if (res[c] != 20) timeout = true;
  }
  return timeout ? 0 : 20;
}

static std::string run(const Unit& u) {
  auto t0 = Clock::now();
  auto end = t0 + std::chrono::milliseconds((long long)(g_seconds * 1000));
  std::ostringstream o;
  auto secs = [&] { return std::chrono::duration<double>(Clock::now() - t0).count(); };
  o << "{\"id\":\"" << u.id << "\"";
  bool any = false, all = true;
  for (int t : u.target) { any = any || t != 0; all = all && t != 0; }
  int R = (int)u.rows.size();
  // trivial: constant targets or an input wire that matches
  if (!any || all) {
    o << ",\"status\":\"TRIVIAL\",\"const\":" << (any ? 1 : 0) << ",\"seconds\":0}";
    return o.str();
  }
  for (int i = 0; i < u.n; ++i) {
    bool ok = true;
    for (int r = 0; r < R && ok; ++r) ok = (int)((u.rows[r] >> i) & 1) == u.target[r];
    if (ok) { o << ",\"status\":\"TRIVIAL\",\"wire\":" << i << ",\"seconds\":0}"; return o.str(); }
  }
  std::ostringstream ks;
  std::vector<Choice> gates;
  for (int k = std::max(1, u.start); k <= u.budget; ++k) {
    double tk = secs();
    int res;
    if (g_probe <= 0) {
      res = solve_k(u, k, end, gates);
    } else {
      auto probe_end = std::min(end, Clock::now() + std::chrono::milliseconds((long long)(g_probe * 1000)));
      res = solve_k(u, k, probe_end, gates);
      if (res == 0 && Clock::now() < end) res = solve_cubes(u, k, end, gates);
    }
    ks << (k > std::max(1, u.start) ? "," : "") << "[" << k << ",\"" << (res == 10 ? "SAT" : res == 20 ? "UNSAT" : "TIMEOUT")
       << "\"," << (secs() - tk) << "]";
    if (res == 0) {
      o << ",\"status\":\"TIMEOUT\",\"k\":" << k << ",\"seconds\":" << secs() << ",\"ks\":[" << ks.str() << "]}";
      return o.str();
    }
    if (res == 10) {
      int out = u.n + k - 1;
      for (int r = 0; r < R; ++r)
        if (simulate(u, gates, out, u.rows[r]) != u.target[r]) { std::fprintf(stderr, "%s: bad model\n", u.id.c_str()); std::abort(); }
      o << ",\"status\":\"SAT\",\"k\":" << k << ",\"gates\":[";
      for (int j = 0; j < k; ++j) o << (j ? "," : "") << "[" << gates[j].op << "," << gates[j].a << "," << gates[j].b << "]";
      o << "],\"out\":" << out << ",\"seconds\":" << secs() << ",\"ks\":[" << ks.str() << "]}";
      return o.str();
    }
  }
  o << ",\"status\":\"UNSAT\",\"k\":" << u.budget << ",\"seconds\":" << secs() << ",\"ks\":[" << ks.str() << "]}";
  return o.str();
}

static bool parse(const std::string& line, Unit& u) {
  std::istringstream in(line);
  std::string rows;
  if (!(in >> u.id >> u.n >> u.general >> u.start >> u.budget >> rows)) return false;
  std::stringstream rs(rows);
  std::string item;
  while (std::getline(rs, item, ',')) {
    size_t c = item.find(':');
    if (c == std::string::npos) return false;
    u.rows.push_back(std::stoull(item.substr(0, c), nullptr, 16));
    u.target.push_back(std::stoi(item.substr(c + 1)));
  }
  return !u.rows.empty() && u.n <= 60;
}

int main(int argc, char** argv) {
#ifdef _WIN32
  SetUnhandledExceptionFilter(crash_trace);
#endif
  int threads = 11;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--threads" && i + 1 < argc) threads = std::atoi(argv[++i]);
    else if (a == "--seconds" && i + 1 < argc) g_seconds = std::atof(argv[++i]);
    else if (a == "--no-used") g_used = false;
    else if (a == "--no-distinct") g_distinct = false;
    else if (a == "--no-colex") g_colex = false;
    else if (a == "--no-essential") g_essential = false;
    else if (a == "--no-slots") g_slots = false;
    else if (a == "--congruence") g_congruence = true;
    else if (a == "--dump" && i + 1 < argc) { g_dump = argv[++i]; g_probe = 0; }
    else if (a == "--solve-cnf" && i + 1 < argc) {  // time this CaDiCaL build on one DIMACS file (same options)
      CaDiCaL::Solver s;
      if (!g_congruence) s.set("congruence", 0);
      int vars = 0;
      if (const char* err = s.read_dimacs(argv[++i], vars, 0)) { std::fprintf(stderr, "%s\n", err); return 2; }
      Deadline t;
      t.end = Clock::now() + std::chrono::milliseconds((long long)(g_seconds * 1000));
      auto t0 = Clock::now();
      s.connect_terminator(&t);
      int res = s.solve();
      std::printf("{\"cnf\":\"%s\",\"status\":%d,\"seconds\":%.3f}\n", argv[i], res,
                  std::chrono::duration<double>(Clock::now() - t0).count());
      return 0;
    }
    else if (a == "--probe" && i + 1 < argc) g_probe = std::atof(argv[++i]);
    else if (a == "--split-reads") g_split_reads = true;
    else { std::fprintf(stderr, "unknown option %s\n", a.c_str()); return 2; }
  }
  if (g_split_reads && !(g_slots && g_essential && g_used)) {
    std::fprintf(stderr, "--split-reads needs the read-slot count (used, essential, slots)\n");
    return 2;
  }
  std::vector<Unit> units;
  std::string line;
  while (std::getline(std::cin, line)) {
    if (line.empty() || line[0] == '#') continue;
    Unit u;
    if (!parse(line, u)) { std::fprintf(stderr, "bad line: %s\n", line.c_str()); return 2; }
    units.push_back(std::move(u));
  }
  std::atomic<size_t> next{0}, done{0};
  std::mutex mu;
  std::vector<std::thread> pool;
  for (int t = 0; t < std::max(1, threads); ++t)
    pool.emplace_back([&] {
      for (;;) {
        if (run_one_cube(false)) continue;
        size_t i = next++;
        if (i < units.size()) {
          std::string r = run(units[i]);
          std::lock_guard<std::mutex> lk(mu);
          std::cout << r << std::endl;
          ++done;
          continue;
        }
        // no units left: keep serving cubes until every unit has reported
        if (done.load() == units.size()) break;
        run_one_cube(true);
      }
    });
  for (auto& th : pool) th.join();
  return 0;
}
