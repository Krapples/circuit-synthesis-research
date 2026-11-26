// Constructive upper bounds by cofactor two-signal decomposition (see src/cofactor_witness.hpp).
// Usage:
//   cofactor_synth [--depth D] N TT [CARE]     one target (hex truth table, row r = sum x_i 2^i)
//   cofactor_synth [--depth D] --stdin         one target per line: N TT [CARE]
// Prints one JSON line per target: size, plan estimate, indexed AIG, and the percy_run --upper-witness spec.
// Each chain is re-simulated against the target on its care set before it is printed.
#include <chrono>
#include <cstdio>
#include <iostream>
#include <sstream>

#include "../src/cofactor_witness.hpp"

using namespace cofactor;

static void emit(const PairTable& T, int n, u64 f, u64 care) {
  auto t0 = std::chrono::steady_clock::now();
  Witness w = synthesize(T, n, f, care);
  double s = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  int hex = std::max(1, (1 << n) / 4);
  char tt[32], cr[32];
  std::snprintf(tt, sizeof tt, "%0*llx", hex, (unsigned long long)w.target);
  std::snprintf(cr, sizeof cr, "%0*llx", hex, (unsigned long long)w.care);
  std::cout << "{\"n\":" << n << ",\"target\":\"" << tt << "\",\"care\":\"" << cr << "\",\"size\":" << w.gates.size()
            << ",\"estimate\":" << w.estimate << ",\"verified\":true,\"seconds\":" << s << ",\"gates\":[";
  for (std::size_t j = 0; j < w.gates.size(); ++j)
    std::cout << (j ? "," : "") << "[" << w.gates[j][0] << "," << w.gates[j][1] << "]";
  std::cout << "],\"output\":" << w.output << ",\"spec\":\"" << w.spec() << "\"}\n";
}

int main(int argc, char** argv) {
  int depth = 7, i = 1;
  bool from_stdin = false;
  for (; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--depth" && i + 1 < argc) depth = std::stoi(argv[++i]);
    else if (a == "--stdin") from_stdin = true;
    else break;
  }
  try {
    auto t0 = std::chrono::steady_clock::now();
    PairTable T(depth);
    std::cerr << "pair table depth " << depth << " transitions " << T.transitions << " pairs " << T.pairs.size()
              << " seconds " << std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() << "\n";
    auto one = [&](const std::string& line) {
      std::istringstream in(line);
      int n; std::string tt, care;
      if (!(in >> n >> tt)) return;
      u64 c = (in >> care) ? std::stoull(care, nullptr, 16) : ~0ull;
      emit(T, n, std::stoull(tt, nullptr, 16), c);
    };
    if (from_stdin) {
      std::string line;
      while (std::getline(std::cin, line)) one(line);
    } else {
      if (argc - i < 2) { std::cerr << "usage: cofactor_synth [--depth D] N TT [CARE] | --stdin\n"; return 2; }
      std::string line;
      for (int j = i; j < argc; ++j) line += std::string(argv[j]) + " ";
      one(line);
    }
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << "\n";
    return 1;
  }
  std::cout.flush();
  return 0;
}
