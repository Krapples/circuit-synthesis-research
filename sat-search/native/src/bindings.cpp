// pybind11 bindings: one Python -> C++ call per regional completion query.
// Interrupts: the core polls every POLL_INTERVAL work units; the poll runs PyErr_CheckSignals(), so
// regional_deadline.timed (interrupt_main) and Ctrl-C raise KeyboardInterrupt out of the native call exactly as
// they would out of the Python reference.  An optional native deadline (seconds) returns status ABORTED instead.
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include <algorithm>
#include <chrono>
#include <unordered_map>

#include "regional_kernel.hpp"
#include "tight_residual.hpp"
#include "slack_two_boundary.hpp"

namespace py = pybind11;

namespace {

synthesis::ResidualFilterMode residual_filter_mode(int mode) {
    if (mode < 0 || mode > 3) throw py::value_error("residual filter must be 0 (off) through 3 (direct)");
    return static_cast<synthesis::ResidualFilterMode>(mode);
}

synthesis::ResidualBackend residual_backend(int backend) {
    if (backend < 0 || backend > 2) throw py::value_error("residual backend must be 0 through 2");
    return static_cast<synthesis::ResidualBackend>(backend);
}

py::tuple directed_tree(const residual_directed::Tree& tree) {
    if (tree->occurrence >= 0) return py::make_tuple("x", tree->occurrence);
    return py::make_tuple("&", tree->pa, tree->pb, tree->po, directed_tree(tree->a), directed_tree(tree->b));
}

py::object directed_witness(const residual_directed::Witness& witness) {
    if (!witness) return py::none();
    return py::make_tuple(directed_tree(witness.tree), witness.phase);
}

// The search holds the GIL (it owns no Python objects while running, so releasing it briefly is safe).  Yield it at
// every poll so other Python threads run -- in particular the regional_deadline.timed alarm thread, which must take
// the GIL to call interrupt_main(); PyErr_CheckSignals() then raises the resulting KeyboardInterrupt here.
inline void yield_gil() {
    Py_BEGIN_ALLOW_THREADS
    Py_END_ALLOW_THREADS
}

py::object to_tree(const std::vector<regional::Node>& nodes, int id, std::unordered_map<int, py::object>& memo,
                   const py::str& x, const py::str& land, const py::str& lor) {
    auto it = memo.find(id);
    if (it != memo.end()) return it->second;
    const regional::Node& nd = nodes[id];
    py::object out;
    if (nd.op == 'x') {
        out = py::make_tuple(x, nd.a, py::bool_(nd.b != 0));
    } else {
        py::object a = to_tree(nodes, nd.a, memo, x, land, lor);
        py::object b = to_tree(nodes, nd.b, memo, x, land, lor);
        out = py::make_tuple(nd.op == '&' ? land : lor, a, b);
    }
    memo.emplace(id, out);
    return out;
}

py::dict stats_dict(const regional::Stats& s) {
    py::dict d;
#define PUT(name) d[#name] = s.name
    PUT(rec); PUT(row_reject); PUT(module_reject); PUT(port_allocations); PUT(port_allocation_reject);
    PUT(partition_checks); PUT(endpoint_split_reject); PUT(dominance_split_reject); PUT(obligation_partitions);
    PUT(cover_nodes); PUT(quotient_conflicts); PUT(quotient_dropped); PUT(work); PUT(complete_cache_hits);
    PUT(peak_cache_entries); PUT(local); PUT(phase_first_calls); PUT(phase_clauses); PUT(phase_nodes);
    PUT(phase_classes); PUT(monotone_calls); PUT(phase_reject);
#undef PUT
    return d;
}

py::tuple solve_blocks(int m, std::vector<int> provider_ids, std::vector<int> counts, std::vector<uint32_t> pats,
                       std::vector<uint8_t> target_any, std::vector<uint64_t> target_words, bool is_signed,
                       bool module_filter, bool row_quotient, std::vector<int8_t> phase,
                       std::vector<uint32_t> forced_and, std::vector<uint32_t> forced_or, int64_t work_limit,
                       double deadline_seconds) {
    regional::Query q;
    q.m = m;
    q.provider_ids = std::move(provider_ids);
    q.counts = std::move(counts);
    q.pats = std::move(pats);
    q.target_any = std::move(target_any);
    q.target_words = std::move(target_words);
    q.is_signed = is_signed;
    q.module_filter = module_filter;
    q.row_quotient = row_quotient;
    q.phase = std::move(phase);
    q.forced_and = std::move(forced_and);
    q.forced_or = std::move(forced_or);
    q.work_limit = work_limit;
    bool interrupted = false;
    const bool timed = deadline_seconds > 0;
    const auto until = std::chrono::steady_clock::now() + std::chrono::duration<double>(timed ? deadline_seconds : 0);
    q.poll = [&]() {
        yield_gil();
        if (PyErr_CheckSignals() != 0) { interrupted = true; return true; }
        return timed && std::chrono::steady_clock::now() >= until;
    };
    regional::Result r = regional::solve(q);
    if (interrupted) throw py::error_already_set();  // KeyboardInterrupt from the deadline timer or Ctrl-C
    py::object tree = py::none();
    if (r.status == regional::Status::SAT) {
        std::unordered_map<int, py::object> memo;
        tree = to_tree(r.nodes, r.root, memo, py::str("x"), py::str("&"), py::str("|"));
    }
    py::dict st = stats_dict(r.stats);
    st["nodes"] = int64_t(r.nodes.size());
    return py::make_tuple(int(r.status), tree, st);
}

py::tuple solve_completion(int m, std::vector<int> provider_ids, std::vector<int> counts, std::vector<uint32_t> pats,
                           std::vector<uint8_t> target_any, std::vector<uint64_t> target_words, bool is_signed,
                           bool module_filter, bool adaptive) {
    regional::Query q;
    q.m = m;
    q.provider_ids = std::move(provider_ids);
    q.counts = std::move(counts);
    q.pats = std::move(pats);
    q.target_any = std::move(target_any);
    q.target_words = std::move(target_words);
    q.is_signed = is_signed;
    q.module_filter = module_filter;
    q.row_quotient = true;
    q.phase.assign(m, -1); q.forced_and.assign(m, 0); q.forced_or.assign(m, 0);   // recomputed natively
    bool interrupted = false;
    q.poll = [&]() {
        yield_gil();
        if (PyErr_CheckSignals() != 0) { interrupted = true; return true; }
        return false;
    };
    regional::Result r = regional::solve_completion(q, adaptive);
    if (interrupted) throw py::error_already_set();
    py::object tree = py::none();
    if (r.status == regional::Status::SAT) {
        std::unordered_map<int, py::object> memo;
        tree = to_tree(r.nodes, r.root, memo, py::str("x"), py::str("&"), py::str("|"));
    }
    py::dict st = stats_dict(r.stats);
    st["nodes"] = int64_t(r.nodes.size());
    return py::make_tuple(int(r.status), tree, st);
}

py::tuple prelude(int m, std::vector<uint8_t> target_any, std::vector<uint64_t> target_words, bool is_signed) {
    std::vector<int8_t> phase;
    std::vector<uint32_t> fa, fo;
    const bool ok = regional::prelude(m, target_any, target_words, is_signed, phase, fa, fo);
    return py::make_tuple(ok, phase, fa, fo);
}

py::tuple pack_obligation_rows(const py::tuple& rows, const std::vector<uint64_t>& columns,
                               const py::tuple& members) {
    if (rows.size() > 64 || columns.size() > 64) {
        throw py::value_error("at most 64 rows and columns can be packed");
    }
    std::vector<std::pair<uint64_t, size_t>> ordered;
    ordered.reserve(rows.size());
    for (size_t row = 0; row < rows.size(); ++row) {
        uint64_t pattern = 0;
        for (size_t column = 0; column < columns.size(); ++column) {
            pattern |= ((columns[column] >> row) & 1) << column;
        }
        ordered.emplace_back(pattern, row);
    }
    std::sort(ordered.begin(), ordered.end());

    py::tuple patterns(rows.size()), targets(rows.size());
    for (size_t i = 0; i < ordered.size(); ++i) {
        const auto [pattern, row] = ordered[i];
        if (i && pattern == ordered[i - 1].first) {
            PyErr_SetString(PyExc_AssertionError, "column equivalence did not preserve the observed row identities");
            throw py::error_already_set();
        }
        patterns[i] = py::int_(pattern);
        targets[i] = py::cast<py::tuple>(rows[row])[1];
    }
    return py::make_tuple(patterns, targets, members);
}

}  // namespace

PYBIND11_MODULE(_regional_native, mod) {
    mod.doc() = "Native regional completion kernel (port of theory/regional_block_completion.local_blocks)";
    mod.attr("MAX_M") = regional::MAX_M;
    mod.attr("MAX_PROVIDERS") = regional::MAX_PROVIDERS;
    mod.attr("MAX_ROWS") = regional::MAX_ROWS;
    mod.def("solve_blocks", &solve_blocks, py::arg("m"), py::arg("provider_ids"), py::arg("counts"), py::arg("pats"),
            py::arg("target_any"), py::arg("target_words"), py::arg("signed"), py::arg("module_filter"),
            py::arg("row_quotient"), py::arg("phase"), py::arg("forced_and"), py::arg("forced_or"),
            py::arg("work_limit") = -1, py::arg("deadline_seconds") = 0.0,
            "Returns (status, tree|None, stats); status 0 UNSAT, 1 SAT, 2 ABORTED (native deadline), 3 WORK_LIMIT.");
    mod.def("solve_completion", &solve_completion, py::arg("m"), py::arg("provider_ids"), py::arg("counts"),
            py::arg("pats"), py::arg("target_any"), py::arg("target_words"), py::arg("signed"),
            py::arg("module_filter"), py::arg("adaptive"),
            "Full completion call: native prelude + local_blocks (adaptive=False) or regional_phase_first."
            "adaptive_completion (adaptive=True).  Returns (status, tree|None, stats).");
    mod.def("prelude", &prelude, py::arg("m"), py::arg("target_any"), py::arg("target_words"), py::arg("signed"),
            "Native read-once prelude: (ok, phase[m] (-1 unknown), forced_and[m], forced_or[m]).");
    mod.def("pack_obligation_rows", &pack_obligation_rows);
    mod.def("tight_residual",
            [](const std::vector<uint64_t>& columns, unsigned first_layer, uint64_t target,
               uint64_t care, unsigned work_limit, int filter_mode, int backend) {
                return int(synthesis::residual_zero(columns, first_layer, target, care, work_limit,
                                                    residual_filter_mode(filter_mode),
                                                    synthesis::residual_detail::Clock::time_point::max(),
                                                    residual_backend(backend)));
            }, py::arg("columns"), py::arg("first_layer"), py::arg("target"), py::arg("care"),
            py::arg("work_limit") = 4096, py::arg("filter_mode") = 0, py::arg("backend") = 0,
            "Exact fixed-boundary free-NOT completion: 0 infeasible, 1 feasible, 2 unknown.");
    mod.def("slack_one_extensions",
            [](const std::vector<uint64_t>& columns, unsigned h, const std::vector<uint64_t>& primaries,
               unsigned mixed, uint64_t target, uint64_t care, unsigned work_limit,
               unsigned tight_work_limit, double deadline_seconds, int filter_mode, bool include_metrics,
               int backend) -> py::tuple {
                if (primaries.size() > 6) throw py::value_error("at most six candidate primaries");
                const auto mode = residual_filter_mode(filter_mode);
                const auto engine = residual_backend(backend);
                using Clock = synthesis::residual_detail::Clock;
                const auto deadline = deadline_seconds > 0
                    ? Clock::now() + std::chrono::duration_cast<Clock::duration>(
                        std::chrono::duration<double>(deadline_seconds))
                    : Clock::time_point::max();
                synthesis::SlackOneStats stats;
                synthesis::SlackOneExtension result;
                {
                    const py::gil_scoped_release release;
                    result = synthesis::slack_one_extensions(columns, h, primaries, mixed, target, care,
                                                             work_limit, tight_work_limit, stats, deadline, mode, engine);
                }
                if (!include_metrics)
                    return py::make_tuple(int(result.exact), result.feasible, result.unknown, stats.completion_case,
                                          stats.work, stats.providers, stats.filtered, stats.decoders);
                py::dict metrics;
                metrics["joins"] = stats.joins;
                metrics["root_splits"] = stats.root_splits;
                metrics["root_rejected"] = stats.root_rejected;
                metrics["allocations"] = stats.allocations;
                metrics["parity_rejected"] = stats.parity_rejected;
                metrics["direct_queries"] = stats.direct_queries;
                metrics["directed_states"] = stats.directed_states;
                return py::make_tuple(int(result.exact), result.feasible, result.unknown, stats.completion_case,
                                      stats.work, stats.providers, stats.filtered, stats.decoders, metrics);
            }, py::arg("columns"), py::arg("first_layer"), py::arg("primaries"), py::arg("mixed_mask"),
            py::arg("target"), py::arg("care"), py::arg("work_limit") = 100000,
            py::arg("tight_work_limit") = 4096, py::arg("deadline_seconds") = 0.0, py::arg("filter_mode") = 0,
            py::arg("include_metrics") = false, py::arg("backend") = 0,
            "Return status, extension masks, completion case, work, provider counts, and optional filter counters.");
    mod.def("directed_completion",
            [](const std::vector<uint64_t>& columns, unsigned h, uint64_t target, uint64_t care,
               unsigned slack, unsigned work_limit, bool dominance) -> py::tuple {
                if (slack > 1) throw py::value_error("slack must be 0 or 1");
                synthesis::ResidualWitness witness;
                synthesis::SlackOneStats stats;
                const auto backend = dominance ? synthesis::ResidualBackend::dominance
                                               : synthesis::ResidualBackend::directed;
                const auto deadline = synthesis::residual_detail::Clock::time_point::max();
                const auto mode = synthesis::ResidualFilterMode::direct;
                const auto result = slack
                    ? synthesis::slack_one_residual(columns, h, target, care, work_limit, stats, deadline,
                                                    mode, backend, &witness)
                    : synthesis::residual_zero(columns, h, target, care, work_limit, mode, deadline,
                                               backend, &witness);
                if (result != synthesis::ResidualStatus::feasible)
                    return py::make_tuple(int(result), py::none());
                return py::make_tuple(int(result),
                    py::make_tuple(stats.completion_case, witness.repeated, witness.provider_leaves,
                                   witness.provider_column, directed_witness(witness.provider),
                                   directed_witness(witness.decoder)));
            }, py::arg("columns"), py::arg("first_layer"), py::arg("target"), py::arg("care"),
            py::arg("slack"), py::arg("work_limit") = 100000, py::arg("dominance") = false,
            "Return status and optional normalized occurrence witness (case, repeated index, provider mask,"
            " provider column, provider tree with phase, decoder tree with phase).");
    mod.def("slack_two_boundary",
            [](const std::vector<uint64_t>& columns, unsigned h, const std::vector<uint64_t>& primaries,
               unsigned mixed, const std::vector<uint64_t>& gate_columns, uint64_t target, uint64_t care,
               unsigned work_limit, double seconds, unsigned mode) {
                if (mode > 5) throw py::value_error("slack-two mode must be 0 through 5");
                using Clock = synthesis::residual_detail::Clock;
                const auto deadline = seconds > 0
                    ? Clock::now() + std::chrono::duration_cast<Clock::duration>(std::chrono::duration<double>(seconds))
                    : Clock::time_point::max();
                synthesis::SlackTwoBoundary result;
                {
                    const py::gil_scoped_release release;
                    result = synthesis::slack_two_boundary(columns, h, primaries, mixed, gate_columns,
                                                           target, care, work_limit, deadline, mode);
                }
                const auto& exact = result.exact;
                using Status = residual_directed::Status;
                py::dict metrics;
                metrics["status"] = exact.status == Status::sat ? 1 : exact.status == Status::unsat ? 0 : 2;
                metrics["work"] = exact.work;
                metrics["allocations"] = exact.allocations;
                metrics["parity_rejects"] = exact.parity_rejects;
                metrics["provider_trials"] = exact.provider_trials;
                metrics["tree_calls"] = exact.tree_calls;
                metrics["memo_hits"] = exact.memo_hits;
                metrics["unate_rejects"] = exact.unate_rejects;
                metrics["unate_merges"] = exact.unate_merges;
                metrics["phase_checks"] = exact.phase.checks;
                metrics["phase_rejects"] = exact.phase.rejects;
                metrics["phase_work"] = exact.phase.work;
                metrics["phase_cache_hits"] = exact.phase.cache_hits;
                metrics["phase_dominance_hits"] = exact.phase.dominance_hits;
                metrics["gate_extensions"] = result.gate_extensions;
                metrics["mixed_extensions"] = result.mixed_extensions;
                metrics["extension_feasible"] = result.feasible;
                metrics["extension_unknown"] = result.unknown;
                metrics["extension_excluded"] = result.excluded;
                py::list regions;
                for (const auto& region : exact.regions) {
                    py::list inputs;
                    for (const auto& leaf : region.inputs)
                        inputs.append(py::make_tuple(leaf.wire, leaf.column, leaf.raw));
                    regions.append(py::make_tuple(region.output, region.column, inputs,
                                                  directed_witness(region.witness)));
                }
                return py::make_tuple(metrics, regions);
            }, py::arg("columns"), py::arg("first_layer"), py::arg("primaries"), py::arg("mixed_mask"),
            py::arg("gate_columns"), py::arg("target"), py::arg("care"), py::arg("work_limit") = 100000,
            py::arg("deadline_seconds") = 0.025, py::arg("mode") = 2);
}
