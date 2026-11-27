import json
from dataclasses import replace
import os
from pathlib import Path
from tempfile import TemporaryDirectory
import sys
import unittest
from unittest.mock import patch

from threading import Event

from common import ROOT, process_alive, read_json, run_logged
from graph import canonical_graph
from ops import audit_lean_axioms, beat, command_failure, heartbeat, normalize
from runs import build_jobs, run_batch


class LeanAuditTests(unittest.TestCase):
    def test_wrapped_and_axiom_free_reports(self):
        report = audit_lean_axioms("'Proof.main' depends on axioms: [propext,\n"
                                   "  Classical.choice, Quot.sound]\n"
                                   "'Proof.direct' does not depend on any axioms\n")
        self.assertEqual(report["status"], "ok")
        self.assertEqual(report["declarations"], {"Proof.main": ["Classical.choice", "Quot.sound", "propext"],
                                                  "Proof.direct": []})

    def test_unexpected_and_missing_reports(self):
        report = audit_lean_axioms("'Proof.direct' does not depend on any axioms\n"
                                   "'Proof.main'' depends on axioms: [propext, sorryAx]\n"
                                   "'Proof.quoted' depends on axioms: [«bad]»]\n")
        self.assertEqual(report["status"], "unexpected")
        self.assertEqual(report["unexpected"], {"Proof.main'": ["sorryAx"], "Proof.quoted": ["«bad]»"]})
        self.assertEqual(audit_lean_axioms("Build finished\n")["status"], "missing")


class CanonicalGraphTests(unittest.TestCase):
    def test_relabel_and_keep_distinct_regular_graphs(self):
        cycle = [(i, (i + 1) % 6) for i in range(6)]
        rename = (3, 5, 1, 4, 0, 2)
        colors = ("a", "b", "a", "a", "a", "b")
        relabeled_colors = [None] * 6
        for i, j in enumerate(rename):
            relabeled_colors[j] = colors[i]
        first = canonical_graph(6, cycle, colors=colors)
        second = canonical_graph(6, [(rename[a], rename[b]) for a, b in cycle], colors=relabeled_colors)
        self.assertTrue(first.canonical and second.canonical)
        self.assertEqual((first.edges, first.colors), (second.edges, second.colors))
        for graph, edges in [(first, cycle), (second, [(rename[a], rename[b]) for a, b in cycle])]:
            self.assertEqual(graph.edges, tuple(sorted(tuple(sorted((graph.old_to_new[a], graph.old_to_new[b])))
                                                       for a, b in edges)))
        triangles = [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)]
        self.assertNotEqual(canonical_graph(6, cycle).edges, canonical_graph(6, triangles).edges)

    def test_safe_fallback(self):
        graph = canonical_graph(3, [(1, 0), (0, 2)], limit=0)
        self.assertFalse(graph.canonical)
        self.assertEqual(graph.old_to_new, (0, 1, 2))
        self.assertEqual(graph.edges, ((0, 1), (0, 2)))
        with self.assertRaises(ValueError):
            canonical_graph(3, [(0, 0)])


class RunTests(unittest.TestCase):
    def job(self, script, initial=10, maximum=10):
        batch = {"schema": "research-batch/1", "jobs": [{
            "id": "diagnostic", "argv": [sys.executable, "-c", script], "kind": "command",
            "cache": True, "inputs": [str(Path(__file__).relative_to(ROOT))],
            "timeout": {"initial": initial, "maximum": maximum}, "memory_mib": 32,
        }]}
        return build_jobs(batch)

    def invoke(self, state, jobs, reason=None):
        records = []
        batch = run_batch(state, jobs, 2, 256, reason, records.append)
        return records[0], batch

    def test_skip_completed_and_require_reason_if_records_missing(self):
        jobs = self.job('print("stdout"); __import__("sys").stderr.write("stderr\\n")')
        with TemporaryDirectory() as folder:
            state = Path(folder)
            first, batch = self.invoke(state, jobs)
            self.assertEqual(first["status"], "command_ok")
            self.assertIn("stdout", Path(first["stdout"]).read_text())
            self.assertIn("stderr", Path(first["stderr"]).read_text())
            second, batch = self.invoke(state, jobs)
            self.assertEqual(second["status"], "cache_hit")
            self.assertEqual(batch["duplicates_avoided"], 1)
            Path(first["stdout"]).unlink()
            missing, _ = self.invoke(state, jobs)
            self.assertEqual(missing["status"], "evidence_missing")
            repeated, _ = self.invoke(state, jobs, "replace the missing stdout record")
            self.assertEqual(repeated["status"], "command_ok")

    def test_increase_timeout_then_skip_at_ceiling(self):
        jobs = self.job('print("starting", flush=True); __import__("time").sleep(10)', 0.10, 0.20)
        with TemporaryDirectory() as folder:
            state = Path(folder)
            first, batch = self.invoke(state, jobs)
            second, _ = self.invoke(state, jobs)
            self.assertEqual((first["status"], second["status"]), ("timeout", "timeout"))
            self.assertEqual(batch["timeout_rate"], 1)
            self.assertEqual((first["cap"], second["cap"]), (0.10, 0.20))
            self.assertIn("adaptive retry", read_json(Path(second["folder"]) / "request.json")["run_reason"])
            self.assertEqual(self.invoke(state, jobs)[0]["status"], "timeout_ceiling")

    def test_repeat_override_runs_one_copy_per_batch(self):
        job, = self.job('print("known control")')
        with TemporaryDirectory() as folder:
            records = []
            state = Path(folder)
            self.invoke(state, [job])
            batch = run_batch(state, [job, replace(job, name="alias")], 1, 256,
                              "remeasure the control under matched settings", records.append)
            self.assertEqual(batch["statuses"], {"command_ok": 1, "cache_hit": 1})
            self.assertEqual(batch["duplicates_avoided"], 1)

    def test_process_capture_can_cancel(self):
        cancel = Event()
        cancel.set()
        with TemporaryDirectory() as folder:
            result = run_logged([sys.executable, "-c", "import time; time.sleep(30)"], ROOT,
                                Path(folder), 30, cancel=cancel)
            self.assertTrue(result["interrupted"])
            self.assertFalse(result["timeout"])
            self.assertFalse(process_alive(read_json(Path(folder) / "process.json")["pid"]))
            self.assertTrue(process_alive(os.getpid()))

    def test_timeout_keeps_cleanup_messages_out_of_command_output(self):
        def stop_with_message(process, cleanup_log):
            cleanup_log.write_text("cleanup utility failed\n", encoding="utf-8")
            process.kill()

        with TemporaryDirectory() as folder, patch("common.kill_tree", side_effect=stop_with_message):
            result = run_logged([sys.executable, "-c",
                                 "import sys, time; print('command diagnostic', file=sys.stderr, flush=True); time.sleep(10)"],
                                ROOT, Path(folder), 0.8)
            self.assertTrue(result["timeout"])
            self.assertEqual(command_failure(result), "time limit reached\ncommand diagnostic")
            self.assertEqual(Path(result["cleanup"]).read_text().strip(), "cleanup utility failed")


class AdminTests(unittest.TestCase):
    def test_read_stop_before_sending_lease(self):
        with patch("ops.request", return_value=(200, b"stop")) as request:
            self.assertEqual(beat("secret")["status"], "upstream_stop")
            self.assertEqual(request.call_count, 1)
            self.assertNotIn("secret", request.call_args.args[0])

    def test_redacted_heartbeat_record(self):
        with TemporaryDirectory() as folder:
            state = Path(folder)
            path = state / "lease.json"
            path.write_text(json.dumps({"gap": {"id": "L-meta-1"}, "lease": {"id": "secret"}}))
            replies = [(404, b""), (200, b'{"lease":{"id":"secret","expires_at":"2026-11-26T12:00:00Z"}}')]
            with patch("ops.request", side_effect=replies):
                result = heartbeat(state, path, 240, once=True)
            self.assertEqual(result["status"], "renewed")
            self.assertNotIn("secret", (state / "desk/L-meta-1.jsonl").read_text())
            self.assertFalse((state / "desk/L-meta-1.watch.lock").exists())

    def test_normalize_a_text_file_only(self):
        with TemporaryDirectory() as folder:
            path = Path(folder) / "proof.lean"
            path.write_bytes("example : True := by\r\n  trivial\r\n".encode("utf-16"))
            # The normalizer used by the CLI expects workspace paths.
            with patch("ops.ROOT", Path(folder)):
                self.assertEqual(normalize([path]), ["proof.lean"])
                self.assertEqual(normalize([path]), [])
            self.assertEqual(path.read_bytes(), b"example : True := by\n  trivial\n")


if __name__ == "__main__":
    unittest.main()
