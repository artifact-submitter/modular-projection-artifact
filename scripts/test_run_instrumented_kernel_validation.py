#!/usr/bin/env python3
"""Unit tests for observational kernel-validation instrumentation."""

import unittest
from pathlib import Path
import tempfile
import json

from run_instrumented_kernel_validation import (
    OBSERVATION_LIMITATIONS,
    canonical_command,
    command_label,
    descendants,
    exact_stage_records,
    parse_ps,
    sha256_file,
    stage_completion,
    summarize_samples,
    validate_output_paths,
)


class InstrumentationTests(unittest.TestCase):
    def test_limitations_disclose_sampling_uncertainty(self):
        joined = " ".join(OBSERVATION_LIMITATIONS)
        self.assertIn("platform-dependent averages", joined)
        self.assertIn("decaying average", joined)
        self.assertIn("between samples", joined)
        self.assertIn("double-count", joined)
        self.assertIn("ten highest", joined)

    def test_parse_and_descendant_closure(self):
        processes = parse_ps(
            "10 1 0.1 100 00:01 python runner\n"
            "11 10 50.0 200 00:01 lake build\n"
            "12 11 99.0 300 00:01 lean /tmp/Example.lean\n"
            "13 1 75.0 400 00:01 unrelated\n"
        )
        self.assertEqual([p["pid"] for p in descendants(processes, 10)], [10, 11, 12])
        self.assertEqual(processes[1]["rss_bytes"], 200 * 1024)

    def test_summary_separates_stage_and_wall_from_cpu(self):
        samples = [{
            "stage": "moderate", "cpu_percent_sum": 200.0,
            "rss_bytes_sum": 1024, "process_count": 2,
            "top_processes": [{"command": "lake build", "cpu_percent": 100.0}],
        }, {
            "stage": "moderate", "cpu_percent_sum": 100.0,
            "rss_bytes_sum": 2048, "process_count": 1,
            "top_processes": [{"command": "lake build", "cpu_percent": 50.0}],
        }]
        summary = summarize_samples(samples, 5.0)
        self.assertEqual(summary["estimated_cpu_seconds"], 15.0)
        self.assertEqual(summary["peak_rss_bytes"], 2048)
        self.assertEqual(summary["sampled_stages"]["moderate"]["samples"], 2)
        self.assertEqual(summary["slowest_sampled_commands"][0]["label"], "lake build")

    def test_lean_source_is_the_bottleneck_label(self):
        self.assertEqual(
            command_label("lean /tmp/Counterexample.lean -o output"),
            "/tmp/Counterexample.lean",
        )

    def test_stream_hash_is_stable(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "samples.jsonl"
            path.write_bytes(b"{}\n")
            self.assertEqual(
                sha256_file(path),
                "sha256:ca3d163bab055381827226140568f3bef7eaac187cebd76878e0b63e9e442356",
            )

    def test_observations_cannot_precreate_proof_directory(self):
        with self.assertRaisesRegex(ValueError, "inside the proof-record"):
            validate_output_paths(
                Path("/tmp/proof"), Path("/tmp/proof/metrics.json"),
                Path("/tmp/samples.jsonl"),
            )
        with self.assertRaisesRegex(ValueError, "distinct"):
            validate_output_paths(
                Path("/tmp/proof"), Path("/tmp/metrics.json"),
                Path("/tmp/metrics.json"),
            )

    def test_canonical_runner_argv_is_unchanged(self):
        self.assertEqual(
            canonical_command(Path("/tmp/proof")),
            ["python3", "scripts/kernel_stage_receipt.py", "run-all",
             "--output-dir", "/tmp/proof"],
        )
        self.assertEqual(
            canonical_command(Path("/tmp/proof"), Path("/tmp/prior"))[-2:],
            ["--reuse-from", "/tmp/prior"],
        )

    def test_exact_stage_records_preserve_cache_and_threads(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            stage = root / "0-evidence"
            stage.mkdir()
            (stage / "stage-receipt.json").write_text(json.dumps({
                "execution": {
                    "started_utc": "2026-09-15T00:00:00Z",
                    "finished_utc": "2026-09-15T00:00:02Z",
                    "exit_code": 0,
                    "log": {"size_bytes": 17},
                },
                "cache": {
                    "policy": "local-project-cache",
                    "requested_key": "local:.lake/build",
                    "restored_key": "local:.lake/build",
                },
                "context": {"environment": {"LEAN_NUM_THREADS": "2"}},
            }), encoding="utf-8")
            (stage / "stage-selection.json").write_text(json.dumps({
                "disposition": "reused",
            }), encoding="utf-8")
            record = exact_stage_records(root)[0]
            self.assertIsNone(record["wall_seconds"])
            self.assertEqual(record["original_execution_wall_seconds"], 2.0)
            self.assertEqual(record["disposition"], "reused")
            self.assertEqual(record["cache"]["restored_key"], "local:.lake/build")
            self.assertEqual(record["lean_num_threads"], "2")

    def test_stage_completion_names_missing_stages(self):
        completion = stage_completion([{"name": "evidence"}, {"name": "moderate"}])
        self.assertEqual(completion["completed_stages"], ["evidence", "moderate"])
        self.assertEqual(
            completion["incomplete_stages"],
            ["ternary-upper", "library", "complete"],
        )

    def test_missing_selection_is_not_mislabeled_as_executed(self):
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory) / "0-evidence"
            stage.mkdir()
            (stage / "stage-receipt.json").write_text(json.dumps({
                "execution": {
                    "started_utc": "2026-09-15T00:00:00Z",
                    "finished_utc": "2026-09-15T00:00:02Z",
                    "exit_code": 0,
                    "log": {"size_bytes": 0},
                },
                "cache": {},
                "context": {"environment": {"LEAN_NUM_THREADS": "2"}},
            }), encoding="utf-8")
            record = exact_stage_records(Path(directory))[0]
            self.assertEqual(record["disposition"], "unknown")
            self.assertIsNone(record["wall_seconds"])


if __name__ == "__main__":
    unittest.main()
