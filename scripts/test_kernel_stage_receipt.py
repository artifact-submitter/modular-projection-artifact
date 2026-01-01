#!/usr/bin/env python3

from __future__ import annotations

import copy
import io
import json
import os
from pathlib import Path
import py_compile
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

from compute_replay_digest import ROOT, canonical_digest, import_graph, tracked_sources
from kernel_stage_receipt import (
    DEFAULT_LEAN_NUM_THREADS,
    DEFAULT_LEAN_GC_THRESHOLD,
    LOG_NAME,
    PLAN_BY_NAME,
    EXECUTION_RECORD_NAME,
    RECEIPT_NAME,
    REPLAY_ENV_KEYS,
    SELECTION_NAME,
    SOURCE_IDENTITY_NAME,
    STAGE_PLAN,
    TOOL_COMMANDS,
    aggregate_digest,
    collect_stage_context,
    compute_stage_identities,
    create_stage_receipt,
    load_reuse_candidates,
    load_execution_receipt_tree,
    make_stage_selection,
    read_json,
    require_no_ignored_stage_sources,
    require_disjoint_trees,
    require_regular_stage_inputs,
    resolved_tool_identity,
    receipt_digest,
    run_and_stream,
    run_all_cli,
    run_fixed_stage,
    selection_digest,
    source_execution_context,
    stage_identity_from_paths,
    stage_input_paths,
    verify_run,
    verify_run_cli,
)


COMMIT = "a" * 40
RUN = {
    "repository": "example/CertifiedJL",
    "workflow": "Kernel proof record",
    "run_id": "1234",
    "run_attempt": "1",
    "commit": COMMIT,
}


def source_identity() -> dict:
    proof = "sha256:" + "1" * 64
    procedure = "sha256:" + "2" * 64
    metadata = "sha256:" + "3" * 64
    complete = canonical_digest("CertifiedJL-validation-inputs-v2", {
        "mode": "kernel",
        "proof_closure_digest": proof,
        "validation_procedure_digest": procedure,
        "metadata_digest": metadata,
    })
    return {
        "schema_version": 2,
        "identity_kind": "source-inputs",
        "attests_execution": False,
        "mode": "kernel",
        "source_commit": COMMIT,
        "source_tree_digest": "sha256:" + "4" * 64,
        "proof_closure_digest": proof,
        "validation_procedure_digest": procedure,
        "metadata_digest": metadata,
        "validation_digest": complete,
        "digest": complete,
    }


def stage_context() -> dict:
    source = source_execution_context()
    verified = [{
        "name": dependency["name"],
        "type": "git",
        "expected_url": dependency["url"],
        "actual_url": dependency["url"],
        "expected_revision": dependency["rev"],
        "actual_revision": dependency["rev"],
        "status_sha256": "e3b0c44298fc1c149afbf4c8996fb924"
            "27ae41e4649b934ca495991b7852b855",
    } for dependency in source["dependencies"]]
    tools = {}
    for index, name in enumerate(TOOL_COMMANDS):
        tool = {
            "invocation_path": f"/fixture/bin/{name}",
            "resolved_path": f"/fixture/tools/{name}",
            "sha256": "sha256:" + format(index + 5, "064x"),
        }
        if TOOL_COMMANDS[name][1] is not None:
            tool["version"] = f"{name} fixture version"
        if name in {"lean", "lake"}:
            tool["selected_toolchain"] = {
                "path": f"/fixture/toolchains/{name}",
                "sha256": "sha256:" + format(index + 100, "064x"),
            }
        tools[name] = tool
    return {
        **source,
        "environment": {key: "" for key in REPLAY_ENV_KEYS} | {
            "CERTIFIEDJL_MODERATE_BATCH_SIZE": "2",
            "CERTIFIEDJL_SPARSE_LOWER_BATCH_SIZE": "1",
            "CERTIFIEDJL_SPARSE_UPPER_CONTOUR_BATCH_SIZE": "all",
            "CI": "true",
            "LEAN_GC_THRESHOLD": DEFAULT_LEAN_GC_THRESHOLD,
            "PATH": "/fixture/bin",
        },
        "runner": {"os": "Linux", "arch": "X64"},
        "tools": tools,
        "verified_dependencies": verified,
    }


def stage_cache() -> dict[str, str]:
    return {
        "policy": "github-actions-kernel",
        "requested_key": "v6-mode-kernel-proof-record-Linux-X64-fixture",
        "restored_key": "v6-mode-kernel-proof-record-Linux-X64-previous",
    }


def stage_identity(stage) -> dict:
    inputs = "sha256:" + format(stage.index + 1, "064x")
    record = {
        "stage": {"index": stage.index, "name": stage.name, "script": stage.script},
        "input_count": stage.index + 1,
        "inputs_digest": inputs,
    }
    record["digest"] = canonical_digest("CertifiedJL-kernel-stage-inputs-v1", record)
    return record


def stage_identities() -> dict:
    return {stage.name: stage_identity(stage) for stage in STAGE_PLAN}


class KernelStageReceiptTests(unittest.TestCase):
    def test_stage_closures_are_tracked_and_materially_finer_than_git_tree(self):
        tracked = tracked_sources()
        graph = import_graph(tracked)
        inputs = {
            stage.name: stage_input_paths(stage, tracked=tracked, graph=graph)
            for stage in STAGE_PLAN
        }
        readme = ROOT / "README.md"
        self.assertIn(readme, tracked)
        self.assertTrue(all(readme in paths for paths in inputs.values()))
        self.assertIn(ROOT / "CONTRIBUTING.md", inputs["evidence"])
        common_script = ROOT / "scripts/kernel_stage_receipt.py"
        self.assertTrue(all(common_script in paths for paths in inputs.values()))
        self.assertIn(ROOT / "Makefile", inputs["evidence"])
        paper_source = ROOT / "paper/sections/certified-jl/abstract.tex"
        self.assertIn(paper_source, inputs["evidence"])
        self.assertTrue(all(
            paper_source not in inputs[stage.name] for stage in STAGE_PLAN[1:]
        ))
        moderate_cell = ROOT / (
            "CertifiedJL/Certificates/Families/OneRow975/NormalApproximation/"
            "Replay/CertificateProofs/Cell000.lean"
        )
        self.assertIn(moderate_cell, inputs["moderate"])
        self.assertNotIn(moderate_cell, inputs["ternary-upper"])
        dynamic_shard = next(path for path in tracked if (
            "L2Upper/ContourFamily/Replay" in path.as_posix()
            and path.name.startswith("Shard") and path.suffix == ".lean"
        ))
        self.assertIn(dynamic_shard, inputs["ternary-upper"])
        self.assertIn(ROOT / "CertifiedJL/Tests/SparseUpperContourFamilyFixture.lean",
                      inputs["ternary-upper"])
        self.assertIn(ROOT / "paper/artifact/upper-gap/verify_U338.py",
                      inputs["ternary-upper"])

    def test_stage_digest_ignores_unrelated_file_and_changes_for_bound_input(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            bound = root / "bound.txt"
            unrelated = root / "unrelated.txt"
            bound.write_text("one", encoding="utf-8")
            unrelated.write_text("one", encoding="utf-8")
            stage = STAGE_PLAN[1]
            original = stage_identity_from_paths(stage, {bound}, root=root)
            unrelated.write_text("two", encoding="utf-8")
            self.assertEqual(original, stage_identity_from_paths(stage, {bound}, root=root))
            bound.write_text("two", encoding="utf-8")
            self.assertNotEqual(original, stage_identity_from_paths(stage, {bound}, root=root))
            contributing = root / "CONTRIBUTING.md"
            contributing.write_bytes((ROOT / "CONTRIBUTING.md").read_bytes())
            evidence_before = stage_identity_from_paths(
                STAGE_PLAN[0], {contributing}, root=root,
            )
            contributing.write_text("changed contributor policy\n", encoding="utf-8")
            self.assertNotEqual(evidence_before, stage_identity_from_paths(
                STAGE_PLAN[0], {contributing}, root=root,
            ))

    def test_ignored_sources_and_symlinked_inputs_are_rejected(self):
        for ignored in (
            b"CertifiedJL/Generated/Shard99.lean\0",
            b"evidence/ignored-manifest.toml\0",
            b".github/ignored-policy.json\0",
        ):
            with self.subTest(ignored=ignored), mock.patch(
                "kernel_stage_receipt.subprocess.check_output", return_value=ignored,
            ):
                with self.assertRaisesRegex(ValueError, "ignored source files"):
                    require_no_ignored_stage_sources()
        with mock.patch(
            "kernel_stage_receipt.subprocess.check_output",
            return_value=b"scripts/__pycache__/unchecked.cpython-311.pyc\0",
        ):
            require_no_ignored_stage_sources()
        target = self.root / "target.txt"
        link = self.root / "input.txt"
        target.write_text("payload", encoding="utf-8")
        link.symlink_to(target)
        with self.assertRaisesRegex(ValueError, "tracked regular file"):
            require_regular_stage_inputs({link}, self.root)

    def test_collected_context_records_effective_thread_default(self):
        with (
            mock.patch("kernel_stage_receipt.source_execution_context", return_value={}),
            mock.patch("kernel_stage_receipt.verified_dependencies", return_value=()),
            mock.patch("kernel_stage_receipt.resolved_tool_identity", return_value={
                "invocation_path": "/fixture/tool",
                "resolved_path": "/fixture/tool", "sha256": "sha256:" + "0" * 64,
                "version": "fixture",
            }),
            mock.patch("kernel_stage_receipt.selected_elan_tool_identity", return_value={
                "path": "/fixture/selected", "sha256": "sha256:" + "1" * 64,
            }),
        ):
            default = collect_stage_context(
                runner_os="Linux", runner_arch="X64", environ={}
            )
            empty = collect_stage_context(
                runner_os="Linux",
                runner_arch="X64",
                environ={"LEAN_NUM_THREADS": ""},
            )
            overridden = collect_stage_context(
                runner_os="Linux",
                runner_arch="X64",
                environ={"LEAN_NUM_THREADS": "4"},
            )
        self.assertEqual(
            default["environment"]["LEAN_NUM_THREADS"], DEFAULT_LEAN_NUM_THREADS
        )
        self.assertEqual(
            empty["environment"]["LEAN_NUM_THREADS"], DEFAULT_LEAN_NUM_THREADS
        )
        self.assertEqual(overridden["environment"]["LEAN_NUM_THREADS"], "4")
        self.assertEqual(default["environment"]["LEAN_GC_THRESHOLD"],
                         DEFAULT_LEAN_GC_THRESHOLD)
        with mock.patch("kernel_stage_receipt.source_execution_context", return_value={}), \
             mock.patch("kernel_stage_receipt.verified_dependencies", return_value=()), \
             mock.patch("kernel_stage_receipt.resolved_tool_identity", return_value={
                 "invocation_path": "/fixture/tool",
                 "resolved_path": "/fixture/tool", "sha256": "sha256:" + "0" * 64,
                 "version": "fixture",
             }), \
             mock.patch("kernel_stage_receipt.selected_elan_tool_identity", return_value={
                 "path": "/fixture/selected", "sha256": "sha256:" + "1" * 64,
             }):
            gc_overridden = collect_stage_context(
                runner_os="Linux", runner_arch="X64",
                environ={"LEAN_GC_THRESHOLD": "4096"},
            )
        self.assertEqual(gc_overridden["environment"]["LEAN_GC_THRESHOLD"], "4096")

    def test_path_and_resolved_timeout_identity_prevent_fake_tool_reuse(self):
        with tempfile.TemporaryDirectory() as directory:
            fake_dir = Path(directory)
            fake_timeout = fake_dir / "timeout"
            fake_timeout.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_timeout.chmod(0o755)
            base_path = os.environ["PATH"]
            with (
                mock.patch("kernel_stage_receipt.source_execution_context", return_value={}),
                mock.patch("kernel_stage_receipt.verified_dependencies", return_value=()),
                mock.patch("kernel_stage_receipt.command_output", return_value="fixture"),
                mock.patch("kernel_stage_receipt.selected_elan_tool_identity", return_value={
                    "path": "/fixture/selected",
                    "sha256": "sha256:" + "1" * 64,
                }),
            ):
                normal = collect_stage_context(
                    runner_os="Linux", runner_arch="X64", environ={"PATH": base_path}
                )
                fake = collect_stage_context(
                    runner_os="Linux", runner_arch="X64",
                    environ={"PATH": f"{fake_dir}:{base_path}"},
                )
            self.assertNotEqual(normal["environment"]["PATH"], fake["environment"]["PATH"])
            self.assertNotEqual(normal["tools"]["timeout"], fake["tools"]["timeout"])
            prior = self.materialize(self.chain()[:1], "fake-timeout")
            fake_context = copy.deepcopy(self.context)
            fake_context["environment"]["PATH"] = fake["environment"]["PATH"]
            fake_context["tools"]["timeout"] = fake["tools"]["timeout"]
            self.assertNotIn("evidence", load_reuse_candidates(
                prior, stage_identities=stage_identities(), context=fake_context,
            ))

    def test_tool_identity_preserves_multicall_shim_and_selected_binary(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            multicall = root / "elan-init"
            multicall.write_text(
                "#!/bin/sh\nprintf '%s version\\n' \"${0##*/}\"\n", encoding="utf-8",
            )
            multicall.chmod(0o755)
            lean = root / "lean"
            lean.symlink_to(multicall)
            identity = resolved_tool_identity(
                "lean", ("--version",), search_path=str(root),
                environ={"PATH": str(root)},
            )
            self.assertEqual(identity["invocation_path"], str(lean))
            self.assertEqual(identity["resolved_path"], str(multicall.resolve()))
            self.assertEqual(identity["version"], "lean version")

            selected_a = root / "toolchain-a-lean"
            selected_b = root / "toolchain-b-lean"
            selected_a.write_bytes(b"compiler a")
            selected_b.write_bytes(b"compiler b")
            with mock.patch(
                "kernel_stage_receipt.command_output",
                side_effect=(str(selected_a), str(selected_b)),
            ):
                from kernel_stage_receipt import selected_elan_tool_identity
                first = selected_elan_tool_identity(
                    "lean", elan_invocation=str(multicall), environ={},
                )
                second = selected_elan_tool_identity(
                    "lean", elan_invocation=str(multicall), environ={},
                )
            self.assertNotEqual(first, second)

    def test_kernel_entrypoint_isolates_python_bytecode_before_local_imports(self):
        source_caches = list((ROOT / "scripts").glob("**/*.pyc"))
        before = {path: path.stat().st_mtime_ns for path in source_caches}
        forced_source_prefix = ROOT / "scripts/forced-source-pycache"
        environment = os.environ.copy()
        environment["PYTHONDONTWRITEBYTECODE"] = "0"
        environment["PYTHONPYCACHEPREFIX"] = str(forced_source_prefix)
        result = subprocess.run(
            [sys.executable, "-B", str(ROOT / "scripts/kernel_stage_receipt.py"), "--help"],
            cwd=ROOT, env=environment, text=True, capture_output=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(forced_source_prefix.exists())
        self.assertEqual(
            before,
            {path: path.stat().st_mtime_ns for path in (ROOT / "scripts").glob("**/*.pyc")},
        )

    def test_workflow_precheck_bytecode_is_irrelevant_under_isolated_runner(self):
        cache_dir = ROOT / "scripts/__pycache__"
        cache_dir.mkdir(exist_ok=True)
        bytecode = cache_dir / "check_dependency_cache.workflow-unchecked.pyc"
        try:
            py_compile.compile(
                str(ROOT / "scripts/check_dependency_cache.py"),
                cfile=str(bytecode), doraise=True,
                invalidation_mode=py_compile.PycInvalidationMode.UNCHECKED_HASH,
            )
            self.assertTrue(bytecode.is_file())
            with tempfile.TemporaryDirectory() as directory:
                prefix = Path(directory) / "fresh-external-prefix"
                environment = os.environ.copy()
                environment["PYTHONDONTWRITEBYTECODE"] = "1"
                environment["PYTHONPYCACHEPREFIX"] = str(prefix)
                result = subprocess.run(
                    [
                        sys.executable, "-B", "-c",
                        "import sys; sys.path.insert(0, 'scripts'); "
                        "import kernel_stage_receipt as k; "
                        "k.require_python_cache_isolation(); "
                        "k.require_clean_source = lambda: None; "
                        "assert len(k.compute_stage_identities()) == len(k.STAGE_PLAN)",
                    ],
                    cwd=ROOT, env=environment, text=True, capture_output=True,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertFalse(prefix.exists())
        finally:
            bytecode.unlink(missing_ok=True)
            try:
                cache_dir.rmdir()
            except OSError:
                pass

    def setUp(self) -> None:
        isolation = mock.patch("kernel_stage_receipt.require_python_cache_isolation")
        isolation.start()
        self.addCleanup(isolation.stop)
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.identity = source_identity()
        self.context = stage_context()
        self.chain_count = 0

    def chain(self, *, last_exit: int = 0):
        chain_root = self.root / f"chain-{self.chain_count}"
        self.chain_count += 1
        receipts = []
        previous = None
        previous_log = None
        for stage in STAGE_PLAN:
            directory = chain_root / stage.name
            directory.mkdir(parents=True)
            log = directory / LOG_NAME
            log.write_text(f"{stage.name} completed\n", encoding="utf-8")
            receipt = create_stage_receipt(
                identity_before=self.identity,
                identity_after=self.identity,
                repository=RUN["repository"],
                workflow=RUN["workflow"],
                run_id=RUN["run_id"],
                run_attempt=RUN["run_attempt"],
                commit=RUN["commit"],
                name=stage.name,
                index=stage.index,
                script=stage.script,
                timeout_minutes=stage.timeout_minutes,
                started_utc=f"2026-09-05T12:0{stage.index}:00Z",
                finished_utc=f"2026-09-05T12:0{stage.index}:01Z",
                exit_code=last_exit if stage.index == len(STAGE_PLAN) - 1 else 0,
                log_path=log,
                context=self.context,
                cache=stage_cache(),
                stage_identity=stage_identity(stage),
                previous_receipt=previous,
                previous_log=previous_log,
            )
            receipts.append((receipt, log))
            previous, previous_log = receipt, log
        return receipts

    def verify(self, receipts):
        return verify_run(
            receipts=receipts,
            current_identity=self.identity,
            repository=RUN["repository"],
            workflow=RUN["workflow"],
            run_id=RUN["run_id"],
            run_attempt=RUN["run_attempt"],
            commit=RUN["commit"],
            current_stage_identities=stage_identities(),
            current_context=self.context,
        )

    def materialize(self, receipts, name="prior"):
        root = self.root / name
        root.mkdir()
        for stage, (receipt, log) in zip(STAGE_PLAN, receipts, strict=False):
            directory = root / f"{stage.index}-{stage.name}"
            directory.mkdir()
            (directory / RECEIPT_NAME).write_text(json.dumps(receipt), encoding="utf-8")
            (directory / LOG_NAME).write_bytes(log.read_bytes())
            selection = make_stage_selection(
                stage=stage, disposition="executed", receipt=receipt,
                assembly_run={
                    "repository": RUN["repository"], "workflow": RUN["workflow"],
                    "run_id": RUN["run_id"], "run_attempt": RUN["run_attempt"],
                    "source_commit": RUN["commit"],
                },
                current_identity=self.identity,
            )
            (directory / SELECTION_NAME).write_text(json.dumps(selection), encoding="utf-8")
        return root

    def resign(self, receipt):
        receipt["receipt_digest"] = receipt_digest(receipt)

    def test_valid_five_stage_chain_attests_execution(self):
        record = self.verify(self.chain())
        self.assertTrue(record["attests_execution"])
        self.assertTrue(record["success"])
        self.assertEqual(len(record["stage_receipts"]), 5)
        self.assertEqual(record["source_identity"], self.identity)
        self.assertEqual(record["assembly_run"]["source_commit"], RUN["commit"])
        self.assertEqual(
            [item["disposition"] for item in record["stage_selections"]],
            ["executed"] * len(STAGE_PLAN),
        )
        self.assertTrue(record["execution_digest"].startswith("sha256:"))

    def test_mixed_origin_final_record_keeps_execution_and_assembly_provenance(self):
        chain = self.chain()
        old_commit = "b" * 40
        old_identity = copy.deepcopy(chain[0][0]["source_identity"])
        old_identity["source_commit"] = old_commit
        chain[0][0]["source_identity"] = old_identity
        chain[0][0]["run"]["source_commit"] = old_commit
        self.resign(chain[0][0])
        dispositions = {stage.name: "executed" for stage in STAGE_PLAN}
        dispositions = {stage.name: "reused" for stage in STAGE_PLAN}
        record = verify_run(
            receipts=chain, current_identity=self.identity,
            repository=RUN["repository"], workflow=RUN["workflow"],
            run_id=RUN["run_id"], run_attempt=RUN["run_attempt"],
            commit=RUN["commit"], current_stage_identities=stage_identities(),
            current_context=self.context, dispositions=dispositions,
        )
        self.assertEqual(record["assembly_run"]["source_commit"], RUN["commit"])
        self.assertEqual(record["stage_selections"][0]["disposition"], "reused")
        self.assertEqual(record["stage_selections"][0]["execution_run"]["source_commit"],
                         old_commit)

    def test_python_runner_captures_log_and_real_exit_code(self):
        log = self.root / "runner.log"
        output = io.BytesIO()
        exit_code = run_and_stream(
            [sys.executable, "-c", "import sys; print('observed'); sys.exit(7)"],
            cwd=self.root,
            log_path=log,
            output=output,
        )
        self.assertEqual(exit_code, 7)
        self.assertEqual(log.read_bytes(), b"observed\n")
        self.assertEqual(output.getvalue(), b"observed\n")

    def test_python_runner_terminates_process_group_on_stream_error(self):
        pid_file = self.root / "child.pid"
        code = (
            "import pathlib, subprocess, sys, time; "
            f"p=subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
            f"pathlib.Path({str(pid_file)!r}).write_text(str(p.pid)); "
            "print('ready', flush=True); time.sleep(60)"
        )

        class BrokenSink:
            def write(self, _chunk):
                raise RuntimeError("synthetic stream failure")

            def flush(self):
                pass

        with self.assertRaisesRegex(RuntimeError, "synthetic stream failure"):
            run_and_stream(
                [sys.executable, "-c", code], cwd=self.root,
                log_path=self.root / "interrupted.log", output=BrokenSink(),
            )
        child_pid = int(pid_file.read_text(encoding="utf-8"))
        for _ in range(40):
            try:
                status = subprocess.check_output(
                    ["ps", "-o", "stat=", "-p", str(child_pid)], text=True,
                ).strip()
            except subprocess.CalledProcessError:
                break
            if not status or status.startswith("Z"):
                break
            time.sleep(0.05)
        else:
            self.fail("stage descendant survived stream failure")

    def test_missing_or_duplicate_stage_is_rejected(self):
        chain = self.chain()
        for changed in (chain[:-1], chain + [chain[-1]]):
            with self.subTest(count=len(changed)), self.assertRaises(ValueError):
                self.verify(changed)

    def test_failed_stage_is_a_diagnostic_not_a_success_record(self):
        chain = self.chain(last_exit=124)
        self.assertTrue(chain[-1][0]["attests_execution"])
        self.assertFalse(chain[-1][0]["success"])
        with self.assertRaisesRegex(ValueError, "failed stage"):
            self.verify(chain)

    def test_mixed_run_attempt_or_commit_is_rejected(self):
        for field, value in (("run_id", "other"), ("run_attempt", "2"),
                             ("source_commit", "b" * 40)):
            with self.subTest(field=field):
                chain = self.chain()
                chain[-1][0]["run"][field] = value
                self.resign(chain[-1][0])
                with self.assertRaises(ValueError):
                    self.verify(chain)

    def test_wrong_stage_or_command_is_rejected(self):
        for mutation in ("stage", "command"):
            with self.subTest(mutation=mutation):
                chain = self.chain()
                if mutation == "stage":
                    chain[2][0]["stage"]["index"] = 3
                else:
                    chain[2][0]["execution"]["command"][-1] = "./scripts/other.sh"
                self.resign(chain[2][0])
                with self.assertRaises(ValueError):
                    self.verify(chain)

    def test_broken_executed_predecessor_chain_is_rejected(self):
        chain = self.chain()
        chain[3][0]["previous_receipt_digest"] = "sha256:" + "0" * 64
        self.resign(chain[3][0])
        with self.assertRaisesRegex(ValueError, "predecessor"):
            self.verify(chain)

    def test_aggregate_does_not_reinterpret_reused_historical_chain(self):
        chain = self.chain()
        chain[3][0]["previous_receipt_digest"] = "sha256:" + "0" * 64
        self.resign(chain[3][0])
        dispositions = {stage.name: "executed" for stage in STAGE_PLAN}
        dispositions["library"] = "reused"
        dispositions["complete"] = "reused"
        record = verify_run(
            receipts=chain, current_identity=self.identity,
            repository=RUN["repository"], workflow=RUN["workflow"],
            run_id=RUN["run_id"], run_attempt=RUN["run_attempt"],
            commit=RUN["commit"], current_stage_identities=stage_identities(),
            current_context=self.context, dispositions=dispositions,
        )
        self.assertEqual(record["stage_receipts"][3]["previous_receipt_digest"],
                         "sha256:" + "0" * 64)

    def test_log_content_is_bound(self):
        chain = self.chain()
        chain[1][1].write_text("changed\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "log"):
            self.verify(chain)

    def test_receipt_digest_is_bound(self):
        chain = self.chain()
        chain[0][0]["receipt_digest"] = "sha256:" + "0" * 64
        with self.assertRaisesRegex(ValueError, "receipt digest"):
            self.verify(chain)

    def test_mixed_environment_tools_or_dependencies_are_rejected(self):
        for component in ("environment", "tools", "dependencies", "verified_dependencies"):
            with self.subTest(component=component):
                chain = self.chain()
                changed = chain[-1][0]["context"]
                if component == "environment":
                    changed[component]["CERTIFIEDJL_SPARSE_LOWER_BATCH_SIZE"] = "9"
                elif component == "tools":
                    changed[component]["lean"] = "different Lean"
                elif component == "dependencies":
                    changed[component] = copy.deepcopy(changed[component]) + [
                        {"name": "unexpected", "rev": "different"}
                    ]
                else:
                    changed[component][0]["actual_revision"] = "different"
                self.resign(chain[-1][0])
                with self.assertRaises(ValueError):
                    self.verify(chain)

    def test_duplicate_dependency_names_are_rejected(self):
        chain = self.chain()
        observed = chain[-1][0]["context"]["verified_dependencies"]
        observed[-1] = copy.deepcopy(observed[0])
        self.resign(chain[-1][0])
        with self.assertRaisesRegex(ValueError, "unique"):
            self.verify(chain)

    def test_boolean_integer_and_nonstring_environment_are_rejected(self):
        mutations = (
            lambda receipt: receipt.__setitem__("schema_version", True),
            lambda receipt: receipt["stage"].__setitem__("index", False),
            lambda receipt: receipt["execution"].__setitem__("timeout_minutes", True),
            lambda receipt: receipt["execution"].__setitem__("exit_code", False),
            lambda receipt: receipt["execution"]["log"].__setitem__("size_bytes", False),
            lambda receipt: receipt["context"]["environment"].__setitem__("LEAN_OPTS", 0),
        )
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                chain = self.chain()
                mutate(chain[-1][0])
                self.resign(chain[-1][0])
                with self.assertRaises(ValueError):
                    self.verify(chain)

    def test_wrong_cache_namespace_is_rejected(self):
        chain = self.chain()
        chain[-1][0]["cache"]["restored_key"] = "v4-mode-fast-untrusted"
        self.resign(chain[-1][0])
        with self.assertRaisesRegex(ValueError, "cache"):
            self.verify(chain)

    def test_source_identity_change_or_success_claim_is_rejected(self):
        for field, value in (("source_tree_digest", "malformed"),
                             ("attests_execution", True)):
            with self.subTest(field=field):
                chain = self.chain()
                chain[-1][0]["source_identity"][field] = value
                self.resign(chain[-1][0])
                with self.assertRaises(ValueError):
                    self.verify(chain)

    def test_new_stage_rejects_mixed_context_and_failed_predecessor(self):
        chain = self.chain()
        stage = STAGE_PLAN[-1]
        for mutation in ("context", "failed"):
            with self.subTest(mutation=mutation):
                previous = copy.deepcopy(chain[-2][0])
                if mutation == "context":
                    previous["context"]["tools"]["lean"] = "other Lean"
                else:
                    previous["success"] = False
                    previous["execution"]["exit_code"] = 1
                self.resign(previous)
                with self.assertRaises(ValueError):
                    create_stage_receipt(
                        identity_before=self.identity,
                        identity_after=self.identity,
                        repository=RUN["repository"], workflow=RUN["workflow"],
                        run_id=RUN["run_id"], run_attempt=RUN["run_attempt"],
                        commit=RUN["commit"], name=stage.name, index=stage.index,
                        script=stage.script, timeout_minutes=stage.timeout_minutes,
                        started_utc="2026-09-05T13:00:00Z",
                        finished_utc="2026-09-05T13:00:01Z", exit_code=0,
                        log_path=chain[-1][1], context=self.context,
                        cache=stage_cache(),
                        stage_identity=stage_identity(stage),
                        previous_receipt=previous, previous_log=chain[-2][1],
                    )

    def test_stage_artifact_paths_are_immutable_and_distinct(self):
        existing = self.root / "existing.log"
        existing.write_text("old", encoding="utf-8")
        common = dict(
            repository=RUN["repository"], workflow=RUN["workflow"],
            run_id=RUN["run_id"], run_attempt=RUN["run_attempt"],
            commit=RUN["commit"], name="evidence", index=0,
            script=STAGE_PLAN[0].script,
            timeout_minutes=STAGE_PLAN[0].timeout_minutes,
            runner_os="Linux", runner_arch="X64",
            cache_policy="local-project-cache",
            cache_requested_key="local:.lake/build", cache_restored_key="",
        )
        with self.assertRaisesRegex(ValueError, "already exists"):
            run_fixed_stage(
                **common, log_path=existing, output=self.root / "new.json",
            )
        same = self.root / "same"
        with self.assertRaisesRegex(ValueError, "overlaps"):
            run_fixed_stage(**common, log_path=same, output=same)

    def test_reuse_and_output_trees_must_not_overlap(self):
        reuse = self.root / "prior"
        reuse.mkdir()
        for first, second in (
            (reuse / "new-output", reuse),
            (reuse, reuse / "nested-source"),
        ):
            with self.subTest(first=first, second=second), self.assertRaisesRegex(
                ValueError, "must not overlap"
            ):
                require_disjoint_trees(first, second)
        args = mock.Mock(output_dir=reuse / "new-output", reuse_from=reuse)
        with (
            mock.patch("kernel_stage_receipt.compute_kernel_identity") as compute,
            self.assertRaisesRegex(ValueError, "must not overlap"),
        ):
            run_all_cli(args)
        compute.assert_not_called()

    def test_verify_cli_recomputes_checkout_identity(self):
        chain = self.chain()
        receipts_dir = self.root / "receipts"
        for stage, (receipt, log) in zip(STAGE_PLAN, chain, strict=True):
            directory = receipts_dir / (
                f"kernel-proof-stage-{RUN['run_id']}-{RUN['run_attempt']}-{stage.name}"
            )
            directory.mkdir(parents=True)
            (directory / RECEIPT_NAME).write_text(
                json.dumps(receipt), encoding="utf-8",
            )
            (directory / LOG_NAME).write_bytes(log.read_bytes())
        identity_path = self.root / "identity.json"
        identity_path.write_text(json.dumps(self.identity), encoding="utf-8")
        args = mock.Mock(
            identity=identity_path, receipts_dir=receipts_dir,
            output=self.root / "record.json", repository=RUN["repository"],
            workflow=RUN["workflow"], run_id=RUN["run_id"],
            run_attempt=RUN["run_attempt"], commit=RUN["commit"],
        )
        changed = copy.deepcopy(self.identity)
        changed["source_commit"] = "b" * 40
        with mock.patch("kernel_stage_receipt.compute_kernel_identity", return_value=changed):
            with self.assertRaises(ValueError):
                verify_run_cli(args)
        with (
            mock.patch("kernel_stage_receipt.compute_kernel_identity", return_value=self.identity),
            mock.patch("kernel_stage_receipt.compute_stage_identities", return_value=stage_identities()),
            mock.patch("kernel_stage_receipt.collect_stage_context", return_value=self.context),
        ):
            verify_run_cli(args)
        self.assertTrue(args.output.is_file())

    def test_verify_receipt_tree_rejects_unrelated_entries(self):
        receipts_dir = self.root / "strict-receipts"
        chain = self.chain()
        for stage, (receipt, log) in zip(STAGE_PLAN, chain, strict=True):
            directory = receipts_dir / (
                f"kernel-proof-stage-{RUN['run_id']}-{RUN['run_attempt']}-{stage.name}"
            )
            directory.mkdir(parents=True)
            (directory / RECEIPT_NAME).write_text(json.dumps(receipt), encoding="utf-8")
            (directory / LOG_NAME).write_bytes(log.read_bytes())
        self.assertEqual(len(load_execution_receipt_tree(
            receipts_dir, run_id=RUN["run_id"], run_attempt=RUN["run_attempt"],
        )), len(STAGE_PLAN))
        (receipts_dir / "unrelated.txt").write_text("no", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "extra or missing"):
            load_execution_receipt_tree(
                receipts_dir, run_id=RUN["run_id"], run_attempt=RUN["run_attempt"],
            )

    def test_run_all_orchestrates_fixed_chain_and_finalizes_only_success(self):
        fixtures = {receipt["stage"]["name"]: (receipt, log)
                    for receipt, log in self.chain()}

        def fake_stage(**kwargs):
            receipt, log = fixtures[kwargs["name"]]
            kwargs["log_path"].write_bytes(log.read_bytes())
            kwargs["output"].write_text(json.dumps(receipt), encoding="utf-8")
            return 0

        args = mock.Mock(
            output_dir=self.root / "all-success",
            repository=RUN["repository"], workflow=RUN["workflow"],
            run_id=RUN["run_id"], run_attempt=RUN["run_attempt"],
            commit=RUN["commit"], runner_os="Linux", runner_arch="X64",
        )
        with mock.patch("kernel_stage_receipt.run_fixed_stage", side_effect=fake_stage) as run:
            with (
                mock.patch("kernel_stage_receipt.compute_kernel_identity", return_value=self.identity),
                mock.patch("kernel_stage_receipt.compute_stage_identities", return_value=stage_identities()),
                mock.patch("kernel_stage_receipt.collect_stage_context", return_value=self.context),
                mock.patch("kernel_stage_receipt.verify_run", return_value={"success": True}),
            ):
                self.assertEqual(run_all_cli(args), 0)
        self.assertEqual(run.call_count, len(STAGE_PLAN))
        self.assertIsNone(run.call_args_list[0].kwargs["previous_receipt_path"])
        self.assertEqual(
            run.call_args_list[-1].kwargs["previous_receipt_path"],
            args.output_dir / "3-library" / RECEIPT_NAME,
        )
        self.assertTrue((args.output_dir / SOURCE_IDENTITY_NAME).is_file())
        self.assertTrue((args.output_dir / EXECUTION_RECORD_NAME).is_file())

    def test_run_all_stops_on_failure_without_final_attestation(self):
        calls = 0
        fixtures = {receipt["stage"]["name"]: (receipt, log)
                    for receipt, log in self.chain(last_exit=17)}

        def fail_third(**kwargs):
            nonlocal calls
            calls += 1
            receipt, log = fixtures[kwargs["name"]]
            kwargs["log_path"].write_bytes(log.read_bytes())
            kwargs["output"].write_text(json.dumps(receipt), encoding="utf-8")
            return 17 if calls == 3 else 0

        output_dir = self.root / "all-failed"
        args = mock.Mock(
            output_dir=output_dir, repository=RUN["repository"],
            workflow=RUN["workflow"], run_id=RUN["run_id"],
            run_attempt=RUN["run_attempt"], commit=RUN["commit"],
            runner_os="Linux", runner_arch="X64",
        )
        with (
            mock.patch("kernel_stage_receipt.run_fixed_stage", side_effect=fail_third),
            mock.patch("kernel_stage_receipt.compute_kernel_identity", return_value=self.identity),
            mock.patch("kernel_stage_receipt.compute_stage_identities", return_value=stage_identities()),
            mock.patch("kernel_stage_receipt.collect_stage_context", return_value=self.context),
        ):
            self.assertEqual(run_all_cli(args), 17)
        self.assertEqual(calls, 3)
        self.assertFalse((output_dir / SOURCE_IDENTITY_NAME).exists())
        self.assertFalse((output_dir / EXECUTION_RECORD_NAME).exists())
        with self.assertRaisesRegex(ValueError, "must be new"):
            run_all_cli(args)

    def test_partial_failed_bundle_reuses_successful_prefix(self):
        prior = self.materialize(self.chain(last_exit=17), "failed-prior")
        candidates = load_reuse_candidates(
            prior, stage_identities=stage_identities(), context=self.context,
        )
        self.assertEqual(set(candidates), {stage.name for stage in STAGE_PLAN[:-1]})

        output = self.root / "retry"
        args = mock.Mock(
            output_dir=output, repository=RUN["repository"], workflow=RUN["workflow"],
            run_id="retry", run_attempt="2", commit=RUN["commit"],
            runner_os="Linux", runner_arch="X64", reuse_from=prior,
        )

        def execute_last(**kwargs):
            self.assertEqual(kwargs["name"], STAGE_PLAN[-1].name)
            receipt, log = self.chain()[-1]
            receipt["run"] = {
                "repository": RUN["repository"], "workflow": RUN["workflow"],
                "run_id": "retry", "run_attempt": "2", "source_commit": RUN["commit"],
            }
            receipt["receipt_digest"] = receipt_digest(receipt)
            kwargs["log_path"].write_bytes(log.read_bytes())
            kwargs["output"].write_text(json.dumps(receipt), encoding="utf-8")
            return 0

        with (
            mock.patch("kernel_stage_receipt.run_fixed_stage", side_effect=execute_last) as run,
            mock.patch("kernel_stage_receipt.compute_kernel_identity", return_value=self.identity),
            mock.patch("kernel_stage_receipt.compute_stage_identities", return_value=stage_identities()),
            mock.patch("kernel_stage_receipt.collect_stage_context", return_value=self.context),
            mock.patch("kernel_stage_receipt.verify_run", return_value={"success": True}),
        ):
            self.assertEqual(run_all_cli(args), 0)
        self.assertEqual(run.call_count, 1)
        for stage in STAGE_PLAN[:-1]:
            copied = output / f"{stage.index}-{stage.name}" / RECEIPT_NAME
            self.assertEqual(copied.read_bytes(),
                             (prior / f"{stage.index}-{stage.name}" / RECEIPT_NAME).read_bytes())

    def test_complete_bundle_is_bound_by_final_record(self):
        chain = self.chain()
        prior = self.materialize(chain, "complete-prior")
        record = self.verify(chain)
        (prior / SOURCE_IDENTITY_NAME).write_text(json.dumps(self.identity), encoding="utf-8")
        (prior / EXECUTION_RECORD_NAME).write_text(json.dumps(record), encoding="utf-8")
        self.assertEqual(set(load_reuse_candidates(
            prior, stage_identities=stage_identities(), context=self.context,
        )), set(PLAN_BY_NAME))
        record["stage_selections"][0]["receipt_digest"] = "sha256:" + "0" * 64
        record["execution_digest"] = aggregate_digest(record)
        (prior / EXECUTION_RECORD_NAME).write_text(json.dumps(record), encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "stage selections"):
            load_reuse_candidates(
                prior, stage_identities=stage_identities(), context=self.context,
            )

    def test_reuse_mismatch_is_ineligible_but_cache_provenance_is_not_context(self):
        prior = self.materialize(self.chain()[:1], "one-stage")
        identities = stage_identities()
        changed = copy.deepcopy(identities)
        changed["evidence"]["inputs_digest"] = "sha256:" + "9" * 64
        changed["evidence"]["digest"] = canonical_digest(
            "CertifiedJL-kernel-stage-inputs-v1",
            {key: value for key, value in changed["evidence"].items() if key != "digest"},
        )
        self.assertNotIn("evidence", load_reuse_candidates(
            prior, stage_identities=changed, context=self.context,
        ))
        context = copy.deepcopy(self.context)
        context["environment"]["CI"] = "false"
        self.assertNotIn("evidence", load_reuse_candidates(
            prior, stage_identities=identities, context=context,
        ))
        for key in ("CERTIFIEDJL_MODERATE_JOBS",
                    "CERTIFIEDJL_KERNEL_CANARY_BATCH_SIZE", "PYTHONOPTIMIZE",
                    "LEAN_GC_THRESHOLD", "ELAN_TOOLCHAIN"):
            with self.subTest(environment=key):
                changed_context = copy.deepcopy(self.context)
                changed_context["environment"][key] = "1"
                self.assertNotIn("evidence", load_reuse_candidates(
                    prior, stage_identities=identities, context=changed_context,
                ))
        for component in ("configuration", "dependency", "tool"):
            with self.subTest(component=component):
                changed_context = copy.deepcopy(self.context)
                if component == "configuration":
                    key = next(iter(changed_context["configuration_sha256"]))
                    changed_context["configuration_sha256"][key] = "sha256:" + "8" * 64
                elif component == "dependency":
                    changed_context["verified_dependencies"][0]["actual_revision"] = "other"
                else:
                    changed_context["tools"]["lean"] = "other Lean"
                self.assertNotIn("evidence", load_reuse_candidates(
                    prior, stage_identities=identities, context=changed_context,
                ))
        receipt_path = prior / "0-evidence" / RECEIPT_NAME
        receipt = read_json(receipt_path)
        receipt["cache"]["restored_key"] = receipt["cache"]["requested_key"]
        receipt["receipt_digest"] = receipt_digest(receipt)
        receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
        selection_path = prior / "0-evidence" / SELECTION_NAME
        selection = read_json(selection_path)
        selection["receipt_digest"] = receipt["receipt_digest"]
        selection["selection_digest"] = selection_digest(selection)
        selection_path.write_text(json.dumps(selection), encoding="utf-8")
        self.assertIn("evidence", load_reuse_candidates(
            prior, stage_identities=identities, context=self.context,
        ))

    def test_reuse_rejects_tampering_broken_chain_and_extra_files(self):
        for mutation, pattern in (("log", "log"), ("chain", "predecessor"),
                                  ("extra", "extra or missing"),
                                  ("symlink", "symlink")):
            with self.subTest(mutation=mutation):
                prior = self.materialize(self.chain(), f"tamper-{mutation}")
                if mutation == "log":
                    (prior / "1-moderate" / LOG_NAME).write_text("tampered\n", encoding="utf-8")
                elif mutation == "chain":
                    path = prior / "2-ternary-upper" / RECEIPT_NAME
                    receipt = read_json(path)
                    receipt["previous_receipt_digest"] = "sha256:" + "0" * 64
                    receipt["receipt_digest"] = receipt_digest(receipt)
                    path.write_text(json.dumps(receipt), encoding="utf-8")
                    selection_path = path.with_name(SELECTION_NAME)
                    selection = read_json(selection_path)
                    selection["receipt_digest"] = receipt["receipt_digest"]
                    selection["selection_digest"] = selection_digest(selection)
                    selection_path.write_text(json.dumps(selection), encoding="utf-8")
                else:
                    if mutation == "extra":
                        (prior / "3-library" / "extra").write_text("no", encoding="utf-8")
                    else:
                        log = prior / "1-moderate" / LOG_NAME
                        target = self.root / f"real-{mutation}.log"
                        target.write_bytes(log.read_bytes())
                        log.unlink()
                        log.symlink_to(target)
                with self.assertRaisesRegex(ValueError, pattern):
                    load_reuse_candidates(
                        prior, stage_identities=stage_identities(), context=self.context,
                    )

    def test_reuse_rejects_stages_after_failure_and_final_context_mismatch(self):
        prior = self.materialize(self.chain(), "post-failure")
        receipt_path = prior / "1-moderate" / RECEIPT_NAME
        receipt = read_json(receipt_path)
        receipt["success"] = False
        receipt["execution"]["exit_code"] = 1
        receipt["receipt_digest"] = receipt_digest(receipt)
        receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
        selection_path = receipt_path.with_name(SELECTION_NAME)
        selection = read_json(selection_path)
        selection["receipt_digest"] = receipt["receipt_digest"]
        selection["selection_digest"] = selection_digest(selection)
        selection_path.write_text(json.dumps(selection), encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "after its first failure"):
            load_reuse_candidates(
                prior, stage_identities=stage_identities(), context=self.context,
            )

        chain = self.chain()
        complete = self.materialize(chain, "context-mismatch")
        record = self.verify(chain)
        record["context"] = copy.deepcopy(record["context"])
        record["context"]["tools"]["lean"] = "different"
        record["execution_digest"] = aggregate_digest(record)
        (complete / SOURCE_IDENTITY_NAME).write_text(json.dumps(self.identity), encoding="utf-8")
        (complete / EXECUTION_RECORD_NAME).write_text(json.dumps(record), encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "execution context"):
            load_reuse_candidates(
                complete, stage_identities=stage_identities(), context=self.context,
            )


if __name__ == "__main__":
    unittest.main()
