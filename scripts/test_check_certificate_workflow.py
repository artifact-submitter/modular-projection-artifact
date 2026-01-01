#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path
import unittest

from check_certificate_workflow import (
    FAMILY_AGGREGATE_EXPECTATIONS,
    NATIVE_REPLAY_MARKERS,
    validate_fast_sample_jobs,
    validate_isolated_builtin_lints,
    validate_family_aggregate_scripts,
    validate_kernel_native_marker_isolation,
    validate_kernel_attestation_context,
    validate_native_production_marker_isolation,
    validate_validation_thread_defaults,
)


ROOT = Path(__file__).resolve().parent.parent
FAMILY_WORKFLOW = ROOT / ".github/workflows/kernel-proof-family.yml"
KERNEL_WORKFLOW = ROOT / ".github/workflows/kernel-proof-record.yml"
NATIVE_WORKFLOW = ROOT / ".github/workflows/native-replay.yml"
FAST_WORKFLOW = ROOT / ".github/workflows/ci.yml"
KERNEL_VALIDATOR = ROOT / "scripts/validate_certificates.sh"
ISOLATED_LINTS = ROOT / "scripts/run_builtin_lints_isolated.sh"


class CertificateWorkflowTests(unittest.TestCase):
    def test_kernel_attestation_recreates_stage_execution_context(self) -> None:
        source = KERNEL_WORKFLOW.read_text(encoding="utf-8")
        attestation = source.split("\n  attestation:\n", 1)[1]
        validate_kernel_attestation_context(attestation)
        for fragment in (
            "CERTIFIEDJL_MODERATE_BATCH_SIZE: 2",
            "CERTIFIEDJL_SPARSE_LOWER_BATCH_SIZE: 1",
            "CERTIFIEDJL_SPARSE_UPPER_CONTOUR_BATCH_SIZE: all",
            "LEAN_GC_THRESHOLD: 256",
            "lake exe cache get",
            "python3 scripts/check_dependency_cache.py",
        ):
            with self.subTest(fragment=fragment), self.assertRaisesRegex(
                SystemExit, "attestation context"
            ):
                validate_kernel_attestation_context(
                    attestation.replace(fragment, "removed", 1)
                )

    def test_fast_and_sample_jobs_are_ordered_and_cache_isolated(self) -> None:
        source = FAST_WORKFLOW.read_text(encoding="utf-8")
        validate_fast_sample_jobs(source)
        mutations = (
            source.replace("    needs: validate", "    needs: missing-fast", 1),
            source.replace("v1-mode-certificate-samples-", "v5-mode-fast-", 1),
            source.replace("python3 scripts/compute_sample_cache_key.py", "removed-selector", 1),
            source.replace("./scripts/validate.sh samples", "./scripts/validate_fast.sh", 1),
        )
        for index, changed in enumerate(mutations):
            with self.subTest(index=index), self.assertRaises(SystemExit):
                validate_fast_sample_jobs(changed)

    def test_family_build_scripts_materialize_semantic_aggregates(self) -> None:
        sources = {
            script: (ROOT / script).read_text(encoding="utf-8")
            for script in FAMILY_AGGREGATE_EXPECTATIONS
        }
        validate_family_aggregate_scripts(sources)
        for script, fragments in FAMILY_AGGREGATE_EXPECTATIONS.items():
            for fragment in fragments:
                changed = dict(sources)
                changed[script] = changed[script].replace(fragment, "removed-aggregate", 1)
                with self.subTest(script=script, fragment=fragment), self.assertRaisesRegex(
                    SystemExit, "does not materialize"
                ):
                    validate_family_aggregate_scripts(changed)

    def test_workflows_set_conservative_lake_thread_default(self) -> None:
        sources = [
            FAST_WORKFLOW.read_text(encoding="utf-8"),
            NATIVE_WORKFLOW.read_text(encoding="utf-8"),
            FAMILY_WORKFLOW.read_text(encoding="utf-8"),
        ]
        validate_validation_thread_defaults(*sources)
        expected_threads = ("2", "1", "1")
        for index, (source, threads) in enumerate(
            zip(sources, expected_threads, strict=True)
        ):
            changed = list(sources)
            changed[index] = source.replace(
                f"LEAN_NUM_THREADS: {threads}", "removed-thread-default", 1
            )
            with self.subTest(workflow=index), self.assertRaisesRegex(
                SystemExit, "LEAN_NUM_THREADS"
            ):
                validate_validation_thread_defaults(*changed)

    def test_kernel_lint_roots_use_isolated_processes(self) -> None:
        validator = KERNEL_VALIDATOR.read_text(encoding="utf-8")
        helper = ISOLATED_LINTS.read_text(encoding="utf-8")
        validate_isolated_builtin_lints(validator, helper)
        with self.assertRaisesRegex(SystemExit, "isolated Lake processes"):
            validate_isolated_builtin_lints(
                validator + "\nlake lint --builtin-only Combined.Root\n", helper
            )
        with self.assertRaisesRegex(SystemExit, "helper is missing"):
            validate_isolated_builtin_lints(
                validator,
                helper.replace('lake lint --builtin-only "$module"', "removed"),
            )

    def test_kernel_rejects_every_native_runtime_marker(self) -> None:
        source = FAMILY_WORKFLOW.read_text(encoding="utf-8")
        validate_kernel_native_marker_isolation(source)
        for marker in NATIVE_REPLAY_MARKERS:
            for location, mutated in (
                ("initial", source.replace(marker, "removed-native-marker", 1)),
                (
                    "restored",
                    "removed-native-marker".join(source.rsplit(marker, 1)),
                ),
            ):
                with self.subTest(marker=marker, location=location), self.assertRaisesRegex(
                    SystemExit, marker.replace(".", r"\.")
                ):
                    validate_kernel_native_marker_isolation(mutated)

    def test_kernel_marker_rejection_is_symlink_safe_and_post_restore(self) -> None:
        source = FAMILY_WORKFLOW.read_text(encoding="utf-8")
        without_symlink_check = source.replace(' || -L "$marker"', "", 1)
        with self.assertRaisesRegex(SystemExit, "dangling"):
            validate_kernel_native_marker_isolation(without_symlink_check)

        post_header = "      - name: Reject native replay artifacts in restored cache\n"
        post_start = source.index(post_header)
        post_end = source.index("\n      - name:", post_start + len(post_header))
        post_step = source[post_start:post_end]
        without_post = source[:post_start] + source[post_end:]
        restore_header = "      - name: Restore incremental checkpoint\n"
        moved_before_restore = without_post.replace(
            restore_header, post_step + "\n\n" + restore_header, 1
        )
        with self.assertRaisesRegex(SystemExit, "follow cache restore"):
            validate_kernel_native_marker_isolation(moved_before_restore)

    def test_native_production_markers_bracket_replay_and_reject_symlinks(self) -> None:
        source = NATIVE_WORKFLOW.read_text(encoding="utf-8")
        validate_native_production_marker_isolation(source)
        marker = NATIVE_REPLAY_MARKERS[-1]
        with self.assertRaisesRegex(SystemExit, marker.replace(".", r"\.")):
            validate_native_production_marker_isolation(
                source.replace(f"./.lake/build/{marker}", "removed-native-marker", 1)
            )
        with self.assertRaisesRegex(SystemExit, "before and after"):
            validate_native_production_marker_isolation(
                source.replace(' || -L "$marker"', "", 1)
            )
        loop = 'for marker in "${production_markers[@]}"; do'
        with self.assertRaisesRegex(SystemExit, "before and after"):
            validate_native_production_marker_isolation(
                "removed-loop".join(source.rsplit(loop, 1))
            )


if __name__ == "__main__":
    unittest.main()
