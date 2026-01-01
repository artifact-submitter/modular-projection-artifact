#!/usr/bin/env python3
"""Check the fast, native, and kernel validation workflow boundaries."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent.parent
FAST = ROOT / ".github/workflows/ci.yml"
NATIVE = ROOT / ".github/workflows/native-replay.yml"
REPLAY = ROOT / ".github/workflows/kernel-proof-record.yml"
FAMILY = ROOT / ".github/workflows/kernel-proof-family.yml"
PAPER = ROOT / ".github/workflows/paper.yml"
VALIDATE = ROOT / "scripts/validate.sh"
VALIDATION_ROOTS = ROOT / "evidence/validation-roots.toml"
VALIDATION_BUILDER = ROOT / "scripts/build_validation_group.sh"
VALIDATE_FAST = ROOT / "scripts/validate_fast.sh"
VALIDATE_SAMPLES = ROOT / "scripts/validate_samples.sh"
VALIDATE_CERTIFICATES = ROOT / "scripts/validate_certificates.sh"
VALIDATE_EVIDENCE = ROOT / "scripts/validate_certificate_evidence.sh"
VALIDATE_LIBRARY = ROOT / "scripts/validate_certificate_library.sh"
VALIDATE_SPARSE_LOWER = ROOT / "scripts/validate_certificate_sparse_lower.sh"
VALIDATION_ENVIRONMENT = ROOT / "scripts/validation_environment.sh"
ISOLATED_BUILTIN_LINTS = ROOT / "scripts/run_builtin_lints_isolated.sh"
KERNEL_RECEIPT = ROOT / "scripts/kernel_stage_receipt.py"
CONTRIBUTING = ROOT / "CONTRIBUTING.md"
MAKEFILE = ROOT / "Makefile"
RUNNER_LABELS = "[self-hosted, linux, x64, exe-dev, certified-jl]"
NATIVE_REPLAY_MARKERS = (
    "native-replay-manifest.json",
    "native-replay-provenance.json",
    "native-replay-axiom-census.txt",
    "native-replay-source-inputs.json",
    "native-replay-audit.json",
    "native-replay-receipt.json",
)
FAMILY_AGGREGATE_EXPECTATIONS = {
    "scripts/build_moderate_certificate_proofs.sh": (
        "lake build CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.TheoremAssembly\n",
    ),
    "scripts/build_sparse_one_row_certificate_proofs.sh": (
        "  CertifiedJL.Certificates.Families.OneRow975.Finite \\\n",
        "  CertifiedJL.Projection.OneRow.BalancedTernary.CoefficientUniform\n",
    ),
    "scripts/validate_certificate_ternary_upper.sh": (
        "CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified\n",
    ),
}


def validate_family_aggregate_scripts(sources: dict[str, str]) -> None:
    for script_name, fragments in FAMILY_AGGREGATE_EXPECTATIONS.items():
        source = sources.get(script_name, "")
        for fragment in fragments:
            if fragment not in source:
                raise SystemExit(
                    f"{script_name} does not materialize its family aggregate: {fragment}"
                )


def validate_validation_thread_defaults(
    fast_source: str, native_source: str, family_source: str
) -> None:
    for name, source, expected_threads, expected_count in (
        ("fast and sample", fast_source, 2, 2),
        ("native", native_source, 1, 1),
        ("kernel", family_source, 1, 1),
    ):
        assignments = re.findall(r"(?m)^\s+LEAN_NUM_THREADS:\s+([0-9]+)\s*$", source)
        if assignments != [str(expected_threads)] * expected_count:
            raise SystemExit(
                f"{name} workflow must set LEAN_NUM_THREADS={expected_threads} "
                f"exactly {expected_count} time(s)"
            )


def validate_kernel_attestation_context(source: str) -> None:
    required = (
        "LEAN_NUM_THREADS: 1",
        "LEAN_GC_THRESHOLD: 256",
        "CERTIFIEDJL_MODERATE_BATCH_SIZE: 2",
        "CERTIFIEDJL_SPARSE_LOWER_BATCH_SIZE: 1",
        "CERTIFIEDJL_SPARSE_UPPER_CONTOUR_BATCH_SIZE: all",
        "leanprover/lean-action@38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9",
        "lake exe cache get",
        "python3 scripts/check_dependency_cache.py",
    )
    for fragment in required:
        if fragment not in source:
            raise SystemExit(f"kernel attestation context is missing: {fragment}")
    verify = source.index("scripts/kernel_stage_receipt.py verify-run")
    if any(source.index(fragment) > verify for fragment in required):
        raise SystemExit("kernel attestation context must be established before verification")


def validate_fast_sample_jobs(source: str) -> None:
    blocks = dict(job_blocks(source))
    if set(blocks) != {"impact", "validate", "certificate-samples"}:
        raise SystemExit("CI must contain the impact, fast, and certificate-sample jobs")
    if "scripts/check_proof_ci_impact.py" not in blocks["impact"]:
        raise SystemExit("CI impact job must use the conservative proof-change selector")
    fast = blocks["validate"]
    if "needs: impact" not in fast or "if: needs.impact.outputs.proof_changed == 'true'" not in fast:
        raise SystemExit("fast validation must honor the proof-change selector")
    samples = blocks["certificate-samples"]
    if not re.search(r"(?m)^    name: Certificate samples$", samples):
        raise SystemExit("certificate sample job must have its stable display name")
    if not re.search(r"(?m)^    needs: validate$", samples):
        raise SystemExit("certificate samples must run after fast validation")
    for name, block in (("fast", fast), ("certificate samples", samples)):
        if RUNNER_LABELS not in block:
            raise SystemExit(f"{name} job does not use the complete runner labels")
        if "LEAN_NUM_THREADS: 2" not in block:
            raise SystemExit(f"{name} job is missing the conservative thread default")
    required_fast = (
        "v5-mode-fast-", "python3 scripts/compute_fast_cache_key.py",
        "./scripts/validate_fast.sh", "Reset project build directory",
    )
    required_samples = (
        "v1-mode-certificate-samples-", "Select certificate samples",
        "python3 scripts/compute_sample_cache_key.py", "./scripts/validate.sh samples",
        "Reset certificate sample build directory", "steps.sample-plan.outputs.count",
    )
    for fragment in required_fast:
        if fragment not in fast:
            raise SystemExit(f"fast job is missing: {fragment}")
    for fragment in required_samples:
        if fragment not in samples:
            raise SystemExit(f"certificate sample job is missing: {fragment}")
    if "v1-mode-certificate-samples-" in fast or "v5-mode-fast-" in samples:
        raise SystemExit("fast and certificate sample cache namespaces must be disjoint")


def validate_isolated_builtin_lints(kernel_source: str, helper_source: str) -> None:
    if "lake lint --builtin-only" in kernel_source:
        raise SystemExit("kernel builtin lint roots must use isolated Lake processes")
    if kernel_source.count("./scripts/run_builtin_lints_isolated.sh") != 4:
        raise SystemExit("kernel builtin lint groups must use the isolated lint helper")
    for fragment in (
        'for module in "$@"; do',
        'lake lint --builtin-only "$module"',
    ):
        if fragment not in helper_source:
            raise SystemExit(f"isolated builtin lint helper is missing: {fragment}")


@dataclass(frozen=True)
class Job:
    key: str
    needs: str | None
    uses: str
    family: str
    stage_index: int
    previous: str
    script: str
    internal_timeout: int
    job_timeout: int


def job_blocks(source: str) -> list[tuple[str, str]]:
    jobs = source.split("\njobs:\n", 1)[1]
    matches = list(re.finditer(r"(?m)^  ([A-Za-z_][A-Za-z0-9_-]*):\n", jobs))
    return [
        (
            match.group(1),
            jobs[match.end() : matches[index + 1].start()]
            if index + 1 < len(matches)
            else jobs[match.end() :],
        )
        for index, match in enumerate(matches)
    ]


def field(block: str, name: str) -> str:
    match = re.search(rf"(?m)^      {re.escape(name)}: (.+)$", block)
    if match is None:
        raise SystemExit(f"certificate job is missing `{name}`")
    return match.group(1).strip()


def parse_jobs(source: str) -> list[Job]:
    result = []
    for key, block in job_blocks(source):
        if key == "attestation":
            continue
        needs_match = re.search(r"(?m)^    needs: ([a-z0-9-]+)$", block)
        uses_match = re.search(r"(?m)^    uses: (.+)$", block)
        if uses_match is None:
            raise SystemExit(f"certificate job {key} is missing `uses`")
        result.append(
            Job(
                key=key,
                needs=needs_match.group(1) if needs_match else None,
                uses=uses_match.group(1).strip(),
                family=field(block, "family"),
                stage_index=int(field(block, "stage-index")),
                previous=field(block, "previous-checkpoint"),
                script=field(block, "script"),
                internal_timeout=int(field(block, "internal-timeout-minutes")),
                job_timeout=int(field(block, "job-timeout-minutes")),
            )
        )
    return result


def workflow_step(source: str, name: str) -> str:
    header = f"      - name: {name}\n"
    if source.count(header) != 1:
        raise SystemExit(f"kernel workflow must contain exactly one {name} step")
    return source.split(header, 1)[1].split("\n      - name:", 1)[0]


def validate_kernel_native_marker_isolation(source: str) -> None:
    initial = workflow_step(source, "Reject native replay artifacts")
    restored = workflow_step(source, "Reject native replay artifacts in restored cache")
    for marker in NATIVE_REPLAY_MARKERS:
        if initial.count(marker) < 2:
            raise SystemExit(
                f"kernel workflow must reject {marker} both explicitly and in .lake/build"
            )
        if marker not in restored:
            raise SystemExit(f"kernel workflow must reject restored-cache {marker}")
    if '[[ -e "$marker" || -L "$marker" ]]' not in initial:
        raise SystemExit("kernel workflow must reject dangling native-artifact symlinks")
    if "[[ -L ./.lake/build ]]" not in restored:
        raise SystemExit("kernel workflow must reject a symlinked restored build cache")
    restore_position = source.index("      - name: Restore incremental checkpoint\n")
    rejection_position = source.index(
        "      - name: Reject native replay artifacts in restored cache\n"
    )
    setup_position = source.index("      - name: Set up Lean\n")
    if not restore_position < rejection_position < setup_position:
        raise SystemExit(
            "kernel restored-cache rejection must follow cache restore and precede replay"
        )


def validate_native_production_marker_isolation(source: str) -> None:
    validation = workflow_step(source, "Native validation")
    for marker in NATIVE_REPLAY_MARKERS:
        expected = f"./.lake/build/{marker}"
        if expected not in validation:
            raise SystemExit(f"native workflow must reject production-cache {marker}")
    loop = 'for marker in "${production_markers[@]}"; do'
    symlink_safe_check = '[[ -e "$marker" || -L "$marker" ]]'
    if validation.count(loop) != 2 or validation.count(symlink_safe_check) != 2:
        raise SystemExit(
            "native workflow must check production-cache markers before and after replay, "
            "including dangling symlinks"
        )
    loop_positions = [match.start() for match in re.finditer(re.escape(loop), validation)]
    replay_position = validation.index("./scripts/validate_native.sh")
    if not loop_positions[0] < replay_position < loop_positions[1]:
        raise SystemExit(
            "native production-cache rejection must bracket the native replay"
        )


def main() -> None:
    fast_source = FAST.read_text(encoding="utf-8")
    native_source = NATIVE.read_text(encoding="utf-8")
    replay_source = REPLAY.read_text(encoding="utf-8")
    family_source = FAMILY.read_text(encoding="utf-8")
    receipt_source = KERNEL_RECEIPT.read_text(encoding="utf-8")
    paper_source = PAPER.read_text(encoding="utf-8")
    jobs = parse_jobs(replay_source)

    expected_plan = [
        ("evidence", "scripts/validate_certificate_evidence.sh"),
        ("moderate", "scripts/validate_certificate_moderate.sh"),
        ("ternary-upper", "scripts/validate_certificate_ternary_upper.sh"),
        ("library", "scripts/validate_certificate_library.sh"),
        ("complete", "scripts/validate_certificate_canaries.sh"),
    ]
    actual_plan = [(job.family, job.script) for job in jobs]
    if actual_plan != expected_plan:
        raise SystemExit(
            "unexpected certificate family plan:\n"
            f"expected={expected_plan}\nactual={actual_plan}"
        )
    actual_families = [job.family for job in jobs]
    if len(set(actual_families)) != len(actual_families):
        raise SystemExit("certificate family names must be unique")

    owner = {job.family: job.key for job in jobs}
    for index, job in enumerate(jobs):
        if job.uses != "./.github/workflows/kernel-proof-family.yml":
            raise SystemExit(f"{job.key}: unexpected reusable workflow {job.uses}")
        expected_previous = "complete" if index == 0 else jobs[index - 1].family
        if job.stage_index != index:
            raise SystemExit(
                f"{job.key}: stage-index={job.stage_index}, expected {index}"
            )
        if job.previous != expected_previous:
            raise SystemExit(
                f"{job.key}: previous-checkpoint={job.previous}, "
                f"expected {expected_previous}"
            )
        if index == 0:
            if job.needs is not None:
                raise SystemExit("the first certificate job must not have `needs`")
        elif job.needs != owner[job.previous]:
            raise SystemExit(
                f"{job.key}: needs={job.needs}, expected {owner[job.previous]}"
            )
        if job.job_timeout - job.internal_timeout < 30:
            raise SystemExit(
                f"{job.key}: hard timeout must leave at least 30 minutes "
                "for interrupt handling and partial-cache upload"
            )
        script = ROOT / job.script
        if not script.is_file():
            raise SystemExit(f"{job.key}: missing script {job.script}")
        if script.stat().st_mode & 0o111 == 0:
            raise SystemExit(f"{job.key}: script is not executable: {job.script}")

    trigger_section = replay_source.split("\njobs:\n", 1)[0]
    if re.search(r"(?m)^  (?:push|pull_request):", trigger_section):
        raise SystemExit("kernel proof record must not run automatically on pushes or PRs")
    trigger_invariants = (
        "workflow_dispatch:",
        'cron: "17 3 * * 0"',
        "release:",
        "types: [published]",
        "format('rejected-kernel-proof-dispatch-{0}', github.run_id)",
        "'kernel-proof-record'",
        "cancel-in-progress: false",
        "queue: max",
    )
    for fragment in trigger_invariants:
        if fragment not in trigger_section:
            raise SystemExit(f"certificate trigger/concurrency is missing: {fragment}")

    replay_blocks = dict(job_blocks(replay_source))
    if list(replay_blocks)[-1] != "attestation":
        raise SystemExit("kernel attestation must be the final proof-record job")
    attestation = replay_blocks["attestation"]
    validate_kernel_attestation_context(attestation)
    attestation_fragments = (
        "needs: [evidence, moderate, ternary-upper, library, canaries]",
        "Kernel proof-record attestation",
        RUNNER_LABELS,
        "scripts/compute_replay_digest.py --mode kernel --json",
        "Download kernel stage execution receipts",
        "actions/download-artifact@",
        "kernel-proof-stage-${{ github.run_id }}-${{ github.run_attempt }}-*",
        "scripts/kernel_stage_receipt.py verify-run",
        'identity_path="$RUNNER_TEMP/kernel-proof-record-source-identity.json"',
        'record_path="$RUNNER_TEMP/kernel-proof-record.json"',
        "${{ runner.temp }}/kernel-proof-record-source-identity.json",
        "${{ runner.temp }}/kernel-proof-stage-receipts",
        "actions/upload-artifact@",
        "kernel-proof-record-${{ github.sha }}-${{ github.run_id }}-${{ github.run_attempt }}",
        "if-no-files-found: error",
        'test "$(git rev-parse HEAD)" = "$GITHUB_SHA"',
        'test -z "$(git status --porcelain --untracked-files=all)"',
    )
    for fragment in attestation_fragments:
        if fragment not in attestation:
            raise SystemExit(f"kernel attestation is missing: {fragment}")
    if re.search(r">\s*kernel-proof-record(?:-source-identity)?\.json", attestation):
        raise SystemExit("kernel execution record must stay outside the source checkout")

    required_family_fragments = (
        "Require default-branch manual dispatch",
        "Reject native replay artifacts",
        "Reset project build directory",
        "v6-mode-kernel-proof-record-",
        "-complete-${{ env.CERTIFIEDJL_CACHE_SCOPE }}-${{ inputs.family }}",
        "-progress-${{ env.CERTIFIEDJL_CACHE_SCOPE }}-${{ inputs.family",
        "format('scheduled-{0}-{1}', github.run_id, github.sha)",
        "format('release-{0}-{1}', github.event.release.tag_name, github.sha)",
        "tier: kernel-proof-record",
        "commit: $GITHUB_SHA",
        "cache-matched-key",
        "unexpected cache tier restored",
        "CERTIFIEDJL_SPARSE_LOWER_BATCH_SIZE: 1",
        "LEAN_GC_THRESHOLD: 256",
        "Verify exact workflow revision",
        "scripts/check_dependency_cache.py",
        "stage-index:",
        "Download predecessor execution receipt",
        "actions/download-artifact@",
        "kernel-proof-stage-${{ github.run_id }}-${{ github.run_attempt }}-${{ inputs.previous-checkpoint }}",
        'shell: bash',
        "scripts/kernel_stage_receipt.py",
        "run-stage",
        "--cache-policy github-actions-kernel",
        '--cache-requested-key "$REQUESTED_KEY"',
        '--cache-restored-key "$RESTORED_KEY"',
        'replay_status="$?"',
        "--previous-receipt",
        "Upload kernel stage execution receipt",
        "kernel-proof-stage-${{ github.run_id }}-${{ github.run_attempt }}-${{ inputs.family }}",
        "if-no-files-found: error",
    )
    for fragment in required_family_fragments:
        if fragment not in family_source:
            raise SystemExit(f"reusable kernel family is missing: {fragment}")
    validate_kernel_native_marker_isolation(family_source)
    if re.search(
        r"\.lake/[^\n]*(?:stage-receipt|stage\.log|kernel-proof-record)",
        family_source,
        re.IGNORECASE,
    ):
        raise SystemExit("kernel execution receipts must remain outside build caches")
    if 'use "re-run all jobs"' not in replay_source:
        raise SystemExit("kernel workflow must document attempt-bound full reruns")
    receipt_fragments = (
        '"evidence", "scripts/validate_certificate_evidence.sh", 90',
        '"moderate", "scripts/validate_certificate_moderate.sh", 330',
        '"ternary-upper", "scripts/validate_certificate_ternary_upper.sh", 150',
        '"library", "scripts/validate_certificate_library.sh", 330',
        '"complete", "scripts/validate_certificate_canaries.sh", 330',
        'canonical_digest("CertifiedJL-kernel-stage-receipt-v1"',
        'canonical_digest("CertifiedJL-kernel-execution-record-v1"',
        'compute_identity(mode="kernel")',
        'subparsers.add_parser("run-all")',
        'start_new_session=True',
        'terminate_process_group(process)',
        'supplied_identity != current_identity',
        'write_json_new',
        '"LEAN_PATH"',
        '"LEAN_SRC_PATH"',
        '"LEAN_OPTS"',
        '"github-actions-kernel"',
        '"local-project-cache"',
        'identity_before != identity_after',
        'context_after != context',
        'verified_dependencies(ROOT)',
        'receipt["stage_identity"] != current_stage_identities.get(stage.name)',
        'receipt["context"] != current_context',
        'load_reuse_candidates(',
        'SELECTION_NAME = "stage-selection.json"',
        'run_all.add_argument(',
        '"--reuse-from", type=Path',
        'reuse stage directory has extra or missing files',
        'reuse bundle historical predecessor chain is broken',
        'source identity changed during kernel run-all',
        'not receipt["success"] or receipt["execution"]["exit_code"] != 0',
        'len(receipts) != len(STAGE_PLAN)',
        'require_outside_checkout',
    )
    for fragment in receipt_fragments:
        if fragment not in receipt_source:
            raise SystemExit(f"kernel receipt implementation is missing: {fragment}")
    validate_validation_thread_defaults(fast_source, native_source, family_source)
    fast_trigger = fast_source.split("\njobs:\n", 1)[0]
    fast_fragments = (
        "name: CI",
        'branches: ["main"]',
        "pull_request:",
        "workflow_dispatch:",
        "cancel-in-progress: true",
        "Reset project build directory",
        "v5-mode-fast-",
        "python3 scripts/compute_fast_cache_key.py",
        "./scripts/validate_fast.sh",
        "tier: fast",
        "commit: $GITHUB_SHA",
        "cache-matched-key",
        "unexpected cache tier restored",
        "Verify exact workflow revision",
        "scripts/check_dependency_cache.py",
    )
    for fragment in fast_fragments:
        if fragment not in fast_source:
            raise SystemExit(f"fast workflow is missing: {fragment}")
    validate_fast_sample_jobs(fast_source)
    if "schedule:" in fast_trigger or "release:" in fast_trigger:
        raise SystemExit("fast workflow must remain the PR/push validation tier")

    scheduling_sources = {
        "validation-root manifest": VALIDATION_ROOTS.read_text(encoding="utf-8"),
        "validation group builder": VALIDATION_BUILDER.read_text(encoding="utf-8"),
        "fast validator": VALIDATE_FAST.read_text(encoding="utf-8"),
        "sample validator": VALIDATE_SAMPLES.read_text(encoding="utf-8"),
        "kernel validator": VALIDATE_CERTIFICATES.read_text(encoding="utf-8"),
        "evidence validator": VALIDATE_EVIDENCE.read_text(encoding="utf-8"),
        "kernel library validator": VALIDATE_LIBRARY.read_text(encoding="utf-8"),
        "sparse lower validator": VALIDATE_SPARSE_LOWER.read_text(encoding="utf-8"),
        "validation environment": VALIDATION_ENVIRONMENT.read_text(encoding="utf-8"),
    }
    scheduling_fragments = {
        "validation-root manifest": (
            'id = "fast"',
            'id = "kernel-canaries"',
            'id = "sparse-lower"',
            'batch_size_env = "CERTIFIEDJL_SPARSE_LOWER_BATCH_SIZE"',
        ),
        "validation group builder": (
            "scripts/validation_roots.py",
            "scripts/build_targets_in_batches.sh",
        ),
        "fast validator": (
            "scripts/test_native_shadow_replay.py",
            "scripts/test_kernel_stage_receipt.py",
            "scripts/test_sparse_upper_contour_build.py",
            "scripts/test_validate_dispatch.py",
            "scripts/test_compute_fast_cache_key.py",
            "scripts/test_sample_selection.py",
            "scripts/test_compute_sample_cache_key.py",
            "scripts/test_validation_roots.py",
            "scripts/test_run_builtin_lints_isolated.py",
            "scripts/check_numeric_import_boundary.py",
            "scripts/test_numeric_import_boundary.py",
            "scripts/build_validation_group.sh fast",
        ),
        "sample validator": (
            "scripts/check_certificate_catalog.py",
            "scripts/test_sample_selection.py",
            "scripts/test_compute_sample_cache_key.py",
            "scripts/run_certificate_samples.py",
        ),
        "kernel validator": (
            "scripts/validate_certificate_sparse_lower.sh",
            "scripts/build_validation_group.sh kernel-canaries",
            "scripts/run_builtin_lints_isolated.sh",
        ),
        "evidence validator": (
            "scripts/check_numeric_import_boundary.py",
            "scripts/test_numeric_import_boundary.py",
            "scripts/test_check_certificate_workflow.py",
            "scripts/test_kernel_stage_receipt.py",
            "scripts/test_sparse_upper_contour_build.py",
            "scripts/test_validate_dispatch.py",
            "scripts/test_run_builtin_lints_isolated.py",
        ),
        "kernel library validator": (
            "scripts/validate_certificate_sparse_lower.sh",
            "CERTIFIEDJL_ASSEMBLY_ONLY=1",
        ),
        "sparse lower validator": (
            "scripts/check_dependency_cache.py",
            "scripts/build_validation_group.sh sparse-lower",
        ),
        "validation environment": (
            "export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}",
            "export LEAN_GC_THRESHOLD=${LEAN_GC_THRESHOLD:-256}",
        ),
    }
    for source_name, fragments in scheduling_fragments.items():
        source = scheduling_sources[source_name]
        for fragment in fragments:
            if fragment not in source:
                raise SystemExit(f"{source_name} is missing: {fragment}")
    if "run_certificate_samples.py" in scheduling_sources["fast validator"]:
        raise SystemExit("fast validation must not execute exact certificate samples")
    if re.search(r"(?m)^lake build CertifiedJL", scheduling_sources["fast validator"]):
        raise SystemExit("fast Lean roots must be built through the shared scheduler")
    if re.search(
        r"(?m)^lake build CertifiedJL", scheduling_sources["kernel validator"]
    ):
        raise SystemExit("kernel canaries must be built through the shared scheduler")
    validate_isolated_builtin_lints(
        scheduling_sources["kernel validator"],
        ISOLATED_BUILTIN_LINTS.read_text(encoding="utf-8"),
    )
    validation_entrypoints = (
        VALIDATE_FAST,
        VALIDATE_SAMPLES,
        ROOT / "scripts/validate_native.sh",
        VALIDATE_CERTIFICATES,
        VALIDATE_EVIDENCE,
        ROOT / "scripts/validate_certificate_moderate.sh",
        ROOT / "scripts/validate_certificate_ternary_upper.sh",
        VALIDATE_LIBRARY,
        ROOT / "scripts/validate_certificate_canaries.sh",
        VALIDATE_SPARSE_LOWER,
    )
    for entrypoint in validation_entrypoints:
        if "scripts/validation_environment.sh" not in entrypoint.read_text(
            encoding="utf-8"
        ):
            raise SystemExit(
                f"{entrypoint.relative_to(ROOT)} is missing the validation environment"
            )

    native_trigger = native_source.split("\njobs:\n", 1)[0]
    native_fragments = (
        "name: Native certificate replay",
        "workflow_dispatch:",
        'cron: "37 11 * * *"',
        "cancel-in-progress: false",
        "Require default-branch manual dispatch",
        "Configure native build directory",
        "Reset native build directory",
        'runtime_dir="${RUNNER_TEMP}/certifiedjl-native-replay"',
        'echo "CERTIFIEDJL_NATIVE_BUILD_DIR=$runtime_dir" >> "$GITHUB_ENV"',
        'echo "CERTIFIEDJL_NATIVE_SHADOW_DIR=$runtime_dir" >> "$GITHUB_ENV"',
        "Compute native replay source digest",
        "scripts/compute_replay_digest.py --mode native --json",
        "steps.native-source.outputs.digest",
        "certifiedjl-native-source-digest.json",
        "./scripts/validate_native.sh",
        "scripts/native_shadow_replay.py",
        "scripts/audit_native_replay.py",
        "scripts/compute_replay_digest.py",
        "evidence/certificates/replay-families.toml",
        "native-replay-manifest.json",
        "native-replay-provenance.json",
        "native-replay-axiom-census.txt",
        "native-replay-source-inputs.json",
        "native-replay-audit.json",
        "native-replay-receipt.json",
        "tier: native-replay",
        "commit: $GITHUB_SHA",
        "project cache: none (cold native shadow)",
        "Upload native replay provenance",
        "actions/upload-artifact@",
        "native-replay-provenance-${{ github.sha }}",
        "if-no-files-found: error",
        "Upload failed native replay diagnostics",
        "if: failure()",
        "native-replay-failure-${{ github.sha }}-${{ github.run_attempt }}",
        "if-no-files-found: warn",
        "Clean native build directory",
        "if: always()",
        "Verify exact workflow revision",
        "scripts/check_dependency_cache.py",
        "Require native replay disk budget",
        "required_kib=$((16 * 1024 * 1024))",
        "timeout --signal=INT --kill-after=5m 450m",
    )
    for fragment in native_fragments:
        if fragment not in native_source:
            raise SystemExit(f"native workflow is missing: {fragment}")
    validate_native_production_marker_isolation(native_source)
    if not re.search(r"(?m)^\s+\./scripts/validate_native\.sh$", native_source):
        raise SystemExit("native workflow must invoke the no-argument all-family replay")
    if re.search(r"(?m)^  (?:push|pull_request|release):", native_trigger):
        raise SystemExit("native replay must be nightly/manual only")
    native_job_header = native_source.split("\n    steps:\n", 1)[0]
    if "${{ runner." in native_job_header:
        raise SystemExit(
            "native job-level fields must not use the step-scoped runner context"
        )
    if "path: ./.lake/build" in native_source:
        raise SystemExit("native replay must not cache the production Lake build tree")
    if "rm -rf -- ./.lake/build" in native_source:
        raise SystemExit("native replay must not delete the production Lake build tree")
    if "actions/cache/" in native_source:
        raise SystemExit("native replay must start from a cold disposable shadow")
    if "test ! -e ./.lake/build\n" in native_source:
        raise SystemExit(
            "native replay must allow lake cache setup to create the production build tree"
        )
    cleanup = native_source.rsplit("      - name: Clean native build directory", 1)
    if len(cleanup) != 2 or "rm -rf -- \"$CERTIFIEDJL_NATIVE_BUILD_DIR\"" not in cleanup[1]:
        raise SystemExit("native replay must clean its exact external runtime directory")
    if "certifiedjl-native-replay" not in cleanup[1]:
        raise SystemExit("native cleanup must guard the expected runner-temp path")

    paper_trigger = paper_source.split("\njobs:\n", 1)[0]
    if re.search(r"(?m)^    paths(?:-ignore)?:", paper_trigger):
        raise SystemExit(
            "paper workflow must not use trigger-level path filters; GitHub truncates "
            "large changed-file lists"
        )
    paper_fragments = (
        'branches: ["main"]',
        "pull_request:",
        "workflow_dispatch:",
        'cron: "43 4 * * 3"',
        "Determine paper impact from complete diff",
        "scripts/check_paper_ci_impact.py",
        "fetch-depth: 0",
        "cancel-in-progress:",
        "github.run_id",
        "steps.paper-impact.outputs.paper_changed == 'true'",
    )
    for fragment in paper_fragments:
        if fragment not in paper_source:
            raise SystemExit(f"paper workflow is missing: {fragment}")
    impact_source = (ROOT / "scripts/check_paper_ci_impact.py").read_text(
        encoding="utf-8"
    )
    for dependency in (
        ".github/workflows/paper.yml",
        "Makefile",
        "evidence/result-catalog.toml",
        "scripts/generate_formalization_table.py",
        "paper/",
    ):
        if dependency not in impact_source:
            raise SystemExit(f"paper impact closure is missing: {dependency}")

    validate_source = VALIDATE.read_text(encoding="utf-8")
    if "CERTIFIEDJL_VALIDATION_MODE:-fast" not in validate_source:
        raise SystemExit("validation entrypoint must default to fast mode")
    contributing_source = CONTRIBUTING.read_text(encoding="utf-8")
    if "./scripts/validate.sh`" in contributing_source or re.search(
        r"(?m)^\./scripts/validate\.sh$", contributing_source
    ):
        raise SystemExit("contributor guidance must select fast validation explicitly")
    make_source = MAKEFILE.read_text(encoding="utf-8")
    if "\t./scripts/validate.sh kernel" not in make_source:
        raise SystemExit("the proof-record Make target must select kernel mode explicitly")

    ci_blocks = dict(job_blocks(fast_source))
    sources_by_mode = {
        "fast": ci_blocks["validate"],
        "samples": ci_blocks["certificate-samples"],
        "native": native_source,
        "kernel": family_source,
    }
    prefixes = {
        "fast": "v5-mode-fast-",
        "samples": "v1-mode-certificate-samples-",
        "kernel": "v6-mode-kernel-proof-record-",
    }
    isolation_markers = {
        "fast": "Reset project build directory",
        "samples": "Reset certificate sample build directory",
        "native": "Reset native build directory",
        "kernel": "Reject native replay artifacts",
    }
    for mode, source in sources_by_mode.items():
        if RUNNER_LABELS not in source:
            raise SystemExit(f"{mode} workflow does not use the complete runner labels")
        if isolation_markers[mode] not in source:
            raise SystemExit(f"{mode} workflow does not isolate its project artifacts")
        for other_mode, prefix in prefixes.items():
            if (prefix in source) != (mode == other_mode):
                raise SystemExit(
                    f"{mode} workflow cache namespace crosses into {other_mode} mode"
                )

    obsolete_workflows = (
        ROOT / ".github/workflows/certificate-replay.yml",
        ROOT / ".github/workflows/certificate-family.yml",
    )
    present_obsolete = [str(path.relative_to(ROOT)) for path in obsolete_workflows if path.exists()]
    if present_obsolete:
        raise SystemExit("obsolete replay workflows remain: " + ", ".join(present_obsolete))

    validate_family_aggregate_scripts(
        {
            script_name: (ROOT / script_name).read_text(encoding="utf-8")
            for script_name in FAMILY_AGGREGATE_EXPECTATIONS
        }
    )

    print(
        f"validation workflow verified: fast PR CI, diff-selected certificate samples, nightly native replay, "
        f"{len(jobs)} serial kernel proof families, "
        "balanced-ternary-only public proof closure, "
        "weekly/manual/release proof record, mode-isolated caches"
    )


if __name__ == "__main__":
    main()
