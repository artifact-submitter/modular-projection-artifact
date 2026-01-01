#!/usr/bin/env python3
"""Run the canonical kernel proof record while sampling resource use.

The proof-record runner and its immutable receipts remain authoritative.  This
wrapper writes separate observational metrics for performance diagnosis; those
metrics do not attest that the proof succeeded.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import sys
import time
from typing import Any
import uuid


def _python_cache_isolation_active() -> bool:
    if not sys.dont_write_bytecode or not sys.pycache_prefix:
        return False
    prefix = Path(sys.pycache_prefix).absolute()
    repository = Path(__file__).resolve().parent.parent
    try:
        prefix.relative_to(repository)
        return False
    except ValueError:
        return not prefix.exists()


def _restart_with_python_cache_isolation() -> None:
    if __name__ != "__main__" or _python_cache_isolation_active():
        return
    environment = os.environ.copy()
    prefix = Path(os.environ.get("TMPDIR", "/tmp")) / (
        f"certifiedjl-disabled-pycache-{uuid.uuid4().hex}"
    )
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONPYCACHEPREFIX"] = str(prefix.absolute())
    os.execve(
        sys.executable,
        [sys.executable, "-B", str(Path(__file__).absolute()), *sys.argv[1:]],
        environment,
    )


_restart_with_python_cache_isolation()

from kernel_stage_receipt import (
    ROOT, SELECTION_NAME, STAGE_PLAN, read_json, require_outside_checkout,
    require_python_cache_isolation,
)


SCHEMA_VERSION = 1
LEAN_SOURCE = re.compile(r"(?P<path>/\S+\.lean|(?:CertifiedJL|Mathlib)/\S+\.lean)")
OBSERVATION_LIMITATIONS = [
    "stage receipt timestamps have one-second precision",
    "ps CPU percentages are platform-dependent averages, not interval CPU "
    "consumed since the preceding sample; macOS reports a decaying average "
    "over up to one minute",
    "processes that start and finish between samples do not contribute to sampled CPU totals",
    "summed RSS can double-count pages shared by related processes",
    "per-sample command attribution retains only the ten highest reported CPU users",
]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")


def parse_ps(output: str) -> list[dict[str, Any]]:
    result = []
    for line in output.splitlines():
        fields = line.strip().split(None, 5)
        if len(fields) != 6:
            continue
        try:
            pid, ppid = int(fields[0]), int(fields[1])
            cpu_percent, rss_kib = float(fields[2]), int(fields[3])
        except ValueError:
            continue
        result.append({
            "pid": pid,
            "ppid": ppid,
            "cpu_percent": cpu_percent,
            "rss_bytes": rss_kib * 1024,
            "elapsed": fields[4],
            "command": fields[5],
        })
    return result


def descendants(processes: list[dict[str, Any]], root_pid: int) -> list[dict[str, Any]]:
    selected = {root_pid}
    changed = True
    while changed:
        changed = False
        for process in processes:
            if process["ppid"] in selected and process["pid"] not in selected:
                selected.add(process["pid"])
                changed = True
    return [process for process in processes if process["pid"] in selected]


def command_label(command: str) -> str:
    match = LEAN_SOURCE.search(command)
    if match:
        source = Path(match.group("path"))
        try:
            return str(source.resolve().relative_to(ROOT.resolve()))
        except (ValueError, OSError):
            return str(source)
    for stage in STAGE_PLAN:
        if stage.script in command:
            return stage.script
    words = command.split()
    if not words:
        return "unknown"
    if "lake" in words[0] or Path(words[0]).name == "lake":
        return "lake " + " ".join(words[1:3])
    return Path(words[0]).name


def current_stage(output_dir: Path) -> str:
    for stage in reversed(STAGE_PLAN):
        if (output_dir / f"{stage.index}-{stage.name}").is_dir():
            return stage.name
    return "startup"


def sample_process_tree(root_pid: int, output_dir: Path, elapsed_seconds: float) -> dict[str, Any]:
    ps = subprocess.check_output(
        ["ps", "-axo", "pid=,ppid=,%cpu=,rss=,etime=,command="], text=True
    )
    tree = descendants(parse_ps(ps), root_pid)
    by_cpu = sorted(tree, key=lambda process: process["cpu_percent"], reverse=True)[:10]
    return {
        "timestamp_utc": utc_now(),
        "elapsed_seconds": elapsed_seconds,
        "stage": current_stage(output_dir),
        "process_count": len(tree),
        "cpu_percent_sum": sum(process["cpu_percent"] for process in tree),
        "rss_bytes_sum": sum(process["rss_bytes"] for process in tree),
        "top_processes": by_cpu,
    }


def exact_stage_records(output_dir: Path) -> list[dict[str, Any]]:
    result = []
    for stage in STAGE_PLAN:
        path = output_dir / f"{stage.index}-{stage.name}" / "stage-receipt.json"
        if not path.is_file():
            continue
        receipt = read_json(path)
        selection_path = path.with_name(SELECTION_NAME)
        selection = read_json(selection_path) if selection_path.is_file() else {
            "disposition": "unknown"
        }
        start = datetime.fromisoformat(receipt["execution"]["started_utc"].replace("Z", "+00:00"))
        finish = datetime.fromisoformat(receipt["execution"]["finished_utc"].replace("Z", "+00:00"))
        original_wall = (finish - start).total_seconds()
        result.append({
            "name": stage.name,
            "disposition": selection["disposition"],
            "started_utc": receipt["execution"]["started_utc"],
            "finished_utc": receipt["execution"]["finished_utc"],
            "wall_seconds": original_wall if selection["disposition"] == "executed" else None,
            "original_execution_wall_seconds": original_wall,
            "exit_code": receipt["execution"]["exit_code"],
            "log_size_bytes": receipt["execution"]["log"]["size_bytes"],
            "cache": receipt["cache"],
            "lean_num_threads": receipt["context"]["environment"]["LEAN_NUM_THREADS"],
        })
    return result


def stage_completion(records: list[dict[str, Any]]) -> dict[str, list[str]]:
    completed = [record["name"] for record in records]
    return {
        "completed_stages": completed,
        "incomplete_stages": [stage.name for stage in STAGE_PLAN if stage.name not in completed],
    }


def summarize_samples(samples: list[dict[str, Any]], sample_seconds: float) -> dict[str, Any]:
    by_stage: dict[str, dict[str, Any]] = defaultdict(
        lambda: {"samples": 0, "estimated_cpu_seconds": 0.0,
                 "peak_rss_bytes": 0, "peak_process_count": 0}
    )
    by_label: dict[str, float] = defaultdict(float)
    for sample in samples:
        stage = by_stage[sample["stage"]]
        stage["samples"] += 1
        stage["estimated_cpu_seconds"] += sample["cpu_percent_sum"] * sample_seconds / 100
        stage["peak_rss_bytes"] = max(stage["peak_rss_bytes"], sample["rss_bytes_sum"])
        stage["peak_process_count"] = max(stage["peak_process_count"], sample["process_count"])
        for process in sample["top_processes"]:
            by_label[command_label(process["command"])] += (
                process["cpu_percent"] * sample_seconds / 100
            )
    return {
        "estimated_cpu_seconds": sum(
            sample["cpu_percent_sum"] * sample_seconds / 100 for sample in samples
        ),
        "peak_rss_bytes": max((sample["rss_bytes_sum"] for sample in samples), default=0),
        "peak_process_count": max((sample["process_count"] for sample in samples), default=0),
        "sampled_stages": dict(by_stage),
        "slowest_sampled_commands": [
            {"label": label, "estimated_cpu_seconds": seconds}
            for label, seconds in sorted(by_label.items(), key=lambda item: item[1], reverse=True)[:25]
        ],
    }


def write_json_new(path: Path, value: dict[str, Any]) -> None:
    require_outside_checkout(path)
    if path.exists() or path.is_symlink():
        raise ValueError(f"instrumentation output already exists: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def validate_output_paths(output_dir: Path, metrics_output: Path, samples_output: Path) -> None:
    resolved_output = output_dir.resolve()
    resolved_metrics = metrics_output.resolve()
    resolved_samples = samples_output.resolve()
    if resolved_metrics == resolved_samples:
        raise ValueError("metrics and streaming samples need distinct paths")
    for label, path in (("metrics", resolved_metrics), ("samples", resolved_samples)):
        if path == resolved_output or resolved_output in path.parents:
            raise ValueError(f"{label} output must not be inside the proof-record directory")


def canonical_command(output_dir: Path, reuse_from: Path | None = None) -> list[str]:
    command = [
        "python3", "scripts/kernel_stage_receipt.py", "run-all",
        "--output-dir", str(output_dir),
    ]
    if reuse_from is not None:
        command.extend(["--reuse-from", str(reuse_from)])
    return command


def main() -> int:
    require_python_cache_isolation()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--metrics-output", type=Path, required=True)
    parser.add_argument(
        "--samples-output", type=Path,
        help="streaming JSONL observations; defaults beside --metrics-output",
    )
    parser.add_argument("--sample-seconds", type=float, default=5.0)
    parser.add_argument(
        "--reuse-from", type=Path,
        help="trusted canonical prior run-all directory used for stage reuse",
    )
    args = parser.parse_args()
    if args.sample_seconds <= 0:
        parser.error("--sample-seconds must be positive")
    require_outside_checkout(args.output_dir)
    require_outside_checkout(args.metrics_output)
    if args.reuse_from is not None:
        require_outside_checkout(args.reuse_from)
    samples_output = args.samples_output or args.metrics_output.with_name(
        args.metrics_output.stem + "-samples.jsonl"
    )
    require_outside_checkout(samples_output)
    validate_output_paths(args.output_dir, args.metrics_output, samples_output)
    if args.output_dir.exists() or args.output_dir.is_symlink():
        raise ValueError(f"proof-record output must be new: {args.output_dir}")
    if args.metrics_output.exists() or args.metrics_output.is_symlink():
        raise ValueError(f"instrumentation output must be new: {args.metrics_output}")
    if samples_output.exists() or samples_output.is_symlink():
        raise ValueError(f"sample output must be new: {samples_output}")
    samples_output.parent.mkdir(parents=True, exist_ok=True)

    command = canonical_command(args.output_dir, args.reuse_from)
    started_utc = utc_now()
    started = time.monotonic()
    project_cache_present_at_start = (ROOT / ".lake/build").is_dir()
    samples = []
    with samples_output.open("x", encoding="utf-8") as sample_stream:
        process = subprocess.Popen(command, cwd=ROOT)
        try:
            while process.poll() is None:
                before = time.monotonic()
                try:
                    sample = sample_process_tree(process.pid, args.output_dir, before - started)
                    sample["system_load_average"] = list(os.getloadavg())
                    samples.append(sample)
                    sample_stream.write(json.dumps(sample, sort_keys=True) + "\n")
                    sample_stream.flush()
                except (OSError, subprocess.SubprocessError):
                    pass
                remaining = args.sample_seconds - (time.monotonic() - before)
                if remaining > 0:
                    time.sleep(remaining)
            exit_code = process.wait()
        except KeyboardInterrupt:
            process.send_signal(signal.SIGINT)
            exit_code = process.wait()

    finished = time.monotonic()
    summary = summarize_samples(samples, args.sample_seconds)
    stage_records = exact_stage_records(args.output_dir)
    metrics = {
        "schema_version": SCHEMA_VERSION,
        "record_kind": "kernel-proof-performance-observation",
        "attests_execution": False,
        "limitations": OBSERVATION_LIMITATIONS,
        "source_commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip(),
        "command": command,
        "started_utc": started_utc,
        "finished_utc": utc_now(),
        "wall_seconds": finished - started,
        "exit_code": exit_code,
        "sample_seconds": args.sample_seconds,
        "machine": {
            "platform": platform.platform(),
            "logical_cpus": os.cpu_count(),
        },
        "project_cache": {
            "present_at_start": project_cache_present_at_start,
            "present_at_finish": (ROOT / ".lake/build").is_dir(),
        },
        "proof_record_output": str(args.output_dir.resolve()),
        "streaming_samples": {
            "path": str(samples_output.resolve()),
            "sha256": sha256_file(samples_output),
            "count": len(samples),
        },
        "exact_stage_records": stage_records,
        "stage_dispositions": {
            record["name"]: record["disposition"] for record in stage_records
        },
        **stage_completion(stage_records),
        "summary": summary,
    }
    write_json_new(args.metrics_output, metrics)
    print(json.dumps({key: metrics[key] for key in (
        "source_commit", "wall_seconds", "exit_code", "exact_stage_records", "summary"
    )}, indent=2))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
