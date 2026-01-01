#!/usr/bin/env python3
"""Run every balanced-ternary upper generator check with bounded concurrency."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
import os
from pathlib import Path
import signal
import subprocess
import threading


ROOT = Path(__file__).resolve().parent.parent
MAX_WORKERS = 2


@dataclass(frozen=True)
class Check:
    label: str
    command: tuple[str, ...]


CHECKS = (
    Check(
        "sparse upper hybrid",
        ("python3", "./scripts/generate_sparse_upper_hybrid.py", "--check"),
    ),
    Check(
        "sparse upper contour",
        ("lake", "env", "lean", "--run", "scripts/GenerateSparseUpperContour.lean", "--check"),
    ),
    Check(
        "contour-family fixture",
        ("lake", "env", "lean", "--run", "scripts/GenerateSparseUpperContourFamilyFixture.lean", "--check"),
    ),
    Check(
        "rows192 bits128 threshold287",
        ("lake", "env", "lean", "--run", "scripts/GenerateSparseUpperContourFamilyRows192Bits128Threshold287.lean", "--check"),
    ),
    Check(
        "rows256 bits152 threshold365",
        ("lake", "env", "lean", "--run", "scripts/GenerateSparseUpperContourFamilyRows256Bits152Threshold365.lean", "--check"),
    ),
    Check(
        "rows256 bits192 threshold406",
        ("lake", "env", "lean", "--run", "scripts/GenerateSparseUpperContourFamilyRows256Bits192Threshold406.lean", "--check"),
    ),
    Check(
        "rows384 bits192 threshold509",
        ("lake", "env", "lean", "--run", "scripts/GenerateSparseUpperContourFamilyRows384Bits192Threshold509.lean", "--check"),
    ),
    Check(
        "rows512 bits256 threshold681",
        ("lake", "env", "lean", "--run", "scripts/GenerateSparseUpperContourFamilyRows512Bits256Threshold681.lean", "--check"),
    ),
)


def worker_count(environ: dict[str, str] | os._Environ[str] = os.environ) -> int:
    try:
        lake_workers = int(environ.get("LEAN_NUM_THREADS", "2"))
    except ValueError as error:
        raise SystemExit("LEAN_NUM_THREADS must be a positive integer") from error
    if lake_workers < 1:
        raise SystemExit("LEAN_NUM_THREADS must be a positive integer")
    return min(lake_workers, MAX_WORKERS, len(CHECKS))


class Processes:
    """Own child process groups so interruption also stops Lake descendants."""

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.cancelled = False
        self.active: set[subprocess.Popen[str]] = set()

    def run(self, check: Check) -> subprocess.CompletedProcess[str]:
        with self.lock:
            if self.cancelled:
                return subprocess.CompletedProcess(check.command, 130, "")
            process = subprocess.Popen(
                check.command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, start_new_session=True,
            )
            self.active.add(process)
        try:
            output, _ = process.communicate()
            return subprocess.CompletedProcess(check.command, process.returncode, output)
        finally:
            with self.lock:
                self.active.discard(process)

    def stop(self) -> None:
        with self.lock:
            self.cancelled = True
            active = tuple(self.active)
        # Kill whole groups, including descendants still holding output pipes.
        # SIGKILL is intentional here: these checks produce no release receipt
        # or durable output, and cancellation must not wait for Lean to finish.
        for process in active:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass


def main() -> None:
    failures: list[str] = []
    processes = Processes()

    def interrupted(signum: int, _frame: object) -> None:
        raise SystemExit(128 + signum)

    previous = {sig: signal.signal(sig, interrupted) for sig in (signal.SIGINT, signal.SIGTERM)}
    executor = ThreadPoolExecutor(max_workers=worker_count())
    try:
        pending = {executor.submit(processes.run, check): check for check in CHECKS}
        for future in as_completed(pending):
            check = pending[future]
            result = future.result()
            print(f"# Generation check: {check.label}")
            if result.stdout:
                print(result.stdout, end="" if result.stdout.endswith("\n") else "\n")
            if result.returncode:
                failures.append(f"{check.label} (exit {result.returncode})")
    finally:
        # Do this before executor shutdown: its default wait would otherwise
        # let interrupted generation jobs run to completion.
        processes.stop()
        executor.shutdown(wait=True, cancel_futures=True)
        for sig, handler in previous.items():
            signal.signal(sig, handler)

    if failures:
        raise SystemExit("generation checks failed: " + ", ".join(failures))
    print(f"balanced-ternary upper generation checks passed: {len(CHECKS)} checks")


if __name__ == "__main__":
    main()
