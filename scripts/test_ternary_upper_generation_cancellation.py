#!/usr/bin/env python3
"""Exercise cancellation against real subprocesses without running Lean."""

import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest


SCRIPTS = Path(__file__).resolve().parent


class CancellationTests(unittest.TestCase):
    def test_interrupt_and_termination_stop_descendants(self) -> None:
        for stop_signal in (signal.SIGINT, signal.SIGTERM):
            with self.subTest(signal=stop_signal), tempfile.TemporaryDirectory() as directory:
                ready = Path(directory) / "ready"
                # The grandchild keeps the output pipe open. Killing only its
                # parent therefore cannot let the orchestrator finish.
                grandchild = (
                    "import pathlib,time; "
                    f"pathlib.Path({str(ready)!r}).touch(); time.sleep(60)"
                )
                child = (
                    "import subprocess,sys,time; "
                    f"subprocess.Popen([sys.executable, '-c', {grandchild!r}]); "
                    "time.sleep(60)"
                )
                driver = (
                    f"import sys; sys.path.insert(0, {str(SCRIPTS)!r}); "
                    "import run_ternary_upper_generation_checks as checks; "
                    f"checks.CHECKS = (checks.Check('sleeping tree', (sys.executable, '-c', {child!r})),); "
                    "checks.main()"
                )
                process = subprocess.Popen(
                    [sys.executable, "-c", driver], stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT, text=True,
                )
                try:
                    deadline = time.monotonic() + 10
                    while not ready.exists() and process.poll() is None:
                        if time.monotonic() >= deadline:
                            self.fail("child process did not become ready")
                        time.sleep(0.02)
                    self.assertTrue(ready.exists())
                    os.kill(process.pid, stop_signal)
                    output, _ = process.communicate(timeout=5)
                    self.assertEqual(process.returncode, 128 + stop_signal, output)
                finally:
                    if process.poll() is None:
                        process.kill()
                        process.wait()


if __name__ == "__main__":
    unittest.main()
