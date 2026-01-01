#!/usr/bin/env python3

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts/run_builtin_lints_isolated.sh"


class IsolatedBuiltinLintTests(unittest.TestCase):
    def run_helper(
        self, roots: list[str], failing: str = ""
    ) -> tuple[subprocess.CompletedProcess[str], list[str]]:
        with tempfile.TemporaryDirectory() as temporary:
            temp = Path(temporary)
            log = temp / "lake.log"
            lake = temp / "lake"
            lake.write_text(
                "#!/usr/bin/env bash\n"
                "printf '%s\\n' \"$*\" >> \"$LAKE_STUB_LOG\"\n"
                "[[ ${3:-} != \"${LAKE_STUB_FAIL:-}\" ]]\n",
                encoding="utf-8",
            )
            lake.chmod(0o755)
            env = os.environ.copy()
            env.update(
                {
                    "PATH": f"{temp}{os.pathsep}{env['PATH']}",
                    "LAKE_STUB_LOG": str(log),
                    "LAKE_STUB_FAIL": failing,
                }
            )
            result = subprocess.run(
                [str(SCRIPT), *roots],
                cwd=ROOT,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            calls = log.read_text(encoding="utf-8").splitlines() if log.exists() else []
            return result, calls

    def test_runs_every_root_in_its_own_lake_process(self) -> None:
        result, calls = self.run_helper(["One", "Two", "Three"])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            calls,
            [
                "lint --builtin-only One",
                "lint --builtin-only Two",
                "lint --builtin-only Three",
            ],
        )

    def test_stops_at_the_first_failure_and_preserves_its_status(self) -> None:
        result, calls = self.run_helper(["One", "Two", "Three"], failing="Two")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(
            calls,
            ["lint --builtin-only One", "lint --builtin-only Two"],
        )


if __name__ == "__main__":
    unittest.main()
