#!/usr/bin/env python3

from __future__ import annotations

import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
VALIDATE = ROOT / "scripts/validate.sh"


class ValidateDispatchTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)
        shutil.copy2(VALIDATE, scripts / "validate.sh")
        for target in (
            "validate_fast.sh",
            "validate_native.sh",
            "validate_certificates.sh",
            "validate_samples.sh",
        ):
            path = scripts / target
            path.write_text(
                '#!/usr/bin/env bash\nprintf \'%s\\n\' "$@" > "$VALIDATE_CAPTURE"\n',
                encoding="utf-8",
            )
            path.chmod(path.stat().st_mode | stat.S_IXUSR)
        self.capture = self.root / "captured-arguments"
        self.environ = os.environ | {"VALIDATE_CAPTURE": str(self.capture)}
        (scripts / "release_validation.py").write_text(
            'import os, sys\nfrom pathlib import Path\n'
            'Path(os.environ["VALIDATE_CAPTURE"]).write_text("\\n".join(sys.argv[1:]))\n'
        )

    def run_validate(self, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["./scripts/validate.sh", *arguments],
            cwd=self.root,
            env=self.environ,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )

    def test_native_options_are_forwarded_exactly(self) -> None:
        result = self.run_validate(
            "native", "--reuse-from", "/tmp/prior-runtime", "--plan-only"
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            self.capture.read_text(encoding="utf-8").splitlines(),
            ["--reuse-from", "/tmp/prior-runtime", "--plan-only"],
        )

    def test_sample_base_is_forwarded_exactly(self) -> None:
        result = self.run_validate("samples", "--base", "base-revision")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            self.capture.read_text(encoding="utf-8").splitlines(),
            ["--base", "base-revision"],
        )

    def test_fast_and_kernel_reject_extra_arguments(self) -> None:
        for mode in ("fast", "kernel", "full"):
            with self.subTest(mode=mode):
                self.capture.unlink(missing_ok=True)
                result = self.run_validate(mode, "--unexpected")
                self.assertEqual(result.returncode, 2)
                self.assertIn("usage:", result.stderr)
                self.assertFalse(self.capture.exists())

    def test_full_requires_explicit_output_and_uses_cold_release_runner(self) -> None:
        result = self.run_validate("full")
        self.assertEqual(result.returncode, 2)
        result = self.run_validate("full", "--output-dir", "/tmp/new-release")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.capture.read_text().splitlines(),
                         ["run", "--output-dir", "/tmp/new-release"])


if __name__ == "__main__":
    unittest.main()
