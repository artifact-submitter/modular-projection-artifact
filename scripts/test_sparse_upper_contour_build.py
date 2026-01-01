#!/usr/bin/env python3

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from run_ternary_upper_generation_checks import CHECKS, worker_count


ROOT = Path(__file__).resolve().parent.parent
SHORT_REPLAY = (
    ROOT
    / "CertifiedJL/Certificates/Families/L2Upper/Rows512Bits192/ShortTail/Replay"
)
FAMILY_REPLAY = (
    ROOT / "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Replay"
)
FAMILY_COUNTS = {
    "Rows192Bits128Threshold287": 30,
    "Rows256Bits152Threshold365": 30,
    "Rows256Bits192Threshold406": 30,
    "Rows384Bits192Threshold509": 51,
    "Rows512Bits256Threshold681": 70,
}


def module_name(path: Path) -> str:
    return path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")


def listed_targets(script: str) -> list[str]:
    result = subprocess.run(
        [str(ROOT / "scripts" / script), "--list-targets"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        check=True,
    )
    return result.stdout.splitlines()


class SparseUpperContourBuildTests(unittest.TestCase):
    def test_short_tail_enumeration_matches_every_checked_in_shard(self) -> None:
        expected = sorted(module_name(path) for path in SHORT_REPLAY.glob("Shards/*/Shard*.lean"))
        actual = listed_targets("build_sparse_upper_contour_proofs.sh")
        self.assertEqual(actual, expected)
        self.assertEqual(len(actual), 14)
        self.assertEqual(len(actual), len(set(actual)))

    def test_family_enumeration_matches_every_checked_in_shard(self) -> None:
        expected: list[str] = []
        for family, count in FAMILY_COUNTS.items():
            family_targets = sorted(
                module_name(path)
                for path in (FAMILY_REPLAY / family).glob("**/Shard*.lean")
            )
            self.assertEqual(len(family_targets), count)
            expected.extend(family_targets)
        actual = listed_targets("build_sparse_upper_contour_family_proofs.sh")
        self.assertEqual(actual, expected)
        self.assertEqual(len(actual), 211)
        self.assertEqual(len(actual), len(set(actual)))

    def test_all_batch_uses_one_lake_scheduler_without_dropping_targets(self) -> None:
        self.assertEqual(
            self.fake_lake_batches("all", ["Target.A", "Target.B", "Target.C"]),
            [["build", "Target.A", "Target.B", "Target.C"]],
        )

    def test_all_batch_accepts_the_complete_family_inventory(self) -> None:
        targets = listed_targets("build_sparse_upper_contour_family_proofs.sh")
        self.assertEqual(
            self.fake_lake_batches("all", targets),
            [["build", *targets]],
        )

    def test_numeric_batch_preserves_existing_chunking(self) -> None:
        self.assertEqual(
            self.fake_lake_batches(
                "2", ["Target.A", "Target.B", "Target.C", "Target.D", "Target.E"]
            ),
            [
                ["build", "Target.A", "Target.B"],
                ["build", "Target.C", "Target.D"],
                ["build", "Target.E"],
            ],
        )

    def test_generation_check_inventory_and_worker_cap_are_fixed(self) -> None:
        expected_sources = {
            "./scripts/generate_sparse_upper_hybrid.py",
            "scripts/GenerateSparseUpperContour.lean",
            "scripts/GenerateSparseUpperContourFamilyFixture.lean",
            "scripts/GenerateSparseUpperContourFamilyRows192Bits128Threshold287.lean",
            "scripts/GenerateSparseUpperContourFamilyRows256Bits152Threshold365.lean",
            "scripts/GenerateSparseUpperContourFamilyRows256Bits192Threshold406.lean",
            "scripts/GenerateSparseUpperContourFamilyRows384Bits192Threshold509.lean",
            "scripts/GenerateSparseUpperContourFamilyRows512Bits256Threshold681.lean",
        }
        actual_sources = {
            next(argument for argument in check.command if argument.endswith((".py", ".lean")))
            for check in CHECKS
        }
        self.assertEqual(actual_sources, expected_sources)
        self.assertTrue(all(check.command[-1] == "--check" for check in CHECKS))
        self.assertEqual(worker_count({"LEAN_NUM_THREADS": "1"}), 1)
        self.assertEqual(worker_count({"LEAN_NUM_THREADS": "2"}), 2)
        self.assertEqual(worker_count({"LEAN_NUM_THREADS": "64"}), 2)

    def fake_lake_batches(self, batch_size: str, targets: list[str]) -> list[list[str]]:
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            log = temp / "calls"
            fake_lake = temp / "lake"
            fake_lake.write_text(
                "#!/usr/bin/env bash\n"
                "printf '%s ' \"$@\" >> \"$CERTIFIEDJL_FAKE_LAKE_LOG\"\n"
                "printf '\\n' >> \"$CERTIFIEDJL_FAKE_LAKE_LOG\"\n",
                encoding="utf-8",
            )
            fake_lake.chmod(0o755)
            environment = os.environ.copy()
            environment["PATH"] = f"{temp}:{environment['PATH']}"
            environment["CERTIFIEDJL_FAKE_LAKE_LOG"] = str(log)
            subprocess.run(
                [
                    str(ROOT / "scripts/build_targets_in_batches.sh"),
                    batch_size,
                    *targets,
                ],
                cwd=ROOT,
                env=environment,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            )
            return [line.split() for line in log.read_text(encoding="utf-8").splitlines()]


if __name__ == "__main__":
    unittest.main()
