#!/usr/bin/env python3

from __future__ import annotations

from unittest.mock import patch
import unittest

from sample_selection import (
    Snapshot, select_for_repository, select_from_paths, validate_sample_boundaries,
)


def entry(identifier: str, sample: str, checker: str, data: str) -> dict:
    return {
        "id": identifier,
        "sample_modules": [sample],
        "data_modules": [data],
        "verified_module": f"Verified.{identifier}",
        "checker": checker,
    }


class SampleSelectionTests(unittest.TestCase):
    def snapshots(self) -> tuple[Snapshot, Snapshot]:
        entries = (
            entry("a", "Sample.A", "Checker.a", "Data.A"),
            entry("b", "Sample.B", "Checker.b", "Data.B"),
        )
        current = Snapshot(
            entries,
            {
                "Sample.A": ("Shared.Source",),
                "Sample.B": ("Shared.Source",),
                "Shared.Source": (),
                "Replay.A": ("Replay.A.UnselectedShard",),
                "Replay.A.UnselectedShard": (),
                "Replay.B": (),
            },
            {
                "Sample.A": "Sample/A.lean", "Sample.B": "Sample/B.lean",
                "Shared.Source": "Shared/Source.lean",
                "Replay.A": "Replay/A.lean",
                "Replay.A.UnselectedShard": "Replay/A/UnselectedShard.lean",
                "Replay.B": "Replay/B.lean",
                "Data.A": "Data/A.lean", "Data.B": "Data/B.lean",
                "Verified.a": "Verified/a.lean", "Verified.b": "Verified/b.lean",
            },
            {"Checker.a": "Checker/A.lean", "Checker.b": "Checker/B.lean"},
            {"a": ("Replay.A",), "b": ("Replay.B",)},
        )
        old = Snapshot(
            entries,
            current.graph | {"Sample.A": ("Shared.Source", "Old.Dependency"), "Old.Dependency": ()},
            current.module_paths | {"Old.Dependency": "Old/Dependency.lean"},
            current.declaration_owners,
            current.replay_roots,
        )
        return current, old

    def test_unselected_production_shard_selects_owning_family_sample(self) -> None:
        current, old = self.snapshots()
        result = select_from_paths(current, old, {"Replay/A/UnselectedShard.lean"})
        self.assertEqual(result.modules, ("Sample.A",))

    def test_changed_cataloged_data_selects_owning_sample(self) -> None:
        current, old = self.snapshots()
        result = select_from_paths(current, old, {"Data/B.lean"})
        self.assertEqual(result.modules, ("Sample.B",))

    def test_checker_change_selects_its_sample(self) -> None:
        current, old = self.snapshots()
        result = select_from_paths(current, old, {"Checker/B.lean"})
        self.assertEqual(result.modules, ("Sample.B",))

    def test_shared_source_selects_every_dependent_sample(self) -> None:
        current, old = self.snapshots()
        result = select_from_paths(current, old, {"Shared/Source.lean"})
        self.assertEqual(result.modules, ("Sample.A", "Sample.B"))

    def test_deleted_dependency_is_found_in_base_closure(self) -> None:
        current, old = self.snapshots()
        result = select_from_paths(current, old, {"Old/Dependency.lean"})
        self.assertEqual(result.modules, ("Sample.A",))

    def test_rename_checks_both_old_and_new_paths(self) -> None:
        current, old = self.snapshots()
        renamed = {"Old/Dependency.lean", "Shared/Source.lean"}
        result = select_from_paths(current, old, renamed)
        self.assertEqual(result.modules, ("Sample.A", "Sample.B"))

    def test_documentation_only_change_selects_nothing(self) -> None:
        current, old = self.snapshots()
        result = select_from_paths(current, old, {"docs/guide.md"})
        self.assertEqual(result.modules, ())
        self.assertFalse(result.fail_closed)

    def test_catalog_or_script_change_fails_closed_to_all_samples(self) -> None:
        current, old = self.snapshots()
        for path in ("evidence/certificates/public-results.toml", "scripts/checker.py"):
            with self.subTest(path=path):
                result = select_from_paths(current, old, {path})
                self.assertEqual(result.modules, ("Sample.A", "Sample.B"))
                self.assertTrue(result.fail_closed)

    def test_unknown_base_fails_closed_to_all_samples(self) -> None:
        current, _ = self.snapshots()
        with patch("sample_selection.repository_is_dirty", return_value=False), patch(
            "sample_selection.changed_paths_since", side_effect=ValueError("unknown base")
        ):
            result = select_for_repository("missing", current=current)
        self.assertEqual(result.modules, ("Sample.A", "Sample.B"))
        self.assertTrue(result.fail_closed)

    def test_dirty_working_tree_fails_closed_to_all_samples(self) -> None:
        current, _ = self.snapshots()
        with patch("sample_selection.repository_is_dirty", return_value=True):
            result = select_for_repository("HEAD", current=current)
        self.assertEqual(result.modules, ("Sample.A", "Sample.B"))
        self.assertIn("working tree", result.reason)

    def test_sample_cannot_import_another_provider_root(self) -> None:
        current, _ = self.snapshots()
        changed_graph = current.graph | {"Sample.A": ("Verified.b",)}
        changed = Snapshot(
            current.entries, changed_graph, current.module_paths,
            current.declaration_owners, current.replay_roots,
        )
        with self.assertRaisesRegex(ValueError, "another replay/provider root"):
            validate_sample_boundaries(changed)


if __name__ == "__main__":
    unittest.main()
