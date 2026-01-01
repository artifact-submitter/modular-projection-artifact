#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from compute_fast_cache_key import BUILD_CONFIGURATION, cache_inputs, input_digest


class FastBuildCacheKeyTests(unittest.TestCase):
    def fixture(
        self, root: Path
    ) -> tuple[dict[str, tuple[str, ...]], list[dict], set[str]]:
        graph = {
            "Fast.Root": ("Shared.Dependency",),
            "Shared.Dependency": (),
            "Sample.Root": ("Sample.Dependency",),
            "Sample.Dependency": (),
        }
        entries = [
            {
                "id": "fixture",
                "sample_modules": ["Sample.Root"],
                "verified_module": "Exact.Verified",
                "replay_roots": ["Exact.Replay"],
            }
        ]
        for module in graph:
            source = root / (module.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(f"-- {module}\n")
        for relative in BUILD_CONFIGURATION:
            (root / relative).write_text(f"{relative}\n")
        return graph, entries, {"Fast.Root"}

    def test_key_covers_every_fast_transitive_source_but_not_samples(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph, entries, roots = self.fixture(root)
            sources, fast_modules = cache_inputs(graph, entries, roots, root)
            self.assertEqual(fast_modules, {"Fast.Root", "Shared.Dependency"})
            for module in fast_modules:
                self.assertIn(root / (module.replace(".", "/") + ".lean"), sources)
            for module in ("Sample.Root", "Sample.Dependency"):
                self.assertNotIn(root / (module.replace(".", "/") + ".lean"), sources)

    def test_transitive_lean_change_changes_key(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph, entries, roots = self.fixture(root)
            sources, _ = cache_inputs(graph, entries, roots, root)
            before = input_digest(sources, root)
            dependency = root / "Shared/Dependency.lean"
            dependency.write_text("-- changed transitive dependency\n")
            self.assertNotEqual(before, input_digest(sources, root))

    def test_added_transitive_source_enters_key(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph, entries, roots = self.fixture(root)
            added = root / "New/Dependency.lean"
            added.parent.mkdir(parents=True)
            added.write_text("-- newly imported\n")
            graph["Fast.Root"] = ("Shared.Dependency", "New.Dependency")
            graph["New.Dependency"] = ()
            sources, fast_modules = cache_inputs(graph, entries, roots, root)
            self.assertIn("New.Dependency", fast_modules)
            self.assertIn(added, sources)

    def test_build_configuration_change_changes_key(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph, entries, roots = self.fixture(root)
            sources, _ = cache_inputs(graph, entries, roots, root)
            before = input_digest(sources, root)
            (root / "lean-toolchain").write_text("changed-toolchain\n")
            self.assertNotEqual(before, input_digest(sources, root))

    def test_validation_metadata_does_not_churn_build_key(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph, entries, roots = self.fixture(root)
            sources, _ = cache_inputs(graph, entries, roots, root)
            before = input_digest(sources, root)
            metadata = root / "evidence/theorem-contract.toml"
            metadata.parent.mkdir(parents=True)
            metadata.write_text("status = 'before'\n")
            metadata.write_text("status = 'after'\n")
            self.assertNotIn(metadata, sources)
            self.assertEqual(before, input_digest(sources, root))

    def test_fast_closure_cannot_reach_a_declared_sample_leaf(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph, entries, roots = self.fixture(root)
            graph["Fast.Root"] = ("Bridge",)
            graph["Bridge"] = ("Sample.Root",)
            bridge = root / "Bridge.lean"
            bridge.write_text("-- bridge\n")
            with self.assertRaisesRegex(SystemExit, "Sample.Root"):
                cache_inputs(graph, entries, roots, root)


if __name__ == "__main__":
    unittest.main()
