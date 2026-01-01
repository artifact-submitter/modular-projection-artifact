#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from compute_sample_cache_key import sample_cache_inputs, sample_digest
from sample_selection import Snapshot


class SampleCacheKeyTests(unittest.TestCase):
    def test_key_includes_selected_roots_and_their_source_closure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph = {"Sample.A": ("Shared",), "Sample.B": ("Shared",), "Shared": ()}
            paths = {module: module.replace(".", "/") + ".lean" for module in graph}
            for module, relative in paths.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"-- {module}\n")
            for relative in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
                (root / relative).write_text(relative)
            snapshot = Snapshot((), graph, paths, {}, {})
            modules = ("Sample.A",)
            sources = sample_cache_inputs(modules, snapshot, root)
            before = sample_digest(modules, sources, root)
            (root / "Shared.lean").write_text("-- changed\n")
            self.assertNotEqual(before, sample_digest(modules, sources, root))
            self.assertNotEqual(
                before, sample_digest(("Sample.A", "Sample.B"), sources, root)
            )


if __name__ == "__main__":
    unittest.main()
