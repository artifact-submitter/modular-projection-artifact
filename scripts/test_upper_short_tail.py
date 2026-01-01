#!/usr/bin/env python3
"""Guard the production prefix geometry and frozen-endpoint generation."""
import unittest
import generate_upper_short_tail as generator
from check_fast_import_boundary import graph, path_to_forbidden
from fast_validation_roots import EXACT_ONLY_ROOTS


class ShortTailTests(unittest.TestCase):
    def test_retained_geometry(self):
        self.assertEqual(generator.COUNTS, [15, 12, 10, 9, 8, 7, 6, 5, 4, 3])
        self.assertEqual(sum(generator.COUNTS), 79)
        self.assertEqual(sum(generator.COUNTS) * 25, 1975)

    def test_generated_replay_exact(self):
        outputs = generator.outputs()
        self.assertEqual(len(outputs), 25)
        for path, expected in outputs.items():
            self.assertEqual(path.read_text(), expected, str(path))
        shards = [text for path, text in outputs.items() if "Shards" in path.parts]
        self.assertEqual(sum(text.count("decide +kernel") for text in shards), 79)
        for text in shards:
            self.assertNotIn("Rows512Bits192.Replay", text)
        verified = outputs[generator.BASE / "ShortTail/Replay/Verified.lean"]
        self.assertIn("Soundness.HighProfile", verified)

    def test_no_experimental_replay_in_default_provider(self):
        experimental = generator.PREFIX + ".Replay"
        self.assertIn(experimental, EXACT_ONLY_ROOTS)
        self.assertIsNone(
            path_to_forbidden(graph(), generator.PREFIX + ".Provider", {experimental})
        )


if __name__ == "__main__":
    unittest.main()
