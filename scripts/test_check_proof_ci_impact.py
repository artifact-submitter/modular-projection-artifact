import unittest

from check_proof_ci_impact import affects_proofs


class ProofImpactTests(unittest.TestCase):
    def test_manuscript_only(self):
        self.assertFalse(affects_proofs(["paper/main.tex", "docs/reading-guide.md"]))

    def test_unknown_and_proof_inputs(self):
        for paths in [None, ["CertifiedJL/Results.lean"], ["lean-toolchain"],
                      ["lake-manifest.json"], ["new-root.lean"],
                      ["scripts/release_validation.py"], ["evidence/result-catalog.toml"],
                      ["paper/Unexpected.lean"], ["docs/Unexpected.lean"],
                      ["paper/artifact/verify_all.py"], ["paper/experiments/input.json"],
                      ["paper/generated/formalization-table.tex"],
                      ["paper/main.tex", "Vendor/Proof.lean"]]:
            with self.subTest(paths=paths):
                self.assertTrue(affects_proofs(paths))


if __name__ == "__main__":
    unittest.main()
