#!/usr/bin/env python3
"""Keep shared dominant caps local to the requested four-cell shard."""

import unittest

from check_fast_import_boundary import graph

PREFIX = "CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay."


def reachable(imports, root):
    seen = set()
    pending = [root]
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(imports.get(module, ()))
    return seen


class DominantSharedCapsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.imports = graph()

    def test_target_shards_do_not_import_other_cap_shards(self):
        families = ["192Bits128", "256Bits192", "384Bits192",
                    "512Bits192", "512Floor73Bits193"]
        for family in families:
            for index in range(47):
                suffix = f"{index:02d}"
                root = PREFIX + f"ConstantDirectCover{family}.Shard{suffix}"
                self.assertIn(root, self.imports)
                closure = reachable(self.imports, root)
                owns_caps = ((family == "192Bits128" and index == 23) or
                             (family in {"256Bits192", "384Bits192"} and
                              index in {2, 3}))
                if not owns_caps:
                    self.assertIn(PREFIX + "ConstantDirectCover128Shard" + suffix,
                                  closure, root + " lacks its proved base caps")
                for module in closure:
                    if not module.startswith(PREFIX):
                        continue
                    local = module.removeprefix(PREFIX)
                    if local.startswith("ConstantDirectCover128Shard"):
                        self.assertEqual(local, "ConstantDirectCover128Shard" + suffix)
                    if "RowCaps.Shard" in local:
                        self.assertTrue(local.endswith(".Shard" + suffix), module)
                    self.assertNotIn("Aggregate", local, module)
                    self.assertNotIn("Selector", local, module)

    def test_retuned_caps_are_shared_between_matching_targets(self):
        for index in (2, 3):
            shared = PREFIX + f"ConstantDirectCover256And384Bits192RowCaps.Shard{index:02d}"
            for family in ("256Bits192", "384Bits192"):
                root = PREFIX + f"ConstantDirectCover{family}.Shard{index:02d}"
                self.assertIn(shared, reachable(self.imports, root))


if __name__ == "__main__":
    unittest.main()
