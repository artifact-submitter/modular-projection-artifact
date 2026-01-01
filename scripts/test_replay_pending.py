#!/usr/bin/env python3
"""A pending replay must not bypass production declaration checks."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_contract


class PendingReplayTests(unittest.TestCase):
    def test_pending_declaration_must_exist(self):
        record = {
            "verification_class": "replay_pending",
            "analytic_owner": "Example.lean",
            "lean": "Example.present",
        }
        with tempfile.TemporaryDirectory() as tmp, patch.object(check_contract, "ROOT", Path(tmp)):
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                check_contract.check_lean_declarations([record])
            Path(tmp, "Example.lean").write_text(
                "namespace Example\ntheorem present : True := by trivial\nend Example\n")
            check_contract.check_lean_declarations([record])
            record["lean"] = "Example.absent"
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                check_contract.check_lean_declarations([record])


if __name__ == "__main__":
    unittest.main()
