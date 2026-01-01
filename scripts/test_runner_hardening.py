#!/usr/bin/env python3

from __future__ import annotations

import unittest

import check_runner_hardening


class RunnerHardeningTests(unittest.TestCase):
    def test_committed_configuration_passes(self) -> None:
        check_runner_hardening.check()

    def test_process_only_kill_mode_is_rejected(self) -> None:
        settings = {
            key.lower(): value
            for key, value in check_runner_hardening.REQUIRED_SERVICE_SETTINGS.items()
        }
        settings["killmode"] = "process"
        with self.assertRaisesRegex(SystemExit, "service guard mismatch"):
            check_runner_hardening.validate_service_settings(settings)


if __name__ == "__main__":
    unittest.main()
