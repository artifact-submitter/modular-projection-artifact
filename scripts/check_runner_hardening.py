#!/usr/bin/env python3
"""Check the persistent self-hosted runner's failure-containment policy."""

from __future__ import annotations

import configparser
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
DROPIN = ROOT / "ops/certifiedjl-runner/actions-runner.service.conf"
INSTALLER = ROOT / "ops/certifiedjl-runner/install-service-guard.sh"

REQUIRED_SERVICE_SETTINGS = {
    "KillMode": "control-group",
    "TimeoutStopSec": "30s",
    "Restart": "always",
    "RestartSec": "5s",
    "OOMPolicy": "kill",
    "MemoryHigh": "12G",
    "MemoryMax": "14G",
    "MemorySwapMax": "1G",
}


def validate_service_settings(service: dict[str, str]) -> None:
    expected = {key.lower(): value for key, value in REQUIRED_SERVICE_SETTINGS.items()}
    if service != expected:
        raise SystemExit(
            f"runner service guard mismatch: expected {expected!r}, found {service!r}"
        )


def check() -> None:
    parser = configparser.ConfigParser()
    if parser.read(DROPIN, encoding="utf-8") != [str(DROPIN)]:
        raise SystemExit(f"missing runner service guard: {DROPIN}")
    if set(parser.sections()) != {"Service"}:
        raise SystemExit("runner service guard must contain exactly [Service]")
    validate_service_settings(dict(parser.items("Service")))

    installer = INSTALLER.read_text(encoding="utf-8")
    required_installer_fragments = (
        "actions.runner.anonymous-certified-jl.certified-jl-exe-dev.service",
        'pgrep -u actions -f "$runner_root/bin/Runner.Worker"',
        'install -m 0644 "$source_dir/actions-runner.service.conf"',
        '"$dropin_dir/override.conf"',
        'systemctl daemon-reload',
        'systemctl restart "$service"',
        'systemctl is-active --quiet "$service"',
    )
    for fragment in required_installer_fragments:
        if fragment not in installer:
            raise SystemExit(f"runner service guard installer is missing: {fragment}")


if __name__ == "__main__":
    check()
    print("Runner hardening configuration passed.")
