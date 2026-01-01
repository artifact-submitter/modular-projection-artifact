#!/usr/bin/env python3
"""Validate the timeless mapping from certificate contracts to replay roots."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import shlex
import sys

try:
    import tomllib
except ModuleNotFoundError as exc:  # pragma: no cover - exercised by old hosts
    raise SystemExit("Python 3.11 or newer is required") from exc


ROOT = Path(__file__).resolve().parent.parent
CERTIFICATES = ROOT / "evidence/certificates/public-results.toml"
FAMILIES = ROOT / "evidence/certificates/replay-families.toml"


def module_source(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def full_replay_root(command: str) -> str:
    words = shlex.split(command)
    if words[:2] != ["lake", "build"] or len(words) != 3:
        raise SystemExit(
            "certificate full_replay must have the canonical form "
            f"`lake build MODULE`, got: {command}"
        )
    return words[2]


def load() -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    with CERTIFICATES.open("rb") as stream:
        certificates = tomllib.load(stream).get("certificate", [])
    with FAMILIES.open("rb") as stream:
        document = tomllib.load(stream)
    if document.get("schema_version") != 1:
        raise SystemExit("unsupported replay-family schema version")
    families = document.get("family", [])
    return certificates, families


def validate() -> list[dict[str, object]]:
    certificates, families = load()
    by_id = {str(record["id"]): record for record in certificates}
    if len(by_id) != len(certificates):
        raise SystemExit("certificate IDs must be unique")

    family_ids: set[str] = set()
    assigned: dict[str, str] = {}
    normalized: list[dict[str, object]] = []
    for family in families:
        family_id = str(family.get("id", ""))
        if not family_id or family_id in family_ids:
            raise SystemExit(f"invalid or duplicate replay-family ID: {family_id!r}")
        family_ids.add(family_id)

        certificate_ids = [str(value) for value in family.get("certificate_ids", [])]
        roots = [str(value) for value in family.get("replay_roots", [])]
        if not certificate_ids or not roots:
            raise SystemExit(f"{family_id}: certificate_ids and replay_roots are required")
        if len(set(certificate_ids)) != len(certificate_ids):
            raise SystemExit(f"{family_id}: duplicate certificate ID")
        if len(set(roots)) != len(roots):
            raise SystemExit(f"{family_id}: duplicate replay root")

        required_roots: set[str] = set()
        for certificate_id in certificate_ids:
            if certificate_id not in by_id:
                raise SystemExit(f"{family_id}: unknown certificate {certificate_id}")
            if certificate_id in assigned:
                raise SystemExit(
                    f"{certificate_id}: assigned to both {assigned[certificate_id]} "
                    f"and {family_id}"
                )
            assigned[certificate_id] = family_id
            required_roots.add(full_replay_root(str(by_id[certificate_id]["full_replay"])))

        missing = sorted(required_roots.difference(roots))
        if missing:
            raise SystemExit(
                f"{family_id}: replay roots do not cover cataloged full replays: {missing}"
            )
        extra = sorted(set(roots).difference(required_roots))
        if extra:
            raise SystemExit(
                f"{family_id}: replay roots exceed cataloged full replays: {extra}"
            )
        for root in roots:
            source = module_source(root)
            if not source.is_file():
                raise SystemExit(f"{family_id}: missing replay-root module {root}")

        normalized.append(
            {
                "id": family_id,
                "certificate_ids": certificate_ids,
                "replay_roots": roots,
            }
        )

    unassigned = sorted(set(by_id).difference(assigned))
    if unassigned:
        raise SystemExit(f"certificates without a replay family: {unassigned}")
    return normalized


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--json", action="store_true", help="write the normalized replay plan as JSON"
    )
    args = parser.parse_args()
    plan = validate()
    if args.json:
        json.dump({"schema_version": 1, "families": plan}, sys.stdout, indent=2)
        print()
    else:
        roots = {root for family in plan for root in family["replay_roots"]}
        print(
            f"Validated {len(plan)} replay families, "
            f"{sum(len(f['certificate_ids']) for f in plan)} certificates, "
            f"and {len(roots)} distinct replay roots."
        )


if __name__ == "__main__":
    main()
