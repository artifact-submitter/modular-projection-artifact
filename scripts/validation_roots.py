#!/usr/bin/env python3
"""Validate and expose the bounded Lean validation build plan."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import tomllib
from typing import Mapping

import check_replay_families
from certificate_catalog import ROOT, module_source


PLAN = ROOT / "evidence" / "validation-roots.toml"
ENVIRONMENT_NAME = re.compile(r"[A-Z][A-Z0-9_]*")


def _positive_integer(value: object, context: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise SystemExit(f"{context}: batch_size must be a positive integer")
    return value


def _common(record: dict[str, object], kind: str) -> dict[str, object]:
    group_id = record.get("id")
    if not isinstance(group_id, str) or not group_id:
        raise SystemExit(f"{kind}: nonempty string id is required")
    batch_size = _positive_integer(record.get("batch_size"), group_id)
    batch_size_env = record.get("batch_size_env")
    if not isinstance(batch_size_env, str) or ENVIRONMENT_NAME.fullmatch(
        batch_size_env
    ) is None:
        raise SystemExit(f"{group_id}: invalid batch_size_env {batch_size_env!r}")
    return {
        "id": group_id,
        "kind": kind,
        "batch_size": batch_size,
        "batch_size_env": batch_size_env,
    }


def load_plan(path: Path = PLAN) -> dict[str, dict[str, object]]:
    with path.open("rb") as stream:
        document = tomllib.load(stream)
    if document.get("schema_version") != 1:
        raise SystemExit("unsupported validation-root schema version")

    answer: dict[str, dict[str, object]] = {}
    for record in document.get("lean_group", []):
        normalized = _common(record, "lean")
        group_id = str(normalized["id"])
        roots = record.get("roots")
        if not isinstance(roots, list) or not roots or not all(
            isinstance(root, str) and root for root in roots
        ):
            raise SystemExit(f"{group_id}: nonempty roots list is required")
        if len(set(roots)) != len(roots):
            raise SystemExit(f"{group_id}: duplicate Lean root")
        for root in roots:
            if not module_source(root).is_file():
                raise SystemExit(f"{group_id}: missing Lean root {root}")
        normalized["targets"] = list(roots)
        if group_id in answer:
            raise SystemExit(f"duplicate validation group: {group_id}")
        answer[group_id] = normalized

    replay_plan = {
        str(family["id"]): family for family in check_replay_families.validate()
    }
    for record in document.get("replay_group", []):
        normalized = _common(record, "replay")
        group_id = str(normalized["id"])
        family_ids = record.get("family_ids")
        if not isinstance(family_ids, list) or not family_ids or not all(
            isinstance(family, str) and family for family in family_ids
        ):
            raise SystemExit(f"{group_id}: nonempty family_ids list is required")
        if len(set(family_ids)) != len(family_ids):
            raise SystemExit(f"{group_id}: duplicate replay family")
        targets: list[str] = []
        for family_id in family_ids:
            family = replay_plan.get(family_id)
            if family is None:
                raise SystemExit(f"{group_id}: unknown replay family {family_id}")
            targets.extend(str(root) for root in family["replay_roots"])
        if len(set(targets)) != len(targets):
            raise SystemExit(f"{group_id}: replay roots overlap between families")
        normalized["family_ids"] = list(family_ids)
        normalized["targets"] = targets
        if group_id in answer:
            raise SystemExit(f"duplicate validation group: {group_id}")
        answer[group_id] = normalized

    if not answer:
        raise SystemExit("validation-root plan is empty")
    return answer


def group(group_id: str, path: Path = PLAN) -> dict[str, object]:
    record = load_plan(path).get(group_id)
    if record is None:
        raise SystemExit(f"unknown validation group: {group_id}")
    return record


def targets(group_id: str, path: Path = PLAN) -> list[str]:
    return list(group(group_id, path)["targets"])


def batch_size(
    group_id: str,
    path: Path = PLAN,
    environ: Mapping[str, str] = os.environ,
) -> int:
    record = group(group_id, path)
    environment_name = str(record["batch_size_env"])
    raw = environ.get(environment_name)
    if raw is None:
        return int(record["batch_size"])
    if re.fullmatch(r"[1-9][0-9]*", raw) is None:
        raise SystemExit(f"{environment_name} must be a positive integer")
    return int(raw)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("group", help="validation group ID")
    parser.add_argument(
        "--batch-size", action="store_true", help="print the resolved batch size"
    )
    parser.add_argument(
        "--describe", action="store_true", help="print a one-line plan summary"
    )
    args = parser.parse_args()
    record = group(args.group)
    resolved_targets = list(record["targets"])
    if args.batch_size:
        print(batch_size(args.group))
    elif args.describe:
        print(
            f"{args.group}: {len(resolved_targets)} {record['kind']} targets, "
            f"batch size {batch_size(args.group)}"
        )
    else:
        for target in resolved_targets:
            print(target)


if __name__ == "__main__":
    main()
