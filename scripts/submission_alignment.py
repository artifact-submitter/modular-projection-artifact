#!/usr/bin/env python3
"""Prepare an alignment checklist or record an explicitly completed human review.

This records an author's attestation; it does not establish mathematical
correspondence automatically. Agents must not supply that attestation on behalf
of a human who has not performed the review.
"""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys

from proof_bundle import (
    BundleError, _paper_inventory, alignment_review_digest,
    canonical_digest, verify_proof_bundle,
)


def prepare(paper_root: Path, proof_bundle: Path, *, verified_manifest: dict | None = None) -> dict:
    manifest = (verify_proof_bundle(proof_bundle)
                if verified_manifest is None else verified_manifest)
    record = {
        "schema_version": 1,
        "record_kind": "certifiedjl-manuscript-proof-alignment-review",
        "attests_human_review": False,
        "reviewer": "",
        "reviewed_utc": "",
        "paper_tree_digest": canonical_digest(
            "CertifiedJL-final-paper-tree-v1", _paper_inventory(paper_root),
        ),
        "proof_bundle_id": manifest["bundle_id"],
        "theorem_map_sha256": manifest["reviewer_workspace"]["theorem_map_sha256"],
    }
    record["review_digest"] = alignment_review_digest(record)
    return record


def record_review(pending: dict, expected: dict, reviewer: str) -> dict:
    if pending != expected:
        raise BundleError("pending checklist differs from the current paper and proof bundle; prepare it again")
    if not reviewer.strip():
        raise BundleError("reviewer name must not be blank")
    record = dict(pending)
    record.update(
        attests_human_review=True, reviewer=reviewer.strip(),
        reviewed_utc=datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
    )
    record["review_digest"] = alignment_review_digest(record)
    return record


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("prepare", "record-review"):
        command = commands.add_parser(name)
        command.add_argument("--paper-root", type=Path, required=True)
        command.add_argument("--proof-bundle", type=Path, required=True)
        command.add_argument("--output", type=Path, required=True)
        if name == "record-review":
            command.add_argument("--pending", type=Path, required=True)
            command.add_argument("--reviewer", required=True)
            command.add_argument(
                "--attest-reviewed", action="store_true", required=True,
                help="attest that the named human has actually reviewed the paper against the mapped Lean statements",
            )
    args = parser.parse_args(argv)
    try:
        manifest = verify_proof_bundle(args.proof_bundle)
        expected = prepare(args.paper_root, args.proof_bundle, verified_manifest=manifest)
        if args.command == "prepare":
            result = expected
        else:
            if (manifest.get("anonymous_source") is True
                    and args.reviewer != manifest["review_guidance"]["review_role"]):
                raise BundleError(
                    "anonymous review requires the fixed public role "
                    + manifest["review_guidance"]["review_role"]
                    + "; keep the actual human identity in private records"
                )
            result = record_review(
                json.loads(args.pending.read_text()), expected, args.reviewer,
            )
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8") as stream:
            json.dump(result, stream, indent=2, sort_keys=True)
            stream.write("\n")
        print("Pending human review; not valid for submission." if args.command == "prepare"
              else "Recorded the named reviewer's explicit attestation.")
        return 0
    except (BundleError, OSError, ValueError) as error:
        print(f"alignment: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
