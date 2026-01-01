#!/usr/bin/env python3
"""Validate the schema and bounded-sample policy of the certificate catalog."""

from __future__ import annotations

import hashlib
import re
import shlex
import tomllib

from certificate_catalog import CATALOG, ROOT, certificates, load_catalog, module_source
from lean_source import LeanSourceError, qualified_declarations


REQUIRED = {
    "id", "group_id", "status", "result_ids", "parameters", "contract", "assembly",
    "verified_module", "verified_declaration", "fast_module",
    "fast_declaration", "fast_type", "checker", "soundness",
    "data_modules", "generated_roots", "payload_hash", "generator",
    "generator_version", "regenerate", "sample_modules", "full_replay",
    "production_axioms", "fast_axioms",
}
PAYLOAD_DOMAIN = b"CertifiedJL certificate payload v1\0"


def fail(message: str) -> None:
    raise SystemExit(f"certificate catalog error: {message}")


def declarations(module: str) -> set[str]:
    path = module_source(module)
    if not path.is_file():
        fail(f"missing module {module}")
    try:
        return qualified_declarations(path.read_text(encoding="utf-8"), module)
    except LeanSourceError as error:
        fail(str(error))


def computed_payload_hash(entry: dict) -> str:
    digest = hashlib.sha256()
    digest.update(PAYLOAD_DOMAIN)
    for module in entry["data_modules"]:
        path = module_source(module)
        if not path.is_file():
            fail(f"{entry['id']}: missing data module {module}")
        relative = path.relative_to(ROOT).as_posix().encode("utf-8")
        payload = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
    return f"sha256:{digest.hexdigest()}"


def validate_reproduction_metadata(entry: dict) -> None:
    generator = str(entry["generator"])
    if generator.startswith("scripts/") and not (ROOT / generator).is_file():
        fail(f"{entry['id']}: missing generator {generator}")
    try:
        command = shlex.split(str(entry["regenerate"]))
    except ValueError as error:
        fail(f"{entry['id']}: malformed regenerate command: {error}")
    if not command:
        fail(f"{entry['id']}: empty regenerate command")
    for argument in command:
        if argument == "." or not argument.startswith(
            ("scripts/", "paper/", "CertifiedJL/")
        ):
            continue
        if not (ROOT / argument).exists():
            fail(f"{entry['id']}: regenerate input does not exist: {argument}")


def resolve_semantic_declarations(entries: list[dict]) -> None:
    fields = ("contract", "assembly", "checker", "soundness")
    wanted = {entry[field] for entry in entries for field in fields}
    leaves = {name.rsplit(".", 1)[-1] for name in wanted}
    found: set[str] = set()
    for path in sorted((ROOT / "CertifiedJL").rglob("*.lean")):
        if "Tests" in path.relative_to(ROOT).parts:
            continue
        source = path.read_text(encoding="utf-8")
        if not any(re.search(
            rf"(?m)^\s*(?:noncomputable\s+)?(?:def|theorem|lemma|axiom|structure)\s+{re.escape(leaf)}\b",
            source,
        ) for leaf in leaves):
            continue
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        try:
            found.update(qualified_declarations(source, module) & wanted)
        except LeanSourceError as error:
            fail(str(error))
    missing = sorted(wanted - found)
    if missing:
        fail(f"unresolved semantic declarations: {missing}")


def main() -> None:
    catalog = load_catalog()
    if catalog.get("schema_version") != 1:
        fail("schema_version must be 1")
    if catalog.get("payload_hash_algorithm") != "sha256":
        fail("payload_hash_algorithm must be sha256")
    if catalog.get("payload_encoding") != "certifiedjl-ordered-module-source-v1":
        fail("unsupported payload encoding")
    entries = certificates()
    resolve_semantic_declarations(entries)
    with (ROOT / "evidence" / "result-catalog.toml").open("rb") as source:
        results = tomllib.load(source).get("result", [])
    result_groups = {
        result["id"]: set(result["certificate_ids"]) for result in results
    }
    ids: set[str] = set()
    fast_declarations: set[str] = set()
    for entry in entries:
        missing = sorted(REQUIRED - entry.keys())
        if missing:
            fail(f"{entry.get('id', '<unnamed>')}: missing {missing}")
        if entry["status"] != "converted":
            fail(f"{entry['id']}: certificate entries must be converted")
        if entry["id"] in ids:
            fail(f"duplicate id {entry['id']}")
        ids.add(entry["id"])
        declaration = entry["fast_declaration"]
        if declaration in fast_declarations:
            fail(f"duplicate fast declaration {declaration}")
        fast_declarations.add(declaration)
        if re.fullmatch(r"sha256:[0-9a-f]{64}", entry["payload_hash"]) is None:
            fail(f"{entry['id']}: invalid or placeholder payload hash")
        expected_hash = computed_payload_hash(entry)
        if entry["payload_hash"] != expected_hash:
            fail(
                f"{entry['id']}: payload hash mismatch; "
                f"catalog={entry['payload_hash']}, computed={expected_hash}"
            )
        validate_reproduction_metadata(entry)
        if entry["fast_axioms"] != [declaration]:
            fail(f"{entry['id']}: fast_axioms must name its one declaration")
        if entry["fast_type"] != entry["contract"]:
            fail(f"{entry['id']}: fast_type must be the exact semantic contract")
        for result_id in entry["result_ids"]:
            if result_id not in result_groups:
                fail(f"{entry['id']}: unknown result ID {result_id}")
            if entry["group_id"] not in result_groups[result_id]:
                fail(
                    f"{entry['id']}: group {entry['group_id']} is not listed by "
                    f"result {result_id}"
                )
        samples = entry["sample_modules"]
        if len(samples) > 2 and not entry.get("sample_rationale"):
            fail(f"{entry['id']}: more than two samples need a rationale")
        if len(samples) > 3:
            fail(f"{entry['id']}: at most three samples are permitted")
        atomic_roots = sorted(set(samples) & set(entry["generated_roots"]))
        if atomic_roots and not entry.get("sample_rationale"):
            fail(
                f"{entry['id']}: sampling a complete atomic replay root requires "
                "a rationale"
            )
        for key in ("verified_module", "fast_module"):
            if not module_source(entry[key]).is_file():
                fail(f"{entry['id']}: missing {key} {entry[key]}")
        if entry["verified_declaration"] not in declarations(entry["verified_module"]):
            fail(
                f"{entry['id']}: verified declaration {entry['verified_declaration']} "
                f"is absent from {entry['verified_module']}"
            )
        for module in samples:
            if not module_source(module).is_file():
                fail(f"{entry['id']}: missing sample module {module}")
    cataloged_providers = {entry["verified_declaration"] for entry in entries}
    declared_providers: set[str] = set()
    certificate_root = ROOT / "CertifiedJL" / "Certificates"
    provider_sources = set(certificate_root.rglob("Provider.lean"))
    provider_sources.update(certificate_root.rglob("Providers/*.lean"))
    for path in sorted(provider_sources):
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        declared_providers.update(declarations(module))
    if declared_providers != cataloged_providers:
        fail(
            "verified-provider catalog mismatch; "
            f"missing={sorted(declared_providers - cataloged_providers)}, "
            f"extra={sorted(cataloged_providers - declared_providers)}"
        )
    pending_groups: set[str] = set()
    for pending in catalog.get("unconverted", []):
        if not pending.get("family_id") or not pending.get("boundaries"):
            fail("every unconverted family needs an id and boundaries")
        pending_groups.add(pending["family_id"])
        if any(key.startswith("fast_") for key in pending):
            fail(f"{pending['family_id']}: unconverted entries cannot allow axioms")
    represented_groups = {entry["group_id"] for entry in entries} | pending_groups
    for result_id, groups in result_groups.items():
        missing_groups = sorted(groups - represented_groups)
        if missing_groups:
            fail(f"{result_id}: certificate groups are not inventoried: {missing_groups}")
    fast_result_names: set[str] = set()
    for fast_result in catalog.get("fast_result", []):
        if set(fast_result) != {"lean", "certificate_ids"}:
            fail(f"malformed fast-result record: {fast_result}")
        if fast_result["lean"] in fast_result_names:
            fail(f"duplicate fast result {fast_result['lean']}")
        fast_result_names.add(fast_result["lean"])
        unknown = sorted(set(fast_result["certificate_ids"]) - ids)
        if unknown:
            fail(f"{fast_result['lean']}: unknown certificate IDs {unknown}")
    result_modules = sorted((ROOT / "CertifiedJLFast" / "Results").rglob("*.lean"))
    declared_fast_results: set[str] = set()
    for path in result_modules:
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        declared_fast_results.update(declarations(module))
    if declared_fast_results != fast_result_names:
        fail(
            "fast-result catalog mismatch; "
            f"missing={sorted(declared_fast_results - fast_result_names)}, "
            f"extra={sorted(fast_result_names - declared_fast_results)}"
        )
    footprint_source = (
        ROOT / "CertifiedJLFast" / "Tests" / "AxiomFootprints.lean"
    ).read_text(encoding="utf-8")
    footprint_records = re.findall(
        r"\(\s*``([A-Za-z0-9_.]+)\s*,\s*#\[(.*?)\]\s*\)",
        footprint_source,
        re.DOTALL,
    )
    actual_footprints = {
        target: set(re.findall(r"``([A-Za-z0-9_.]+)", assumptions))
        for target, assumptions in footprint_records
    }
    assumption_by_id = {
        entry["id"]: entry["fast_declaration"] for entry in entries
    }
    expected_footprints = {
        record["lean"]: {
            assumption_by_id[certificate_id]
            for certificate_id in record["certificate_ids"]
        }
        for record in catalog.get("fast_result", [])
    }
    if actual_footprints != expected_footprints:
        fail(
            "fast-result footprint catalog mismatch; "
            f"expected={expected_footprints}, actual={actual_footprints}"
        )
    print(
        f"certificate catalog verified: {len(entries)} converted boundaries, "
        f"{len(catalog.get('unconverted', []))} explicitly pending families "
        f"({CATALOG.relative_to(CATALOG.parents[2])})"
    )


if __name__ == "__main__":
    main()
