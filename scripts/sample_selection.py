#!/usr/bin/env python3
"""Select bounded certificate samples affected by a complete Git diff."""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from io import BytesIO
from pathlib import Path
import re
import subprocess
import tarfile
import tomllib

from certificate_catalog import CATALOG, ROOT
from lean_source import imports_in_source, qualified_declarations


REPLAY_FAMILIES = Path("evidence/certificates/replay-families.toml")
FAIL_CLOSED_PATHS = {
    CATALOG.relative_to(ROOT).as_posix(),
    REPLAY_FAMILIES.as_posix(),
    ".github/workflows/ci.yml",
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
}
DECLARATION_FIELDS = ("checker",)


@dataclass(frozen=True)
class Snapshot:
    entries: tuple[dict, ...]
    graph: dict[str, tuple[str, ...]]
    module_paths: dict[str, str]
    declaration_owners: dict[str, str]
    replay_roots: dict[str, tuple[str, ...]]


@dataclass(frozen=True)
class Selection:
    modules: tuple[str, ...]
    certificate_ids: tuple[str, ...]
    reason: str
    fail_closed: bool = False


def _module(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def _closure(graph: dict[str, tuple[str, ...]], roots: list[str]) -> set[str]:
    reached: set[str] = set()
    pending = deque(roots)
    while pending:
        module = pending.popleft()
        if module in reached:
            continue
        reached.add(module)
        pending.extend(graph.get(module, ()))
    return reached


def _replay_roots(document: dict) -> dict[str, tuple[str, ...]]:
    answer: dict[str, tuple[str, ...]] = {}
    for family in document.get("family", []):
        roots = tuple(family["replay_roots"])
        for certificate_id in family["certificate_ids"]:
            if certificate_id in answer:
                raise ValueError(f"duplicate replay-family owner: {certificate_id}")
            answer[certificate_id] = roots
    return answer


def snapshot_from_sources(
    entries: list[dict], replay_document: dict, sources: dict[str, str]
) -> Snapshot:
    graph: dict[str, tuple[str, ...]] = {}
    module_paths: dict[str, str] = {}
    for path, source in sources.items():
        if not path.endswith(".lean"):
            continue
        module = _module(path)
        module_paths[module] = path
        graph[module] = imports_in_source(source, path)

    wanted = {
        entry[field]
        for entry in entries
        for field in DECLARATION_FIELDS
        if isinstance(entry.get(field), str)
    }
    wanted_leaves = {name.rsplit(".", 1)[-1] for name in wanted}
    declaration_owners: dict[str, str] = {}
    patterns = {
        leaf: re.compile(
            rf"(?m)^\s*(?:(?:private|protected|noncomputable|nonrec|local|public|unsafe)\s+)*"
            rf"(?:def|theorem|lemma|structure|opaque|abbrev)\s+{re.escape(leaf)}\b"
        )
        for leaf in wanted_leaves
    }
    for path, source in sources.items():
        if not path.endswith(".lean") or not any(p.search(source) for p in patterns.values()):
            continue
        declarations = qualified_declarations(source, path)
        for name in declarations & wanted:
            previous = declaration_owners.setdefault(name, path)
            if previous != path:
                raise ValueError(f"ambiguous declaration owner for {name}")
    missing = wanted - declaration_owners.keys()
    if missing:
        raise ValueError(f"unresolved declaration owners: {sorted(missing)}")
    return Snapshot(
        tuple(entries), graph, module_paths, declaration_owners,
        _replay_roots(replay_document),
    )


def _sources_on_disk(root: Path) -> dict[str, str]:
    answer: dict[str, str] = {}
    for path in root.rglob("*.lean"):
        if ".lake" not in path.parts:
            answer[path.relative_to(root).as_posix()] = path.read_text(encoding="utf-8")
    return answer


def current_snapshot(root: Path = ROOT) -> Snapshot:
    with (root / CATALOG.relative_to(ROOT)).open("rb") as stream:
        entries = tomllib.load(stream).get("certificate", [])
    with (root / REPLAY_FAMILIES).open("rb") as stream:
        replay_document = tomllib.load(stream)
    return snapshot_from_sources(entries, replay_document, _sources_on_disk(root))


def snapshot_at_revision(revision: str, root: Path = ROOT) -> Snapshot:
    archive = subprocess.run(
        ["git", "archive", "--format=tar", revision], cwd=root,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
    ).stdout
    sources: dict[str, str] = {}
    catalog_source: bytes | None = None
    replay_source: bytes | None = None
    with tarfile.open(fileobj=BytesIO(archive), mode="r:") as stream:
        for member in stream:
            if not member.isfile():
                continue
            if member.name == CATALOG.relative_to(ROOT).as_posix():
                catalog_source = stream.extractfile(member).read()
            elif member.name == REPLAY_FAMILIES.as_posix():
                replay_source = stream.extractfile(member).read()
            elif member.name.endswith(".lean"):
                sources[member.name] = stream.extractfile(member).read().decode("utf-8")
    if catalog_source is None or replay_source is None:
        raise ValueError("base revision lacks certificate selection metadata")
    return snapshot_from_sources(
        tomllib.loads(catalog_source.decode("utf-8")).get("certificate", []),
        tomllib.loads(replay_source.decode("utf-8")),
        sources,
    )


def all_sample_modules(entries: tuple[dict, ...] | list[dict]) -> tuple[str, ...]:
    return tuple(dict.fromkeys(
        module for entry in entries for module in entry.get("sample_modules", [])
    ))


def validate_sample_boundaries(snapshot: Snapshot) -> None:
    forbidden: set[str] = set()
    for entry in snapshot.entries:
        forbidden.add(entry["verified_module"])
        forbidden.update(entry.get("generated_roots", []))
    failures: list[str] = []
    for entry in snapshot.entries:
        owned = set(entry.get("generated_roots", []))
        for sample in entry.get("sample_modules", []):
            for module in _closure(snapshot.graph, [sample]):
                for forbidden_root in forbidden:
                    if module != forbidden_root and not module.startswith(forbidden_root + "."):
                        continue
                    owns_leaf = any(
                        (sample == owner or sample.startswith(owner + "."))
                        for owner in owned if owner == forbidden_root
                    )
                    if not owns_leaf:
                        failures.append(f"{entry['id']}: {sample} -> {module}")
    if failures:
        raise ValueError(
            "certificate sample closure reaches another replay/provider root: "
            + "; ".join(sorted(set(failures)))
        )


def _entry_paths(snapshot: Snapshot, entry: dict) -> set[str]:
    modules = set(entry.get("data_modules", []))
    modules.add(entry["verified_module"])
    modules.update(_closure(snapshot.graph, list(entry.get("sample_modules", []))))
    modules.update(_closure(
        snapshot.graph, list(snapshot.replay_roots.get(entry["id"], ()))
    ))
    paths = {snapshot.module_paths[module] for module in modules if module in snapshot.module_paths}
    for field in DECLARATION_FIELDS:
        declaration = entry.get(field)
        if isinstance(declaration, str):
            paths.add(snapshot.declaration_owners[declaration])
    generator = entry.get("generator")
    if isinstance(generator, str) and generator.startswith("scripts/"):
        paths.add(generator)
    return paths


def select_from_paths(
    current: Snapshot,
    base: Snapshot | None,
    changed_paths: set[str],
    *,
    uncertainty: str | None = None,
) -> Selection:
    all_modules = all_sample_modules(current.entries)
    all_ids = tuple(entry["id"] for entry in current.entries if entry.get("sample_modules"))
    if uncertainty is not None or base is None:
        return Selection(all_modules, all_ids, uncertainty or "base unavailable", True)
    if any(path.startswith("scripts/") or path in FAIL_CLOSED_PATHS for path in changed_paths):
        return Selection(all_modules, all_ids, "validation, catalog, or toolchain input changed", True)

    current_by_id = {entry["id"]: entry for entry in current.entries}
    base_by_id = {entry["id"]: entry for entry in base.entries}
    selected_ids: list[str] = []
    selected_modules: list[str] = []
    for certificate_id, entry in current_by_id.items():
        samples = entry.get("sample_modules", [])
        if not samples:
            continue
        paths = _entry_paths(current, entry)
        old_entry = base_by_id.get(certificate_id)
        if old_entry is not None:
            paths.update(_entry_paths(base, old_entry))
        if paths.isdisjoint(changed_paths):
            continue
        selected_ids.append(certificate_id)
        selected_modules.extend(samples)
    return Selection(
        tuple(dict.fromkeys(selected_modules)), tuple(selected_ids),
        "affected certificate ownership or import closure" if selected_ids else "no sample dependency changed",
    )


def changed_paths_since(base: str, root: Path = ROOT) -> tuple[str, set[str]]:
    resolved = subprocess.run(
        ["git", "rev-parse", "--verify", f"{base}^{{commit}}"], cwd=root,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if resolved.returncode != 0:
        raise ValueError(f"unknown base revision: {base}")
    merge_base = subprocess.run(
        ["git", "merge-base", resolved.stdout.strip(), "HEAD"], cwd=root,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if merge_base.returncode != 0 or not merge_base.stdout.strip():
        raise ValueError(f"no merge base for revision: {base}")
    revision = merge_base.stdout.strip()
    diff = subprocess.run(
        ["git", "diff", "--name-status", "-z", "-M", revision, "HEAD"],
        cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
    ).stdout.split(b"\0")
    paths: set[str] = set()
    index = 0
    while index < len(diff) and diff[index]:
        status = diff[index].decode("ascii")
        index += 1
        count = 2 if status.startswith(("R", "C")) else 1
        for _ in range(count):
            if index >= len(diff) or not diff[index]:
                raise ValueError("malformed Git name-status output")
            paths.add(diff[index].decode("utf-8", "surrogateescape"))
            index += 1
    return revision, paths


def repository_is_dirty(root: Path = ROOT) -> bool:
    status = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
        cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
    )
    return bool(status.stdout)


def select_for_repository(
    base: str | None, root: Path = ROOT, current: Snapshot | None = None
) -> Selection:
    current = current or current_snapshot(root)
    validate_sample_boundaries(current)
    try:
        if repository_is_dirty(root):
            return select_from_paths(
                current, None, set(), uncertainty="working tree has uncommitted or untracked changes"
            )
    except (OSError, subprocess.SubprocessError) as error:
        return select_from_paths(current, None, set(), uncertainty=str(error))
    if not base:
        return select_from_paths(current, None, set(), uncertainty="no diff base supplied")
    try:
        revision, paths = changed_paths_since(base, root)
        if any(path.startswith("scripts/") or path in FAIL_CLOSED_PATHS for path in paths):
            return select_from_paths(current, current, paths)
        old = snapshot_at_revision(revision, root)
        return select_from_paths(current, old, paths)
    except (OSError, ValueError, subprocess.SubprocessError, tomllib.TOMLDecodeError) as error:
        return select_from_paths(current, None, set(), uncertainty=str(error))
