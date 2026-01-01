#!/usr/bin/env python3
"""Refresh paper-snapshot.toml from a clean committed paper subtree."""

from __future__ import annotations

import hashlib
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SNAPSHOT = ROOT / "evidence" / "paper-snapshot.toml"
TRACKED_CATEGORIES = {"source", "context", "artifact"}


def git(*arguments: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(ROOT), *arguments])


def main() -> None:
    dirty = git("status", "--porcelain", "--", "paper").decode().strip()
    if dirty:
        raise SystemExit(
            "paper/ must be committed before refreshing the snapshot:\n" + dirty
        )

    head = git("rev-parse", "HEAD").decode().strip()
    date = git("show", "-s", "--format=%cs", head).decode().strip()
    lines = SNAPSHOT.read_text(encoding="utf-8").splitlines(keepends=True)
    output: list[str] = []
    category: str | None = None
    current_path: str | None = None

    for line in lines:
        section = re.fullmatch(r"\[\[([a-z_]+)\]\]\n?", line)
        if section is not None:
            category = section.group(1)
            current_path = None
        if line.startswith("snapshot_date = "):
            line = f'snapshot_date = "{date}"\n'
        elif line.startswith("paper_git_head = "):
            line = f'paper_git_head = "{head}"\n'
        elif line.startswith("paper_git_prefix = "):
            line = 'paper_git_prefix = "paper"\n'
        elif category in TRACKED_CATEGORIES and line.startswith("path = "):
            match = re.fullmatch(r'path = "([^"]+)"\n?', line)
            if match is None:
                raise SystemExit(f"invalid snapshot path line: {line.rstrip()}")
            current_path = match.group(1)
        elif (
            category in TRACKED_CATEGORIES
            and current_path is not None
            and line.startswith("sha256 = ")
        ):
            data = git("show", f"{head}:paper/{current_path}")
            line = f'sha256 = "{hashlib.sha256(data).hexdigest()}"\n'
            current_path = None
        output.append(line)

    SNAPSHOT.write_text("".join(output), encoding="utf-8")
    print(f"refreshed {SNAPSHOT.relative_to(ROOT)} from {head}")


if __name__ == "__main__":
    main()
