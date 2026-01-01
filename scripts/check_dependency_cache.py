#!/usr/bin/env python3
"""Verify that every live Lake package is exact, complete, and clean."""

from __future__ import annotations

from native_shadow_replay import NativeReplayError, ROOT, verified_dependencies


def main() -> None:
    try:
        dependencies = verified_dependencies(ROOT)
    except NativeReplayError as error:
        raise SystemExit(f"dependency cache error: {error}") from error
    print(f"exact dependency cache verified: {len(dependencies)} clean Git checkouts")


if __name__ == "__main__":
    main()
