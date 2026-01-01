#!/usr/bin/env python3
"""Shared accessors for the machine-readable certificate catalog."""

from __future__ import annotations

import tomllib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CATALOG = ROOT / "evidence" / "certificates" / "public-results.toml"


def load_catalog() -> dict:
    with CATALOG.open("rb") as stream:
        return tomllib.load(stream)


def certificates() -> list[dict]:
    return load_catalog().get("certificate", [])


def module_source(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def normalize_type(value: str) -> str:
    return " ".join(value.split())
