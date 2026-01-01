#!/usr/bin/env python3
"""Generate the acyclic import topology for lower-tail certificate shards.

The arithmetic payloads remain in their existing generated Lean files.  This
script owns only their import edges and the import-only aggregate modules.
"""

from argparse import ArgumentParser
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
DOMINANT = ROOT / "CertifiedJL/Certificates/Families/L2Lower/Shared/Dominant"
DOMINANT_DATA = DOMINANT / "Data"
DOMINANT_REPLAY = DOMINANT / "Replay"
NEAR = ROOT / "CertifiedJL/Certificates/Families/L2Lower/Rows256Bits128/Near"
NEAR_REPLAY = NEAR / "Replay"
NEAR_SOUNDNESS = NEAR / "Soundness"


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def unique_named(root: Path, name: str) -> Path:
    matches = list(root.rglob(name))
    if len(matches) != 1:
        raise ValueError(f"expected one {name} below {root}, found {len(matches)}")
    return matches[0]

DIRECT_TARGETS = (
    "ConstantDirectCover192Bits128",
    "ConstantDirectCover256Bits192",
    "ConstantDirectCover384Bits192",
    "ConstantDirectCover512Bits192",
    "ConstantDirectCover512Bits256",
)

DIRECT_TARGET_DATA_IMPORTS = {
    "ConstantDirectCover192Bits128": ("ConstantDirectCover128Shard23",),
    "ConstantDirectCover256Bits192":
        ("ConstantDirectCover256And384Bits192Caps",),
    "ConstantDirectCover384Bits192":
        ("ConstantDirectCover256And384Bits192Caps",),
    "ConstantDirectCover512Bits192": ("ConstantNumericData",),
    "ConstantDirectCover512Bits256":
        ("ConstantDirectCover128Shard02", "ConstantDirectCover128Shard03"),
}


def replace_imports(source: str, imports: list[str]) -> str:
    lines = source.splitlines()
    first = next(i for i, line in enumerate(lines) if line.startswith("import "))
    last = first
    while last + 1 < len(lines) and lines[last + 1].startswith("import "):
        last += 1
    lines[first:last + 1] = [f"import {module}" for module in imports]
    return "\n".join(lines) + "\n"


def dominant_expected() -> dict[Path, str]:
    expected: dict[Path, str] = {}
    for target in DIRECT_TARGETS:
        data = DOMINANT_DATA / target / "Data.lean"
        target_imports = []
        for module in DIRECT_TARGET_DATA_IMPORTS[target]:
            if module.startswith("ConstantDirectCover128Shard"):
                tag = module.removeprefix("ConstantDirectCover128Shard")
                owner = DOMINANT_DATA / "ConstantDirectCover128" / f"Shard{tag}.lean"
            else:
                owner = unique_named(DOMINANT, f"{module}.lean")
            target_imports.append(module_name(owner))
        expected[data] = replace_imports(data.read_text(), target_imports)
        paths = {DOMINANT_REPLAY / target / f"Shard{index:02d}.lean" for index in range(47)}
        actual = set((DOMINANT_REPLAY / target).glob("Shard*.lean"))
        if actual != paths:
            raise SystemExit(f"{target}: expected exactly shards 00 through 46")
        for path in sorted(paths):
            tag = path.stem.removeprefix("Shard")
            reusable_data = (
                DOMINANT_DATA / "ConstantDirectCover128" / f"Shard{tag}.lean"
            )
            base_shard = (
                reusable_data
                if reusable_data.is_file() and (
                    target == "ConstantDirectCover512Bits256" or
                    (target == "ConstantDirectCover192Bits128" and tag == "23") or
                    (target in {"ConstantDirectCover256Bits192",
                                "ConstantDirectCover384Bits192"} and
                     tag in {"02", "03"}))
                else DOMINANT_REPLAY / f"ConstantDirectCover128Shard{tag}.lean"
            )
            expected[path] = replace_imports(path.read_text(), [
                module_name(data),
                module_name(base_shard),
            ] + ([module_name(DOMINANT_REPLAY /
                    "ConstantDirectCover256And384Bits192RowCaps" /
                    f"Shard{tag}.lean")]
                 if target in {"ConstantDirectCover256Bits192",
                               "ConstantDirectCover384Bits192"} and
                    tag in {"02", "03"}
                 else []))

    for family, count in (("CappedFourierCover128", 5),
                          ("SingletonFourierCover128", 2)):
        for shard in range(count):
            path = DOMINANT_REPLAY / f"{family}Shard{shard:02d}.lean"
            expected[path] = replace_imports(
                path.read_text(), [module_name(DOMINANT_REPLAY / f"{family}.lean")])
        aggregate = DOMINANT_REPLAY / f"{family}Verified.lean"
        numeric = ("CappedFourierNumeric128" if count == 5
                   else "SingletonFourierNumeric128")
        data = DOMINANT_REPLAY / f"{family}.lean"
        expected[data] = replace_imports(data.read_text(), [
            module_name(unique_named(DOMINANT, f"{numeric}Data.lean"))])
        expected[aggregate] = f"import {module_name(unique_named(DOMINANT, f'{numeric}.lean'))}\n" + "\n".join(
            f"import {module_name(DOMINANT_REPLAY / f'{family}Shard{shard:02d}.lean')}"
            for shard in range(count)
        ) + f"\n\n/-! # Aggregate of the independent {('capped-Fourier' if count == 5 else 'singleton-Fourier')} 128-bit cover shards -/\n"

    selector_imports = {
        "CappedFourierCover128Selector.lean":
            module_name(DOMINANT_REPLAY / "CappedFourierCover128Verified.lean"),
        "SingletonFourierCover128Selector.lean":
            module_name(DOMINANT_REPLAY / "SingletonFourierCover128Verified.lean"),
    }
    for name, module in selector_imports.items():
        path = DOMINANT_REPLAY / name
        expected[path] = replace_imports(path.read_text(), [module])
    return expected


def near_expected() -> dict[Path, str]:
    files = sorted(NEAR_REPLAY.glob("ThresholdNearCoarseShard*128.lean"))
    theorem_file: dict[str, Path] = {}
    for path in files:
        match = re.search(r"theorem\s+(shard[A-Za-z0-9_]+_check)\b",
                          path.read_text())
        if match is None:
            raise ValueError(f"no shard theorem in {path}")
        theorem_file[match.group(1)] = path

    expected: dict[Path, str] = {}
    for own, path in theorem_file.items():
        dependencies: list[str] = []
        for name in re.findall(r"\b(shard[A-Za-z0-9_]+_check)\b",
                               path.read_text()):
            if name != own and name in theorem_file and name not in dependencies:
                dependencies.append(name)
        modules = ([theorem_file[name].stem for name in dependencies]
                   or ["ThresholdNearCoarsePartition128"])
        expected[path] = replace_imports(
            path.read_text(), [module_name(unique_named(NEAR, f"{module}.lean"))
                               for module in modules])

    top_modules = [f"ThresholdNearCoarseShard{index:04b}_128"
                   for index in range(16)]
    aggregate = NEAR_SOUNDNESS / "ThresholdNearCoarseAggregate128.lean"
    expected[aggregate] = "\n".join(
        f"import {module_name(NEAR_REPLAY / f'{module}.lean')}" for module in top_modules
    ) + "\n\n/-! # Aggregate of the independent coarse near-band replay shards -/\n"

    verified = NEAR_SOUNDNESS / "ThresholdNearCoarseVerified128.lean"
    expected[verified] = replace_imports(
        verified.read_text(), [
            module_name(aggregate),
            module_name(NEAR_SOUNDNESS / "ThresholdNearCoarseCover128.lean"),
        ])
    return expected


def main() -> None:
    parser = ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()

    expected = {**dominant_expected(), **near_expected()}
    if args.write:
        for path, source in expected.items():
            path.write_text(source)
        print(f"wrote {len(expected)} shard-topology files")
        return

    mismatches = [path for path, source in expected.items()
                  if not path.exists() or path.read_text() != source]
    if mismatches:
        print("shard topology differs:",
              *(path.relative_to(ROOT) for path in mismatches),
              sep="\n", file=sys.stderr)
        raise SystemExit(1)
    print(f"checked {len(expected)} shard-topology files")


if __name__ == "__main__":
    main()
