#!/usr/bin/env python3
"""Privacy and runtime-closure checks for the reviewer container image."""

from pathlib import Path
import shlex
import unittest


ROOT = Path(__file__).resolve().parents[1]
DOCKERFILE = ROOT / "artifact" / "Dockerfile"

PUBLIC_VERIFIER_CLOSURE = {
    "scripts/check_replay_families.py",
    "scripts/compute_replay_digest.py",
    "scripts/lean_source.py",
    "scripts/native_shadow_replay.py",
    "scripts/proof_bundle.py",
    "scripts/release_validation.py",
    "scripts/reviewer_workspace.py",
}


def copied_sources() -> list[str]:
    sources: list[str] = []
    for raw_line in DOCKERFILE.read_text().splitlines():
        words = shlex.split(raw_line, comments=True)
        if words and words[0].upper() == "COPY":
            if len(words) != 3:
                raise AssertionError(f"COPY must name one exact source: {raw_line}")
            sources.append(words[1])
    return sources


class ArtifactDockerfileTests(unittest.TestCase):
    def test_image_contains_only_public_verifier_scripts(self) -> None:
        dockerfile = DOCKERFILE.read_text()
        sources = copied_sources()
        script_sources = {source for source in sources if source.startswith("scripts/")}
        self.assertEqual(script_sources, PUBLIC_VERIFIER_CLOSURE)
        self.assertNotIn("scripts/", sources)
        self.assertFalse(any("*" in source for source in sources))
        self.assertNotIn("anonymous_export.py", dockerfile)

        copied_names = {Path(source).name for source in script_sources}
        self.assertFalse(any(name.startswith("test_") for name in copied_names))

    def test_container_entrypoint_is_the_only_non_python_copy(self) -> None:
        sources = copied_sources()
        non_scripts = {source for source in sources if not source.startswith("scripts/")}
        self.assertEqual(non_scripts, {"artifact/entrypoint.sh"})


if __name__ == "__main__":
    unittest.main()
