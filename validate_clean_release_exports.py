#!/usr/bin/env python3
"""Validate migrated clean-room names and docstrings against built Lean modules."""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from collections import defaultdict
from pathlib import Path


IMPORT = re.compile(r"(?m)^\s*(?:public\s+)?import\s+([^\s]+)\s*$")


def build_staleness_errors(release: Path) -> list[str]:
    """Report whether the built artifacts are current with respect to the source.

    Comparing source and `.ilean` modification times is not a sound test. Lake
    keys its build on content hashes recorded in `.trace`, and restoring a
    module from the artifact cache preserves the artifact's original timestamp,
    so an untouched checkout routinely leaves every `.ilean` older than its
    source. Ask Lake instead: it owns those traces, and `--no-build` fails
    exactly when a target is not up to date.
    """

    lake = shutil.which("lake")
    if lake is None:
        return ["cannot verify build currency: `lake` is not on PATH"]
    completed = subprocess.run(
        [lake, "--no-build", "build", "RepresentationTheory"],
        cwd=release,
        capture_output=True,
        text=True,
    )
    if completed.returncode == 0:
        return []
    detail = (completed.stderr or completed.stdout or "").strip().splitlines()
    tail = " / ".join(detail[-3:]) if detail else f"exit status {completed.returncode}"
    return [f"built artifacts are not up to date with the source: {tail}"]


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def module_path(root: Path, module: str, suffix: str) -> Path:
    return root / (module.replace(".", "/") + suffix)


def reference_name(encoded: str) -> str | None:
    try:
        value = json.loads(encoded)
    except json.JSONDecodeError:
        return None
    return value.get("c", {}).get("n") if isinstance(value, dict) else None


def reference_module(encoded: str) -> str | None:
    try:
        value = json.loads(encoded)
    except json.JSONDecodeError:
        return None
    return value.get("c", {}).get("m") if isinstance(value, dict) else None


def normalized(value: str) -> str:
    return " ".join(value.split())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("release", type=Path)
    parser.add_argument("proposals", type=Path)
    args = parser.parse_args()

    release = args.release.resolve()
    proposals_by_module: dict[str, list[dict]] = defaultdict(list)
    for proposal in read_jsonl(args.proposals):
        if proposal.get("new_fqn"):
            proposals_by_module[proposal["new_module"]].append(proposal)

    errors: list[str] = []
    umbrella_path = release / "RepresentationTheory.lean"
    if not umbrella_path.exists():
        umbrella_imports: set[str] = set()
        errors.append("missing public umbrella RepresentationTheory.lean")
    else:
        umbrella_imports = set(IMPORT.findall(umbrella_path.read_text(encoding="utf-8")))
    public_modules = {
        ".".join(path.relative_to(release).with_suffix("").parts)
        for path in (release / "RepresentationTheory").rglob("*.lean")
    }
    for module in sorted(public_modules - umbrella_imports):
        errors.append(f"RepresentationTheory.lean: missing public module import {module}")
    for module in sorted(umbrella_imports - public_modules):
        errors.append(f"RepresentationTheory.lean: import has no public module source {module}")

    errors.extend(build_staleness_errors(release))

    checked_modules = checked_declarations = 0
    for module, proposals in sorted(proposals_by_module.items()):
        source_path = module_path(release, module, ".lean")
        if not source_path.exists():
            continue
        checked_modules += 1
        ilean_path = module_path(release / ".lake/build/lib/lean", module, ".ilean")
        if not ilean_path.exists():
            errors.append(f"{module}: missing built identifier index")
            continue
        source = source_path.read_text(encoding="utf-8")
        ilean = json.loads(ilean_path.read_text(encoding="utf-8"))
        defined = {
            reference_name(encoded)
            for encoded, record in ilean.get("references", {}).items()
            if record.get("definition") is not None
        }
        # Declarations synthesized by command elaborators such as `@[reassoc]`
        # have no source-range definition in the `.ilean` index.  A resolved
        # constant reference whose defining module is this module still proves
        # that the generated declaration exists in the compiled environment.
        locally_generated = {
            reference_name(encoded)
            for encoded in ilean.get("references", {})
            if reference_module(encoded) == module
        }
        available = defined | locally_generated
        docstrings = {
            normalized(match.group(1))
            for match in re.finditer(r"/--(.*?)-/", source, flags=re.DOTALL)
        }
        for proposal in proposals:
            checked_declarations += 1
            new_fqn = proposal["new_fqn"]
            if new_fqn not in available:
                errors.append(f"{module}: missing clean-room declaration {new_fqn}")
            expected_doc = normalized(proposal["cleanroom_docstring"])
            if expected_doc not in docstrings:
                errors.append(
                    f"{module}: missing exact clean-room docstring for {new_fqn}: "
                    f"{expected_doc!r}"
                )

    result = {
        "modules": checked_modules,
        "declarations": checked_declarations,
        "public_modules": len(public_modules),
        "umbrella_imports": len(umbrella_imports),
        "errors": len(errors),
    }
    print(json.dumps(result, sort_keys=True))
    if errors:
        raise SystemExit("\n".join(errors[:100]))


if __name__ == "__main__":
    main()
