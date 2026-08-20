#!/usr/bin/env python3
"""Derive the stable dependency identity for the Mathlib native-object cache."""

# Copyright (c) 2026 American Mathematical Society. All rights reserved.

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path


CACHE_SCHEMA = "mathlib-ir-v1"
MATHLIB_URL = "https://github.com/leanprover-community/mathlib4"
SAFE_RUNNER_VALUE = re.compile(r"[A-Za-z0-9_.-]{1,64}")
CANONICAL_REVISION = re.compile(r"[0-9a-f]{40}")
CANONICAL_TOOLCHAIN = re.compile(rb"[A-Za-z0-9._/-]+:[A-Za-z0-9._+-]+\n")


def cache_key_base(root: Path, runner_os: str, runner_arch: str) -> str:
    """Return a validated cache base that changes only with native ABI inputs."""
    for name, value in (("runner OS", runner_os), ("runner architecture", runner_arch)):
        if SAFE_RUNNER_VALUE.fullmatch(value) is None:
            raise ValueError(f"{name} is not a canonical cache-key component")

    toolchain = (root / "lean-toolchain").read_bytes()
    if CANONICAL_TOOLCHAIN.fullmatch(toolchain) is None:
        raise ValueError(
            "lean-toolchain must contain exactly one canonical newline-terminated value"
        )
    toolchain_hash = hashlib.sha256(toolchain).hexdigest()

    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = manifest.get("packages")
    if not isinstance(packages, list) or not all(
        isinstance(package, dict) for package in packages
    ):
        raise ValueError("lake-manifest.json has no package list")
    mathlib = [package for package in packages if package.get("name") == "mathlib"]
    if len(mathlib) != 1:
        raise ValueError("lake-manifest.json must contain exactly one Mathlib package")
    package = mathlib[0]
    revision = package.get("rev")
    if (
        package.get("type") != "git"
        or package.get("url") != MATHLIB_URL
        or not isinstance(revision, str)
        or CANONICAL_REVISION.fullmatch(revision) is None
    ):
        raise ValueError(
            "lake-manifest.json does not contain canonical pinned Mathlib Git metadata"
        )

    return f"{CACHE_SCHEMA}-{runner_os}-{runner_arch}-{toolchain_hash}-{revision}"


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: mathlib_ir_cache_key.py <runner-os> <runner-arch>")
    root = Path(__file__).resolve().parent.parent
    try:
        print(cache_key_base(root, sys.argv[1], sys.argv[2]))
    except (OSError, ValueError, json.JSONDecodeError) as error:
        raise SystemExit(f"cannot derive Mathlib native cache key: {error}") from error


if __name__ == "__main__":
    main()
