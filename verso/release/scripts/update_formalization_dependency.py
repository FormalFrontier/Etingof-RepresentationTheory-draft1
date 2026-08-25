#!/usr/bin/env python3
# Copyright (c) 2026 American Mathematical Society. All rights reserved.
"""Update only the pinned clean-formalization revision in lakefile.toml."""

from __future__ import annotations

import re
import sys
import tomllib
from pathlib import Path


SHA = re.compile(r"[0-9a-f]{40}")
VERSO_URL = "https://github.com/leanprover/verso.git"
VERSO_REV = "e09d21a5f7f66c9fc985b73197708298569bf583"
FORMALIZATION_URL = (
    "https://github.com/mathlib-initiative/EtingofRepresentationTheory.git"
)


def verso_stanza() -> str:
    return (
        "[[require]]\n"
        'name = "verso"\n'
        f'git = "{VERSO_URL}"\n'
        f'rev = "{VERSO_REV}"\n'
    )


def formalization_stanza(revision: str) -> str:
    return (
        "[[require]]\n"
        'name = "RepresentationTheoryFormalization"\n'
        f'git = "{FORMALIZATION_URL}"\n'
        f'rev = "{revision}"\n'
    )


def validate_layout(source: str) -> str:
    try:
        config = tomllib.loads(source)
    except tomllib.TOMLDecodeError as error:
        raise SystemExit(f"lakefile.toml is not valid TOML: {error}") from error
    requires = config.get("require")
    if not isinstance(requires, list) or len(requires) != 2:
        raise SystemExit("lakefile.toml must contain exactly two Git dependencies")
    formal_revision = requires[1].get("rev") if isinstance(requires[1], dict) else None
    if not isinstance(formal_revision, str) or SHA.fullmatch(formal_revision) is None:
        raise SystemExit("current formalization revision is not exact lowercase 40-hex")
    expected = [
        {"name": "verso", "git": VERSO_URL, "rev": VERSO_REV},
        {
            "name": "RepresentationTheoryFormalization",
            "git": FORMALIZATION_URL,
            "rev": formal_revision,
        },
    ]
    if requires != expected:
        raise SystemExit(
            "lakefile.toml dependencies must be the exact canonical Verso and "
            "formalization Git stanzas"
        )
    if source.count(verso_stanza()) != 1 or source.count(
        formalization_stanza(formal_revision)
    ) != 1:
        raise SystemExit("lakefile.toml dependency stanza text is not canonical")
    return formal_revision


def main() -> None:
    if len(sys.argv) != 2 or SHA.fullmatch(sys.argv[1]) is None:
        raise SystemExit("usage: update_formalization_dependency.py <40-hex-sha>")
    path = Path(__file__).resolve().parent.parent / "lakefile.toml"
    source = path.read_text(encoding="utf-8")
    current_revision = validate_layout(source)
    updated = source.replace(
        formalization_stanza(current_revision),
        formalization_stanza(sys.argv[1]),
        1,
    )
    if validate_layout(updated) != sys.argv[1]:
        raise SystemExit("updated lakefile did not retain the canonical dependency layout")
    path.write_text(updated, encoding="utf-8")


if __name__ == "__main__":
    main()
