#!/usr/bin/env python3
# Copyright (c) 2026 American Mathematical Society. All rights reserved.
"""Update only the pinned clean-formalization revision in lakefile.toml."""

from __future__ import annotations

import re
import sys
from pathlib import Path


SHA = re.compile(r"[0-9a-f]{40}")
STANZA = re.compile(
    r'(\[\[require\]\]\nname = "RepresentationTheoryFormalization"\n'
    r'git = "[^"\n]+"\n'
    r'rev = ")[^"\n]+("\n)'
)


def main() -> None:
    if len(sys.argv) != 2 or SHA.fullmatch(sys.argv[1]) is None:
        raise SystemExit("usage: update_formalization_dependency.py <40-hex-sha>")
    path = Path(__file__).resolve().parent.parent / "lakefile.toml"
    source = path.read_text(encoding="utf-8")
    updated, count = STANZA.subn(rf"\g<1>{sys.argv[1]}\g<2>", source)
    if count != 1:
        raise SystemExit("lakefile.toml does not contain exactly one canonical formalization stanza")
    path.write_text(updated, encoding="utf-8")


if __name__ == "__main__":
    main()
