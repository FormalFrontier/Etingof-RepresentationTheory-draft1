#!/usr/bin/env python3
"""Validate rendered formalization panels and reject leaked Lean commands."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("alignment_export", type=Path)
    parser.add_argument("html_root", type=Path)
    args = parser.parse_args()

    entries = json.loads(args.alignment_export.read_text(encoding="utf-8"))
    html_paths = sorted(args.html_root.rglob("*.html"))
    rendered = "\n".join(path.read_text(encoding="utf-8") for path in html_paths)
    errors: list[str] = []

    leaked_close = "end IntroductionToRepresentationTheoryVerso."
    if leaked_close in rendered:
        errors.append("rendered HTML contains a Lean namespace-closing command")

    for entry in entries:
        citation = f"book-ref={entry['reference']}; role={entry['role']}"
        if citation not in rendered:
            errors.append(f"missing rendered citation: {citation}")
        if entry["declaration"] not in rendered:
            errors.append(f"missing rendered declaration: {entry['declaration']}")

    summary = {
        "alignment_entries": len(entries),
        "errors": len(errors),
        "html_files": len(html_paths),
    }
    print(json.dumps(summary, sort_keys=True))
    if errors:
        for error in errors:
            print(error)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
