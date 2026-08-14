#!/usr/bin/env python3
"""Fail on book prose or source-process identifiers in the clean Lean release."""

from __future__ import annotations

import argparse
import json
import re
import unicodedata
from pathlib import Path


BANNED_IDENTIFIER = re.compile(
    r"(?i)(etingof|chapter[_-]?\d|(?:theorem|corollary|proposition|lemma|problem|exercise)[_-]?\d)"
)
BANNED_TEXT = (
    "EtingofRepresentationTheory",
    "Etingof.",
    "Faithfulness note",
    "Mathlib correspondence",
)
SOURCE_REF = re.compile(
    r'source_ref\s*"(?:Frontmatter|Backmatter|Chapter\d+)/[A-Za-z][A-Za-z0-9_.-]*'
    r'(?:/Derived\d+)?"\s*\(role\s*:=\s*(?:primary|supporting)\)'
)


def words(value: str) -> list[str]:
    value = unicodedata.normalize("NFKC", value).casefold()
    return re.findall(r"[^\W_]+", value, flags=re.UNICODE)


def ngrams(value: str, size: int) -> set[tuple[str, ...]]:
    tokens = words(value)
    return {tuple(tokens[i : i + size]) for i in range(len(tokens) - size + 1)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("release", type=Path)
    parser.add_argument("book_blobs", type=Path)
    args = parser.parse_args()
    release = args.release.resolve()

    book_ngrams: set[tuple[str, ...]] = set()
    for path in args.book_blobs.rglob("*.md"):
        book_ngrams |= ngrams(path.read_text(encoding="utf-8"), 8)

    errors: list[str] = []
    lean_files = sorted(
        path
        for path in release.rglob("*.lean")
        if ".lake" not in path.relative_to(release).parts
    )
    source_ref_count = 0
    for path in lean_files:
        relative = str(path.relative_to(release))
        if BANNED_IDENTIFIER.search(relative):
            errors.append(f"{relative}: source-derived path marker")
        text = path.read_text(encoding="utf-8")
        identifier_text = text.replace(
            "Etingof et al., Introduction to Representation Theory", ""
        )
        identifier_text = SOURCE_REF.sub("source_ref", identifier_text)
        for marker in BANNED_TEXT:
            if marker in text:
                errors.append(f"{relative}: banned text marker {marker!r}")
        for match in re.finditer(r"\b[A-Za-z_][A-Za-z0-9_'.]*\b", identifier_text):
            if BANNED_IDENTIFIER.search(match.group()) and "source_ref" not in match.group():
                errors.append(f"{relative}: source-derived identifier {match.group()!r}")
        source_ref_count += len(SOURCE_REF.findall(text))
        overlap = ngrams(text, 8) & book_ngrams
        if overlap:
            errors.append(f"{relative}: repeats book prose: {' '.join(sorted(overlap)[0])!r}")

    result = {
        "lean_files": len(lean_files),
        "source_ref_attributes": source_ref_count,
        "errors": len(errors),
    }
    print(json.dumps(result, sort_keys=True))
    if errors:
        raise SystemExit("\n".join(errors[:100]))


if __name__ == "__main__":
    main()
