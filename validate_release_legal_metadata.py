#!/usr/bin/env python3
"""Validate the fixed legal and ownership contract of both release trees."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


PUBLIC_HEADER = "Copyright (c) 2026 mathlib-initiative. All rights reserved."
PRIVATE_HEADER = (
    "Copyright (c) 2026 American Mathematical Society. All rights reserved."
)


def require_file(root: Path, relative: str, errors: list[str]) -> Path:
    path = root / relative
    if not path.is_file():
        errors.append(f"{root}: missing {relative}")
    return path


def require_text(path: Path, needles: tuple[str, ...], errors: list[str]) -> None:
    if not path.is_file():
        return
    text = path.read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            errors.append(f"{path}: missing required text {needle!r}")


def validate_public(root: Path, errors: list[str]) -> None:
    if (root / "LICENSE").exists():
        errors.append(f"{root}: LICENSE must not exist; the required filename is LICENCE")
    licence = require_file(root, "LICENCE", errors)
    readme = require_file(root, "README.md", errors)
    notice = require_file(root, "NOTICE", errors)
    require_text(
        licence,
        ("Apache License", "Version 2.0, January 2004"),
        errors,
    )
    require_text(
        readme,
        (
            "Introduction to Representation Theory",
            "https://bookstore.ams.org/stml-59/",
            "does not quote or reproduce the book's prose",
            "do not reproduce the book's structure",
            "not a derivative work",
            "access-controlled",
            "not publicly available",
        ),
        errors,
    )
    require_text(notice, ("Copyright 2026 mathlib-initiative", "Apache License"), errors)
    public_ci = require_file(root, ".github/workflows/ci.yml", errors)
    notify = require_file(root, ".github/workflows/notify-verso.yml", errors)
    require_text(public_ci, ("leanprover/lean-action@v1", "test -f LICENCE"), errors)
    require_text(
        notify,
        (
            "workflow_run:",
            "VERSO_REPO_DISPATCH_TOKEN",
            "mathlib-initiative/EtingofRepresentationTheory-verso/dispatches",
            "formalization-updated",
        ),
        errors,
    )
    for path in root.rglob("*.lean"):
        if any(part in {".lake", "_out"} for part in path.relative_to(root).parts):
            continue
        text = path.read_text(encoding="utf-8")
        if PUBLIC_HEADER not in text[:300]:
            errors.append(f"{path}: missing mathlib-initiative copyright header")
        if "Copyright (c) 2026 Kim Morrison" in text:
            errors.append(f"{path}: retained superseded personal copyright header")
        if "file LICENSE" in text[:400]:
            errors.append(f"{path}: header names LICENSE instead of LICENCE")


def validate_private(root: Path, errors: list[str]) -> None:
    if (root / "LICENSE").exists():
        errors.append(f"{root}: LICENSE must not exist; the required filename is LICENCE")
    licence = require_file(root, "LICENCE", errors)
    readme = require_file(root, "README.md", errors)
    require_text(
        licence,
        (
            "Copyright © 2026 American Mathematical Society. All rights reserved.",
            "No permission is granted",
            "mathlib-initiative disclaims any copyright, ownership, or other",
        ),
        errors,
    )
    require_text(
        readme,
        (
            "Copyright © 2026 American Mathematical Society. All rights reserved.",
            "mathlib-initiative hosts this private repository on behalf of the American",
            "mathlib-initiative disclaims any copyright, ownership, or other",
            "mathlib-initiative/EtingofRepresentationTheory",
            "does not deploy GitHub Pages",
        ),
        errors,
    )
    source_markdown = root / "source-markdown"
    markdown_files = list(source_markdown.glob("*.md")) if source_markdown.is_dir() else []
    if len(markdown_files) != 235:
        errors.append(
            f"{root}: expected the complete 235-file Markdown corpus, found {len(markdown_files)}"
        )
    require_file(root, "source-markdown/chapter_map.json", errors)
    metadata_items = require_file(root, "metadata/items.json", errors)
    require_file(root, "metadata/book.json", errors)
    require_file(root, "metadata/overlays.json", errors)
    if metadata_items.is_file():
        item_count = len(json.loads(metadata_items.read_text(encoding="utf-8")).get("items", []))
        if item_count != 583:
            errors.append(f"{metadata_items}: expected 583 semantic items, found {item_count}")
    for path in root.rglob("*.lean"):
        if any(part in {".lake", "_out"} for part in path.relative_to(root).parts):
            continue
        text = path.read_text(encoding="utf-8")
        if PRIVATE_HEADER not in text[:240]:
            errors.append(f"{path}: missing AMS copyright header")
    alignment_export = require_file(root, "AlignmentExport.lean", errors)
    require_text(
        alignment_export,
        (PRIVATE_HEADER, "#define_source_refs_json", "IO.println sourceReferences"),
        errors,
    )
    build_script = require_file(root, "scripts/build_site.py", errors)
    require_text(build_script, (PRIVATE_HEADER,), errors)
    panel_sync = require_file(root, "scripts/sync_formalization_panels.py", errors)
    require_text(
        panel_sync,
        (PRIVATE_HEADER, "metadata/items.json", "## Formalization", "--check"),
        errors,
    )
    lakefile = require_file(root, "lakefile.toml", errors)
    require_text(lakefile, ('name = "alignmentExport"', 'root = "AlignmentExport"'), errors)
    private_ci = require_file(root, ".github/workflows/ci.yml", errors)
    updater = require_file(root, ".github/workflows/update-formalization.yml", errors)
    require_text(
        private_ci,
        (
            "leanprover/lean-action@v1",
            "actions/upload-artifact@v4",
            "_out/html-multi",
            "AlignmentExport.lean",
            "sync_formalization_panels.py --check",
        ),
        errors,
    )
    require_text(
        updater,
        (
            "repository_dispatch:",
            "formalization-updated",
            "scripts/update_formalization_dependency.py",
            "AlignmentExport.lean",
            "scripts/sync_formalization_panels.py",
            "gh workflow run ci.yml",
            "gh pr merge",
            "--auto",
        ),
        errors,
    )
    if updater.is_file() and "lake-manifest.json" in updater.read_text(encoding="utf-8"):
        errors.append(
            f"{updater}: must not stage excluded generated lake-manifest.json"
        )
    workflow_text = "\n".join(
        path.read_text(encoding="utf-8")
        for path in sorted((root / ".github/workflows").glob("*.yml"))
    ).lower()
    for forbidden in ("actions/deploy-pages", "github-pages"):
        if forbidden in workflow_text:
            errors.append(f"{root}: private workflows contain public Pages deployment marker {forbidden!r}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("public_release", type=Path)
    parser.add_argument("private_release", type=Path)
    args = parser.parse_args()
    errors: list[str] = []
    validate_public(args.public_release.resolve(), errors)
    validate_private(args.private_release.resolve(), errors)
    print(json.dumps({"errors": len(errors)}, sort_keys=True))
    if errors:
        raise SystemExit("\n".join(errors[:100]))


if __name__ == "__main__":
    main()
