#!/usr/bin/env python3
"""Create a private, tainted-but-filtered Lean workspace for release migration."""

from __future__ import annotations

import argparse
import json
import shutil
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("draft", type=Path)
    parser.add_argument("disposition", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    draft = args.draft.resolve()
    output = args.output.resolve()
    ledger = json.loads(args.disposition.read_text(encoding="utf-8"))
    if output.exists():
        shutil.rmtree(output)
    output.mkdir(parents=True)

    copied_modules: list[str] = []
    copied_paths: set[str] = set()
    for record in ledger["records"]:
        if record["disposition"] not in {"include", "split_review"}:
            continue
        relative = record["path"]
        source = draft / relative
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        copied_paths.add(relative)
        copied_modules.append(record["module"])

    root_lines = [f"import {module}" for module in sorted(copied_modules)]
    (output / "EtingofRepresentationTheory.lean").write_text(
        "\n".join(root_lines) + "\n", encoding="utf-8"
    )
    copied_paths.add("EtingofRepresentationTheory.lean")

    for name in ("lean-toolchain", "lake-manifest.json"):
        shutil.copyfile(draft / name, output / name)
    (output / "lakefile.toml").write_text(
        """name = "EtingofRepresentationTheoryReleaseStaging"
version = "0.0.0-private"
defaultTargets = ["EtingofRepresentationTheory"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3
weak.backward.isDefEq.respectTransparency = false

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.32.2"

[[lean_lib]]
name = "EtingofRepresentationTheory"
""",
        encoding="utf-8",
    )
    (output / ".gitignore").write_text("/.lake/\n", encoding="utf-8")
    (output / "FILTERED-SOURCE.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "source_commit": ledger["source_commit"],
                "copied_module_count": len(copied_modules),
                "copied_paths": sorted(copied_paths),
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
