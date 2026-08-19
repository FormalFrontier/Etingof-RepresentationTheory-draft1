#!/usr/bin/env python3
"""Synchronize roles on existing public ``source_ref`` attributes.

This intentionally does not add or remove references.  Missing and obsolete
reference keys can indicate that a corrected declaration migration is still
pending, whereas a role mismatch on an existing declaration/reference pair is
safe to update mechanically from the adjudicated ledger.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path

from validate_clean_release_source_refs import (
    canonical_reference,
    module_path,
    read_jsonl,
)


def expected_roles(
    release: Path,
    proposals_path: Path,
    edges_path: Path,
    source_nodes_path: Path,
) -> tuple[dict[tuple[str, str], str], dict[str, dict]]:
    proposals = [
        row for row in read_jsonl(proposals_path) if row.get("new_fqn")
    ]
    proposals_by_old = {row["old_fqn"]: row for row in proposals}
    proposals_by_new = {row["new_fqn"]: row for row in proposals}

    source_node_rows = read_jsonl(source_nodes_path)
    source_references: dict[str, str] = {}
    derived_counts: dict[str, int] = {}
    for row in source_node_rows:
        derived_ordinal = None
        if row["kind"] == "derived":
            parent = row["parent_item_id"]
            derived_counts[parent] = derived_counts.get(parent, 0) + 1
            derived_ordinal = derived_counts[parent]
        source_references[row["source_node"]] = canonical_reference(
            row, derived_ordinal
        )

    result: dict[tuple[str, str], str] = {}
    for edge in read_jsonl(edges_path):
        if edge.get("adjudication_status") != "adjudicated":
            continue
        proposal = proposals_by_old.get(edge["old_fqn"])
        if proposal is None:
            continue
        if not module_path(release, proposal["new_module"]).exists():
            continue
        key = (
            proposal["new_fqn"],
            source_references[edge["source_node"]],
        )
        if edge["role"] == "primary" or key not in result:
            result[key] = edge["role"]
    return result, proposals_by_new


def exported_roles(release: Path) -> dict[tuple[str, str], str]:
    completed = subprocess.run(
        ["lake", "env", "lean", "--run", "AlignmentExport.lean"],
        cwd=release,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        raise SystemExit(
            "alignment export failed:\n" + completed.stdout + completed.stderr
        )
    rows = json.loads(completed.stdout)
    result = {
        (row["declaration"], row["reference"]): row["role"]
        for row in rows
    }
    if len(result) != len(rows):
        raise SystemExit("alignment export contains duplicate entries")
    return result


def ilean_declarations(release: Path, module: str) -> dict[str, list[int]]:
    path = (
        release
        / ".lake/build/lib/lean"
        / (module.replace(".", "/") + ".ilean")
    )
    if not path.exists():
        raise ValueError(f"missing identifier index for {module}: {path}")
    with path.open(encoding="utf-8") as stream:
        return json.load(stream)["decls"]


def synchronize(
    release: Path,
    proposals_by_new: dict[str, dict],
    role_changes: dict[tuple[str, str], tuple[str, str]],
) -> tuple[dict[Path, str], int]:
    changes_by_module: dict[str, list[tuple[str, str, str, str]]] = (
        defaultdict(list)
    )
    for (declaration, reference), (old_role, new_role) in role_changes.items():
        proposal = proposals_by_new.get(declaration)
        if proposal is None:
            raise ValueError(f"no approved proposal for {declaration}")
        changes_by_module[proposal["new_module"]].append(
            (declaration, reference, old_role, new_role)
        )

    rewritten: dict[Path, str] = {}
    total = 0
    for module, changes in sorted(changes_by_module.items()):
        path = module_path(release, module)
        text = path.read_text(encoding="utf-8")
        declarations = ilean_declarations(release, module)

        for declaration, reference, old_role, new_role in sorted(changes):
            lines = text.splitlines(keepends=True)
            position = declarations.get(declaration)
            pattern = re.compile(
                r"(source_ref\s*\""
                + re.escape(reference)
                + r"\"\s*\(\s*role\s*:=\s*)"
                + re.escape(old_role)
                + r"(\s*\))"
            )
            if position is None or len(position) < 6:
                # Lean's identifier index can omit declarations such as
                # ``abbrev``.  In that case, select a pre-declaration
                # attribute by both its reference and the explicit local
                # declaration name in the immediately following command.
                local_name = declaration.rsplit(".", 1)[-1]
                name_pattern = re.compile(
                    r"(?<![A-Za-z0-9_'])"
                    + re.escape(local_name)
                    + r"(?![A-Za-z0-9_'])"
                )
                candidates: list[re.Match[str]] = []
                for match in pattern.finditer(text):
                    close = text.find("]", match.end())
                    if close < 0:
                        continue
                    tail = text[close + 1 : close + 2001]
                    tail = tail.split("\n\n", 1)[0]
                    if name_pattern.search(tail):
                        candidates.append(match)
                if len(candidates) != 1:
                    raise ValueError(
                        f"missing source position and expected one "
                        f"pre-declaration {old_role} attribute for "
                        f"{declaration} | {reference}, found {len(candidates)}"
                    )
                match = candidates[0]
                text = (
                    text[: match.start()]
                    + match.group(1)
                    + new_role
                    + match.group(2)
                    + text[match.end() :]
                )
                total += 1
                continue

            start_line = position[0]
            selection_line = position[4]
            segment = "".join(lines[start_line : selection_line + 1])
            matches = list(pattern.finditer(segment))
            if len(matches) == 1:
                match = matches[0]
                segment = (
                    segment[: match.start()]
                    + match.group(1)
                    + new_role
                    + match.group(2)
                    + segment[match.end() :]
                )
                replacement_lines = segment.splitlines(keepends=True)
                if len(replacement_lines) != selection_line + 1 - start_line:
                    raise ValueError(
                        f"role rewrite changed line count for {declaration}"
                    )
                lines[start_line : selection_line + 1] = replacement_lines
                text = "".join(lines)
                total += 1
                continue
            if matches:
                raise ValueError(
                    f"expected one {old_role} attribute for {declaration} | "
                    f"{reference} in source-position segment, found {len(matches)}"
                )

            # Some migrated files attach metadata after a declaration with an
            # ``attribute [...] declarationName`` command.  Select such a
            # command by both its reference and its explicit declaration name.
            local_name = declaration.rsplit(".", 1)[-1]
            candidates: list[re.Match[str]] = []
            for match in pattern.finditer(text):
                attribute_start = text.rfind("attribute", 0, match.start())
                if attribute_start < 0:
                    continue
                prefix = text[attribute_start : match.start()]
                if "\n\n" in prefix:
                    continue
                close = text.find("]", match.end())
                if close < 0:
                    continue
                tail = text[close + 1 : close + 1001]
                tail = tail.split("\n\n", 1)[0]
                name_pattern = re.compile(
                    r"(?<![A-Za-z0-9_'])"
                    + re.escape(local_name)
                    + r"(?![A-Za-z0-9_'])"
                )
                if name_pattern.search(tail):
                    candidates.append(match)
            if len(candidates) != 1:
                raise ValueError(
                    f"expected one post-declaration {old_role} attribute for "
                    f"{declaration} | {reference}, found {len(candidates)}"
                )
            match = candidates[0]
            text = (
                text[: match.start()]
                + match.group(1)
                + new_role
                + match.group(2)
                + text[match.end() :]
            )
            total += 1

        # ``text`` is authoritative here: the postfix-attribute branch edits
        # it directly, while the pre-declaration branch refreshes it from
        # ``lines`` after every replacement.
        rewritten[path] = text
    return rewritten, total


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("release", type=Path)
    parser.add_argument("proposals", type=Path)
    parser.add_argument("adjudicated_edges", type=Path)
    parser.add_argument("source_nodes", type=Path)
    parser.add_argument(
        "--check",
        action="store_true",
        help="report role mismatches without modifying source files",
    )
    args = parser.parse_args()

    release = args.release.resolve()
    expected, proposals_by_new = expected_roles(
        release,
        args.proposals,
        args.adjudicated_edges,
        args.source_nodes,
    )
    actual = exported_roles(release)
    common = set(actual) & set(expected)
    role_changes = {
        key: (actual[key], expected[key])
        for key in common
        if actual[key] != expected[key]
    }

    rewritten, changed = synchronize(
        release, proposals_by_new, role_changes
    )
    if changed != len(role_changes):
        raise SystemExit(
            f"located {changed} role attributes for {len(role_changes)} mismatches"
        )
    result = {
        "changed_roles": changed,
        "missing_reference_keys": len(set(expected) - set(actual)),
        "obsolete_reference_keys": len(set(actual) - set(expected)),
    }
    print(json.dumps(result, sort_keys=True))

    if args.check:
        # Reaching this point proves that every reported mismatch was located
        # unambiguously and could be rewritten without changing line counts.
        # Dry-run mode intentionally reports pending changes as success.
        return
    for path, text in rewritten.items():
        path.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
