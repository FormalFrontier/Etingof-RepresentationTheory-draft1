#!/usr/bin/env python3
"""Report which clean-room-renamed modules have a closed renamed import graph."""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path


IMPORT = re.compile(r"(?m)^\s*(?:public\s+)?import\s+([^\s]+)\s*$")


def strip_lean_comments(source: str) -> str:
    """Remove nested Lean comments while preserving strings and identifier apostrophes."""

    output: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False
    while index < len(source):
        char = source[index]
        following = source[index + 1] if index + 1 < len(source) else ""
        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                output.append(char)
            index += 1
            continue
        if block_depth:
            if char == "/" and following == "-":
                block_depth += 1
                index += 2
            elif char == "-" and following == "/":
                block_depth -= 1
                index += 2
            else:
                if char == "\n":
                    output.append(char)
                index += 1
            continue
        if in_string:
            output.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            output.append(char)
            index += 1
        elif char == "-" and following == "-":
            in_line_comment = True
            index += 2
        elif char == "/" and following == "-":
            block_depth = 1
            index += 2
        else:
            output.append(char)
            index += 1
    return "".join(output)


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("draft", type=Path)
    parser.add_argument("module_disposition", type=Path)
    parser.add_argument("private_mapping", type=Path)
    parser.add_argument("proposals", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    draft = args.draft.resolve()
    dispositions = json.loads(args.module_disposition.read_text(encoding="utf-8"))["records"]
    project_modules = {row["module"]: row for row in dispositions}
    mapping = read_jsonl(args.private_mapping)
    proposals = {row["temporary_id"]: row for row in read_jsonl(args.proposals)}

    ids_by_module: dict[str, set[str]] = defaultdict(set)
    for row in mapping:
        ids_by_module[row["old_module"]].add(row["temporary_id"])

    resolved_modules: dict[str, str] = {}
    partially_resolved: dict[str, list[str]] = {}
    for old_module, temporary_ids in sorted(ids_by_module.items()):
        unresolved = sorted(
            temporary_id
            for temporary_id in temporary_ids
            if not proposals.get(temporary_id, {}).get("new_fqn")
        )
        new_modules = {
            proposals[temporary_id]["new_module"]
            for temporary_id in temporary_ids
            if proposals.get(temporary_id, {}).get("new_fqn")
        }
        if unresolved:
            if new_modules:
                partially_resolved[old_module] = unresolved
            continue
        if len(new_modules) != 1:
            partially_resolved[old_module] = ["inconsistent-new-module"]
            continue
        resolved_modules[old_module] = new_modules.pop()

    dependencies: dict[str, list[str]] = {}
    direct_blockers: dict[str, list[str]] = {}

    source_by_module: dict[str, str] = {}
    imports_by_module: dict[str, list[str]] = {}

    def source_for(module: str) -> str:
        if module not in source_by_module:
            source_by_module[module] = (draft / project_modules[module]["path"]).read_text(
                encoding="utf-8"
            )
        return source_by_module[module]

    def project_imports_for(module: str) -> list[str]:
        if module not in imports_by_module:
            imports_by_module[module] = sorted(
                imported
                for imported in IMPORT.findall(source_for(module))
                if imported in project_modules
            )
        return imports_by_module[module]

    def is_transparent_reexport(module: str) -> bool:
        without_comments = strip_lean_comments(source_for(module))
        return not IMPORT.sub("", without_comments).strip()

    def expand_import(module: str, active: set[str]) -> set[str]:
        if module in resolved_modules:
            return {module}
        if module in active or not is_transparent_reexport(module):
            return {module}
        expanded: set[str] = set()
        for imported in project_imports_for(module):
            expanded.update(expand_import(imported, active | {module}))
        return expanded

    for old_module in sorted(resolved_modules):
        row = project_modules.get(old_module)
        if row is None:
            direct_blockers[old_module] = ["missing-module-disposition"]
            continue
        project_imports = sorted(
            {
                expanded
                for imported in project_imports_for(old_module)
                for expanded in expand_import(imported, {old_module})
            }
        )
        dependencies[old_module] = project_imports
        blockers = [imported for imported in project_imports if imported not in resolved_modules]
        if blockers:
            direct_blockers[old_module] = blockers

    ready: set[str] = set()
    changed = True
    while changed:
        changed = False
        for module in resolved_modules:
            if module in ready or module in direct_blockers:
                continue
            if all(dependency in ready for dependency in dependencies.get(module, [])):
                ready.add(module)
                changed = True

    transitive_blockers = {
        module: sorted(set(dependencies.get(module, [])) - ready)
        for module in resolved_modules
        if module not in ready and module not in direct_blockers
    }
    report = {
        "schema_version": "clean-migration-plan/v1",
        "summary": {
            "eligible_source_modules": len(ids_by_module),
            "fully_named_modules": len(resolved_modules),
            "partially_named_modules": len(partially_resolved),
            "directly_blocked_modules": len(direct_blockers),
            "transitively_blocked_modules": len(transitive_blockers),
            "export_ready_modules": len(ready),
        },
        "export_ready": [
            {
                "old_module": module,
                "new_module": resolved_modules[module],
                "renamed_imports": {
                    dependency: resolved_modules[dependency]
                    for dependency in dependencies.get(module, [])
                },
            }
            for module in sorted(ready)
        ],
        "direct_blockers": direct_blockers,
        "transitive_blockers": transitive_blockers,
        "partially_resolved": partially_resolved,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report["summary"], sort_keys=True))


if __name__ == "__main__":
    main()
