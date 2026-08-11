#!/usr/bin/env python3
"""Audit whether Lean's identifier index can drive exact clean-room renaming."""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def reference_name(encoded: str) -> str | None:
    try:
        value = json.loads(encoded)
    except json.JSONDecodeError:
        return None
    return value.get("c", {}).get("n") if isinstance(value, dict) else None


def source_slice(source: str, position: list) -> str:
    start_line, start_col, end_line, end_col = position[:4]
    lines = source.splitlines(keepends=True)
    if not (0 <= start_line < len(lines) and 0 <= end_line < len(lines)):
        raise ValueError(f"line out of bounds: {position[:4]}")
    if start_line == end_line:
        return lines[start_line][start_col:end_col]
    chunks = [lines[start_line][start_col:]]
    chunks.extend(lines[start_line + 1 : end_line])
    chunks.append(lines[end_line][:end_col])
    return "".join(chunks)


def module_path(root: Path, module: str, suffix: str) -> Path:
    return root / (module.replace(".", "/") + suffix)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("tainted", type=Path)
    parser.add_argument("proposals", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    proposals = [row for row in read_jsonl(args.proposals) if row.get("new_fqn")]
    by_old = {row["old_fqn"]: row for row in proposals}
    definition_audit: list[dict] = []
    usage_counts: Counter[str] = Counter()
    usage_spellings: dict[str, Counter[str]] = defaultdict(Counter)
    errors: list[str] = []

    source_cache: dict[str, str] = {}
    ilean_cache: dict[str, dict] = {}

    def load(module: str) -> tuple[str, dict]:
        if module not in source_cache:
            source_path = module_path(args.tainted, module, ".lean")
            ilean_path = module_path(args.tainted / ".lake/build/lib/lean", module, ".ilean")
            if source_path.stat().st_mtime_ns > ilean_path.stat().st_mtime_ns:
                raise OSError(
                    f"stale identifier index {ilean_path}: source is newer; rebuild the tainted snapshot"
                )
            source_cache[module] = source_path.read_text(encoding="utf-8")
            ilean_cache[module] = json.loads(ilean_path.read_text(encoding="utf-8"))
        return source_cache[module], ilean_cache[module]

    for old_fqn, proposal in sorted(by_old.items()):
        module = proposal["old_module"]
        try:
            source, ilean = load(module)
        except OSError as exc:
            errors.append(f"{old_fqn}: {exc}")
            continue
        ref = next(
            (
                record
                for encoded, record in ilean.get("references", {}).items()
                if reference_name(encoded) == old_fqn
            ),
            None,
        )
        position = ref.get("definition") if ref else None
        if position is None:
            errors.append(f"{old_fqn}: no definition range in provider ilean")
            continue
        try:
            spelling = source_slice(source, position)
        except (ValueError, UnicodeError) as exc:
            errors.append(f"{old_fqn}: invalid definition range {position[:4]}: {exc}")
            continue
        if not spelling or not (
            old_fqn.endswith(spelling)
            or spelling.endswith(old_fqn)
            or old_fqn.rsplit(".", 1)[-1] == spelling
            or spelling in {"instance", "theorem", "def", "abbrev"}
        ):
            errors.append(f"{old_fqn}: unexpected definition spelling {spelling!r}")
        definition_audit.append({
            "temporary_id": proposal["temporary_id"],
            "old_fqn": old_fqn,
            "new_fqn": proposal["new_fqn"],
            "old_module": module,
            "new_module": proposal["new_module"],
            "definition_range": position[:4],
            "definition_spelling": spelling,
        })

    ilean_root = args.tainted / ".lake/build/lib/lean/EtingofRepresentationTheory"
    for ilean_path in sorted(ilean_root.rglob("*.ilean")):
        ilean = json.loads(ilean_path.read_text(encoding="utf-8"))
        module = ilean["module"]
        source_path = module_path(args.tainted, module, ".lean")
        if not source_path.exists():
            continue
        if source_path.stat().st_mtime_ns > ilean_path.stat().st_mtime_ns:
            errors.append(f"{module}: source is newer than its identifier index")
            continue
        source = source_path.read_text(encoding="utf-8")
        for encoded, record in ilean.get("references", {}).items():
            old_fqn = reference_name(encoded)
            if old_fqn not in by_old:
                continue
            for usage in record.get("usages", []):
                try:
                    spelling = source_slice(source, usage)
                except (ValueError, UnicodeError) as exc:
                    errors.append(f"{module}: {old_fqn} invalid usage {usage[:4]}: {exc}")
                    continue
                usage_counts[old_fqn] += 1
                usage_spellings[old_fqn][spelling] += 1

    modules: dict[str, set[str]] = defaultdict(set)
    for proposal in proposals:
        modules[proposal["old_module"]].add(proposal["new_module"])
    split_modules = {old: sorted(new) for old, new in modules.items() if len(new) != 1}
    if split_modules:
        errors.append(f"source modules with multiple new modules: {split_modules}")

    report = {
        "schema_version": "cleanroom-ilean-rename-audit/v1",
        "summary": {
            "resolved_proposals": len(proposals),
            "definitions_indexed": len(definition_audit),
            "semantic_usages_indexed": sum(usage_counts.values()),
            "source_modules": len(modules),
            "errors": len(errors),
        },
        "errors": errors,
        "definitions": definition_audit,
        "usage_counts": {
            name: {
                "count": usage_counts[name],
                "spellings": dict(sorted(usage_spellings[name].items())),
            }
            for name in sorted(by_old)
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report["summary"], sort_keys=True))
    if errors:
        for error in errors[:20]:
            print(error)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
