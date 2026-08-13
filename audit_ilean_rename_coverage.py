#!/usr/bin/env python3
"""Audit whether Lean's identifier index can drive exact clean-room renaming."""

from __future__ import annotations

import argparse
import json
import re
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


def simps_generated_origin(
    old_fqn: str,
    module: str,
    source: str,
    ilean: dict,
    proposals_by_old: dict[str, dict],
) -> tuple[str, list] | None:
    """Find an indexed ``@[simps]`` declaration that generated ``old_fqn``.

    Declarations synthesized by ``simps`` exist in the environment but have no
    source token of their own, so Lean's identifier index cannot give them a
    definition range.  Accept that exceptional case only when the missing name
    extends a resolved declaration in the same provider module and that
    declaration has an immediately attached ``@[simps]`` attribute.
    """
    references = ilean.get("references", {})
    source_lines = source.splitlines(keepends=True)
    candidates = sorted(proposals_by_old, key=len, reverse=True)
    for parent_fqn in candidates:
        parent = proposals_by_old[parent_fqn]
        if parent.get("old_module") != module or not old_fqn.startswith(parent_fqn + "_"):
            continue
        parent_ref = next(
            (
                record
                for encoded, record in references.items()
                if reference_name(encoded) == parent_fqn
            ),
            None,
        )
        position = parent_ref.get("definition") if parent_ref else None
        if position is None:
            continue
        start_line = position[0]
        attached_context = "".join(source_lines[max(0, start_line - 2) : start_line + 1])
        if re.search(r"@\[\s*simps!?[^\]]*\]\s*(?:noncomputable\s+)?def\s+", attached_context):
            return parent_fqn, position
    return None


def reassoc_generated_origin(
    old_fqn: str,
    module: str,
    source: str,
    ilean: dict,
    proposals_by_old: dict[str, dict],
) -> tuple[str, list] | None:
    """Find the indexed ``@[reassoc]`` lemma that generated ``old_fqn``.

    A reassociation theorem has no source token of its own.  Accept that case
    only when both the old and new names are exact ``_assoc`` extensions, the
    child is absent from the provider index or has a null definition, and the
    indexed parent lemma has an attached ``@[reassoc]`` attribute.  A later
    explicit attribute additionally requires an indexed null child.
    """
    if not old_fqn.endswith("_assoc"):
        return None
    parent_fqn = old_fqn.removesuffix("_assoc")
    child = proposals_by_old.get(old_fqn)
    parent = proposals_by_old.get(parent_fqn)
    if child is None or parent is None:
        return None
    if (
        child.get("old_module") != module
        or parent.get("old_module") != module
        or child.get("new_module") != parent.get("new_module")
        or child.get("new_fqn") != f"{parent.get('new_fqn')}_assoc"
    ):
        return None

    references = ilean.get("references", {})
    child_ref = next(
        (
            record
            for encoded, record in references.items()
            if reference_name(encoded) == old_fqn
        ),
        None,
    )
    parent_ref = next(
        (
            record
            for encoded, record in references.items()
            if reference_name(encoded) == parent_fqn
        ),
        None,
    )
    if child_ref is not None and child_ref.get("definition") is not None:
        return None
    position = parent_ref.get("definition") if parent_ref else None
    if position is None:
        return None
    try:
        spelling = source_slice(source, position)
    except (ValueError, UnicodeError):
        return None
    if parent_fqn.rsplit(".", 1)[-1] != spelling:
        return None

    source_lines = source.splitlines(keepends=True)
    start_line = position[0]
    attached_context = "".join(source_lines[max(0, start_line - 2) : start_line + 1])
    attached = re.search(r"@\[\s*reassoc\s*\]\s*(?:lemma|theorem)\s+", attached_context)
    explicit = re.search(
        rf"(?m)^\s*attribute\s+\[\s*reassoc\s*\]\s+{re.escape(spelling)}\s*$",
        source,
    )
    if attached is None:
        if child_ref is None or explicit is None:
            return None
        explicit_line = source.count("\n", 0, explicit.start())
        if explicit_line <= start_line:
            return None
    return parent_fqn, position


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
            generated = simps_generated_origin(old_fqn, module, source, ilean, by_old)
            generated_by = "simps"
            if generated is None:
                generated = reassoc_generated_origin(old_fqn, module, source, ilean, by_old)
                generated_by = "reassoc"
            if generated is None:
                errors.append(f"{old_fqn}: no definition range in provider ilean")
                continue
            parent_fqn, parent_position = generated
            definition_audit.append({
                "temporary_id": proposal["temporary_id"],
                "old_fqn": old_fqn,
                "new_fqn": proposal["new_fqn"],
                "old_module": module,
                "new_module": proposal["new_module"],
                "definition_range": None,
                "definition_spelling": None,
                "generated_by": generated_by,
                "generated_from": parent_fqn,
                "generator_definition_range": parent_position[:4],
            })
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
