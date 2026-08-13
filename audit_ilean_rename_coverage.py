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
    indexed parent lemma has an attached ``@[reassoc]`` or
    ``@[reassoc (attr := simp)]`` attribute.  A later explicit attribute
    additionally requires an indexed null child.
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
    attached = re.search(
        r"@\[\s*reassoc(?:\s*\(\s*attr\s*:=\s*simp\s*\))?\s*\]"
        r"\s*(?:lemma|theorem)\s+",
        attached_context,
    )
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


def extends_projection_generated_origin(
    old_fqn: str,
    module: str,
    source: str,
    ilean: dict,
    proposals_by_old: dict[str, dict],
) -> tuple[str, list] | None:
    """Find a projection generated by a ``class ... extends ...`` clause.

    Lean does not assign an independent definition range to projections such
    as ``Foo.toBar`` that it synthesizes for ``class Foo extends Bar``.  Accept
    such a declaration only when the clean-room row is owned by the extended
    class, preserves the exact generated ``toBar`` suffix, and the indexed
    parent command visibly extends that base class in the provider source.
    """
    parent_fqn, separator, projection = old_fqn.rpartition(".")
    if not separator or not projection.startswith("to") or len(projection) == 2:
        return None
    child = proposals_by_old.get(old_fqn)
    parent = proposals_by_old.get(parent_fqn)
    if child is None or parent is None:
        return None
    if (
        child.get("old_module") != module
        or parent.get("old_module") != module
        or child.get("owner_temporary_id") != parent.get("temporary_id")
        or child.get("new_module") != parent.get("new_module")
        or child.get("new_fqn") != f"{parent.get('new_fqn')}.{projection}"
    ):
        return None

    parent_ref = next(
        (
            record
            for encoded, record in ilean.get("references", {}).items()
            if reference_name(encoded) == parent_fqn
        ),
        None,
    )
    position = parent_ref.get("definition") if parent_ref else None
    if position is None:
        return None
    try:
        spelling = source_slice(source, position)
    except (ValueError, UnicodeError):
        return None
    if spelling not in {parent_fqn, parent_fqn.rsplit(".", 1)[-1]}:
        return None

    source_lines = source.splitlines(keepends=True)
    header = "".join(source_lines[position[0] : position[0] + 25])
    command = re.search(
        rf"\b(?:class|structure)\s+{re.escape(spelling)}\b(?P<body>.*?)\bwhere\b",
        header,
        flags=re.DOTALL,
    )
    if command is None:
        return None
    extends = re.search(r"\bextends\b(?P<bases>.*)", command.group("body"), flags=re.DOTALL)
    if extends is None:
        return None
    base = projection.removeprefix("to")
    if re.search(
        rf"(?:^|,)\s*(?:[A-Za-z_][A-Za-z0-9_']*\.)*{re.escape(base)}\b",
        extends.group("bases"),
    ) is None:
        return None
    return parent_fqn, position


def tactic_macro_generated_origin(
    old_fqn: str,
    source: str,
) -> tuple[str, list[int]] | None:
    """Locate the string token that generated a tactic-macro declaration.

    Lean gives a command such as ``macro "cartan_det" : tactic =>`` the
    synthesized environment name ``tacticCartan_det``.  That declaration has
    neither an identifier token nor a definition range in the ``.ilean`` file.
    Accept this case only for an exact, unique one-token tactic macro enclosed
    by the namespace encoded in ``old_fqn``.
    """
    namespace, separator, leaf = old_fqn.rpartition(".")
    if not separator or not leaf.startswith("tactic") or len(leaf) == len("tactic"):
        return None
    surface = leaf[len("tactic") :]
    surface = surface[:1].lower() + surface[1:]
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", surface):
        return None
    expected_leaf = f"tactic{surface[:1].upper()}{surface[1:]}"
    if leaf != expected_leaf:
        return None

    # Preserve offsets while hiding line comments and nested block comments so
    # that commented-out macro or namespace commands cannot satisfy the audit.
    visible = list(source)
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        if block_depth:
            if source.startswith("/-", index):
                visible[index : index + 2] = "  "
                block_depth += 1
                index += 2
            elif source.startswith("-/", index):
                visible[index : index + 2] = "  "
                block_depth -= 1
                index += 2
            else:
                if source[index] != "\n":
                    visible[index] = " "
                index += 1
        elif in_string:
            if escaped:
                escaped = False
            elif source[index] == "\\":
                escaped = True
            elif source[index] == '"':
                in_string = False
            index += 1
        elif source.startswith("--", index):
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            visible[index:end] = " " * (end - index)
            index = end
        elif source.startswith("/-", index):
            visible[index : index + 2] = "  "
            block_depth = 1
            index += 2
        else:
            if source[index] == '"':
                in_string = True
            index += 1
    visible_source = "".join(visible)

    pattern = re.compile(
        rf'(?m)^[ \t]*macro[ \t]+"(?P<surface>{re.escape(surface)})"'
        r"[ \t]*:[ \t]*tactic[ \t]*=>"
    )
    matches = list(pattern.finditer(visible_source))
    if len(matches) != 1:
        return None
    match = matches[0]

    namespace_pattern = re.compile(
        rf"(?m)^[ \t]*namespace[ \t]+{re.escape(namespace)}[ \t]*$"
    )
    namespace_matches = list(namespace_pattern.finditer(visible_source, 0, match.start()))
    if not namespace_matches:
        return None
    namespace_match = namespace_matches[-1]
    scope_boundary_pattern = re.compile(
        r"(?m)^[ \t]*(?:namespace(?:[ \t]+[^\r\n]+)?|end(?:[ \t]+[^\r\n]+)?)[ \t]*$"
    )
    if scope_boundary_pattern.search(visible_source, namespace_match.end(), match.start()):
        return None

    end_pattern = re.compile(
        rf"(?m)^[ \t]*end[ \t]+{re.escape(namespace)}[ \t]*$"
    )
    end_match = end_pattern.search(visible_source, match.end())
    if end_match is None:
        return None
    boundary = scope_boundary_pattern.search(visible_source, match.end(), end_match.end())
    if boundary is None or boundary.start() != end_match.start():
        return None

    start = match.start("surface")
    end = match.end("surface")
    start_line = source.count("\n", 0, start)
    start_column = start - (source.rfind("\n", 0, start) + 1)
    end_line = source.count("\n", 0, end)
    end_column = end - (source.rfind("\n", 0, end) + 1)
    if start_line != end_line:
        return None
    return surface, [start_line, start_column, end_line, end_column]


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
                generated = extends_projection_generated_origin(
                    old_fqn, module, source, ilean, by_old
                )
                generated_by = "extends_projection"
            if generated is None:
                macro_origin = tactic_macro_generated_origin(old_fqn, source)
                if macro_origin is None:
                    errors.append(f"{old_fqn}: no definition range in provider ilean")
                    continue
                macro_spelling, macro_position = macro_origin
                definition_audit.append({
                    "temporary_id": proposal["temporary_id"],
                    "old_fqn": old_fqn,
                    "new_fqn": proposal["new_fqn"],
                    "old_module": module,
                    "new_module": proposal["new_module"],
                    "definition_range": macro_position,
                    "definition_spelling": macro_spelling,
                    "generated_by": "tactic_macro",
                })
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
        # Some Lean/simps versions index a generated projection theorem at the
        # `simps` token rather than leaving its definition range null.  Accept
        # that representation only when the same strict source-side origin
        # check used for null-range generated declarations succeeds.
        if spelling == "simps":
            generated = simps_generated_origin(old_fqn, module, source, ilean, by_old)
            if generated is not None:
                parent_fqn, parent_position = generated
                definition_audit.append({
                    "temporary_id": proposal["temporary_id"],
                    "old_fqn": old_fqn,
                    "new_fqn": proposal["new_fqn"],
                    "old_module": module,
                    "new_module": proposal["new_module"],
                    "definition_range": position[:4],
                    "definition_spelling": spelling,
                    "generated_by": "simps",
                    "generated_from": parent_fqn,
                    "generator_definition_range": parent_position[:4],
                })
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
