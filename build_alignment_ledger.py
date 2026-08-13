#!/usr/bin/env python3
"""Build the frozen private declaration/alignment migration ledger."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path
from typing import Any, Iterator


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def stable_id(prefix: str, *parts: str) -> str:
    material = "\x1f".join(parts).encode("utf-8")
    return f"{prefix}:{sha256_bytes(material)[:20]}"


def load_validator(root: Path):
    path = root / "scripts/validate_lean_decls.py"
    spec = importlib.util.spec_from_file_location("draft_validate_lean_decls", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def jsonl(path: Path, records: Iterator[dict[str, Any]]) -> int:
    count = 0
    with path.open("w", encoding="utf-8") as stream:
        for record in records:
            stream.write(json.dumps(record, sort_keys=True) + "\n")
            count += 1
    return count


def module_path(root: Path, module: str) -> Path | None:
    path = root / (module.replace(".", "/") + ".lean")
    return path if path.exists() else None


def item_identity(item: dict[str, Any]) -> tuple[str, str]:
    if item.get("id"):
        return f"partition:{item['id']}", str(item["id"])
    parent = str(item["derived_from"])
    identity = stable_id(
        "derived", parent, str(item.get("source_span", "")), str(item.get("claim", ""))
    )
    return identity, parent


def claim_identity(item_node: str, claim: dict[str, Any], ordinal: int) -> str:
    unit = claim.get("unit")
    if isinstance(unit, str) and unit:
        return f"claim:{item_node.removeprefix('partition:')}:{unit}"
    text = str(claim.get("claim") or claim.get("text") or claim.get("description") or "")
    return stable_id("claim", item_node, str(ordinal), text)


def source_nodes(items: list[dict[str, Any]]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for item in items:
        item_node, parent = item_identity(item)
        records.append(
            {
                "source_node": item_node,
                "kind": "partition" if item.get("id") else "derived",
                "item_id": item.get("id"),
                "parent_item_id": parent if not item.get("id") else None,
                "item_type": item.get("type"),
                "status": item.get("status"),
                "source_text_sha256": sha256_bytes(
                    str(item.get("claim") or item.get("source_span") or "").encode("utf-8")
                ),
            }
        )
        claims = ((item.get("claim_coverage") or {}).get("claims") or [])
        for ordinal, claim in enumerate(claims, start=1):
            if not isinstance(claim, dict):
                continue
            claim_node = claim_identity(item_node, claim, ordinal)
            text = str(claim.get("claim") or claim.get("text") or claim.get("description") or "")
            records.append(
                {
                    "source_node": claim_node,
                    "kind": "claim",
                    "item_id": item.get("id"),
                    "parent_source_node": item_node,
                    "ordinal": ordinal,
                    "unit": claim.get("unit"),
                    "verdict": claim.get("verdict") or claim.get("status"),
                    "claim_text_sha256": sha256_bytes(text.encode("utf-8")),
                }
            )
    return records


def parse_raw_declarations(raw_path: Path) -> list[dict[str, str]]:
    declarations: list[dict[str, str]] = []
    with gzip.open(raw_path, "rt", encoding="utf-8") as stream:
        for line in stream:
            fields = line.rstrip("\n").split("\t")
            if fields[0] == "D" and len(fields) == 4:
                declarations.append(
                    {"old_fqn": fields[1], "provider_module": fields[2], "kind": fields[3]}
                )
    return declarations


def strip_lean_comments_and_strings(source: str) -> str:
    """Blank comments and strings while preserving line structure.

    Apostrophes are intentionally left alone: in Lean they commonly occur in
    identifiers, and treating them as character delimiters corrupts the rest
    of a source line.
    """
    result: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(source):
        pair = source[index : index + 2]
        char = source[index]
        if block_depth:
            if pair == "/-":
                result.extend("  ")
                block_depth += 1
                index += 2
            elif pair == "-/":
                result.extend("  ")
                block_depth -= 1
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            if char == "\\" and index + 1 < len(source):
                result.extend("  ")
                index += 2
            elif char == '"':
                result.append(" ")
                in_string = False
                index += 1
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "/-":
            result.extend("  ")
            block_depth = 1
            index += 2
        elif pair == "--":
            while index < len(source) and source[index] != "\n":
                result.append(" ")
                index += 1
        elif char == '"':
            result.append(" ")
            in_string = True
            index += 1
        else:
            result.append(char)
            index += 1
    return "".join(result)


def explicit_declaration_tokens(path: Path | None) -> set[str]:
    """Return source-spelled names introduced by declaration commands."""
    if path is None:
        return set()
    source = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
    return {
        match.group(1)
        for match in re.finditer(
            r"(?m)^\s*(?:@\[[^\n]*\]\s*)*"
            r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
            r"(?:theorem|lemma|def|abbrev|opaque|instance)\s+"
            r"([^\s:({\[]+)",
            source,
        )
    }


def source_explicitly_declares(name: str, tokens: set[str]) -> bool:
    """Whether a source declaration token can resolve to ``name``."""
    parts = name.split(".")
    suffixes = {".".join(parts[index:]) for index in range(len(parts))}
    return bool(tokens & suffixes)


def is_generated(name: str, kind: str, *, explicitly_declared: bool = False) -> bool:
    if kind in {"constructor", "recursor"}:
        return True
    # These names are emitted by elaborators rather than introduced by a
    # declaration command.  The explicit-source guard matters for conventional
    # names such as `ext` and `instReprFoo`: both are also valid user names.
    source_sensitive_generated = bool(
        re.search(
            r"(?:\._unsafe_rec|\.toCtorIdx|(?:^|\.)instRepr[^.]+(?:\.repr)?|\.ext|"
            r"\._sparseCasesOn_[1-9][0-9]*(?:\.[A-Za-z_][A-Za-z0-9_']*_eq)?)$",
            name,
        )
    )
    if source_sensitive_generated and not explicitly_declared:
        return True
    return bool(
        re.search(
            r"(?:\._proof_|\._eq_|\.eq_[0-9]+$|\._unary|\._match_|\._aux|"
            r"\.match_[0-9]|\.rec(?:On)?$|\.casesOn$|\.brecOn$|\.below$|"
            r"\.binductionOn$|\.noConfusion(?:Type)?$|\.ctorIdx$|\.injEq$|"
            r"\.intro$|\.elim$|\.toNat$|\.mk\._flat_ctor$|\.mk\.inj$|"
            r"\.mk\.sizeOf_spec$|\._sizeOf_(?:[0-9]+|inst)$|"
            r"\.[^.]+\.sizeOf_spec$|\.ctorElim(?:Type)?$|\.[^.]+\.inj$|"
            r"\.instDecidableEq[A-Za-z0-9_']*$|\.decEq$|"
            r"\._abel_(?:[0-9]+_)*[0-9]+$|\.lieSubalgebraOfLieAlgebra$|"
            r"\._f$|\._sunfold$|\.eq_def$|\.ext_iff$|"
            r"\._simp_(?:[0-9]+_)*[0-9]+$|\.congr_simp$)",
            name,
        )
    )


def alignment_edges(items: list[dict[str, Any]], validator: Any) -> list[dict[str, Any]]:
    edges: list[dict[str, Any]] = []

    def pointers(value: dict[str, Any], source_node: str, path: str, verdict: Any) -> None:
        for key, child in value.items():
            here = f"{path}/{key}"
            if key == "lean_decl":
                errors: list[str] = []
                for name in validator.exact_names(child, here, errors):
                    edges.append(
                        {
                            "source_node": source_node,
                            "old_fqn": name,
                            "role": "pending_adjudication",
                            "authority": "explicit_lean_decl",
                            "verdict": verdict,
                            "evidence_pointer": here,
                        }
                    )
                if errors:
                    raise SystemExit("; ".join(errors))
            elif key == "lean_ref":
                errors = []
                for provider_path, names in validator.lean_ref_groups(child, here, errors):
                    for name in names:
                        edges.append(
                            {
                                "source_node": source_node,
                                "old_fqn": name,
                                "role": "pending_adjudication",
                                "authority": "explicit_lean_ref",
                                "verdict": verdict,
                                "provider_path_hint": provider_path,
                                "evidence_pointer": here,
                            }
                        )
                if errors:
                    raise SystemExit("; ".join(errors))
            elif key == "claims" and isinstance(child, list):
                for ordinal, claim in enumerate(child, start=1):
                    if isinstance(claim, dict):
                        claim_node = claim_identity(source_node, claim, ordinal)
                        pointers(
                            claim,
                            claim_node,
                            f"{here}/{ordinal - 1}",
                            claim.get("verdict") or claim.get("status"),
                        )
            elif isinstance(child, dict):
                pointers(child, source_node, here, verdict)
            elif isinstance(child, list):
                for index, entry in enumerate(child):
                    if isinstance(entry, dict):
                        pointers(entry, source_node, f"{here}/{index}", verdict)

    for index, item in enumerate(items):
        item_node, _ = item_identity(item)
        pointers(item, item_node, f"/items/{index}", item.get("status"))
    return edges


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("draft", type=Path)
    parser.add_argument("module_disposition", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = args.draft.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)

    items_path = root / "progress/items.json"
    providers_path = root / "scripts/lean-decl-providers.json"
    stage34_path = root / "progress/reviews/2026-08-01-stage3-4-proof-terms.json"
    raw_path = root / "progress/reviews/2026-08-01-stage3-4-proof-terms.tsv.gz"
    items = json.loads(items_path.read_text(encoding="utf-8"))
    providers = json.loads(providers_path.read_text(encoding="utf-8"))
    module_ledger = json.loads(args.module_disposition.read_text(encoding="utf-8"))
    dispositions = {record["module"]: record for record in module_ledger["records"]}
    validator = load_validator(root)

    nodes = source_nodes(items)
    declarations = parse_raw_declarations(raw_path)
    edges = alignment_edges(items, validator)
    cited_names = {edge["old_fqn"] for edge in edges}

    explicit_tokens_by_path: dict[Path | None, set[str]] = {}
    declaration_records = []
    for ordinal, declaration in enumerate(sorted(declarations, key=lambda row: row["old_fqn"]), start=1):
        name = declaration["old_fqn"]
        module = declaration["provider_module"]
        path = module_path(root, module)
        disposition = dispositions.get(module)
        visibility = "private" if name.startswith("_private.") else "public"
        if path not in explicit_tokens_by_path:
            explicit_tokens_by_path[path] = explicit_declaration_tokens(path)
        generated = is_generated(
            name,
            declaration["kind"],
            explicitly_declared=source_explicitly_declares(
                name, explicit_tokens_by_path[path]
            ),
        )
        declaration_records.append(
            {
                "declaration_id": f"decl-{ordinal:06d}",
                **declaration,
                "source_path": str(path.relative_to(root)) if path else None,
                "source_sha256": sha256_file(path) if path else None,
                "visibility": visibility,
                "compiler_generated": generated,
                "exactly_cited": name in cited_names,
                "module_disposition": disposition["disposition"] if disposition else "unknown",
                "migration_class": (
                    "compiler_generated"
                    if generated
                    else "private"
                    if visibility == "private"
                    else "book_facing"
                    if name in cited_names
                    else "support_candidate"
                ),
                "structural_type_hash": None,
                "pretty_type_available": False,
                "new_fqn": None,
                "new_module": None,
                "rename_status": "pending",
            }
        )

    by_name = {record["old_fqn"]: record for record in declaration_records}
    for edge in edges:
        record = by_name.get(edge["old_fqn"])
        edge["declaration_id"] = record["declaration_id"] if record else None
        edge["provider_module"] = providers.get(edge["old_fqn"])
        edge["confidence"] = "explicit"
        edge["adjudication_status"] = "pending"

    files = {
        "source_nodes": "source-nodes.jsonl",
        "declarations": "declarations.jsonl",
        "alignment_edges": "alignment-edges.jsonl",
    }
    counts = {
        "source_nodes": jsonl(output / files["source_nodes"], iter(nodes)),
        "declarations": jsonl(output / files["declarations"], iter(declaration_records)),
        "alignment_edges": jsonl(output / files["alignment_edges"], iter(edges)),
    }
    manifest = {
        "schema_version": "etingof-alignment-migration/v1",
        "snapshot": {
            "commit": module_ledger["source_commit"],
            "lean_toolchain": (root / "lean-toolchain").read_text(encoding="utf-8").strip(),
            "progress_items_sha256": sha256_file(items_path),
            "decl_providers_sha256": sha256_file(providers_path),
            "stage34_sha256": sha256_file(stage34_path),
            "raw_extraction_archive_sha256": sha256_file(raw_path),
        },
        "files": files,
        "counts": counts,
        "roles": ["primary", "supporting", "pending_adjudication"],
        "release_gate": "blocked_until_all_pending_adjudication_edges_and_renames_are_resolved",
    }
    for key, relative in files.items():
        manifest.setdefault("hashes", {})[key] = sha256_file(output / relative)
    (output / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
