#!/usr/bin/env python3
"""Finalize Stages 3.4 and 3.5 from reproducible repository evidence.

The dependency pass combines direct project imports of each item's provider
with explicit numbered references in its source blob.  It never invents a
forward dependency, and it preserves the hand-audited records already present.

The polishing pass requires a successful full-build log.  It records whether
each provider is warning-free or still governed by the checked-in warning
ratchet; editorial/folded items without a dedicated provider are marked not
applicable.  Run without ``--apply`` for a summary, then inspect before applying.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent.parent
ITEMS_PATH = ROOT / "progress" / "items.json"
DEPS_PATH = ROOT / "dependencies" / "internal.json"
LEAN_ROOT = ROOT / "EtingofRepresentationTheory"

IMPORT = re.compile(r"^import EtingofRepresentationTheory\.(\S+)\s*$", re.MULTILINE)
SOURCE_REFERENCE = re.compile(
    r"\b(Theorem|Lemma|Proposition|Corollary|Definition|Example|Remark|Problem|Exercise)\s+"
    r"(\d+)\.(\d+)(?:\.(\d+))?"
)
LEAN_PATH = re.compile(
    r"(?:(?:EtingofRepresentationTheory)/)?(Chapter\d+/[A-Za-z0-9_./-]+\.lean)"
)
WARNING = re.compile(
    r"^warning: (?P<file>EtingofRepresentationTheory/[^:\s]+\.lean):\d+:\d+: ",
    re.MULTILINE,
)


def normalized(value: str) -> str:
    return re.sub(r"[^a-z0-9]", "", value.lower())


def section(item_id: str) -> str | None:
    match = re.match(r"Chapter(\d+)/(.*)", item_id)
    if not match:
        return None
    chapter, tail = match.groups()
    found = re.search(rf"(?<!\d){chapter}[._](\d+)(?:[._]|$)", tail)
    return f"{chapter}.{found.group(1)}" if found else None


def blob_path(item_id: str) -> Path | None:
    candidate = ROOT / "blobs" / f"{item_id}.md"
    return candidate if candidate.exists() else None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-log", required=True, type=Path)
    parser.add_argument("--apply", action="store_true")
    parser.add_argument(
        "--regenerate-dependencies",
        action="store_true",
        help="replace every Stage-3.4 record instead of preserving completed records",
    )
    parser.add_argument(
        "--regenerate-polish",
        action="store_true",
        help="replace every Stage-3.5 record with build-diagnostic evidence",
    )
    args = parser.parse_args()

    log = args.build_log.read_text(encoding="utf-8", errors="replace")
    if "Build completed successfully" not in log or "error: build failed" in log:
        raise SystemExit("refusing to finalize from a build log that is not successful")

    all_items = json.loads(ITEMS_PATH.read_text(encoding="utf-8"))
    items = [item for item in all_items if item.get("type") != "derived"]
    ids = [item["id"] for item in items]
    index = {item_id: i for i, item_id in enumerate(ids)}
    by_id = {item["id"]: item for item in items}
    lean_files = sorted(LEAN_ROOT.rglob("*.lean"))

    exact_files: dict[tuple[str, str], list[Path]] = defaultdict(list)
    exact_item_for_file: dict[Path, list[str]] = defaultdict(list)
    for path in lean_files:
        rel = path.relative_to(ROOT)
        chapter = rel.parts[1] if len(rel.parts) > 2 else ""
        exact_files[(chapter, normalized(path.stem))].append(path)
    for item in items:
        parts = item["id"].split("/", 1)
        if len(parts) != 2:
            continue
        for path in exact_files[(parts[0], normalized(parts[1]))]:
            exact_item_for_file[path].append(item["id"])

    def providers(item: dict) -> list[Path]:
        result: set[Path] = set()
        raw_files = item.get("lean_file", [])
        if isinstance(raw_files, str):
            raw_files = [raw_files]
        for raw in raw_files:
            path = ROOT / raw
            if path.exists():
                result.add(path)
        for raw in (item.get("lean_ref") or "", item.get("coverage_note") or ""):
            for found in LEAN_PATH.findall(raw):
                path = LEAN_ROOT / found
                if path.exists():
                    result.add(path)
        parts = item["id"].split("/", 1)
        if len(parts) == 2:
            matches = exact_files[(parts[0], normalized(parts[1]))]
            if len(matches) == 1:
                result.add(matches[0])
        return sorted(result)

    provider_map = {item["id"]: providers(item) for item in items}

    def imported_item_dependencies(provider: Path) -> set[str]:
        """Resolve imports through helper modules to the nearest item providers."""
        result: set[str] = set()
        seen: set[Path] = set()

        def visit(path: Path) -> None:
            if path in seen or not path.exists():
                return
            seen.add(path)
            text = path.read_text(encoding="utf-8")
            for module in IMPORT.findall(text):
                imported = LEAN_ROOT / (module.replace(".", "/") + ".lean")
                mapped = exact_item_for_file.get(imported, [])
                if mapped:
                    result.update(mapped)
                else:
                    visit(imported)

        visit(provider)
        return result

    def primary_provider(item: dict) -> Path | None:
        """The provider whose import closure defines the item-DAG edge set."""
        candidates = provider_map[item["id"]]
        parts = item["id"].split("/", 1)
        if len(parts) == 2:
            exact = exact_files[(parts[0], normalized(parts[1]))]
            for path in exact:
                if path in candidates:
                    return path
        return candidates[0] if candidates else None
    warned = defaultdict(int)
    for match in WARNING.finditer(log):
        warned[match["file"]] += 1

    new_deps: dict[str, list[str]] = {}
    new_stage34 = new_stage35 = 0
    for item in items:
        item_id = item["id"]
        current = item.get("stage3_4")
        if (
            current
            and current.get("status") in {"complete", "import_dag_complete"}
            and not args.regenerate_dependencies
        ):
            deps = list(current.get("actual_internal_dependencies", []))
        else:
            deps_set: set[str] = set()
            primary = primary_provider(item)
            if primary is not None:
                deps_set.update(imported_item_dependencies(primary))
            supplemental_set: set[str] = set()
            for provider in provider_map[item_id]:
                if provider != primary:
                    supplemental_set.update(imported_item_dependencies(provider))
            supplemental_set.discard(item_id)
            supplemental_set.difference_update(deps_set)
            source_refs: set[str] = set()
            source = blob_path(item_id)
            if source is not None:
                for kind, chapter, sec, number in SOURCE_REFERENCE.findall(
                    source.read_text(encoding="utf-8")
                ):
                    label = f"{kind}{chapter}.{sec}" + (f".{number}" if number else "")
                    target = f"Chapter{chapter}/{label}"
                    if target in by_id:
                        source_refs.add(target)
            deps_set.discard(item_id)
            source_refs.discard(item_id)
            deps = sorted(deps_set, key=index.__getitem__)
            forward = [dependency for dependency in deps if index[dependency] > index[item_id]]
            evidence = [str(path.relative_to(ROOT)) for path in provider_map[item_id]]
            item["stage3_4"] = {
                "status": "import_dag_complete",
                "section": section(item_id),
                "verified_on": "2026-08-01",
                "actual_internal_dependencies": deps,
                "forward_internal_dependencies": forward,
                "supplemental_provider_dependencies": sorted(
                    supplemental_set, key=index.__getitem__
                ),
                "explicit_source_references": sorted(source_refs, key=index.__getitem__),
                "basis": (
                    "The primary provider's project imports, resolved recursively through helper "
                    "modules to the nearest item provider, define the item DAG. Dependencies unique "
                    "to supplemental coverage providers and explicit numbered source references are "
                    "recorded separately. Forward DAG edges are retained and flagged. Providers: "
                    + ", ".join(evidence)
                    if evidence
                    else "No dedicated Lean provider or explicit numbered source reference; the item is editorial or its coverage is folded into a neighboring audited provider."
                ),
            }
            new_stage34 += 1
        new_deps[item_id] = deps

        polish = item.get("stage3_5")
        if not (
            polish
            and polish.get("status") in {
                "complete", "diagnostic_pass_complete", "not_applicable"
            }
        ) or args.regenerate_polish:
            evidence = [str(path.relative_to(ROOT)) for path in provider_map[item_id]]
            warning_count = sum(warned[str(path.relative_to(ROOT))] for path in provider_map[item_id])
            item["stage3_5"] = {
                "status": "diagnostic_pass_complete" if evidence else "not_applicable",
                "section": section(item_id),
                "reviewed_on": "2026-08-01",
                "mathlib_quality": "diagnostic_pass_complete" if evidence else "not_applicable",
                "result": (
                    f"Provider batch was rebuilt after the diagnostic-driven deprecation, tactic, and simp cleanup; full build succeeded. This records the repository-wide diagnostic pass, not a proof-by-proof human quality review. {warning_count} warning(s) remain governed by the checked-in ratchet. Providers: "
                    + ", ".join(evidence)
                    if evidence
                    else "No dedicated Lean declaration belongs to this partition item; proof polishing is not applicable."
                ),
            }
            new_stage35 += 1
        if provider_map[item_id] and item.get("status") in {
            "sorry_free", "dependency_trimmed", "proof_polished",
            "diagnostically_polished",
        }:
            item["status"] = "diagnostically_polished"
            item["last_updated"] = "2026-08-01"
        elif not provider_map[item_id] and item.get("status") == "proof_polished":
            item["status"] = "not_applicable"

    # Derived claims are completeness overlays rather than partition items, so
    # they do not belong in the dependency graph.  They do have independent
    # providers, however, and must pass through the same polishing gate.
    for item in (entry for entry in all_items if entry.get("type") == "derived"):
        provider_paths: set[Path] = set()
        for found in LEAN_PATH.findall(item.get("lean_ref") or ""):
            path = LEAN_ROOT / found
            if path.exists():
                provider_paths.add(path)
        evidence = [str(path.relative_to(ROOT)) for path in sorted(provider_paths)]
        warning_count = sum(warned[path] for path in evidence)
        polish = item.get("stage3_5")
        if not (
            polish
            and polish.get("status") in {
                "complete", "diagnostic_pass_complete", "not_applicable"
            }
        ) or args.regenerate_polish:
            item["stage3_5"] = {
                "status": "diagnostic_pass_complete",
                "reviewed_on": "2026-08-01",
                "mathlib_quality": "diagnostic_pass_complete",
                "result": (
                    "Derived-claim provider was rebuilt after the diagnostic-driven "
                    "cleanup; full build succeeded. This records the diagnostic pass, "
                    f"not a proof-by-proof human quality review. {warning_count} warning(s) remain "
                    "governed by the checked-in ratchet. Providers: "
                    + ", ".join(evidence)
                ),
            }
            new_stage35 += 1
        if item.get("status") in {
            "sorry_free", "dependency_trimmed", "proof_polished",
            "diagnostically_polished",
        }:
            item["status"] = "diagnostically_polished"
            item["last_updated"] = "2026-08-01"

    total_edges = sum(map(len, new_deps.values()))
    print(
        f"would add {new_stage34} Stage-3.4 and {new_stage35} Stage-3.5 records; "
        f"dependency graph has {total_edges} direct edge(s)"
    )
    if not args.apply:
        return
    ITEMS_PATH.write_text(json.dumps(all_items, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    DEPS_PATH.write_text(json.dumps(new_deps, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print("updated progress/items.json and dependencies/internal.json")


if __name__ == "__main__":
    main()
