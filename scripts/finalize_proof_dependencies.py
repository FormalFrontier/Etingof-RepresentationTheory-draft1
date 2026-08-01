#!/usr/bin/env python3
"""Finalize Stage 3.4 from imported Lean kernel terms and import evidence.

The Lean extractor reads theorem/opaque bodies with ``allowOpaque := true`` and
emits direct constants from both declaration types and values.  This driver
maps their defining modules to book-item providers, compares them with the
existing conservative import DAG, and writes a source-bound audit certificate.
Run without ``--apply`` first; applying updates only Stage 3.4 metadata and the
dependency graph, never Stage 3.5 proof-quality records.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parent.parent
LEAN_ROOT = ROOT / "EtingofRepresentationTheory"
ITEMS_PATH = ROOT / "progress" / "items.json"
DEPS_PATH = ROOT / "dependencies" / "internal.json"
IMPORT_DAG_PATH = ROOT / "dependencies" / "import-dag-stage3-4-baseline.json"
EVIDENCE_PATH = ROOT / "progress" / "reviews" / "2026-08-01-stage3-4-proof-terms.json"
REPORT_PATH = ROOT / "progress" / "reviews" / "2026-08-01-stage3-4-proof-terms.md"
RAW_ARCHIVE_PATH = ROOT / "progress" / "reviews" / "2026-08-01-stage3-4-proof-terms.tsv.gz"
EXTRACTOR = ROOT / "scripts" / "extract_proof_dependencies.lean"

LEAN_PATH = re.compile(
    r"(?:(?:EtingofRepresentationTheory)/)?(Chapter\d+/[A-Za-z0-9_./-]+\.lean)"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def normalized(value: str) -> str:
    return re.sub(r"[^a-z0-9]", "", value.lower())


def section(item_id: str) -> str | None:
    match = re.match(r"Chapter(\d+)/(.*)", item_id)
    if not match:
        return None
    chapter, tail = match.groups()
    found = re.search(rf"(?<!\d){chapter}[._](\d+)(?:[._]|$)", tail)
    return f"{chapter}.{found.group(1)}" if found else None


def module_for_source(path: Path) -> str:
    return "EtingofRepresentationTheory." + str(
        path.relative_to(LEAN_ROOT).with_suffix("")
    ).replace("/", ".")


GENERATED_PROOF_HELPER = re.compile(
    r"\.(?:_proof_|_simp_)\d+(?:_\d+)*(?:\.|$)"
    r"|\.match_\d+(?:_\d+)*(?:\.|$)"
    r"|\.eq_\d+(?:_\d+)*(?:\.|$)"
    r"|\.congr_simp(?:_\d+)*(?:\.|$)"
)


def is_surface_proof_name(name: str) -> bool:
    """Exclude compiler/elaborator helper theorems while retaining source declarations."""
    return GENERATED_PROOF_HELPER.search(name) is None


def provider_maps(items: list[dict]) -> tuple[dict[str, list[Path]], dict[str, list[str]]]:
    lean_files = sorted(LEAN_ROOT.rglob("*.lean"))
    exact: dict[tuple[str, str], list[Path]] = defaultdict(list)
    for path in lean_files:
        rel = path.relative_to(ROOT)
        chapter = rel.parts[1] if len(rel.parts) > 2 else ""
        exact[(chapter, normalized(path.stem))].append(path)

    by_item: dict[str, list[Path]] = {}
    by_module: dict[str, list[str]] = defaultdict(list)
    for item in items:
        found: set[Path] = set()
        raw_files = item.get("lean_file", [])
        if isinstance(raw_files, str):
            raw_files = [raw_files]
        for raw in raw_files:
            path = ROOT / raw
            if path.exists():
                found.add(path)
        for raw in (item.get("lean_ref") or "", item.get("coverage_note") or ""):
            for match in LEAN_PATH.findall(raw):
                path = LEAN_ROOT / match
                if path.exists():
                    found.add(path)
        parts = item["id"].split("/", 1)
        if len(parts) == 2:
            matches = exact[(parts[0], normalized(parts[1]))]
            if len(matches) == 1:
                found.add(matches[0])
        by_item[item["id"]] = sorted(found)
        for path in found:
            by_module[module_for_source(path)].append(item["id"])
    return by_item, by_module


def expanded_provider_maps(
    items: list[dict],
) -> tuple[dict[str, list[Path]], dict[str, str], dict[str, dict]]:
    """Partition project modules among provider items, expanding re-export hubs.

    Explicit provider files seed the attribution.  A module claimed by several
    items is owned by the item whose id exactly matches its stem when possible.
    Otherwise the earliest ledger claimant wins deterministically.  Previously
    unowned project imports are assigned to the closest seed module that imports
    them transitively.  This makes re-export-only item files review the proofs in
    their implementation submodules without mapping one module to several items.
    """
    seed_by_item, candidates_by_module = provider_maps(items)
    item_index = {item["id"]: position for position, item in enumerate(items)}
    sources = {module_for_source(path): path for path in LEAN_ROOT.rglob("*.lean")}

    owner: dict[str, str] = {}
    attribution: dict[str, dict] = {}
    for module, candidates in candidates_by_module.items():
        path = sources[module]
        exact = [
            item_id for item_id in candidates
            if normalized(item_id.split("/", 1)[-1]) == normalized(path.stem)
        ]
        selected = min(exact or candidates, key=item_index.__getitem__)
        owner[module] = selected
        attribution[module] = {
            "owner": selected,
            "basis": "exact_item_stem" if exact else "explicit_provider_tiebreak",
            "seed_module": module,
            "distance": 0,
            "other_explicit_claimants": sorted(
                set(candidates) - {selected}, key=item_index.__getitem__
            ),
        }

    imports: dict[str, list[str]] = {}
    import_pattern = re.compile(r"^import\s+(EtingofRepresentationTheory(?:\.[A-Za-z0-9_']+)+)\s*$")
    for module, path in sources.items():
        imports[module] = [
            match.group(1)
            for line in path.read_text(encoding="utf-8").splitlines()
            if (match := import_pattern.match(line.strip())) and match.group(1) in sources
        ]

    choices: dict[str, list[tuple[int, int, int, int, str, str]]] = defaultdict(list)
    for seed_module, item_id in owner.items():
        queue = [(dependency, 1) for dependency in imports.get(seed_module, [])]
        seen = {seed_module}
        while queue:
            module, distance = queue.pop(0)
            if module in seen:
                continue
            seen.add(module)
            if module not in owner:
                module_chapter = next(
                    (part for part in module.split(".") if re.fullmatch(r"Chapter\d+", part)),
                    None,
                )
                item_chapter = item_id.split("/", 1)[0]
                choices[module].append((
                    0 if module_chapter is not None and module_chapter == item_chapter else 1,
                    distance,
                    0 if module.startswith(seed_module + "_") else 1,
                    -item_index[item_id],
                    item_id,
                    seed_module,
                ))
            queue.extend((dependency, distance + 1) for dependency in imports.get(module, []))

    for module, candidates in choices.items():
        chapter_penalty, distance, prefix_penalty, _, item_id, seed_module = min(candidates)
        # A chapter-specific implementation module with no same-chapter claimant
        # is shared infrastructure from the item ledger's perspective. Leaving it
        # unowned is more honest than inventing a reversed cross-chapter edge.
        if chapter_penalty != 0:
            continue
        equal_claimants = {
            candidate_item
            for (
                candidate_chapter_penalty,
                candidate_distance,
                candidate_prefix_penalty,
                _,
                candidate_item,
                _,
            ) in candidates
            if candidate_chapter_penalty == chapter_penalty
            and candidate_distance == distance
            and candidate_prefix_penalty == prefix_penalty
        }
        if len(equal_claimants) > 1:
            continue
        owner[module] = item_id
        attribution[module] = {
            "owner": item_id,
            "basis": "closest_transitive_import_of_provider",
            "seed_module": seed_module,
            "distance": distance,
            "other_equal_distance_claimants": [],
        }

    # Review coverage keeps every explicit claimant, while dependency mapping
    # uses the single `owner` above. Thus an overlapping editorial claim is not
    # reported as having zero reviewed proofs, but cannot create duplicate edges.
    by_item: dict[str, list[Path]] = {
        item["id"]: list(seed_by_item[item["id"]]) for item in items
    }
    for module, item_id in owner.items():
        if sources[module] not in by_item[item_id]:
            by_item[item_id].append(sources[module])
    for paths in by_item.values():
        paths.sort()
    return by_item, owner, attribution


def extract(required_modules: list[str], cache: Path | None = None) -> tuple[dict[str, dict], str]:
    command = [
        "lake", "env", "lean", "--run", str(EXTRACTOR.relative_to(ROOT)),
        *required_modules,
    ]
    if cache is not None and cache.exists():
        raw_output = cache.read_text(encoding="utf-8")
    else:
        process = subprocess.run(
            command, cwd=ROOT, text=True, capture_output=True, check=False
        )
        if process.returncode:
            raise SystemExit(
                f"proof-term extractor failed (exit {process.returncode}):\n"
                f"stdout:\n{process.stdout[-4000:]}\nstderr:\n{process.stderr[-4000:]}"
            )
        raw_output = process.stdout
        if cache is not None:
            cache.write_text(raw_output, encoding="utf-8")
    modules: dict[str, dict] = {}
    declarations: dict[str, dict] = {}
    for line_number, raw in enumerate(raw_output.splitlines(), 1):
        fields = raw.split("\t")
        if fields[0] == "M" and len(fields) == 2:
            modules.setdefault(fields[1], {"declarations": []})
        elif fields[0] == "D" and len(fields) == 4:
            _, name, module, kind = fields
            entry = {
                "name": name,
                "kind": kind,
                "type_dependencies": [],
                "proof_dependencies": [],
            }
            declarations[name] = entry
            modules.setdefault(module, {"declarations": []})["declarations"].append(entry)
        elif fields[0] in {"T", "P"} and len(fields) == 4:
            tag, owner, dependency, dep_module = fields
            if owner not in declarations:
                raise SystemExit(f"extractor line {line_number}: dependency before declaration")
            key = "type_dependencies" if tag == "T" else "proof_dependencies"
            declarations[owner][key].append({"name": dependency, "module": dep_module})
        else:
            raise SystemExit(f"unrecognized extractor line {line_number}: {raw!r}")
    for module in modules.values():
        for declaration in module["declarations"]:
            declaration["type_dependencies"].sort(key=lambda value: (value["module"], value["name"]))
            declaration["proof_dependencies"].sort(key=lambda value: (value["module"], value["name"]))
    return modules, raw_output


def find_cycle(graph: dict[str, list[str]]) -> list[str] | None:
    visiting: set[str] = set()
    visited: set[str] = set()

    path: list[str] = []

    def visit(node: str) -> list[str] | None:
        if node in visiting:
            start = path.index(node)
            return path[start:] + [node]
        if node in visited:
            return None
        visiting.add(node)
        path.append(node)
        for dependency in graph.get(node, []):
            if cycle := visit(dependency):
                return cycle
        path.pop()
        visiting.remove(node)
        visited.add(node)
        return None

    for node in graph:
        if cycle := visit(node):
            return cycle
    return None


def cyclic_components(graph: dict[str, list[str]]) -> list[list[str]]:
    """Return the nontrivial strongly connected components of an item relation."""
    index = 0
    indices: dict[str, int] = {}
    lowlinks: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    result: list[list[str]] = []

    def visit(node: str) -> None:
        nonlocal index
        indices[node] = lowlinks[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)
        for dependency in graph.get(node, []):
            if dependency not in indices:
                visit(dependency)
                lowlinks[node] = min(lowlinks[node], lowlinks[dependency])
            elif dependency in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[dependency])
        if lowlinks[node] != indices[node]:
            return
        component: list[str] = []
        while True:
            member = stack.pop()
            on_stack.remove(member)
            component.append(member)
            if member == node:
                break
        if len(component) > 1 or node in graph.get(node, []):
            result.append(sorted(component))

    for node in graph:
        if node not in indices:
            visit(node)
    return sorted(result)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-log", required=True, type=Path)
    parser.add_argument(
        "--raw-extraction-cache", type=Path,
        help="reuse/write the exact extractor TSV (use only with the same built tree)",
    )
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    log = args.build_log.read_text(encoding="utf-8", errors="replace")
    if "Build completed successfully" not in log or "error: build failed" in log:
        raise SystemExit("refusing to finalize from an unsuccessful full build")

    all_items = json.loads(ITEMS_PATH.read_text(encoding="utf-8"))
    items = [item for item in all_items if item.get("type") != "derived"]
    item_index = {item["id"]: position for position, item in enumerate(items)}
    provider_by_item, module_owner, module_attribution = expanded_provider_maps(items)
    import_graph = json.loads(IMPORT_DAG_PATH.read_text(encoding="utf-8"))
    required_modules = sorted({
        module_for_source(path) for paths in provider_by_item.values() for path in paths
    })
    modules, raw_extraction = extract(required_modules, args.raw_extraction_cache)

    source_by_module = {module_for_source(path): path for path in LEAN_ROOT.rglob("*.lean")}
    source_by_module["EtingofRepresentationTheory"] = ROOT / "EtingofRepresentationTheory.lean"
    missing_provider_modules = sorted(
        {module_for_source(path) for paths in provider_by_item.values() for path in paths} - modules.keys()
    )
    if missing_provider_modules:
        raise SystemExit("provider modules absent from root proof environment: " + ", ".join(missing_provider_modules))

    module_summaries: dict[str, dict] = {}
    for module, data in sorted(modules.items()):
        source = source_by_module.get(module)
        if source is None:
            # Ignore stale imported oleans with no current source, but expose them below.
            continue
        proof_modules = sorted({
            dep["module"]
            for declaration in data["declarations"]
            for dep in declaration["proof_dependencies"]
            if dep["module"] != module
        })
        type_modules = sorted({
            dep["module"]
            for declaration in data["declarations"]
            for dep in declaration["type_dependencies"]
            if dep["module"] != module
        })
        proof_declarations = [
            {
                "name": declaration["name"],
                "kind": declaration["kind"],
                "type_dependencies": [
                    dependency for dependency in declaration["type_dependencies"]
                    if dependency["module"] != module
                ],
                "proof_dependencies": [
                    dependency for dependency in declaration["proof_dependencies"]
                    if dependency["module"] != module
                ],
            }
            for declaration in data["declarations"]
            if declaration["kind"] in {"theorem", "opaque"}
            and is_surface_proof_name(declaration["name"])
        ]
        supporting_declarations = [
            {
                "name": declaration["name"],
                "kind": declaration["kind"],
                "type_dependencies": [
                    dependency for dependency in declaration["type_dependencies"]
                    if dependency["module"] != module
                ],
                "proof_dependencies": [
                    dependency for dependency in declaration["proof_dependencies"]
                    if dependency["module"] != module
                ],
            }
            for declaration in data["declarations"]
            if declaration["kind"] not in {"theorem", "opaque"}
            and any(
                dependency["module"] != module
                for dependency in declaration["type_dependencies"]
                + declaration["proof_dependencies"]
            )
        ]
        module_summaries[module] = {
            "source": str(source.relative_to(ROOT)),
            "source_sha256": sha256(source),
            "declaration_count": len(data["declarations"]),
            "kernel_proof_declaration_count": sum(
                declaration["kind"] in {"theorem", "opaque"}
                for declaration in data["declarations"]
            ),
            "proof_declaration_count": len(proof_declarations),
            "proof_dependency_modules": proof_modules,
            "type_dependency_modules": type_modules,
            "proof_declarations": proof_declarations,
            "cross_module_supporting_declarations": supporting_declarations,
        }

    proof_union_graph: dict[str, list[str]] = {}
    proof_graph: dict[str, list[str]] = {}
    unsupported_import_edge_records: list[dict[str, str]] = []
    proof_only_edges = 0
    unsupported_import_edges = 0
    for item in items:
        item_id = item["id"]
        own_modules = {module_for_source(path) for path in provider_by_item[item_id]}
        proof_modules: set[str] = set()
        type_modules: set[str] = set()
        declaration_count = 0
        for module in own_modules:
            summary = module_summaries[module]
            proof_modules.update(summary["proof_dependency_modules"])
            type_modules.update(summary["type_dependency_modules"])
            declaration_count += summary["declaration_count"]
        mapped: set[str] = set()
        for module in proof_modules | type_modules:
            if owner := module_owner.get(module):
                mapped.add(owner)
        mapped.discard(item_id)
        import_deps = set(import_graph[item_id])
        proof_only_edges += len(mapped - import_deps)
        unsupported_import_edges += len(import_deps - mapped)
        unsupported_import_edge_records.extend(
            {"item": item_id, "dependency": dependency}
            for dependency in sorted(import_deps - mapped, key=item_index.__getitem__)
        )
        deps = sorted(import_deps | mapped, key=item_index.__getitem__)
        proof_union_graph[item_id] = deps
        proof_graph[item_id] = sorted(mapped, key=item_index.__getitem__)
        previous_stage3_4 = item.get("stage3_4") or {}
        item["stage3_4"] = {
            **{
                key: previous_stage3_4[key]
                for key in ("supplemental_provider_dependencies", "explicit_source_references")
                if key in previous_stage3_4
            },
            "status": "complete",
            "section": section(item_id),
            "verified_on": "2026-08-01",
            "actual_internal_dependencies": [],
            "forward_internal_dependencies": [
                dep for dep in import_deps if item_index[dep] > item_index[item_id]
            ],
            "import_dag_dependencies": sorted(import_deps, key=item_index.__getitem__),
            "proof_term_dependencies": sorted(mapped, key=item_index.__getitem__),
            "provider_module_attribution": {
                module: module_attribution[module] for module in sorted(own_modules)
            },
            "proof_dependency_modules": sorted(proof_modules - own_modules),
            "type_dependency_modules": sorted(type_modules - own_modules),
            "declarations_reviewed": declaration_count,
            "evidence": str(EVIDENCE_PATH.relative_to(ROOT)),
            "basis": (
                "Direct constants were collected from imported kernel declaration types and "
                "proof/opaque bodies using ConstantInfo.value? (allowOpaque := true). Re-export "
                "implementation modules were attributed to one closest provider item. The shipped "
                "item graph is the maximal deterministic acyclic subset of mapped kernel edges; "
                "any cycle-excluded association is retained explicitly in the evidence."
                if own_modules else
                "No dedicated Lean provider belongs to this editorial/folded partition item."
            ),
        }
        if own_modules and item.get("status") in {"sorry_free", "dependency_trimmed"}:
            item["status"] = "dependency_trimmed"
            item["last_updated"] = "2026-08-01"

    for item in all_items:
        if item.get("type") != "derived":
            continue
        raw_files = item.get("lean_file") or []
        if isinstance(raw_files, str):
            raw_files = [raw_files]
        paths = {
            LEAN_ROOT / match
            for match in LEAN_PATH.findall(item.get("lean_ref") or "")
            if (LEAN_ROOT / match).exists()
        }
        paths.update(ROOT / raw for raw in raw_files if (ROOT / raw).exists())
        own_modules = sorted(module_for_source(path) for path in paths)
        if not own_modules:
            raise SystemExit(f"derived item {item['derived_from']} has no resolvable provider module")
        item["stage3_4"] = {
            "status": "complete",
            "verified_on": "2026-08-01",
            "provider_modules": own_modules,
            "declarations_reviewed": sum(
                module_summaries[module]["declaration_count"] for module in own_modules
            ),
            "evidence": str(EVIDENCE_PATH.relative_to(ROOT)),
            "basis": (
                "Derived claims are overlays keyed by `derived_from`, not graph nodes. Their "
                "provider modules and kernel proof terms were reviewed in the same certificate; "
                "their item dependencies are represented by the parent partition item."
            ),
        }
        if item.get("status") in {
            "dependency_trimmed", "diagnostically_polished", "sorry_free", "proof_polished"
        }:
            item["status"] = "dependency_trimmed"
        item["last_updated"] = "2026-08-01"

    # Item grouping can still coarsen an acyclic module graph into a cycle.  Ship
    # the maximal deterministic acyclic subset of *proof-supported* edges and
    # retain every excluded edge explicitly. Import-supported edges are tried
    # first, then backward/book-order edges, so the choice is reproducible rather
    # than a hidden cycle break.
    item_level_cyclic_components = cyclic_components(proof_graph)
    graph: dict[str, list[str]] = {item["id"]: [] for item in items}
    excluded_cycle_edges: list[dict] = []
    candidate_edges = [
        (item_id, dependency)
        for item_id, dependencies in proof_graph.items()
        for dependency in dependencies
    ]
    candidate_edges.sort(key=lambda edge: (
        edge[1] not in import_graph[edge[0]],
        item_index[edge[1]] > item_index[edge[0]],
        item_index[edge[0]],
        item_index[edge[1]],
    ))
    for item_id, dependency in candidate_edges:
        graph[item_id].append(dependency)
        if cycle := find_cycle(graph):
            graph[item_id].remove(dependency)
            excluded_cycle_edges.append({
                "item": item_id,
                "dependency": dependency,
                "cycle": cycle,
            })
    for item_id, dependencies in graph.items():
        dependencies.sort(key=item_index.__getitem__)
        stage = next(item for item in items if item["id"] == item_id)["stage3_4"]
        stage["actual_internal_dependencies"] = dependencies
        stage["forward_internal_dependencies"] = [
            dependency for dependency in dependencies
            if item_index[dependency] > item_index[item_id]
        ]
        stage["cyclic_proof_term_dependencies_excluded_from_dag"] = [
            edge["dependency"] for edge in excluded_cycle_edges if edge["item"] == item_id
        ]
    if cycle := find_cycle(graph):
        raise SystemExit("selected proof-term graph unexpectedly contains a cycle: " + " -> ".join(cycle))

    stale_modules = sorted(set(modules) - set(source_by_module))
    modules_without_item_owner = sorted(set(module_summaries) - set(module_owner))
    unimported_sources = sorted(
        str(path.relative_to(ROOT))
        for module, path in source_by_module.items()
        if module not in modules
    )
    evidence = {
        "generated_on": "2026-08-01",
        "method": "Lean imported kernel terms with allowOpaque := true; maximal acyclic item projection",
        "source_proof_inventory_policy": (
            "Conservative source-facing theorem/opaque inventory: private declarations are retained; "
            "only anchored compiler-helper name forms are excluded. The inventory may retain other "
            "generated declarations, so it is a coverage superset rather than an exact syntax count."
        ),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "extractor_sha256": sha256(EXTRACTOR),
        "build_log_sha256": hashlib.sha256(log.encode()).hexdigest(),
        "import_dag_baseline": str(IMPORT_DAG_PATH.relative_to(ROOT)),
        "import_dag_baseline_sha256": sha256(IMPORT_DAG_PATH),
        "raw_extraction_sha256": hashlib.sha256(raw_extraction.encode()).hexdigest(),
        "raw_extraction_archive": str(RAW_ARCHIVE_PATH.relative_to(ROOT)),
        "module_count": len(module_summaries),
        "declaration_count": sum(value["declaration_count"] for value in module_summaries.values()),
        "proof_declaration_count": sum(
            value["proof_declaration_count"] for value in module_summaries.values()
        ),
        "kernel_proof_declaration_count": sum(
            value["kernel_proof_declaration_count"] for value in module_summaries.values()
        ),
        "proof_only_item_edges_added_to_import_dag": proof_only_edges,
        "import_edges_without_kernel_proof_or_type_support": unsupported_import_edges,
        "import_edges_without_mapped_owned_module_support": unsupported_import_edge_records,
        "proof_union_item_edge_count": sum(map(len, proof_union_graph.values())),
        "proof_union_item_level_cyclic_components": item_level_cyclic_components,
        "proof_term_cycle_edges_excluded_from_shipped_dag": excluded_cycle_edges,
        "shipped_item_edge_count": sum(map(len, graph.values())),
        "graph_policy": (
            "dependencies/internal.json is the maximal deterministic acyclic subset of mapped "
            "kernel proof/type edges. Import edges without kernel support are trimmed; proof edges "
            "excluded solely to avoid item-coarsening cycles are listed explicitly."
        ),
        "module_attribution": module_attribution,
        "modules_without_item_owner": modules_without_item_owner,
        "stale_imported_modules_without_source": stale_modules,
        "current_sources_absent_from_root_import": unimported_sources,
        "modules": module_summaries,
    }
    print(
        f"kernel review: {evidence['declaration_count']} declarations in "
        f"{evidence['module_count']} current root-imported modules; "
        f"{proof_only_edges} proof/type-mapped edge(s) beyond and {unsupported_import_edges} unsupported edge(s) in "
        f"the {sum(map(len, import_graph.values()))}-edge import DAG; proof relation has "
        f"{sum(map(len, proof_graph.values()))} edge(s), {len(item_level_cyclic_components)} cyclic component(s), "
        f"and {len(excluded_cycle_edges)} excluded cycle edge(s); shipped proof DAG has "
        f"{sum(map(len, graph.values()))} edge(s)"
    )
    print(f"unimported current sources: {len(unimported_sources)}; stale imported modules: {len(stale_modules)}")
    if not args.apply:
        return

    ITEMS_PATH.write_text(json.dumps(all_items, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    DEPS_PATH.write_text(json.dumps(graph, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    EVIDENCE_PATH.write_text(json.dumps(evidence, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    RAW_ARCHIVE_PATH.write_bytes(gzip.compress(raw_extraction.encode(), compresslevel=9, mtime=0))
    REPORT_PATH.write_text(
        "# Stage 3.4 kernel proof-term review\n\n"
        "Completed 2026-08-01 using imported Lean kernel terms with opaque/theorem bodies enabled.\n\n"
        f"- Current root-imported modules: {evidence['module_count']}\n"
        f"- Declarations inspected: {evidence['declaration_count']}\n"
        f"- Import-DAG edges: {sum(map(len, import_graph.values()))}\n"
        f"- Mapped proof/type edges beyond the old import DAG: {proof_only_edges}\n"
        f"- Old import edges not recovered through owned-module proof/type mapping (trimmed): {unsupported_import_edges}\n"
        f"- Mapped proof/type relation edges: {sum(map(len, proof_graph.values()))}\n"
        f"- Cyclic item components in that relation: {len(item_level_cyclic_components)}\n"
        f"- Explicitly recorded cycle edges excluded from the DAG: {len(excluded_cycle_edges)}\n"
        f"- Shipped acyclic proof-term edges: {sum(map(len, graph.values()))}\n"
        f"- Current sources outside the root import: {len(unimported_sources)}\n"
        f"- Stale imported modules without source: {len(stale_modules)}\n\n"
        "The JSON companion conservatively covers every source-level theorem/opaque declaration and its "
        "direct cross-module "
        "project-local type and proof-body constants, plus every other declaration that contributes "
        "a cross-module edge and the source, extractor, toolchain, raw-extraction, and build-log "
        "identity. Re-export implementation modules are attributed to the closest unambiguous explicit "
        f"provider item; {len(modules_without_item_owner)} root-imported modules without an unambiguous "
        "item owner remain in the declaration inventory but are not projected into the item graph. "
        "The shipped graph trims import edges not recovered through owned-module kernel mapping "
        "and includes every mapped "
        "proof edge compatible with acyclicity; each edge excluded for an item-coarsening cycle is "
        "named with its cycle path in the certificate.\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
