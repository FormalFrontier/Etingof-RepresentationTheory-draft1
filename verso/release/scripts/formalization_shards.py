#!/usr/bin/env python3
# Copyright (c) 2026 American Mathematical Society. All rights reserved.
"""Plan, package, merge, and verify sharded Lean build artifacts.

This tool is intentionally dependency-free.  It models the public
``RepresentationTheory`` library as the imports of ``RepresentationTheory.lean``.
Every direct import is owned by exactly one shard; a shard may build additional
transitive dependencies, but ``extract`` packages only its owned modules.  The
merged payload therefore has one authoritative producer for each library
module.  The umbrella module is deliberately built only after the merge.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Iterable


SCHEMA = 1
ALGORITHM = "closure-source-byte-greedy-v1"
PACKAGE = "RepresentationTheoryFormalization"
MODULE_PREFIX = "RepresentationTheory"
UMBRELLA = "RepresentationTheory"
MODULE_RE = re.compile(r"^RepresentationTheory(?:\.[A-Za-z][A-Za-z0-9_]*)+$")
IMPORT_RE = re.compile(
    r"^\s*import\s+(RepresentationTheory(?:\.[A-Za-z][A-Za-z0-9_]*)+)\s*$",
    re.MULTILINE,
)


class ShardError(RuntimeError):
    """A plan or payload violates the artifact protocol."""


def fail(message: str) -> None:
    raise ShardError(message)


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_json(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode("utf-8")


def require_directory(path: Path, label: str) -> None:
    if not path.is_dir():
        fail(f"{label} is not a directory: {path}")


def require_empty_directory(path: Path, label: str) -> None:
    if path.exists():
        if not path.is_dir():
            fail(f"{label} is not a directory: {path}")
        if any(path.iterdir()):
            fail(f"{label} must be empty: {path}")
    else:
        path.mkdir(parents=True)


def check_module(module: str) -> None:
    if not MODULE_RE.fullmatch(module):
        fail(f"invalid RepresentationTheory module name: {module!r}")


def source_path(package_root: Path, module: str) -> Path:
    check_module(module)
    relative = Path(*module.split(".")).with_suffix(".lean")
    path = package_root / relative
    if not path.is_file() or path.is_symlink():
        fail(f"module source is missing or not a regular file: {module}")
    return path


def parse_imports(path: Path, *, require_nonempty: bool) -> list[str]:
    if not path.is_file() or path.is_symlink():
        fail(f"umbrella source is missing or not regular: {path}")
    modules = IMPORT_RE.findall(path.read_text(encoding="utf-8"))
    if require_nonempty and not modules:
        fail(f"no {MODULE_PREFIX} imports found in {path}")
    if len(modules) != len(set(modules)):
        duplicates = sorted({m for m in modules if modules.count(m) > 1})
        fail(f"duplicate umbrella imports: {duplicates[:5]}")
    for module in modules:
        check_module(module)
    return modules


def all_source_modules(package_root: Path) -> set[str]:
    root = package_root / MODULE_PREFIX
    require_directory(root, f"{MODULE_PREFIX} source root")
    modules: set[str] = set()
    for path in root.rglob("*.lean"):
        if path.is_symlink() or not path.is_file():
            fail(f"non-regular Lean source: {path}")
        module = path.relative_to(package_root).with_suffix("").as_posix().replace("/", ".")
        check_module(module)
        modules.add(module)
    return modules


@dataclass(frozen=True)
class SourceModel:
    package_root: Path
    modules: tuple[str, ...]
    index: dict[str, int]
    weights: dict[str, int]
    dependencies: dict[str, tuple[str, ...]]
    closures: dict[str, frozenset[str]]
    umbrella_sha256: str
    source_fingerprint: str


def load_source_model(package_root: Path) -> SourceModel:
    require_directory(package_root, "package root")
    umbrella_path = package_root / f"{UMBRELLA}.lean"
    modules = tuple(parse_imports(umbrella_path, require_nonempty=True))
    imported = set(modules)
    actual = all_source_modules(package_root)
    if imported != actual:
        missing = sorted(actual - imported)
        unknown = sorted(imported - actual)
        fail(
            "umbrella import set does not equal source-module set; "
            f"unimported={missing[:5]}, missing_source={unknown[:5]}"
        )
    index = {module: position for position, module in enumerate(modules)}
    weights = {module: source_path(package_root, module).stat().st_size for module in modules}
    dependencies: dict[str, tuple[str, ...]] = {}
    for module in modules:
        local = tuple(
            dep
            for dep in parse_imports(source_path(package_root, module), require_nonempty=False)
            if dep in imported
        )
        dependencies[module] = local

    closures: dict[str, frozenset[str]] = {}

    def closure(module: str, stack: tuple[str, ...] = ()) -> frozenset[str]:
        cached = closures.get(module)
        if cached is not None:
            return cached
        if module in stack:
            fail("local RepresentationTheory import cycle: " + " -> ".join((*stack, module)))
        result = {module}
        for dependency in dependencies[module]:
            result.update(closure(dependency, (*stack, module)))
        frozen = frozenset(result)
        closures[module] = frozen
        return frozen

    for module in modules:
        closure(module)

    fingerprint = hashlib.sha256()
    for module in (UMBRELLA, *modules):
        path = umbrella_path if module == UMBRELLA else source_path(package_root, module)
        fingerprint.update(module.encode("utf-8"))
        fingerprint.update(b"\0")
        fingerprint.update(path.read_bytes())
        fingerprint.update(b"\0")
    return SourceModel(
        package_root=package_root,
        modules=modules,
        index=index,
        weights=weights,
        dependencies=dependencies,
        closures=closures,
        umbrella_sha256=sha256_file(umbrella_path),
        source_fingerprint=fingerprint.hexdigest(),
    )


def closure_weight(model: SourceModel, modules: Iterable[str]) -> int:
    return sum(model.weights[module] for module in modules)


def make_plan(model: SourceModel, shards: int) -> dict[str, Any]:
    if shards < 1:
        fail("--shards must be positive")
    assignments: list[set[str]] = [set() for _ in range(shards)]
    closures: list[set[str]] = [set() for _ in range(shards)]
    order = sorted(
        model.modules,
        key=lambda module: (-closure_weight(model, model.closures[module]), model.index[module]),
    )
    for module in order:
        chosen = min(
            range(shards),
            key=lambda shard: (closure_weight(model, closures[shard] | model.closures[module]), shard),
        )
        assignments[chosen].add(module)
        closures[chosen].update(model.closures[module])
    shard_entries: list[dict[str, Any]] = []
    for shard, members in enumerate(assignments, start=1):
        targets = [module for module in model.modules if module in members]
        target_text = "".join(f"@{PACKAGE}/+{module}\n" for module in targets)
        shard_entries.append(
            {
                "index": shard,
                "targets": targets,
                "target_count": len(targets),
                "requested_source_bytes": closure_weight(model, targets),
                "closure_module_count": len(closures[shard - 1]),
                "closure_source_bytes": closure_weight(model, closures[shard - 1]),
                "target_list_sha256": sha256_bytes(target_text.encode("utf-8")),
            }
        )
    plan = {
        "schema": SCHEMA,
        "algorithm": ALGORITHM,
        "package": PACKAGE,
        "module_prefix": MODULE_PREFIX,
        "umbrella_module": UMBRELLA,
        "umbrella_sha256": model.umbrella_sha256,
        "source_fingerprint": model.source_fingerprint,
        "module_count": len(model.modules),
        "modules": list(model.modules),
        "shards": shard_entries,
    }
    validate_plan(plan)
    return plan


def target_lines(plan: dict[str, Any], shard: int) -> list[str]:
    entry = shard_entry(plan, shard)
    lines = [f"@{PACKAGE}/+{module}" for module in entry["targets"]]
    expected = sha256_bytes(("\n".join(lines) + "\n").encode("utf-8"))
    if entry["target_list_sha256"] != expected:
        fail(f"plan target-list digest mismatch for shard {shard}")
    return lines


def shard_entry(plan: dict[str, Any], shard: int) -> dict[str, Any]:
    if not isinstance(shard, int) or shard < 1:
        fail(f"invalid shard index: {shard!r}")
    entries = plan["shards"]
    if shard > len(entries):
        fail(f"shard {shard} is outside 1..{len(entries)}")
    entry = entries[shard - 1]
    if entry.get("index") != shard:
        fail("plan shards are not contiguous and ordered")
    return entry


def validate_plan(plan: Any) -> None:
    if not isinstance(plan, dict):
        fail("plan must be a JSON object")
    required = {"schema", "algorithm", "package", "module_prefix", "umbrella_module", "umbrella_sha256", "source_fingerprint", "module_count", "modules", "shards"}
    if set(plan) != required:
        fail(f"unexpected plan fields: {sorted(set(plan) ^ required)}")
    if plan["schema"] != SCHEMA or plan["algorithm"] != ALGORITHM:
        fail("unsupported plan schema or algorithm")
    if plan["package"] != PACKAGE or plan["module_prefix"] != MODULE_PREFIX or plan["umbrella_module"] != UMBRELLA:
        fail("plan is for a different package")
    if not isinstance(plan["umbrella_sha256"], str) or not re.fullmatch(r"[0-9a-f]{64}", plan["umbrella_sha256"]):
        fail("invalid umbrella SHA-256")
    if not isinstance(plan["source_fingerprint"], str) or not re.fullmatch(r"[0-9a-f]{64}", plan["source_fingerprint"]):
        fail("invalid source fingerprint")
    modules = plan["modules"]
    if not isinstance(modules, list) or not modules or any(not isinstance(module, str) for module in modules):
        fail("invalid plan modules")
    for module in modules:
        check_module(module)
    if len(modules) != len(set(modules)) or plan["module_count"] != len(modules):
        fail("plan module count or uniqueness is invalid")
    shards = plan["shards"]
    if not isinstance(shards, list) or not shards:
        fail("plan has no shards")
    owned: list[str] = []
    for position, entry in enumerate(shards, start=1):
        if not isinstance(entry, dict):
            fail("invalid shard entry")
        expected_fields = {"index", "targets", "target_count", "requested_source_bytes", "closure_module_count", "closure_source_bytes", "target_list_sha256"}
        if set(entry) != expected_fields or entry["index"] != position:
            fail("invalid shard fields or ordering")
        targets = entry["targets"]
        if not isinstance(targets, list) or not targets or any(not isinstance(target, str) for target in targets):
            fail("invalid shard targets")
        if len(targets) != len(set(targets)) or entry["target_count"] != len(targets):
            fail("invalid shard target count or uniqueness")
        for target in targets:
            check_module(target)
        if any(target not in modules for target in targets):
            fail("shard contains a module outside the plan")
        if any(not isinstance(entry[key], int) or entry[key] < 0 for key in ("requested_source_bytes", "closure_module_count", "closure_source_bytes")):
            fail("invalid shard metrics")
        if not isinstance(entry["target_list_sha256"], str) or not re.fullmatch(r"[0-9a-f]{64}", entry["target_list_sha256"]):
            fail("invalid target-list digest")
        owned.extend(targets)
    if owned != [module for entry in shards for module in entry["targets"]]:
        fail("unreachable plan validation error")
    if len(owned) != len(set(owned)) or set(owned) != set(modules):
        fail("shards do not partition the module set exactly")
    for shard in range(1, len(shards) + 1):
        target_lines(plan, shard)


def read_plan(path: Path) -> tuple[dict[str, Any], bytes]:
    if not path.is_file() or path.is_symlink():
        fail(f"plan is not a regular file: {path}")
    raw = path.read_bytes()
    try:
        plan = json.loads(raw)
    except json.JSONDecodeError as error:
        fail(f"invalid plan JSON: {error}")
    validate_plan(plan)
    if canonical_json(plan) != raw:
        fail("plan JSON is not canonical")
    return plan, raw


def assert_plan_matches_source(plan: dict[str, Any], package_root: Path) -> SourceModel:
    model = load_source_model(package_root)
    if list(model.modules) != plan["modules"]:
        fail("plan modules do not match current umbrella import order")
    if model.umbrella_sha256 != plan["umbrella_sha256"] or model.source_fingerprint != plan["source_fingerprint"]:
        fail("plan fingerprint does not match current package source")
    return model


def module_artifact_paths(module: str) -> tuple[PurePosixPath, ...]:
    if module != UMBRELLA:
        check_module(module)
    relative = PurePosixPath(*module.split("."))
    return (
        PurePosixPath("lib", "lean") / relative.with_suffix(".olean"),
        PurePosixPath("lib", "lean") / relative.with_suffix(".ilean"),
        PurePosixPath("lib", "lean") / relative.with_suffix(".olean.hash"),
        PurePosixPath("lib", "lean") / relative.with_suffix(".ilean.hash"),
        PurePosixPath("lib", "lean") / relative.with_suffix(".trace"),
        PurePosixPath("ir") / relative.with_suffix(".c"),
        PurePosixPath("ir") / relative.with_suffix(".c.hash"),
        PurePosixPath("ir") / relative.with_suffix(".setup.json"),
    )


def safe_build_file(build_root: Path, relative: PurePosixPath) -> Path:
    if relative.is_absolute() or ".." in relative.parts:
        fail(f"unsafe artifact path: {relative}")
    path = build_root.joinpath(*relative.parts)
    if not path.is_file() or path.is_symlink():
        fail(f"missing or non-regular artifact: {path}")
    return path


def write_plan_output(plan: dict[str, Any], output: Path) -> None:
    require_empty_directory(output, "plan output")
    (output / "plan.json").write_bytes(canonical_json(plan))
    for shard in range(1, len(plan["shards"]) + 1):
        (output / f"shard-{shard}.targets").write_text("\n".join(target_lines(plan, shard)) + "\n", encoding="utf-8")


def cmd_plan(args: argparse.Namespace) -> None:
    model = load_source_model(args.package_root)
    plan = make_plan(model, args.shards)
    write_plan_output(plan, args.output)
    print(json.dumps({"plan": str(args.output / "plan.json"), "module_count": plan["module_count"], "shards": len(plan["shards"]), "source_fingerprint": plan["source_fingerprint"]}, sort_keys=True))


def cmd_targets(args: argparse.Namespace) -> None:
    plan, _ = read_plan(args.plan)
    if args.package_root is not None:
        assert_plan_matches_source(plan, args.package_root)
    print("\n".join(target_lines(plan, args.shard)))


def cmd_extract(args: argparse.Namespace) -> None:
    plan, raw_plan = read_plan(args.plan)
    assert_plan_matches_source(plan, args.package_root)
    entry = shard_entry(plan, args.shard)
    require_directory(args.build_root, "build root")
    require_empty_directory(args.output, "extract output")
    payload_build = args.output / "build"
    files: list[dict[str, Any]] = []
    for module in entry["targets"]:
        for relative in module_artifact_paths(module):
            source = safe_build_file(args.build_root, relative)
            destination = payload_build.joinpath(*relative.parts)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
            files.append({"path": relative.as_posix(), "sha256": sha256_file(source), "size": source.stat().st_size})
    files.sort(key=lambda item: item["path"])
    expected = len(entry["targets"]) * len(module_artifact_paths(UMBRELLA))
    if len(files) != expected or len({item["path"] for item in files}) != len(files):
        fail("extract did not produce the exact expected artifact set")
    payload = {
        "schema": SCHEMA,
        "plan_sha256": sha256_bytes(raw_plan),
        "source_fingerprint": plan["source_fingerprint"],
        "shard": args.shard,
        "targets": entry["targets"],
        "files": files,
    }
    (args.output / "plan.json").write_bytes(raw_plan)
    (args.output / "payload.json").write_bytes(canonical_json(payload))
    print(json.dumps({"output": str(args.output), "shard": args.shard, "targets": len(entry["targets"]), "artifacts": len(files)}, sort_keys=True))


def read_payload(path: Path, plan: dict[str, Any], raw_plan: bytes) -> tuple[dict[str, Any], Path]:
    require_directory(path, "payload directory")
    plan_path = path / "plan.json"
    payload_path = path / "payload.json"
    if not plan_path.is_file() or plan_path.is_symlink() or plan_path.read_bytes() != raw_plan:
        fail(f"payload has a different plan: {path}")
    if not payload_path.is_file() or payload_path.is_symlink():
        fail(f"payload metadata is missing: {path}")
    raw_payload = payload_path.read_bytes()
    try:
        payload = json.loads(raw_payload)
    except json.JSONDecodeError as error:
        fail(f"invalid payload JSON in {path}: {error}")
    if canonical_json(payload) != raw_payload:
        fail(f"payload JSON is not canonical: {path}")
    expected_fields = {"schema", "plan_sha256", "source_fingerprint", "shard", "targets", "files"}
    if not isinstance(payload, dict) or set(payload) != expected_fields or payload.get("schema") != SCHEMA:
        fail(f"invalid payload fields: {path}")
    if payload["plan_sha256"] != sha256_bytes(raw_plan) or payload["source_fingerprint"] != plan["source_fingerprint"]:
        fail(f"payload fingerprint mismatch: {path}")
    if not isinstance(payload["shard"], int):
        fail(f"invalid payload shard: {path}")
    entry = shard_entry(plan, payload["shard"])
    if payload["targets"] != entry["targets"]:
        fail(f"payload targets do not match plan: {path}")
    expected_paths = sorted(
        relative.as_posix() for module in entry["targets"] for relative in module_artifact_paths(module)
    )
    files = payload["files"]
    if not isinstance(files, list) or len(files) != len(expected_paths):
        fail(f"payload artifact count does not match owning targets: {path}")
    observed: list[str] = []
    for item in files:
        if not isinstance(item, dict) or set(item) != {"path", "sha256", "size"}:
            fail(f"invalid payload artifact entry: {path}")
        rel = item["path"]
        if not isinstance(rel, str) or not isinstance(item["sha256"], str) or not isinstance(item["size"], int):
            fail(f"invalid payload artifact types: {path}")
        parsed = PurePosixPath(rel)
        if parsed.is_absolute() or ".." in parsed.parts or rel != parsed.as_posix() or not re.fullmatch(r"[0-9a-f]{64}", item["sha256"]):
            fail(f"unsafe payload artifact path: {rel!r}")
        observed.append(rel)
    if observed != sorted(observed) or observed != expected_paths:
        fail(f"payload does not contain exactly its owning module artifacts: {path}")
    build = path / "build"
    require_directory(build, "payload build directory")
    actual_paths = sorted(candidate.relative_to(build).as_posix() for candidate in build.rglob("*") if candidate.is_file())
    if actual_paths != expected_paths:
        fail(f"payload build directory has missing or unexpected artifacts: {path}")
    for item in files:
        source = safe_build_file(build, PurePosixPath(item["path"]))
        if source.stat().st_size != item["size"] or sha256_file(source) != item["sha256"]:
            fail(f"payload artifact digest mismatch: {source}")
    return payload, build


def cmd_merge(args: argparse.Namespace) -> None:
    plan, raw_plan = read_plan(args.plan)
    if args.package_root is not None:
        assert_plan_matches_source(plan, args.package_root)
    require_empty_directory(args.output, "merge output")
    if len(args.payload) != len(plan["shards"]):
        fail(f"merge requires exactly {len(plan['shards'])} payload directories")
    loaded = [read_payload(path, plan, raw_plan) for path in args.payload]
    payloads = [pair[0] for pair in loaded]
    shards = [payload["shard"] for payload in payloads]
    if sorted(shards) != list(range(1, len(plan["shards"]) + 1)):
        fail("payloads must contain every shard exactly once")
    merged = args.output / "build"
    copied = 0
    collisions = 0
    for payload, source_root in sorted(loaded, key=lambda pair: pair[0]["shard"]):
        for item in payload["files"]:
            relative = PurePosixPath(item["path"])
            source = safe_build_file(source_root, relative)
            destination = merged.joinpath(*relative.parts)
            if destination.exists():
                if not destination.is_file() or destination.is_symlink() or sha256_file(destination) != item["sha256"]:
                    fail(f"conflicting artifact collision: {relative}")
                collisions += 1
                continue
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
            copied += 1
    expected_files = len(plan["modules"]) * len(module_artifact_paths(UMBRELLA))
    if copied != expected_files or collisions:
        fail(f"merged artifact count is wrong: copied={copied}, expected={expected_files}, collisions={collisions}")
    merged_metadata = {
        "schema": SCHEMA,
        "plan_sha256": sha256_bytes(raw_plan),
        "source_fingerprint": plan["source_fingerprint"],
        "shards": sorted(shards),
        "artifacts": copied,
    }
    (args.output / "plan.json").write_bytes(raw_plan)
    (args.output / "merged.json").write_bytes(canonical_json(merged_metadata))
    print(json.dumps({"output": str(args.output), "artifacts": copied, "shards": len(shards)}, sort_keys=True))


def cmd_verify(args: argparse.Namespace) -> None:
    plan, _ = read_plan(args.plan)
    assert_plan_matches_source(plan, args.package_root)
    require_directory(args.build_root, "build root")
    missing: list[str] = []
    for module in (*plan["modules"], UMBRELLA):
        for relative in module_artifact_paths(module):
            path = args.build_root.joinpath(*relative.parts)
            if not path.is_file() or path.is_symlink():
                missing.append(relative.as_posix())
    if missing:
        fail(f"build is incomplete: {len(missing)} expected leanArts artifacts missing; examples={missing[:10]}")
    print(json.dumps({"status": "complete", "modules": len(plan["modules"]), "artifacts": (len(plan["modules"]) + 1) * len(module_artifact_paths(UMBRELLA))}, sort_keys=True))


def cmd_self_test(args: argparse.Namespace) -> None:
    """Exercise determinism, protocol validation, and completeness checks."""
    with tempfile.TemporaryDirectory(prefix="rtf-shards-self-test-") as temporary:
        root = Path(temporary)
        plan_a = root / "plan-a"
        plan_b = root / "plan-b"
        model = load_source_model(args.package_root)
        plan = make_plan(model, args.shards)
        write_plan_output(plan, plan_a)
        write_plan_output(make_plan(load_source_model(args.package_root), args.shards), plan_b)
        raw_plan = (plan_a / "plan.json").read_bytes()
        if raw_plan != (plan_b / "plan.json").read_bytes():
            fail("planner is not deterministic")
        for shard in range(1, args.shards + 1):
            cmd_extract(
                argparse.Namespace(
                    plan=plan_a / "plan.json",
                    package_root=args.package_root,
                    shard=shard,
                    build_root=args.build_root,
                    output=root / f"payload-{shard}",
                )
            )
        cmd_merge(
            argparse.Namespace(
                plan=plan_a / "plan.json",
                package_root=args.package_root,
                payload=[root / f"payload-{shard}" for shard in range(1, args.shards + 1)],
                output=root / "merged",
            )
        )
        cmd_verify(
            argparse.Namespace(plan=plan_a / "plan.json", package_root=args.package_root, build_root=args.build_root)
        )
        try:
            cmd_verify(
                argparse.Namespace(
                    plan=plan_a / "plan.json", package_root=args.package_root, build_root=root / "merged" / "build"
                )
            )
        except ShardError as error:
            if "8 expected leanArts artifacts missing" not in str(error):
                raise
        else:
            fail("verify accepted a pre-umbrella merged tree")
        first_payload, _ = read_payload(root / "payload-1", plan, raw_plan)
        hash_entry = next(item for item in first_payload["files"] if item["path"].endswith(".hash"))
        tampered = root / "payload-1" / "build" / hash_entry["path"]
        tampered.write_bytes(b"tampered\n")
        try:
            read_payload(root / "payload-1", plan, raw_plan)
        except ShardError as error:
            if "digest mismatch" not in str(error):
                raise
        else:
            fail("payload digest validation accepted tampering")
    print(json.dumps({"status": "self-test-passed", "modules": len(plan["modules"]), "shards": args.shards}, sort_keys=True))


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    sub = result.add_subparsers(dest="command", required=True)
    plan = sub.add_parser("plan", help="generate a canonical closure-aware shard plan")
    plan.add_argument("--package-root", type=Path, required=True)
    plan.add_argument("--shards", type=int, default=8)
    plan.add_argument("--output", type=Path, required=True)
    plan.set_defaults(handler=cmd_plan)
    targets = sub.add_parser("targets", help="print one shard's exact Lake targets")
    targets.add_argument("--plan", type=Path, required=True)
    targets.add_argument("--shard", type=int, required=True)
    targets.add_argument("--package-root", type=Path)
    targets.set_defaults(handler=cmd_targets)
    extract = sub.add_parser("extract", help="package only a shard's owned module artifacts")
    extract.add_argument("--plan", type=Path, required=True)
    extract.add_argument("--package-root", type=Path, required=True)
    extract.add_argument("--shard", type=int, required=True)
    extract.add_argument("--build-root", type=Path, required=True)
    extract.add_argument("--output", type=Path, required=True)
    extract.set_defaults(handler=cmd_extract)
    merge = sub.add_parser("merge", help="validate and merge exactly one payload per shard")
    merge.add_argument("--plan", type=Path, required=True)
    merge.add_argument("--package-root", type=Path)
    merge.add_argument("--payload", type=Path, action="append", required=True)
    merge.add_argument("--output", type=Path, required=True)
    merge.set_defaults(handler=cmd_merge)
    verify = sub.add_parser("verify", help="require all module and umbrella leanArts artifacts")
    verify.add_argument("--plan", type=Path, required=True)
    verify.add_argument("--package-root", type=Path, required=True)
    verify.add_argument("--build-root", type=Path, required=True)
    verify.set_defaults(handler=cmd_verify)
    self_test = sub.add_parser("self-test", help="exercise the protocol against a complete package build")
    self_test.add_argument("--package-root", type=Path, required=True)
    self_test.add_argument("--build-root", type=Path, required=True)
    self_test.add_argument("--shards", type=int, default=8)
    self_test.set_defaults(handler=cmd_self_test)
    return result


def main() -> None:
    args = parser().parse_args()
    try:
        args.handler(args)
    except ShardError as error:
        print(f"rtf_shards: {error}", file=sys.stderr)
        raise SystemExit(2) from error


if __name__ == "__main__":
    main()
