#!/usr/bin/env python3
"""Validate every Lean declaration-evidence pointer in the claim ledger.

The durable provider map is produced from Lean's imported environment, not by
source-text matching.  Generated checker shards then import the defining
modules directly and `#check` every cited name.  CI builds the shards only
after its provider-file sweep, keeping each environment small and avoiding the
root aggregate's runner-memory cost.  Ledger editors should cite the most
specific public declaration that proves a claim, never a coarser theorem merely
to make validation pass.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import textwrap
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ITEMS = ROOT / "progress" / "items.json"
PROVIDERS = ROOT / "scripts" / "lean-decl-providers.json"
CHECKER_DIR = ROOT / "EtingofRepresentationTheory" / "ClaimCoverageDeclarations"
EXTRACTOR = ROOT / "scripts" / "extract_lean_decl_providers.lean"
CI_EXCLUDED_MODULES_FILE = ROOT / "scripts" / "ci-excluded-lean-modules.txt"
EXCLUDED_ATTESTATIONS = ROOT / "scripts" / "lean-decl-excluded-attestations.json"

EXACT_NAME = re.compile(r"^[^\s,;()/:\[\]]+$")
LEAN_PATH = re.compile(r"^EtingofRepresentationTheory/.+\.lean$")
MODULES_PER_SHARD = 12

def load_ci_excluded_modules() -> frozenset[str]:
    modules = [
        line.strip() for line in
        CI_EXCLUDED_MODULES_FILE.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    if len(modules) != len(set(modules)):
        raise ValueError(f"duplicate module in {CI_EXCLUDED_MODULES_FILE}")
    for module in modules:
        if not module_source_path(module).is_file():
            raise ValueError(f"CI-excluded module has no source file: {module}")
    return frozenset(modules)


def module_source_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def source_sha256(module: str) -> str:
    return hashlib.sha256(module_source_path(module).read_bytes()).hexdigest()


def environment_pins() -> dict[str, str]:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = [package for package in manifest["packages"] if package["name"] == "mathlib"]
    if len(mathlib) != 1:
        raise ValueError("lake-manifest.json must contain exactly one mathlib package")
    return {
        "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "mathlib_revision": mathlib[0]["rev"],
    }


CI_EXCLUDED_PROVIDER_MODULES = load_ci_excluded_modules()


@dataclass(frozen=True)
class Pointer:
    name: str
    label: str


def item_label(item: dict[str, object]) -> str:
    return str(item.get("id") or f"derived-from:{item.get('derived_from', '<unknown>')}")


def exact_names(value: object, where: str, errors: list[str]) -> list[str]:
    entries = value if isinstance(value, list) else [value]
    result: list[str] = []
    for entry in entries:
        if not isinstance(entry, str):
            errors.append(f"{where}: declaration pointer must be a string")
            continue
        for part in entry.split(";"):
            name = part.strip()
            if not name:
                errors.append(f"{where}: empty declaration pointer")
            elif not EXACT_NAME.fullmatch(name):
                errors.append(f"{where}: not an exact Lean declaration name: {name!r}")
            else:
                result.append(name)
    return result


def lean_ref_groups(value: object, where: str, errors: list[str]) -> list[tuple[str, list[str]]]:
    if not isinstance(value, str):
        errors.append(f"{where}: lean_ref must be a string")
        return []
    result: list[tuple[str, list[str]]] = []
    for raw_group in value.split(";"):
        group = raw_group.strip()
        path, separator, declarations = group.partition("::")
        path = path.strip()
        if not separator or not LEAN_PATH.fullmatch(path) or not (ROOT / path).is_file():
            errors.append(
                f"{where}: lean_ref group must start with an existing "
                f"EtingofRepresentationTheory/*.lean provider: {group!r}"
            )
            continue
        names: list[str] = []
        for raw_name in declarations.split(","):
            name = raw_name.strip()
            if not name or not EXACT_NAME.fullmatch(name):
                errors.append(f"{where}: not an exact lean_ref declaration name: {name!r}")
            else:
                names.append(name)
        if not names:
            errors.append(f"{where}: lean_ref provider has no declarations: {path}")
        result.append((path, names))
    return result


def collect(items: list[dict[str, object]]) -> tuple[list[Pointer], list[str]]:
    pointers: list[Pointer] = []
    errors: list[str] = []

    def walk(value: object, label: str) -> None:
        if isinstance(value, dict):
            for key, child in value.items():
                where = f"{label}.{key}"
                if key == "lean_decl":
                    pointers.extend(
                        Pointer(name, where) for name in exact_names(child, where, errors))
                elif key == "lean_ref":
                    for _, names in lean_ref_groups(child, where, errors):
                        pointers.extend(Pointer(name, where) for name in names)
                else:
                    walk(child, where)
        elif isinstance(value, list):
            for index, child in enumerate(value, 1):
                walk(child, f"{label}[{index}]")

    for item in items:
        walk(item, item_label(item))
    return pointers, errors


def validate_lean_ref_providers(
    items: list[dict[str, object]], providers: dict[str, str]
) -> list[str]:
    """Require every lean_ref declaration to be defined by its cited file."""
    errors: list[str] = []

    def walk(value: object, label: str) -> None:
        if isinstance(value, dict):
            for key, child in value.items():
                where = f"{label}.{key}"
                if key == "lean_ref":
                    parse_errors: list[str] = []
                    for path, names in lean_ref_groups(child, where, parse_errors):
                        expected_module = path.removesuffix(".lean").replace("/", ".")
                        for name in names:
                            actual_module = providers.get(name)
                            if actual_module is not None and actual_module != expected_module:
                                errors.append(
                                    f"{where}: {name} is provided by {actual_module}, "
                                    f"not {expected_module}"
                                )
                    errors.extend(parse_errors)
                else:
                    walk(child, where)
        elif isinstance(value, list):
            for index, child in enumerate(value, 1):
                walk(child, f"{label}[{index}]")

    for item in items:
        walk(item, item_label(item))
    return errors


def refresh_providers(names: list[str]) -> dict[str, str]:
    with tempfile.NamedTemporaryFile("w", encoding="utf-8") as names_file:
        names_file.write("\n".join(names) + "\n")
        names_file.flush()
        command = [
            "lake", "env", "lean", "--run", str(EXTRACTOR.relative_to(ROOT)), names_file.name
        ]
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        print(result.stdout, end="", file=sys.stderr)
        print(result.stderr, end="", file=sys.stderr)
        raise RuntimeError(
            "Lean provider discovery failed; build the root project locally, fix every "
            "unknown declaration, and rerun --refresh-providers"
        )
    providers: dict[str, str] = {}
    for line in result.stdout.splitlines():
        name, separator, module = line.partition("\t")
        if not separator or not name or not module:
            raise RuntimeError(f"malformed provider-discovery output: {line!r}")
        providers[name] = module
    if set(providers) != set(names):
        raise RuntimeError("provider discovery did not return exactly the requested declarations")
    PROVIDERS.write_text(
        json.dumps(providers, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_excluded_attestations(providers)
    return providers


def provider_is_ci_excluded(module: str) -> bool:
    return module in CI_EXCLUDED_PROVIDER_MODULES


def write_excluded_attestations(providers: dict[str, str]) -> None:
    """Record the locally compiler-resolved names omitted from cold CI."""
    attestations = {
        name: {
            "module": module,
            "source_sha256": source_sha256(module),
            **environment_pins(),
        }
        for name, module in sorted(providers.items())
        if provider_is_ci_excluded(module)
    }
    EXCLUDED_ATTESTATIONS.write_text(
        json.dumps(attestations, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def validate_excluded_attestations(
    providers: dict[str, str], attestations: dict[str, object]
) -> list[str]:
    """Ratchet local Lean resolution for providers too large for cold CI."""
    errors: list[str] = []
    expected = {
        name for name, module in providers.items() if provider_is_ci_excluded(module)
    }
    if set(attestations) != expected:
        missing = sorted(expected - set(attestations))
        stale = sorted(set(attestations) - expected)
        if missing:
            errors.append(f"excluded attestations missing: {', '.join(missing)}")
        if stale:
            errors.append(f"excluded attestations stale: {', '.join(stale)}")
    for name in sorted(expected & set(attestations)):
        record = attestations[name]
        module = providers[name]
        wanted = {
            "module": module,
            "source_sha256": source_sha256(module),
            **environment_pins(),
        }
        if record != wanted:
            errors.append(
                f"excluded attestation stale for {name}; rerun --refresh-providers"
            )
    return errors


def render_shards(
    pointers: list[Pointer], providers: dict[str, str]
) -> tuple[dict[str, str], list[str]]:
    labels_by_name: dict[str, set[str]] = {}
    for pointer in pointers:
        labels_by_name.setdefault(pointer.name, set()).add(pointer.label)

    names = set(labels_by_name)
    if set(providers) != names:
        missing = sorted(names - set(providers))
        extra = sorted(set(providers) - names)
        details = []
        if missing:
            details.append(f"missing: {', '.join(missing[:8])}")
        if extra:
            details.append(f"stale: {', '.join(extra[:8])}")
        raise ValueError(
            "scripts/lean-decl-providers.json is stale (" + "; ".join(details)
            + "); run python3 scripts/validate_lean_decls.py --refresh-providers"
        )

    names_by_module: dict[str, list[str]] = {}
    excluded_names: list[str] = []
    for name in sorted(names):
        module = providers[name]
        if provider_is_ci_excluded(module):
            excluded_names.append(name)
            continue
        names_by_module.setdefault(module, []).append(name)

    modules = sorted(names_by_module)
    shards: dict[str, str] = {}
    for start in range(0, len(modules), MODULES_PER_SHARD):
        shard_modules = modules[start:start + MODULES_PER_SHARD]
        lines = [
            *(f"import {module}" for module in shard_modules),
            "",
            "/-!",
            "# Claim-ledger declaration pointers",
            "",
            "Generated by `scripts/validate_lean_decls.py --apply`.",
            "-/",
            "",
            "set_option linter.style.longLine false",
            "",
        ]
        for module in shard_modules:
            lines.append(f"-- Provider: {module}")
            for name in names_by_module[module]:
                labels = ", ".join(sorted(labels_by_name[name]))
                lines.extend(f"-- {line}" for line in textwrap.wrap(labels, width=96))
                lines.append(f"#check @{name}")
            lines.append("")
        filename = f"Shard{start // MODULES_PER_SHARD + 1:03d}.lean"
        shards[filename] = "\n".join(lines)
    return shards, excluded_names


def apply_shards(shards: dict[str, str]) -> None:
    CHECKER_DIR.mkdir(parents=True, exist_ok=True)
    for path in CHECKER_DIR.glob("*.lean"):
        if path.name not in shards:
            path.unlink()
    for filename, content in shards.items():
        (CHECKER_DIR / filename).write_text(content, encoding="utf-8")


def check_shards(shards: dict[str, str]) -> bool:
    actual = {path.name for path in CHECKER_DIR.glob("*.lean")} if CHECKER_DIR.is_dir() else set()
    if actual != set(shards):
        return False
    return all(
        (CHECKER_DIR / name).read_text(encoding="utf-8") == content
        for name, content in shards.items())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--apply", action="store_true", help="rewrite generated checker shards")
    mode.add_argument(
        "--refresh-providers", action="store_true",
        help="resolve every name in Lean, rewrite the provider map, and apply shards",
    )
    mode.add_argument(
        "--check", action="store_true",
        help="require provider map and shards to be current")
    args = parser.parse_args()

    items = json.loads(ITEMS.read_text(encoding="utf-8"))
    pointers, errors = collect(items)
    if errors:
        print("Declaration-evidence validation failed:", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1
    names = sorted({pointer.name for pointer in pointers})

    try:
        if args.refresh_providers:
            providers = refresh_providers(names)
        else:
            providers = (
                json.loads(PROVIDERS.read_text(encoding="utf-8"))
                if PROVIDERS.is_file() else {})
        ref_errors = validate_lean_ref_providers(items, providers)
        attestations = (
            json.loads(EXCLUDED_ATTESTATIONS.read_text(encoding="utf-8"))
            if EXCLUDED_ATTESTATIONS.is_file() else {}
        )
        attestation_errors = validate_excluded_attestations(providers, attestations)
        if ref_errors or attestation_errors:
            raise ValueError("; ".join(ref_errors + attestation_errors))
        shards, excluded_names = render_shards(pointers, providers)
    except (RuntimeError, ValueError, json.JSONDecodeError) as error:
        print(error, file=sys.stderr)
        return 1

    if args.apply or args.refresh_providers:
        apply_shards(shards)
    elif not check_shards(shards):
        print(
            "ClaimCoverageDeclarations shards are stale; run "
            "python3 scripts/validate_lean_decls.py --apply",
            file=sys.stderr,
        )
        return 1

    print(
        f"LEAN DECLARATION POINTERS VALIDATED: {len(pointers)} uses, "
        f"{len(names) - len(excluded_names)} compiler-checked CI names, "
        f"{len(excluded_names)} locally attested runner exclusions, "
        f"{len(shards)} checker shards"
    )
    for name in excluded_names:
        print(f"  locally attested (CI memory exclusion): {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
