#!/usr/bin/env python3
"""Validate every Lean declaration-evidence pointer in the claim ledger.

The durable provider map is produced from Lean's imported environment, not by
source-text matching.  Generated checker shards then import the defining
modules directly and `#check` every cited name.  CI builds the shards only
after its provider-file sweep, keeping each environment small and avoiding the
root aggregate's runner-memory cost.
"""

from __future__ import annotations

import argparse
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

EXACT_NAME = re.compile(r"^[^\s,;()/:\[\]]+$")
LEAN_PATH = re.compile(r"^EtingofRepresentationTheory/.+\.lean$")
MODULES_PER_SHARD = 12

# These entry modules are intentionally absent from cold CI because elaborating
# one of them exceeds the hosted runner's memory.  Their names are still
# resolved by Lean when the provider map is refreshed locally; the exact-key
# check below prevents unreviewed pointer changes from bypassing that audit.
CI_EXCLUDED_PROVIDER_PATTERNS = tuple(
    re.compile(pattern)
    for pattern in (
        r"^EtingofRepresentationTheory\.Infrastructure\.SpechtModuleSimple$",
        r"^EtingofRepresentationTheory\.Chapter5\.SpechtCharacterGeneral$",
        r"^EtingofRepresentationTheory\.Chapter5\.YoungSymTraceKronecker$",
        r"^EtingofRepresentationTheory\.Chapter5\.FrobeniusCharacterBridge$",
        r"^EtingofRepresentationTheory\.Chapter5\.Proposition5_22_2$",
        r"^EtingofRepresentationTheory\.Chapter6\.Example6_4_9_EType$",
        r"^EtingofRepresentationTheory\.Chapter6\.Example6_4_9$",
    )
)


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
                    pointers.extend(Pointer(name, where) for name in exact_names(child, where, errors))
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
    PROVIDERS.write_text(json.dumps(providers, indent=2, sort_keys=True) + "\n")
    return providers


def provider_is_ci_excluded(module: str) -> bool:
    return any(pattern.fullmatch(module) for pattern in CI_EXCLUDED_PROVIDER_PATTERNS)


def render_shards(pointers: list[Pointer], providers: dict[str, str]) -> tuple[dict[str, str], int]:
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
    excluded_count = 0
    for name in sorted(names):
        module = providers[name]
        if provider_is_ci_excluded(module):
            excluded_count += 1
            continue
        names_by_module.setdefault(module, []).append(name)

    modules = sorted(names_by_module)
    shards: dict[str, str] = {}
    for start in range(0, len(modules), MODULES_PER_SHARD):
        shard_modules = modules[start:start + MODULES_PER_SHARD]
        lines = [*(f"import {module}" for module in shard_modules), "", "/-!", "# Claim-ledger declaration pointers", "", "Generated by `scripts/validate_lean_decls.py --apply`.", "-/", ""]
        for module in shard_modules:
            lines.append(f"-- Provider: {module}")
            for name in names_by_module[module]:
                labels = ", ".join(sorted(labels_by_name[name]))
                lines.extend(f"-- {line}" for line in textwrap.wrap(labels, width=96))
                lines.append(f"#check @{name}")
            lines.append("")
        filename = f"Shard{start // MODULES_PER_SHARD + 1:03d}.lean"
        shards[filename] = "\n".join(lines)
    return shards, excluded_count


def apply_shards(shards: dict[str, str]) -> None:
    CHECKER_DIR.mkdir(parents=True, exist_ok=True)
    for path in CHECKER_DIR.glob("*.lean"):
        if path.name not in shards:
            path.unlink()
    for filename, content in shards.items():
        (CHECKER_DIR / filename).write_text(content)


def check_shards(shards: dict[str, str]) -> bool:
    actual = {path.name for path in CHECKER_DIR.glob("*.lean")} if CHECKER_DIR.is_dir() else set()
    if actual != set(shards):
        return False
    return all((CHECKER_DIR / name).read_text() == content for name, content in shards.items())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--apply", action="store_true", help="rewrite generated checker shards")
    mode.add_argument(
        "--refresh-providers", action="store_true",
        help="resolve every name in Lean, rewrite the provider map, and apply shards",
    )
    mode.add_argument("--check", action="store_true", help="require provider map and shards to be current")
    args = parser.parse_args()

    items = json.loads(ITEMS.read_text())
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
            providers = json.loads(PROVIDERS.read_text()) if PROVIDERS.is_file() else {}
        shards, excluded_count = render_shards(pointers, providers)
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
        f"LEAN DECLARATION POINTERS VALIDATED: {len(pointers)} uses, {len(names)} unique names, "
        f"{len(shards)} checker shards, {excluded_count} locally resolved runner exclusions"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
