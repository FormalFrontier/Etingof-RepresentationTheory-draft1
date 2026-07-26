#!/usr/bin/env python3
"""Fail the build when a Lean file emits warnings it is not on record as emitting.

`lakefile.toml` sets `weak.linter.mathlibStandardSet = true`, so the linters this
project cares about (`unusedSectionVars`, `unusedDecidableInType`,
`unusedFintypeInType`, `linter.style.show`, `linter.style.setOption`, …) already
run on every build. `lake build` exits 0 on warnings, though, so nothing stopped
new ones from accumulating.

This script closes that by ratcheting against a checked-in baseline of the files
that emit warnings today (`scripts/lint-warning-baseline.txt`). Two conditions
fail:

1. a file emitted a warning and is **not** in the baseline (a new warning), and
2. a baseline file was built and emitted **no** warning (a stale entry, i.e. the
   file was cleaned but the baseline was not updated).

Condition 2 is what keeps the baseline shrinking rather than rotting. It is only
applied to files the run actually built, so entries for modules excluded from CI
are left alone.

Usage:

    scripts/check_lint_clean.py --log build.log --modules modules.txt
    scripts/check_lint_clean.py --log build.log --modules modules.txt --update

`--modules` takes the module-name list the build was invoked with (one
`EtingofRepresentationTheory.Chapter3.Foo` per line); `--update` rewrites the
baseline from the log instead of checking it, for regenerating after a
deliberate change.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

SOURCE_ROOT = "EtingofRepresentationTheory"

# `lake build` renders diagnostics as
#   warning: EtingofRepresentationTheory/Chapter3/Foo.lean:3:31: Variable name ...
# with the path relative to the project root. Continuation lines of a multi-line
# message carry no prefix, so anchoring on the whole line is what distinguishes a
# real diagnostic from message text that happens to mention a file.
WARNING_RE = re.compile(
    r"^warning: (?P<file>\.?/?" + SOURCE_ROOT + r"/[^:\s]+\.lean):\d+:\d+: "
)

ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")


def warned_file(line: str) -> str | None:
    """The source file a build-log line reports a warning against, if any."""
    match = WARNING_RE.match(ANSI_RE.sub("", line))
    return match.group("file").lstrip("./") if match else None


def parse_log(log_path: pathlib.Path) -> dict[str, int]:
    """Map each source file appearing in a build log to its warning count."""
    counts: dict[str, int] = {}
    with log_path.open(encoding="utf-8", errors="replace") as handle:
        for line in handle:
            path = warned_file(line)
            if path is not None:
                counts[path] = counts.get(path, 0) + 1
    return counts


def module_to_path(module: str) -> str:
    return module.strip().replace(".", "/") + ".lean"


def read_lines(path: pathlib.Path) -> list[str]:
    if not path.exists():
        return []
    return [
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.startswith("#")
    ]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", required=True, type=pathlib.Path)
    parser.add_argument(
        "--baseline",
        type=pathlib.Path,
        default=pathlib.Path("scripts/lint-warning-baseline.txt"),
    )
    parser.add_argument(
        "--modules",
        type=pathlib.Path,
        help="module-name list the build was invoked with; enables stale-entry detection",
    )
    parser.add_argument(
        "--update",
        action="store_true",
        help="rewrite the baseline from the log instead of checking against it",
    )
    args = parser.parse_args()

    if not args.log.exists():
        print(f"error: build log {args.log} does not exist", file=sys.stderr)
        return 1

    counts = parse_log(args.log)
    offenders = sorted(counts)

    if args.update:
        header = [
            "# Lean source files that emit build warnings.",
            "#",
            "# Checked by scripts/check_lint_clean.py: a file not listed here must build",
            "# warning-free, and a listed file that has been cleaned must be removed from",
            "# this list. Both directions are enforced, so the list only shrinks.",
            "#",
            "# Regenerate after a deliberate change with:",
            "#   scripts/check_lint_clean.py --log <build.log> --update",
        ]
        args.baseline.write_text(
            "\n".join(header + offenders) + "\n", encoding="utf-8"
        )
        total = sum(counts.values())
        print(f"wrote {args.baseline}: {len(offenders)} files, {total} warnings")
        return 0

    baseline = set(read_lines(args.baseline))
    built = (
        {module_to_path(module) for module in read_lines(args.modules)}
        if args.modules
        else set()
    )

    new_warnings = [path for path in offenders if path not in baseline]
    # Only files this run actually built can be judged clean; a baseline entry for a
    # module the run skipped simply was not measured.
    stale = sorted(path for path in baseline if path in built and path not in counts)

    if new_warnings:
        print("::error::New build warnings. This project keeps the build lint-clean.")
        for path in new_warnings:
            print(f"::error file={path}::{counts[path]} new warning(s) in {path}")
            for line in warning_lines(args.log, path):
                print(f"  {line}")

    if stale:
        print(
            "::error::These files are warning-free now but still listed in "
            f"{args.baseline}. Remove them so the baseline keeps ratcheting down."
        )
        for path in stale:
            print(f"::error file={path}::stale baseline entry: {path}")

    if new_warnings or stale:
        print(
            "\nTo see them locally: lake build <the modules you touched>\n"
            f"To regenerate the baseline after cleaning: "
            f"scripts/check_lint_clean.py --log <build.log> --update"
        )
        return 1

    print(
        f"OK: no new warnings. {len(baseline)} file(s) on the baseline, "
        f"{len(built & baseline)} of them built by this run."
    )
    return 0


def warning_lines(log_path: pathlib.Path, path: str) -> list[str]:
    """The diagnostic header lines a given file contributed, for the failure report."""
    lines = []
    with log_path.open(encoding="utf-8", errors="replace") as handle:
        for line in handle:
            if warned_file(line) == path:
                lines.append(ANSI_RE.sub("", line).rstrip())
    return lines


if __name__ == "__main__":
    sys.exit(main())
