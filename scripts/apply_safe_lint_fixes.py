#!/usr/bin/env python3
"""Apply syntax-preserving fixes explicitly requested by Lean's style linters.

The input is a complete ``lake build`` log.  Only two diagnostics with an
unambiguous one-token edit are handled:

* a goal-changing ``show`` tactic becomes ``change``;
* an explicitly identified unused simp argument is removed from its list.

Every edit is anchored at the diagnostic's file/line/column and is applied
bottom-up.  If the expected token is not at that exact location the diagnostic
is skipped, so this tool cannot guess at a nearby occurrence.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from pathlib import Path
import re


DIAGNOSTIC = re.compile(
    r"^warning: (?P<file>EtingofRepresentationTheory/[^:]+\.lean):"
    r"(?P<line>\d+):(?P<column>\d+): (?P<message>.*)$"
)


def requested_edit(message: str) -> tuple[str, str] | None:
    if message.startswith("The `show` tactic should only be used"):
        return "show", "change"
    if message.startswith("Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"):
        return "<;>", ";"
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    args = parser.parse_args()

    edits: dict[Path, set[tuple[int, int, str, str]]] = defaultdict(set)
    raw_lines = args.log.read_text(encoding="utf-8", errors="replace").splitlines()
    pending_unused: tuple[Path, int, int] | None = None
    for raw in raw_lines:
        if pending_unused is not None:
            path, line_no, column = pending_unused
            argument = raw.strip()
            if argument:
                edits[path].add((line_no, column, argument, ""))
            pending_unused = None
            continue
        match = DIAGNOSTIC.match(raw)
        if not match:
            continue
        if match["message"].startswith("This simp argument is unused:"):
            pending_unused = (
                Path(match["file"]), int(match["line"]) - 1, int(match["column"])
            )
            continue
        if (edit := requested_edit(match["message"])) is None:
            continue
        edits[Path(match["file"])].add(
            (int(match["line"]) - 1, int(match["column"]), *edit)
        )

    applied = skipped = 0
    for path, file_edits in edits.items():
        lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
        for line_no, column, old, new in sorted(file_edits, reverse=True):
            if line_no >= len(lines):
                skipped += 1
                continue
            line = lines[line_no]
            if line[column : column + len(old)] != old:
                skipped += 1
                continue
            before = line[column - 1] if column else " "
            after = line[column + len(old)] if column + len(old) < len(line) else " "
            if (before.isalnum() or before == "_") or (after.isalnum() or after == "_"):
                skipped += 1
                continue
            start = column
            end = column + len(old)
            if not new:
                # Remove the adjacent comma as well.  If this is the sole
                # argument, remove the brackets unless they belong to
                # ``simp only``, where an empty list would be invalid.
                right = end
                while right < len(line) and line[right].isspace() and line[right] != "\n":
                    right += 1
                left = start - 1
                while left >= 0 and line[left].isspace():
                    left -= 1
                if right < len(line) and line[right] == ",":
                    end = right + 1
                    while end < len(line) and line[end].isspace() and line[end] != "\n":
                        end += 1
                elif left >= 0 and line[left] == ",":
                    start = left
                    while start > 0 and line[start - 1].isspace():
                        start -= 1
                elif left >= 0 and line[left] == "[" and right < len(line) and line[right] == "]":
                    if line[:left].rstrip().endswith("simp only"):
                        skipped += 1
                        continue
                    start, end = left, right + 1
                else:
                    skipped += 1
                    continue
            lines[line_no] = line[:start] + new + line[end:]
            applied += 1
        path.write_text("".join(lines), encoding="utf-8")

    print(f"applied {applied} safe lint fix(es); skipped {skipped}")


if __name__ == "__main__":
    main()
