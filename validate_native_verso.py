#!/usr/bin/env python3
"""Validate structural invariants of item-shaped native Verso modules."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path


RAW_DOLLAR = re.compile(r"\$(?!\$?`)")
FOOTNOTE_MARKER = re.compile(r"\$\^[0-9]+\$")
MARKDOWN_TABLE_SEPARATOR = re.compile(r"^\s*\|(?:\s*:?-+:?\s*\|)+\s*$")
SOURCE_TEX = re.compile(
    r"(?<!\\)\$\$(.*?)(?<!\\)\$\$|(?<!\\)\$(?!\$)(.*?)(?<!\\)\$",
    re.DOTALL,
)
NATIVE_TEX = re.compile(r"\$\$`(.*?)`|\$`(.*?)`", re.DOTALL)
WAIVER_PATH = Path(__file__).resolve().parent / "manifests/book/native-verso-fidelity-waivers.json"

# These ten notes were present in the source as legacy numbered markers.  Six
# definitions fell in a later extraction packet than their reference.  Verso
# resolves named notes within one #doc, so those definitions intentionally
# live in the referencing item; fidelity comparison projects their source body
# there as well.  Names include the stable item ID to remain collision-free
# when all item documents are assembled.
FOOTNOTES = (
    ("Chapter1/Discussion_BookOrganization", "Chapter1/Acknowledgments", 1),
    ("Chapter2/Theorem2.1.2", "Chapter2/Theorem2.1.2", 1),
    ("Chapter2/Definition2.8.4", "Chapter2/Discussion_quiver_rep_bijection", 2),
    ("Chapter3/Proposition3.1.4", "Chapter3/Remark3.1.5", 1),
    (
        "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4",
        "Chapter3/Introduction_to_3.2",
        2,
    ),
    ("Chapter3/Theorem3.2.2", "Chapter3/Theorem3.2.2", 3),
    ("Chapter3/Definition3.5.7", "Chapter3/Proposition3.5.8", 4),
    ("Chapter3/Theorem3.7.1", "Chapter3/Theorem3.7.1", 5),
    ("Chapter4/Definition4.6.1", "Chapter4/Discussion_after_Theorem4.6.2", 1),
    ("Chapter4/Problem4.12.8", "Chapter4/Problem4.12.8", 2),
)


def scoped_footnote_name(reference_item: str, number: int) -> str:
    return f"{reference_item}/footnote-{number}"


def source_footnote_body(source: str, number: int) -> str:
    """Extract one legacy source note body without its marker syntax."""
    patterns = (
        rf"(?m)^\$\^{number}\$\s?(.*)$",
        rf"(?m)^\[\^{number}\]:\s?(.*)$",
        # The first note in Chapter 2 used Pandoc's inline-footnote syntax.
        r":\^\[([^\n]*)\]",
    )
    bodies = [match.group(1) for pattern in patterns for match in re.finditer(pattern, source)]
    if len(bodies) != 1:
        raise ValueError(f"expected one source body for footnote {number}, found {len(bodies)}")
    return bodies[0]


def remove_source_footnote_definition(source: str, number: int) -> str:
    """Remove a cross-packet note definition and its print-only separator."""
    for pattern in (
        rf"(?m)^\$\^{number}\$\s?.*(?:\n|$)",
        rf"(?m)^\[\^{number}\]:\s?.*(?:\n|$)",
    ):
        source, count = re.subn(pattern, "", source)
        if count:
            # A horizontal rule adjacent to a legacy $^n$ definition is the
            # printed-footnote separator, not book prose.
            source = re.sub(r"(?m)^---\s*(?:\n|$)", "", source)
            return source
    raise ValueError(f"missing source definition for footnote {number}")


def semantic_footnote_body(value: str, native: bool) -> str:
    """Normalize prose markup; ordered TeX payloads are checked separately."""
    if native:
        value = re.sub(r"\$\$?`[^`]*`", " <math> ", value)
        value = value.replace(r"\[", "[").replace(r"\]", "]")
        value = value.replace("*", "").replace("_", "")
    else:
        value = re.sub(r"\$\$[^$]*\$\$|\$[^$\n]*\$", " <math> ", value)
        value = value.replace("**", "").replace("*", "")
    return " ".join(value.split())


def packet_source_path(content_path: Path, item_id: str) -> Path:
    packet_root = next(parent for parent in content_path.parents if parent.name == "conversion-packets")
    matches = sorted(packet_root.glob(f"*/{item_id}/source.md"))
    if len(matches) != 1:
        raise ValueError(f"expected one source packet for {item_id}, found {len(matches)}")
    return matches[0]


def projected_source_for_fidelity(path: Path, item_id: str, source: str) -> str:
    projected = source
    for reference_item, body_item, number in FOOTNOTES:
        if reference_item == body_item:
            continue
        if item_id == reference_item:
            body_source = packet_source_path(path, body_item).read_text(encoding="utf-8")
            projected = projected.rstrip() + "\n\n" + source_footnote_body(body_source, number) + "\n"
        elif item_id == body_item:
            projected = remove_source_footnote_definition(projected, number)
    return projected


def load_fidelity_waivers() -> dict[str, dict[str, str]]:
    if not WAIVER_PATH.exists():
        return {}
    waivers = json.loads(WAIVER_PATH.read_text(encoding="utf-8"))
    for item_id, categories in waivers.items():
        if not isinstance(categories, dict) or not categories:
            raise ValueError(f"invalid empty fidelity waiver for {item_id}")
        for category, reason in categories.items():
            if category not in {"bold", "tex"} or not isinstance(reason, str) or not reason.strip():
                raise ValueError(f"invalid {category!r} fidelity waiver for {item_id}")
    return waivers


FIDELITY_WAIVERS = load_fidelity_waivers()


def outside_math_delimiters(line: str, marker: str, native: bool) -> list[str]:
    """Return paired emphasis bodies delimited by marker outside TeX/code spans."""
    bodies: list[str] = []
    start: int | None = None
    index = 0
    while index < len(line):
        if line[index] == "\\":
            index += 2
            continue
        if native and line.startswith("$$`", index):
            end = line.find("`", index + 3)
            index = len(line) if end < 0 else end + 1
            continue
        if native and line.startswith("$`", index):
            end = line.find("`", index + 2)
            index = len(line) if end < 0 else end + 1
            continue
        if not native and line[index] == "$":
            width = 2 if line.startswith("$$", index) else 1
            end = line.find("$" * width, index + width)
            index = len(line) if end < 0 else end + width
            continue
        if native and line[index] == "`":
            end = line.find("`", index + 1)
            index = len(line) if end < 0 else end + 1
            continue
        if line[index] == marker:
            if marker == "*" and (
                (index > 0 and line[index - 1] == "*")
                or (index + 1 < len(line) and line[index + 1] == "*")
            ):
                index += 1
                continue
            if start is None:
                start = index + 1
            else:
                bodies.append(line[start:index])
                start = None
        index += 1
    return bodies


def outside_math_delimiter(line: str, delimiter: str, native: bool) -> list[str]:
    """Return paired delimiter bodies outside math/code, for `*` and `**`."""
    bodies: list[str] = []
    start: int | None = None
    index = 0
    width = len(delimiter)
    while index < len(line):
        if line[index] == "\\":
            index += 2
            continue
        if native and line.startswith("$$`", index):
            end = line.find("`", index + 3)
            index = len(line) if end < 0 else end + 1
            continue
        if native and line.startswith("$`", index):
            end = line.find("`", index + 2)
            index = len(line) if end < 0 else end + 1
            continue
        if not native and line[index] == "$":
            math_width = 2 if line.startswith("$$", index) else 1
            end = line.find("$" * math_width, index + math_width)
            index = len(line) if end < 0 else end + math_width
            continue
        if native and line[index] == "`":
            end = line.find("`", index + 1)
            index = len(line) if end < 0 else end + 1
            continue
        if line.startswith(delimiter, index):
            before_same = index > 0 and line[index - 1] == delimiter[0]
            after_same = (
                index + width < len(line) and line[index + width] == delimiter[-1]
            )
            if not before_same and not after_same:
                if start is None:
                    start = index + width
                else:
                    bodies.append(line[start:index])
                    start = None
                index += width
                continue
        index += 1
    return bodies


def semantic_emphasis_body(value: str, native: bool) -> str:
    if native:
        value = re.sub(r"\$\$?`[^`]*`", " <math> ", value)
        value = value.replace(r"\[", "[").replace(r"\]", "]")
    else:
        value = re.sub(r"\$\$[^$]*\$\$|\$[^$\n]*\$", " <math> ", value)
    return " ".join(value.split())


def tex_payloads(value: str, native: bool) -> list[str]:
    """Extract ordered TeX bodies, ignoring raw footnote-reference markers."""
    if not native:
        value = FOOTNOTE_MARKER.sub("", value)
    pattern = NATIVE_TEX if native else SOURCE_TEX
    payloads: list[str] = []
    for match in pattern.finditer(value):
        payload = match.group(1) if match.group(1) is not None else match.group(2)
        payloads.append(" ".join(payload.strip().split()))
    return payloads


def validate(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    errors: list[str] = []
    if "import VersoManual" not in text:
        errors.append("missing `import VersoManual`")
    if not re.search(r"(?m)^#doc\s*\(Manual\)", text):
        errors.append("missing composable top-level `#doc (Manual)` document")
    packet_path = path.with_name("packet.json")
    if packet_path.exists():
        packet = json.loads(packet_path.read_text(encoding="utf-8"))
        module = packet["item"]["verso_module"]
        item_id = packet["item"]["id"]
        item_waivers = FIDELITY_WAIVERS.get(item_id, {})
        if not re.search(rf"(?m)^namespace\s+{re.escape(module)}\s*$", text):
            errors.append(f"missing exact document namespace `{module}`")
        if f'tag := {json.dumps(item_id)}' in text and re.search(
            rf"(?m)^end\s+{re.escape(module)}\s*$", text
        ):
            errors.append("normalized item must leave its namespace open at EOF")
        source_path = path.with_name("source.md")
        if source_path.exists():
            source = source_path.read_text(encoding="utf-8")
            actual_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
            expected_hash = packet["item"].get("source_sha256")
            if expected_hash != actual_hash:
                errors.append(
                    f"source hash mismatch: packet has {expected_hash}, actual is {actual_hash}"
                )
            for reference_item, body_item, number in FOOTNOTES:
                name = scoped_footnote_name(reference_item, number)
                if item_id == reference_item:
                    references = re.findall(rf"\[\^{re.escape(name)}\](?!:)", text)
                    definitions = re.findall(
                        rf"(?m)^\[\^{re.escape(name)}\]:\s?(.*)$", text
                    )
                    if len(references) != 1:
                        errors.append(
                            f"expected one reference to scoped footnote {name!r}, "
                            f"found {len(references)}"
                        )
                    if len(definitions) != 1:
                        errors.append(
                            f"expected one definition of scoped footnote {name!r}, "
                            f"found {len(definitions)}"
                        )
                    if len(definitions) == 1:
                        body_source = (
                            source
                            if body_item == reference_item
                            else packet_source_path(path, body_item).read_text(encoding="utf-8")
                        )
                        expected_body = source_footnote_body(body_source, number)
                        if semantic_footnote_body(definitions[0], native=True) != semantic_footnote_body(
                            expected_body, native=False
                        ):
                            errors.append(
                                f"scoped footnote {name!r} body differs from source"
                            )
                elif item_id == body_item and name in text:
                    errors.append(
                        f"cross-packet footnote {name!r} must live in its referencing item"
                    )
            source = projected_source_for_fidelity(path, item_id, source)
            source_without_display_math = re.sub(r"\$\$.*?\$\$", "", source, flags=re.DOTALL)
            markdown_italics = Counter(
                semantic_emphasis_body(body, native=False)
                for line in source_without_display_math.splitlines()
                for body in outside_math_delimiters(line, "*", native=False)
            )
            native_emphasis = Counter(
                semantic_emphasis_body(body, native=True)
                for line in text.splitlines()
                for body in outside_math_delimiters(line, "_", native=True)
            )
            missing_emphasis = markdown_italics - native_emphasis
            for body, count in sorted(missing_emphasis.items()):
                errors.append(
                    f"{count} Markdown italic span(s) not represented as native Verso emphasis: {body!r}"
                )
            markdown_bold = Counter(
                semantic_emphasis_body(body, native=False)
                for line in source_without_display_math.splitlines()
                for body in outside_math_delimiter(line, "**", native=False)
            )
            native_bold = Counter(
                semantic_emphasis_body(body, native=True)
                for line in text.splitlines()
                for delimiter in ("*", "**")
                for body in outside_math_delimiter(line, delimiter, native=True)
            )
            if "bold" not in item_waivers:
                missing_bold = markdown_bold - native_bold
                for body, count in sorted(missing_bold.items()):
                    errors.append(
                        f"{count} Markdown bold span(s) not represented as native Verso bold: {body!r}"
                    )
            source_tex = tex_payloads(source, native=False)
            native_tex = tex_payloads(text, native=True)
            if source_tex != native_tex and "tex" not in item_waivers:
                mismatch = next(
                    (
                        index
                        for index, (source_body, native_body) in enumerate(
                            zip(source_tex, native_tex), start=1
                        )
                        if source_body != native_body
                    ),
                    min(len(source_tex), len(native_tex)) + 1,
                )
                source_body = source_tex[mismatch - 1] if mismatch <= len(source_tex) else None
                native_body = native_tex[mismatch - 1] if mismatch <= len(native_tex) else None
                errors.append(
                    "TeX payload mismatch at expression "
                    f"{mismatch}: source={source_body!r}, native={native_body!r} "
                    f"(counts {len(source_tex)} != {len(native_tex)})"
                )
    for line_number, line in enumerate(text.splitlines(), start=1):
        if FOOTNOTE_MARKER.search(line):
            errors.append(
                f"line {line_number}: legacy literal footnote marker; use an item-scoped native Verso named footnote"
            )
        match = RAW_DOLLAR.search(FOOTNOTE_MARKER.sub("", line))
        if match:
            errors.append(
                f"line {line_number}: raw Markdown TeX dollar; use native Verso `$`/`$$` backtick syntax"
            )
        if MARKDOWN_TABLE_SEPARATOR.match(line):
            errors.append(
                f"line {line_number}: raw Markdown pipe table; use the native Verso `:::table` directive"
            )
    return errors


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="+", type=Path)
    args = parser.parse_args()
    failed = False
    for input_path in args.paths:
        paths = sorted(input_path.rglob("Content.lean")) if input_path.is_dir() else [input_path]
        for path in paths:
            errors = validate(path)
            if errors:
                failed = True
                for error in errors:
                    print(f"{path}: {error}")
    if failed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
