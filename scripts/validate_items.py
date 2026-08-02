#!/usr/bin/env python3
"""Validate items.json for Stage 1.5 contiguity: every line of every page
belongs to exactly one blob, with no gaps and no overlaps.

`derived` items (PLAN Stage 1.6) are an overlay on that partition rather than
members of it: they record a formalizable claim found inside an existing blob,
are keyed by `derived_from` instead of `id`, carry no line span, and are
skipped by the contiguity check."""

import json
import re
import sys
from functools import lru_cache
from pathlib import Path
from urllib.parse import unquote

from proof_wanted_policy import validate_item_approval
from scope_refs import github_heading_slug

REPO_ROOT = Path(__file__).resolve().parent.parent
PAGES_DIR = REPO_ROOT / "pages"
ITEMS_PATH = REPO_ROOT / "progress" / "items.json"
SCHEMA_PATH = Path(__file__).resolve().parent / "items_schema.json"

VALID_TYPES = {
    "theorem", "lemma", "proposition", "corollary",
    "definition", "example", "exercise", "remark",
    "discussion", "introduction", "preface", "notation",
    "bibliography", "index",
}

# Derived items (PLAN Stage 1.6) are an overlay on the text partition, not
# members of it: they record a formalizable claim found *inside* an existing
# blob, so they carry no line span and are skipped by the contiguity check.
DERIVED_TYPE = "derived"
DERIVED_REQUIRED_FIELDS = {"type", "derived_from", "source_span", "claim", "status"}
DERIVED_OPTIONAL_FIELDS = {
    "coverage", "coverage_issue", "last_updated", "lean_file", "lean_ref",
    "note", "stage3_4", "stage3_5",
}

# Audit and implementation metadata accumulated after the original Stage 1
# partition.  Keep this explicit so misspelled fields still produce warnings.
PARTITION_OPTIONAL_FIELDS = {
    "aristotle_project_id", "aristotle_projects", "attention_needed",
    "attention_note", "claim_coverage", "coverage", "coverage_issue",
    "coverage_note", "coverage_swept", "fidelity", "fidelity_decl",
    "fidelity_issue", "fidelity_note", "followup_issue",
    "has_true_hypothesis", "last_updated", "lean_decl", "lean_file",
    "lean_ref", "needs_statement", "note", "notes",
    "proof_wanted_approval", "reason", "sorries", "sorry_count",
    "sorry_free", "source_regression_note", "stage3_3", "stage3_4",
    "stage3_5", "status",
}

# PLAN Stage 3.6 requires every exercise item to carry one of these honest
# coverage states.  In particular, `status: sorry_free` is not a substitute:
# an exercise can have no matching Lean declaration and still be sorry-free.
VALID_EXERCISE_COVERAGE = {
    "covered_full",
    "covered_partial",
    "not_started",
    "non_formalizable",
}

VALID_CLAIM_VERDICTS = {
    "context_only",
    "covered_elsewhere",
    "formalized",
    "historical_context",
    "intentional_omission",
    "non_formalizable",
    "proof_route",
    "source_correction",
}

# Files in pages/ that are not actual page content
EXCLUDED_FILES = {"CONVENTIONS.md"}


@lru_cache
def markdown_heading_slugs(path: Path) -> frozenset[str]:
    """Read and cache the GitHub fragments of all headings in a Markdown file."""
    return frozenset(
        github_heading_slug(line.lstrip("#").strip())
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.startswith("#")
    )


def validate_scope_ref(scope_ref: object) -> str | None:
    """Return an error for a missing or non-resolving omission scope reference."""
    if not isinstance(scope_ref, str):
        return "intentional_omission claim has no string scope_ref"
    path_text, separator, fragment = scope_ref.partition("#")
    if not separator or not path_text or not fragment:
        return f"invalid omission scope_ref {scope_ref!r}"
    scope_path = (REPO_ROOT / path_text).resolve()
    try:
        scope_path.relative_to(REPO_ROOT.resolve())
    except ValueError:
        return f"omission scope_ref escapes the repository: {scope_ref!r}"
    if not scope_path.is_file():
        return f"invalid omission scope_ref {scope_ref!r}"
    if unquote(fragment) not in markdown_heading_slugs(scope_path):
        return f"omission scope_ref anchor does not resolve: {scope_ref!r}"
    return None


def get_page_order():
    """Return ordered list of logical page names matching the book's order."""
    mapping_path = REPO_ROOT / "pdf" / "pages" / "mapping.json"
    if mapping_path.exists():
        with open(mapping_path) as f:
            data = json.load(f)
        # mapping is raw_page -> logical_page; sort by raw page number
        pairs = sorted(data["mapping"].items(), key=lambda p: int(p[0]))
        return [logical for _, logical in pairs]

    # Fallback: frontmatter first, then numbered pages
    pages = []
    for p in sorted(PAGES_DIR.glob("frontmatter-*.md"),
                     key=lambda x: int(x.stem.split("-")[1])):
        pages.append(p.stem)
    for p in sorted(PAGES_DIR.glob("[0-9]*.md"),
                     key=lambda x: int(x.stem)):
        pages.append(p.stem)
    for p in sorted(PAGES_DIR.glob("backmatter-*.md"),
                     key=lambda x: int(x.stem.split("-")[1])):
        pages.append(p.stem)
    return pages


def get_page_files():
    """Return set of page names that have .md files (excluding non-page files)."""
    return {
        p.stem for p in PAGES_DIR.glob("*.md")
        if p.name not in EXCLUDED_FILES
    }


def load_items(path):
    with open(path) as f:
        return json.load(f)


def page_line_count(page_name):
    """Return the number of lines in a page's markdown file."""
    p = PAGES_DIR / f"{page_name}.md"
    if not p.exists():
        return None
    return sum(1 for _ in open(p))


def section_from_item_id(item_id):
    """Infer a numbered section such as ``4.10`` from a Chapter item ID.

    Both source-style dots (``Theorem4.10.2``) and filename-style underscores
    (``Example4_3_S4``) occur in the ledger. Items without a section number,
    such as ``Chapter4/Introduction``, return ``None``.
    """
    chapter_match = re.match(r"^Chapter(\d+)/(.*)$", item_id)
    if chapter_match is None:
        return None
    chapter, tail = chapter_match.groups()
    section_match = re.search(
        rf"(?<!\d){re.escape(chapter)}[._](\d+)(?:[._]|$)", tail
    )
    if section_match is None:
        return None
    return f"{chapter}.{section_match.group(1)}"


def expand_item_lines(item, page_order):
    """Expand an item into a set of (page, line) tuples it covers.

    Returns (set_of_tuples, list_of_errors).
    """
    errors = []
    covered = set()

    start_page = item["start_page"]
    end_page = item["end_page"]
    start_line = item["start_line"]
    end_line = item["end_line"]

    if start_page not in page_order_set:
        errors.append(f"  start_page '{start_page}' not in page order")
        return covered, errors
    if end_page not in page_order_set:
        errors.append(f"  end_page '{end_page}' not in page order")
        return covered, errors

    si = page_order.index(start_page)
    ei = page_order.index(end_page)

    if si > ei:
        errors.append(f"  start_page '{start_page}' comes after end_page '{end_page}'")
        return covered, errors

    for pi in range(si, ei + 1):
        page = page_order[pi]
        lc = page_line_count(page)
        if lc is None:
            errors.append(f"  page file pages/{page}.md does not exist")
            continue

        if pi == si and pi == ei:
            # Same page
            lo, hi = start_line, end_line
        elif pi == si:
            lo, hi = start_line, lc
        elif pi == ei:
            lo, hi = 1, end_line
        else:
            lo, hi = 1, lc

        if lo < 1:
            errors.append(f"  line {lo} < 1 on page {page}")
            lo = 1
        if lc is not None and hi > lc:
            errors.append(f"  end_line {hi} exceeds line count {lc} on page {page}")
            hi = lc
        if lo > hi:
            errors.append(f"  start_line {lo} > end_line {hi} on page {page}")
            continue

        for line in range(lo, hi + 1):
            covered.add((page, line))

    return covered, errors


def validate(items_path):
    errors = []
    warnings = []

    # --- Load items ---
    try:
        items = load_items(items_path)
    except json.JSONDecodeError as e:
        print(f"FATAL: items.json is not valid JSON: {e}", file=sys.stderr)
        return 1
    except FileNotFoundError:
        print(f"FATAL: {items_path} not found", file=sys.stderr)
        return 1

    if not isinstance(items, list):
        print("FATAL: items.json root must be an array", file=sys.stderr)
        return 1

    print(f"Loaded {len(items)} items from {items_path}")

    page_order = get_page_order()
    global page_order_set
    page_order_set = set(page_order)
    page_files = get_page_files()

    # --- Schema-level checks per item ---
    required_fields = {"id", "type", "title", "start_page", "end_page", "start_line", "end_line"}
    seen_ids = set()

    # Every partition id, collected up front so derived items can be checked
    # against parents that appear later in the array.
    partition_ids = {
        item["id"] for item in items
        if isinstance(item, dict) and "id" in item
    }
    derived_count = 0

    for i, item in enumerate(items):
        prefix = f"Item [{i}]"
        if not isinstance(item, dict):
            errors.append(f"{prefix}: not an object")
            continue

        # Derived items are keyed by `derived_from` rather than `id` and carry
        # no line span, so they get their own required-field set.
        if item.get("type") == DERIVED_TYPE:
            derived_count += 1
            parent = item.get("derived_from", f"<index {i}>")
            prefix = f"Derived item '{parent}'"

            missing = DERIVED_REQUIRED_FIELDS - set(item.keys())
            if missing:
                errors.append(f"{prefix}: missing fields: {missing}")
                continue

            extra = set(item.keys()) - DERIVED_REQUIRED_FIELDS - DERIVED_OPTIONAL_FIELDS
            if extra:
                warnings.append(f"{prefix}: unexpected fields: {extra}")

            if parent not in partition_ids:
                errors.append(
                    f"{prefix}: derived_from '{parent}' does not name any item"
                )
            continue

        item_id = item.get("id", f"<index {i}>")
        prefix = f"Item '{item_id}'"

        # Required fields
        missing = required_fields - set(item.keys())
        if missing:
            errors.append(f"{prefix}: missing fields: {missing}")
            continue

        # Extra fields
        extra = set(item.keys()) - required_fields - PARTITION_OPTIONAL_FIELDS
        if extra:
            warnings.append(f"{prefix}: unexpected fields: {extra}")

        # Duplicate IDs
        if item_id in seen_ids:
            errors.append(f"{prefix}: duplicate id")
        seen_ids.add(item_id)

        # Type enum
        if item["type"] not in VALID_TYPES:
            errors.append(f"{prefix}: invalid type '{item['type']}'")

        # Stage 3.6 exercise-coverage ratchet.  This is deliberately limited to
        # the mechanically checkable part of the requirement: presence of a
        # recognized state.  Whether the state is mathematically accurate still
        # requires the source/Lean review recorded in `coverage_note`.
        if item["type"] == "exercise":
            exercise_coverage = item.get("coverage")
            if exercise_coverage not in VALID_EXERCISE_COVERAGE:
                errors.append(
                    f"{prefix}: exercise coverage must be one of "
                    f"{sorted(VALID_EXERCISE_COVERAGE)}, got {exercise_coverage!r}"
                )

        # Scope-approved wanted theorems use the same narrow metadata policy as
        # the source scanner. A bare legacy `proof_wanted` status is rejected.
        errors.extend(validate_item_approval(item))

        # Stage 3.2 claim records must stay attached to the source section named
        # by their item ID. This catches a syntactically valid but dangerous
        # failure mode where a broad JSON patch lands on an earlier item with
        # the same generic fields.
        claim_coverage = item.get("claim_coverage")
        expected_section = section_from_item_id(item_id)
        if isinstance(claim_coverage, dict) and expected_section is not None:
            actual_section = claim_coverage.get("section")
            if actual_section is not None and str(actual_section) != expected_section:
                errors.append(
                    f"{prefix}: claim_coverage.section is {actual_section!r}, "
                    f"expected {expected_section!r} from the item id"
                )

        # Every deliberate omission must resolve to the project-wide scope
        # register. This keeps the prose policy and the machine ledger in sync.
        if isinstance(claim_coverage, dict):
            claims = claim_coverage.get("claims")
            if isinstance(claims, list):
                for claim_index, claim in enumerate(claims, 1):
                    if not isinstance(claim, dict):
                        continue
                    verdict = claim.get("verdict")
                    if verdict not in VALID_CLAIM_VERDICTS:
                        errors.append(
                            f"{prefix} claim {claim_index}: invalid verdict {verdict!r}"
                        )
                    if verdict == "intentional_omission":
                        scope_error = validate_scope_ref(claim.get("scope_ref"))
                        if scope_error is not None:
                            errors.append(
                                f"{prefix} claim {claim_index}: {scope_error}"
                            )

        # Line number types
        if not isinstance(item["start_line"], int):
            errors.append(f"{prefix}: start_line must be integer, got {type(item['start_line']).__name__}")
        if not isinstance(item["end_line"], int):
            errors.append(f"{prefix}: end_line must be integer, got {type(item['end_line']).__name__}")

    # --- Contiguity check (partition items only; derived items are an overlay) ---
    # Build complete coverage map: (page, line) -> item_id
    coverage = {}
    for item in items:
        if not isinstance(item, dict) or "id" not in item:
            continue
        if item.get("type") == DERIVED_TYPE:
            continue
        item_id = item["id"]
        covered, item_errors = expand_item_lines(item, page_order)
        for e in item_errors:
            errors.append(f"Item '{item_id}': {e}")
        for pl in covered:
            if pl in coverage:
                errors.append(
                    f"Overlap: page {pl[0]} line {pl[1]} claimed by "
                    f"both '{coverage[pl]}' and '{item_id}'"
                )
            else:
                coverage[pl] = item_id

    # --- Gap check: every line of every page file must be covered ---
    pages_referenced = set()
    for item in items:
        if not isinstance(item, dict) or item.get("type") == DERIVED_TYPE:
            continue
        sp = item.get("start_page")
        ep = item.get("end_page")
        if sp and ep and sp in page_order_set and ep in page_order_set:
            si = page_order.index(sp)
            ei = page_order.index(ep)
            for pi in range(si, ei + 1):
                pages_referenced.add(page_order[pi])

    # Exclude empty (0-line) pages — they have no content to cover
    uncovered_pages = {
        p for p in page_files - pages_referenced
        if (page_line_count(p) or 0) > 0
    }
    if uncovered_pages:
        # Sort for readable output
        sorted_uncovered = sorted(uncovered_pages, key=lambda p: (
            0 if p.startswith("frontmatter") else (2 if p.startswith("backmatter") else 1),
            int(p.split("-")[-1]) if "-" in p else int(p) if p.isdigit() else 0
        ))
        errors.append(
            f"Pages with no blob coverage ({len(uncovered_pages)}): "
            + ", ".join(sorted_uncovered)
        )

    gap_count = 0
    for page in page_order:
        if page not in page_files:
            continue  # Page file doesn't exist yet (still being transcribed)
        lc = page_line_count(page)
        if lc is None or lc == 0:
            continue  # Empty page (blank pages are OK)
        for line in range(1, lc + 1):
            if (page, line) not in coverage:
                gap_count += 1
                if gap_count <= 20:
                    errors.append(f"Gap: page {page} line {line} not covered by any blob")
    if gap_count > 20:
        errors.append(f"  ... and {gap_count - 20} more uncovered lines")

    # --- Report ---
    if warnings:
        print(f"\nWarnings ({len(warnings)}):")
        for w in warnings:
            print(f"  WARNING: {w}")

    if errors:
        print(f"\nErrors ({len(errors)}):", file=sys.stderr)
        for e in errors:
            print(f"  ERROR: {e}", file=sys.stderr)
        print(f"\nVALIDATION FAILED: {len(errors)} error(s)", file=sys.stderr)
        return 1

    total_lines = sum(
        page_line_count(p) or 0
        for p in page_order if p in page_files
    )
    print(f"\nCoverage: {len(coverage)}/{total_lines} lines across {len(page_files)} pages")
    print(
        f"Items: {len(items) - derived_count} blobs, {len(seen_ids)} unique IDs, "
        f"{derived_count} derived overlay items"
    )
    print("VALIDATION PASSED")
    return 0


if __name__ == "__main__":
    items_path = Path(sys.argv[1]) if len(sys.argv) > 1 else ITEMS_PATH
    sys.exit(validate(items_path))
