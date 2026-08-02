#!/usr/bin/env python3
"""Focused tests for the omission-scope checks in validate_items.py."""

import json

from scope_refs import github_heading_slug
from validate_items import ITEMS_PATH, validate_scope_ref


def test_slug_fidelity() -> None:
    assert github_heading_slug("Two  spaces and `proof_wanted`") == (
        "two--spaces-and-proof_wanted"
    )
    assert github_heading_slug("Example S₃") == "example-s"


def test_current_omission_refs() -> None:
    items = json.loads(ITEMS_PATH.read_text(encoding="utf-8"))
    refs = [
        claim.get("scope_ref")
        for item in items
        for claim in item.get("claim_coverage", {}).get("claims", [])
        if claim.get("verdict") == "intentional_omission"
    ]
    assert refs
    assert all(validate_scope_ref(ref) is None for ref in refs)
    assert validate_scope_ref(None) is not None
    assert validate_scope_ref("skipped-exercises.md#not-a-real-heading") is not None
    assert validate_scope_ref("../outside.md#heading") is not None


if __name__ == "__main__":
    test_slug_fidelity()
    test_current_omission_refs()
