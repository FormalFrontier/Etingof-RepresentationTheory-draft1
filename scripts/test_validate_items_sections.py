#!/usr/bin/env python3
"""Focused tests for source-order section inference in validate_items.py."""

from validate_items import partition_order_errors, sections_from_item_order


def test_editorial_item_inherits_current_section() -> None:
    sections = sections_from_item_order([
        {"id": "Chapter5/Definition5.8.1"},
        {"id": "Chapter5/Discussion_verification_of_Ind"},
        {"id": "Chapter5/Theorem5.9.1"},
    ])
    assert sections["Chapter5/Discussion_verification_of_Ind"] == "5.8"


def test_filename_style_section_updates_context() -> None:
    sections = sections_from_item_order([
        {"id": "Chapter4/Example4_3_Q8"},
        {"id": "Chapter4/Discussion_after_example"},
    ])
    assert sections["Chapter4/Discussion_after_example"] == "4.3"


def test_chapter_boundary_resets_context() -> None:
    sections = sections_from_item_order([
        {"id": "Chapter4/Theorem4.10.1"},
        {"id": "Chapter5/Introduction"},
        {"id": "Chapter5/Definition5.1.1"},
    ])
    assert sections["Chapter5/Introduction"] is None
    assert sections["Chapter5/Definition5.1.1"] == "5.1"


def test_back_reference_does_not_regress_source_context() -> None:
    sections = sections_from_item_order([
        {"id": "Chapter5/Definition5.13.1"},
        {"id": "Chapter5/Discussion_proof_of_Theorem5.12.2"},
        {"id": "Chapter5/Discussion_following_proof"},
    ])
    assert sections["Chapter5/Discussion_following_proof"] == "5.13"


def test_partition_order_is_checked() -> None:
    ordered = [
        {"id": "Chapter1/First", "start_page": "1", "start_line": 1},
        {"id": "Chapter1/Second", "start_page": "2", "start_line": 1},
    ]
    assert partition_order_errors(ordered, ["1", "2"]) == []
    assert partition_order_errors(list(reversed(ordered)), ["1", "2"])


if __name__ == "__main__":
    test_editorial_item_inherits_current_section()
    test_filename_style_section_updates_context()
    test_chapter_boundary_resets_context()
    test_back_reference_does_not_regress_source_context()
    test_partition_order_is_checked()
