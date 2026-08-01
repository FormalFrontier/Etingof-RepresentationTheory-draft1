#!/usr/bin/env python3
"""Regression tests for Stage 3.5 diagnostic classification."""

from __future__ import annotations

import sys
import unittest

import finalize_proof_polishing as review


class DiagnosticClassificationTests(unittest.TestCase):
    def test_real_multi_goal_message_blocks(self) -> None:
        message = (
            "The following tactic starts with 2 goals and ends with 1 goal, "
            "1 of which is not operated on."
        )
        kind = review.category(message)
        self.assertEqual(kind, "multi_goal_risk")
        self.assertEqual(review.DISPOSITIONS[kind], "blocking")

    def test_sorry_message_blocks(self) -> None:
        kind = review.category("declaration uses 'sorry'")
        self.assertEqual(kind, "proof_blocker")
        self.assertEqual(review.DISPOSITIONS[kind], "blocking")

    def test_unknown_message_fails_closed(self) -> None:
        kind = review.category("a future linter warning unknown to this certificate")
        self.assertEqual(kind, "unknown")
        self.assertEqual(review.DISPOSITIONS[kind], "blocking")


class SourceProofClassificationTests(unittest.TestCase):
    def test_private_source_declaration_is_retained(self) -> None:
        name = "_private.Example.Module.0.Example.privateLemma"
        self.assertTrue(review.dependency_review.is_surface_proof_name(name))

    def test_public_eq_prefix_is_retained(self) -> None:
        name = "Example.Namespace.eq_top_of_mem"
        self.assertTrue(review.dependency_review.is_surface_proof_name(name))

    def test_generated_helpers_are_excluded(self) -> None:
        for name in (
            "Example.theorem._proof_1_2",
            "Example.theorem._simp_1_3",
            "Example.theorem.match_1",
            "Example.theorem.eq_2",
            "Example.map.congr_simp",
        ):
            with self.subTest(name=name):
                self.assertFalse(review.dependency_review.is_surface_proof_name(name))

if __name__ == "__main__":
    sys.exit(unittest.main())
