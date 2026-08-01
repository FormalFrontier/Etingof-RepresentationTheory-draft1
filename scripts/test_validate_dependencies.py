#!/usr/bin/env python3
"""Unit tests for the Stage 3.4 dependency validator."""

from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import tempfile
import unittest

import validate_dependencies as validator


class DependencyValidationTests(unittest.TestCase):
    def validate(self, items: list[dict], deps: dict[str, list[str]]) -> int:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            items_path = root / "items.json"
            deps_path = root / "dependencies.json"
            items_path.write_text(json.dumps(items), encoding="utf-8")
            deps_path.write_text(json.dumps(deps), encoding="utf-8")
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                return validator.validate(deps_path, items_path)

    def test_flagged_forward_dependency_is_valid(self) -> None:
        items = [
            {
                "id": "A",
                "stage3_4": {"forward_internal_dependencies": ["B"]},
            },
            {"id": "B"},
        ]
        self.assertEqual(self.validate(items, {"A": ["B"], "B": []}), 0)

    def test_unflagged_forward_dependency_is_rejected(self) -> None:
        items = [{"id": "A"}, {"id": "B"}]
        self.assertEqual(self.validate(items, {"A": ["B"], "B": []}), 1)

    def test_cycle_is_rejected_even_when_forward_edge_is_flagged(self) -> None:
        items = [
            {
                "id": "A",
                "stage3_4": {"forward_internal_dependencies": ["B"]},
            },
            {"id": "B"},
        ]
        self.assertEqual(self.validate(items, {"A": ["B"], "B": ["A"]}), 1)


if __name__ == "__main__":
    unittest.main()
