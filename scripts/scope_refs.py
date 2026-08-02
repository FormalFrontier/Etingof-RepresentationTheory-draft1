#!/usr/bin/env python3
"""Shared helpers for Markdown scope-document references."""

import re


def github_heading_slug(heading: str) -> str:
    """Return GitHub's fragment form for the characters used in scope headings."""
    spaces_replaced = re.sub(r"\s", "-", heading.strip().lower())
    return "".join(
        char
        for char in spaces_replaced
        if char.isalpha() or char.isdecimal() or char in "-_"
    )
