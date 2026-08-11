#!/usr/bin/env python3
# Copyright (c) 2026 American Mathematical Society. All rights reserved.
"""Build the book after removing output left by earlier renders."""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    html = root / "_out" / "html-multi"
    if html.exists():
        shutil.rmtree(html)
    subprocess.run(["lake", "build"], cwd=root, check=True)
    subprocess.run(["lake", "exe", "book"], cwd=root, check=True)


if __name__ == "__main__":
    main()
