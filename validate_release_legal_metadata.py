#!/usr/bin/env python3
"""Validate the fixed legal and ownership contract of both release trees."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


PUBLIC_HEADER = "Copyright (c) 2026 mathlib-initiative. All rights reserved."
CHECKOUT_ACTION = "actions/checkout@11d5960a326750d5838078e36cf38b85af677262"
UPLOAD_ARTIFACT_ACTION = (
    "actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02"
)
DOWNLOAD_ARTIFACT_ACTION = (
    "actions/download-artifact@d3f86a106a0bac45b974a628896c90dbdf5c8093"
)
LEAN_ACTION = "leanprover/lean-action@38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9"
ELAN_REVISION = "464c9d28395000a2a0128e07081e4956d50eced2"
ELAN_SHA256 = "a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53"
PRIVATE_HEADER = (
    "Copyright (c) 2026 American Mathematical Society. All rights reserved."
)


def require_file(root: Path, relative: str, errors: list[str]) -> Path:
    path = root / relative
    if not path.is_file():
        errors.append(f"{root}: missing {relative}")
    return path


def require_text(path: Path, needles: tuple[str, ...], errors: list[str]) -> None:
    if not path.is_file():
        return
    text = path.read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            errors.append(f"{path}: missing required text {needle!r}")


def require_nonpersisting_checkouts(path: Path, errors: list[str]) -> None:
    if not path.is_file():
        return
    lines = path.read_text(encoding="utf-8").splitlines()
    checkouts = [
        index
        for index, line in enumerate(lines)
        if line.strip() == f"- uses: {CHECKOUT_ACTION} # v4"
    ]
    if not checkouts:
        errors.append(f"{path}: contains no pinned checkout steps")
        return
    for index in checkouts:
        following = "\n".join(lines[index + 1 : index + 4])
        if "persist-credentials: false" not in following:
            errors.append(f"{path}:{index + 1}: checkout must not persist repository credentials")


def validate_public(root: Path, errors: list[str]) -> None:
    if (root / "LICENSE").exists():
        errors.append(f"{root}: LICENSE must not exist; the required filename is LICENCE")
    licence = require_file(root, "LICENCE", errors)
    readme = require_file(root, "README.md", errors)
    notice = require_file(root, "NOTICE", errors)
    require_text(
        licence,
        ("Apache License", "Version 2.0, January 2004"),
        errors,
    )
    require_text(
        readme,
        (
            "Introduction to Representation Theory",
            "https://bookstore.ams.org/stml-59/",
            "does not quote or reproduce the book's prose",
            "do not reproduce the book's structure",
            "not a derivative work",
            "access-controlled",
            "not publicly available",
        ),
        errors,
    )
    require_text(notice, ("Copyright 2026 mathlib-initiative", "Apache License"), errors)
    public_ci = require_file(root, ".github/workflows/ci.yml", errors)
    notify = require_file(root, ".github/workflows/notify-verso.yml", errors)
    require_text(
        public_ci,
        (
            LEAN_ACTION,
            UPLOAD_ARTIFACT_ACTION,
            DOWNLOAD_ARTIFACT_ACTION,
            ELAN_REVISION,
            ELAN_SHA256,
            "test -f LICENCE",
        ),
        errors,
    )
    require_nonpersisting_checkouts(public_ci, errors)
    require_text(
        notify,
        (
            "workflow_run:",
            "VERSO_REPO_DISPATCH_TOKEN",
            "mathlib-initiative/EtingofRepresentationTheory-verso/dispatches",
            "formalization-updated",
        ),
        errors,
    )
    for path in root.rglob("*.lean"):
        if any(part in {".lake", "_out"} for part in path.relative_to(root).parts):
            continue
        text = path.read_text(encoding="utf-8")
        if PUBLIC_HEADER not in text[:300]:
            errors.append(f"{path}: missing mathlib-initiative copyright header")
        if "Copyright (c) 2026 Kim Morrison" in text:
            errors.append(f"{path}: retained superseded personal copyright header")
        if "file LICENSE" in text[:400]:
            errors.append(f"{path}: header names LICENSE instead of LICENCE")


def validate_private(root: Path, errors: list[str]) -> None:
    if (root / "LICENSE").exists():
        errors.append(f"{root}: LICENSE must not exist; the required filename is LICENCE")
    licence = require_file(root, "LICENCE", errors)
    readme = require_file(root, "README.md", errors)
    require_text(
        licence,
        (
            "Copyright © 2026 American Mathematical Society. All rights reserved.",
            "No permission is granted",
            "mathlib-initiative disclaims any copyright, ownership, or other",
        ),
        errors,
    )
    require_text(
        readme,
        (
            "Copyright © 2026 American Mathematical Society. All rights reserved.",
            "mathlib-initiative hosts this private repository on behalf of the American",
            "mathlib-initiative disclaims any copyright, ownership, or other",
            "mathlib-initiative/EtingofRepresentationTheory",
            "does not deploy GitHub Pages",
        ),
        errors,
    )
    source_markdown = root / "source-markdown"
    markdown_files = list(source_markdown.glob("*.md")) if source_markdown.is_dir() else []
    if len(markdown_files) != 235:
        errors.append(
            f"{root}: expected the complete 235-file Markdown corpus, found {len(markdown_files)}"
        )
    require_file(root, "source-markdown/chapter_map.json", errors)
    metadata_items = require_file(root, "metadata/items.json", errors)
    require_file(root, "metadata/book.json", errors)
    require_file(root, "metadata/overlays.json", errors)
    if metadata_items.is_file():
        item_count = len(json.loads(metadata_items.read_text(encoding="utf-8")).get("items", []))
        if item_count != 583:
            errors.append(f"{metadata_items}: expected 583 semantic items, found {item_count}")
    for path in root.rglob("*.lean"):
        if any(part in {".lake", "_out"} for part in path.relative_to(root).parts):
            continue
        text = path.read_text(encoding="utf-8")
        if PRIVATE_HEADER not in text[:240]:
            errors.append(f"{path}: missing AMS copyright header")
    alignment_export = require_file(root, "AlignmentExport.lean", errors)
    require_text(
        alignment_export,
        (PRIVATE_HEADER, "#define_source_refs_json", "IO.println sourceReferences"),
        errors,
    )
    build_script = require_file(root, "scripts/build_site.py", errors)
    require_text(build_script, (PRIVATE_HEADER,), errors)
    panel_sync = require_file(root, "scripts/sync_formalization_panels.py", errors)
    require_text(
        panel_sync,
        (PRIVATE_HEADER, "metadata/items.json", "## Formalization", "--check"),
        errors,
    )
    lakefile = require_file(root, "lakefile.toml", errors)
    require_text(lakefile, ('name = "alignmentExport"', 'root = "AlignmentExport"'), errors)
    release_setup = require_file(root, ".github/RELEASE_SETUP.md", errors)
    require_text(
        release_setup,
        (
            "Configure strict branch protection on `main`",
            "Private Verso CI / build",
            "Require branches to be up to date before merging",
            "requests an immediate head-bound squash merge",
        ),
        errors,
    )
    if release_setup.is_file():
        setup_text = release_setup.read_text(encoding="utf-8").lower()
        if "auto-merge" in setup_text:
            errors.append(f"{release_setup}: must not contain stale auto-merge setup wording")
    private_ci = require_file(root, ".github/workflows/ci.yml", errors)
    updater = require_file(root, ".github/workflows/update-formalization.yml", errors)
    require_text(
        private_ci,
        (
            LEAN_ACTION,
            UPLOAD_ARTIFACT_ACTION,
            ELAN_REVISION,
            ELAN_SHA256,
            "_out/html-multi",
            "AlignmentExport.lean",
            "sync_formalization_panels.py --check",
        ),
        errors,
    )
    require_nonpersisting_checkouts(private_ci, errors)
    require_text(
        updater,
        (
            "repository_dispatch:",
            "formalization-updated",
            "scripts/update_formalization_dependency.py",
            "AlignmentExport.lean",
            "scripts/sync_formalization_panels.py",
            "permissions:\n  contents: read",
            "persist-credentials: false",
            "  prepare_update:",
            "name: formalization-update-${{ github.run_id }}",
            '["git", "diff", "--name-only", "-z"]',
            '["git", "diff", "--cached", "--name-only", "-z"]',
            "os.path.islink(path)",
            '["git", "diff", "--check"]',
            '["git", "diff", "--cached", "--check"]',
            '["git", "diff", "--summary"]',
            '["git", "diff", "--cached", "--summary"]',
            "git diff --binary --full-index --",
            "git apply --index --whitespace=error-all",
            '["git", "show", "HEAD:lakefile.toml"]',
            "staged lakefile is not the exact canonical dispatched-SHA update",
            "gh auth setup-git --hostname github.com --force",
            "gh workflow run ci.yml",
            '"repos/$GITHUB_REPOSITORY/actions/runs/$run_id"',
            'if test "$conclusion" != success',
            "gh pr merge",
            "matching-refs/heads/automation/formalization-",
            "--disable-auto",
            "gh pr close",
            LEAN_ACTION,
            UPLOAD_ARTIFACT_ACTION,
            DOWNLOAD_ARTIFACT_ACTION,
            ELAN_REVISION,
            ELAN_SHA256,
        ),
        errors,
    )
    if updater.is_file():
        updater_text = updater.read_text(encoding="utf-8")
        require_nonpersisting_checkouts(updater, errors)
        if "git add " in updater_text:
            errors.append(f"{updater}: privileged updater must consume only the validated patch artifact")
        if "--auto" in updater_text:
            errors.append(f"{updater}: dependency updates must merge immediately, never via auto-merge")
        if updater_text.count('"repos/$GITHUB_REPOSITORY/git/ref/heads/main"') != 2:
            errors.append(f"{updater}: must query private main before branching and before merge")
        patch_scope = (
            "git diff --binary --full-index -- \\\n"
            "            lakefile.toml \\\n"
            "            IntroductionToRepresentationTheoryVerso/Content \\\n"
            '            > "$RUNNER_TEMP/formalization-update.patch"'
        )
        if patch_scope not in updater_text:
            errors.append(
                f"{updater}: validated patch must contain only the dependency pin and generated panels"
            )
        publisher_contract = (
            "  update:\n"
            "    if: ${{ always() }}\n"
            "    needs: prepare_update\n"
            "    permissions:\n"
            "      actions: write\n"
            "      contents: write\n"
            "      pull-requests: write\n"
            "    runs-on: ubuntu-latest\n"
            "    timeout-minutes: 360"
        )
        if publisher_contract not in updater_text or any(
            updater_text.count(permission) != 1
            for permission in ("actions: write", "contents: write", "pull-requests: write")
        ):
            errors.append(f"{updater}: write permissions must be isolated to one publishing job")
        ci_merge_order = (
            "private_base_sha=$(git rev-parse HEAD)",
            "checked_out_private_main=$(gh api \\",
            'if test "$private_base_sha" != "$checked_out_private_main"',
            'git switch -c "$branch"',
            "dispatch_started=$(date -u +%Y-%m-%dT%H:%M:%SZ)",
            'gh workflow run ci.yml --ref "$branch"',
            '--branch "$branch"',
            "--event workflow_dispatch",
            "--json databaseId,createdAt,headSha",
            '.headSha == \\"$head_sha\\" and .createdAt >= \\"$dispatch_started\\"',
            '"repos/$GITHUB_REPOSITORY/actions/runs/$run_id"',
            'if test "$conclusion" != success',
            "Public main advanced to $current_public_main before merge.",
            "current_private_main=$(gh api \\",
            'if test "$private_base_sha" != "$current_private_main"',
            'gh pr merge "$pr_url" \\',
            '--match-head-commit "$head_sha" --squash --delete-branch',
        )
        positions = [updater_text.find(marker) for marker in ci_merge_order]
        if any(position < 0 for position in positions) or positions != sorted(positions):
            errors.append(
                f"{updater}: must bind private main and the dispatched head run before merge"
            )
    workflow_text = "\n".join(
        path.read_text(encoding="utf-8")
        for path in sorted((root / ".github/workflows").glob("*.yml"))
    ).lower()
    for forbidden in ("actions/deploy-pages", "github-pages"):
        if forbidden in workflow_text:
            errors.append(f"{root}: private workflows contain public Pages deployment marker {forbidden!r}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("public_release", type=Path)
    parser.add_argument("private_release", type=Path)
    args = parser.parse_args()
    errors: list[str] = []
    validate_public(args.public_release.resolve(), errors)
    validate_private(args.private_release.resolve(), errors)
    print(json.dumps({"errors": len(errors)}, sort_keys=True))
    if errors:
        raise SystemExit("\n".join(errors[:100]))


if __name__ == "__main__":
    main()
