#!/usr/bin/env python3
"""Run the complete local gate before materializing or publishing either repository."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CLEAN = ROOT / "clean-code/release"
VERSO = ROOT / "verso/release"


def run(arguments: list[str], *, cwd: Path = ROOT, stdout=None) -> None:
    subprocess.run(arguments, cwd=cwd, stdout=stdout, check=True)


def available_declarations() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    proposals = ROOT / "manifests/alignment/cleanroom-proposals.jsonl"
    for line in proposals.read_text(encoding="utf-8").splitlines():
        proposal = json.loads(line)
        module = proposal.get("new_module")
        declaration = proposal.get("new_fqn")
        if not module or not declaration:
            continue
        source = CLEAN / (module.replace(".", "/") + ".lean")
        if source.is_file():
            rows.append({"declaration": declaration})
    return rows


def assert_private_sources_exact() -> None:
    pairs = (
        (ROOT / "verso/source-markdown", VERSO / "source-markdown"),
        (ROOT / "verso/metadata", VERSO / "metadata"),
    )
    for source, released in pairs:
        source_files = {
            path.relative_to(source): path
            for path in source.rglob("*")
            if path.is_file()
        }
        released_files = {
            path.relative_to(released): path
            for path in released.rglob("*")
            if path.is_file()
        }
        if source_files.keys() != released_files.keys():
            missing = sorted(set(source_files) - set(released_files))
            extra = sorted(set(released_files) - set(source_files))
            raise SystemExit(
                f"private source corpus differs in file set: missing={missing[:10]}, extra={extra[:10]}"
            )
        changed = [
            str(relative)
            for relative in sorted(source_files)
            if source_files[relative].read_bytes() != released_files[relative].read_bytes()
        ]
        if changed:
            raise SystemExit(
                f"private source corpus is not byte-identical; changed={changed[:10]}"
            )


def main() -> None:
    assert_private_sources_exact()
    run(
        [
            sys.executable,
            str(ROOT / "validate_cleanroom_responses.py"),
            str(ROOT / "clean-room-packets"),
            str(ROOT / "verso/source-markdown"),
            str(ROOT / "manifests/alignment/cleanroom-private-mapping.jsonl"),
            str(ROOT / "manifests/alignment/cleanroom-proposals.jsonl"),
        ]
    )
    run(
        [
            sys.executable,
            str(ROOT / "validate_alignment_adjudications.py"),
            "--require-all",
            str(ROOT / "alignment-adjudication-packets"),
        ]
    )
    run(
        [
            sys.executable,
            str(ROOT / "merge_alignment_adjudications.py"),
            str(ROOT / "alignment-adjudication-packets"),
            str(ROOT / "manifests/alignment/alignment-edges.jsonl"),
            str(ROOT / "manifests/alignment/adjudicated-alignment-edges.jsonl"),
        ]
    )
    proposals = [
        json.loads(line)
        for line in (ROOT / "manifests/alignment/cleanroom-proposals.jsonl")
        .read_text(encoding="utf-8")
        .splitlines()
        if line.strip()
    ]
    available = available_declarations()
    if len(available) != len(proposals):
        available_names = {row["declaration"] for row in available}
        missing = [row["new_fqn"] for row in proposals if row["new_fqn"] not in available_names]
        raise SystemExit(
            f"clean release is incomplete: {len(missing)} reviewed declarations lack a module; "
            f"examples={missing[:10]}"
        )
    run(["lake", "build", "RepresentationTheory", "alignmentExport"], cwd=CLEAN)
    run(
        [
            sys.executable,
            str(ROOT / "validate_clean_release_exports.py"),
            str(CLEAN),
            str(ROOT / "manifests/alignment/cleanroom-proposals.jsonl"),
        ]
    )
    run(
        [
            sys.executable,
            str(ROOT / "validate_native_verso.py"),
            str(ROOT / "conversion-packets"),
        ]
    )
    run(
        [
            sys.executable,
            str(ROOT / "validate_clean_release_source_refs.py"),
            str(CLEAN),
            str(ROOT / "manifests/alignment/cleanroom-proposals.jsonl"),
            str(ROOT / "manifests/alignment/adjudicated-alignment-edges.jsonl"),
            str(ROOT / "manifests/alignment/source-nodes.jsonl"),
        ]
    )
    run(
        [
            sys.executable,
            str(ROOT / "scan_clean_release.py"),
            str(CLEAN),
            str(ROOT / "verso/source-markdown"),
        ]
    )

    with tempfile.TemporaryDirectory(prefix="etingof-release-gate-") as temporary:
        temporary_root = Path(temporary)
        available = temporary_root / "available-declarations.json"
        available.write_text(
            json.dumps(available_declarations(), sort_keys=True), encoding="utf-8"
        )
        run(
            [
                sys.executable,
                str(ROOT / "assemble_verso_release.py"),
                str(ROOT / "verso/metadata"),
                str(ROOT / "conversion-packets"),
                str(VERSO),
                "--alignment-edges",
                str(ROOT / "manifests/alignment/adjudicated-alignment-edges.jsonl"),
                "--source-nodes",
                str(ROOT / "manifests/alignment/source-nodes.jsonl"),
                "--cleanroom-proposals",
                str(ROOT / "manifests/alignment/cleanroom-proposals.jsonl"),
                "--available-declarations",
                str(available),
                "--approved-items",
                str(ROOT / "manifests/book/approved-verso-items.json"),
            ]
        )
        run(
            [
                sys.executable,
                str(ROOT / "validate_release_legal_metadata.py"),
                str(CLEAN),
                str(VERSO),
            ]
        )
        alignment = temporary_root / "alignment.json"
        with alignment.open("w", encoding="utf-8") as output:
            run(
                ["lake", "env", "lean", "--run", "AlignmentExport.lean"],
                cwd=CLEAN,
                stdout=output,
            )
        run(
            [
                sys.executable,
                "scripts/sync_formalization_panels.py",
                "--check",
                str(alignment),
            ],
            cwd=VERSO,
        )
        run([sys.executable, "scripts/build_site.py"], cwd=VERSO)
        run(
            [
                sys.executable,
                str(ROOT / "validate_rendered_formalization.py"),
                str(alignment),
                str(VERSO / "_out/html-multi"),
            ]
        )
        materializer = subprocess.run(
            [sys.executable, str(ROOT / "materialize_release_repositories.py"), "--self-test"],
            text=True,
            capture_output=True,
            check=True,
        )
        materializer_report = json.loads(materializer.stdout)

    html_pages = len(list((VERSO / "_out/html-multi").rglob("index.html")))
    print(
        json.dumps(
            {
                "available_declarations": len(available_declarations()),
                "html_pages": html_pages,
                "materializer": materializer_report["self_test"],
                "derived_clean_git_rev": materializer_report["derived_clean_git_rev"],
                "status": "passed",
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
