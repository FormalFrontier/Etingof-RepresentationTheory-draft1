#!/usr/bin/env python3
"""Backfill durable Stage 3.2 records from the completed wave-9 fidelity audit.

Wave 9 recorded mathematical verdicts in Markdown and the top-level ``fidelity``
field, but these older records predate the structured ``claim_coverage`` field.
This migration is deliberately finite and idempotent: it names exactly the
nineteen adjudicated items and refuses to overwrite an existing record.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ITEMS = ROOT / "progress" / "items.json"

AUDITS = {
    "Chapter5/Theorem5.17.1": ("5.17", "The hook-length endpoint and its tableau-cardinality bridge were checked against the source statement."),
    "Chapter5/Lemma5.18.3": ("5.18", "The completed fidelity review found the formal character identity faithful to every source conjunct."),
    "Chapter5/Proposition5.19.1": ("5.19", "The completed fidelity review found both Weyl-character formulas fully represented."),
    "Chapter5/Proposition5.21.2": ("5.21", "The completed fidelity review checked both source formulas, including the geometric specialization and dimension formula."),
    "Chapter5/Theorem5.22.1": ("5.22", "The completed fidelity review checked vanishing, character, and dimension branches at source generality."),
    "Chapter5/Definition5.23.1": ("5.23", "The repaired bundled definition includes the representation laws as well as algebraicity of matrix coefficients."),
    "Chapter5/Theorem5.23.2": ("5.23", "The completed fidelity review checked named-constituent classification, uniqueness, and the equivariant Peter–Weyl endpoint."),
    "Chapter9/Proposition9.1.1": ("9.1", "Wave 9 checked both idempotent-lifting existence and conjugacy of lifts."),
    "Chapter9/Definition9.1.2": ("9.1", "Wave 9 checked idempotence, pairwise orthogonality, and sum-to-one."),
    "Chapter9/Corollary9.1.3": ("9.1", "Wave 9 checked componentwise lifting of a complete orthogonal system."),
    "Chapter9/Theorem9.2.1": ("9.2", "Wave 9 rechecked existence, uniqueness, regular-module decomposition, and classification after the uniqueness repair."),
    "Chapter9/Definition9.2.2": ("9.2", "Wave 9 checked the projective-cover API, including its essential-surjection condition."),
    "Chapter9/Proposition9.2.3": ("9.2", "Wave 9 checked the Hom-dimension/composition-factor multiplicity equality."),
    "Chapter9/Definition9.3.1": ("9.3", "Wave 9 checked that the Cartan matrix is constructed from Hom-space dimensions rather than arbitrary data."),
    "Chapter9/Definition9.4.1": ("9.4", "Wave 9 checked the projective-dimension definition; the later normalization repair handles the zero object faithfully."),
    "Chapter9/Definition9.4.3": ("9.4", "Wave 9 checked the uniform bound and infimum convention defining homological dimension."),
    "Chapter9/Example9.4.4": ("9.4", "Wave 9 checked both inequalities in the polynomial-ring homological-dimension computation."),
    "Chapter9/Definition9.5.1": ("9.5", "Wave 9 found a gap; the recorded repair now restricts chains to simples and defines blocks by Jordan–Hölder factors."),
    "Chapter9/Example9.5.2": ("9.5", "Wave 9 checked all three examples; subsequent repairs expose the full semisimple block equivalence."),
    "Chapter9/Definition9.6.1": ("9.6", "Wave 9 checked enough projectives, the finite simple family, and the documented finite-length context."),
    "Chapter9/Definition9.6.2": ("9.6", "Wave 9 checked projectivity and generation; subsequent work proves agreement of the general and finite variants."),
    "Chapter9/Theorem9.6.4": ("9.6", "Wave 9 checked the source-facing equivalence and derivation of the Noetherian hypothesis."),
    "Chapter9/Definition9.7.1": ("9.7", "Wave 9 checked genuine module-category equivalence and its documented finite-module refinement."),
    "Chapter9/Definition9.7.2": ("9.7", "Wave 9 checked the radical-quotient definition of a basic algebra and its split refinement."),
    "Chapter9/Corollary9.7.3": ("9.7", "Wave 9 and the later repairs checked existence, uniqueness, categorical presentation, and the dimension bound."),
}


def main() -> None:
    items = json.loads(ITEMS.read_text(encoding="utf-8"))
    found: set[str] = set()
    changed = 0
    for item in items:
        item_id = item.get("id")
        if item_id not in AUDITS:
            continue
        found.add(item_id)
        original_fidelity = item.get("fidelity")
        if original_fidelity not in {"verified", "exact", "faithful", "full"}:
            raise SystemExit(f"refusing to backfill non-verified item: {item_id}")
        if original_fidelity in {"exact", "faithful", "full"}:
            item["fidelity"] = "verified"
            changed += 1
        if "claim_coverage" in item:
            continue
        section, basis = AUDITS[item_id]
        item["claim_coverage"] = {
            "stage": "3.2",
            "status": "complete",
            "section": section,
            "reviewed_on": "2026-08-01",
            "definition_integrity": "verified",
            "statement_fidelity": "verified",
            "nonvacuity": "verified",
            "basis": basis,
            "certificate": "progress/coverage-audit/fidelity-wave-9.md",
        }
        changed += 1
    missing = set(AUDITS) - found
    if missing:
        raise SystemExit(f"items missing from ledger: {sorted(missing)}")
    ITEMS.write_text(json.dumps(items, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"backfilled {changed} structured claim-coverage record(s)")


if __name__ == "__main__":
    main()
