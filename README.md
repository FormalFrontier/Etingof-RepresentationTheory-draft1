# EtingofRepresentationTheory

## Project scope

The project aims to formalize the mathematical content of Etingof's representation
theory text. Deliberate exceptions are recorded in
[Intentional omissions and exercise scope](skipped-exercises.md). That document
distinguishes project-wide omissions from work that is merely incomplete or outside
the scope of a particular issue. Exercises deferred to a later import point, with
partial results recorded now, are tracked separately in
[Deferred reprises](deferred-reprises.md).

Project completion requires zero accidental `sorry` or `admit` terms and zero
project axioms. Every `proof_wanted` must instead be individually enumerated and
justified in the scope document, with matching machine-readable approval metadata
in `progress/items.json`. The currently approved Ado–Iwasawa marker in Remark
2.9.3 is non-blocking; no future marker inherits that exception automatically.
Run `scripts/check_proof_placeholders.py --enforce-completion` to check these
release criteria.

The mathematical formalization reached this completion gate on 2026-07-29. The
Lean import-DAG and bounded completeness passes closed on 2026-08-01, along with
a repository-wide diagnostic style pass. The scanner reports zero blocking
placeholders, the exercise ledger reports no untracked gaps, and the sole wanted
theorem is the explicitly approved Ado–Iwasawa scope marker. The proof-term
dependency review required by Stage 3.4 and proof-by-proof quality review
required by Stage 3.5 remain separate release tasks.

## Verification

`PROGRESS.md` records the completed stages and final metrics. The bounded audit
certificate is `progress/coverage-audit/completeness-audit-wave-1.md`; it
documents both the dry stopping rule and residual risk. The standard release
checks are the full `lake build`, `scripts/check_proof_placeholders.py
--enforce-completion`, and the item, dependency, exercise-coverage, and lint
validators under `scripts/`. Upstream-contribution triage is deliberately not
part of this project's plan.
