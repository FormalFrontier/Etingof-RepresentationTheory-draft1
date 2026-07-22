Stage 3.7 **coverage-arm audit** of **Problem 5.16.1** (branching rules for
`Sₙ`: restriction and induction of Specht modules) at sub-part granularity.
This continues the §5.16/§5.24 symmetric-group audit sweep (siblings #7328
5.24.1, #7334 5.24.2 in flight; §4.12 audits already merged).

## Current state

- Blob: `blobs/Chapter5/Problem5.16.1.md`. Two sub-parts:
  - (a) `Res_{S_{n-1}}^{S_n} V_μ = ⨁_{λ ∈ R(μ)} V_λ` (remove one square).
  - (b) `Ind_{S_{n-1}}^{S_n} V_μ = ⨁_{λ ∈ A(μ)} V_λ` (add one square).
- Lean: `EtingofRepresentationTheory/Chapter5/Problem5_16_1.lean` (sorry-free,
  568 lines). The two headline theorems are stated at the **character /
  multiplicity** level, not as literal `⊕` module isomorphisms:
  - (a) `res_spechtModule_character` — for `μ ⊢ n+1`, `spechtModuleCharacter (n+1) μ (permEmb n σ) = ∑_{λ ∈ removeSquare μ} spechtModuleCharacter n λ σ`.
  - (b) `ind_spechtModule_multiplicity` — Frobenius-reciprocity pairing equals
    `if μ.toYoungDiagram ≤ la.toYoungDiagram then 1 else 0` (multiplicity 1 iff
    `μ ⊆ λ`, i.e. `λ ∈ A(μ)`).
- `progress/items.json` item `Chapter5/Problem5.16.1` has **no `coverage`
  field** yet (never run through the exercise-coverage ratchet).

## Deliverables

1. Decide `covered_full` / `covered_partial` / `not_started` for **each
   sub-part** (a) and (b) separately, recording a `derived` sub-part entry per
   part (mirror the structure used for `Chapter4/Problem4.12.2` and the §5.24
   audits): `claim`, `source_span`, `lean_decl` pointer(s), `coverage`.
2. Apply the Stage 3.2 step 6–7 fidelity tests (judged as a different model
   than formalized it): confirm the character-level statements are the faithful
   standard formalization of the module-decomposition claims and are
   **non-vacuous** (e.g. `removeSquare`/`addSquare` are the genuine
   remove/add-a-square sets; the pairing is real Frobenius reciprocity, not a
   tautology). If a sub-part's Lean statement is strictly weaker than the
   book's claim (e.g. a character identity that does not pin down the actual
   module decomposition where the book asserts an isomorphism), record it as
   `covered_partial` and open a follow-up `feature` issue describing the exact
   gap — do **not** wave it through as `covered_full`.
3. Set the parent `Chapter5/Problem5.16.1` roll-up `coverage` to the min over
   its sub-parts.

## Context

- This is a **read-only audit + items.json bookkeeping** task plus (if a gap is
  found) one follow-up issue. No new Lean proofs. Do not modify the sorry-free
  Lean unless fixing a genuine fidelity gap you discover.
- Character-level branching rules are the accepted faithful formalization in
  this project (the same convention was used for §5.24). The audit's job is to
  confirm faithfulness and non-vacuity, not to demand a literal `DirectSum`
  reconstruction — but flag it explicitly in the note if the isomorphism itself
  is only asserted at character level.
- Sibling audits for tone/format: the merged §4.12 audits (e.g. PR #7324) and
  the in-flight §5.24 audits (#7328, #7334).

## Verification

- `progress/items.json`: `Chapter5/Problem5.16.1` has a `coverage` field and a
  per-sub-part `derived` array; every accepted gap has a follow-up issue.
- `lake build EtingofRepresentationTheory.Chapter5.Problem5_16_1` still
  succeeds (unchanged unless a fidelity fix was needed).
- A progress file records the audit decision and any follow-up issue numbers.
