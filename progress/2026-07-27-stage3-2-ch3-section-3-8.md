# Stage 3.2 claim audit: Chapter 3, Section 3.8

Reviewed on 2026-07-27 against the coverage, definition-integrity, anti-vacuity,
and statement-fidelity gates in `PLAN.md`, from exact base
`3b9b43ceb75e9948d851e42716967fdec8fe6356`.

## Scope

The audit covers the eight contiguous tracker records strictly between
`Chapter3/Discussion_after_Theorem3.7.1` and `Chapter3/Introduction_to_3.9`:

- `Chapter3/Introduction_to_3.8`
- `Chapter3/Theorem3.8.1`
- `Chapter3/Lemma3.8.2`
- `Chapter3/Discussion_proof_of_Theorem3.8.1`
- `Chapter3/Problem3.8.3`
- `Chapter3/Problem3.8.4`
- `Chapter3/Problem3.8.5`
- `Chapter3/Remark3.8.6`

Every exact source blob and all thirteen Lean providers were read in full. The
providers are `Theorem3_8_1`, `Lemma3_8_2`, `Problem3_8_3`, the eight-file
`Problem3_8_4` chain (`Problem3_8_4`, `Cancellation`, `Descent`, `Finite`,
`Functoriality`, `General`, `Main`, and `Power`), `Problem3_8_5`, and
`Remark3_8_6` (thirteen files total).

## Result

The 29 source claim units are recorded in `progress/items.json` with these
dispositions:

- 18 `formalized`
- 10 `covered_elsewhere`
- 1 `non_formalizable` (the section heading)
- 0 `gap`

The section has no Stage 3.3 proof obligation. In particular:

- Theorem 3.8.1 has genuine existence and uniqueness endpoints, including the
  permutation and isomorphisms of matched summands.
- Lemma 3.8.2 is stronger than the source proof: Fitting decomposition proves
  the endomorphism dichotomy over an arbitrary field, and the finite-sum result
  is implemented without an algebraic-closure hypothesis.
- Problem 3.8.3 exposes named arbitrary-field wrappers for both lemma parts and
  both Krull-Schmidt endpoints.
- Both parts of Problem 3.8.4 have arbitrary-extension endpoints. The proof
  descends to a finitely generated subalgebra, specializes to a finite residue
  extension using Zariski's lemma, then applies the formalized power and
  Krull-Schmidt cancellation results. A direct summand is represented by a
  split injection, so part (ii) is not weakened.
- Problem 3.8.5 uses the literal algebras/modules of periodic and antiperiodic
  continuous real functions. Both are indecomposable, they are not isomorphic,
  and their binary direct sums are explicitly linearly equivalent.
- Remark 3.8.6 is covered both negatively by the Problem 3.8.5 counterexample
  and positively by existence and uniqueness of indecomposable decompositions
  for Artinian and Noetherian modules, the standard equivalent finite-length
  formulation. `Module.length` supplies the uniform filtration bound.

The terminal correction regenerates the three shifted source blobs from their
exact source spans: the proof discussion is page 55 lines 7–10, Problem 3.8.3
is page 55 lines 11–12, and Problem 3.8.4 runs from page 55 line 13 through page
56 line 4. The synchronized tracker records now mark those blobs verified and
fully covered. Stale regression references #7495, #7532, #7533, and the resolved
Remark 3.8.6 fidelity reference #7185 are removed because the exact providers
build cleanly. The seven mathematical records are promoted to
`dependency_trimmed`; the organizational heading is terminal
`non_formalizable`, as required by `PLAN.md`.

## Declaration and axiom audit

After stripping comments, the thirteen providers contain 102 declaration heads
(84 public and 18 private). Every declaration body was inspected in the full-file
read. A source scan found no `sorry`, `admit`, `axiom`, or `unsafe` token in the
providers.

A fresh scratch-import `#print axioms` audit covered all 26 public headline and
proof-chain results used by the claim inventory: the four Theorem/Lemma results,
four Problem 3.8.3 wrappers, nine Problem 3.8.4 cancellation/descent/finite/general
results, four Problem 3.8.5 results, and five finite-length results. Every one
reports exactly `[propext, Classical.choice, Quot.sound]`; none depends on
`sorryAx` or a project-specific axiom. The scratch file was removed after the
check.

## Validation

- Exact provider build: `lake build` on all thirteen scoped modules succeeds
  (8,593 jobs; linter warnings only).
- Full chapter build: `lake build EtingofRepresentationTheory.Chapter3`
  succeeds (8,692 jobs; pre-existing linter warnings only).

The corrected terminal stack keeps the 29-unit claim inventory intact while
synchronizing exact source spans, blobs, coverage/fidelity fields, resolved
issue fields, and terminal workflow statuses.
