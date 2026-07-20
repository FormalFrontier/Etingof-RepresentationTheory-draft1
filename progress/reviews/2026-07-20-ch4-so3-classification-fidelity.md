# Review: Ch4 Problem 4.12.8 — SO(3) finite-subgroup classification fidelity + axiom cleanliness

**Issue:** #7002 (review, report-only)
**File:** `EtingofRepresentationTheory/Chapter4/Problem4_12_8.lean` (3536 lines)
**Book reference:** `blobs/Chapter4/Problem4.12.8.md`
**Date:** 2026-07-20 (UTC)

## Verdict

**SOUND.** Every audited headline lemma is sorry-free and depends only on the standard
`[propext, Classical.choice, Quot.sound]` axiom set — no `sorryAx`, no stray custom axiom. All
signatures faithfully state the book's claim; no `def`/`instance` body is sorried and no
proposition is weakened to `True`. The only defects found were **stale docstrings** falsely
asserting a "remaining sorry"; these were trivial, isolated docstring corrections (the two
formerly in-flight PRs #6998/#6999 are now merged, so no conflict risk) and have been fixed in
this same PR.

Note: since planning, PRs #6998 (`simpleGroup_card60_exists_index_five`) and #6999
(`exists_octahedral_faithful_hom`) both **merged** (2026-07-20T17:21). The file therefore now has
**zero** real `sorry` terms (comment-stripped scan). The two theorems the issue asked to treat as
report-only were audited as merged lemmas.

## 1. Axiom-cleanliness audit

`#print axioms` was run on every headline declaration via a scratch importer. All report exactly
`[propext, Classical.choice, Quot.sound]`:

| Declaration | Axioms |
|---|---|
| `so3_finite_subgroup_classification` (public (a)) | clean |
| `su2_finite_subgroup_double_cover` (public (b)) | clean |
| `so3_classification_aux` | clean |
| `pole_order_data` | clean |
| `pole_order_diophantine` | clean |
| `so3_cyclic_of_poleData` | clean |
| `so3_dihedral_of_poleData` | clean |
| `so3_tetrahedral_of_poleData` | clean |
| `octahedral_order3_pole_neg_mem_orbit` | clean |
| `exists_octahedral_faithful_hom` | clean |
| `so3_octahedral_of_poleData` | clean |
| `isSimpleGroup_of_card_sixty_of_nontrivial_sylow5` | clean |
| `simpleGroup_card60_exists_index_five` | clean |
| `so3_icosahedral_G_simple` | clean |
| `so3_icosahedral_card` | clean |
| `faithful_perm5_of_simple_index_five` | clean |
| `so3_icosahedral_exists_faithful_perm5` | clean |
| `so3_icosahedral_of_poleData` | clean |

("clean" = `depends on axioms: [propext, Classical.choice, Quot.sound]`.)

Comment-stripped `sorry`/`admit` scan of the file: **0** real occurrences (all remaining textual
`sorry` tokens are inside docstrings/comments; three of those were the stale claims fixed below).

## 2. Statement-fidelity audit vs `blobs/Chapter4/Problem4.12.8.md`

The book lists five families (blob lines 3–11) and derives them by the pole-counting identity
`2(1 − 1/n) = ∑ᵢ (1 − 1/mᵢ)` (blob line 17). Each Lean statement matches:

- **`so3_finite_subgroup_classification`** — the exact 5-way disjunction: `IsCyclic G`,
  `∃ n, G ≃* DihedralGroup n`, `G ≃* alternatingGroup (Fin 4)` (A₄),
  `G ≃* Equiv.Perm (Fin 4)` (S₄), `G ≃* alternatingGroup (Fin 5)` (A₅). Matches blob items (1)–(5)
  with the correct group identifications (tetrahedron=A₄, cube/octahedron=S₄,
  dodecahedron/icosahedron=A₅).
- **`pole_order_diophantine` / `pole_order_data`** — encode the counting identity
  `2(1 − 1/n) = ∑ᵢ (1 − 1/mᵢ)` and pin the multiset of pole orders. Faithful to blob line 17.
- **`so3_tetrahedral_of_poleData`** — hypothesis `m = {2,3,3}`, conclusion `G ≃* A₄`; the counting
  forces `|G| = 12`. Correct (`½ + ⅔ + ⅔ = ... ⇒ n = 12`).
- **`exists_octahedral_faithful_hom` / `so3_octahedral_of_poleData`** — `m = {2,3,4}`, `|G| = 24`,
  faithful `G ↪ Equiv.Perm (Fin 4) = S₄`. Correct; the "4 body diagonals of the cube" action.
- **`octahedral_order3_pole_neg_mem_orbit`** — support lemma: for `|G| = 24`, the antipode of an
  order-3 pole lies in its orbit (Sylow n₃ = 4). Faithful to the octahedral pole geometry.
- **`so3_icosahedral_card`** — `m = {2,3,5}` forces `|G| = 60` (checked:
  `½ + ⅔ + ⅘ = 59/30 = 2(1 − 1/60)`). Correct.
- **`isSimpleGroup_of_card_sixty_of_nontrivial_sylow5`** — order-60 group with `n₅ > 1` is simple.
  Standard group-theory input to the A₅ identification; hypotheses/conclusion faithful.
- **`simpleGroup_card60_exists_index_five`** — a simple group of order 60 has an index-5 subgroup.
  Correct (Sylow n₂ = 5 counting).
- **`so3_icosahedral_G_simple` / `faithful_perm5_of_simple_index_five` /
  `so3_icosahedral_exists_faithful_perm5` / `so3_icosahedral_of_poleData`** — the A₅ disjunct:
  `G` simple ⇒ index-5 subgroup ⇒ faithful coset action `G ↪ Equiv.Perm (Fin 5)` ⇒ image of order
  60 has index 2 in S₅ ⇒ `= A₅` (`Equiv.Perm.eq_alternatingGroup_of_index_eq_two`). Faithful; the
  geometric "five inscribed tetrahedra" set is realized via the equivalent group-theoretic route.
- **`su2_finite_subgroup_double_cover`** (part (b)) — parameterized on a given homomorphism
  `h : SU(2) → SO(3)` with kernel `{±1}` (the double cover, blob line 24 "use the homomorphism
  SU(2) → SO(3)"); concludes `|H| = 2·|h(H)|` if `−1 ∈ H`, else `|H| = |h(H)|`. Faithful
  conditional formalization of the double-cover reduction; existence of `h` is taken as a
  hypothesis rather than constructed, which matches the book's "use the homomorphism" hint.

No `def`/`instance` body (`UnitSphere`, `IsPole`, `poleSet`, `fixedUnitVectors`, the `MulAction`
instances) is sorried; the clean `#print axioms` on all downstream theorems confirms no vacuity
leaks through the definitional layer. No proposition is weakened to `True`.

## 3. Defects found and disposition

Three stale docstrings falsely claimed a live `sorry` (all now false — the file is sorry-free):

1. Module docstring (line ~27): "Statements (faithful signatures, `sorry` proofs — a statement
   pass)". Corrected to state both parts are proved sorry-free.
2. `so3_icosahedral_exists_faithful_perm5` docstring (lines ~3331): "is the ONLY remaining
   `sorry`". Doubly stale — the theorem is proved, and it describes a *geometric construction* the
   proof never performs (the actual proof is the abstract simple-group / index-5 coset route).
   Rewritten to describe the actual proof and mark it sorry-free, keeping the geometric
   interpretation as motivation.
3. `so3_icosahedral_of_poleData` docstring (lines ~3359): "the sole remaining `sorry` is the
   geometric `5`-point action ...". Corrected to state all three components are proved sorry-free.

These are docstring/comment-only edits; `#print axioms` behaviour and build output are unchanged.
`lake build EtingofRepresentationTheory.Chapter4.Problem4_12_8` succeeds (exit 0) after the edits.

No follow-up `feature` issues were filed: no fidelity or soundness gap remains in any merged
lemma. The pre-existing 100-char long-line linter *warning* at line 3273 is untouched and out of
scope for this fidelity review.
