# Fidelity audit: Chapter 3, Problem 3.9.x cluster (#7034)

**Date:** 2026-07-20 (UTC)
**Reviewer:** review agent (session c71b2ba3)
**Scope:** `Problem3_9_1.lean` … `Problem3_9_5.lean`
**Method:** axiom-cleanliness first, then statement-vs-blob fidelity, then non-vacuity.
Mirrors the Ch8 homological audits (#7020, #7023).

## Overall verdict: **SOUND**

All five files are genuinely sorry-free (comment-stripped scan = 0 across all five),
every headline declaration is axiom-clean (`sorryAx`-free, no custom axioms), and every
statement is faithful to its book problem and non-vacuous. Four files carried a stale
"proofs are `sorry`" / "statement pass" docstring that predated their completed proofs;
those are corrected in this PR (docstring-only, no proof/signature/import/`def`-body
changes). `Problem3_9_1.lean` already had an accurate docstring.

## Axiom table

`#print axioms` on the headline declaration(s) of each file. Expected clean set is
`[propext, Classical.choice, Quot.sound]`; anything smaller is also clean.

| Declaration | Axioms |
|---|---|
| `Problem3_9_1.blockOp_mul_iff_isCocycle` | `propext, Quot.sound` |
| `Problem3_9_1.coboundaryOf_eq_zero_iff` | `propext, Quot.sound` |
| `Problem3_9_1.coboundaries_le_cocycles` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_1.iso_of_sub_mem_coboundaries` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_1.ext_iso_of_sub_smul_mem_coboundaries` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_1.irreducible_ext_iso_iff_proportional` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_2.ext1_self` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_2.ext1_subsingleton_of_ne` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_2.two_dim_is_extension` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_2.infinitely_many_indecomposables` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_3.simpleRep_isIrreducible` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_3.irreducible_isSimpleRep` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_3.ext1_simpleRep_vanishes_iff` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_3.two_dim_classification` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_4.isTrivial_of_ext1_subsingleton` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_5.cliffordAlgebra_zero_eq_exterior` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_5.isSemisimpleRing_of_nondegenerate` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_5.even_isMatrixAlgebra` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_5.odd_isSumMatrixAlgebra` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_5.not_isSemisimpleRing_of_degenerate` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_5.isSemisimpleRing_iff_nondegenerate` | `propext, Classical.choice, Quot.sound` |
| `Problem3_9_5.radicalQuotient_isClifford_of_degenerate` | `propext, Classical.choice, Quot.sound` |

No `sorryAx`. No custom axioms. **Axiom-clean.**

## Per-file fidelity findings

### Problem 3.9.1 — Extensions and `Ext¹` (SOUND)

Faithful to all four book parts. (a) the 1-cocycle condition `blockOp_mul_iff_isCocycle`;
(b) `coboundaryOf_isCocycle` + `coboundaryOf_eq_zero_iff` (vanishing ⇔ `A`-linear) +
`coboundaries_le_cocycles` (`B¹ ⊆ Z¹`); (c) `iso_of_sub_mem_coboundaries`; (d)
`irreducible_ext_iso_iff_proportional`, an honest strengthening. The book's part (d) says
"iso ⇔ `f`, `f'` proportional" and `ℙ Ext¹` parametrizes nontrivial classes; the Lean form
pins "proportional" down to a **nonzero** ratio `∃ c ≠ 0, f − c • f' ∈ B¹`. The docstring
explains why the `c ≠ 0` constraint is essential (a spurious `c = 0` would only assert
`f ∈ B¹` and make the naive `iff` false), and that algebraic closedness enters through Schur's
lemma (`Corollary_2_3_10`). Non-vacuous: `IsCocycle`, `coboundaries`, `Ext1`, `IntertwinesExt`
are all real definitions; no `def`/data is stubbed. Docstring already accurate ("All parts are
proved (`sorry`-free)"); untouched.

### Problem 3.9.2 — Polynomial algebra + zero-multiplication algebra (SOUND)

(a) `ext1_self` (`Ext¹(Vₐ,Vₐ) ≅ ℂⁿ`) and `ext1_subsingleton_of_ne`
(`Ext¹(Vₐ,V_b) = 0` for `a ≠ b`), plus the 2-dimensional classification
`two_dim_is_extension` (every 2-dim rep is an extension of two 1-dim reps). (b)
`infinitely_many_indecomposables` (for `n > 1`, infinitely many pairwise-nonisomorphic
indecomposables). The 1-dim reps `Vₐ = A ⧸ 𝔪ₐ` and the algebra `B = zeroMulAlg` (a
`RingQuot` of `FreeAlgebra`) are genuinely constructed; the indecomposable family `Cyc n k`
carries real `Module (zeroMulAlg n)` instances. Non-vacuous. **Docstring corrected**
(was "Statement pass: … proofs are `sorry`").

### Problem 3.9.3 — Path algebras / quiver representations (SOUND)

Reuses `Etingof.QuiverRepresentation` and the Ch6.9 `Ext¹`/simple infrastructure.
`simpleRep_isIrreducible` + `irreducible_isSimpleRep` (irreducibles are exactly the vertex
simples `S_i`, for finite acyclic `Q`); `ext1_simpleRep_vanishes_iff` (`Ext¹(S_i,S_j) = 0 ⇔`
no arrow `i → j`); `two_dim_classification`. The acyclicity/finiteness hypotheses are genuinely
used (documented), so the statements are not over-strengthened into triviality. `IsIrreducible`
and `NoOrientedCycles` are real predicates. Non-vacuous. **Docstring corrected**
(was "Statement pass: … the proofs are `sorry`").

Note: build emits pre-existing lint warnings on this file (an unused `[DecidableEq Q]` on
`two_dim_classification`, a long line at 435, two `show`-vs-`change` style hints). Cosmetic
only; out of scope for a report-only fidelity audit — not touched here.

### Problem 3.9.4 — Formal deformations (SOUND)

`FormalDeformation` (coefficient sequence + `base_eq` + Cauchy-product `isMul`),
`constDeformation`, and `IsIsomorphic`/`IsTrivial` are genuinely constructed. Part (a)
`isTrivial_of_ext1_subsingleton` is fully proved via an order-by-order intertwiner
construction (`star`, `bSeq`). Part (b) is the book's open-ended "is the converse true?",
recorded honestly as a `Prop`-valued definition `Problem3_9_4b` / `ConverseHolds` rather than
asserted as a theorem — appropriate, not vacuous. **Docstring corrected** (module docstring and
the `constDeformation` docstring both claimed `sorry`; the `isMul` field is in fact proved).

### Problem 3.9.5 — The Clifford algebra (SOUND)

The largest file (1801 lines). `CliffAlg B = CliffordAlgebra (quadForm B)` and the orthogonal
monomial basis `cliffBasis` are genuinely constructed. Faithful coverage of both book parts:

- (i) semisimplicity `isSemisimpleRing_of_nondegenerate` (Dickson trace-form criterion);
  even case `even_isMatrixAlgebra` (`∃ S, finrank S = 2ⁿ ∧ Cl(V) ≃ₐ End S`); odd case
  `odd_isSumMatrixAlgebra` (`∃ S, finrank S = 2ⁿ ∧ Cl(V) ≃ₐ End S × End S`). The "matrix
  algebra / two matrix algebras" language of the book is rendered as `End ℂ S`
  (= `Module.End`), which is the intended reading, and the `2ⁿ` spinor dimension is proved by
  a dimension count, so the existentials carry real content.
- (ii) `isSemisimpleRing_iff_nondegenerate` (semisimple ⇔ nondegenerate), forward direction
  `not_isSemisimpleRing_of_degenerate`; and the degenerate quotient
  `radicalQuotient_isClifford_of_degenerate` (`Cl(V)/Rad` is the Clifford algebra of the
  nondegenerate induced form `B'` on `V ⧸ rad B`, via a surjection with kernel = Jacobson
  radical). Faithful to "what is `Cl(V)/Rad(Cl(V))`?".

Non-vacuous throughout. **Docstring corrected** (was "Statement pass: … proofs are left as
`sorry`").

## Source changes in this PR

Docstring-only corrections of four stale "proofs are `sorry`"/"statement pass" banners that
outlived their completed proofs (same pattern as #7019, #7027, #7029):

- `Problem3_9_2.lean` (module docstring)
- `Problem3_9_3.lean` (module docstring)
- `Problem3_9_4.lean` (module docstring + `constDeformation` docstring)
- `Problem3_9_5.lean` (module docstring)

No proof, signature, import, or `def`-body edits. All five files rebuild successfully.
