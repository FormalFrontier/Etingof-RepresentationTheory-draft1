# Review — Stage 3.7 stale `fidelity: gap` re-verification (Chapters 2–4)

- **Issue:** #7182 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/37ead39b`
- **Scope:** 9 claim-bearing items marked `fidelity: gap` in `progress/items.json`, each carrying a
  `fidelity_issue` whose repair issue is now **CLOSED (merged)**. Task: re-audit each against its
  blob using Stage 3.2 steps 6–7 (statement fidelity + non-vacuity), and normalize the stale
  `gap` markers to `verified` **only** where the current Lean declaration is genuinely faithful and
  non-vacuous.
- **Method:** For each item — read the book blob; locate the current headline Lean declaration(s);
  confirm the object is genuinely constructed (no `sorry`/`True`-as-proposition in `def`/`instance`
  bodies); confirm the stated theorem faithfully and non-vacuously asserts the book's claim; build
  the touched modules; `#print axioms` the headline declarations (no `sorryAx`). Evidence gathering
  fanned out across parallel sub-audits; every verdict was cross-checked against the actual source.

## Overall verdict: **all 9 items FAITHFUL → flip `gap` → `verified`**

Every recorded gap has been genuinely repaired. No item is vacuous, strictly weaker than the book,
or mislabeled. No new `feature` repair issue is warranted. The stale `gap` markers understated
Stage 3.7 progress; they are normalized to `verified` (with `fidelity_issue` kept as a historical
note). No `.lean` source was modified.

---

## Per-item verdicts

### 1. `Chapter2/Definition2.2.1` — Associative algebra — **VERIFIED**
Book defines a **non-unital** associative algebra (a `k`-vector space with an associative bilinear
multiplication; the unit is deliberately deferred to 2.2.2). The original gap was that the old
abbrev aliased a unital `[Ring A]`/`Algebra`. The current
`class Etingof.AssociativeAlgebra (k A) [Field k] [AddCommGroup A] [Module k A]` carries a bare
`mul : A → A → A` with `mul_assoc'` and full bilinearity (`add_mul'`, `mul_add'`, `smul_mul'`,
`mul_smul'`) and **no** unit field — exactly the book's non-unital notion. An `instance` from
Mathlib's unital `Algebra k A` witnesses it as a faithful generalization (non-vacuous). Faithful.

### 2. `Chapter2/Definition2.2.2` — Unit in an associative algebra — **VERIFIED**
Book *defines* the concept "a unit is `1 ∈ A` with `1a = a1 = a`". The old formalization was a mere
demonstration theorem `one_isUnit` about a `Ring`. The current file genuinely *defines* the concept
as a predicate `def IsUnit (e : A) : Prop := ∀ a, inst.mul e a = a ∧ inst.mul a e = a` over the
non-unital `AssociativeAlgebra` of 2.2.1 (so it is a real defining property, not automatic), plus
`theorem isUnit_unique`. Matches the book's `1a = a1 = a` verbatim. Faithful.

### 3. `Chapter2/Remark2.3.2` — Left/right modules over a commutative ring — **VERIFIED**
Book: over a commutative ring `A`, a left `A`-module becomes a right `A`-module via `ma := am`, and
conversely. The original gap was "no Lean declaration exists." The current file constructs both
directions: `abbrev rightModuleOfLeft : Module Aᵐᵒᵖ M := Module.compHom M (unopRingHom A)` and
`leftModuleOfRight`, along the ring isomorphism `Aᵐᵒᵖ ≃+* A` that exists *because* `A` is
commutative. The defining equation is certified at defeq level by `rightModuleOfLeft_smul`
(`op a • m = a • m`, `rfl`) and `leftModuleOfRight_smul`. Real bodies, no `sorry`. Faithful.

### 4. `Chapter3/Definition3.3.2` — Dual representation — **VERIFIED**
Book: `V*` is a representation of `Aᵒᵖ` with action `(f · a)(v) := f(a v)`. The original gap was that
the old abbrev was the bare linear dual with no representation action. The current file equips the
dual with a genuine `instance instModuleMulOppositeDual : Module Aᵐᵒᵖ (Module.Dual k V)` (all six
module axioms proved, no `sorry`), and the defining formula is captured exactly by
`dualRepresentation_smul_apply : (a • f) v = f (a.unop • v)` (`rfl`). The carrier abbrev + typeclass
instance split follows the project's representation convention. Faithful.

### 5. `Chapter4/Theorem4.1.1` — Maschke's theorem — **VERIFIED**
A PASS report already existed (`progress/reviews/2026-07-21-ch4-theorem4_1_1-maschke-fidelity.md`);
confirmed independently, and the file has since been extended to cover strictly more of the book.
The current file states all five book claims as faithful, non-vacuous Lean theorems: part (i)
`Theorem4_1_1_semisimple` (`IsSemisimpleRing (MonoidAlgebra k G)`, correctly *not* assuming
`IsAlgClosed`); (ii-a) `Theorem4_1_1_algebra_iso` (complete non-redundant irreducible enumeration +
`k[G] ≃ₐ[k] Π i, End(Vᵢ)`, with `endIso_of_apply` proving the block map is `g ↦ g|_{Vᵢ}`); (ii-b)
`Theorem4_1_1_regularRep_iso` (isomorphism *of representations*, action `ρ_end g F i = ρᵢ(g) ∘ₗ Fᵢ`);
(ii-c) `Theorem4_1_1_regularRep_isotypic` (`k[G] ≅ ⊕ᵢ (dim Vᵢ)·Vᵢ`, multiplicity `= finrank`);
(ii-d) sum-of-squares `Σ finrank(Vᵢ)² = |G|`. Every existential is witnessed by
`IrrepDecomp.mk'` (built from `MonoidAlgebra.wedderburnArtin`) — never `sorry`/`True`. The earlier
recorded coverage gap (rep-iso and isotypic decomposition only in prose) is fully closed. Faithful.

### 6. `Chapter4/Example4.3_S3` — Irreps of S₃ — **VERIFIED**
Book enumerates trivial, sign, and 2-dim standard irreps, dims (1,1,2), `Σ dᵢ² = 6`. Current file
constructs all three as genuine `FDRep ℂ S₃` objects (the 2-dim one as the honest sum-zero subrep of
the permutation representation), proves each `Simple` via the real character (traces / fixed-point
counts, not asserted), derives finranks 1,1,2, and combines them in
`irreps_dim_sum_of_squares : 1²+1²+2² = |S₃|`. No `sorry`/`True`. Faithful.

### 7. `Chapter4/Example4.3_Q8` — Irreps of Q₈ — **VERIFIED**
Book: five irreps, dims (1,1,1,1,2), `Σ dᵢ² = 8`; four 1-dim from `Q₈/Z ≅ ℤ₂×ℤ₂`; the 2-dim rep
(4.3.1) with explicit Pauli matrices; center `{±1}`. Current file builds all five as genuine
`FDRep ℂ Q₈` objects: the four sign characters via `chiHom`, the 2-dim as the actual (4.3.1) matrix
rep with `rep_i/rep_j/rep_k/rep_neg_one` verifying the exact matrices and `ρ(−1) = −Id`; each proved
`Simple` via character norm-one sums; center `{±1}` proved (`mem_center_iff`); dims feed
`1²+1²+1²+1²+2² = 8`. No `sorry`/`True`. Faithful.

### 8. `Chapter4/Example4.3_S4` — Irreps of S₄ — **VERIFIED**
Book: five irreps, dims (1,1,2,3,3), `Σ dᵢ² = 24`; ℂ² via `S₄/V₄ ≅ S₃`; ℂ³₋ zero-sum functions;
ℂ³₊ = ℂ³₋ ⊗ sign; ℂ³₊ ≠ ℂ³₋. Current file constructs all five as real `FDRep ℂ S₄` objects: ℂ² as
the sum-zero subrep of the genuine S₄-action on the three pair-partitions (`actHom`, multiplicativity
by `decide`), ℂ³₋ zero-sum, ℂ³₊ the sign twist; each proved `Simple` via real characters; the
ℂ³₊ ≠ ℂ³₋ distinction captured by distinct character values on a transposition (a faithful equivalent
of the book's determinant argument, flagged in the docstring); dims feed `1²+1²+2²+3²+3² = 24`. No
`sorry`/`True`. Faithful.

### 9. `Chapter4/Example4.8.1` — Character tables of Q₈, S₄, A₅ — **VERIFIED**
Book presents three full character tables. Current file encodes all three as explicit data in a
purpose-built `Q5 = ℚ[√5]` ring (`chiQ8`, `chiS4`, `chiA5`, matching the book verbatim including the
A₅ golden-ratio entries `(1±√5)/2`), constructs genuine `FDRep ℂ G` representations for every row
(Q₈ quaternion matrices; S₄ pair-partition + deleted-permutation reps; A₅ deleted-perm ℂ⁴, ℂ⁵ on the
six Sylow-5 subgroups, and the two golden-ratio reps as the `μ± = 10±10√5` eigenspaces of the central
5-cycle class-sum on Λ²(ℂ⁴)), and proves each tabulated entry equals the actual character (trace):
`irrep_character` / `irrepS4_character_book` / `irrepA5_character_book`, plus simplicity, pairwise
non-isomorphism, class-count = 5, and A₅ completeness (`simple_iso_irrepA5`, `exists_char_eq_chiA5`).
The golden-ratio values are honestly derived from the class-sum minimal polynomial `z² = 20z + 400`,
not asserted. No `sorry`/`True`. **Packaging note (not a defect):** the umbrella file
`Example4_8_1.lean` re-exports `_A5_conj_classes`/`_A5_card`/`_A5_irrep` but not public
`_A5_simple`/`_A5_character`/`_A5_pairwise` wrappers the way it does for Q₈/S₄; the full A₅ content
exists as genuine theorems in namespace `Etingof.Example4_8_1.A5`. Faithful.

---

## Verification

- `lake build` of all 9 touched modules: **exit 0**.
- `#print axioms` (via a scratch importer, since removed) on a headline declaration of each item:
  every one depends only on the standard axioms — **no `sorryAx`, no custom axiom**:
  - Ch2 Def2.2.2 `isUnit_unique`, Ch2 Rem2.3.2 `rightModuleOfLeft_smul` / `leftModuleOfRight_smul`,
    Ch3 Def3.3.2 `dualRepresentation_smul_apply` / `instModuleMulOppositeDual` → `[propext, Quot.sound]`.
  - Ch4 Maschke `Theorem4_1_1_semisimple` / `_algebra_iso` / `_regularRep_iso` / `_regularRep_isotypic`,
    the three `Example4_3_*.irreps_dim_sum_of_squares`, and the character-table theorems
    `Example4_8_1_Q8_character` / `Example4_8_1_S4_character` / `Example4_8_1.A5.irrepA5_character_book`
    → `[propext, Classical.choice, Quot.sound]`.
  - No `sorry`/`admit`/`native_decide` appears in any of the audited `.lean` sources (`decide` and
    `norm_num` only).
- `git diff progress/items.json`: only `fidelity` field edits (`gap` → `verified`) for the 9 listed
  items; `fidelity_issue` retained as a historical note; `status` unchanged (all remained
  `sorry_free`).
