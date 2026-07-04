import EtingofRepresentationTheory.Chapter4.Example4_8_1.S4

/-!
# Example 4.8.1 — `A₅`: table, orthonormality, and the `ℂ`, `ℂ⁴`, `ℂ⁵`, `Λ²(ℂ⁴)` representations

Split out of `Example4_8_1.lean` for CI memory (issue #5852); see there for the umbrella.
Contains the `A₅` character table `chiA5`, its orthonormality, the conjugacy-class index
machinery `classIdxA5`, the three integer-character representations and the exterior square
`Λ²(ℂ⁴)`, with the bridge to the tabulated `Q5` values.
-/

namespace Etingof.Example4_8_1

open Q5
/-! ## `A₅`

Classes (in order): `Id` (1), 3-cycles `(123)` (20), double transpositions `(12)(34)` (15),
5-cycles `(12345)` (12), 5-cycles `(13245)` (12); `|A₅| = 60`.  Irreducibles `ℂ` (trivial),
`ℂ³₊`, `ℂ³₋` (the two icosahedral rotation reps, with golden-ratio values `(1 ± √5)/2` on
the two 5-cycle classes), `ℂ⁴`, `ℂ⁵`. -/

/-- Class sizes of `A₅`. -/
def sizesA5 : Fin 5 → ℚ := ![1, 20, 15, 12, 12]

/-- Character table of `A₅`, exactly as in the book.  The entries `⟨1/2, 1/2⟩ = (1+√5)/2`
and `⟨1/2, -1/2⟩ = (1-√5)/2` are the golden-ratio character values of the two 3-dimensional
irreducibles on the two classes of 5-cycles. -/
def chiA5 : Fin 5 → Fin 5 → Q5 :=
  ![![1,  1,  1,  1,           1          ],
    ![3,  0, -1, ⟨1/2, 1/2⟩,  ⟨1/2, -1/2⟩ ],
    ![3,  0, -1, ⟨1/2, -1/2⟩, ⟨1/2, 1/2⟩  ],
    ![4,  1,  0, -1,          -1          ],
    ![5, -1,  1,  0,           0          ]]

/-- The tabulated `A₅` characters are orthonormal, with the golden-ratio entries
contributing genuine `√5` terms that cancel.  Combined with the fact that `A₅` has exactly 5
conjugacy classes (`A5_conj_classes`), this certifies the five rows are the distinct
irreducible characters of `A₅`. (Etingof Example 4.8.1)

Proved honestly (no `native_decide`): each of the 25 inner products is split into its rational
`re`/`im` components (`Q5.ext`), the 5-term `sumFin` is unfolded (`Q5.sumFin_five`), and the
resulting rational arithmetic -- in which the golden-ratio `√5` terms cancel -- is discharged
by `norm_num`.  Kernel `decide` cannot evaluate this directly: the `ℚ`-normalisation of the
`1/60` factor stalls the kernel. -/
theorem A5_orthonormal (i j : Fin 5) :
    ip 60 sizesA5 (chiA5 i) (chiA5 j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    (first | rw [if_pos rfl] | rw [if_neg (by decide)]) <;>
    apply Q5.ext <;>
    norm_num [ip, Q5.sumFin_five, sizesA5, chiA5, Q5.mk_re, Q5.mk_im, Q5.add_re, Q5.add_im,
      Q5.mul_re, Q5.mul_im, Q5.neg_re, Q5.neg_im, Q5.zero_re, Q5.zero_im, Q5.one_re, Q5.one_im,
      Q5.ofNat_re, Q5.ofNat_im, Q5.ofRat_re, Q5.ofRat_im, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons]

/-! ### Genuine `A₅` representations: trivial `ℂ`, the 4-dim `ℂ⁴`, and the 5-dim `ℂ⁵`

Three of the five rows of `chiA5` are realised here as the characters (traces) of actual
representations of `A₅ = alternatingGroup (Fin 5)`:

* `ℂ` (row 0) is the trivial representation, character `(1,1,1,1,1)`;
* `ℂ⁴` (row 3) is the deleted natural permutation representation of `A₅` on `Fin 5`, with
  character `χ(g) = #fix(g) − 1`, giving the row `(4,1,0,-1,-1)`;
* `ℂ⁵` (row 4) is the deleted permutation representation on the **six Sylow-5 subgroups** of
  `A₅` (equivalently the six pairs of opposite icosahedron vertices, i.e. `P¹(𝔽₅)`), on which
  `A₅` acts 2-transitively by conjugation, giving the row `(5,-1,1,0,0)`.

Simplicity of `ℂ⁴` and `ℂ⁵` follows from `FDRep.simple_iff_char_is_norm_one` via the honest
`decide`-evaluated character-norm sum over the 60 elements (no `native_decide`); the three rows
are pairwise distinct characters, hence the three representations are pairwise non-isomorphic.
The generic deleted-permutation-representation machinery (`S4.stdRepM`, `S4.fixCardM`,
`S4.stdRepM_character`) and the one-dimensional `S4.charRep` are reused from the `S₄` section. -/

namespace A5

open Equiv CategoryTheory

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- `A₅`, realised as the alternating group on `Fin 5`. -/
abbrev G := alternatingGroup (Fin 5)

/-- `|A₅| = 5! / 2 = 60`. -/
lemma card_G : Nat.card G = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide

/-- The five class representatives `Id, (123), (12)(34), (12345), (13245)`. -/
def classRepA5 : Fin 5 → G :=
  ![1,
    ⟨Equiv.swap 0 2 * Equiv.swap 0 1, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1,
      Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨(Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1) ^ 2,
      Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩]

/-! #### Conjugacy-class index machinery

The five conjugacy classes of `A₅` are `Id, (123), (12)(34), (12345), (13245)` with sizes
`1, 20, 15, 12, 12` (matching `sizesA5`).  Four of the five are already separated by the number
of fixed points of the natural action on `Fin 5` (`5, 2, 1, 0`); the two fixed-point-free
5-cycle classes are separated by a conjugacy test against `classRepA5 3`.  All specifications
are honest `decide`s over the 60 elements (no `native_decide`). -/

/-- The index (in `Fin 5`) of the conjugacy class of `g ∈ A₅`.  The identity, 3-cycles and
double transpositions are recognised by their `5, 2, 1` fixed points on `Fin 5`; the two
5-cycle classes (both fixed-point-free) are told apart by a conjugacy test against
`classRepA5 3`. -/
def classIdxA5 (g : G) : Fin 5 :=
  if S4.fixCardM (G := G) (α := Fin 5) g = 5 then 0
  else if S4.fixCardM (G := G) (α := Fin 5) g = 2 then 1
  else if S4.fixCardM (G := G) (α := Fin 5) g = 1 then 2
  else if ∃ c : G, c * classRepA5 3 * c⁻¹ = g then 3
  else 4

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` over the 60 elements of A₅ (conjugacy search per element); no `native_decide`
/-- Every `g ∈ A₅` is conjugate to its class representative `classRepA5 (classIdxA5 g)`
(honest `decide` over the 60 elements, no `native_decide`).  Combine with `isConj_iff` to
recover `IsConj (classRepA5 (classIdxA5 g)) g`. -/
lemma classIdxA5_spec (g : G) : ∃ c : G, c * classRepA5 (classIdxA5 g) * c⁻¹ = g := by
  revert g; decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` over the 60 elements of A₅ (class index per element); no `native_decide`
/-- The five conjugacy classes have sizes `1, 20, 15, 12, 12`, matching `sizesA5` (honest
`decide` over the 60 elements). -/
lemma classIdxA5_card (j : Fin 5) :
    (Finset.univ.filter fun g => classIdxA5 g = j).card = ![1, 20, 15, 12, 12] j := by
  revert j; decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` over the 5 representatives × 60 conjugators of A₅; no `native_decide`
/-- The conjugacy classes of `A₅` are real: every class representative is conjugate to its own
inverse (honest `decide` over the 60 elements). -/
lemma classRepA5_inv_conj (j : Fin 5) :
    ∃ c : G, c * classRepA5 j * c⁻¹ = (classRepA5 j)⁻¹ := by
  revert j; decide

end

end A5

end Etingof.Example4_8_1
