import EtingofRepresentationTheory.Chapter4.Example4_8_1.S4
import EtingofRepresentationTheory.Chapter4.Corollary4_2_2

/-!
# Introduction to Section 4.8: the character table of `A₄`

The introduction to §4.8 displays the character table of `A₄`, the group of even permutations
of four items:

| `A₄` | `Id` | `(123)` | `(132)` | `(12)(34)` |
|---|---|---|---|---|
| `#` | 1 | 4 | 4 | 3 |
| `ℂ` | 1 | 1 | 1 | 1 |
| `ℂ_ε` | 1 | `ε` | `ε²` | 1 |
| `ℂ_{ε²}` | 1 | `ε²` | `ε` | 1 |
| `ℂ³` | 3 | 0 | 0 | −1 |

with `ε = exp(2πi/3)`.  The three one-dimensional characters come from the quotient
`A₄ / V₄ ≅ ℤ/3`, where `V₄ ≅ ℤ/2 ⊕ ℤ/2` is the normal Klein four subgroup, and the fourth
irreducible is three-dimensional because `A₄` has four conjugacy classes and
`1² + 1² + 1² + 3² = 12 = |A₄|`.

Every row of the table is here the character of an actual representation:

* `repEps k` (`k : ℤ/3`) is the one-dimensional representation attached to the character
  `A₄ → A₄/V₄ ≅ ℤ/3 → ℂˣ`, `g ↦ εᵏᵍ`.  The quotient map is `qHom`, which is surjective
  (`qHom_surjective`) with kernel exactly `alternatingGroup.kleinFour (Fin 4)`
  (`ker_qHom`), so it realises the book's `A₄/(ℤ/2 ⊕ ℤ/2) = ℤ/3`.
* `repStd` is the deleted natural permutation representation on `{x ∈ ℂ⁴ | Σ xᵢ = 0}`, with
  character `#fix(g) − 1`.

The four conjugacy classes are represented by `classRepA4 = (Id, (012), (021), (01)(23))`,
recognised by `classIdxA4`, and have sizes `1, 4, 4, 3` (`classIdxA4_card`).  Simplicity is
proved by the norm-one character criterion, pairwise non-isomorphism by distinctness of the
rows, and completeness by Corollary 4.2.2 together with the count of four conjugacy classes.

The general permutation-representation machinery (`charRep`, `stdRepM`, `fixCardM`) is reused
from the `S₄` catalogue of Example 4.8.1, as is the conjugation action of `S₄` on the three
pair-partitions of `Fin 4`, which supplies the quotient map `A₄ → ℤ/3`.

The realisation of `ℂ³` by the rotations of a regular tetrahedron is not formalised; the
deleted permutation representation is the same representation.
-/

namespace Etingof.Introduction_4_8

open CategoryTheory Equiv

namespace A4

noncomputable section

set_option linter.unusedSectionVars false

/-! ### The group and its order -/

/-- `A₄`, realised as the alternating group on `Fin 4`. -/
abbrev G := alternatingGroup (Fin 4)

/-- `|A₄| = 4! / 2 = 12`. -/
lemma card_G : Fintype.card G = 12 := by
  rw [card_alternatingGroup, Fintype.card_fin]; decide

/-! ### The quotient `A₄ / V₄ ≅ ℤ/3`

`S₄` acts by conjugation on the three pair-partitions of `Fin 4`
(`Etingof.Example4_8_1.S4.conjIdxS4`), with kernel the Klein four subgroup.  The image of
`A₄` under this action is the group of cyclic rotations of the three partitions, so
`g ↦ g • 0` is a homomorphism `A₄ → ℤ/3`; we normalise it (by a sign) so that the 3-cycle
`(012)` maps to `1`. -/

/-- The index of the image of the pair-partition `{{0,1},{2,3}}` under conjugation by `g`. -/
def qIdx (g : G) : Fin 3 :=
  Etingof.Example4_8_1.S4.conjIdxS4 (g : Equiv.Perm (Fin 4)) 0

/-- The class of `g` in `A₄/V₄ ≅ ℤ/3`, normalised so that `(012) ↦ 1`. -/
def qVal (g : G) : ZMod 3 := -((qIdx g).val : ZMod 3)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` over the 12 × 12 multiplication table of `A₄` (no `native_decide`)
lemma qVal_mul (g h : G) : qVal (g * h) = qVal g + qVal h := by
  revert g h; decide

lemma qVal_one : qVal 1 = 0 := by decide

/-- The quotient homomorphism `A₄ → ℤ/3` (written multiplicatively), with kernel the Klein
four subgroup `V₄`. -/
def qHom : G →* Multiplicative (ZMod 3) where
  toFun g := Multiplicative.ofAdd (qVal g)
  map_one' := congrArg Multiplicative.ofAdd qVal_one
  map_mul' g h := congrArg Multiplicative.ofAdd (qVal_mul g h)

@[simp] lemma qHom_apply (g : G) : qHom g = Multiplicative.ofAdd (qVal g) := rfl

set_option maxRecDepth 10000 in
/-- `qHom : A₄ → ℤ/3` is surjective. -/
lemma qHom_surjective : Function.Surjective qHom := by
  intro x
  have : ∀ y : ZMod 3, ∃ g : G, qVal g = y := by decide
  obtain ⟨g, hg⟩ := this (Multiplicative.toAdd x)
  exact ⟨g, by rw [qHom_apply, hg]; rfl⟩

set_option maxRecDepth 10000 in
/-- The kernel of `qHom` is the Klein four subgroup `V₄ ≅ ℤ/2 ⊕ ℤ/2` of `A₄`.  Together with
`qHom_surjective` this is the book's `A₄ / (ℤ/2 ⊕ ℤ/2) = ℤ/3`. -/
lemma ker_qHom : qHom.ker = alternatingGroup.kleinFour (Fin 4) := by
  have hfwd : ∀ g : G, qVal g = 0 → (g = 1 ∨ (g : Equiv.Perm (Fin 4)).cycleType = {2, 2}) := by
    decide
  have hbwd : ∀ g : G, (g : Equiv.Perm (Fin 4)).cycleType = {2, 2} → qVal g = 0 := by decide
  refine le_antisymm (fun g hg => ?_) ?_
  · rcases hfwd g (Multiplicative.ofAdd.injective (MonoidHom.mem_ker.mp hg)) with rfl | h
    · exact one_mem _
    · exact Subgroup.subset_closure h
  · rw [alternatingGroup.kleinFour, Subgroup.closure_le]
    exact fun g hg => MonoidHom.mem_ker.mpr (congrArg Multiplicative.ofAdd (hbwd g hg))

/-- `V₄` is normal in `A₄` (Mathlib's `alternatingGroup.normal_kleinFour`), as the book
asserts. -/
lemma normal_kleinFour : (alternatingGroup.kleinFour (Fin 4)).Normal :=
  alternatingGroup.normal_kleinFour (by simp)

/-! ### The primitive cube root of unity `ε = exp(2πi/3)` -/

/-- `ε = exp(2πi/3)`, as a unit of `ℂ`. -/
def zeta3 : ℂˣ := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / 3)) (Complex.exp_ne_zero _)

/-- `ε = exp(2πi/3)`, as a complex number. -/
def eps : ℂ := (zeta3 : ℂ)

lemma eps_eq : eps = Complex.exp (2 * Real.pi * Complex.I / 3) := rfl

lemma zeta3_pow_three : zeta3 ^ 3 = 1 := by
  apply Units.ext
  have hval : ((zeta3 ^ 3 : ℂˣ) : ℂ) = (Complex.exp (2 * Real.pi * Complex.I / 3)) ^ 3 := by
    simp [zeta3]
  rw [hval, ← Complex.exp_nat_mul,
    show ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3) = 2 * Real.pi * Complex.I by
      push_cast; ring, Complex.exp_two_pi_mul_I, Units.val_one]

lemma zeta3_pow_mod (m : ℕ) : zeta3 ^ (m % 3) = zeta3 ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 3]
  rw [pow_add, pow_mul, zeta3_pow_three, one_pow, one_mul]

/-- `ε` is a primitive cube root of unity. -/
lemma zeta3_primitive : IsPrimitiveRoot (zeta3 : ℂ) 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  rw [show (zeta3 : ℂ) = Complex.exp (2 * ↑Real.pi * Complex.I / 3) from rfl,
    show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num]
  exact h

/-- `ε` is a primitive cube root of unity. -/
lemma eps_primitive : IsPrimitiveRoot eps 3 := zeta3_primitive

/-- The powers `1, ε, ε²` are pairwise distinct. -/
lemma eps_pow_inj {i j : ℕ} (hi : i < 3) (hj : j < 3) (h : eps ^ i = eps ^ j) : i = j :=
  zeta3_primitive.pow_inj hi hj h

/-! ### The three one-dimensional representations -/

/-- The character `ℤ/3 → ℂˣ`, `x ↦ ε^(k·x)`. -/
def cubeChar (k : ZMod 3) : Multiplicative (ZMod 3) →* ℂˣ where
  toFun x := zeta3 ^ (k * Multiplicative.toAdd x).val
  map_one' := by
    change zeta3 ^ (k * (0 : ZMod 3)).val = 1
    rw [mul_zero, ZMod.val_zero, pow_zero]
  map_mul' x y := by
    change zeta3 ^ (k * (Multiplicative.toAdd x + Multiplicative.toAdd y)).val
      = zeta3 ^ (k * Multiplicative.toAdd x).val * zeta3 ^ (k * Multiplicative.toAdd y).val
    rw [mul_add, ZMod.val_add, ← pow_add, zeta3_pow_mod]

/-- The character `A₄ → ℂˣ`, `g ↦ ε^(k·q(g))`, pulled back along `qHom` from `ℤ/3`.
`k = 0` gives the trivial character, `k = 1` and `k = 2` the two nontrivial ones. -/
def epsHom (k : ZMod 3) : G →* ℂˣ := (cubeChar k).comp qHom

lemma epsHom_apply (k : ZMod 3) (g : G) : epsHom k g = zeta3 ^ (k * qVal g).val := rfl

/-- The one-dimensional representation attached to `epsHom k`. -/
def repEps (k : ZMod 3) : FDRep ℂ G := FDRep.of (Etingof.Example4_8_1.S4.charRep (epsHom k))

lemma repEps_character (k : ZMod 3) (g : G) :
    (repEps k).character g = eps ^ (k * qVal g).val := by
  rw [repEps, Etingof.Example4_8_1.S4.charRep_character, epsHom_apply, eps,
    Units.val_pow_eq_pow_val]

/-! ### The three-dimensional representation -/

/-- `ℂ³`, the deleted natural permutation representation of `A₄` on `{x ∈ ℂ⁴ | Σ xᵢ = 0}`.
Etingof identifies it with the rotation representation of the regular tetrahedron. -/
def repStd : FDRep ℂ G := Etingof.Example4_8_1.S4.stdRepM (G := G) (α := Fin 4)

lemma repStd_character (g : G) :
    repStd.character g
      = ((Etingof.Example4_8_1.S4.fixCardM (G := G) (α := Fin 4) g : ℤ) - 1 : ℂ) := by
  rw [repStd, Etingof.Example4_8_1.S4.stdRepM_character]; push_cast; ring

/-! ### The conjugacy classes -/

/-- The four class representatives `Id, (012), (021), (01)(23)`. -/
def classRepA4 : Fin 4 → G :=
  ![1,
    ⟨Equiv.swap 0 2 * Equiv.swap 0 1, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩]

/-- The index of the conjugacy class of `g ∈ A₄`.  The identity and the double transpositions
are recognised by their `4` and `0` fixed points on `Fin 4`; the two classes of 3-cycles are
told apart by their images in `A₄/V₄ ≅ ℤ/3`, which are the two nonzero elements. -/
def classIdxA4 (g : G) : Fin 4 :=
  if Etingof.Example4_8_1.S4.fixCardM (G := G) (α := Fin 4) g = 4 then 0
  else if Etingof.Example4_8_1.S4.fixCardM (G := G) (α := Fin 4) g = 0 then 3
  else if qVal g = 1 then 1
  else 2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` over the 12 × 12 conjugation table of `A₄` (no `native_decide`); the raised
-- limit covers kernel reduction of the permutation multiplications
/-- Every `g ∈ A₄` is conjugate to its class representative `classRepA4 (classIdxA4 g)`. -/
lemma classIdxA4_spec (g : G) : ∃ c : G, c * classRepA4 (classIdxA4 g) * c⁻¹ = g := by
  revert g; decide

set_option maxRecDepth 10000 in
/-- The four conjugacy classes have sizes `1, 4, 4, 3`. -/
lemma classIdxA4_card (j : Fin 4) :
    (Finset.univ.filter fun g => classIdxA4 g = j).card = ![1, 4, 4, 3] j := by
  revert j; decide

set_option maxRecDepth 10000 in
/-- Each class representative lies in its own class. -/
lemma classIdxA4_classRepA4 (j : Fin 4) : classIdxA4 (classRepA4 j) = j := by
  revert j; decide

set_option maxRecDepth 10000 in
/-- The two 3-cycle classes are distinguished: `(012)` and `(021)` are not conjugate. -/
lemma classRepA4_one_two_not_conj : ¬ ∃ c : G, c * classRepA4 1 * c⁻¹ = classRepA4 2 := by
  decide

/-! ### The character table -/

/-- The character table of `A₄`, exactly as in the book, with `ε = exp(2πi/3)`. -/
def tblA4 : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1],
    ![1, eps, eps ^ 2, 1],
    ![1, eps ^ 2, eps, 1],
    ![3, 0, 0, -1]]

/-- The four irreducible representations, indexed as the rows of `tblA4`:
`ℂ, ℂ_ε, ℂ_{ε²}, ℂ³`. -/
def irrepA4 : Fin 4 → FDRep ℂ G := ![repEps 0, repEps 1, repEps 2, repStd]

set_option maxRecDepth 10000 in
lemma qVal_classRepA4 : ∀ j : Fin 4, qVal (classRepA4 j) = ![0, 1, 2, 0] j := by decide

set_option maxRecDepth 10000 in
lemma fixCard_classRepA4 : ∀ j : Fin 4,
    Etingof.Example4_8_1.S4.fixCardM (G := G) (α := Fin 4) (classRepA4 j) = ![4, 1, 1, 0] j := by
  decide

lemma repEps_zero_char (j : Fin 4) : (repEps 0).character (classRepA4 j) = tblA4 0 j := by
  have hexp : ∀ j : Fin 4, ((0 : ZMod 3) * qVal (classRepA4 j)).val = 0 := by
    intro j; rw [zero_mul, ZMod.val_zero]
  rw [repEps_character, hexp j, pow_zero]
  fin_cases j <;>
    norm_num [tblA4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

set_option maxRecDepth 10000 in
lemma repEps_one_char (j : Fin 4) : (repEps 1).character (classRepA4 j) = tblA4 1 j := by
  have hexp : ∀ j : Fin 4, ((1 : ZMod 3) * qVal (classRepA4 j)).val = ![0, 1, 2, 0] j := by decide
  rw [repEps_character, hexp j]
  fin_cases j <;>
    norm_num [tblA4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

set_option maxRecDepth 10000 in
lemma repEps_two_char (j : Fin 4) : (repEps 2).character (classRepA4 j) = tblA4 2 j := by
  have hexp : ∀ j : Fin 4, ((2 : ZMod 3) * qVal (classRepA4 j)).val = ![0, 2, 1, 0] j := by decide
  rw [repEps_character, hexp j]
  fin_cases j <;>
    norm_num [tblA4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

lemma repStd_char (j : Fin 4) : repStd.character (classRepA4 j) = tblA4 3 j := by
  rw [repStd_character, fixCard_classRepA4 j]
  fin_cases j <;>
    norm_num [tblA4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- **The character table of `A₄`.**  The character of `irrepA4 i` at the class representative
`classRepA4 j` is the tabulated value `tblA4 i j`. -/
theorem irrepA4_character (i j : Fin 4) :
    (irrepA4 i).character (classRepA4 j) = tblA4 i j := by
  fin_cases i
  · exact repEps_zero_char j
  · exact repEps_one_char j
  · exact repEps_two_char j
  · exact repStd_char j

/-! ### Irreducibility -/

lemma repEps_simple (k : ZMod 3) : Simple (repEps k) :=
  Etingof.Example4_8_1.S4.charRep_simple _

set_option maxRecDepth 10000 in
lemma repStd_simple : Simple repStd := by
  rw [repStd, FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : G,
      (Etingof.Example4_8_1.S4.stdRepM (G := G) (α := Fin 4)).character g
        * (Etingof.Example4_8_1.S4.stdRepM (G := G) (α := Fin 4)).character g⁻¹
      = ((((Etingof.Example4_8_1.S4.fixCardM (G := G) (α := Fin 4) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [Etingof.Example4_8_1.S4.stdRepM_character, Etingof.Example4_8_1.S4.stdRepM_character,
      Etingof.Example4_8_1.S4.fixCardM_inv]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : G,
      (((Etingof.Example4_8_1.S4.fixCardM (G := G) (α := Fin 4) g : ℤ) - 1) ^ 2) = 12 := by
    decide
  rw [hsum, Nat.card_eq_fintype_card, card_G]; norm_num

theorem irrepA4_simple (i : Fin 4) : Simple (irrepA4 i) := by
  fin_cases i
  · exact repEps_simple 0
  · exact repEps_simple 1
  · exact repEps_simple 2
  · exact repStd_simple

/-! ### Pairwise non-isomorphism -/

/-- The values of `tblA4` in the first two columns: row `3` is the only one with a `3` in
column `0`, and the other three rows take the distinct values `ε⁰, ε¹, ε²` in column `1`. -/
lemma tblA4_col_zero (i : Fin 4) : tblA4 i 0 = if i = 3 then 3 else 1 := by
  fin_cases i <;>
    norm_num [tblA4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> decide

lemma tblA4_col_one (i : Fin 4) (hi : i ≠ 3) : tblA4 i 1 = eps ^ (i : ℕ) := by
  fin_cases i
  · norm_num [tblA4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
  · norm_num [tblA4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
  · norm_num [tblA4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  · exact absurd rfl hi

/-- The four rows of `tblA4` are pairwise distinct. -/
lemma tblA4_injective : Function.Injective tblA4 := by
  intro i j hij
  have h1 : tblA4 i 1 = tblA4 j 1 := congrFun hij 1
  have h0 : tblA4 i 0 = tblA4 j 0 := congrFun hij 0
  have hpow := tblA4_col_one
  have hzero := tblA4_col_zero
  by_cases hi3 : i = 3
  · by_cases hj3 : j = 3
    · rw [hi3, hj3]
    · rw [hzero i, hzero j, if_pos hi3, if_neg hj3] at h0
      exact absurd h0 (by norm_num)
  · by_cases hj3 : j = 3
    · rw [hzero i, hzero j, if_neg hi3, if_pos hj3] at h0
      exact absurd h0 (by norm_num)
    · rw [hpow i hi3, hpow j hj3] at h1
      exact Fin.ext (eps_pow_inj (by omega) (by omega) h1)

theorem irrepA4_pairwise (i j : Fin 4) (hij : i ≠ j) :
    ¬ Nonempty (irrepA4 i ≅ irrepA4 j) := by
  rintro ⟨e⟩
  apply hij
  have hchar : (irrepA4 i).character = (irrepA4 j).character := FDRep.char_iso e
  refine tblA4_injective (funext fun c => ?_)
  rw [← irrepA4_character, ← irrepA4_character, hchar]

/-! ### Completeness -/

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` over the `ConjClasses` quotient of the 12-element group `A₄`; the raised
-- limit covers kernel reduction of the quotient enumeration
/-- `A₄` has exactly four conjugacy classes. -/
theorem conj_classes_A4 : Fintype.card (ConjClasses G) = 4 := by decide

private instance : Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero (by rw [card_G]; norm_num)

/-- **Completeness of `irrepA4`.**  Every simple complex representation of `A₄` is isomorphic
to one of the four `irrepA4 i`.  The four are pairwise non-isomorphic simples and there are
exactly `4 = |ConjClasses A₄|` isomorphism classes of simples (Corollary 4.2.2), so they
exhaust them. -/
theorem simple_iso_irrepA4 (V : FDRep ℂ G) [Simple V] :
    ∃ i : Fin 4, Nonempty (V ≅ irrepA4 i) := by
  obtain ⟨n, W, _hWsimp, _hWinj, hWsurj, hn⟩ := Etingof.Corollary4_2_2 (k := ℂ) (G := G)
  rw [conj_classes_A4] at hn
  subst hn
  choose c hc using fun i => hWsurj (irrepA4 i) (irrepA4_simple i)
  have hcinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    refine irrepA4_pairwise i j hne ?_
    obtain ⟨αi⟩ := hc i
    obtain ⟨αj⟩ := hc j
    exact ⟨αi ≪≫ eqToIso (congrArg W hij) ≪≫ αj.symm⟩
  have hcsurj : Function.Surjective c := Finite.surjective_of_injective hcinj
  obtain ⟨k, hk⟩ := hWsurj V ‹Simple V›
  obtain ⟨i, hi⟩ := hcsurj k
  refine ⟨i, ?_⟩
  obtain ⟨αV⟩ := hk
  obtain ⟨αi⟩ := hc i
  exact ⟨αV ≪≫ eqToIso (congrArg W hi.symm) ≪≫ αi.symm⟩

/-- The dimensions of the four irreducibles are `1, 1, 1, 3`, and `1² + 1² + 1² + 3² = 12`. -/
theorem sum_sq_dim : ∑ i : Fin 4, (tblA4 i 0) ^ 2 = (Fintype.card G : ℂ) := by
  rw [card_G]
  simp only [Fin.sum_univ_four]
  norm_num [tblA4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

end

end A4

end Etingof.Introduction_4_8

/-! ## Public endpoints -/

open Etingof.Introduction_4_8 in
/-- `A₄` has order 12. (Etingof, introduction to §4.8) -/
theorem Etingof.Introduction_4_8_A4_card :
    Fintype.card (alternatingGroup (Fin 4)) = 12 := A4.card_G

open Etingof.Introduction_4_8 in
/-- `A₄` has exactly four conjugacy classes, with representatives `Id, (012), (021), (01)(23)`
and sizes `1, 4, 4, 3`. (Etingof, introduction to §4.8) -/
theorem Etingof.Introduction_4_8_A4_conj_classes :
    Fintype.card (ConjClasses (alternatingGroup (Fin 4))) = 4 := A4.conj_classes_A4

open Etingof.Introduction_4_8 in
/-- The four conjugacy classes of `A₄` have sizes `1, 4, 4, 3`; in particular the two classes
of 3-cycles are distinct. (Etingof, introduction to §4.8) -/
theorem Etingof.Introduction_4_8_A4_class_sizes (j : Fin 4) :
    (Finset.univ.filter fun g => A4.classIdxA4 g = j).card = ![1, 4, 4, 3] j :=
  A4.classIdxA4_card j

open Etingof.Introduction_4_8 in
/-- `A₄ / V₄ ≅ ℤ/3`: the map `qHom` is surjective onto `ℤ/3` with kernel the normal Klein four
subgroup `V₄ = ℤ/2 ⊕ ℤ/2`. (Etingof, introduction to §4.8) -/
theorem Etingof.Introduction_4_8_A4_quotient :
    Function.Surjective A4.qHom ∧
      A4.qHom.ker = alternatingGroup.kleinFour (Fin 4) :=
  ⟨A4.qHom_surjective, A4.ker_qHom⟩

open Etingof.Introduction_4_8 in
/-- The four class representatives `Id, (012), (021), (01)(23)` exhaust the conjugacy classes of
`A₄`: every element is conjugate to exactly one of them, and in particular the two classes of
3-cycles are distinct. (Etingof, introduction to §4.8) -/
theorem Etingof.Introduction_4_8_A4_class_reps :
    (∀ g : alternatingGroup (Fin 4),
        ∃ c : alternatingGroup (Fin 4),
          c * A4.classRepA4 (A4.classIdxA4 g) * c⁻¹ = g) ∧
      (∀ j, A4.classIdxA4 (A4.classRepA4 j) = j) ∧
      ¬ ∃ c : alternatingGroup (Fin 4), c * A4.classRepA4 1 * c⁻¹ = A4.classRepA4 2 :=
  ⟨A4.classIdxA4_spec, A4.classIdxA4_classRepA4, A4.classRepA4_one_two_not_conj⟩

open Etingof.Introduction_4_8 in
/-- The `ε` of the table is `exp(2πi/3)`, a primitive cube root of unity.
(Etingof, introduction to §4.8) -/
theorem Etingof.Introduction_4_8_A4_eps :
    A4.eps = Complex.exp (2 * Real.pi * Complex.I / 3) ∧ IsPrimitiveRoot A4.eps 3 :=
  ⟨A4.eps_eq, A4.eps_primitive⟩

open Etingof.Introduction_4_8 in
/-- The dimensions `1, 1, 1, 3` of the four irreducibles satisfy `1² + 1² + 1² + 3² = 12 = |A₄|`,
the sum-of-squares identity that forces the fourth irreducible to be three-dimensional.
(Etingof, introduction to §4.8) -/
theorem Etingof.Introduction_4_8_A4_sum_sq_dim :
    ∑ i : Fin 4, (A4.tblA4 i 0) ^ 2 = (Fintype.card (alternatingGroup (Fin 4)) : ℂ) :=
  A4.sum_sq_dim

open Etingof.Introduction_4_8 in
/-- The four irreducible representations of `A₄`, indexed `0..3` as `ℂ, ℂ_ε, ℂ_{ε²}, ℂ³`. -/
noncomputable def Etingof.Introduction_4_8_A4_irrep :
    Fin 4 → FDRep ℂ (alternatingGroup (Fin 4)) := A4.irrepA4

open Etingof.Introduction_4_8 in
/-- Each of the four `A₄` representations is simple, proved via the norm-one character
criterion (no `native_decide`). (Etingof, introduction to §4.8) -/
theorem Etingof.Introduction_4_8_A4_simple (i : Fin 4) :
    CategoryTheory.Simple (Etingof.Introduction_4_8_A4_irrep i) := A4.irrepA4_simple i

open Etingof.Introduction_4_8 in
/-- The character of the `i`-th `A₄` representation at the `j`-th class representative
`(Id, (012), (021), (01)(23))` equals the tabulated value `tblA4 i j`, i.e. the rows are
`(1,1,1,1)`, `(1,ε,ε²,1)`, `(1,ε²,ε,1)`, `(3,0,0,-1)` with `ε = exp(2πi/3)`.
(Etingof, introduction to §4.8) -/
theorem Etingof.Introduction_4_8_A4_character (i j : Fin 4) :
    (Etingof.Introduction_4_8_A4_irrep i).character (A4.classRepA4 j) = A4.tblA4 i j :=
  A4.irrepA4_character i j

open Etingof.Introduction_4_8 in
/-- The four `A₄` representations are pairwise non-isomorphic. (Etingof, introduction to §4.8) -/
theorem Etingof.Introduction_4_8_A4_pairwise (i j : Fin 4) (hij : i ≠ j) :
    ¬ Nonempty (Etingof.Introduction_4_8_A4_irrep i ≅ Etingof.Introduction_4_8_A4_irrep j) :=
  A4.irrepA4_pairwise i j hij

open Etingof.Introduction_4_8 in
/-- **Completeness of the `A₄` character table.**  Every simple complex representation of `A₄`
is isomorphic to one of the four tabulated ones. (Etingof, introduction to §4.8) -/
theorem Etingof.Introduction_4_8_A4_complete (V : FDRep ℂ (alternatingGroup (Fin 4)))
    [CategoryTheory.Simple V] :
    ∃ i : Fin 4, Nonempty (V ≅ Etingof.Introduction_4_8_A4_irrep i) :=
  A4.simple_iso_irrepA4 V
