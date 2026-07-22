import Mathlib
import EtingofRepresentationTheory.Chapter5.FrobeniusSchurRealType

/-!
# Remark 4.5.5: The unitary character matrix and column orthogonality

This file formalizes Etingof's Remark 4.5.5, which gives an alternate proof of the
second orthogonality relation (Theorem 4.5.4) via a *unitary matrix* argument.

Consider the square matrix `U` whose rows are labeled by the irreducible
representations of `G` and whose columns are labeled by the conjugacy classes,
with entries
`U_{V, c} = χ_V(g_c) / √|Z_{g_c}|`,
where `g_c` is a representative of the class `c` and `Z_g` is the centralizer of
`g`. The matrix is *square* because the number of irreducible representations
equals the number of conjugacy classes (Theorem 4.5.2); we encode this squareness
by indexing the irreducible family `V` by `ConjClasses G` itself.

The argument is:

1. **Rows are orthonormal** (`character_matrix_mul_conjTranspose`): `U Uᴴ = 1`.
   This is the first orthogonality relation (Theorem 4.5.1, here
   `FDRep.char_orthonormal`) reindexed from a sum over group elements to a sum
   over conjugacy classes, using `|c.carrier| · |Z_{g_c}| = |G|`.
2. **`U` is unitary** (`character_matrix_conjTranspose_mul`): for a square matrix,
   `U Uᴴ = 1` forces `Uᴴ U = 1`.
3. **Columns are orthonormal** (`Remark4_5_5`): reading off the entries of
   `Uᴴ U = 1` gives the second orthogonality relation
   `∑_V χ_V(g⁻¹) χ_V(h) = |Z_g|` if `g ~ h`, else `0`.

The conjugate enters through `χ_V(g⁻¹) = conj(χ_V(g))`
(`Etingof.character_inv_eq_conj`), which makes `Uᴴ` the genuine conjugate
transpose.

## Mathlib correspondence

The conclusion is the column (second) orthogonality relation, the same statement as
`Etingof.Theorem4_5_4`, but obtained here by the independent unitary-matrix route of
Remark 4.5.5 (resting on the *first* orthogonality relation rather than the
Wedderburn trace computation).
-/

open CategoryTheory MulAction
open scoped Classical ComplexConjugate Matrix

namespace Etingof.Remark4_5_5

variable {G : Type} [Group G] [Fintype G]

/-- The order of the centralizer `Z_g` of `g` in `G`. -/
noncomputable def Zc (g : G) : ℕ := Nat.card (Subgroup.centralizer ({g} : Set G))

lemma Zc_pos (g : G) : 0 < Zc g := by
  rw [Zc]
  exact Nat.card_pos

/-- `ConjClasses.mk` of a chosen representative recovers the class. -/
lemma mk_out (c : ConjClasses G) : ConjClasses.mk (Quotient.out c) = c := by
  rw [← ConjClasses.quotient_mk_eq_mk]
  exact Quotient.out_eq c

/-- `χ_V(g⁻¹) = conj(χ_V(g))` for a complex representation of a finite group. -/
lemma char_star (W : FDRep ℂ G) (g : G) :
    star (W.character g) = W.character g⁻¹ := by
  rw [← starRingEnd_apply]
  exact (Etingof.character_inv_eq_conj W.ρ g).symm

/-- `√|Z_{g_c}|` as a complex number, where `g_c = Quotient.out c`. -/
noncomputable def sqZ (c : ConjClasses G) : ℂ :=
  (Real.sqrt (Zc (Quotient.out c) : ℝ) : ℂ)

lemma sqZ_pos_real (c : ConjClasses G) : 0 < Real.sqrt (Zc (Quotient.out c) : ℝ) :=
  Real.sqrt_pos.mpr (by exact_mod_cast Zc_pos (Quotient.out c))

lemma sqZ_ne (c : ConjClasses G) : sqZ c ≠ 0 := by
  rw [sqZ, Ne, Complex.ofReal_eq_zero]
  exact (sqZ_pos_real c).ne'

lemma star_sqZ (c : ConjClasses G) : star (sqZ c) = sqZ c := by
  rw [sqZ, ← starRingEnd_apply, Complex.conj_ofReal]

lemma sqZ_mul_self (c : ConjClasses G) :
    sqZ c * sqZ c = (Zc (Quotient.out c) : ℂ) := by
  rw [sqZ, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast]

/-- The character matrix `U` of Remark 4.5.5: rows indexed by irreducible
representations (a family `V` indexed by conjugacy classes), columns by conjugacy
classes, entries `χ_{V i}(g_j) / √|Z_{g_j}|`. -/
noncomputable def U (V : ConjClasses G → FDRep ℂ G) :
    Matrix (ConjClasses G) (ConjClasses G) ℂ :=
  fun i j => (V i).character (Quotient.out j) / sqZ j

/-- One entry of `U Uᴴ`: `U_{i,c} · conj(U_{j,c}) = χ_i(g_c) χ_j(g_c⁻¹) / |Z_{g_c}|`. -/
lemma U_mul_starU (V : ConjClasses G → FDRep ℂ G) (i j c : ConjClasses G) :
    U V i c * star (U V j c)
      = (V i).character (Quotient.out c) * (V j).character (Quotient.out c)⁻¹
          / (Zc (Quotient.out c) : ℂ) := by
  simp only [U]
  rw [star_div₀, char_star, star_sqZ, div_mul_div_comm, sqZ_mul_self]

/-- One entry of `Uᴴ U`: `conj(U_{i,c}) · U_{i,c'} = χ_i(g_c⁻¹) χ_i(g_c') / (√|Z_c|·√|Z_c'|)`. -/
lemma starU_mul_U (V : ConjClasses G → FDRep ℂ G) (i c c' : ConjClasses G) :
    star (U V i c) * U V i c'
      = (V i).character (Quotient.out c)⁻¹ * (V i).character (Quotient.out c')
          / (sqZ c * sqZ c') := by
  simp only [U]
  rw [star_div₀, char_star, star_sqZ, div_mul_div_comm]

/-- Fiber-cardinality identity: `|{a | ⟦a⟧ = c}| · |Z_{g_c}| = |G|` (orbit-stabilizer). -/
lemma fiber_card_mul_Zc (c : ConjClasses G) :
    (Finset.univ.filter (fun a : G => ConjClasses.mk a = c)).card * Zc (Quotient.out c)
      = Fintype.card G := by
  classical
  -- The fiber is the carrier of the class, i.e. the conjugation orbit of `g_c`.
  have hcarrier :
      (Finset.univ.filter (fun a : G => ConjClasses.mk a = c))
        = (c.carrier).toFinset := by
    ext a
    simp [ConjClasses.mem_carrier_iff_mk_eq]
  have horb : MulAction.orbit (ConjAct G) (Quotient.out c) = c.carrier := by
    rw [ConjAct.orbit_eq_carrier_conjClasses, mk_out]
  have hstab : Zc (Quotient.out c)
      = Fintype.card (MulAction.stabilizer (ConjAct G) (Quotient.out c)) := by
    rw [Zc, Subgroup.nat_card_centralizer_nat_card_stabilizer, Nat.card_eq_fintype_card]
  rw [hcarrier, Set.toFinset_card,
    Fintype.card_congr (Equiv.setCongr horb.symm), hstab,
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) (Quotient.out c),
    ConjAct.card]

/-- Averaging a class function over `G` equals the class-indexed sum weighted by
`1/|Z_{g_c}|`. This is the reindexing at the heart of Remark 4.5.5. -/
lemma sum_class_function (F : G → ℂ) (hF : ∀ a b : G, F (b * a * b⁻¹) = F a)
    [Invertible (Fintype.card G : ℂ)] :
    ∑ c : ConjClasses G, F (Quotient.out c) / (Zc (Quotient.out c) : ℂ)
      = ⅟(Fintype.card G : ℂ) • ∑ g : G, F g := by
  classical
  -- `F` is constant on each fiber, and the fiber has size `|G|/|Z|`.
  have key : ∀ c : ConjClasses G,
      ∑ a ∈ Finset.univ.filter (fun a : G => ConjClasses.mk a = c), F a
        = (Fintype.card G : ℂ) / (Zc (Quotient.out c) : ℂ) * F (Quotient.out c) := by
    intro c
    have hconst : ∀ a ∈ Finset.univ.filter (fun a : G => ConjClasses.mk a = c),
        F a = F (Quotient.out c) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      have hconj : ConjClasses.mk a = ConjClasses.mk (Quotient.out c) := by
        rw [ha, mk_out]
      obtain ⟨u, hu⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hconj)
      rw [← hu, hF]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [eq_div_iff (by exact_mod_cast (Zc_pos (Quotient.out c)).ne')]
    exact_mod_cast fiber_card_mul_Zc c
  have step : ∑ g : G, F g
      = ∑ c : ConjClasses G,
          (Fintype.card G : ℂ) / (Zc (Quotient.out c) : ℂ) * F (Quotient.out c) := by
    rw [← Finset.sum_fiberwise Finset.univ ConjClasses.mk F]
    exact Finset.sum_congr rfl (fun c _ => key c)
  rw [step, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [smul_eq_mul,
    show (Fintype.card G : ℂ) / (Zc (Quotient.out c) : ℂ) * F (Quotient.out c)
      = (Fintype.card G : ℂ) * (F (Quotient.out c) / (Zc (Quotient.out c) : ℂ)) from by ring,
    ← mul_assoc, invOf_mul_self, one_mul]

variable (V : ConjClasses G → FDRep ℂ G)

/-- **Rows of the character matrix are orthonormal** (`U Uᴴ = 1`).

This is the first orthogonality relation (Theorem 4.5.1) reindexed over conjugacy
classes. -/
theorem character_matrix_mul_conjTranspose
    [∀ i, Simple (V i)] (hdist : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    [Invertible (Fintype.card G : ℂ)] :
    U V * (U V)ᴴ = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  have hrow : (∑ c, U V i c * (U V)ᴴ c j)
      = ∑ c : ConjClasses G,
          (fun g => (V i).character g * (V j).character g⁻¹) (Quotient.out c)
            / (Zc (Quotient.out c) : ℂ) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [Matrix.conjTranspose_apply]
    exact U_mul_starU V i j c
  rw [hrow, sum_class_function (fun g => (V i).character g * (V j).character g⁻¹) ?hF]
  · rw [FDRep.char_orthonormal, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos ⟨Iso.refl _⟩, if_pos rfl]
    · rw [if_neg (fun hn => h (hdist i j hn)), if_neg h]
  case hF =>
    intro a b
    show (V i).character (b * a * b⁻¹) * (V j).character (b * a * b⁻¹)⁻¹
        = (V i).character a * (V j).character a⁻¹
    rw [show (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ from by group]
    rw [FDRep.char_conj, FDRep.char_conj]

/-- **The character matrix is unitary** (`Uᴴ U = 1`).

For a square matrix, orthonormality of the rows forces orthonormality of the
columns. -/
theorem character_matrix_conjTranspose_mul
    [∀ i, Simple (V i)] (hdist : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    [Invertible (Fintype.card G : ℂ)] :
    (U V)ᴴ * U V = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (ConjClasses G))).mp
    (character_matrix_mul_conjTranspose V hdist)

/-- **Remark 4.5.5: the second orthogonality relation via the unitary matrix.**

Reading off the `(c, c')` entry of `Uᴴ U = 1` gives column orthonormality:
`∑_V χ_V(g_c⁻¹) χ_V(g_c') = |Z_{g_c}|` if `c = c'`, else `0`. -/
theorem column_orthogonality
    [∀ i, Simple (V i)] (hdist : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    [Invertible (Fintype.card G : ℂ)] (c c' : ConjClasses G) :
    ∑ i : ConjClasses G,
        (V i).character (Quotient.out c)⁻¹ * (V i).character (Quotient.out c')
      = if c = c' then (Zc (Quotient.out c) : ℂ) else 0 := by
  classical
  have hU := character_matrix_conjTranspose_mul V hdist
  have h2 := congrFun (congrFun hU c) c'
  rw [Matrix.mul_apply] at h2
  simp only [Matrix.conjTranspose_apply] at h2
  rw [Finset.sum_congr rfl (fun i _ => starU_mul_U V i c c')] at h2
  rw [← Finset.sum_div, Matrix.one_apply] at h2
  rw [div_eq_iff (mul_ne_zero (sqZ_ne c) (sqZ_ne c'))] at h2
  rw [h2]
  by_cases hcc : c = c'
  · subst hcc
    rw [if_pos rfl, if_pos rfl, one_mul, sqZ_mul_self]
  · rw [if_neg hcc, if_neg hcc, zero_mul]

end Etingof.Remark4_5_5
