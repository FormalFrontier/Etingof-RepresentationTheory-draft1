/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! Results on commutator subgroups of two-dimensional general linear groups. -/

open Matrix

namespace RepresentationTheory.SpecialLinear.Commutator

variable {F : Type*} [Field F]

/-- An auxiliary group associated with a commutative ring. -/
abbrev AuxiliaryGroup (F : Type*) [CommRing F] := GeneralLinearGroup (Fin 2) F

/-- Associates an element of the auxiliary group to a scalar in a field. -/
def auxiliaryElement (t : F) : AuxiliaryGroup F where
  val := !![1, t; 0, 1]
  inv := !![1, -t; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

/-- Associates a second scalar-indexed element of the auxiliary group to a field scalar. -/
def auxiliaryElement' (t : F) : AuxiliaryGroup F where
  val := !![1, 0; t, 1]
  inv := !![1, 0; -t, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

/-- Constructs an auxiliary group element from two nonzero field elements. -/
def auxiliaryElementOfNonzero (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) : AuxiliaryGroup F where
  val := !![a, 0; 0, b]
  inv := !![a⁻¹, 0; 0, b⁻¹]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb]

/-- A fixed element of the auxiliary group over a field. -/
def auxiliaryConstant : AuxiliaryGroup F where
  val := !![0, 1; -1, 0]
  inv := !![0, -1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

/-- Every group commutator is an element of the commutator subgroup. -/
theorem commutator_mem (g h : AuxiliaryGroup F) :
    g * h * g⁻¹ * h⁻¹ ∈ commutator (AuxiliaryGroup F) :=
  Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)

/-- Computes the commutator expression involving a nonzero parameter and a scalar-indexed auxiliary element. -/
theorem auxiliaryElement_commutator_eq (a t : F) (ha : a ≠ 0) :
    auxiliaryElementOfNonzero a 1 ha one_ne_zero * auxiliaryElement t * (auxiliaryElementOfNonzero a 1 ha one_ne_zero)⁻¹ * (auxiliaryElement t)⁻¹ =
      auxiliaryElement ((a - 1) * t) := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, auxiliaryElement, auxiliaryElementOfNonzero, Units.inv_mk] <;> field_simp ; ring

/-- Computes the corresponding commutator expression for the second scalar-indexed auxiliary element. -/
theorem auxiliaryElement'_commutator_eq (a t : F) (ha : a ≠ 0) :
    auxiliaryElementOfNonzero 1 a one_ne_zero ha * auxiliaryElement' t * (auxiliaryElementOfNonzero 1 a one_ne_zero ha)⁻¹ * (auxiliaryElement' t)⁻¹ =
      auxiliaryElement' ((a - 1) * t) := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, auxiliaryElement', auxiliaryElementOfNonzero, Units.inv_mk] <;> field_simp ; ring

/-- Evaluates the commutator expression of a parameterized auxiliary element with the fixed auxiliary element. -/
theorem auxiliaryElement_commutator_constant_eq (d : F) (hd : d ≠ 0) :
    auxiliaryElementOfNonzero d 1 hd one_ne_zero * auxiliaryConstant * (auxiliaryElementOfNonzero d 1 hd one_ne_zero)⁻¹ * auxiliaryConstant⁻¹ =
      auxiliaryElementOfNonzero d d⁻¹ hd (inv_ne_zero hd) := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, auxiliaryElementOfNonzero, auxiliaryConstant, Units.inv_mk]

/-- The scalar-indexed auxiliary element belongs to the commutator subgroup when a field element is neither zero nor one. -/
theorem auxiliaryElement_mem_commutator (t : F) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    auxiliaryElement (F := F) t ∈ commutator (AuxiliaryGroup F) := by
  have hsub : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  rw [show auxiliaryElement t = auxiliaryElementOfNonzero a 1 ha0 one_ne_zero * auxiliaryElement (t * (a - 1)⁻¹) *
      (auxiliaryElementOfNonzero a 1 ha0 one_ne_zero)⁻¹ * (auxiliaryElement (t * (a - 1)⁻¹))⁻¹
    from by rw [auxiliaryElement_commutator_eq]; congr 1; field_simp]
  exact commutator_mem _ _

/-- The second scalar-indexed auxiliary element lies in the commutator subgroup when a field parameter is distinct from zero and one. -/
theorem auxiliaryElement'_mem_commutator (t : F) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    auxiliaryElement' (F := F) t ∈ commutator (AuxiliaryGroup F) := by
  have hsub : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  rw [show auxiliaryElement' t = auxiliaryElementOfNonzero 1 a one_ne_zero ha0 * auxiliaryElement' (t * (a - 1)⁻¹) *
      (auxiliaryElementOfNonzero 1 a one_ne_zero ha0)⁻¹ * (auxiliaryElement' (t * (a - 1)⁻¹))⁻¹
    from by rw [auxiliaryElement'_commutator_eq]; congr 1; field_simp]
  exact commutator_mem _ _

/-- The auxiliary element formed from a nonzero scalar and its inverse belongs to the commutator subgroup. -/
theorem auxiliaryElementOfNonzero_mem_commutator (d : F) (hd : d ≠ 0) :
    auxiliaryElementOfNonzero (F := F) d d⁻¹ hd (inv_ne_zero hd) ∈ commutator (AuxiliaryGroup F) := by
  rw [show auxiliaryElementOfNonzero d d⁻¹ hd (inv_ne_zero hd) =
    auxiliaryElementOfNonzero d 1 hd one_ne_zero * auxiliaryConstant * (auxiliaryElementOfNonzero d 1 hd one_ne_zero)⁻¹ * auxiliaryConstant⁻¹
    from (auxiliaryElement_commutator_constant_eq d hd).symm]
  exact commutator_mem _ _

/-- A field with cardinality greater than two has an element distinct from both zero and one. -/
theorem exists_ne_zero_ne_one_of_two_lt_card (hcard : 2 < Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hcard
  by_contra h; push Not at h
  have huniv : ∀ x : F, x = 0 ∨ x = 1 := fun x => by
    by_contra hx; push Not at hx; exact absurd (h x hx.1) hx.2
  have : Fintype.card F ≤ 2 := Fintype.card_le_of_surjective
    (fun b : Bool => if b then (1 : F) else 0)
    (fun x => by
      rcases huniv x with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩)
    |>.trans (by simp [Fintype.card_bool])
  omega

/-- If the field has an element distinct from zero and one, every embedded two-dimensional special linear element lies in the commutator subgroup. -/
theorem specialLinear_mem_commutator (s : SpecialLinearGroup (Fin 2) F)
    (a₀ : F) (ha0 : a₀ ≠ 0) (ha1 : a₀ ≠ 1) :
    SpecialLinearGroup.toGL s ∈ commutator (AuxiliaryGroup F) := by
  set M := (s : Matrix (Fin 2) (Fin 2) F)
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := s.prop; rwa [det_fin_two] at this
  by_cases hc : M 1 0 = 0
  ·
    have had : M 0 0 * M 1 1 = 1 := by rw [hc, mul_zero, sub_zero] at hdet; exact hdet
    have ha_ne : M 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one had
    have hd_eq : M 1 1 = (M 0 0)⁻¹ :=
      mul_left_cancel₀ ha_ne (had.trans (mul_inv_cancel₀ ha_ne).symm)
    have hM : ∀ i j, (↑s : Matrix (Fin 2) (Fin 2) F) i j = M i j := fun _ _ => rfl
    have hval : SpecialLinearGroup.toGL s =
        auxiliaryElementOfNonzero (M 0 0) (M 0 0)⁻¹ ha_ne (inv_ne_zero ha_ne) *
        auxiliaryElement ((M 0 0)⁻¹ * M 0 1) := by
      apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
        simp [Units.val_mul, auxiliaryElement, auxiliaryElementOfNonzero, mul_apply, Fin.sum_univ_two,
          SpecialLinearGroup.coe_GL_coe_matrix, hM, hc, hd_eq] ;
        field_simp
    rw [hval]
    exact (commutator _).mul_mem (auxiliaryElementOfNonzero_mem_commutator _ ha_ne)
      (auxiliaryElement_mem_commutator _ a₀ ha0 ha1)
  ·
    have hM : ∀ i j, (↑s : Matrix (Fin 2) (Fin 2) F) i j = M i j := fun _ _ => rfl
    have hval : SpecialLinearGroup.toGL s =
        auxiliaryElement ((M 0 0 - 1) / M 1 0) * auxiliaryElement' (M 1 0) * auxiliaryElement ((M 1 1 - 1) / M 1 0) := by
      have hbc : M 0 1 * M 1 0 = M 0 0 * M 1 1 - 1 := by
        clear_value M; linear_combination -hdet
      apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
        simp [Units.val_mul, auxiliaryElement, auxiliaryElement', mul_apply, Fin.sum_univ_two,
          SpecialLinearGroup.coe_GL_coe_matrix, hM]
      ·
        rw [div_mul_cancel₀ _ hc]; ring
      ·
        rw [div_mul_cancel₀ _ hc]
        clear_value M; field_simp; linear_combination hbc
      ·
        rw [mul_div_cancel₀ _ hc]; ring
    rw [hval]
    exact (commutator _).mul_mem
      ((commutator _).mul_mem (auxiliaryElement_mem_commutator _ a₀ ha0 ha1)
        (auxiliaryElement'_mem_commutator _ a₀ ha0 ha1))
      (auxiliaryElement_mem_commutator _ a₀ ha0 ha1)

/-- For a positive-degree Galois field with more than two elements, the commutator subgroup of its two-dimensional general linear group equals the range of the special linear group embedding. -/
@[source_ref "Chapter5/Proposition5.25.1" (role := supporting)]
theorem generalLinear_commutator_eq_specialLinear_range
    (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ) (_hn : 0 < n)
    (hq : 2 < Nat.card (GaloisField p n)) :
    commutator (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) =
      (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := GaloisField p n)).range := by
  apply le_antisymm
  ·
    intro g hg
    rw [MonoidHom.mem_range]
    have hdet : g ∈ (Matrix.GeneralLinearGroup.det).ker :=
      Abelianization.commutator_subset_ker _ hg
    rw [MonoidHom.mem_ker] at hdet
    exact ⟨⟨g, Units.ext_iff.mp hdet⟩, Units.ext rfl⟩
  ·
    intro g hg
    obtain ⟨s, rfl⟩ := hg
    obtain ⟨a₀, ha0, ha1⟩ := exists_ne_zero_ne_one_of_two_lt_card hq
    exact specialLinear_mem_commutator s a₀ ha0 ha1

end RepresentationTheory.SpecialLinear.Commutator
