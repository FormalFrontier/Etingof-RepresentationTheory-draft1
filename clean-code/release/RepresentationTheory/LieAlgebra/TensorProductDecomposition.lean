/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Lie.DirectSum
import RepresentationTheory.Polynomial.Recurrences
import RepresentationTheory.LieModule.CentralAction
import RepresentationTheory.Alignment.Attribute

open scoped TensorProduct DirectSum

namespace RepresentationTheory.LieAlgebra.TensorProductDecomposition



section Ladder

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra M] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra M]


/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux1 (n : ℕ) (w : M) : M := (fun v => ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, v⁆)^[n] w

omit [Module ℂ M] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra M] in

/-- The two displayed expressions are equal. -/
@[simp] theorem displayed_eq_aux6 (w : M) : distinguishedElement_aux1 0 w = w := rfl

omit [Module ℂ M] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra M] in

/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux5 (n : ℕ) (w : M) : distinguishedElement_aux1 (n + 1) w = ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, distinguishedElement_aux1 n w⁆ :=
  Function.iterate_succ_apply' _ _ _


/-- The indexed iterate agrees with the corresponding power of the displayed Lie action. -/
theorem iterate_eq_pow_action (n : ℕ) (w : M) :
    distinguishedElement_aux1 n w = ((LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra M _root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement) ^ n) w := by
  have hfun : (fun v => ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, v⁆) = ⇑(LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra M _root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement) := by
    funext v; rw [LieModule.toEnd_apply_apply]
  rw [distinguishedElement_aux1, Module.End.pow_apply, hfun]


/-- The weight bracket on an iterate has eigenvalue `ν - 2n`. -/
theorem weight_bracket_iterate (ν : ℂ) (w : M) (hH : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, w⁆ = ν • w) (n : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, distinguishedElement_aux1 n w⁆ = (ν - 2 * n) • distinguishedElement_aux1 n w := by
  induction n with
  | zero => simpa using hH
  | succ n ih =>
    rw [bracket_eq_aux5, leibniz_lie _root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement _root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_weight_lowering, ih]
    rw [neg_lie, nsmul_lie, lie_smul, two_nsmul]
    push_cast
    module


/-- The raising bracket on the next iterate equals the stated scalar multiple of the preceding iterate. -/
theorem raising_bracket_iterate (ν : ℂ) (w : M) (hE : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, w⁆ = 0) (hH : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, w⁆ = ν • w)
    (n : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, distinguishedElement_aux1 (n + 1) w⁆ = (((n : ℂ) + 1) * (ν - n)) • distinguishedElement_aux1 n w := by
  induction n with
  | zero =>
    rw [bracket_eq_aux5, displayed_eq_aux6, leibniz_lie _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement _root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_raising_lowering, hE, lie_zero, add_zero, hH]
    push_cast; module
  | succ n ih =>
    rw [bracket_eq_aux5, leibniz_lie _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement _root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_raising_lowering,
      weight_bracket_iterate ν w hH (n + 1), ih, lie_smul, ← bracket_eq_aux5]
    push_cast
    module

end Ladder



section Intertwine

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
  [AddCommGroup W] [Module ℂ W] [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W]


/-- A linear map commuting with the action of the three displayed generators commutes with the action of every Lie element. -/
theorem map_bracket_eq_of_generators (φ : V →ₗ[ℂ] W)
    (hh : ∀ v, φ ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, φ v⁆)
    (he : ∀ v, φ ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, φ v⁆)
    (hf : ∀ v, φ ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, φ v⁆)
    (x : _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : V) : φ ⁅x, v⁆ = ⁅x, φ v⁆ := by
  conv_lhs => rw [_root_.RepresentationTheory.LieModule.CentralAction.eq_linearCombination_generators x]
  conv_rhs => rw [_root_.RepresentationTheory.LieModule.CentralAction.eq_linearCombination_generators x]
  simp only [add_lie, smul_lie, map_add, map_smul, hh, he, hf]


/-- A homomorphism between the displayed Lie modules. -/
def lieModuleHom_aux2 (φ : V →ₗ[ℂ] W)
    (hh : ∀ v, φ ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, φ v⁆)
    (he : ∀ v, φ ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, φ v⁆)
    (hf : ∀ v, φ ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, φ v⁆) :
    V →ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ W :=
  { φ with map_lie' := fun {x v} => map_bracket_eq_of_generators φ hh he hf x v }


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux5 (φ : V →ₗ[ℂ] W) (hh he hf) (v : V) :
    lieModuleHom_aux2 φ hh he hf v = φ v := rfl

end Intertwine

variable (lam mu : ℕ)


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux12 (x : _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (v : Fin (lam + 1) → ℂ) (w : Fin (mu + 1) → ℂ) :
    ⁅x, v ⊗ₜ[ℂ] w⁆ = ⁅x, v⁆ ⊗ₜ[ℂ] w + v ⊗ₜ[ℂ] ⁅x, w⁆ :=
  TensorProduct.LieModule.lie_tmul_right x v w


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux11 (x : _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (c : ℂ)
    (m : (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) :
    ⁅x, c • m⁆ = c • ⁅x, m⁆ :=
  lie_smul c x m


/-- A distinguished element of the displayed tensor product. -/
noncomputable def distinguishedTensor (k : ℕ) (hk : k ≤ min lam mu) :
    (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) :=
  ∑ i : Fin (k + 1),
    ((-1) ^ (i : ℕ) * (k.choose (i : ℕ) : ℂ)) •
      (_root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + 1) ⟨(i : ℕ), by omega⟩ ⊗ₜ[ℂ]
        _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (mu + 1) ⟨k - (i : ℕ), by omega⟩)


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux9 (k : ℕ) (hk : k ≤ min lam mu) :
    ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, distinguishedTensor lam mu k hk⁆ = ((lam : ℂ) + mu - 2 * k) • distinguishedTensor lam mu k hk := by
  rw [distinguishedTensor, lie_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hik : (i : ℕ) ≤ k := by omega
  rw [bracket_eq_aux11, bracket_eq_aux12, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_weight_coordinateVector, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_weight_coordinateVector,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← add_smul, smul_smul, smul_smul]
  congr 1
  push_cast [Nat.cast_sub hik]
  ring


private noncomputable def raisingFirstSummand (k : ℕ) (hk : k ≤ min lam mu) (i : Fin (k + 1)) :
    (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) :=
  (((-1) ^ (i : ℕ) * (k.choose (i : ℕ) : ℂ)) * (i : ℕ)) •
    (_root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + 1) ⟨(i : ℕ) - 1, by omega⟩ ⊗ₜ[ℂ]
      _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (mu + 1) ⟨k - (i : ℕ), by omega⟩)


private noncomputable def raisingSecondSummand (k : ℕ) (hk : k ≤ min lam mu) (i : Fin (k + 1)) :
    (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) :=
  (((-1) ^ (i : ℕ) * (k.choose (i : ℕ) : ℂ)) * ((k - (i : ℕ) : ℕ) : ℂ)) •
    (_root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + 1) ⟨(i : ℕ), by omega⟩ ⊗ₜ[ℂ]
      _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (mu + 1) ⟨k - (i : ℕ) - 1, by omega⟩)


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux7 (k : ℕ) (hk : k ≤ min lam mu) :
    ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, distinguishedTensor lam mu k hk⁆ = 0 := by
  rw [distinguishedTensor, lie_sum]
  have hterm : ∀ i : Fin (k + 1),
      ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, ((-1) ^ (i : ℕ) * (k.choose (i : ℕ) : ℂ)) •
        (_root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + 1) ⟨(i : ℕ), by omega⟩ ⊗ₜ[ℂ]
          _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (mu + 1) ⟨k - (i : ℕ), by omega⟩)⁆
        = raisingFirstSummand lam mu k hk i + raisingSecondSummand lam mu k hk i := by
    intro i
    rw [bracket_eq_aux11, bracket_eq_aux12,
      _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_raising_coordinateVector (lam + 1) (i : ℕ) (by omega),
      _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_raising_coordinateVector (mu + 1) (k - (i : ℕ)) (by omega),
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add, smul_smul, smul_smul]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
  conv_lhs =>
    rw [Fin.sum_univ_succ (raisingFirstSummand lam mu k hk), Fin.sum_univ_castSucc (raisingSecondSummand lam mu k hk)]
  rw [show raisingFirstSummand lam mu k hk 0 = 0 by simp [raisingFirstSummand],
    show raisingSecondSummand lam mu k hk (Fin.last k) = 0 by simp [raisingSecondSummand, Fin.val_last],
    zero_add, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  have hik : (i : ℕ) ≤ k := by omega
  have key : (k.choose ((i : ℕ) + 1) : ℂ) * (((i : ℕ) + 1 : ℕ) : ℂ)
      = (k.choose (i : ℕ) : ℂ) * ((k - (i : ℕ) : ℕ) : ℂ) := by
    exact_mod_cast Nat.choose_succ_right_eq k (i : ℕ)
  simp only [raisingFirstSummand, raisingSecondSummand, Fin.val_succ, Fin.val_castSucc,
    Nat.add_sub_cancel, Nat.sub_sub]
  rw [← add_smul]
  convert zero_smul ℂ _ using 2
  rw [pow_succ]
  linear_combination (-(-1 : ℂ) ^ (i : ℕ)) * key


/-- The specified element is nonzero. -/
theorem distinguished_ne_zero (k : ℕ) (hk : k ≤ min lam mu) : distinguishedTensor lam mu k hk ≠ 0 := by
  have hkmu : k < mu + 1 := by omega

  set φ : (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) →ₗ[ℂ] ℂ :=
    TensorProduct.lift
      ((LinearMap.mul ℂ ℂ).compl₁₂ (LinearMap.proj (0 : Fin (lam + 1)))
        (LinearMap.proj (⟨k, hkmu⟩ : Fin (mu + 1)))) with hφ
  have hval : φ (distinguishedTensor lam mu k hk) = 1 := by
    rw [distinguishedTensor, map_sum]
    rw [Finset.sum_eq_single (0 : Fin (k + 1))]
    · simp [hφ, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector_apply]
    · intro i _ hi
      have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp only [hφ, map_smul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply,
        LinearMap.proj_apply, LinearMap.mul_apply', _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector_apply]
      rw [if_neg (by rw [Fin.ext_iff]; simpa using hi'.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  intro h0
  rw [h0, map_zero] at hval
  exact zero_ne_one hval




/-- The distinguished tensor is a primitive vector with the displayed weight for the specified sl2-triple. -/
theorem hasPrimitiveVectorWith (k : ℕ) (hk : k ≤ min lam mu) :
    IsSl2Triple.HasPrimitiveVectorWith _root_.RepresentationTheory.LieAlgebra.Sl2Representations.isSl2Triple_weight_raising_lowering (distinguishedTensor lam mu k hk)
      ((lam : ℂ) + mu - 2 * k) where
  ne_zero := distinguished_ne_zero lam mu k hk
  lie_h := bracket_eq_aux9 lam mu k hk
  lie_e := bracket_eq_aux7 lam mu k hk


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux5 (k : ℕ) (hk : k ≤ min lam mu) :
    distinguishedElement_aux1 (lam + mu - 2 * k + 1) (distinguishedTensor lam mu k hk) = 0 := by
  have hk2 : 2 * k ≤ lam + mu := by omega
  have hcast : ((lam : ℂ) + mu - 2 * k) = ((lam + mu - 2 * k : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hk2]; ring
  have hzero := (hasPrimitiveVectorWith lam mu k hk).pow_toEnd_f_eq_zero_of_eq_nat hcast
  rw [iterate_eq_pow_action]
  exact hzero




/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq (k : ℕ) (hk : k ≤ min lam mu) :
    ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, distinguishedTensor lam mu k hk⁆⁆
        + ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, distinguishedTensor lam mu k hk⁆⁆
        + (2⁻¹ : ℂ) • ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, distinguishedTensor lam mu k hk⁆⁆
      = ((((lam : ℂ) + mu - 2 * k) * ((lam : ℂ) + mu - 2 * k + 2)) / 2)
          • distinguishedTensor lam mu k hk := by
  have hE : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, distinguishedTensor lam mu k hk⁆ = 0 := bracket_eq_aux7 lam mu k hk
  have hH : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, distinguishedTensor lam mu k hk⁆
      = ((lam : ℂ) + mu - 2 * k) • distinguishedTensor lam mu k hk := bracket_eq_aux9 lam mu k hk

  have hEF : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, distinguishedTensor lam mu k hk⁆⁆
      = ((lam : ℂ) + mu - 2 * k) • distinguishedTensor lam mu k hk := by
    rw [leibniz_lie _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement _root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_raising_lowering, hH, hE, lie_zero, add_zero]

  have hFE : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, distinguishedTensor lam mu k hk⁆⁆ = 0 := by rw [hE, lie_zero]

  have hHH : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, distinguishedTensor lam mu k hk⁆⁆
      = (((lam : ℂ) + mu - 2 * k) * ((lam : ℂ) + mu - 2 * k)) • distinguishedTensor lam mu k hk := by
    rw [hH, bracket_eq_aux11, hH, smul_smul]
  rw [hEF, hFE, hHH, add_zero, smul_smul, ← add_smul]
  congr 1
  ring


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux1 {k k' : ℕ} (hk : k ≤ min lam mu) (hk' : k' ≤ min lam mu)
    (h : ((lam : ℂ) + mu - 2 * k) * ((lam : ℂ) + mu - 2 * k + 2)
        = ((lam : ℂ) + mu - 2 * k') * ((lam : ℂ) + mu - 2 * k' + 2)) :
    k = k' := by

  have hfactor :
      (((lam : ℂ) + mu - 2 * k) - ((lam : ℂ) + mu - 2 * k'))
        * (((lam : ℂ) + mu - 2 * k) + ((lam : ℂ) + mu - 2 * k') + 2) = 0 := by
    linear_combination h

  have hsum :
      ((lam : ℂ) + mu - 2 * k) + ((lam : ℂ) + mu - 2 * k') + 2
        = ((2 * lam + 2 * mu + 2 : ℕ) : ℂ) - ((2 * k + 2 * k' : ℕ) : ℂ) := by
    push_cast; ring
  have hpos :
      ((lam : ℂ) + mu - 2 * k) + ((lam : ℂ) + mu - 2 * k') + 2 ≠ 0 := by
    rw [hsum, sub_ne_zero, Ne, Nat.cast_inj]; omega

  have hab : ((lam : ℂ) + mu - 2 * k) - ((lam : ℂ) + mu - 2 * k') = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right hpos
  have hkk : (k : ℂ) = (k' : ℂ) := by linear_combination (-2⁻¹ : ℂ) * hab
  exact_mod_cast hkk




/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux10 (k : ℕ) (hk : k ≤ min lam mu) (n : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, distinguishedElement_aux1 n (distinguishedTensor lam mu k hk)⁆
      = ((lam : ℂ) + mu - 2 * k - 2 * n) • distinguishedElement_aux1 n (distinguishedTensor lam mu k hk) :=
  weight_bracket_iterate ((lam : ℂ) + mu - 2 * k) (distinguishedTensor lam mu k hk)
    (bracket_eq_aux9 lam mu k hk) n


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux8 (k : ℕ) (hk : k ≤ min lam mu) (n : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, distinguishedElement_aux1 (n + 1) (distinguishedTensor lam mu k hk)⁆
      = (((n : ℂ) + 1) * ((lam : ℂ) + mu - 2 * k - n)) • distinguishedElement_aux1 n (distinguishedTensor lam mu k hk) :=
  raising_bracket_iterate ((lam : ℂ) + mu - 2 * k) (distinguishedTensor lam mu k hk)
    (bracket_eq_aux7 lam mu k hk) (bracket_eq_aux9 lam mu k hk) n




/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply (d : ℕ) (n : Fin d) :
    Pi.basisFun ℂ (Fin d) n = _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector d n := by
  ext j; simp [_root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector, Pi.basisFun_apply, Pi.single_apply]


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux2 (nu m : ℕ) (hm : m < nu) :
    (Nat.descFactorial nu (m + 1) : ℂ)⁻¹ * ((nu : ℂ) - m) = (Nat.descFactorial nu m : ℂ)⁻¹ := by
  have hle : m ≤ nu := le_of_lt hm
  have hpos : (Nat.descFactorial nu m : ℂ) ≠ 0 := by
    have := Nat.descFactorial_pos.mpr hle
    exact_mod_cast this.ne'
  have hnm : (nu : ℂ) - m ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => (ne_of_lt hm) ((by exact_mod_cast h : (nu : ℕ) = m).symm)
  rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hle, mul_inv]
  field_simp

variable (lam mu : ℕ)


/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux1 (k : ℕ) (hk : k ≤ min lam mu) :
    (Fin (lam + mu - 2 * k + 1) → ℂ) →ₗ[ℂ]
      (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) :=
  (Pi.basisFun ℂ (Fin (lam + mu - 2 * k + 1))).constr ℂ
    fun n => ((Nat.descFactorial (lam + mu - 2 * k) (n : ℕ) : ℂ)⁻¹) •
      distinguishedElement_aux1 (n : ℕ) (distinguishedTensor lam mu k hk)


/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux4 (k : ℕ) (hk : k ≤ min lam mu)
    (n : Fin (lam + mu - 2 * k + 1)) :
    linearMap_aux1 lam mu k hk (_root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + mu - 2 * k + 1) n)
      = (Nat.descFactorial (lam + mu - 2 * k) (n : ℕ) : ℂ)⁻¹ •
        distinguishedElement_aux1 (n : ℕ) (distinguishedTensor lam mu k hk) := by
  rw [← map_apply, linearMap_aux1]
  exact (Pi.basisFun ℂ (Fin (lam + mu - 2 * k + 1))).constr_basis ℂ _ n


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux4 (k : ℕ) (hk : k ≤ min lam mu) (v : Fin (lam + mu - 2 * k + 1) → ℂ) :
    linearMap_aux1 lam mu k hk ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement, linearMap_aux1 lam mu k hk v⁆ := by
  have hcast : (lam : ℂ) + mu - 2 * k = ((lam + mu - 2 * k : ℕ) : ℂ) := by
    have h2 : 2 * k ≤ lam + mu := by omega
    push_cast [Nat.cast_sub h2]; ring
  have key : (linearMap_aux1 lam mu k hk).comp (LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra _ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement)
           = (LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra _ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement).comp (linearMap_aux1 lam mu k hk) := by
    refine (Pi.basisFun ℂ (Fin (lam + mu - 2 * k + 1))).ext fun n => ?_
    simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, map_apply]
    rw [_root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_weight_coordinateVector, map_smul, map_apply_aux4, bracket_eq_aux11, bracket_eq_aux10,
      smul_smul, smul_smul]
    congr 1
    rw [hcast]; push_cast; ring
  have := LinearMap.congr_fun key v
  simpa only [LinearMap.comp_apply, LieModule.toEnd_apply_apply] using this


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux2 (k : ℕ) (hk : k ≤ min lam mu) (v : Fin (lam + mu - 2 * k + 1) → ℂ) :
    linearMap_aux1 lam mu k hk ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, linearMap_aux1 lam mu k hk v⁆ := by
  have hcast : (lam : ℂ) + mu - 2 * k = ((lam + mu - 2 * k : ℕ) : ℂ) := by
    have h2 : 2 * k ≤ lam + mu := by omega
    push_cast [Nat.cast_sub h2]; ring
  have key : (linearMap_aux1 lam mu k hk).comp (LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra _ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement)
           = (LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra _ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement).comp (linearMap_aux1 lam mu k hk) := by
    refine (Pi.basisFun ℂ (Fin (lam + mu - 2 * k + 1))).ext fun n => ?_
    simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, map_apply]
    rcases Nat.eq_zero_or_pos (n : ℕ) with hn0 | hnpos
    ·
      have hL : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + mu - 2 * k + 1) n⁆ = 0 := by
        have h := _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_raising_coordinateVector (lam + mu - 2 * k + 1) (n : ℕ) n.isLt
        rw [Fin.eta] at h
        rw [h, show ((n : ℕ) : ℂ) = 0 by rw [hn0]; simp, zero_smul]
      rw [hL, map_zero, map_apply_aux4, bracket_eq_aux11, hn0, displayed_eq_aux6, bracket_eq_aux7,
        smul_zero]
    ·
      obtain ⟨m, hm⟩ : ∃ m, (n : ℕ) = m + 1 := ⟨(n : ℕ) - 1, by omega⟩
      have hmnu : m < lam + mu - 2 * k := by omega
      have hL : linearMap_aux1 lam mu k hk ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + mu - 2 * k + 1) n⁆
          = ((n : ℕ) : ℂ) • ((Nat.descFactorial (lam + mu - 2 * k) ((n : ℕ) - 1) : ℂ)⁻¹
              • distinguishedElement_aux1 ((n : ℕ) - 1) (distinguishedTensor lam mu k hk)) := by
        have h := _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_raising_coordinateVector (lam + mu - 2 * k + 1) (n : ℕ) n.isLt
        rw [Fin.eta] at h
        rw [h, map_smul, map_apply_aux4]
      have hR : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, linearMap_aux1 lam mu k hk (_root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + mu - 2 * k + 1) n)⁆
          = (Nat.descFactorial (lam + mu - 2 * k) (n : ℕ) : ℂ)⁻¹
              • ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, distinguishedElement_aux1 (n : ℕ) (distinguishedTensor lam mu k hk)⁆ := by
        rw [map_apply_aux4, bracket_eq_aux11]
      rw [hL, hR, hm, Nat.add_sub_cancel, bracket_eq_aux8, smul_smul, smul_smul, hcast]
      congr 1
      have hc := displayed_eq_aux2 (lam + mu - 2 * k) m hmnu
      rw [← hc]; push_cast; ring
  have := LinearMap.congr_fun key v
  simpa only [LinearMap.comp_apply, LieModule.toEnd_apply_apply] using this


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux3 (k : ℕ) (hk : k ≤ min lam mu) (v : Fin (lam + mu - 2 * k + 1) → ℂ) :
    linearMap_aux1 lam mu k hk ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, linearMap_aux1 lam mu k hk v⁆ := by
  have hcast : (lam : ℂ) + mu - 2 * k = ((lam + mu - 2 * k : ℕ) : ℂ) := by
    have h2 : 2 * k ≤ lam + mu := by omega
    push_cast [Nat.cast_sub h2]; ring
  have key : (linearMap_aux1 lam mu k hk).comp (LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra _ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement)
           = (LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra _ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement).comp (linearMap_aux1 lam mu k hk) := by
    refine (Pi.basisFun ℂ (Fin (lam + mu - 2 * k + 1))).ext fun n => ?_
    simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, map_apply]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp n.isLt) with hlt | htop
    ·
      have hL : linearMap_aux1 lam mu k hk ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + mu - 2 * k + 1) n⁆
          = (((lam + mu - 2 * k + 1 : ℕ) : ℂ) - 1 - (n : ℕ))
              • ((Nat.descFactorial (lam + mu - 2 * k) ((n : ℕ) + 1) : ℂ)⁻¹
                  • distinguishedElement_aux1 ((n : ℕ) + 1) (distinguishedTensor lam mu k hk)) := by
        have h := _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_lowering_coordinateVector (lam + mu - 2 * k + 1) (n : ℕ) (by omega)
        rw [Fin.eta] at h
        rw [h, map_smul, map_apply_aux4]
      have hR : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, linearMap_aux1 lam mu k hk (_root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + mu - 2 * k + 1) n)⁆
          = (Nat.descFactorial (lam + mu - 2 * k) (n : ℕ) : ℂ)⁻¹
              • distinguishedElement_aux1 ((n : ℕ) + 1) (distinguishedTensor lam mu k hk) := by
        rw [map_apply_aux4, bracket_eq_aux11, ← bracket_eq_aux5]
      rw [hL, hR, smul_smul]
      congr 1
      have hc := displayed_eq_aux2 (lam + mu - 2 * k) (n : ℕ) hlt
      rw [← hc]; push_cast; ring
    ·
      have hL : linearMap_aux1 lam mu k hk ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + mu - 2 * k + 1) n⁆ = 0 := by
        have h := _root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_lowering_coordinateVector_eq_zero (lam + mu - 2 * k + 1) (n : ℕ) n.isLt (by omega)
        rw [Fin.eta] at h
        rw [h, map_zero]
      rw [hL, map_apply_aux4, bracket_eq_aux11, ← bracket_eq_aux5, htop, displayed_eq_aux5,
        smul_zero]
  have := LinearMap.congr_fun key v
  simpa only [LinearMap.comp_apply, LieModule.toEnd_apply_apply] using this


/-- A homomorphism between the displayed Lie modules. -/
noncomputable def lieModuleHom_aux1 (k : ℕ) (hk : k ≤ min lam mu) :
    (Fin (lam + mu - 2 * k + 1) → ℂ) →ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆
      (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) :=
  lieModuleHom_aux2 (linearMap_aux1 lam mu k hk) (bracket_eq_aux4 lam mu k hk) (bracket_eq_aux2 lam mu k hk)
    (bracket_eq_aux3 lam mu k hk)


/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux3 (k : ℕ) (hk : k ≤ min lam mu)
    (v : Fin (lam + mu - 2 * k + 1) → ℂ) : lieModuleHom_aux1 lam mu k hk v = linearMap_aux1 lam mu k hk v := rfl


/-- The displayed map is injective. -/
theorem map_injective (k : ℕ) (hk : k ≤ min lam mu) :
    Function.Injective (lieModuleHom_aux1 lam mu k hk) := by
  haveI : NeZero (lam + mu - 2 * k + 1) := ⟨Nat.succ_ne_zero _⟩
  haveI := _root_.RepresentationTheory.LieAlgebra.Sl2Representations.isIrreducible_finFunction (lam + mu - 2 * k + 1)
  rw [← LieModuleHom.ker_eq_bot]
  rcases eq_bot_or_eq_top (lieModuleHom_aux1 lam mu k hk).ker with h | h
  · exact h
  ·
    exfalso
    have hmem : _root_.RepresentationTheory.LieAlgebra.Sl2Representations.coordinateVector (lam + mu - 2 * k + 1) ⟨0, Nat.succ_pos _⟩ ∈ (lieModuleHom_aux1 lam mu k hk).ker :=
      h ▸ trivial
    rw [LieModuleHom.mem_ker, map_apply_aux3, map_apply_aux4] at hmem
    simp only [Nat.descFactorial_zero, Nat.cast_one, inv_one, one_smul,
      displayed_eq_aux6] at hmem
    exact distinguished_ne_zero lam mu k hk hmem


/-- There exists a Lie-module equivalence from the displayed standard module to the image of the top submodule. -/
theorem nonempty_lieModuleEquiv_map_top (k : ℕ) (hk : k ≤ min lam mu) :
    Nonempty ((Fin (lam + mu - 2 * k + 1) → ℂ) ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆
      (LieSubmodule.map (lieModuleHom_aux1 lam mu k hk) ⊤ :
        LieSubmodule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)))) :=
  ⟨(LieModuleEquiv.ofTop (R := ℂ) (L := _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra)
      (M := Fin (lam + mu - 2 * k + 1) → ℂ)).symm.trans
    (LieSubmodule.equivMapOfInjective ⊤ (map_injective lam mu k hk))⟩




/-- The canonical Lie-module endomorphism agrees with the displayed representation map. -/
theorem toEnd_eq_representation (d : ℕ) (x : _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) :
    LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (Fin d → ℂ) x = _root_.RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d x := by
  refine LinearMap.ext fun v => ?_
  rw [LieModule.toEnd_apply_apply]
  rfl


/-- The two displayed expressions are equal. -/
theorem displayed_eq (n : ℕ) :
    _root_.RepresentationTheory.LieModule.CentralAction.centralEndomorphism (Fin (n + 1) → ℂ)
      = (((n : ℂ) * ((n : ℂ) + 2)) / 2) • (1 : Module.End ℂ (Fin (n + 1) → ℂ)) := by
  rw [_root_.RepresentationTheory.LieModule.CentralAction.centralEndomorphism, toEnd_eq_representation, toEnd_eq_representation, toEnd_eq_representation]
  exact _root_.RepresentationTheory.LieAlgebra.Sl2Representations.quadraticGeneratorCombination_succ_eq_smul_id n

section CasimirIntertwine

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
  [AddCommGroup W] [Module ℂ W] [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W]


/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux1 (φ : V →ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ W) (v : V) :
    _root_.RepresentationTheory.LieModule.CentralAction.centralEndomorphism W (φ v) = φ (_root_.RepresentationTheory.LieModule.CentralAction.centralEndomorphism V v) := by
  simp only [_root_.RepresentationTheory.LieModule.CentralAction.centralEndomorphism_apply, map_add, map_smul, LieModuleHom.map_lie]

end CasimirIntertwine

variable (lam mu : ℕ)


/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement (k : ℕ) : ℂ :=
  ((lam : ℂ) + mu - 2 * k) * ((lam : ℂ) + mu - 2 * k + 2) / 2


/-- The submodule specified by the displayed construction. -/
noncomputable def submodule (k : Fin (min lam mu + 1)) :
    LieSubmodule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) :=
  LieSubmodule.map (lieModuleHom_aux1 lam mu (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)) ⊤


/-- The first displayed submodule is contained in the second. -/
theorem submodule_le (k : Fin (min lam mu + 1)) :
    submodule lam mu k ≤ _root_.RepresentationTheory.LieModule.CentralAction.centralGeneralizedEigenspace (distinguishedElement lam mu (k : ℕ)) := by
  have hk : (k : ℕ) ≤ min lam mu := Nat.lt_succ_iff.mp k.isLt
  have hk2 : 2 * (k : ℕ) ≤ lam + mu := by omega
  have hcast : ((lam : ℂ) + mu - 2 * (k : ℕ)) = ((lam + mu - 2 * (k : ℕ) : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hk2]; ring
  intro w hw
  simp only [submodule, LieSubmodule.mem_map] at hw
  obtain ⟨v, -, rfl⟩ := hw

  have heig : _root_.RepresentationTheory.LieModule.CentralAction.centralEndomorphism _ (lieModuleHom_aux1 lam mu (k : ℕ) hk v)
      = distinguishedElement lam mu (k : ℕ) • lieModuleHom_aux1 lam mu (k : ℕ) hk v := by
    rw [map_apply_aux1, displayed_eq, LinearMap.smul_apply, Module.End.one_apply,
      map_smul]
    rw [distinguishedElement, hcast]
  rw [← LieSubmodule.mem_toSubmodule, _root_.RepresentationTheory.LieModule.CentralAction.centralGeneralizedEigenspace_toSubmodule_eq_maxGenEigenspace]
  exact Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr heig)


/-- The displayed family of weight submodules is independent under supremum. -/
theorem weightSubmodules_iSupIndep : iSupIndep (submodule lam mu) := by
  have hginj : Function.Injective
      (fun k : Fin (min lam mu + 1) => distinguishedElement lam mu (k : ℕ)) := by
    intro k k' h
    have hk : (k : ℕ) ≤ min lam mu := Nat.lt_succ_iff.mp k.isLt
    have hk' : (k' : ℕ) ≤ min lam mu := Nat.lt_succ_iff.mp k'.isLt
    apply Fin.ext
    have hprod : ((lam : ℂ) + mu - 2 * (k : ℕ)) * ((lam : ℂ) + mu - 2 * (k : ℕ) + 2)
        = ((lam : ℂ) + mu - 2 * (k' : ℕ)) * ((lam : ℂ) + mu - 2 * (k' : ℕ) + 2) := by
      simp only [distinguishedElement] at h
      linear_combination 2 * h
    exact displayed_eq_aux1 lam mu hk hk' hprod
  exact ((_root_.RepresentationTheory.LieModule.CentralAction.centralGeneralizedEigenspace_iSupIndep).comp hginj).mono
    (submodule_le lam mu)


/-- The displayed Lie submodule has the stated finite rank. -/
theorem finrank_weightSubmodule (k : Fin (min lam mu + 1)) :
    Module.finrank ℂ (submodule lam mu k) = lam + mu - 2 * (k : ℕ) + 1 := by
  haveI : NeZero (lam + mu - 2 * (k : ℕ) + 1) := ⟨Nat.succ_ne_zero _⟩
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_map_top lam mu (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)
  have he := e.toLinearEquiv.finrank_eq
  rw [_root_.RepresentationTheory.LieAlgebra.Sl2Representations.finrank_finFunction] at he
  exact he.symm


/-- The finite rank of the displayed module has the stated value. -/
theorem finrank_eq :
    Module.finrank ℂ ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) = (lam + 1) * (mu + 1) := by
  haveI : NeZero (lam + 1) := ⟨Nat.succ_ne_zero _⟩
  haveI : NeZero (mu + 1) := ⟨Nat.succ_ne_zero _⟩
  rw [Module.finrank_tensorProduct, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.finrank_finFunction, _root_.RepresentationTheory.LieAlgebra.Sl2Representations.finrank_finFunction]


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux4 :
    (∑ k : Fin (min lam mu + 1), (lam + mu - 2 * (k : ℕ) + 1)) = (lam + 1) * (mu + 1) := by
  have h := _root_.RepresentationTheory.Polynomial.Recurrences.succ_mul_succ_eq_indexSum lam mu
  have hcast : ((∑ k : Fin (min lam mu + 1), (lam + mu - 2 * (k : ℕ) + 1) : ℕ) : ℤ)
      = (((lam + 1) * (mu + 1) : ℕ) : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => lam + mu - 2 * k + 1) (min lam mu + 1)]
    push_cast
    linear_combination -h
  exact_mod_cast hcast


/-- The displayed submodules are equal. -/
theorem submodule_eq :
    (⨆ k, (submodule lam mu k : Submodule ℂ ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)))) = ⊤ := by
  set P : Fin (min lam mu + 1) →
      Submodule ℂ ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) :=
    fun k => (submodule lam mu k : Submodule ℂ _) with hP
  have hindep : iSupIndep P :=
    (LieSubmodule.iSupIndep_toSubmodule).mpr (weightSubmodules_iSupIndep lam mu)
  have hinj : Function.Injective (DirectSum.coeLinearMap P) :=
    hindep.dfinsupp_lsum_injective

  have hequiv : (⨁ k, P k) ≃ₗ[ℂ] ↥(⨆ k, P k) :=
    (LinearEquiv.ofInjective (DirectSum.coeLinearMap P) hinj).trans
      (LinearEquiv.ofEq _ _ (DirectSum.range_coeLinearMap (A := P)))
  have hfr : Module.finrank ℂ ↥(⨆ k, P k) = (lam + 1) * (mu + 1) := by
    rw [← hequiv.finrank_eq, Module.finrank_directSum]
    rw [← displayed_eq_aux4 lam mu]
    exact Finset.sum_congr rfl (fun k _ => finrank_weightSubmodule lam mu k)
  apply Submodule.eq_top_of_finrank_eq
  rw [hfr, finrank_eq]


/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux3 : (⨆ k, submodule lam mu k) = ⊤ := by
  rw [← LieSubmodule.iSup_toSubmodule_eq_top]
  exact submodule_eq lam mu


/-- The displayed family of weight submodules forms an internal direct sum. -/
theorem weightSubmodules_isInternal :
    DirectSum.IsInternal
      (fun k => (submodule lam mu k :
        Submodule ℂ ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)))) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    ((LieSubmodule.iSupIndep_toSubmodule).mpr (weightSubmodules_iSupIndep lam mu))
    (submodule_eq lam mu)




/-- A linear map between the displayed modules. -/
noncomputable def linearMap :
    (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) →ₗ[ℂ]
      ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) :=
  DirectSum.toModule ℂ _ _
    (fun k => (lieModuleHom_aux1 lam mu (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)).toLinearMap)


/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux2 (k : Fin (min lam mu + 1))
    (w : Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ) :
    linearMap lam mu (DirectSum.lof ℂ _ _ k w)
      = lieModuleHom_aux1 lam mu (k : ℕ) (Nat.lt_succ_iff.mp k.isLt) w := by
  rw [linearMap, DirectSum.toModule_lof]
  rfl


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux6 (x : _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra) (k : Fin (min lam mu + 1))
    (w : Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ) :
    ⁅x, DirectSum.lof ℂ (Fin (min lam mu + 1))
        (fun k => Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ) k w⁆
      = DirectSum.lof ℂ _ _ k ⁅x, w⁆ := by
  apply DirectSum.ext
  intro j
  rw [DirectSum.lie_module_bracket_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.lof_eq_of, DirectSum.of_eq_same]
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hjk, DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne _ _ _ hjk, lie_zero]


/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux1 (x : _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra)
    (v : ⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) :
    linearMap lam mu ⁅x, v⁆ = ⁅x, linearMap lam mu v⁆ := by
  have key : (linearMap lam mu).comp (LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra _ x)
           = (LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra _ x).comp (linearMap lam mu) := by
    refine DirectSum.linearMap_ext ℂ fun k => ?_
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply]
    rw [bracket_eq_aux6, map_apply_aux2, map_apply_aux2]
    exact LieModuleHom.map_lie _ x w
  have := LinearMap.congr_fun key v
  simpa only [LinearMap.comp_apply, LieModule.toEnd_apply_apply] using this


/-- A homomorphism between the displayed Lie modules. -/
noncomputable def lieModuleHom :
    (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) →ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆
      ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) :=
  lieModuleHom_aux2 (linearMap lam mu)
    (bracket_eq_aux1 lam mu _root_.RepresentationTheory.LieAlgebra.Sl2Representations.weightElement) (bracket_eq_aux1 lam mu _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement) (bracket_eq_aux1 lam mu _root_.RepresentationTheory.LieAlgebra.Sl2Representations.loweringElement)


/-- The displayed map is surjective. -/
theorem map_surjective : Function.Surjective (linearMap lam mu) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← submodule_eq lam mu]
  refine iSup_le fun k => ?_
  rw [SetLike.le_def]
  intro y hy
  simp only [LieSubmodule.mem_toSubmodule, submodule, LieSubmodule.mem_map] at hy
  obtain ⟨w, -, rfl⟩ := hy
  exact ⟨DirectSum.lof ℂ _ _ k w, map_apply_aux2 lam mu k w⟩


/-- The displayed map is bijective. -/
theorem map_bijective : Function.Bijective (linearMap lam mu) := by
  haveI : FiniteDimensional ℂ
      (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) :=
    Module.Finite.equiv
      (DirectSum.linearEquivFunOnFintype ℂ (Fin (min lam mu + 1))
        (fun k => Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)).symm
  have hcard : Module.finrank ℂ
        (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ))
      = Module.finrank ℂ ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) := by
    rw [Module.finrank_directSum, finrank_eq, ← displayed_eq_aux4 lam mu]
    refine Finset.sum_congr rfl fun k _ => ?_
    haveI : NeZero (lam + mu - 2 * (k : ℕ) + 1) := ⟨Nat.succ_ne_zero _⟩
    exact _root_.RepresentationTheory.LieAlgebra.Sl2Representations.finrank_finFunction _
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hcard).mpr
    (map_surjective lam mu), map_surjective lam mu⟩


/-- An equivalence between the displayed Lie modules. -/
noncomputable def lieModuleEquiv :
    (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆
      ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) :=
  { LinearEquiv.ofBijective (lieModuleHom lam mu).toLinearMap (map_bijective lam mu) with
    map_lie' := fun {x m} => (lieModuleHom lam mu).map_lie x m }


/-- There exists a Lie-module equivalence between the tensor product and the displayed direct sum. -/
@[source_ref "Chapter2/Problem2.15.1" (role := primary)]
theorem nonempty_lieModuleEquiv_directSum :
    Nonempty (((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆
      (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ))) :=
  ⟨(lieModuleEquiv lam mu).symm⟩

end RepresentationTheory.LieAlgebra.TensorProductDecomposition
