/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Sl2
import RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices

/-! # Representations of a complex two-by-two matrix Lie algebra -/

open scoped Matrix
open RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RepresentationTheory.LieAlgebra.Sl2Representations

/-- The raising element of the displayed special-linear Lie algebra. -/
@[nolint defsWithUnderscore]
noncomputable def raisingElement : complexTwoByTwoMatrixLieSubalgebra :=
  LieAlgebra.SpecialLinear.single 0 1 (by omega) 1

/-- The lowering element of the displayed special-linear Lie algebra. -/
@[nolint defsWithUnderscore]
noncomputable def loweringElement : complexTwoByTwoMatrixLieSubalgebra :=
  LieAlgebra.SpecialLinear.single 1 0 (by omega) 1

/-- The weight element of the displayed special-linear Lie algebra. -/
@[nolint defsWithUnderscore]
noncomputable def weightElement : complexTwoByTwoMatrixLieSubalgebra :=
  LieAlgebra.SpecialLinear.singleSubSingle 0 1 1

private theorem matrixSubtype_ext {A B : complexTwoByTwoMatrixLieSubalgebra} (h : A.val = B.val) : A = B :=
  Subtype.ext h

/-- The bracket of the raising and lowering elements is the weight element. -/
theorem bracket_raising_lowering : ⁅raisingElement, loweringElement⁆ = weightElement := by
  apply matrixSubtype_ext
  simp only [LieAlgebra.SpecialLinear.sl_bracket, raisingElement, loweringElement, weightElement,
    LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.sub_apply, Matrix.mul_apply,
    Matrix.single, Fin.sum_univ_two]

/-- The bracket of the weight element with the raising element is twice the raising element. -/
theorem bracket_weight_raising : ⁅weightElement, raisingElement⁆ = 2 • raisingElement := by
  apply matrixSubtype_ext
  simp only [LieAlgebra.SpecialLinear.sl_bracket, raisingElement, weightElement,
    LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.sub_apply, Matrix.mul_apply,
    Matrix.single, Matrix.smul_apply, Fin.sum_univ_two]

/-- The bracket of the weight element with the lowering element is negative twice the lowering element. -/
theorem bracket_weight_lowering : ⁅weightElement, loweringElement⁆ = -(2 • loweringElement) := by
  apply matrixSubtype_ext
  simp only [LieAlgebra.SpecialLinear.sl_bracket, loweringElement, weightElement,
    LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.sub_apply, Matrix.mul_apply,
    Matrix.single, Matrix.smul_apply, Matrix.neg_apply, Fin.sum_univ_two]

/-- The weight element is nonzero. -/
theorem weightElement_ne_zero : weightElement ≠ 0 := by
  intro h
  have : (weightElement : complexTwoByTwoMatrixLieSubalgebra).val 0 0 = (0 : complexTwoByTwoMatrixLieSubalgebra).val 0 0 := by rw [h]
  simp [weightElement, LieAlgebra.SpecialLinear.val_singleSubSingle, Matrix.sub_apply,
    Matrix.single] at this

/-- The weight, raising, and lowering elements form an `sl₂` triple. -/
theorem isSl2Triple_weight_raising_lowering : IsSl2Triple weightElement raisingElement loweringElement where
  h_ne_zero := weightElement_ne_zero
  lie_e_f := bracket_raising_lowering
  lie_h_e_nsmul := bracket_weight_raising
  lie_h_f_nsmul := bracket_weight_lowering

/-- For every element of the displayed special-linear Lie algebra, the `(1, 1)` entry is the negation of the `(0, 0)` entry. -/
theorem entry_one_one_eq_neg_entry_zero_zero (X : complexTwoByTwoMatrixLieSubalgebra) : X.val 1 1 = -X.val 0 0 := by
  have h2 : X.val 0 0 + X.val 1 1 = 0 := by
    have h3 : Matrix.trace X.val = 0 := X.property
    have h4 : Matrix.trace X.val = X.val 0 0 + X.val 1 1 := by
      change ∑ i : Fin 2, X.val i i = _
      rw [Fin.sum_univ_two]
    rw [h4] at h3; exact h3
  have : X.val 1 1 = 0 - X.val 0 0 := by rw [← h2]; ring
  simpa only [zero_sub] using this

private theorem val_add (X Y : complexTwoByTwoMatrixLieSubalgebra) (i j : Fin 2) :
    (X + Y).val i j = X.val i j + Y.val i j := rfl

private theorem val_smul (r : ℂ) (X : complexTwoByTwoMatrixLieSubalgebra) (i j : Fin 2) :
    (r • X).val i j = r * X.val i j := rfl

/-- Every element of the displayed special-linear Lie algebra is the stated linear combination of the weight, raising, and lowering elements using its matrix entries. -/
theorem eq_linearCombination_weight_raising_lowering (X : complexTwoByTwoMatrixLieSubalgebra) :
    X = X.val 0 0 • weightElement + X.val 0 1 • raisingElement + X.val 1 0 • loweringElement := by
  apply Subtype.ext
  push_cast
  simp only [weightElement, raisingElement, loweringElement,
    LieAlgebra.SpecialLinear.val_singleSubSingle, LieAlgebra.SpecialLinear.val_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.single, entry_one_one_eq_neg_entry_zero_zero X]

/-- The Lie homomorphism to endomorphisms determined by three endomorphisms satisfying the displayed `sl₂` bracket relations. -/
noncomputable def lieHomOfSl2Triple {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E F H : Module.End ℂ V)
    (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hHF : ⁅H, F⁆ = -((2 : ℂ) • F)) :
    complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V where
  toFun X := X.val 0 0 • H + X.val 0 1 • E + X.val 1 0 • F
  map_add' X Y := by
    simp only [val_add, add_smul]
    abel
  map_smul' r X := by
    simp only [val_smul, mul_smul, RingHom.id_apply, smul_add]
  map_lie' {X Y} := by
    have htX : X.val 1 1 = -X.val 0 0 := entry_one_one_eq_neg_entry_zero_zero X
    have htY : Y.val 1 1 = -Y.val 0 0 := entry_one_one_eq_neg_entry_zero_zero Y
    have hEH : ⁅E, H⁆ = -((2 : ℂ) • E) := by rw [← lie_skew, hHE]
    have hFH : ⁅F, H⁆ = (2 : ℂ) • F := by rw [← lie_skew, hHF, neg_neg]
    have hFE : ⁅F, E⁆ = -H := by rw [← lie_skew, hEF]
    have hbr00 : ⁅X, Y⁆.val 0 0 =
        X.val 0 1 * Y.val 1 0 - Y.val 0 1 * X.val 1 0 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have hbr01 : ⁅X, Y⁆.val 0 1 =
        2 * X.val 0 0 * Y.val 0 1 - 2 * Y.val 0 0 * X.val 0 1 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, htX, htY]
      ring
    have hbr10 : ⁅X, Y⁆.val 1 0 =
        2 * X.val 1 0 * Y.val 0 0 - 2 * Y.val 1 0 * X.val 0 0 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, htX, htY]
      ring
    have smul_lie' : ∀ (c : ℂ) (a b : Module.End ℂ V), ⁅c • a, b⁆ = c • ⁅a, b⁆ :=
      fun c a b => smul_lie c a b
    have lie_smul' : ∀ (c : ℂ) (a b : Module.End ℂ V), ⁅a, c • b⁆ = c • ⁅a, b⁆ :=
      fun c a b => lie_smul c a b
    simp only [add_lie, lie_add, smul_lie', lie_smul', lie_self, smul_zero,
      add_zero, zero_add, hHE, hHF, hEF, hEH, hFH, hFE, smul_neg, smul_smul,
      hbr00, hbr01, hbr10]
    module

/-- The Lie homomorphism associated with an `sl₂` triple sends the raising element to the specified endomorphism `E`. -/
@[simp]
theorem lieHomOfSl2Triple_apply_raising {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E F H : Module.End ℂ V) (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hHF : ⁅H, F⁆ = -((2 : ℂ) • F)) :
    lieHomOfSl2Triple E F H hEF hHE hHF raisingElement = E := by
  simp [lieHomOfSl2Triple, raisingElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]

/-- The Lie homomorphism associated with an `sl₂` triple sends the lowering element to the specified endomorphism `F`. -/
@[simp]
theorem lieHomOfSl2Triple_apply_lowering {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E F H : Module.End ℂ V) (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hHF : ⁅H, F⁆ = -((2 : ℂ) • F)) :
    lieHomOfSl2Triple E F H hEF hHE hHF loweringElement = F := by
  simp [lieHomOfSl2Triple, loweringElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]

/-- The Lie homomorphism associated with an `sl₂` triple sends the weight element to the specified endomorphism `H`. -/
@[simp]
theorem lieHomOfSl2Triple_apply_weight {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E F H : Module.End ℂ V) (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hHF : ⁅H, F⁆ = -((2 : ℂ) • F)) :
    lieHomOfSl2Triple E F H hEF hHE hHF weightElement = H := by
  simp [lieHomOfSl2Triple, weightElement,
    LieAlgebra.SpecialLinear.val_singleSubSingle, Matrix.single]

private noncomputable def weightEnd (d : ℕ) : Module.End ℂ (Fin d → ℂ) where
  toFun v k := ((d : ℂ) - 1 - 2 * ↑(k : ℕ)) * v k
  map_add' u w := by ext k; simp [mul_add]
  map_smul' r w := by ext k; simp [mul_comm r, mul_assoc, smul_eq_mul]

private noncomputable def raisingEnd (d : ℕ) : Module.End ℂ (Fin d → ℂ) where
  toFun v k := (↑(k : ℕ) + 1) * if h : (k : ℕ) + 1 < d then v ⟨k + 1, h⟩ else 0
  map_add' u w := by ext k; simp only [Pi.add_apply]; split <;> ring
  map_smul' r w := by
    ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring

private noncomputable def loweringEnd (d : ℕ) : Module.End ℂ (Fin d → ℂ) where
  toFun v k := ((d : ℂ) - ↑(k : ℕ)) *
    if h : 0 < (k : ℕ) then v ⟨k - 1, by omega⟩ else 0
  map_add' u w := by ext k; simp only [Pi.add_apply]; split <;> ring
  map_smul' r w := by
    ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring

private theorem bracket_weightEnd_raisingEnd (d : ℕ) :
    ⁅weightEnd d, raisingEnd d⁆ = (2 : ℂ) • raisingEnd d := by
  apply LinearMap.ext; intro v; funext k
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, weightEnd, raisingEnd, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases he : (k : ℕ) + 1 < d
  · simp only [he, dite_true]
    push_cast; ring
  · simp only [he, dite_false, mul_zero, sub_zero]

private theorem bracket_weightEnd_loweringEnd (d : ℕ) :
    ⁅weightEnd d, loweringEnd d⁆ = -((2 : ℂ) • loweringEnd d) := by
  apply LinearMap.ext; intro v; funext k
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul, weightEnd, loweringEnd, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hf : 0 < (k : ℕ)
  · simp only [hf, dite_true]
    have hle : 1 ≤ (k : ℕ) := by omega
    simp only [Nat.cast_sub hle]
    ring
  · simp only [hf, dite_false, mul_zero, sub_zero, neg_zero]

private theorem bracket_raisingEnd_loweringEnd (d : ℕ) :
    ⁅raisingEnd d, loweringEnd d⁆ = weightEnd d := by
  apply LinearMap.ext; intro v; funext k
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, Pi.sub_apply,
    weightEnd, raisingEnd, loweringEnd, LinearMap.coe_mk, AddHom.coe_mk]
  have hfin_k : ∀ (h : (k : ℕ) < d), (⟨(k : ℕ), h⟩ : Fin d) = k :=
    fun _ => by ext; rfl
  by_cases he : (k : ℕ) + 1 < d <;> by_cases hf : 0 < (k : ℕ)
  · 
    simp only [he, hf, k.isLt, dite_true,
      show 0 < (k : ℕ) + 1 from by omega,
      show (k : ℕ) + 1 - 1 = (k : ℕ) from by omega,
      show (k : ℕ) - 1 + 1 = (k : ℕ) from by omega,
      dite_true, hfin_k k.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k : ℕ) from by omega)]
    push_cast; ring
  · 
    have hk0 : (k : ℕ) = 0 := by omega
    simp only [he, hf, dite_true, dite_false, mul_zero, sub_zero,
      show 0 < (k : ℕ) + 1 from by omega,
      show (k : ℕ) + 1 - 1 = (k : ℕ) from by omega,
      dite_true, hfin_k k.isLt]
    simp [hk0]
  · 
    simp only [he, hf, k.isLt, dite_true, dite_false, mul_zero, zero_sub,
      show (k : ℕ) - 1 + 1 = (k : ℕ) from by omega,
      dite_true, hfin_k k.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k : ℕ) from by omega)]
    have hkd1 : (k : ℕ) + 1 = d := by omega
    push_cast [Nat.cast_sub (show 1 ≤ d from by omega), ← hkd1]; ring
  · 
    have hk0 : (k : ℕ) = 0 := by omega
    have hd1 : d = 1 := by omega
    simp only [he, hf, dite_false, mul_zero, zero_sub, neg_zero]
    subst hd1
    simp

/-- The Lie algebra representation on complex-valued functions on `Fin d`. -/
noncomputable def finFunctionRepresentation (d : ℕ) :
    complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ (Fin d → ℂ) where
  toFun X := X.val 0 0 • weightEnd d + X.val 0 1 • raisingEnd d + X.val 1 0 • loweringEnd d
  map_add' X Y := by
    simp only [val_add, add_smul]; abel
  map_smul' r X := by
    simp only [val_smul, mul_smul, RingHom.id_apply, smul_add]
  map_lie' {X Y} := by
    have htX : X.val 1 1 = -X.val 0 0 := entry_one_one_eq_neg_entry_zero_zero X
    have htY : Y.val 1 1 = -Y.val 0 0 := entry_one_one_eq_neg_entry_zero_zero Y
    have hEH : ⁅raisingEnd d, weightEnd d⁆ = -((2 : ℂ) • raisingEnd d) := by
      rw [← lie_skew, bracket_weightEnd_raisingEnd]
    have hFH : ⁅loweringEnd d, weightEnd d⁆ = (2 : ℂ) • loweringEnd d := by
      rw [← lie_skew, bracket_weightEnd_loweringEnd, neg_neg]
    have hFE : ⁅loweringEnd d, raisingEnd d⁆ = -(weightEnd d) := by
      rw [← lie_skew, bracket_raisingEnd_loweringEnd]
    have hbr00 : ⁅X, Y⁆.val 0 0 =
        X.val 0 1 * Y.val 1 0 - Y.val 0 1 * X.val 1 0 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]; ring
    have hbr01 : ⁅X, Y⁆.val 0 1 =
        2 * X.val 0 0 * Y.val 0 1 - 2 * Y.val 0 0 * X.val 0 1 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, htX, htY]; ring
    have hbr10 : ⁅X, Y⁆.val 1 0 =
        2 * X.val 1 0 * Y.val 0 0 - 2 * Y.val 1 0 * X.val 0 0 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, htX, htY]; ring

    

    have smul_lie' : ∀ (c : ℂ) (a b : Module.End ℂ (Fin d → ℂ)),
        ⁅c • a, b⁆ = c • ⁅a, b⁆ := fun c a b => smul_lie c a b
    have lie_smul' : ∀ (c : ℂ) (a b : Module.End ℂ (Fin d → ℂ)),
        ⁅a, c • b⁆ = c • ⁅a, b⁆ := fun c a b => lie_smul c a b
    simp only [add_lie, lie_add, smul_lie', lie_smul', lie_self, smul_zero,
      add_zero, zero_add, bracket_weightEnd_raisingEnd, bracket_weightEnd_loweringEnd, bracket_raisingEnd_loweringEnd,
      hEH, hFH, hFE, smul_neg, smul_smul, hbr00, hbr01, hbr10]
    module

/-- The Lie-ring module structure on complex-valued functions on `Fin d` for the displayed special-linear Lie algebra. -/
noncomputable instance lieRingModule_finFunction (d : ℕ) :
    LieRingModule complexTwoByTwoMatrixLieSubalgebra (Fin d → ℂ) :=
  LieRingModule.compLieHom (Fin d → ℂ) (finFunctionRepresentation d)

/-- The complex-valued functions on `Fin d` form a Lie module over the displayed special-linear Lie algebra. -/
noncomputable instance lieModule_finFunction (d : ℕ) :
    @LieModule ℂ complexTwoByTwoMatrixLieSubalgebra (Fin d → ℂ) _ _ _ _ _ (lieRingModule_finFunction d) :=
  LieModule.compLieHom (Fin d → ℂ) (finFunctionRepresentation d)

/-- For nonzero `d`, the complex vector space of functions on `Fin d` has finrank `d`. -/
theorem finrank_finFunction (d : ℕ) [NeZero d] :
    Module.finrank ℂ (Fin d → ℂ) = d := by
  simp

private lemma finFunctionRepresentation_apply_weight (d : ℕ) : finFunctionRepresentation d weightElement = weightEnd d := by
  have h00 : weightElement.val 0 0 = 1 := by
    simp [weightElement, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have h01 : weightElement.val 0 1 = 0 := by
    simp [weightElement, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have h10 : weightElement.val 1 0 = 0 := by
    simp [weightElement, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have key : finFunctionRepresentation d weightElement =
    weightElement.val 0 0 • weightEnd d + weightElement.val 0 1 • raisingEnd d +
      weightElement.val 1 0 • loweringEnd d := rfl
  rw [key, h00, h01, h10]; simp

private lemma finFunctionRepresentation_apply_raising (d : ℕ) : finFunctionRepresentation d raisingElement = raisingEnd d := by
  have h00 : raisingElement.val 0 0 = 0 := by
    simp [raisingElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h01 : raisingElement.val 0 1 = 1 := by
    simp [raisingElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h10 : raisingElement.val 1 0 = 0 := by
    simp [raisingElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have key : finFunctionRepresentation d raisingElement =
    raisingElement.val 0 0 • weightEnd d + raisingElement.val 0 1 • raisingEnd d +
      raisingElement.val 1 0 • loweringEnd d := rfl
  rw [key, h00, h01, h10]; simp

private lemma finFunctionRepresentation_apply_lowering (d : ℕ) : finFunctionRepresentation d loweringElement = loweringEnd d := by
  have h00 : loweringElement.val 0 0 = 0 := by
    simp [loweringElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h01 : loweringElement.val 0 1 = 0 := by
    simp [loweringElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h10 : loweringElement.val 1 0 = 1 := by
    simp [loweringElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have key : finFunctionRepresentation d loweringElement =
    loweringElement.val 0 0 • weightEnd d + loweringElement.val 0 1 • raisingEnd d +
      loweringElement.val 1 0 • loweringEnd d := rfl
  rw [key, h00, h01, h10]; simp

/-- The displayed coordinate vector in the space of complex-valued functions on `Fin d`. -/
@[nolint defsWithUnderscore]
def coordinateVector (d : ℕ) (k : Fin d) : Fin d → ℂ := Pi.single k 1

/-- The coordinate vector indexed by `k` is one at `k` and zero at every other index. -/
theorem coordinateVector_apply (d : ℕ) (k j : Fin d) :
    coordinateVector d k j = if j = k then 1 else 0 := by
  simp [coordinateVector, Pi.single_apply]

/-- The Lie action of an element on a coordinate vector is evaluation of the corresponding endomorphism in the displayed representation. -/
theorem bracket_eq_representation_apply (d : ℕ) (x : complexTwoByTwoMatrixLieSubalgebra) (v : Fin d → ℂ) :
    ⁅x, v⁆ = finFunctionRepresentation d x v := rfl

/-- The weight element acts on the coordinate vector at `i` by the scalar `d - 1 - 2 * i`. -/
theorem bracket_weight_coordinateVector (d : ℕ) (i : Fin d) :
    ⁅weightElement, coordinateVector d i⁆ = ((d : ℂ) - 1 - 2 * (i : ℕ)) • coordinateVector d i := by
  rw [bracket_eq_representation_apply, finFunctionRepresentation_apply_weight]
  ext k
  simp only [weightEnd, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
    coordinateVector_apply]
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

/-- The raising element sends the coordinate vector at `i` to `i` times the coordinate vector at `i - 1`. -/
theorem bracket_raising_coordinateVector (d : ℕ) (i : ℕ) (hi : i < d) :
    ⁅raisingElement, coordinateVector d ⟨i, hi⟩⁆ = (i : ℂ) • coordinateVector d ⟨i - 1, by omega⟩ := by
  rw [bracket_eq_representation_apply, finFunctionRepresentation_apply_raising]
  ext k
  have hkd : (k : ℕ) < d := k.isLt
  simp only [raisingEnd, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
    coordinateVector_apply, Fin.ext_iff]
  by_cases hk : (k : ℕ) + 1 < d
  · simp only [hk, dite_true]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [if_neg (by omega : ¬ (k : ℕ) + 1 = 0)]; push_cast; ring
    · by_cases hki : (k : ℕ) + 1 = i
      · rw [if_pos hki, if_pos (by omega : (k : ℕ) = i - 1), ← hki]; push_cast; ring
      · rw [if_neg hki, if_neg (by omega : ¬ (k : ℕ) = i - 1)]; ring
  · simp only [hk, dite_false, mul_zero]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0; simp
    · rw [if_neg (by omega : ¬ (k : ℕ) = i - 1)]; ring

/-- When `i + 1 < d`, the lowering element sends the coordinate vector at `i` to `(d - 1 - i)` times the coordinate vector at `i + 1`. -/
theorem bracket_lowering_coordinateVector (d : ℕ) (i : ℕ) (hi : i + 1 < d) :
    ⁅loweringElement, coordinateVector d ⟨i, by omega⟩⁆ = ((d : ℂ) - 1 - (i : ℕ)) • coordinateVector d ⟨i + 1, hi⟩ := by
  rw [bracket_eq_representation_apply, finFunctionRepresentation_apply_lowering]
  ext k
  have hkd : (k : ℕ) < d := k.isLt
  simp only [loweringEnd, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
    coordinateVector_apply, Fin.ext_iff]
  by_cases hk : 0 < (k : ℕ)
  · simp only [hk, dite_true]
    by_cases hki : (k : ℕ) - 1 = i
    · rw [if_pos hki, if_pos (by omega : (k : ℕ) = i + 1)]
      have hkc : ((k : ℕ) : ℂ) = (i : ℂ) + 1 := by
        have : (k : ℕ) = i + 1 := by omega
        rw [this]; push_cast; ring
      rw [hkc]
      ring
    · rw [if_neg hki, if_neg (by omega : ¬ (k : ℕ) = i + 1)]; ring
  · simp only [dif_neg hk, mul_zero]
    rw [if_neg (by omega : ¬ (k : ℕ) = i + 1)]; ring

/-- The lowering element sends the final coordinate vector to zero. -/
theorem bracket_lowering_coordinateVector_eq_zero (d : ℕ) (i : ℕ) (hi : i < d) (htop : i + 1 = d) :
    ⁅loweringElement, coordinateVector d ⟨i, hi⟩⁆ = 0 := by
  rw [bracket_eq_representation_apply, finFunctionRepresentation_apply_lowering]
  ext k
  have hkd : (k : ℕ) < d := k.isLt
  simp only [loweringEnd, LinearMap.coe_mk, AddHom.coe_mk, coordinateVector_apply, Pi.zero_apply,
    Fin.ext_iff]
  by_cases hk : 0 < (k : ℕ)
  · simp only [hk, dite_true]
    rw [if_neg (by omega : ¬ (k : ℕ) - 1 = i)]; ring
  · simp only [hk, dite_false, mul_zero]

/-- For nonzero `d`, the displayed Lie-module structure on complex-valued functions on `Fin d` is irreducible. -/
theorem isIrreducible_finFunction (d : ℕ) [NeZero d] :
    letI := lieRingModule_finFunction d
    letI := lieModule_finFunction d
    LieModule.IsIrreducible ℂ complexTwoByTwoMatrixLieSubalgebra (Fin d → ℂ) := by
  letI := lieRingModule_finFunction d
  letI := lieModule_finFunction d
  apply LieModule.IsIrreducible.mk
  intro N hN
  rw [ne_eq, LieSubmodule.eq_bot_iff] at hN
  push Not at hN
  obtain ⟨w, hw_mem, hw_ne⟩ := hN

  have lie_h_comp : ∀ (v : Fin d → ℂ) (k : Fin d),
      ((finFunctionRepresentation d weightElement) v) k = ((d : ℂ) - 1 - 2 * ↑(k : ℕ)) * v k := by
    intro v k; rw [finFunctionRepresentation_apply_weight]; rfl

  have smul_extract : ∀ (c : ℂ) (v : Fin d → ℂ), c ≠ 0 → c • v ∈ N → v ∈ N := by
    intro c v hc hcv
    have h1 : c⁻¹ • (c • v) ∈ N := N.smul_mem c⁻¹ hcv
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1

  suffices basis_in_N : ∀ k : Fin d, coordinateVector d k ∈ N by
    rw [eq_top_iff]; intro v _
    have decomp : v = Finset.univ.sum (fun k : Fin d => v k • coordinateVector d k) := by
      ext j; simp [Finset.sum_apply, coordinateVector_apply]
    rw [decomp]
    refine Finset.sum_induction _
      (· ∈ (N : Set (Fin d → ℂ))) (fun a b ha hb => ?_) ?_
      (fun k _ => ?_)
    · exact N.add_mem ha hb
    · exact N.zero_mem
    · exact N.smul_mem _ (basis_in_N k)

  have extract : ∃ k : Fin d, coordinateVector d k ∈ N := by
    suffices ∀ (n : ℕ) (w : Fin d → ℂ), w ∈ N → w ≠ 0 →
        (Finset.univ.filter (fun k => w k ≠ 0)).card ≤ n →
        ∃ k : Fin d, coordinateVector d k ∈ N by
      exact this _ w hw_mem hw_ne le_rfl
    intro n
    induction n with
    | zero =>
      intro w _ hw_ne hn
      exfalso; apply hw_ne; ext k
      by_contra hk
      have : k ∈ Finset.univ.filter (fun k => w k ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      exact absurd (Finset.card_pos.mpr ⟨k, this⟩) (by omega)
    | succ n ih =>
      intro w hw_mem hw_ne hn
      by_cases hn1 : (Finset.univ.filter (fun k => w k ≠ 0)).card ≤ 1
      · 
        have hcard := Finset.card_le_one.mp hn1
        have hne : (Finset.univ.filter (fun k => w k ≠ 0)).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]; intro hempty
          apply hw_ne; ext k
          by_contra hk
          have : k ∈ (∅ : Finset (Fin d)) :=
            hempty ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
          simp only [Finset.notMem_empty] at this
        obtain ⟨k, hk_mem⟩ := hne
        have hk : k ∈ Finset.univ ∧ w k ≠ 0 := Finset.mem_filter.mp hk_mem
        refine ⟨k, ?_⟩
        have hw_eq : w = w k • coordinateVector d k := by
          ext j
          simp only [Pi.smul_apply, coordinateVector_apply, smul_eq_mul]
          by_cases hjk : j = k
          · subst hjk; simp
          · have : w j = 0 := by
              by_contra hj
              exact hjk (hcard j
                (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) k hk_mem)
            simp [this, hjk]
        rw [hw_eq] at hw_mem
        exact smul_extract _ _ hk.2 hw_mem
      · 
        push Not at hn1
        obtain ⟨j₁, hj₁_mem, j₂, hj₂_mem, hne⟩ :=
          Finset.one_lt_card.mp hn1
        have hj₁ := (Finset.mem_filter.mp hj₁_mem).2
        have hj₂ := (Finset.mem_filter.mp hj₂_mem).2
        let c : ℂ := (d : ℂ) - 1 - 2 * ↑(j₁ : ℕ)
        have hw'_mem :
            (fun i => ((finFunctionRepresentation d weightElement) w) i - c * w i) ∈ N := by
          change (finFunctionRepresentation d weightElement) w - c • w ∈ (N : Set _)
          exact N.sub_mem (N.lie_mem hw_mem) (N.smul_mem c hw_mem)
        have hw'_val : ∀ i : Fin d,
            ((finFunctionRepresentation d weightElement) w i - c * w i) =
            (2 * (↑(j₁ : ℕ) - ↑(i : ℕ))) * w i := by
          intro i; rw [lie_h_comp]; ring
        have hw'_ne : (fun i => (finFunctionRepresentation d weightElement) w i - c * w i) ≠ 0 := by
          intro h
          have := congr_fun h j₂
          rw [hw'_val] at this
          simp only [Pi.zero_apply, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at this
          rcases this with h1 | h2
          · have : (j₁ : ℕ) = (j₂ : ℕ) := by exact_mod_cast sub_eq_zero.mp h1
            exact hne (Fin.ext this)
          · exact hj₂ h2
        have hw'_fewer :
            (Finset.univ.filter (fun k =>
              (finFunctionRepresentation d weightElement) w k - c * w k ≠ 0)).card ≤ n := by
          have hssub : (Finset.univ.filter (fun k =>
              (finFunctionRepresentation d weightElement) w k - c * w k ≠ 0)) ⊂
            (Finset.univ.filter (fun k => w k ≠ 0)) := by
            constructor
            · intro i hi
              rw [Finset.mem_filter] at hi ⊢
              refine ⟨Finset.mem_univ i, ?_⟩
              rw [hw'_val i] at hi
              exact (mul_ne_zero_iff.mp hi.2).2
            · intro hsub
              have hj₁_in := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ j₁, hj₁⟩)
              rw [Finset.mem_filter] at hj₁_in
              have habs := hj₁_in.2
              rw [hw'_val] at habs
              simp at habs
          linarith [Finset.card_lt_card hssub]
        exact ih _ hw'_mem hw'_ne hw'_fewer
  obtain ⟨k₀, hk₀⟩ := extract

  
  have step_down : ∀ (m : ℕ) (hm : m + 1 < d),
      coordinateVector d ⟨m + 1, by omega⟩ ∈ N →
      coordinateVector d ⟨m, by omega⟩ ∈ N := by
    intro m hm hmem
    have lie_in_N : (finFunctionRepresentation d raisingElement) (coordinateVector d ⟨m + 1, by omega⟩) ∈ N :=
      N.lie_mem hmem
    have lie_eq : (finFunctionRepresentation d raisingElement) (coordinateVector d ⟨m + 1, by omega⟩) =
        (↑(m + 1) : ℂ) • coordinateVector d ⟨m, by omega⟩ := by
      rw [finFunctionRepresentation_apply_raising]
      ext k
      simp only [raisingEnd, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
        smul_eq_mul, coordinateVector, Pi.single_apply]
      by_cases hk : (k : ℕ) + 1 < d
      · simp only [hk, dite_true]
        by_cases hkm : (k : ℕ) = m
        · subst hkm; simp
        · have hne1 : ¬((k : ℕ) + 1 = m + 1) := by omega
          simp [Fin.ext_iff, hkm]
      · simp only [hk, dite_false, mul_zero]
        by_cases hkm : (k : ℕ) = m
        · exfalso; omega
        · simp [Fin.ext_iff, hkm]
    rw [lie_eq] at lie_in_N
    exact smul_extract _ _ (Nat.cast_ne_zero.mpr (by omega)) lie_in_N

  have step_up : ∀ (m : ℕ) (hm : m + 1 < d),
      coordinateVector d ⟨m, by omega⟩ ∈ N →
      coordinateVector d ⟨m + 1, by omega⟩ ∈ N := by
    intro m hm hmem
    have lie_in_N : (finFunctionRepresentation d loweringElement) (coordinateVector d ⟨m, by omega⟩) ∈ N :=
      N.lie_mem hmem
    have lie_eq : (finFunctionRepresentation d loweringElement) (coordinateVector d ⟨m, by omega⟩) =
        ((d : ℂ) - ↑(m + 1)) • coordinateVector d ⟨m + 1, by omega⟩ := by
      rw [finFunctionRepresentation_apply_lowering]
      ext k
      simp only [loweringEnd, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
        smul_eq_mul, coordinateVector, Pi.single_apply]
      by_cases hk : 0 < (k : ℕ)
      · simp only [hk, dite_true]
        by_cases hkm : (k : ℕ) = m + 1
        · have hksub : (k : ℕ) - 1 = m := by omega
          have hkeq : k = ⟨m + 1, by omega⟩ := Fin.ext (by omega)
          simp [hkeq]
        · have : (k : ℕ) - 1 ≠ m := by omega
          simp [Fin.ext_iff, this, hkm]
      · simp only [hk, dite_false, mul_zero]
        push Not at hk
        simp [Fin.ext_iff, show (k : ℕ) ≠ m + 1 from by omega]
    rw [lie_eq] at lie_in_N
    have hc : ((d : ℂ) - ↑(m + 1)) ≠ 0 := by
      rw [Ne, sub_eq_zero]; exact_mod_cast (by omega : d ≠ m + 1)
    exact smul_extract _ _ hc lie_in_N

  have hd_pos : 0 < d := NeZero.pos d
  have e0_mem : coordinateVector d ⟨0, hd_pos⟩ ∈ N := by
    suffices ∀ (m : ℕ) (hm : m < d),
        coordinateVector d ⟨m, hm⟩ ∈ N → coordinateVector d ⟨0, hd_pos⟩ ∈ N from
      this k₀.val k₀.isLt hk₀
    intro m hm
    induction m with
    | zero => exact id
    | succ m ihm => intro hmem; exact ihm (by omega) (step_down m (by omega) hmem)

  intro k
  suffices ∀ (j : ℕ) (hj : j < d), coordinateVector d ⟨j, hj⟩ ∈ N from
    this k.val k.isLt
  intro j hj
  induction j with
  | zero => exact e0_mem
  | succ j ih => exact step_up j hj (ih (by omega))

private theorem quadraticGeneratorCombination_ends (d : ℕ) :
    raisingEnd d * loweringEnd d + loweringEnd d * raisingEnd d + (2⁻¹ : ℂ) • (weightEnd d * weightEnd d)
      = (((d : ℂ) - 1) * ((d : ℂ) + 1) / 2) • (1 : Module.End ℂ (Fin d → ℂ)) := by
  apply LinearMap.ext; intro v; funext k
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Module.End.one_apply,
    weightEnd, raisingEnd, loweringEnd, LinearMap.coe_mk, AddHom.coe_mk]
  have hfin_k : ∀ (h : (k : ℕ) < d), (⟨(k : ℕ), h⟩ : Fin d) = k :=
    fun _ => by ext; rfl
  by_cases he : (k : ℕ) + 1 < d <;> by_cases hf : 0 < (k : ℕ)
  · 
    simp only [he, hf, dite_true,
      show 0 < (k : ℕ) + 1 from by omega,
      show (k : ℕ) + 1 - 1 = (k : ℕ) from by omega,
      show (k : ℕ) - 1 + 1 = (k : ℕ) from by omega,
      show (k : ℕ) < d from k.isLt, hfin_k k.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k : ℕ) from by omega)]
    push_cast; ring
  · 
    have hk0 : (k : ℕ) = 0 := by omega
    simp only [he, hf, dite_true, dite_false, mul_zero, add_zero,
      show 0 < (k : ℕ) + 1 from by omega,
      show (k : ℕ) + 1 - 1 = (k : ℕ) from by omega,
      hfin_k k.isLt]
    simp only [hk0]; push_cast; ring
  · 
    simp only [he, hf, dite_true, dite_false, mul_zero,
      show (k : ℕ) - 1 + 1 = (k : ℕ) from by omega,
      show (k : ℕ) < d from k.isLt, hfin_k k.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k : ℕ) from by omega)]
    have hkd1 : (k : ℕ) + 1 = d := by omega
    push_cast [← hkd1]; ring
  · 
    have hk0 : (k : ℕ) = 0 := by omega
    have hd1 : d = 1 := by omega
    subst hd1
    simp only [hk0, zero_add]
    push_cast; ring

/-- In the `d`-dimensional coordinate representation, the displayed symmetric quadratic combination of the raising, lowering, and weight operators is `((d - 1) * (d + 1) / 2)` times the identity. -/
theorem quadraticGeneratorCombination_eq_smul_id (d : ℕ) :
    finFunctionRepresentation d raisingElement * finFunctionRepresentation d loweringElement
        + finFunctionRepresentation d loweringElement * finFunctionRepresentation d raisingElement
        + (2⁻¹ : ℂ) • (finFunctionRepresentation d weightElement * finFunctionRepresentation d weightElement)
      = (((d : ℂ) - 1) * ((d : ℂ) + 1) / 2) • (1 : Module.End ℂ (Fin d → ℂ)) := by
  rw [finFunctionRepresentation_apply_raising, finFunctionRepresentation_apply_lowering, finFunctionRepresentation_apply_weight, quadraticGeneratorCombination_ends]

/-- In the representation indexed by `lam + 1`, the displayed symmetric quadratic combination is `(lam * (lam + 2) / 2)` times the identity. -/
theorem quadraticGeneratorCombination_succ_eq_smul_id (lam : ℕ) :
    finFunctionRepresentation (lam + 1) raisingElement * finFunctionRepresentation (lam + 1) loweringElement
        + finFunctionRepresentation (lam + 1) loweringElement * finFunctionRepresentation (lam + 1) raisingElement
        + (2⁻¹ : ℂ) • (finFunctionRepresentation (lam + 1) weightElement * finFunctionRepresentation (lam + 1) weightElement)
      = (((lam : ℂ) * ((lam : ℂ) + 2)) / 2) • (1 : Module.End ℂ (Fin (lam + 1) → ℂ)) := by
  rw [quadraticGeneratorCombination_eq_smul_id (lam + 1)]
  push_cast; ring_nf

end RepresentationTheory.LieAlgebra.Sl2Representations
