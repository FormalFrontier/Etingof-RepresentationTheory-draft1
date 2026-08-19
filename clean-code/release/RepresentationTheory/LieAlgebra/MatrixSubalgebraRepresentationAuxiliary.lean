/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Sl2
import RepresentationTheory.Algebra.Lie.ComplexMatrixSubalgebraAuxiliary
import RepresentationTheory.Alignment.Attribute

/-! # Representations of an auxiliary complex matrix Lie subalgebra -/
























































open scoped Matrix
open RepresentationTheory.Algebra.Lie.ComplexMatrixSubalgebraAuxiliary

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RepresentationTheory.LieAlgebra.MatrixSubalgebraRepresentationAuxiliary








/-- The first auxiliary element of the displayed Lie algebra. -/
@[nolint defsWithUnderscore]
noncomputable def auxiliaryElement1 : auxiliaryLieSubalgebra :=
  LieAlgebra.SpecialLinear.single 0 1 (by omega) 1


/-- The second auxiliary element of the displayed Lie algebra. -/
@[nolint defsWithUnderscore]
noncomputable def auxiliaryElement2 : auxiliaryLieSubalgebra :=
  LieAlgebra.SpecialLinear.single 1 0 (by omega) 1


/-- The third auxiliary element of the displayed Lie algebra. -/
@[nolint defsWithUnderscore]
noncomputable def auxiliaryElement3 : auxiliaryLieSubalgebra :=
  LieAlgebra.SpecialLinear.singleSubSingle 0 1 1

private theorem sl2_ext {A B : auxiliaryLieSubalgebra} (h : A.val = B.val) : A = B :=
  Subtype.ext h


/-- The bracket of the first and second auxiliary elements is the third auxiliary element. -/
theorem bracket_auxiliaryElement1_auxiliaryElement2 : ⁅auxiliaryElement1, auxiliaryElement2⁆ = auxiliaryElement3 := by
  apply sl2_ext
  simp only [LieAlgebra.SpecialLinear.sl_bracket, auxiliaryElement1, auxiliaryElement2, auxiliaryElement3,
    LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.sub_apply, Matrix.mul_apply,
    Matrix.single, Fin.sum_univ_two]


/-- The bracket of the third auxiliary element with the first is twice the first. -/
theorem bracket_auxiliaryElement3_auxiliaryElement1 : ⁅auxiliaryElement3, auxiliaryElement1⁆ = 2 • auxiliaryElement1 := by
  apply sl2_ext
  simp only [LieAlgebra.SpecialLinear.sl_bracket, auxiliaryElement1, auxiliaryElement3,
    LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.sub_apply, Matrix.mul_apply,
    Matrix.single, Matrix.smul_apply, Fin.sum_univ_two]


/-- The bracket of the third auxiliary element with the second is negative twice the second. -/
theorem bracket_auxiliaryElement3_auxiliaryElement2 : ⁅auxiliaryElement3, auxiliaryElement2⁆ = -(2 • auxiliaryElement2) := by
  apply sl2_ext
  simp only [LieAlgebra.SpecialLinear.sl_bracket, auxiliaryElement2, auxiliaryElement3,
    LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.sub_apply, Matrix.mul_apply,
    Matrix.single, Matrix.smul_apply, Matrix.neg_apply, Fin.sum_univ_two]


/-- The third auxiliary element is nonzero. -/
theorem auxiliaryElement3_ne_zero : auxiliaryElement3 ≠ 0 := by
  intro h
  have : (auxiliaryElement3 : auxiliaryLieSubalgebra).val 0 0 = (0 : auxiliaryLieSubalgebra).val 0 0 := by rw [h]
  simp [auxiliaryElement3, LieAlgebra.SpecialLinear.val_singleSubSingle, Matrix.sub_apply,
    Matrix.single] at this


/-- The third, first, and second auxiliary elements form an `sl₂` triple. -/
theorem isSl2Triple_auxiliaryElements : IsSl2Triple auxiliaryElement3 auxiliaryElement1 auxiliaryElement2 where
  h_ne_zero := auxiliaryElement3_ne_zero
  lie_e_f := bracket_auxiliaryElement1_auxiliaryElement2
  lie_h_e_nsmul := bracket_auxiliaryElement3_auxiliaryElement1
  lie_h_f_nsmul := bracket_auxiliaryElement3_auxiliaryElement2




/-- For every element of the displayed matrix Lie algebra, the `(1, 1)` entry is the negation of the `(0, 0)` entry. -/
theorem entry_one_one_eq_neg_entry_zero_zero (X : auxiliaryLieSubalgebra) : X.val 1 1 = -X.val 0 0 := by
  have h2 : X.val 0 0 + X.val 1 1 = 0 := by
    have h3 : Matrix.trace X.val = 0 := X.property
    have h4 : Matrix.trace X.val = X.val 0 0 + X.val 1 1 := by
      change ∑ i : Fin 2, X.val i i = _
      rw [Fin.sum_univ_two]
    rw [h4] at h3; exact h3
  have : X.val 1 1 = 0 - X.val 0 0 := by rw [← h2]; ring
  simpa only [zero_sub] using this

private theorem sl2_val_add (X Y : auxiliaryLieSubalgebra) (i j : Fin 2) :
    (X + Y).val i j = X.val i j + Y.val i j := rfl

private theorem sl2_val_smul (r : ℂ) (X : auxiliaryLieSubalgebra) (i j : Fin 2) :
    (r • X).val i j = r * X.val i j := rfl



/-- Every displayed element is the stated linear combination of the three auxiliary elements using its matrix entries. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem eq_linearCombination_auxiliaryElements (X : auxiliaryLieSubalgebra) :
    X = X.val 0 0 • auxiliaryElement3 + X.val 0 1 • auxiliaryElement1 + X.val 1 0 • auxiliaryElement2 := by
  apply Subtype.ext
  push_cast
  simp only [auxiliaryElement3, auxiliaryElement1, auxiliaryElement2,
    LieAlgebra.SpecialLinear.val_singleSubSingle, LieAlgebra.SpecialLinear.val_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.single, entry_one_one_eq_neg_entry_zero_zero X]




/-- An auxiliary Lie homomorphism to endomorphisms from three endomorphisms satisfying the displayed bracket relations. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
noncomputable def auxiliaryLieHomOfBracketRelations {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E F H : Module.End ℂ V)
    (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hHF : ⁅H, F⁆ = -((2 : ℂ) • F)) :
    auxiliaryLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V where
  toFun X := X.val 0 0 • H + X.val 0 1 • E + X.val 1 0 • F
  map_add' X Y := by
    simp only [sl2_val_add, add_smul]
    abel
  map_smul' r X := by
    simp only [sl2_val_smul, mul_smul, RingHom.id_apply, smul_add]
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


/-- The auxiliary Lie homomorphism sends the first displayed element to `E`. -/
@[simp, source_ref "Chapter2/Problem2.15.1" (role := supporting)] theorem auxiliaryLieHomOfBracketRelations_apply_element1 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E F H : Module.End ℂ V) (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hHF : ⁅H, F⁆ = -((2 : ℂ) • F)) :
    auxiliaryLieHomOfBracketRelations E F H hEF hHE hHF auxiliaryElement1 = E := by
  simp [auxiliaryLieHomOfBracketRelations, auxiliaryElement1, LieAlgebra.SpecialLinear.val_single, Matrix.single]


/-- The auxiliary Lie homomorphism sends the second displayed element to `F`. -/
@[simp, source_ref "Chapter2/Problem2.15.1" (role := supporting)] theorem auxiliaryLieHomOfBracketRelations_apply_element2 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E F H : Module.End ℂ V) (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hHF : ⁅H, F⁆ = -((2 : ℂ) • F)) :
    auxiliaryLieHomOfBracketRelations E F H hEF hHE hHF auxiliaryElement2 = F := by
  simp [auxiliaryLieHomOfBracketRelations, auxiliaryElement2, LieAlgebra.SpecialLinear.val_single, Matrix.single]


/-- The auxiliary Lie homomorphism sends the third displayed element to `H`. -/
@[simp, source_ref "Chapter2/Problem2.15.1" (role := supporting)] theorem auxiliaryLieHomOfBracketRelations_apply_element3 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E F H : Module.End ℂ V) (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hHF : ⁅H, F⁆ = -((2 : ℂ) • F)) :
    auxiliaryLieHomOfBracketRelations E F H hEF hHE hHF auxiliaryElement3 = H := by
  simp [auxiliaryLieHomOfBracketRelations, auxiliaryElement3,
    LieAlgebra.SpecialLinear.val_singleSubSingle, Matrix.single]












private noncomputable def rhoH (d : ℕ) : Module.End ℂ (Fin d → ℂ) where
  toFun v k := ((d : ℂ) - 1 - 2 * ↑(k : ℕ)) * v k
  map_add' u w := by ext k; simp [mul_add]
  map_smul' r w := by ext k; simp [mul_comm r, mul_assoc, smul_eq_mul]


private noncomputable def rhoE (d : ℕ) : Module.End ℂ (Fin d → ℂ) where
  toFun v k := (↑(k : ℕ) + 1) * if h : (k : ℕ) + 1 < d then v ⟨k + 1, h⟩ else 0
  map_add' u w := by ext k; simp only [Pi.add_apply]; split <;> ring
  map_smul' r w := by
    ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring


private noncomputable def rhoF (d : ℕ) : Module.End ℂ (Fin d → ℂ) where
  toFun v k := ((d : ℂ) - ↑(k : ℕ)) *
    if h : 0 < (k : ℕ) then v ⟨k - 1, by omega⟩ else 0
  map_add' u w := by ext k; simp only [Pi.add_apply]; split <;> ring
  map_smul' r w := by
    ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring


private theorem lie_rhoH_rhoE (d : ℕ) :
    ⁅rhoH d, rhoE d⁆ = (2 : ℂ) • rhoE d := by
  apply LinearMap.ext; intro v; funext k
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, rhoH, rhoE, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases he : (k : ℕ) + 1 < d
  · simp only [he, dite_true]
    push_cast; ring
  · simp only [he, dite_false, mul_zero, sub_zero]


private theorem lie_rhoH_rhoF (d : ℕ) :
    ⁅rhoH d, rhoF d⁆ = -((2 : ℂ) • rhoF d) := by
  apply LinearMap.ext; intro v; funext k
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul, rhoH, rhoF, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hf : 0 < (k : ℕ)
  · simp only [hf, dite_true]
    have hle : 1 ≤ (k : ℕ) := by omega
    simp only [Nat.cast_sub hle]
    ring
  · simp only [hf, dite_false, mul_zero, sub_zero, neg_zero]


private theorem lie_rhoE_rhoF (d : ℕ) :
    ⁅rhoE d, rhoF d⁆ = rhoH d := by
  apply LinearMap.ext; intro v; funext k
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, Pi.sub_apply,
    rhoH, rhoE, rhoF, LinearMap.coe_mk, AddHom.coe_mk]
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


/-- An auxiliary Lie homomorphism to the endomorphisms of complex-valued functions on `Fin d`. -/
noncomputable def auxiliaryFinFunctionRepresentation (d : ℕ) :
    auxiliaryLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ (Fin d → ℂ) where
  toFun X := X.val 0 0 • rhoH d + X.val 0 1 • rhoE d + X.val 1 0 • rhoF d
  map_add' X Y := by
    simp only [sl2_val_add, add_smul]; abel
  map_smul' r X := by
    simp only [sl2_val_smul, mul_smul, RingHom.id_apply, smul_add]
  map_lie' {X Y} := by
    have htX : X.val 1 1 = -X.val 0 0 := entry_one_one_eq_neg_entry_zero_zero X
    have htY : Y.val 1 1 = -Y.val 0 0 := entry_one_one_eq_neg_entry_zero_zero Y
    have hEH : ⁅rhoE d, rhoH d⁆ = -((2 : ℂ) • rhoE d) := by
      rw [← lie_skew, lie_rhoH_rhoE]
    have hFH : ⁅rhoF d, rhoH d⁆ = (2 : ℂ) • rhoF d := by
      rw [← lie_skew, lie_rhoH_rhoF, neg_neg]
    have hFE : ⁅rhoF d, rhoE d⁆ = -(rhoH d) := by
      rw [← lie_skew, lie_rhoE_rhoF]
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
      add_zero, zero_add, lie_rhoH_rhoE, lie_rhoH_rhoF, lie_rhoE_rhoF,
      hEH, hFH, hFE, smul_neg, smul_smul, hbr00, hbr01, hbr10]
    module


/-- A Lie-ring-module structure on the complex-valued functions on `Fin d` for the displayed Lie algebra. -/
noncomputable instance finFunctionLieRingModule (d : ℕ) :
    LieRingModule auxiliaryLieSubalgebra (Fin d → ℂ) :=
  LieRingModule.compLieHom (Fin d → ℂ) (auxiliaryFinFunctionRepresentation d)


/-- The complex-valued functions on `Fin d` carry the displayed Lie-module structure. -/
noncomputable instance finFunctionLieModule (d : ℕ) :
    @LieModule ℂ auxiliaryLieSubalgebra (Fin d → ℂ) _ _ _ _ _ (finFunctionLieRingModule d) :=
  LieModule.compLieHom (Fin d → ℂ) (auxiliaryFinFunctionRepresentation d)


/-- For nonzero `d`, the complex vector space of functions on `Fin d` has finrank `d`. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem finrank_finFunction (d : ℕ) [NeZero d] :
    Module.finrank ℂ (Fin d → ℂ) = d := by
  simp


private lemma rhoLieHom_sl2_h_eq (d : ℕ) : auxiliaryFinFunctionRepresentation d auxiliaryElement3 = rhoH d := by
  have h00 : auxiliaryElement3.val 0 0 = 1 := by
    simp [auxiliaryElement3, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have h01 : auxiliaryElement3.val 0 1 = 0 := by
    simp [auxiliaryElement3, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have h10 : auxiliaryElement3.val 1 0 = 0 := by
    simp [auxiliaryElement3, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have key : auxiliaryFinFunctionRepresentation d auxiliaryElement3 =
    auxiliaryElement3.val 0 0 • rhoH d + auxiliaryElement3.val 0 1 • rhoE d +
      auxiliaryElement3.val 1 0 • rhoF d := rfl
  rw [key, h00, h01, h10]; simp


private lemma rhoLieHom_sl2_e_eq (d : ℕ) : auxiliaryFinFunctionRepresentation d auxiliaryElement1 = rhoE d := by
  have h00 : auxiliaryElement1.val 0 0 = 0 := by
    simp [auxiliaryElement1, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h01 : auxiliaryElement1.val 0 1 = 1 := by
    simp [auxiliaryElement1, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h10 : auxiliaryElement1.val 1 0 = 0 := by
    simp [auxiliaryElement1, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have key : auxiliaryFinFunctionRepresentation d auxiliaryElement1 =
    auxiliaryElement1.val 0 0 • rhoH d + auxiliaryElement1.val 0 1 • rhoE d +
      auxiliaryElement1.val 1 0 • rhoF d := rfl
  rw [key, h00, h01, h10]; simp


private lemma rhoLieHom_sl2_f_eq (d : ℕ) : auxiliaryFinFunctionRepresentation d auxiliaryElement2 = rhoF d := by
  have h00 : auxiliaryElement2.val 0 0 = 0 := by
    simp [auxiliaryElement2, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h01 : auxiliaryElement2.val 0 1 = 0 := by
    simp [auxiliaryElement2, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h10 : auxiliaryElement2.val 1 0 = 1 := by
    simp [auxiliaryElement2, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have key : auxiliaryFinFunctionRepresentation d auxiliaryElement2 =
    auxiliaryElement2.val 0 0 • rhoH d + auxiliaryElement2.val 0 1 • rhoE d +
      auxiliaryElement2.val 1 0 • rhoF d := rfl
  rw [key, h00, h01, h10]; simp


/-- An auxiliary complex-valued function of two indices in `Fin d`. -/
@[nolint defsWithUnderscore]
def auxiliaryCoordinateFunction (d : ℕ) (k : Fin d) : Fin d → ℂ := Pi.single k 1


/-- The auxiliary function indexed by `k` is one at `k` and zero at every other index. -/
theorem auxiliaryCoordinateFunction_apply (d : ℕ) (k j : Fin d) :
    auxiliaryCoordinateFunction d k j = if j = k then 1 else 0 := by
  simp [auxiliaryCoordinateFunction, Pi.single_apply]








/-- The Lie action on a complex-valued function is evaluation of the corresponding endomorphism in the displayed representation. -/
theorem bracket_eq_auxiliaryRepresentation_apply (d : ℕ) (x : auxiliaryLieSubalgebra) (v : Fin d → ℂ) :
    ⁅x, v⁆ = auxiliaryFinFunctionRepresentation d x v := rfl


/-- The third auxiliary element acts on the function at `i` by the scalar `d - 1 - 2 * i`. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem bracket_auxiliaryElement3_auxiliaryCoordinateFunction (d : ℕ) (i : Fin d) :
    ⁅auxiliaryElement3, auxiliaryCoordinateFunction d i⁆ = ((d : ℂ) - 1 - 2 * (i : ℕ)) • auxiliaryCoordinateFunction d i := by
  rw [bracket_eq_auxiliaryRepresentation_apply, rhoLieHom_sl2_h_eq]
  ext k
  simp only [rhoH, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
    auxiliaryCoordinateFunction_apply]
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]



/-- The first auxiliary element sends the function at `i` to `i` times the function at `i - 1`. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem bracket_auxiliaryElement1_auxiliaryCoordinateFunction (d : ℕ) (i : ℕ) (hi : i < d) :
    ⁅auxiliaryElement1, auxiliaryCoordinateFunction d ⟨i, hi⟩⁆ = (i : ℂ) • auxiliaryCoordinateFunction d ⟨i - 1, by omega⟩ := by
  rw [bracket_eq_auxiliaryRepresentation_apply, rhoLieHom_sl2_e_eq]
  ext k
  have hkd : (k : ℕ) < d := k.isLt
  simp only [rhoE, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
    auxiliaryCoordinateFunction_apply, Fin.ext_iff]
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



/-- When `i + 1 < d`, the second auxiliary element sends the function at `i` to `(d - 1 - i)` times the function at `i + 1`. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem bracket_auxiliaryElement2_auxiliaryCoordinateFunction (d : ℕ) (i : ℕ) (hi : i + 1 < d) :
    ⁅auxiliaryElement2, auxiliaryCoordinateFunction d ⟨i, by omega⟩⁆ = ((d : ℂ) - 1 - (i : ℕ)) • auxiliaryCoordinateFunction d ⟨i + 1, hi⟩ := by
  rw [bracket_eq_auxiliaryRepresentation_apply, rhoLieHom_sl2_f_eq]
  ext k
  have hkd : (k : ℕ) < d := k.isLt
  simp only [rhoF, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
    auxiliaryCoordinateFunction_apply, Fin.ext_iff]
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


/-- The second auxiliary element sends the final indexed function to zero. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem bracket_auxiliaryElement2_auxiliaryCoordinateFunction_eq_zero (d : ℕ) (i : ℕ) (hi : i < d) (htop : i + 1 = d) :
    ⁅auxiliaryElement2, auxiliaryCoordinateFunction d ⟨i, hi⟩⁆ = 0 := by
  rw [bracket_eq_auxiliaryRepresentation_apply, rhoLieHom_sl2_f_eq]
  ext k
  have hkd : (k : ℕ) < d := k.isLt
  simp only [rhoF, LinearMap.coe_mk, AddHom.coe_mk, auxiliaryCoordinateFunction_apply, Pi.zero_apply,
    Fin.ext_iff]
  by_cases hk : 0 < (k : ℕ)
  · simp only [hk, dite_true]
    rw [if_neg (by omega : ¬ (k : ℕ) - 1 = i)]; ring
  · simp only [hk, dite_false, mul_zero]


/-- For nonzero `d`, the displayed Lie-module structure on complex-valued functions on `Fin d` is irreducible. -/
@[source_ref "Chapter2/Theorem2.1.1" (role := supporting),
  source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem finFunction_isIrreducible (d : ℕ) [NeZero d] :
    letI := finFunctionLieRingModule d
    letI := finFunctionLieModule d
    LieModule.IsIrreducible ℂ auxiliaryLieSubalgebra (Fin d → ℂ) := by
  letI := finFunctionLieRingModule d
  letI := finFunctionLieModule d
  apply LieModule.IsIrreducible.mk
  intro N hN
  rw [ne_eq, LieSubmodule.eq_bot_iff] at hN
  push Not at hN
  obtain ⟨w, hw_mem, hw_ne⟩ := hN

  have lie_h_comp : ∀ (v : Fin d → ℂ) (k : Fin d),
      ((auxiliaryFinFunctionRepresentation d auxiliaryElement3) v) k = ((d : ℂ) - 1 - 2 * ↑(k : ℕ)) * v k := by
    intro v k; rw [rhoLieHom_sl2_h_eq]; rfl

  have smul_extract : ∀ (c : ℂ) (v : Fin d → ℂ), c ≠ 0 → c • v ∈ N → v ∈ N := by
    intro c v hc hcv
    have h1 : c⁻¹ • (c • v) ∈ N := N.smul_mem c⁻¹ hcv
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1

  suffices basis_in_N : ∀ k : Fin d, auxiliaryCoordinateFunction d k ∈ N by
    rw [eq_top_iff]; intro v _
    have decomp : v = Finset.univ.sum (fun k : Fin d => v k • auxiliaryCoordinateFunction d k) := by
      ext j; simp [Finset.sum_apply, auxiliaryCoordinateFunction_apply]
    rw [decomp]
    refine Finset.sum_induction _
      (· ∈ (N : Set (Fin d → ℂ))) (fun a b ha hb => ?_) ?_
      (fun k _ => ?_)
    · exact N.add_mem ha hb
    · exact N.zero_mem
    · exact N.smul_mem _ (basis_in_N k)

  have extract : ∃ k : Fin d, auxiliaryCoordinateFunction d k ∈ N := by
    suffices ∀ (n : ℕ) (w : Fin d → ℂ), w ∈ N → w ≠ 0 →
        (Finset.univ.filter (fun k => w k ≠ 0)).card ≤ n →
        ∃ k : Fin d, auxiliaryCoordinateFunction d k ∈ N by
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
        have hw_eq : w = w k • auxiliaryCoordinateFunction d k := by
          ext j
          simp only [Pi.smul_apply, auxiliaryCoordinateFunction_apply, smul_eq_mul]
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
            (fun i => ((auxiliaryFinFunctionRepresentation d auxiliaryElement3) w) i - c * w i) ∈ N := by
          change (auxiliaryFinFunctionRepresentation d auxiliaryElement3) w - c • w ∈ (N : Set _)
          exact N.sub_mem (N.lie_mem hw_mem) (N.smul_mem c hw_mem)
        have hw'_val : ∀ i : Fin d,
            ((auxiliaryFinFunctionRepresentation d auxiliaryElement3) w i - c * w i) =
            (2 * (↑(j₁ : ℕ) - ↑(i : ℕ))) * w i := by
          intro i; rw [lie_h_comp]; ring
        have hw'_ne : (fun i => (auxiliaryFinFunctionRepresentation d auxiliaryElement3) w i - c * w i) ≠ 0 := by
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
              (auxiliaryFinFunctionRepresentation d auxiliaryElement3) w k - c * w k ≠ 0)).card ≤ n := by
          have hssub : (Finset.univ.filter (fun k =>
              (auxiliaryFinFunctionRepresentation d auxiliaryElement3) w k - c * w k ≠ 0)) ⊂
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
      auxiliaryCoordinateFunction d ⟨m + 1, by omega⟩ ∈ N →
      auxiliaryCoordinateFunction d ⟨m, by omega⟩ ∈ N := by
    intro m hm hmem
    have lie_in_N : (auxiliaryFinFunctionRepresentation d auxiliaryElement1) (auxiliaryCoordinateFunction d ⟨m + 1, by omega⟩) ∈ N :=
      N.lie_mem hmem
    have lie_eq : (auxiliaryFinFunctionRepresentation d auxiliaryElement1) (auxiliaryCoordinateFunction d ⟨m + 1, by omega⟩) =
        (↑(m + 1) : ℂ) • auxiliaryCoordinateFunction d ⟨m, by omega⟩ := by
      rw [rhoLieHom_sl2_e_eq]
      ext k
      simp only [rhoE, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
        smul_eq_mul, auxiliaryCoordinateFunction, Pi.single_apply]
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
      auxiliaryCoordinateFunction d ⟨m, by omega⟩ ∈ N →
      auxiliaryCoordinateFunction d ⟨m + 1, by omega⟩ ∈ N := by
    intro m hm hmem
    have lie_in_N : (auxiliaryFinFunctionRepresentation d auxiliaryElement2) (auxiliaryCoordinateFunction d ⟨m, by omega⟩) ∈ N :=
      N.lie_mem hmem
    have lie_eq : (auxiliaryFinFunctionRepresentation d auxiliaryElement2) (auxiliaryCoordinateFunction d ⟨m, by omega⟩) =
        ((d : ℂ) - ↑(m + 1)) • auxiliaryCoordinateFunction d ⟨m + 1, by omega⟩ := by
      rw [rhoLieHom_sl2_f_eq]
      ext k
      simp only [rhoF, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
        smul_eq_mul, auxiliaryCoordinateFunction, Pi.single_apply]
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
  have e0_mem : auxiliaryCoordinateFunction d ⟨0, hd_pos⟩ ∈ N := by
    suffices ∀ (m : ℕ) (hm : m < d),
        auxiliaryCoordinateFunction d ⟨m, hm⟩ ∈ N → auxiliaryCoordinateFunction d ⟨0, hd_pos⟩ ∈ N from
      this k₀.val k₀.isLt hk₀
    intro m hm
    induction m with
    | zero => exact id
    | succ m ihm => intro hmem; exact ihm (by omega) (step_down m (by omega) hmem)

  intro k
  suffices ∀ (j : ℕ) (hj : j < d), auxiliaryCoordinateFunction d ⟨j, hj⟩ ∈ N from
    this k.val k.isLt
  intro j hj
  induction j with
  | zero => exact e0_mem
  | succ j ih => exact step_up j hj (ih (by omega))
















private theorem casimir_rhoEFH (d : ℕ) :
    rhoE d * rhoF d + rhoF d * rhoE d + (2⁻¹ : ℂ) • (rhoH d * rhoH d)
      = (((d : ℂ) - 1) * ((d : ℂ) + 1) / 2) • (1 : Module.End ℂ (Fin d → ℂ)) := by
  apply LinearMap.ext; intro v; funext k
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Module.End.one_apply,
    rhoH, rhoE, rhoF, LinearMap.coe_mk, AddHom.coe_mk]
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





/-- For the displayed representation, the stated quadratic combination of three auxiliary elements is `((d - 1) * (d + 1) / 2)` times the identity. -/
theorem auxiliaryQuadraticCombination_eq_smul_id (d : ℕ) :
    auxiliaryFinFunctionRepresentation d auxiliaryElement1 * auxiliaryFinFunctionRepresentation d auxiliaryElement2
        + auxiliaryFinFunctionRepresentation d auxiliaryElement2 * auxiliaryFinFunctionRepresentation d auxiliaryElement1
        + (2⁻¹ : ℂ) • (auxiliaryFinFunctionRepresentation d auxiliaryElement3 * auxiliaryFinFunctionRepresentation d auxiliaryElement3)
      = (((d : ℂ) - 1) * ((d : ℂ) + 1) / 2) • (1 : Module.End ℂ (Fin d → ℂ)) := by
  rw [rhoLieHom_sl2_e_eq, rhoLieHom_sl2_f_eq, rhoLieHom_sl2_h_eq, casimir_rhoEFH]




/-- In the representation indexed by `lam + 1`, the stated quadratic combination of three auxiliary elements is `(lam * (lam + 2) / 2)` times the identity. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem auxiliaryQuadraticCombination_succ_eq_smul_id (lam : ℕ) :
    auxiliaryFinFunctionRepresentation (lam + 1) auxiliaryElement1 * auxiliaryFinFunctionRepresentation (lam + 1) auxiliaryElement2
        + auxiliaryFinFunctionRepresentation (lam + 1) auxiliaryElement2 * auxiliaryFinFunctionRepresentation (lam + 1) auxiliaryElement1
        + (2⁻¹ : ℂ) • (auxiliaryFinFunctionRepresentation (lam + 1) auxiliaryElement3 * auxiliaryFinFunctionRepresentation (lam + 1) auxiliaryElement3)
      = (((lam : ℂ) * ((lam : ℂ) + 2)) / 2) • (1 : Module.End ℂ (Fin (lam + 1) → ℂ)) := by
  rw [auxiliaryQuadraticCombination_eq_smul_id (lam + 1)]
  push_cast; ring_nf

end RepresentationTheory.LieAlgebra.MatrixSubalgebraRepresentationAuxiliary
