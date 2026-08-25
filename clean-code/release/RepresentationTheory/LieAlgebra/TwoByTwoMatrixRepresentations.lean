/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import RepresentationTheory.Alignment.Attribute

/-! # Representations of a two-by-two matrix Lie subalgebra -/


namespace RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations

open scoped Matrix


attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (k : Type u) [Field k]


/-- A Lie subalgebra of two-by-two matrices over a field. -/
noncomputable def twoByTwoMatrixLieSubalgebra : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) :=
  LieAlgebra.SpecialLinear.sl (Fin 2) k


/-- The raising element of the matrix Lie subalgebra. -/
noncomputable def raisingElement : twoByTwoMatrixLieSubalgebra k :=
  LieAlgebra.SpecialLinear.single 0 1 (by omega) 1


/-- The lowering element of the matrix Lie subalgebra. -/
noncomputable def loweringElement : twoByTwoMatrixLieSubalgebra k :=
  LieAlgebra.SpecialLinear.single 1 0 (by omega) 1


/-- The weight element of the matrix Lie subalgebra. -/
noncomputable def weightElement : twoByTwoMatrixLieSubalgebra k :=
  LieAlgebra.SpecialLinear.singleSubSingle 0 1 1


/-- For a matrix in the Lie subalgebra, the lower-right entry is the negative of the upper-left entry. -/
theorem entry_one_one_eq_neg_entry_zero_zero (X : twoByTwoMatrixLieSubalgebra k) : X.val 1 1 = -X.val 0 0 := by
  have h2 : X.val 0 0 + X.val 1 1 = 0 := by
    have h3 : Matrix.trace X.val = 0 := X.property
    have h4 : Matrix.trace X.val = X.val 0 0 + X.val 1 1 := by
      change ∑ i : Fin 2, X.val i i = _
      rw [Fin.sum_univ_two]
    rw [h4] at h3; exact h3
  have : X.val 1 1 = 0 - X.val 0 0 := by rw [← h2]; ring
  simpa only [zero_sub] using this


/-- The weight endomorphism of the field-valued functions on `Fin d`. -/
noncomputable def weightEnd (d : ℕ) : Module.End k (Fin d → k) where
  toFun v k' := ((d : k) - 1 - 2 * ↑(k' : ℕ)) * v k'
  map_add' u w := by ext k'; simp [mul_add]
  map_smul' r w := by ext k'; simp [mul_comm r, mul_assoc, smul_eq_mul]


/-- The raising endomorphism of the field-valued functions on `Fin d`. -/
noncomputable def raisingEnd (d : ℕ) : Module.End k (Fin d → k) where
  toFun v k' := (↑(k' : ℕ) + 1) * if h : (k' : ℕ) + 1 < d then v ⟨k' + 1, h⟩ else 0
  map_add' u w := by ext k'; simp only [Pi.add_apply]; split <;> ring
  map_smul' r w := by
    ext k'; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring


/-- The lowering endomorphism of the field-valued functions on `Fin d`. -/
noncomputable def loweringEnd (d : ℕ) : Module.End k (Fin d → k) where
  toFun v k' := ((d : k) - ↑(k' : ℕ)) *
    if h : 0 < (k' : ℕ) then v ⟨k' - 1, by omega⟩ else 0
  map_add' u w := by ext k'; simp only [Pi.add_apply]; split <;> ring
  map_smul' r w := by
    ext k'; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring


/-- The bracket of the weight and raising endomorphisms is twice the raising endomorphism. -/
theorem bracket_weightEnd_raisingEnd (d : ℕ) :
    ⁅weightEnd k d, raisingEnd k d⁆ = (2 : k) • raisingEnd k d := by
  apply LinearMap.ext; intro v; funext k'
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, weightEnd, raisingEnd, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases he : (k' : ℕ) + 1 < d
  · simp only [he, dite_true]
    push_cast; ring
  · simp only [he, dite_false, mul_zero, sub_zero]


/-- The bracket of the weight and lowering endomorphisms is minus twice the lowering endomorphism. -/
theorem bracket_weightEnd_loweringEnd (d : ℕ) :
    ⁅weightEnd k d, loweringEnd k d⁆ = -((2 : k) • loweringEnd k d) := by
  apply LinearMap.ext; intro v; funext k'
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul, weightEnd, loweringEnd, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hf : 0 < (k' : ℕ)
  · simp only [hf, dite_true]
    have hle : 1 ≤ (k' : ℕ) := by omega
    simp only [Nat.cast_sub hle]
    ring
  · simp only [hf, dite_false, mul_zero, sub_zero, neg_zero]


/-- The bracket of the raising and lowering endomorphisms is the weight endomorphism. -/
theorem bracket_raisingEnd_loweringEnd (d : ℕ) :
    ⁅raisingEnd k d, loweringEnd k d⁆ = weightEnd k d := by
  apply LinearMap.ext; intro v; funext k'
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, Pi.sub_apply,
    weightEnd, raisingEnd, loweringEnd, LinearMap.coe_mk, AddHom.coe_mk]
  have hfin_k : ∀ (h : (k' : ℕ) < d), (⟨(k' : ℕ), h⟩ : Fin d) = k' :=
    fun _ => by ext; rfl
  by_cases he : (k' : ℕ) + 1 < d <;> by_cases hf : 0 < (k' : ℕ)
  · 
    simp only [he, hf, k'.isLt, dite_true,
      show 0 < (k' : ℕ) + 1 from by omega,
      show (k' : ℕ) + 1 - 1 = (k' : ℕ) from by omega,
      show (k' : ℕ) - 1 + 1 = (k' : ℕ) from by omega,
      dite_true, hfin_k k'.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k' : ℕ) from by omega)]
    push_cast; ring
  · 
    have hk0 : (k' : ℕ) = 0 := by omega
    simp only [he, hf, dite_true, dite_false, mul_zero, sub_zero,
      show 0 < (k' : ℕ) + 1 from by omega,
      show (k' : ℕ) + 1 - 1 = (k' : ℕ) from by omega,
      dite_true, hfin_k k'.isLt]
    simp [hk0]
  · 
    simp only [he, hf, k'.isLt, dite_true, dite_false, mul_zero, zero_sub,
      show (k' : ℕ) - 1 + 1 = (k' : ℕ) from by omega,
      dite_true, hfin_k k'.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k' : ℕ) from by omega)]
    have hkd1 : (k' : ℕ) + 1 = d := by omega
    push_cast [Nat.cast_sub (show 1 ≤ d from by omega), ← hkd1]; ring
  · 
    have hk0 : (k' : ℕ) = 0 := by omega
    have hd1 : d = 1 := by omega
    simp only [he, hf, dite_false, mul_zero, zero_sub, neg_zero]
    subst hd1; simp

private theorem val_add (X Y : twoByTwoMatrixLieSubalgebra k) (i j : Fin 2) :
    (X + Y).val i j = X.val i j + Y.val i j := rfl

private theorem val_smul (r : k) (X : twoByTwoMatrixLieSubalgebra k) (i j : Fin 2) :
    (r • X).val i j = r * X.val i j := rfl


/-- The Lie algebra representation on field-valued functions on `Fin d`. -/
noncomputable def finFunctionRepresentation (d : ℕ) :
    twoByTwoMatrixLieSubalgebra k →ₗ⁅k⁆ Module.End k (Fin d → k) where
  toFun X := X.val 0 0 • weightEnd k d + X.val 0 1 • raisingEnd k d + X.val 1 0 • loweringEnd k d
  map_add' X Y := by
    simp only [val_add, add_smul]; abel
  map_smul' r X := by
    simp only [val_smul, mul_smul, RingHom.id_apply, smul_add]
  map_lie' {X Y} := by
    have htX : X.val 1 1 = -X.val 0 0 := entry_one_one_eq_neg_entry_zero_zero k X
    have htY : Y.val 1 1 = -Y.val 0 0 := entry_one_one_eq_neg_entry_zero_zero k Y
    have hEH : ⁅raisingEnd k d, weightEnd k d⁆ = -((2 : k) • raisingEnd k d) := by
      rw [← lie_skew, bracket_weightEnd_raisingEnd]
    have hFH : ⁅loweringEnd k d, weightEnd k d⁆ = (2 : k) • loweringEnd k d := by
      rw [← lie_skew, bracket_weightEnd_loweringEnd, neg_neg]
    have hFE : ⁅loweringEnd k d, raisingEnd k d⁆ = -(weightEnd k d) := by
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
    
    
    
    have smul_lie' : ∀ (c : k) (a b : Module.End k (Fin d → k)),
        ⁅c • a, b⁆ = c • ⁅a, b⁆ := fun c a b => smul_lie c a b
    have lie_smul' : ∀ (c : k) (a b : Module.End k (Fin d → k)),
        ⁅a, c • b⁆ = c • ⁅a, b⁆ := fun c a b => lie_smul c a b
    simp only [add_lie, lie_add, smul_lie', lie_smul', lie_self, smul_zero,
      add_zero, zero_add, bracket_weightEnd_raisingEnd, bracket_weightEnd_loweringEnd, bracket_raisingEnd_loweringEnd,
      hEH, hFH, hFE, smul_neg, smul_smul, hbr00, hbr01, hbr10]
    module


/-- The Lie ring module structure on functions from a finite type to the base field. -/
noncomputable instance lieRingModule_finFunction (d : ℕ) :
    LieRingModule (twoByTwoMatrixLieSubalgebra k) (Fin d → k) :=
  LieRingModule.compLieHom (Fin d → k) (finFunctionRepresentation k d)


/-- The Lie module structure on functions from a finite type to the base field. -/
noncomputable instance lieModule_finFunction (d : ℕ) :
    @LieModule k (twoByTwoMatrixLieSubalgebra k) (Fin d → k) _ _ _ _ _ (lieRingModule_finFunction k d) :=
  LieModule.compLieHom (Fin d → k) (finFunctionRepresentation k d)


/-- The finrank of the field-valued functions on a nonempty `Fin d` is `d`. -/
theorem finrank_finFunction (d : ℕ) [NeZero d] :
    Module.finrank k (Fin d → k) = d := by
  simp


private lemma finFunctionRepresentation_apply_weight (d : ℕ) : finFunctionRepresentation k d (weightElement k) = weightEnd k d := by
  have h00 : (weightElement k).val 0 0 = 1 := by
    simp [weightElement, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have h01 : (weightElement k).val 0 1 = 0 := by
    simp [weightElement, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have h10 : (weightElement k).val 1 0 = 0 := by
    simp [weightElement, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have key : finFunctionRepresentation k d (weightElement k) =
    (weightElement k).val 0 0 • weightEnd k d + (weightElement k).val 0 1 • raisingEnd k d +
      (weightElement k).val 1 0 • loweringEnd k d := rfl
  rw [key, h00, h01, h10]; simp


private lemma finFunctionRepresentation_apply_raising (d : ℕ) : finFunctionRepresentation k d (raisingElement k) = raisingEnd k d := by
  have h00 : (raisingElement k).val 0 0 = 0 := by
    simp [raisingElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h01 : (raisingElement k).val 0 1 = 1 := by
    simp [raisingElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h10 : (raisingElement k).val 1 0 = 0 := by
    simp [raisingElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have key : finFunctionRepresentation k d (raisingElement k) =
    (raisingElement k).val 0 0 • weightEnd k d + (raisingElement k).val 0 1 • raisingEnd k d +
      (raisingElement k).val 1 0 • loweringEnd k d := rfl
  rw [key, h00, h01, h10]; simp


private lemma finFunctionRepresentation_apply_lowering (d : ℕ) : finFunctionRepresentation k d (loweringElement k) = loweringEnd k d := by
  have h00 : (loweringElement k).val 0 0 = 0 := by
    simp [loweringElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h01 : (loweringElement k).val 0 1 = 0 := by
    simp [loweringElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h10 : (loweringElement k).val 1 0 = 1 := by
    simp [loweringElement, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have key : finFunctionRepresentation k d (loweringElement k) =
    (loweringElement k).val 0 0 • weightEnd k d + (loweringElement k).val 0 1 • raisingEnd k d +
      (loweringElement k).val 1 0 • loweringEnd k d := rfl
  rw [key, h00, h01, h10]; simp


/-- The coordinate vector at a specified index of a finite function space over a field. -/
def coordinateVector (d : ℕ) (k' : Fin d) : Fin d → k := Pi.single k' 1


/-- A coordinate vector is one at its distinguished index and zero at every other index. -/
theorem coordinateVector_apply (d : ℕ) (k' j : Fin d) :
    coordinateVector k d k' j = if j = k' then 1 else 0 := by
  simp [coordinateVector, Pi.single_apply]


private theorem natCast_inj_lt (p : ℕ) [CharP k p] {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : k) = (b : k)) : a = b := by
  rcases le_total a b with hab | hab
  · have hz : ((b - a : ℕ) : k) = 0 := by rw [Nat.cast_sub hab, h, sub_self]
    rw [CharP.cast_eq_zero_iff k p] at hz
    have := Nat.eq_zero_of_dvd_of_lt hz (by omega)
    omega
  · have hz : ((a - b : ℕ) : k) = 0 := by rw [Nat.cast_sub hab, h, sub_self]
    rw [CharP.cast_eq_zero_iff k p] at hz
    have := Nat.eq_zero_of_dvd_of_lt hz (by omega)
    omega


private theorem natCast_ne_zero_of_lt (p : ℕ) [CharP k p] {n : ℕ} (h0 : 0 < n) (hn : n < p) :
    (n : k) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff k p]
  intro hdvd
  have := Nat.eq_zero_of_dvd_of_lt hdvd hn
  omega


/-- The finite-function Lie module of positive dimension at most the characteristic is irreducible when the characteristic is greater than two. -/
theorem isIrreducible_finFunction_of_le_characteristic (p : ℕ) [CharP k p] (hp2 : 2 < p) (d : ℕ) [NeZero d] (hdp : d ≤ p) :
    LieModule.IsIrreducible k (twoByTwoMatrixLieSubalgebra k) (Fin d → k) := by
  classical
  have h2ne : (2 : k) ≠ 0 := by
    have h := natCast_ne_zero_of_lt k p (show (0 : ℕ) < 2 by norm_num) hp2
    simpa using h
  apply LieModule.IsIrreducible.mk
  intro N hN
  rw [ne_eq, LieSubmodule.eq_bot_iff] at hN
  push Not at hN
  obtain ⟨w, hw_mem, hw_ne⟩ := hN
  
  have lie_h_comp : ∀ (v : Fin d → k) (k' : Fin d),
      ((finFunctionRepresentation k d (weightElement k)) v) k' = ((d : k) - 1 - 2 * ↑(k' : ℕ)) * v k' := by
    intro v k'; rw [finFunctionRepresentation_apply_weight]; rfl
  
  have smul_extract : ∀ (c : k) (v : Fin d → k), c ≠ 0 → c • v ∈ N → v ∈ N := by
    intro c v hc hcv
    have h1 : c⁻¹ • (c • v) ∈ N := N.smul_mem c⁻¹ hcv
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
  
  suffices basis_in_N : ∀ k' : Fin d, coordinateVector k d k' ∈ N by
    rw [eq_top_iff]; intro v _
    have decomp : v = Finset.univ.sum (fun k' : Fin d => v k' • coordinateVector k d k') := by
      ext j; simp [Finset.sum_apply, coordinateVector_apply]
    rw [decomp]
    refine Finset.sum_induction _
      (· ∈ (N : Set (Fin d → k))) (fun a b ha hb => ?_) ?_
      (fun k' _ => ?_)
    · exact N.add_mem ha hb
    · exact N.zero_mem
    · exact N.smul_mem _ (basis_in_N k')
  
  have extract : ∃ k' : Fin d, coordinateVector k d k' ∈ N := by
    suffices ∀ (n : ℕ) (w : Fin d → k), w ∈ N → w ≠ 0 →
        (Finset.univ.filter (fun k' => w k' ≠ 0)).card ≤ n →
        ∃ k' : Fin d, coordinateVector k d k' ∈ N by
      exact this _ w hw_mem hw_ne le_rfl
    intro n
    induction n with
    | zero =>
      intro w _ hw_ne hn
      exfalso; apply hw_ne; ext k'
      by_contra hk
      have : k' ∈ Finset.univ.filter (fun k' => w k' ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k', hk⟩
      exact absurd (Finset.card_pos.mpr ⟨k', this⟩) (by omega)
    | succ n ih =>
      intro w hw_mem hw_ne hn
      by_cases hn1 : (Finset.univ.filter (fun k' => w k' ≠ 0)).card ≤ 1
      · 
        have hcard := Finset.card_le_one.mp hn1
        have hne : (Finset.univ.filter (fun k' => w k' ≠ 0)).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]; intro hempty
          apply hw_ne; ext k'
          by_contra hk
          have : k' ∈ (∅ : Finset (Fin d)) :=
            hempty ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ k', hk⟩
          simp at this
        obtain ⟨k', hk_mem⟩ := hne
        have hk : k' ∈ Finset.univ ∧ w k' ≠ 0 := Finset.mem_filter.mp hk_mem
        refine ⟨k', ?_⟩
        have hw_eq : w = w k' • coordinateVector k d k' := by
          ext j
          simp only [Pi.smul_apply, coordinateVector_apply, smul_eq_mul]
          by_cases hjk : j = k'
          · subst hjk; simp
          · have : w j = 0 := by
              by_contra hj
              exact hjk (hcard j
                (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) k' hk_mem)
            simp [this, hjk]
        rw [hw_eq] at hw_mem
        exact smul_extract _ _ hk.2 hw_mem
      · 
        push Not at hn1
        obtain ⟨j₁, hj₁_mem, j₂, hj₂_mem, hne⟩ :=
          Finset.one_lt_card.mp hn1
        have hj₁ := (Finset.mem_filter.mp hj₁_mem).2
        have hj₂ := (Finset.mem_filter.mp hj₂_mem).2
        let c : k := (d : k) - 1 - 2 * ↑(j₁ : ℕ)
        have hw'_mem :
            (fun i => ((finFunctionRepresentation k d (weightElement k)) w) i - c * w i) ∈ N := by
          change (finFunctionRepresentation k d (weightElement k)) w - c • w ∈ (N : Set _)
          exact N.sub_mem (N.lie_mem hw_mem) (N.smul_mem c hw_mem)
        have hw'_val : ∀ i : Fin d,
            ((finFunctionRepresentation k d (weightElement k)) w i - c * w i) =
            (2 * (↑(j₁ : ℕ) - ↑(i : ℕ))) * w i := by
          intro i; rw [lie_h_comp]; ring
        have hw'_ne : (fun i => (finFunctionRepresentation k d (weightElement k)) w i - c * w i) ≠ 0 := by
          intro h
          have hval := congr_fun h j₂
          rw [hw'_val] at hval
          rcases mul_eq_zero.mp hval with hz | hz
          · rcases mul_eq_zero.mp hz with h2 | hsub
            · exact h2ne h2
            · exact hne (Fin.ext (natCast_inj_lt k p (j₁.isLt.trans_le hdp)
                (j₂.isLt.trans_le hdp) (sub_eq_zero.mp hsub)))
          · exact hj₂ hz
        have hw'_fewer :
            (Finset.univ.filter (fun k' =>
              (finFunctionRepresentation k d (weightElement k)) w k' - c * w k' ≠ 0)).card ≤ n := by
          have hssub : (Finset.univ.filter (fun k' =>
              (finFunctionRepresentation k d (weightElement k)) w k' - c * w k' ≠ 0)) ⊂
            (Finset.univ.filter (fun k' => w k' ≠ 0)) := by
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
      coordinateVector k d ⟨m + 1, by omega⟩ ∈ N →
      coordinateVector k d ⟨m, by omega⟩ ∈ N := by
    intro m hm hmem
    have lie_in_N : (finFunctionRepresentation k d (raisingElement k)) (coordinateVector k d ⟨m + 1, by omega⟩) ∈ N :=
      N.lie_mem hmem
    have lie_eq : (finFunctionRepresentation k d (raisingElement k)) (coordinateVector k d ⟨m + 1, by omega⟩) =
        (↑(m + 1) : k) • coordinateVector k d ⟨m, by omega⟩ := by
      rw [finFunctionRepresentation_apply_raising]
      ext k'
      simp only [raisingEnd, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
        smul_eq_mul, coordinateVector, Pi.single_apply]
      by_cases hk : (k' : ℕ) + 1 < d
      · simp only [hk, dite_true]
        by_cases hkm : (k' : ℕ) = m
        · subst hkm; simp
        · have hne1 : ¬((k' : ℕ) + 1 = m + 1) := by omega
          simp [Fin.ext_iff, hkm]
      · simp only [hk, dite_false, mul_zero]
        by_cases hkm : (k' : ℕ) = m
        · exfalso; omega
        · simp [Fin.ext_iff, hkm]
    rw [lie_eq] at lie_in_N
    exact smul_extract _ _
      (natCast_ne_zero_of_lt k p (by omega : 0 < m + 1) (by omega : m + 1 < p)) lie_in_N
  
  have step_up : ∀ (m : ℕ) (hm : m + 1 < d),
      coordinateVector k d ⟨m, by omega⟩ ∈ N →
      coordinateVector k d ⟨m + 1, by omega⟩ ∈ N := by
    intro m hm hmem
    have lie_in_N : (finFunctionRepresentation k d (loweringElement k)) (coordinateVector k d ⟨m, by omega⟩) ∈ N :=
      N.lie_mem hmem
    have lie_eq : (finFunctionRepresentation k d (loweringElement k)) (coordinateVector k d ⟨m, by omega⟩) =
        ((d : k) - ↑(m + 1)) • coordinateVector k d ⟨m + 1, by omega⟩ := by
      rw [finFunctionRepresentation_apply_lowering]
      ext k'
      simp only [loweringEnd, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
        smul_eq_mul, coordinateVector, Pi.single_apply]
      by_cases hk : 0 < (k' : ℕ)
      · simp only [hk, dite_true]
        by_cases hkm : (k' : ℕ) = m + 1
        · have hksub : (k' : ℕ) - 1 = m := by omega
          have hkeq : k' = ⟨m + 1, by omega⟩ := Fin.ext (by omega)
          simp [hkeq]
        · have : (k' : ℕ) - 1 ≠ m := by omega
          simp [Fin.ext_iff, this, hkm]
      · simp only [hk, dite_false, mul_zero]
        push Not at hk
        simp [Fin.ext_iff, show (k' : ℕ) ≠ m + 1 from by omega]
    rw [lie_eq] at lie_in_N
    have hc : ((d : k) - ↑(m + 1)) ≠ 0 := by
      rw [← Nat.cast_sub (by omega : m + 1 ≤ d)]
      exact natCast_ne_zero_of_lt k p (by omega : 0 < d - (m + 1)) (by omega : d - (m + 1) < p)
    exact smul_extract _ _ hc lie_in_N
  
  have hd_pos : 0 < d := NeZero.pos d
  have e0_mem : coordinateVector k d ⟨0, hd_pos⟩ ∈ N := by
    suffices ∀ (m : ℕ) (hm : m < d),
        coordinateVector k d ⟨m, hm⟩ ∈ N → coordinateVector k d ⟨0, hd_pos⟩ ∈ N from
      this k₀.val k₀.isLt hk₀
    intro m hm
    induction m with
    | zero => exact id
    | succ m ihm => intro hmem; exact ihm (by omega) (step_down m (by omega) hmem)
  
  intro k'
  suffices ∀ (j : ℕ) (hj : j < d), coordinateVector k d ⟨j, hj⟩ ∈ N from
    this k'.val k'.isLt
  intro j hj
  induction j with
  | zero => exact e0_mem
  | succ j ih => exact step_up j hj (ih (by omega))


section DimensionBound

variable {k}


/-- The bracket of the weight and raising elements is twice the raising element. -/
theorem bracket_weight_raising : ⁅weightElement k, raisingElement k⁆ = (2 : k) • raisingElement k := by
  apply Subtype.ext
  
  
  
  rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket,
    show (↑((2 : k) • raisingElement k) : Matrix (Fin 2) (Fin 2) k) = (2 : k) • ↑(raisingElement k) from rfl]
  simp only [weightElement, raisingElement, LieAlgebra.SpecialLinear.val_singleSubSingle,
    LieAlgebra.SpecialLinear.val_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply] ; ring


/-- The bracket of the weight and lowering elements is minus twice the lowering element. -/
theorem bracket_weight_lowering : ⁅weightElement k, loweringElement k⁆ = -((2 : k) • loweringElement k) := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket,
    show (↑(-((2 : k) • loweringElement k)) : Matrix (Fin 2) (Fin 2) k) = -((2 : k) • ↑(loweringElement k)) from rfl]
  simp only [weightElement, loweringElement, LieAlgebra.SpecialLinear.val_singleSubSingle,
    LieAlgebra.SpecialLinear.val_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply] ; ring


/-- The bracket of the raising and lowering elements is the weight element. -/
theorem bracket_raising_lowering : ⁅raisingElement k, loweringElement k⁆ = weightElement k := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket]
  simp only [weightElement, raisingElement, loweringElement, LieAlgebra.SpecialLinear.val_singleSubSingle,
    LieAlgebra.SpecialLinear.val_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply]


/-- Every element of the matrix Lie subalgebra is the indicated linear combination of the raising, lowering, and weight elements. -/
theorem eq_linearCombination_raising_lowering_weight (x : twoByTwoMatrixLieSubalgebra k) :
    x = x.val 0 1 • raisingElement k + x.val 1 0 • loweringElement k + x.val 0 0 • weightElement k := by
  apply Subtype.ext
  have htr : x.val 1 1 = -x.val 0 0 := entry_one_one_eq_neg_entry_zero_zero k x
  
  
  
  rw [show (↑(x.val 0 1 • raisingElement k + x.val 1 0 • loweringElement k + x.val 0 0 • weightElement k)
        : Matrix (Fin 2) (Fin 2) k)
      = x.val 0 1 • (↑(raisingElement k) : Matrix (Fin 2) (Fin 2) k)
        + x.val 1 0 • ↑(loweringElement k) + x.val 0 0 • ↑(weightElement k) from rfl]
  simp only [raisingElement, loweringElement, weightElement, LieAlgebra.SpecialLinear.val_single,
    LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, htr]


section SchurHelpers

variable {M : Type*} [AddCommGroup M] [Module k M] [LieRingModule (twoByTwoMatrixLieSubalgebra k) M]
  [LieModule k (twoByTwoMatrixLieSubalgebra k) M]

omit [LieModule k (twoByTwoMatrixLieSubalgebra k) M] in


/-- In an irreducible Lie module, a Lie-stable submodule containing a nonzero vector is the whole module. -/
theorem eq_top_of_lieStable_of_exists_ne_zero [LieModule.IsIrreducible k (twoByTwoMatrixLieSubalgebra k) M]
    (W : Submodule k M) (hlie : ∀ (x : twoByTwoMatrixLieSubalgebra k) (m : M), m ∈ W → ⁅x, m⁆ ∈ W)
    (hne : ∃ v ∈ W, v ≠ 0) : W = ⊤ := by
  let N : LieSubmodule k (twoByTwoMatrixLieSubalgebra k) M :=
    { toSubmodule := W, lie_mem := fun {x m} h => hlie x m h }
  have hNbot : N ≠ ⊥ := by
    rw [ne_eq, LieSubmodule.eq_bot_iff]
    push Not
    obtain ⟨v, hvW, hv0⟩ := hne
    exact ⟨v, hvW, hv0⟩
  have hNtop : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hNbot
  have hWtop : (N : Submodule k M) = ⊤ := by rw [LieSubmodule.toSubmodule_eq_top]; exact hNtop
  exact hWtop


/-- A submodule stable under the raising, lowering, and weight elements is stable under every element of the matrix Lie subalgebra. -/
theorem lieStable_of_stable_generators (W : Submodule k M)
    (hE : ∀ m ∈ W, ⁅raisingElement k, m⁆ ∈ W)
    (hF : ∀ m ∈ W, ⁅loweringElement k, m⁆ ∈ W)
    (hH : ∀ m ∈ W, ⁅weightElement k, m⁆ ∈ W) :
    ∀ (x : twoByTwoMatrixLieSubalgebra k) (m : M), m ∈ W → ⁅x, m⁆ ∈ W := by
  intro x m hm
  have e1 : ∀ y : twoByTwoMatrixLieSubalgebra k, ⁅y, m⁆ = (LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M y) m := fun _ => rfl
  have key : ⁅x, m⁆ = x.val 0 1 • ⁅raisingElement k, m⁆ + x.val 1 0 • ⁅loweringElement k, m⁆
      + x.val 0 0 • ⁅weightElement k, m⁆ := by
    conv_lhs => rw [e1 x, eq_linearCombination_raising_lowering_weight x, map_add, map_add, map_smul, map_smul, map_smul,
      LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      LinearMap.smul_apply]
    rw [e1 (raisingElement k), e1 (loweringElement k), e1 (weightElement k)]
  rw [key]
  exact W.add_mem (W.add_mem (W.smul_mem _ (hE m hm)) (W.smul_mem _ (hF m hm)))
    (W.smul_mem _ (hH m hm))


/-- An endomorphism of a finite-dimensional irreducible Lie module over an algebraically closed field that commutes with the Lie action acts by a scalar. -/
theorem exists_scalar_action_eq_of_commutes_lieAction [IsAlgClosed k] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (twoByTwoMatrixLieSubalgebra k) M]
    (φ : Module.End k M) (hφ : ∀ (x : twoByTwoMatrixLieSubalgebra k) (m : M), φ ⁅x, m⁆ = ⁅x, φ m⁆) :
    ∃ c : k, ∀ m : M, φ m = c • m := by
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (twoByTwoMatrixLieSubalgebra k) M
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue φ
  refine ⟨μ, ?_⟩
  have hclosed : ∀ (x : twoByTwoMatrixLieSubalgebra k) (m : M), m ∈ φ.eigenspace μ → ⁅x, m⁆ ∈ φ.eigenspace μ := by
    intro x m hm
    rw [Module.End.mem_eigenspace_iff] at hm ⊢
    rw [hφ, hm, lie_smul]
  have hne : ∃ v ∈ φ.eigenspace μ, v ≠ 0 := by
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    exact ⟨v, hv.1, hv.2⟩
  have htop := eq_top_of_lieStable_of_exists_ne_zero (φ.eigenspace μ) hclosed hne
  intro m
  have hm : m ∈ φ.eigenspace μ := by rw [htop]; trivial
  rwa [Module.End.mem_eigenspace_iff] at hm

omit [LieRingModule (twoByTwoMatrixLieSubalgebra k) M] [LieModule k (twoByTwoMatrixLieSubalgebra k) M] in


/-- A linear endomorphism that sends every member of a set into its span preserves that span. -/
theorem map_mem_span_of_forall_mem_span (T : Module.End k M) (S : Set M)
    (h : ∀ s ∈ S, T s ∈ Submodule.span k S) {m : M} (hm : m ∈ Submodule.span k S) :
    T m ∈ Submodule.span k S := by
  induction hm using Submodule.span_induction with
  | mem s hs => exact h s hs
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

omit [LieRingModule (twoByTwoMatrixLieSubalgebra k) M] [LieModule k (twoByTwoMatrixLieSubalgebra k) M] in


/-- If the vectors indexed by `Fin p` span a module, then its finrank is at most `p`. -/
theorem finrank_le_of_span_range_fin_eq_top (p : ℕ) (g : ℕ → M)
    (htop : Submodule.span k (Set.range (fun i : Fin p => g (i : ℕ))) = ⊤) :
    Module.finrank k M ≤ p := by
  have := finrank_le_of_span_eq_top htop
  simpa using this

end SchurHelpers


variable (k)


/-- Over an algebraically closed field of prime characteristic greater than two, every finite-dimensional irreducible module has finrank at most the characteristic. -/
theorem finrank_le_characteristic [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hp : 2 < p)
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (twoByTwoMatrixLieSubalgebra k) M] [LieModule k (twoByTwoMatrixLieSubalgebra k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (twoByTwoMatrixLieSubalgebra k) M] :
    Module.finrank k M ≤ p := by
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (twoByTwoMatrixLieSubalgebra k) M
  
  set E := LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M (raisingElement k) with hEdef
  set F := LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M (loweringElement k) with hFdef
  set H := LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M (weightElement k) with hHdef
  
  have hEe : ∀ m : M, ⁅raisingElement k, m⁆ = E m := fun _ => rfl
  have hFf : ∀ m : M, ⁅loweringElement k, m⁆ = F m := fun _ => rfl
  have hHh : ∀ m : M, ⁅weightElement k, m⁆ = H m := fun _ => rfl
  
  have hHE : H * E = E * H + (2 : k) • E := by
    have h1 : (⁅H, E⁆ : Module.End k M) = (2 : k) • E := by
      rw [hHdef, hEdef, ← (LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M).map_lie, bracket_weight_raising, map_smul]
    rw [LieRing.of_associative_ring_bracket, sub_eq_iff_eq_add] at h1
    rw [h1, add_comm]
  have hHF : H * F = F * H - (2 : k) • F := by
    have h1 : (⁅H, F⁆ : Module.End k M) = -((2 : k) • F) := by
      rw [hHdef, hFdef, ← (LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M).map_lie, bracket_weight_lowering, map_neg, map_smul]
    rw [LieRing.of_associative_ring_bracket, sub_eq_iff_eq_add] at h1
    rw [h1]; abel
  have hEF : E * F - F * E = H := by
    have h1 : (⁅E, F⁆ : Module.End k M) = H := by
      rw [hEdef, hFdef, ← (LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M).map_lie, bracket_raising_lowering]
    rwa [LieRing.of_associative_ring_bracket] at h1
  
  have hHEpow : ∀ i : ℕ, H * E ^ i = E ^ i * H + ((2 * i : ℕ) : k) • E ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ n ih =>
      have hsc : ((2 : k) + ((2 * n : ℕ) : k)) = ((2 * (n + 1) : ℕ) : k) := by push_cast; ring
      calc H * E ^ (n + 1)
          = (H * E ^ n) * E := by rw [pow_succ, ← mul_assoc]
        _ = (E ^ n * H + ((2 * n : ℕ) : k) • E ^ n) * E := by rw [ih]
        _ = E ^ n * (H * E) + ((2 * n : ℕ) : k) • (E ^ n * E) := by
              rw [add_mul, mul_assoc, smul_mul_assoc]
        _ = E ^ n * (E * H + (2 : k) • E) + ((2 * n : ℕ) : k) • (E ^ n * E) := by rw [hHE]
        _ = (E ^ n * E) * H + ((2 : k) + ((2 * n : ℕ) : k)) • (E ^ n * E) := by
              rw [mul_add, ← mul_assoc, mul_smul_comm, add_assoc, ← add_smul]
        _ = E ^ (n + 1) * H + ((2 * (n + 1) : ℕ) : k) • E ^ (n + 1) := by rw [hsc, ← pow_succ]
  
  have hrec : ∀ m : ℕ, F * E ^ (m + 1) - E ^ (m + 1) * F
      = (F * E ^ m - E ^ m * F) * E - E ^ m * H := by
    intro m
    have hEFc : E * F = F * E + H := by rw [← hEF]; abel
    calc F * E ^ (m + 1) - E ^ (m + 1) * F
        = F * E ^ m * E - E ^ m * (E * F) := by rw [pow_succ]; noncomm_ring
      _ = F * E ^ m * E - E ^ m * (F * E + H) := by rw [hEFc]
      _ = F * E ^ m * E - E ^ m * (F * E) - E ^ m * H := by noncomm_ring
      _ = (F * E ^ m - E ^ m * F) * E - E ^ m * H := by noncomm_ring
  have hFEpow : ∀ n : ℕ, F * E ^ (n + 1) - E ^ (n + 1) * F
      = -(((n + 1 : ℕ) : k)) • (E ^ n * H) - (((n + 1) * n : ℕ) : k) • E ^ n := by
    intro n
    induction n with
    | zero =>
      have hlhs : F * E ^ (0 + 1) - E ^ (0 + 1) * F = -H := by
        rw [zero_add, pow_one, ← hEF]; abel
      have hrhs : -(((0 + 1 : ℕ) : k)) • (E ^ 0 * H) - (((0 + 1) * 0 : ℕ) : k) • E ^ 0 = -H := by
        simp
      rw [hlhs, hrhs]
    | succ n ih =>
      rw [hrec (n + 1), ih]
      have hHErw : E ^ (n + 1) * H = E ^ n * (H * E) - (2 : k) • E ^ (n + 1) := by
        rw [hHE]; noncomm_ring
      
      have hsc1 : (((n + 1 : ℕ) : k) + 1) = (((n + 1) + 1 : ℕ) : k) := by push_cast; ring
      have hsc2 : ((2 : k) * ((n + 1 : ℕ) : k) + (((n + 1) * n : ℕ) : k))
          = ((((n + 1) + 1) * (n + 1) : ℕ) : k) := by push_cast; ring
      rw [sub_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc, hHE, mul_add, mul_smul_comm,
        ← pow_succ]
      
      rw [show (E ^ n * (E * H)) = E ^ (n + 1) * H from by rw [pow_succ]; noncomm_ring]
      module
  
  have hcharp : ((p : ℕ) : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k p
  have hcomm_to_schur : ∀ (φ : Module.End k M), φ * E = E * φ → φ * F = F * φ →
      φ * H = H * φ → ∀ (x : twoByTwoMatrixLieSubalgebra k) (m : M), φ ⁅x, m⁆ = ⁅x, φ m⁆ := by
    intro φ hcE hcF hcH x m
    have hxdecomp : (LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M x)
        = x.val 0 1 • E + x.val 1 0 • F + x.val 0 0 • H := by
      conv_lhs => rw [eq_linearCombination_raising_lowering_weight x]
      rw [map_add, map_add, map_smul, map_smul, map_smul, ← hEdef, ← hFdef, ← hHdef]
    have hgen : φ * (LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M x) = (LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M x) * φ := by
      rw [hxdecomp, mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm, hcE, hcF, hcH,
        ← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, ← add_mul, ← add_mul]
    calc φ ⁅x, m⁆ = φ ((LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M x) m) := rfl
      _ = (φ * (LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M x)) m := rfl
      _ = ((LieModule.toEnd k (twoByTwoMatrixLieSubalgebra k) M x) * φ) m := by rw [hgen]
      _ = ⁅x, φ m⁆ := rfl
  
  have hEpFcomm : E ^ p * F = F * E ^ p := by
    have hp1 : p - 1 + 1 = p := by omega
    have h := hFEpow (p - 1)
    have hz1 : (((p - 1 + 1 : ℕ) : k)) = 0 := by rw [hp1]; exact hcharp
    have hz2 : ((((p - 1 + 1) * (p - 1) : ℕ) : k)) = 0 := by
      rw [hp1]; push_cast [hcharp]; ring
    rw [hz1, hz2] at h
    simp only [neg_zero, zero_smul, sub_zero] at h
    rw [hp1] at h
    exact (sub_eq_zero.mp h).symm
  have hEpHcomm : E ^ p * H = H * E ^ p := by
    have h := hHEpow p
    have hz : (((2 * p : ℕ) : k)) = 0 := by push_cast [hcharp]; ring
    rw [hz, zero_smul, add_zero] at h
    exact h.symm
  have hEpEcomm : E ^ p * E = E * E ^ p := by rw [← pow_succ, ← pow_succ']
  obtain ⟨α, hα'⟩ := exists_scalar_action_eq_of_commutes_lieAction (E ^ p) (hcomm_to_schur (E ^ p) hEpEcomm hEpFcomm hEpHcomm)
  have hα : E ^ p = α • 1 := by ext m; rw [hα' m]; simp
  
  have hFpEcomm : F ^ p * E = E * F ^ p := by
    
    have hHF' : (-H) * F = F * (-H) + (2 : k) • F := by
      rw [neg_mul, mul_neg, hHF]; abel
    have hFE' : F * E - E * F = -H := by rw [← hEF]; abel
    
    have hrec' : ∀ m : ℕ, E * F ^ (m + 1) - F ^ (m + 1) * E
        = (E * F ^ m - F ^ m * E) * F - F ^ m * (-H) := by
      intro m
      have hFEc : F * E = E * F + (-H) := by rw [← hFE']; abel
      calc E * F ^ (m + 1) - F ^ (m + 1) * E
          = E * F ^ m * F - F ^ m * (F * E) := by rw [pow_succ]; noncomm_ring
        _ = E * F ^ m * F - F ^ m * (E * F + (-H)) := by rw [hFEc]
        _ = E * F ^ m * F - F ^ m * (E * F) - F ^ m * (-H) := by noncomm_ring
        _ = (E * F ^ m - F ^ m * E) * F - F ^ m * (-H) := by noncomm_ring
    have hFFpow : ∀ n : ℕ, E * F ^ (n + 1) - F ^ (n + 1) * E
        = -(((n + 1 : ℕ) : k)) • (F ^ n * (-H)) - (((n + 1) * n : ℕ) : k) • F ^ n := by
      intro n
      induction n with
      | zero =>
        have hlhs : E * F ^ (0 + 1) - F ^ (0 + 1) * E = -(-H) := by
          rw [zero_add, pow_one, ← hFE']; abel
        have hrhs : -(((0 + 1 : ℕ) : k)) • (F ^ 0 * (-H)) - (((0 + 1) * 0 : ℕ) : k) • F ^ 0
            = -(-H) := by simp
        rw [hlhs, hrhs]
      | succ n ih =>
        rw [hrec' (n + 1), ih]
        rw [sub_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc, hHF', mul_add, mul_smul_comm,
          ← pow_succ]
        rw [show (F ^ n * (F * (-H))) = F ^ (n + 1) * (-H) from by rw [pow_succ]; noncomm_ring]
        module
    have hp1 : p - 1 + 1 = p := by omega
    have hh := hFFpow (p - 1)
    have hz1 : (((p - 1 + 1 : ℕ) : k)) = 0 := by rw [hp1]; exact hcharp
    have hz2 : ((((p - 1 + 1) * (p - 1) : ℕ) : k)) = 0 := by rw [hp1]; push_cast [hcharp]; ring
    rw [hz1, hz2] at hh
    simp only [neg_zero, zero_smul, sub_zero] at hh
    rw [hp1] at hh
    exact (sub_eq_zero.mp hh).symm
  have hFpHcomm : F ^ p * H = H * F ^ p := by
    
    have hHFpow : ∀ i : ℕ, H * F ^ i = F ^ i * H - ((2 * i : ℕ) : k) • F ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ n ih =>
        have hsc : (((2 * (n + 1) : ℕ) : k)) = ((2 * n : ℕ) : k) + (2 : k) := by push_cast; ring
        calc H * F ^ (n + 1)
            = (H * F ^ n) * F := by rw [pow_succ, ← mul_assoc]
          _ = (F ^ n * H - ((2 * n : ℕ) : k) • F ^ n) * F := by rw [ih]
          _ = F ^ n * (H * F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by
                rw [sub_mul, mul_assoc, smul_mul_assoc]
          _ = F ^ n * (F * H - (2 : k) • F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by rw [hHF]
          _ = F ^ (n + 1) * H - ((2 * (n + 1) : ℕ) : k) • F ^ (n + 1) := by
                rw [mul_sub, ← mul_assoc, mul_smul_comm, ← pow_succ, hsc, add_smul]
                abel
    have h := hHFpow p
    have hz : (((2 * p : ℕ) : k)) = 0 := by push_cast [hcharp]; ring
    rw [hz, zero_smul, sub_zero] at h
    exact h.symm
  have hFpFcomm : F ^ p * F = F * F ^ p := by rw [← pow_succ, ← pow_succ']
  obtain ⟨β, hβ'⟩ := exists_scalar_action_eq_of_commutes_lieAction (F ^ p) (hcomm_to_schur (F ^ p) hFpEcomm hFpFcomm hFpHcomm)
  have hβ : F ^ p = β • 1 := by ext m; rw [hβ' m]; simp
  
  
  have hHFpow : ∀ i : ℕ, H * F ^ i = F ^ i * H - ((2 * i : ℕ) : k) • F ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ n ih =>
      have hsc : (((2 * (n + 1) : ℕ) : k)) = ((2 * n : ℕ) : k) + (2 : k) := by push_cast; ring
      calc H * F ^ (n + 1)
          = (H * F ^ n) * F := by rw [pow_succ, ← mul_assoc]
        _ = (F ^ n * H - ((2 * n : ℕ) : k) • F ^ n) * F := by rw [ih]
        _ = F ^ n * (H * F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by
              rw [sub_mul, mul_assoc, smul_mul_assoc]
        _ = F ^ n * (F * H - (2 : k) • F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by rw [hHF]
        _ = F ^ (n + 1) * H - ((2 * (n + 1) : ℕ) : k) • F ^ (n + 1) := by
              rw [mul_sub, ← mul_assoc, mul_smul_comm, ← pow_succ, hsc, add_smul]
              abel
  by_cases hα0 : α = 0
  · 
    have hEnil : E ^ p = 0 := by rw [hα, hα0, zero_smul]
    
    have hKne : LinearMap.ker E ≠ ⊥ := by
      rw [Ne, LinearMap.ker_eq_bot]
      intro hEinj
      have hEpinj : Function.Injective (E ^ p) := by
        rw [Module.End.coe_pow]; exact hEinj.iterate p
      rw [hEnil] at hEpinj
      obtain ⟨a, b, hab⟩ := exists_pair_ne M
      exact hab (hEpinj (by simp))
    
    have hHK : ∀ v ∈ LinearMap.ker E, H v ∈ LinearMap.ker E := by
      intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have hEH : E * H = H * E - (2 : k) • E := by rw [hHE]; abel
      have hEHv : E (H v) = (E * H) v := rfl
      rw [hEHv, hEH]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, hv]
      simp
    
    haveI : Nontrivial (LinearMap.ker E) := (Submodule.nontrivial_iff_ne_bot).mpr hKne
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue (H.restrict hHK)
    obtain ⟨w, hw⟩ := hlam.exists_hasEigenvector
    set v0 : M := (w : M) with hv0def
    have hv0ne : v0 ≠ 0 := by rw [hv0def, Ne, Submodule.coe_eq_zero]; exact hw.2
    have hEv0 : E v0 = 0 := LinearMap.mem_ker.mp w.2
    have hHv0 : H v0 = lam • v0 := by
      have h1 : (H.restrict hHK) w = lam • w := (Module.End.mem_eigenspace_iff).mp hw.1
      have := congrArg (Subtype.val) h1
      simpa [LinearMap.restrict_apply, hv0def, Submodule.coe_smul] using this
    
    set g : ℕ → M := fun j => (F ^ j) v0 with hgdef
    set W : Submodule k M := Submodule.span k (Set.range (fun i : Fin p => g (i : ℕ))) with hWdef
    have hg0 : g 0 = v0 := by simp [hgdef]
    have hmemgen : ∀ j : ℕ, j < p → g j ∈ W := fun j hj =>
      Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    
    have hFW : ∀ w ∈ W, F w ∈ W := by
      refine fun w hw => map_mem_span_of_forall_mem_span F _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hFg : F (g (i : ℕ)) = g ((i : ℕ) + 1) := by
        simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
      rw [hFg]
      by_cases hip : (i : ℕ) + 1 < p
      · exact hmemgen _ hip
      · have hip1 : (i : ℕ) + 1 = p := by omega
        have hval : g ((i : ℕ) + 1) = β • v0 := by
          simp only [hgdef, hip1, hβ, LinearMap.smul_apply, Module.End.one_apply]
        rw [hval]
        exact W.smul_mem β (hg0 ▸ hmemgen 0 (by omega))
    have hgW : ∀ j, g j ∈ W := by
      intro j
      induction j with
      | zero => exact hg0 ▸ hmemgen 0 (by omega)
      | succ j ih =>
        have hFg : g (j + 1) = F (g j) := by
          simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
        rw [hFg]; exact hFW _ ih
    
    have hHW : ∀ w ∈ W, H w ∈ W := by
      refine fun w hw => map_mem_span_of_forall_mem_span H _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hval : H (g (i : ℕ)) = lam • g (i : ℕ) - ((2 * (i : ℕ) : ℕ) : k) • g (i : ℕ) := by
        simp only [hgdef]
        rw [← Module.End.mul_apply, hHFpow (i : ℕ)]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, hHv0, map_smul]
      rw [hval]
      exact W.sub_mem (W.smul_mem _ (hmemgen _ i.isLt)) (W.smul_mem _ (hmemgen _ i.isLt))
    
    have hEW : ∀ w ∈ W, E w ∈ W := by
      have hEorbit : ∀ j : ℕ, E (g j) ∈ W := by
        intro j
        induction j with
        | zero =>
          have hz : E (g 0) = 0 := by rw [hg0]; exact hEv0
          rw [hz]; exact W.zero_mem
        | succ j ih =>
          have hEF' : E * F = F * E + H := by rw [← hEF]; abel
          have hstep : E (g (j + 1)) = F (E (g j)) + H (g j) := by
            have hFg : g (j + 1) = F (g j) := by
              simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
            rw [hFg, ← Module.End.mul_apply, hEF']
            simp only [LinearMap.add_apply, Module.End.mul_apply]
          rw [hstep]
          exact W.add_mem (hFW _ ih) (hHW _ (hgW j))
      refine fun w hw => map_mem_span_of_forall_mem_span E _ ?_ hw
      rintro s ⟨i, rfl⟩
      exact hEorbit (i : ℕ)
    
    have hlie := lieStable_of_stable_generators W
      (fun m hm => by rw [hEe]; exact hEW m hm)
      (fun m hm => by rw [hFf]; exact hFW m hm)
      (fun m hm => by rw [hHh]; exact hHW m hm)
    have htop : W = ⊤ := eq_top_of_lieStable_of_exists_ne_zero W hlie ⟨v0, hg0 ▸ hgW 0, hv0ne⟩
    exact finrank_le_of_span_range_fin_eq_top p g htop
  · 
    have hEinj : Function.Injective E := by
      have hEpinj : Function.Injective (E ^ p) := by
        rw [hα]
        intro a b hab
        simp only [LinearMap.smul_apply, Module.End.one_apply] at hab
        exact smul_right_injective M hα0 hab
      intro a b hab
      apply hEpinj
      have hsplit : E ^ p = E ^ (p - 1) * E := by rw [← pow_succ]; congr 1; omega
      rw [hsplit, Module.End.mul_apply, Module.End.mul_apply, hab]
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue H
    
    have hFEmaps : ∀ v ∈ H.eigenspace lam, (F * E) v ∈ H.eigenspace lam := by
      intro v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      have hcomm : H * (F * E) = (F * E) * H := by
        calc H * (F * E) = (H * F) * E := by rw [mul_assoc]
          _ = (F * H - (2 : k) • F) * E := by rw [hHF]
          _ = F * (H * E) - (2 : k) • (F * E) := by rw [sub_mul, mul_assoc, smul_mul_assoc]
          _ = F * (E * H + (2 : k) • E) - (2 : k) • (F * E) := by rw [hHE]
          _ = (F * E) * H := by rw [mul_add, mul_smul_comm, ← mul_assoc]; abel
      calc H ((F * E) v) = (H * (F * E)) v := rfl
        _ = ((F * E) * H) v := by rw [hcomm]
        _ = (F * E) (H v) := rfl
        _ = (F * E) (lam • v) := by rw [hv]
        _ = lam • (F * E) v := by rw [map_smul]
    haveI : Nontrivial (H.eigenspace lam) := (Submodule.nontrivial_iff_ne_bot).mpr hlam
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((F * E).restrict hFEmaps)
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    set v0 : M := (w : M) with hv0def
    have hv0ne : v0 ≠ 0 := by rw [hv0def, Ne, Submodule.coe_eq_zero]; exact hw.2
    have hHv0 : H v0 = lam • v0 := by
      have hmem := w.2
      rw [Module.End.mem_eigenspace_iff] at hmem
      exact hmem
    have hFEv0 : (F * E) v0 = c • v0 := by
      have h1 : ((F * E).restrict hFEmaps) w = c • w := (Module.End.mem_eigenspace_iff).mp hw.1
      have h2 := congrArg (Subtype.val) h1
      simpa [LinearMap.restrict_apply, hv0def, Submodule.coe_smul] using h2
    
    have hEFv0 : E (F v0) = (c + lam) • v0 := by
      have hEF' : E * F = F * E + H := by rw [← hEF]; abel
      have he : E (F v0) = (E * F) v0 := rfl
      rw [he, hEF', LinearMap.add_apply, hFEv0, hHv0, ← add_smul]
    
    have hFv0 : F v0 = (c + lam) • α⁻¹ • (E ^ (p - 1)) v0 := by
      apply hEinj
      rw [hEFv0, map_smul, map_smul]
      have hEp : E ((E ^ (p - 1)) v0) = α • v0 := by
        have hmul : E * E ^ (p - 1) = E ^ p := by rw [← pow_succ']; congr 1; omega
        rw [← Module.End.mul_apply, hmul, hα, LinearMap.smul_apply, Module.End.one_apply]
      rw [hEp, smul_smul α⁻¹ α v0, inv_mul_cancel₀ hα0, one_smul]
    
    set g : ℕ → M := fun j => (E ^ j) v0 with hgdef
    set W : Submodule k M := Submodule.span k (Set.range (fun i : Fin p => g (i : ℕ))) with hWdef
    have hg0 : g 0 = v0 := by simp [hgdef]
    have hmemgen : ∀ j : ℕ, j < p → g j ∈ W := fun j hj =>
      Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    
    have hEW : ∀ w ∈ W, E w ∈ W := by
      refine fun w hw => map_mem_span_of_forall_mem_span E _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hEg : E (g (i : ℕ)) = g ((i : ℕ) + 1) := by
        simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
      rw [hEg]
      by_cases hip : (i : ℕ) + 1 < p
      · exact hmemgen _ hip
      · have hip1 : (i : ℕ) + 1 = p := by omega
        have hval : g ((i : ℕ) + 1) = α • v0 := by
          simp only [hgdef, hip1, hα, LinearMap.smul_apply, Module.End.one_apply]
        rw [hval]
        exact W.smul_mem α (hg0 ▸ hmemgen 0 (by omega))
    have hgW : ∀ j, g j ∈ W := by
      intro j
      induction j with
      | zero => exact hg0 ▸ hmemgen 0 (by omega)
      | succ j ih =>
        have hEg : g (j + 1) = E (g j) := by
          simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
        rw [hEg]; exact hEW _ ih
    
    have hHW : ∀ w ∈ W, H w ∈ W := by
      refine fun w hw => map_mem_span_of_forall_mem_span H _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hval : H (g (i : ℕ)) = lam • g (i : ℕ) + ((2 * (i : ℕ) : ℕ) : k) • g (i : ℕ) := by
        simp only [hgdef]
        rw [← Module.End.mul_apply, hHEpow (i : ℕ)]
        simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, hHv0, map_smul]
      rw [hval]
      exact W.add_mem (W.smul_mem _ (hmemgen _ i.isLt)) (W.smul_mem _ (hmemgen _ i.isLt))
    
    have hFW : ∀ w ∈ W, F w ∈ W := by
      have hForbit : ∀ j : ℕ, F (g j) ∈ W := by
        intro j
        induction j with
        | zero =>
          rw [hg0, hFv0]
          have hEp1 : (E ^ (p - 1)) v0 = g (p - 1) := by simp only [hgdef]
          rw [hEp1, smul_smul]
          exact W.smul_mem _ (hmemgen (p - 1) (by omega))
        | succ j ih =>
          have hFE' : F * E = E * F - H := by rw [← hEF]; abel
          have hstep : F (g (j + 1)) = E (F (g j)) - H (g j) := by
            have hEg : g (j + 1) = E (g j) := by
              simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
            rw [hEg, ← Module.End.mul_apply, hFE']
            simp only [LinearMap.sub_apply, Module.End.mul_apply]
          rw [hstep]
          exact W.sub_mem (hEW _ ih) (hHW _ (hgW j))
      refine fun w hw => map_mem_span_of_forall_mem_span F _ ?_ hw
      rintro s ⟨i, rfl⟩
      exact hForbit (i : ℕ)
    
    have hlie := lieStable_of_stable_generators W
      (fun m hm => by rw [hEe]; exact hEW m hm)
      (fun m hm => by rw [hFf]; exact hFW m hm)
      (fun m hm => by rw [hHh]; exact hHW m hm)
    have htop : W = ⊤ := eq_top_of_lieStable_of_exists_ne_zero W hlie ⟨v0, hg0 ▸ hgW 0, hv0ne⟩
    exact finrank_le_of_span_range_fin_eq_top p g htop

end DimensionBound


/-- Over an algebraically closed field of prime characteristic greater than two, not every finite-dimensional irreducible module has finrank strictly below the characteristic. -/
theorem not_forall_finrank_lt_characteristic [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hp : 2 < p) :
    ¬ ∀ (M : Type u) [AddCommGroup M] [Module k M] [LieRingModule (twoByTwoMatrixLieSubalgebra k) M]
        [LieModule k (twoByTwoMatrixLieSubalgebra k) M] [FiniteDimensional k M] [LieModule.IsIrreducible k (twoByTwoMatrixLieSubalgebra k) M],
        Module.finrank k M < p := by
  intro H
  haveI : NeZero p := ⟨by omega⟩
  haveI : FiniteDimensional k (Fin p → k) := inferInstance
  haveI := isIrreducible_finFunction_of_le_characteristic k p hp p le_rfl
  have hlt := H (Fin p → k)
  rw [finrank_finFunction] at hlt
  exact absurd hlt (lt_irrefl p)

end RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations

attribute [source_ref "Chapter2/Problem2.16.4" (role := supporting)]
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.finrank_finFunction
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.finrank_le_characteristic
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.isIrreducible_finFunction_of_le_characteristic
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.not_forall_finrank_lt_characteristic


attribute [nolint defsWithUnderscore]
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightEnd
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingEnd
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringEnd
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.finFunctionRepresentation
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.lieRingModule_finFunction
  RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.coordinateVector
