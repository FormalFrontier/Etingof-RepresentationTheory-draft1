/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.LinearAlgebra.TensorProduct.ModuleBaseChange
import RepresentationTheory.Alignment.Attribute

/-! # Descent to finitely generated subalgebras -/


































































open scoped TensorProduct

namespace RepresentationTheory.Algebra.Module.FinitelyGeneratedSubalgebraDescent

open RepresentationTheory.LinearAlgebra.TensorProduct.ModuleBaseChange

variable {K A V W L : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]
  [Field L] [Algebra K L]

set_option maxHeartbeats 800000 in













/-- A tensor-product-module equivalence descends to an equivalence over a finitely generated
subalgebra. -/
@[source_ref "Chapter3/Problem3.8.4" (role := supporting)]
theorem exists_fgSubalgebra_equiv
    [FiniteDimensional K V] [FiniteDimensional K W]
    (e : (L ⊗[K] V) ≃ₗ[L ⊗[K] A] (L ⊗[K] W)) :
    ∃ R : Subalgebra K L, R.FG ∧
      Nonempty ((R ⊗[K] V) ≃ₗ[R ⊗[K] A] (R ⊗[K] W)) := by
  classical
  
  let bV := Module.finBasis K V
  let bW := Module.finBasis K W
  let BVL := bV.baseChange L
  let BWL := bW.baseChange L
  
  let c : Fin (Module.finrank K V) → Fin (Module.finrank K W) → L :=
    fun i j => BWL.repr (e (BVL i)) j
  let d : Fin (Module.finrank K W) → Fin (Module.finrank K V) → L :=
    fun j i => BVL.repr (e.symm (BWL j)) i
  have he : ∀ i, e (BVL i) = ∑ j, c i j • BWL j := fun i => (BWL.sum_repr (e (BVL i))).symm
  have he_symm : ∀ j, e.symm (BWL j) = ∑ i, d j i • BVL i :=
    fun j => (BVL.sum_repr (e.symm (BWL j))).symm
  
  let Sc : Finset L :=
    Finset.image (fun p : Fin (Module.finrank K V) × Fin (Module.finrank K W) => c p.1 p.2)
      Finset.univ
  let Sd : Finset L :=
    Finset.image (fun p : Fin (Module.finrank K W) × Fin (Module.finrank K V) => d p.1 p.2)
      Finset.univ
  let entries : Finset L := Sc ∪ Sd
  
  
  obtain ⟨RA, hFG, hc, hd⟩ :
      ∃ R : Subalgebra K L, R.FG ∧ (∀ i j, c i j ∈ R) ∧ (∀ j i, d j i ∈ R) := by
    refine ⟨Algebra.adjoin K (↑entries : Set L), Subalgebra.fg_adjoin_finset entries, ?_, ?_⟩
    · intro i j
      apply Algebra.subset_adjoin
      rw [Finset.mem_coe]
      exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    · intro j i
      apply Algebra.subset_adjoin
      rw [Finset.mem_coe]
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(j, i), Finset.mem_univ _, rfl⟩)
  let cR : Fin (Module.finrank K V) → Fin (Module.finrank K W) → ↥RA :=
    fun i j => ⟨c i j, hc i j⟩
  let dR : Fin (Module.finrank K W) → Fin (Module.finrank K V) → ↥RA :=
    fun j i => ⟨d j i, hd j i⟩
  have hcRval : ∀ i j, RA.val (cR i j) = c i j := fun _ _ => rfl
  have hdRval : ∀ j i, RA.val (dR j i) = d j i := fun _ _ => rfl
  
  let bVR := bV.baseChange (↥RA)
  let bWR := bW.baseChange (↥RA)
  have hbVR : ∀ i, bVR i = (1 : ↥RA) ⊗ₜ[K] bV i := fun i => Module.Basis.baseChange_apply _ _ _
  have hbWR : ∀ j, bWR j = (1 : ↥RA) ⊗ₜ[K] bW j := fun j => Module.Basis.baseChange_apply _ _ _
  have hBVL : ∀ i, BVL i = (1 : L) ⊗ₜ[K] bV i := fun i => Module.Basis.baseChange_apply _ _ _
  have hBWL : ∀ j, BWL j = (1 : L) ⊗ₜ[K] bW j := fun j => Module.Basis.baseChange_apply _ _ _
  let φ : (↥RA ⊗[K] V) →ₗ[↥RA] (↥RA ⊗[K] W) :=
    bVR.constr (↥RA) (fun i => ∑ j, cR i j • bWR j)
  let ψ : (↥RA ⊗[K] W) →ₗ[↥RA] (↥RA ⊗[K] V) :=
    bWR.constr (↥RA) (fun j => ∑ i, dR j i • bVR i)
  
  let incV : (↥RA ⊗[K] V) →ₗ[K] (L ⊗[K] V) := LinearMap.rTensor V RA.val.toLinearMap
  let incW : (↥RA ⊗[K] W) →ₗ[K] (L ⊗[K] W) := LinearMap.rTensor W RA.val.toLinearMap
  have hvalinj : Function.Injective (RA.val.toLinearMap) := fun a b h => Subtype.ext h
  have hincVinj : Function.Injective incV :=
    Module.Flat.rTensor_preserves_injective_linearMap RA.val.toLinearMap hvalinj
  have hincWinj : Function.Injective incW :=
    Module.Flat.rTensor_preserves_injective_linearMap RA.val.toLinearMap hvalinj
  have incV_tmul : ∀ (r : ↥RA) (v : V), incV (r ⊗ₜ[K] v) = RA.val r ⊗ₜ[K] v := fun _ _ => rfl
  have incW_tmul : ∀ (r : ↥RA) (w : W), incW (r ⊗ₜ[K] w) = RA.val r ⊗ₜ[K] w := fun _ _ => rfl
  
  have incV_smul : ∀ (r : ↥RA) (x : ↥RA ⊗[K] V), incV (r • x) = RA.val r • incV x := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul s v =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, incV_tmul, incV_tmul,
          TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add p q hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]
  have incW_smul : ∀ (r : ↥RA) (x : ↥RA ⊗[K] W), incW (r • x) = RA.val r • incW x := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul s w =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, incW_tmul, incW_tmul,
          TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add p q hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]
  
  have incV_Aequiv : ∀ (a : A) (x : ↥RA ⊗[K] V),
      incV ((1 ⊗ₜ[K] a : ↥RA ⊗[K] A) • x) = (1 ⊗ₜ[K] a : L ⊗[K] A) • incV x := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul s v =>
        rw [tmul_one_smul_tmul]
        simp only [incV_tmul, tmul_one_smul_tmul]
    | add p q hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]
  have incW_Aequiv : ∀ (a : A) (x : ↥RA ⊗[K] W),
      incW ((1 ⊗ₜ[K] a : ↥RA ⊗[K] A) • x) = (1 ⊗ₜ[K] a : L ⊗[K] A) • incW x := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul s w =>
        rw [tmul_one_smul_tmul]
        simp only [incW_tmul, tmul_one_smul_tmul]
    | add p q hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]
  
  have e_smulL : ∀ (l : L) (x : L ⊗[K] V), e (l • x) = l • e x := by
    intro l x
    rw [← tmul_one_smul_eq_smul (A := A) l x, e.map_smul, tmul_one_smul_eq_smul]
  have esymm_smulL : ∀ (l : L) (y : L ⊗[K] W), e.symm (l • y) = l • e.symm y := by
    intro l y
    rw [← tmul_one_smul_eq_smul (A := A) l y, e.symm.map_smul, tmul_one_smul_eq_smul]
  
  have hbasis_phi : ∀ i, incW (φ (bVR i)) = e (incV (bVR i)) := by
    intro i
    have hφ : φ (bVR i) = ∑ j, cR i j • bWR j := bVR.constr_basis (↥RA) _ i
    have hVi : incV (bVR i) = BVL i := by rw [hbVR, incV_tmul, map_one, hBVL]
    rw [hφ, map_sum, hVi, he i]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [incW_smul, hbWR, incW_tmul, map_one, hBWL, hcRval]
  have hbasis_psi : ∀ j, incV (ψ (bWR j)) = e.symm (incW (bWR j)) := by
    intro j
    have hψ : ψ (bWR j) = ∑ i, dR j i • bVR i := bWR.constr_basis (↥RA) _ j
    have hWj : incW (bWR j) = BWL j := by rw [hbWR, incW_tmul, map_one, hBWL]
    rw [hψ, map_sum, hWj, he_symm j]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [incV_smul, hbVR, incV_tmul, map_one, hBVL, hdRval]
  have int_phi : ∀ x, incW (φ x) = e (incV x) := by
    intro x
    have hL : incW (φ x) = ∑ i, RA.val (bVR.repr x i) • incW (φ (bVR i)) := by
      conv_lhs => rw [← bVR.sum_repr x, map_sum, map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, incW_smul])
    have hR : e (incV x) = ∑ i, RA.val (bVR.repr x i) • e (incV (bVR i)) := by
      conv_lhs => rw [← bVR.sum_repr x, map_sum, map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [incV_smul, e_smulL])
    rw [hL, hR]
    exact Finset.sum_congr rfl (fun i _ => by rw [hbasis_phi i])
  have int_psi : ∀ y, incV (ψ y) = e.symm (incW y) := by
    intro y
    have hL : incV (ψ y) = ∑ j, RA.val (bWR.repr y j) • incV (ψ (bWR j)) := by
      conv_lhs => rw [← bWR.sum_repr y, map_sum, map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [map_smul, incV_smul])
    have hR : e.symm (incW y) = ∑ j, RA.val (bWR.repr y j) • e.symm (incW (bWR j)) := by
      conv_lhs => rw [← bWR.sum_repr y, map_sum, map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [incW_smul, esymm_smulL])
    rw [hL, hR]
    exact Finset.sum_congr rfl (fun j _ => by rw [hbasis_psi j])
  
  have psi_phi : ∀ x, ψ (φ x) = x := by
    intro x
    apply hincVinj
    rw [int_psi, int_phi, e.symm_apply_apply]
  have phi_psi : ∀ y, φ (ψ y) = y := by
    intro y
    apply hincWinj
    rw [int_phi, int_psi, e.apply_symm_apply]
  
  have phi_Aequiv : ∀ (a : A) (x : ↥RA ⊗[K] V),
      φ ((1 ⊗ₜ[K] a : ↥RA ⊗[K] A) • x) = (1 ⊗ₜ[K] a : ↥RA ⊗[K] A) • φ x := by
    intro a x
    apply hincWinj
    rw [int_phi, incV_Aequiv, e.map_smul, incW_Aequiv, int_phi]
  
  refine ⟨RA, hFG, ⟨?_⟩⟩
  exact
    { toFun := φ
      invFun := ψ
      left_inv := psi_phi
      right_inv := phi_psi
      map_add' := φ.map_add
      map_smul' := by
        intro y x
        simp only [RingHom.id_apply]
        induction y using TensorProduct.induction_on with
        
        
        
        | zero => rw [zero_smul (↥RA ⊗[K] A) x, zero_smul (↥RA ⊗[K] A) (φ x), map_zero]
        | tmul t a =>
            have hmul : (t ⊗ₜ[K] a : ↥RA ⊗[K] A) = (t ⊗ₜ[K] (1 : A)) * (1 ⊗ₜ[K] a) := by
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
            rw [hmul, mul_smul, mul_smul, tmul_one_smul_eq_smul, tmul_one_smul_eq_smul,
              map_smul, phi_Aequiv]
        | add p q hp hq => rw [add_smul, add_smul, map_add, hp, hq] }

set_option maxHeartbeats 1600000 in
















/-- A tensor-product-module retraction descends to a retraction over a finitely generated
subalgebra. -/
@[source_ref "Chapter3/Problem3.8.4/Derived6" (role := supporting)]
theorem exists_fgSubalgebra_retract
    [FiniteDimensional K V] [FiniteDimensional K W]
    (i : (L ⊗[K] V) →ₗ[L ⊗[K] A] (L ⊗[K] W)) (p : (L ⊗[K] W) →ₗ[L ⊗[K] A] (L ⊗[K] V))
    (hpi : p.comp i = LinearMap.id) :
    ∃ R : Subalgebra K L, R.FG ∧
      ∃ (i' : (R ⊗[K] V) →ₗ[R ⊗[K] A] (R ⊗[K] W))
        (p' : (R ⊗[K] W) →ₗ[R ⊗[K] A] (R ⊗[K] V)), p'.comp i' = LinearMap.id := by
  classical
  
  let bV := Module.finBasis K V
  let bW := Module.finBasis K W
  let BVL := bV.baseChange L
  let BWL := bW.baseChange L
  
  let c : Fin (Module.finrank K V) → Fin (Module.finrank K W) → L :=
    fun row col => BWL.repr (i (BVL row)) col
  let d : Fin (Module.finrank K W) → Fin (Module.finrank K V) → L :=
    fun row col => BVL.repr (p (BWL row)) col
  have hi_sum : ∀ row, i (BVL row) = ∑ col, c row col • BWL col :=
    fun row => (BWL.sum_repr (i (BVL row))).symm
  have hp_sum : ∀ row, p (BWL row) = ∑ col, d row col • BVL col :=
    fun row => (BVL.sum_repr (p (BWL row))).symm
  
  let Sc : Finset L :=
    Finset.image (fun q : Fin (Module.finrank K V) × Fin (Module.finrank K W) => c q.1 q.2)
      Finset.univ
  let Sd : Finset L :=
    Finset.image (fun q : Fin (Module.finrank K W) × Fin (Module.finrank K V) => d q.1 q.2)
      Finset.univ
  let entries : Finset L := Sc ∪ Sd
  obtain ⟨RA, hFG, hc, hd⟩ :
      ∃ R : Subalgebra K L, R.FG ∧ (∀ row col, c row col ∈ R) ∧ (∀ row col, d row col ∈ R) := by
    refine ⟨Algebra.adjoin K (↑entries : Set L), Subalgebra.fg_adjoin_finset entries, ?_, ?_⟩
    · intro row col
      apply Algebra.subset_adjoin
      rw [Finset.mem_coe]
      exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(row, col), Finset.mem_univ _, rfl⟩)
    · intro row col
      apply Algebra.subset_adjoin
      rw [Finset.mem_coe]
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(row, col), Finset.mem_univ _, rfl⟩)
  let cR : Fin (Module.finrank K V) → Fin (Module.finrank K W) → ↥RA :=
    fun row col => ⟨c row col, hc row col⟩
  let dR : Fin (Module.finrank K W) → Fin (Module.finrank K V) → ↥RA :=
    fun row col => ⟨d row col, hd row col⟩
  have hcRval : ∀ row col, RA.val (cR row col) = c row col := fun _ _ => rfl
  have hdRval : ∀ row col, RA.val (dR row col) = d row col := fun _ _ => rfl
  
  let bVR := bV.baseChange (↥RA)
  let bWR := bW.baseChange (↥RA)
  have hbVR : ∀ row, bVR row = (1 : ↥RA) ⊗ₜ[K] bV row :=
    fun row => Module.Basis.baseChange_apply _ _ _
  have hbWR : ∀ col, bWR col = (1 : ↥RA) ⊗ₜ[K] bW col :=
    fun col => Module.Basis.baseChange_apply _ _ _
  have hBVL : ∀ row, BVL row = (1 : L) ⊗ₜ[K] bV row :=
    fun row => Module.Basis.baseChange_apply _ _ _
  have hBWL : ∀ col, BWL col = (1 : L) ⊗ₜ[K] bW col :=
    fun col => Module.Basis.baseChange_apply _ _ _
  let i'R : (↥RA ⊗[K] V) →ₗ[↥RA] (↥RA ⊗[K] W) :=
    bVR.constr (↥RA) (fun row => ∑ col, cR row col • bWR col)
  let p'R : (↥RA ⊗[K] W) →ₗ[↥RA] (↥RA ⊗[K] V) :=
    bWR.constr (↥RA) (fun row => ∑ col, dR row col • bVR col)
  
  let incV : (↥RA ⊗[K] V) →ₗ[K] (L ⊗[K] V) := LinearMap.rTensor V RA.val.toLinearMap
  let incW : (↥RA ⊗[K] W) →ₗ[K] (L ⊗[K] W) := LinearMap.rTensor W RA.val.toLinearMap
  have hvalinj : Function.Injective (RA.val.toLinearMap) := fun a b h => Subtype.ext h
  have hincVinj : Function.Injective incV :=
    Module.Flat.rTensor_preserves_injective_linearMap RA.val.toLinearMap hvalinj
  have hincWinj : Function.Injective incW :=
    Module.Flat.rTensor_preserves_injective_linearMap RA.val.toLinearMap hvalinj
  have incV_tmul : ∀ (r : ↥RA) (v : V), incV (r ⊗ₜ[K] v) = RA.val r ⊗ₜ[K] v := fun _ _ => rfl
  have incW_tmul : ∀ (r : ↥RA) (w : W), incW (r ⊗ₜ[K] w) = RA.val r ⊗ₜ[K] w := fun _ _ => rfl
  have incV_smul : ∀ (r : ↥RA) (x : ↥RA ⊗[K] V), incV (r • x) = RA.val r • incV x := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul s v =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, incV_tmul, incV_tmul,
          TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add pp qq hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]
  have incW_smul : ∀ (r : ↥RA) (x : ↥RA ⊗[K] W), incW (r • x) = RA.val r • incW x := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul s w =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, incW_tmul, incW_tmul,
          TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add pp qq hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]
  have incV_Aequiv : ∀ (a : A) (x : ↥RA ⊗[K] V),
      incV ((1 ⊗ₜ[K] a : ↥RA ⊗[K] A) • x) = (1 ⊗ₜ[K] a : L ⊗[K] A) • incV x := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul s v =>
        rw [tmul_one_smul_tmul]
        simp only [incV_tmul, tmul_one_smul_tmul]
    | add pp qq hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]
  have incW_Aequiv : ∀ (a : A) (x : ↥RA ⊗[K] W),
      incW ((1 ⊗ₜ[K] a : ↥RA ⊗[K] A) • x) = (1 ⊗ₜ[K] a : L ⊗[K] A) • incW x := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul s w =>
        rw [tmul_one_smul_tmul]
        simp only [incW_tmul, tmul_one_smul_tmul]
    | add pp qq hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]
  
  have i_smulL : ∀ (l : L) (x : L ⊗[K] V), i (l • x) = l • i x := by
    intro l x
    rw [← tmul_one_smul_eq_smul (A := A) l x, i.map_smul, tmul_one_smul_eq_smul]
  have p_smulL : ∀ (l : L) (y : L ⊗[K] W), p (l • y) = l • p y := by
    intro l y
    rw [← tmul_one_smul_eq_smul (A := A) l y, p.map_smul, tmul_one_smul_eq_smul]
  
  have hbasis_i : ∀ row, incW (i'R (bVR row)) = i (incV (bVR row)) := by
    intro row
    have hi' : i'R (bVR row) = ∑ col, cR row col • bWR col := bVR.constr_basis (↥RA) _ row
    have hVrow : incV (bVR row) = BVL row := by rw [hbVR, incV_tmul, map_one, hBVL]
    rw [hi', map_sum, hVrow, hi_sum row]
    refine Finset.sum_congr rfl (fun col _ => ?_)
    rw [incW_smul, hbWR, incW_tmul, map_one, hBWL, hcRval]
  have hbasis_p : ∀ row, incV (p'R (bWR row)) = p (incW (bWR row)) := by
    intro row
    have hp' : p'R (bWR row) = ∑ col, dR row col • bVR col := bWR.constr_basis (↥RA) _ row
    have hWrow : incW (bWR row) = BWL row := by rw [hbWR, incW_tmul, map_one, hBWL]
    rw [hp', map_sum, hWrow, hp_sum row]
    refine Finset.sum_congr rfl (fun col _ => ?_)
    rw [incV_smul, hbVR, incV_tmul, map_one, hBVL, hdRval]
  have int_i : ∀ x, incW (i'R x) = i (incV x) := by
    intro x
    have hL : incW (i'R x) = ∑ row, RA.val (bVR.repr x row) • incW (i'R (bVR row)) := by
      conv_lhs => rw [← bVR.sum_repr x, map_sum, map_sum]
      exact Finset.sum_congr rfl (fun row _ => by rw [map_smul, incW_smul])
    have hR : i (incV x) = ∑ row, RA.val (bVR.repr x row) • i (incV (bVR row)) := by
      conv_lhs => rw [← bVR.sum_repr x, map_sum, map_sum]
      exact Finset.sum_congr rfl (fun row _ => by rw [incV_smul, i_smulL])
    rw [hL, hR]
    exact Finset.sum_congr rfl (fun row _ => by rw [hbasis_i row])
  have int_p : ∀ y, incV (p'R y) = p (incW y) := by
    intro y
    have hL : incV (p'R y) = ∑ row, RA.val (bWR.repr y row) • incV (p'R (bWR row)) := by
      conv_lhs => rw [← bWR.sum_repr y, map_sum, map_sum]
      exact Finset.sum_congr rfl (fun row _ => by rw [map_smul, incV_smul])
    have hR : p (incW y) = ∑ row, RA.val (bWR.repr y row) • p (incW (bWR row)) := by
      conv_lhs => rw [← bWR.sum_repr y, map_sum, map_sum]
      exact Finset.sum_congr rfl (fun row _ => by rw [incW_smul, p_smulL])
    rw [hL, hR]
    exact Finset.sum_congr rfl (fun row _ => by rw [hbasis_p row])
  
  have split : ∀ x, p'R (i'R x) = x := by
    intro x
    apply hincVinj
    rw [int_p, int_i, ← LinearMap.comp_apply, hpi, LinearMap.id_coe, id_eq]
  
  have i_Aequiv : ∀ (a : A) (x : ↥RA ⊗[K] V),
      i'R ((1 ⊗ₜ[K] a : ↥RA ⊗[K] A) • x) = (1 ⊗ₜ[K] a : ↥RA ⊗[K] A) • i'R x := by
    intro a x
    apply hincWinj
    rw [int_i, incV_Aequiv, i.map_smul, incW_Aequiv, int_i]
  have p_Aequiv : ∀ (a : A) (y : ↥RA ⊗[K] W),
      p'R ((1 ⊗ₜ[K] a : ↥RA ⊗[K] A) • y) = (1 ⊗ₜ[K] a : ↥RA ⊗[K] A) • p'R y := by
    intro a y
    apply hincVinj
    rw [int_p, incW_Aequiv, p.map_smul, incV_Aequiv, int_p]
  
  let i' : (↥RA ⊗[K] V) →ₗ[↥RA ⊗[K] A] (↥RA ⊗[K] W) :=
    { toFun := i'R
      map_add' := i'R.map_add
      map_smul' := by
        intro y x
        simp only [RingHom.id_apply]
        induction y using TensorProduct.induction_on with
        | zero => rw [zero_smul (↥RA ⊗[K] A) x, zero_smul (↥RA ⊗[K] A) (i'R x), map_zero]
        | tmul t a =>
            have hmul : (t ⊗ₜ[K] a : ↥RA ⊗[K] A) = (t ⊗ₜ[K] (1 : A)) * (1 ⊗ₜ[K] a) := by
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
            rw [hmul, mul_smul, mul_smul, tmul_one_smul_eq_smul, tmul_one_smul_eq_smul, map_smul, i_Aequiv]
        | add pp qq hp hq => rw [add_smul, add_smul, map_add, hp, hq] }
  let p' : (↥RA ⊗[K] W) →ₗ[↥RA ⊗[K] A] (↥RA ⊗[K] V) :=
    { toFun := p'R
      map_add' := p'R.map_add
      map_smul' := by
        intro y x
        simp only [RingHom.id_apply]
        induction y using TensorProduct.induction_on with
        | zero => rw [zero_smul (↥RA ⊗[K] A) x, zero_smul (↥RA ⊗[K] A) (p'R x), map_zero]
        | tmul t a =>
            have hmul : (t ⊗ₜ[K] a : ↥RA ⊗[K] A) = (t ⊗ₜ[K] (1 : A)) * (1 ⊗ₜ[K] a) := by
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
            rw [hmul, mul_smul, mul_smul, tmul_one_smul_eq_smul, tmul_one_smul_eq_smul, map_smul, p_Aequiv]
        | add pp qq hp hq => rw [add_smul, add_smul, map_add, hp, hq] }
  refine ⟨RA, hFG, i', p', ?_⟩
  refine LinearMap.ext fun x => ?_
  change p'R (i'R x) = x
  exact split x

end RepresentationTheory.Algebra.Module.FinitelyGeneratedSubalgebraDescent
