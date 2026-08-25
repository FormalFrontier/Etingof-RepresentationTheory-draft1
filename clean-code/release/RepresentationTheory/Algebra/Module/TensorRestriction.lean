/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.Module.TensorProductCoordinates
import RepresentationTheory.Algebra.Module.EquivalenceTransfers
import RepresentationTheory.Alignment.Attribute

/-! # Tensor restriction -/

open scoped TensorProduct

namespace RepresentationTheory.Algebra.Module.TensorRestriction

variable {K A V W L : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]
  [Field L] [Algebra K L]

/-- A tensor-product-algebra linear equivalence induces an A-linear equivalence of the same tensor-product modules. -/
noncomputable def restrictScalarsLinearEquiv
    (e : (L ⊗[K] V) ≃ₗ[L ⊗[K] A] (L ⊗[K] W)) :
    (L ⊗[K] V) ≃ₗ[A] (L ⊗[K] W) where
  toFun := e
  map_add' := map_add e
  map_smul' a x := by
    simp only [RingHom.id_apply]
    rw [RepresentationTheory.Algebra.Module.TensorProductCoordinates.smul_eq_includeRight_smul
      (a := a) (x := x),
      RepresentationTheory.Algebra.Module.TensorProductCoordinates.smul_eq_includeRight_smul
        (a := a) (x := e x)]
    exact e.map_smul _ x
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- The induced A-linear equivalence has the same value as the original tensor-product-algebra linear equivalence. -/
@[simp]
theorem restrictScalarsLinearEquiv_apply
    (e : (L ⊗[K] V) ≃ₗ[L ⊗[K] A] (L ⊗[K] W)) (x : L ⊗[K] V) :
    restrictScalarsLinearEquiv e x = e x := rfl

/-- An equivalence after tensor extension yields an equivalence before tensor extension under finite-dimensionality hypotheses. -/
@[source_ref "Chapter3/Problem3.8.4" (role := supporting)]
theorem exists_equiv_of_tensorEquiv [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K L]
    (h : Nonempty ((L ⊗[K] V) ≃ₗ[L ⊗[K] A] (L ⊗[K] W))) :
    Nonempty (V ≃ₗ[A] W) := by
  obtain ⟨e⟩ := h
  obtain ⟨fV⟩ :=
    RepresentationTheory.Algebra.Module.TensorProductCoordinates.nonempty_linearEquiv_fin_fun
      (K := K) (A := A) (V := V) (L := L)
  obtain ⟨fW⟩ :=
    RepresentationTheory.Algebra.Module.TensorProductCoordinates.nonempty_linearEquiv_fin_fun
      (K := K) (A := A) (V := W) (L := L)
  have hpow :
      Nonempty ((Fin (Module.finrank K L) → V) ≃ₗ[A] (Fin (Module.finrank K L) → W)) :=
    ⟨fV.symm ≪≫ₗ restrictScalarsLinearEquiv e ≪≫ₗ fW⟩
  exact
    RepresentationTheory.Algebra.Module.EquivalenceTransfers.exists_equiv_of_fin_fun_equiv
      K A V W Module.finrank_pos hpow

/-- A tensor-product-algebra linear map induces an A-linear map of the same tensor-product modules. -/
noncomputable def restrictScalarsLinearMap
    (f : (L ⊗[K] V) →ₗ[L ⊗[K] A] (L ⊗[K] W)) :
    (L ⊗[K] V) →ₗ[A] (L ⊗[K] W) where
  toFun := f
  map_add' := map_add f
  map_smul' a x := by
    simp only [RingHom.id_apply]
    rw [RepresentationTheory.Algebra.Module.TensorProductCoordinates.smul_eq_includeRight_smul
      (a := a) (x := x),
      RepresentationTheory.Algebra.Module.TensorProductCoordinates.smul_eq_includeRight_smul
        (a := a) (x := f x)]
    exact f.map_smul _ x

/-- The induced A-linear map has the same value as the original tensor-product-algebra linear map. -/
@[simp]
theorem restrictScalarsLinearMap_apply
    (f : (L ⊗[K] V) →ₗ[L ⊗[K] A] (L ⊗[K] W)) (x : L ⊗[K] V) :
    restrictScalarsLinearMap f x = f x := rfl

/-- A retraction after tensor extension yields a retraction before tensor extension under finite-dimensionality hypotheses. -/
@[source_ref "Chapter3/Problem3.8.4/Derived6" (role := supporting)]
theorem exists_retract_of_tensorRetract
    [FiniteDimensional K V] [FiniteDimensional K W] [FiniteDimensional K L]
    (h : ∃ (i : (L ⊗[K] V) →ₗ[L ⊗[K] A] (L ⊗[K] W))
           (p : (L ⊗[K] W) →ₗ[L ⊗[K] A] (L ⊗[K] V)), p.comp i = LinearMap.id) :
    ∃ (i : V →ₗ[A] W) (p : W →ₗ[A] V), p.comp i = LinearMap.id := by
  obtain ⟨i, p, hpi⟩ := h
  obtain ⟨fV⟩ :=
    RepresentationTheory.Algebra.Module.TensorProductCoordinates.nonempty_linearEquiv_fin_fun
      (K := K) (A := A) (V := V) (L := L)
  obtain ⟨fW⟩ :=
    RepresentationTheory.Algebra.Module.TensorProductCoordinates.nonempty_linearEquiv_fin_fun
      (K := K) (A := A) (V := W) (L := L)
  refine RepresentationTheory.Algebra.Module.EquivalenceTransfers.exists_split_of_exists_split
    K A V W (n := Module.finrank K L) Module.finrank_pos
    ⟨(fW : (L ⊗[K] W) →ₗ[A] _).comp ((restrictScalarsLinearMap i).comp
        (fV.symm : (Fin (Module.finrank K L) → V) →ₗ[A] _)),
     (fV : (L ⊗[K] V) →ₗ[A] _).comp ((restrictScalarsLinearMap p).comp
        (fW.symm : (Fin (Module.finrank K L) → W) →ₗ[A] _)), ?_⟩
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq,
    LinearEquiv.symm_apply_apply, restrictScalarsLinearMap_apply]
  have : p (i (fV.symm x)) = fV.symm x := LinearMap.congr_fun hpi (fV.symm x)
  rw [this, LinearEquiv.apply_symm_apply]

end RepresentationTheory.Algebra.Module.TensorRestriction
