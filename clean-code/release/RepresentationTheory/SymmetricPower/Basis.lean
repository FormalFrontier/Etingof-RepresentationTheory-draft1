/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib

/-!
# Symmetric Power Basis
-/

open scoped TensorProduct BigOperators
open Module

namespace RepresentationTheory.SymmetricPower.Basis.SymmetricPower.Basis

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
  {κ : Type*} {n : ℕ}

/-- The setoid on functions from `Fin n` to a label type. -/
def functionSetoid (n : ℕ) (κ : Type*) : Setoid (Fin n → κ) where
  r p q := ∃ σ : Equiv.Perm (Fin n), q = p ∘ σ
  iseqv :=
    { refl := fun p => ⟨1, by funext i; simp⟩
      symm := fun {p q} ⟨σ, h⟩ => ⟨σ⁻¹, by subst h; funext i; simp⟩
      trans := fun {p q r} ⟨σ, h⟩ ⟨τ, h'⟩ =>
        ⟨σ * τ, by subst h; subst h'; funext i; simp⟩ }

/-- The auxiliary index type parameterized by a natural number and a label type. -/
def Index (n : ℕ) (κ : Type*) : Type _ := Quotient (functionSetoid n κ)

/-- Maps a function from `Fin n` to the auxiliary index type. -/
def indexOfFunction : (Fin n → κ) → Index n κ := Quotient.mk (functionSetoid n κ)

/-- The basis of the finite pi tensor product induced by a module basis. -/
noncomputable def tensorBasis (b : Basis κ k V) :
    Basis (Fin n → κ) k (⨂[k] (_ : Fin n), V) :=
  Basis.piTensorProduct (fun _ : Fin n => b)

/-- Associates an element of a symmetric power to an auxiliary index using a module basis. -/
noncomputable def element (b : Basis κ k V) :
    Index n κ → SymmetricPower k (Fin n) V :=
  Quotient.lift (fun p => SymmetricPower.mk k (Fin n) V (tensorBasis b p))
    (by
      rintro p q ⟨σ, rfl⟩
      simp only [tensorBasis, Basis.piTensorProduct_apply]
      exact (SymmetricPower.tprod_equiv σ (fun i => b (p i))).symm)

/-- On an index obtained from a function, the associated element is the symmetric-power class of the corresponding tensor-basis element. -/
@[simp] lemma element_ofFunction (b : Basis κ k V) (p : Fin n → κ) :
    element b (indexOfFunction p) = SymmetricPower.mk k (Fin n) V (tensorBasis b p) :=
  rfl

/-- The linear map assigning finitely supported auxiliary-index coordinates to elements of the finite pi tensor product. -/
noncomputable def tensorCoordinates (b : Basis κ k V) :
    (⨂[k] (_ : Fin n), V) →ₗ[k] (Index n κ →₀ k) :=
  (Finsupp.lmapDomain k k (indexOfFunction (n := n) (κ := κ))).comp
    (tensorBasis b).repr.toLinearMap

/-- The tensor coordinate map sends a tensor-basis element to the unit singleton at its function index. -/
@[simp] lemma tensorCoordinates_tensorBasis (b : Basis κ k V) (p : Fin n → κ) :
    tensorCoordinates b (tensorBasis b p) = Finsupp.single (indexOfFunction p) 1 := by
  simp only [tensorCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.repr_self,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The tensor coordinate map is unchanged by reindexing with a permutation of `Fin n`. -/
lemma tensorCoordinates_reindex (b : Basis κ k V) (σ : Equiv.Perm (Fin n))
    (x : ⨂[k] (_ : Fin n), V) :
    tensorCoordinates b (PiTensorProduct.reindex k (fun _ : Fin n => V) σ x) =
      tensorCoordinates b x := by
  have h : (tensorCoordinates b).comp
      (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap = tensorCoordinates b := by
    apply Basis.ext (tensorBasis b)
    intro p
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hre : PiTensorProduct.reindex k (fun _ : Fin n => V) σ (tensorBasis b p)
        = tensorBasis b (fun i => p (σ.symm i)) := by
      simp only [tensorBasis, Basis.piTensorProduct_apply, PiTensorProduct.reindex_tprod]
    rw [hre, tensorCoordinates_tensorBasis, tensorCoordinates_tensorBasis]
    congr 1
    exact Quotient.sound ⟨σ, by funext i; simp⟩
  exact LinearMap.congr_fun h x

/-- The linear map assigning finitely supported auxiliary-index coordinates to elements of a symmetric power. -/
noncomputable def coordinates (b : Basis κ k V) :
    SymmetricPower k (Fin n) V →ₗ[k] (Index n κ →₀ k) where
  toFun := AddCon.lift _ (tensorCoordinates b).toAddMonoidHom (by
    refine AddCon.addConGen_le.mpr (fun a c hac => ?_)
    cases hac with
    | perm σ f =>
      have hswap : (PiTensorProduct.tprod k fun i => f (σ i))
          = PiTensorProduct.reindex k (fun _ : Fin n => V) σ⁻¹
            (PiTensorProduct.tprod k f) := by
        rw [PiTensorProduct.reindex_tprod]
        simp [Equiv.Perm.inv_def]
      change tensorCoordinates b (PiTensorProduct.tprod k f)
        = tensorCoordinates b (PiTensorProduct.tprod k fun i => f (σ i))
      rw [hswap, tensorCoordinates_reindex])
  map_add' := fun x y => by
    refine AddCon.induction_on₂ x y (fun a c => ?_)
    change tensorCoordinates b (a + c) = tensorCoordinates b a + tensorCoordinates b c
    rw [map_add]
  map_smul' := fun r x => by
    refine AddCon.induction_on x (fun a => ?_)
    change tensorCoordinates b (r • a) = r • tensorCoordinates b a
    rw [map_smul]

/-- Taking coordinates after forming a symmetric-power class agrees with the tensor coordinate map. -/
@[simp] lemma coordinates_mk (b : Basis κ k V) (x : ⨂[k] (_ : Fin n), V) :
    coordinates b (SymmetricPower.mk k (Fin n) V x) = tensorCoordinates b x :=
  rfl

/-- The linear map from finitely supported coefficient functions on the auxiliary indices to the symmetric power determined by a module basis. -/
noncomputable def elementLinearMap (b : Basis κ k V) :
    (Index n κ →₀ k) →ₗ[k] SymmetricPower k (Fin n) V :=
  Finsupp.linearCombination k (element b)

/-- Evaluating the element linear map on a singleton coefficient function scales the associated element. -/
@[simp] lemma elementLinearMap_single (b : Basis κ k V) (m : Index n κ) (r : k) :
    elementLinearMap b (Finsupp.single m r) = r • element b m := by
  simp only [elementLinearMap, Finsupp.linearCombination_single]

/-- The linear equivalence between a symmetric power and finitely supported coordinate functions indexed by the auxiliary type. -/
noncomputable def coordinateEquiv (b : Basis κ k V) :
    SymmetricPower k (Fin n) V ≃ₗ[k] (Index n κ →₀ k) :=
  LinearEquiv.ofLinear (coordinates b) (elementLinearMap b)
    (by
      apply Basis.ext (Finsupp.basisSingleOne)
      intro m
      refine Quotient.inductionOn m (fun p => ?_)
      simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, LinearMap.id_apply,
        elementLinearMap_single, one_smul]
      exact tensorCoordinates_tensorBasis b p)
    (by
      have key : (elementLinearMap b).comp (tensorCoordinates b) =
          SymmetricPower.mk k (Fin n) V := by
        apply Basis.ext (tensorBasis b)
        intro p
        rw [LinearMap.comp_apply, tensorCoordinates_tensorBasis, elementLinearMap_single, one_smul]
        rfl
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := (LinearMap.range_eq_top.mp (SymmetricPower.range_mk k (Fin n) V)) y
      rw [LinearMap.comp_apply, LinearMap.id_apply, coordinates_mk]
      exact LinearMap.congr_fun key x)

/-- The inverse coordinate equivalence sends the unit singleton at an index to its associated symmetric-power element. -/
@[simp] lemma coordinateEquiv_symm_single (b : Basis κ k V) (m : Index n κ) :
    (coordinateEquiv b).symm (Finsupp.single m 1) = element b m := by
  rw [coordinateEquiv, LinearEquiv.ofLinear_symm_apply, elementLinearMap_single, one_smul]

/-- The module basis of the symmetric power indexed by the auxiliary index type. -/
noncomputable def basis (b : Basis κ k V) :
    Basis (Index n κ) k (SymmetricPower k (Fin n) V) :=
  Basis.ofRepr (coordinateEquiv b)

/-- The symmetric-power basis evaluates at an index as the associated element. -/
@[simp] lemma basis_apply (b : Basis κ k V) (m : Index n κ) :
    basis b m = element b m := by
  simp only [basis, Basis.coe_ofRepr, coordinateEquiv_symm_single]

/-- At an index arising from a function, the symmetric-power basis is the class of the corresponding tensor-basis element. -/
lemma basis_ofFunction (b : Basis κ k V) (p : Fin n → κ) :
    basis b (indexOfFunction p) = SymmetricPower.mk k (Fin n) V (tensorBasis b p) := by
  rw [basis_apply]
  rfl

end RepresentationTheory.SymmetricPower.Basis.SymmetricPower.Basis
