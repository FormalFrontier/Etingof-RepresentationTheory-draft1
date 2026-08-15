/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LinearAlgebra.NilpotentOperators
import RepresentationTheory.LieAlgebra.TensorProductDecomposition
import RepresentationTheory.Alignment.Attribute

open scoped TensorProduct DirectSum

namespace RepresentationTheory.LieModule.TensorProductDecomposition

/-- An endomorphism of a tensor product of two finite-dimensional complex function spaces. -/
noncomputable def tensorProductEndomorphism (lam mu : ℕ) :
    Module.End ℂ ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) :=
  TensorProduct.map (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement (lam + 1)) LinearMap.id
    + TensorProduct.map LinearMap.id (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement (mu + 1))

/-- Computes the tensor-product endomorphism on a pure tensor as a sum of two pure tensors. -/
theorem tensorProductEndomorphism_apply_tmul (lam mu : ℕ) (a : Fin (lam + 1) → ℂ)
    (b : Fin (mu + 1) → ℂ) :
    tensorProductEndomorphism lam mu (a ⊗ₜ[ℂ] b)
      = _root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement (lam + 1) a ⊗ₜ[ℂ] b + a ⊗ₜ[ℂ] _root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement (mu + 1) b := by
  simp only [tensorProductEndomorphism, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_coe,
    id_eq]

/-- An endomorphism of the displayed direct sum of finite-dimensional complex vector spaces. -/
noncomputable def directSumEndomorphism (lam mu : ℕ) :
    Module.End ℂ (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) :=
  DirectSum.toModule ℂ _ _
    (fun k => (DirectSum.lof ℂ _ _ k).comp (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement (lam + mu - 2 * (k : ℕ) + 1)))

/-- Computes the direct-sum endomorphism on an element placed in one summand. -/
theorem directSumEndomorphism_apply_lof (lam mu : ℕ) (k : Fin (min lam mu + 1))
    (w : Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ) :
    directSumEndomorphism lam mu (DirectSum.lof ℂ _ _ k w)
      = DirectSum.lof ℂ _ _ k (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement (lam + mu - 2 * (k : ℕ) + 1) w) := by
  rw [directSumEndomorphism, DirectSum.toModule_lof]
  rfl

/-- A linear equivalence from the displayed direct sum to a tensor product of complex vector spaces. -/
noncomputable def tensorProductDecompositionEquiv (lam mu : ℕ) :
    (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) ≃ₗ[ℂ]
      (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) :=
  DirectSum.congrLinearEquiv (fun k => _root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 (lam + mu - 2 * (k : ℕ) + 1))

/-- Computes the decomposition equivalence on an element embedded from a single direct summand. -/
theorem tensorProductDecompositionEquiv_apply_lof (lam mu : ℕ) (k : Fin (min lam mu + 1))
    (w : Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ) :
    tensorProductDecompositionEquiv lam mu (DirectSum.lof ℂ _ _ k w)
      = DirectSum.lof ℂ _ _ k (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 (lam + mu - 2 * (k : ℕ) + 1) w) := by
  rw [tensorProductDecompositionEquiv, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  rfl

/-- Under the coordinate equivalence, the bracket action is the specified endomorphism. -/
theorem coordinateEquiv_bracket_eq (n : ℕ) (v : Fin n → ℂ) :
    _root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 n ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, v⁆ = _root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement n (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 n v) := by
  have h : (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 n).conjAlgEquiv ℂ (_root_.RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation n _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement) = _root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement n := by
    rw [← _root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.map_apply_aux11]; exact _root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.map_apply_aux12 n
  have h2 := LinearMap.congr_fun h (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 n v)
  rw [LinearEquiv.conjAlgEquiv_apply] at h2
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2
  rw [_root_.RepresentationTheory.LieAlgebra.Sl2Representations.bracket_eq_representation_apply]
  exact h2

/-- The tensor-product decomposition equivalence commutes with the displayed endomorphisms. -/
theorem tensorProductDecompositionEquiv_commutes (lam mu : ℕ) :
    (TensorProduct.congr (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 (lam + 1)) (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 (mu + 1))).toLinearMap
        ∘ₗ LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement
      = tensorProductEndomorphism lam mu ∘ₗ
          (TensorProduct.congr (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 (lam + 1)) (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 (mu + 1))).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, LinearEquiv.coe_coe]
  rw [_root_.RepresentationTheory.LieAlgebra.TensorProductDecomposition.bracket_eq_aux12, map_add, TensorProduct.congr_tmul, TensorProduct.congr_tmul,
    TensorProduct.congr_tmul, tensorProductEndomorphism_apply_tmul, coordinateEquiv_bracket_eq, coordinateEquiv_bracket_eq]

/-- The decomposition equivalence intertwines the two displayed linear actions. -/
theorem tensorProductDecompositionEquiv_intertwines (lam mu : ℕ) :
    (tensorProductDecompositionEquiv lam mu).toLinearMap ∘ₗ
        LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra
          (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement
      = directSumEndomorphism lam mu ∘ₗ (tensorProductDecompositionEquiv lam mu).toLinearMap := by
  apply DirectSum.linearMap_ext
  intro k
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, LinearEquiv.coe_coe]
  rw [_root_.RepresentationTheory.LieAlgebra.TensorProductDecomposition.bracket_eq_aux6, tensorProductDecompositionEquiv_apply_lof, tensorProductDecompositionEquiv_apply_lof, directSumEndomorphism_apply_lof, coordinateEquiv_bracket_eq]

/-- There exists a linear equivalence intertwining the tensor-product endomorphism with the displayed direct-sum endomorphism. -/
@[source_ref "Chapter2/Problem2.15.1/Derived16" (role := supporting)]
theorem exists_tensorProductEndomorphismEquiv (lam mu : ℕ) :
    ∃ Θ : ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) ≃ₗ[ℂ]
        (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)),
      ∀ z, Θ (tensorProductEndomorphism lam mu z) = directSumEndomorphism lam mu (Θ z) := by
  obtain ⟨Φ⟩ := _root_.RepresentationTheory.LieAlgebra.TensorProductDecomposition.nonempty_lieModuleEquiv_directSum lam mu
  set T := TensorProduct.congr (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 (lam + 1)) (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 (mu + 1)) with hT
  have hΦ : ∀ z, Φ ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, z⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, Φ z⁆ := fun z => Φ.toLieModuleHom.map_lie _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement z
  refine ⟨T.symm ≪≫ₗ Φ.toLinearEquiv ≪≫ₗ tensorProductDecompositionEquiv lam mu, fun z => ?_⟩
  have e1 : ⁅_root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement, T.symm z⁆ = T.symm (tensorProductEndomorphism lam mu z) := by
    have h := LinearMap.congr_fun (tensorProductDecompositionEquiv_commutes lam mu) (T.symm z)
    simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, ← hT] at h
    rw [← h, LinearEquiv.symm_apply_apply]
  have e2 := LinearMap.congr_fun (tensorProductDecompositionEquiv_intertwines lam mu) (Φ (T.symm z))
  simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, LinearEquiv.coe_coe] at e2
  simp only [LinearEquiv.trans_apply, LieModuleEquiv.coe_toLinearEquiv]
  rw [← e1, hΦ (T.symm z), e2]

end RepresentationTheory.LieModule.TensorProductDecomposition
