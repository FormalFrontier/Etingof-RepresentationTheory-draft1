/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib

/-! # Tensor products and finite products of matrix algebras -/

open scoped TensorProduct

universe u

namespace RepresentationTheory.Algebra.TensorProduct.MatrixProductEquivalence

noncomputable section

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

private def upgradeToK {X Y : Type u} [Semiring X] [Semiring Y]
    [Algebra k X] [Algebra k Y] [Algebra K X] [Algebra K Y]
    [IsScalarTower k K X] [IsScalarTower k K Y]
    (f : X ≃ₐ[k] Y) (h : ∀ (c : K) (x : X), f (c • x) = c • f x) : X ≃ₐ[K] Y :=
  { f with
    commutes' := fun r => by
      have hh := h r 1
      rw [map_one] at hh
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      exact hh }

private def matrixBaseChange (n : ℕ) (D : Type u) [Ring D] [Algebra k D] :
    K ⊗[k] Matrix (Fin n) (Fin n) D ≃ₐ[K] Matrix (Fin n) (Fin n) (K ⊗[k] D) :=
  let c1 : K ⊗[k] Matrix (Fin n) (Fin n) D ≃ₐ[K]
      K ⊗[k] (D ⊗[k] Matrix (Fin n) (Fin n) k) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K)) (matrixEquivTensor (Fin n) k D)
  let c2 : K ⊗[k] (D ⊗[k] Matrix (Fin n) (Fin n) k) ≃ₐ[K]
      (K ⊗[k] D) ⊗[k] Matrix (Fin n) (Fin n) k :=
    (Algebra.TensorProduct.assoc k k K K D (Matrix (Fin n) (Fin n) k)).symm
  let c3 : (K ⊗[k] D) ⊗[k] Matrix (Fin n) (Fin n) k ≃ₐ[K]
      Matrix (Fin n) (Fin n) (K ⊗[k] D) :=
    upgradeToK k K (matrixEquivTensor (Fin n) k (K ⊗[k] D)).symm (fun c x => by
      induction x with
      | zero => simp
      | add a b ha hb => simp [ha, hb]
      | tmul b M =>
        rw [TensorProduct.smul_tmul']
        simp only [matrixEquivTensor_apply_symm]
        exact smul_assoc c b _)
  c1.trans (c2.trans c3)

/-- An algebra equivalence with a finite product of matrix algebras induces a nonempty
scalar-extended algebra equivalence with the corresponding product. -/
theorem nonempty_tensorProduct_algEquiv_pi_matrix
    {n : ℕ} (D : Fin n → Type u) [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)]
    (d : Fin n → ℕ) {A : Type u} [Ring A] [Algebra k A]
    (e : A ≃ₐ[k] (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))) :
    Nonempty (K ⊗[k] A ≃ₐ[K] (∀ i, Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i))) := by
  refine ⟨?_⟩
  let s1 : K ⊗[k] A ≃ₐ[K] K ⊗[k] (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K)) e
  let s2 : K ⊗[k] (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) ≃ₐ[K]
      (∀ i, K ⊗[k] Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
    Algebra.TensorProduct.piRight k K K (fun i => Matrix (Fin (d i)) (Fin (d i)) (D i))
  let s3 : (∀ i, K ⊗[k] Matrix (Fin (d i)) (Fin (d i)) (D i)) ≃ₐ[K]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i)) :=
    AlgEquiv.piCongrRight (fun i => matrixBaseChange k K (d i) (D i))
  exact s1.trans (s2.trans s3)

end

end RepresentationTheory.Algebra.TensorProduct.MatrixProductEquivalence
