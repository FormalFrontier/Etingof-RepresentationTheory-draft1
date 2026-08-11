import Mathlib

/-!
# Base change distributes over a Wedderburn product of matrix algebras

This file proves that scalar extension along a field extension `K ⊇ k` commutes with a finite
product of matrix algebras over division rings: if a `k`-algebra `A` is Wedderburn-isomorphic to
`∏ᵢ Matrix (Fin (d i)) (Fin (d i)) (D i)`, then

  `K ⊗[k] A ≃ₐ[K] ∏ᵢ Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i)`.

This is one of two reusable, self-contained lemmas used by the semisimple base-change result
`Etingof.natCard_simpleModuleClasses_le_baseChange_of_isSemisimpleRing`
(`Exercise4_2_3_SemisimpleBaseChange.lean`), itself a separability-free ingredient of the
field-general base-change monotonicity `#(simple k[G]) ≤ #(simple K[G])`.

The statement is phrased purely in terms of Mathlib types, so it stands on its own.

## Main result

* `Etingof.nonempty_baseChange_pi_matrix_algEquiv`: base change distributes over `∏ Matrix (D i)`.

## Construction

The isomorphism composes three standard base-change equivalences:

1. `Algebra.TensorProduct.congr (AlgEquiv.refl K) e` base-changes `e` along `k → K`;
2. `Algebra.TensorProduct.piRight` moves `K ⊗[k] -` inside the finite product;
3. `matrixBaseChange` (a helper here) commutes `K ⊗[k] -` past each `Matrix (D i)`, built from
   `matrixEquivTensor`, `Algebra.TensorProduct.assoc`, and a `k`-to-`K` linearity upgrade of the
   matrix-tensor identification.
-/

open scoped TensorProduct

universe u

namespace Etingof

noncomputable section

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- Upgrade a `k`-algebra equivalence that is also `K`-linear to a `K`-algebra equivalence.
The ring-equivalence data is scalar-independent; only the `K`-scalar compatibility `commutes'`
requires the extra `K`-linearity hypothesis `h`. -/
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

/-- Base change commutes with matrices: `K ⊗[k] Matrix n n D ≃ₐ[K] Matrix n n (K ⊗[k] D)`. -/
private def matrixBaseChange (n : ℕ) (D : Type u) [Ring D] [Algebra k D] :
    K ⊗[k] Matrix (Fin n) (Fin n) D ≃ₐ[K] Matrix (Fin n) (Fin n) (K ⊗[k] D) :=
  -- `K ⊗[k] Matrix n n D  ≃  K ⊗[k] (D ⊗[k] Matrix n n k)`
  let c1 : K ⊗[k] Matrix (Fin n) (Fin n) D ≃ₐ[K]
      K ⊗[k] (D ⊗[k] Matrix (Fin n) (Fin n) k) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K)) (matrixEquivTensor (Fin n) k D)
  -- reassociate, keeping `K` on the left: `≃ (K ⊗[k] D) ⊗[k] Matrix n n k`
  let c2 : K ⊗[k] (D ⊗[k] Matrix (Fin n) (Fin n) k) ≃ₐ[K]
      (K ⊗[k] D) ⊗[k] Matrix (Fin n) (Fin n) k :=
    (Algebra.TensorProduct.assoc k k K K D (Matrix (Fin n) (Fin n) k)).symm
  -- `(K ⊗[k] D) ⊗[k] Matrix n n k ≃ Matrix n n (K ⊗[k] D)`: `k`→`K` upgrade of `matrixEquivTensor`
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

/-- Scalar extension along a field extension `K ⊇ k` commutes with a Wedderburn product of matrix
algebras over division rings: a `k`-algebra iso `A ≃ₐ[k] ∏ᵢ Matrix (D i)` base-changes to a
`K`-algebra iso `K ⊗[k] A ≃ₐ[K] ∏ᵢ Matrix (K ⊗[k] D i)`. -/
theorem nonempty_baseChange_pi_matrix_algEquiv
    {n : ℕ} (D : Fin n → Type u) [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)]
    (d : Fin n → ℕ) {A : Type u} [Ring A] [Algebra k A]
    (e : A ≃ₐ[k] (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))) :
    Nonempty (K ⊗[k] A ≃ₐ[K] (∀ i, Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i))) := by
  refine ⟨?_⟩
  -- base-change `e` along `k → K`
  let s1 : K ⊗[k] A ≃ₐ[K] K ⊗[k] (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K)) e
  -- distribute `K ⊗[k] -` over the finite product
  let s2 : K ⊗[k] (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) ≃ₐ[K]
      (∀ i, K ⊗[k] Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
    Algebra.TensorProduct.piRight k K K (fun i => Matrix (Fin (d i)) (Fin (d i)) (D i))
  -- commute `K ⊗[k] -` past each matrix factor
  let s3 : (∀ i, K ⊗[k] Matrix (Fin (d i)) (Fin (d i)) (D i)) ≃ₐ[K]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i)) :=
    AlgEquiv.piCongrRight (fun i => matrixBaseChange k K (d i) (D i))
  exact s1.trans (s2.trans s3)

end

end Etingof
