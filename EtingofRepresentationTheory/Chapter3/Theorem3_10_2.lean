import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Tower

/-!
# Theorem 3.10.2: Irreducible Representations of Tensor Products of Algebras

(i) Let V be an irreducible finite dimensional representation of A and let W be an
    irreducible finite dimensional representation of B. Then V ⊗ W is an irreducible
    representation of A ⊗ B.

(ii) Any irreducible finite dimensional representation M of A ⊗ B has the form (i) for
     unique V and W.

The (A ⊗_k B)-module structure on V ⊗_k W is given by (a ⊗ b) • (v ⊗ w) = (a • v) ⊗ (b • w).
Irreducibility is stated as: the only k-submodules of V ⊗ W invariant under all such
actions are {0} and the whole space.
-/

open TensorProduct in
/-- The tensor product of irreducible representations is irreducible over the tensor
product of algebras: the only k-submodules of V ⊗ W closed under the action
(a ⊗ b) • (v ⊗ w) = (a • v) ⊗ (b • w) for all a ∈ A, b ∈ B are {0} and V ⊗ W.
Etingof Theorem 3.10.2(i). -/
theorem Etingof.tensor_product_irreducible (k : Type*) (A B V W : Type*)
    [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Ring B] [Algebra k B] [FiniteDimensional k B]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule A V] [IsSimpleModule B W] :
    ∀ (U : Submodule k (V ⊗[k] W)),
      (∀ (a : A) (b : B) (x : V ⊗[k] W), x ∈ U →
        TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] Module.End k V) a)
          ((Algebra.lsmul k k W : B →ₐ[k] Module.End k W) b) x ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
  sorry

open TensorProduct in
/-- Every irreducible representation of A ⊗ B arises as V ⊗ W for unique irreducible
representations V of A and W of B. Specifically, given any finite-dimensional
k-vector space M with commuting A and B actions that is irreducible (no proper nonzero
invariant k-submodules), M ≅ V ⊗ W for some irreducible V of A and W of B.
Etingof Theorem 3.10.2(ii). -/
theorem Etingof.tensor_product_irreducible_classification (k : Type*) (A B M : Type*)
    [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Ring B] [Algebra k B] [FiniteDimensional k B]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module A M] [IsScalarTower k A M]
    [Module B M] [IsScalarTower k B M]
    [SMulCommClass A B M]
    (hM : ∀ (U : Submodule k M),
      (∀ (a : A) (x : M), x ∈ U → a • x ∈ U) →
      (∀ (b : B) (x : M), x ∈ U → b • x ∈ U) →
      U = ⊥ ∨ U = ⊤) :
    ∃ (V W : Type*) (_ : AddCommGroup V) (_ : Module k V) (_ : Module A V)
      (_ : IsScalarTower k A V) (_ : FiniteDimensional k V) (_ : IsSimpleModule A V)
      (_ : AddCommGroup W) (_ : Module k W) (_ : Module B W)
      (_ : IsScalarTower k B W) (_ : FiniteDimensional k W) (_ : IsSimpleModule B W),
      Nonempty (M ≃ₗ[k] V ⊗[k] W) := by
  sorry
