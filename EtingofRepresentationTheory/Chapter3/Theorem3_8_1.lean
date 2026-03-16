import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.SupIndep

/-!
# Theorem 3.8.1: Krull-Schmidt Theorem

Any finite dimensional representation of A can be uniquely (up to isomorphism and the
order of summands) decomposed into a direct sum of indecomposable representations.

The existence of such a decomposition is clear. Uniqueness is proved by induction on dim V,
using Lemma 3.8.2 (endomorphisms of indecomposable representations are either isomorphisms
or nilpotent).
-/

/-- A module is indecomposable if it cannot be decomposed as a nontrivial direct sum
of two submodules. This matches the formulation used in Lemma 3.8.2. -/
def Etingof.IsIndecomposable (A : Type*) (W : Type*) [Ring A] [AddCommGroup W] [Module A W] :
    Prop :=
  ¬ ∃ (M N : Submodule A W), M ≠ ⊥ ∧ N ≠ ⊥ ∧ M ⊔ N = ⊤ ∧ M ⊓ N = ⊥

/-- Existence part of Krull-Schmidt: any finite dimensional representation admits an
internal direct sum decomposition into indecomposable submodules.
Etingof Theorem 3.8.1 (existence). -/
theorem Etingof.krull_schmidt_existence (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ (n : ℕ) (W : Fin n → Submodule A V),
      (∀ i, Etingof.IsIndecomposable A (W i)) ∧
      iSup W = ⊤ ∧ iSupIndep W := by
  sorry

/-- Uniqueness part of Krull-Schmidt: any two decompositions into indecomposable
direct summands have the same number of summands, and the summands can be matched
up to isomorphism after reindexing.
Etingof Theorem 3.8.1 (uniqueness). -/
theorem Etingof.krull_schmidt_uniqueness (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V]
    {n m : ℕ} (W : Fin n → Submodule A V) (W' : Fin m → Submodule A V)
    (hW_indec : ∀ i, Etingof.IsIndecomposable A (W i))
    (hW'_indec : ∀ i, Etingof.IsIndecomposable A (W' i))
    (hW_sup : iSup W = ⊤) (hW_ind : iSupIndep W)
    (hW'_sup : iSup W' = ⊤) (hW'_ind : iSupIndep W') :
    n = m ∧ ∃ σ : Fin n ≃ Fin m, ∀ i, Nonempty ((W i) ≃ₗ[A] (W' (σ i))) := by
  sorry
