import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Projection

/-!
# Definition 2.3.8: Indecomposable Representation

A nonzero representation V of an algebra A is said to be **indecomposable** if it is
not isomorphic to a direct sum of two nonzero representations.

## Mathlib correspondence (partial)

Mathlib has `Indecomposable` for order theory but not directly for modules.
We define indecomposability for modules as: V is nontrivial and for any submodules
W₁, W₂ with V = W₁ ⊕ W₂, either W₁ = 0 or W₂ = 0.

This is equivalent to saying that V has no nontrivial complemented submodules.
-/

-- not in Mathlib as of v4.28
/-- A module is **indecomposable** if it is nontrivial and cannot be decomposed as a
direct sum of two nonzero submodules. Etingof Definition 2.3.8. -/
def Etingof.IsIndecomposable (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] : Prop :=
  Nontrivial V ∧ ∀ (W₁ W₂ : Submodule A V),
    IsCompl W₁ W₂ → W₁ = ⊥ ∨ W₂ = ⊥

universe u v

/-- Data exhibiting a representation as a direct sum of two nonzero representations. This is the
literal formulation used in Definition 2.3.8; `IsIndecomposable` uses the equivalent internal
complement formulation because that is the useful API for subsequent proofs. -/
structure Etingof.NontrivialDirectSumDecomposition
    (A : Type u) (V : Type v) [Ring A] [AddCommGroup V] [Module A V] where
  V₁ : Type v
  V₂ : Type v
  [addCommGroupV₁ : AddCommGroup V₁]
  [addCommGroupV₂ : AddCommGroup V₂]
  [moduleV₁ : Module A V₁]
  [moduleV₂ : Module A V₂]
  [nontrivialV₁ : Nontrivial V₁]
  [nontrivialV₂ : Nontrivial V₂]
  equiv : V ≃ₗ[A] V₁ × V₂

/-- The book's direct formulation: `V` is nonzero and is not isomorphic to a direct sum of two
nonzero representations. -/
def Etingof.IsIndecomposableAsDirectSum
    (A : Type u) (V : Type v) [Ring A] [AddCommGroup V] [Module A V] : Prop :=
  Nontrivial V ∧ IsEmpty (Etingof.NontrivialDirectSumDecomposition A V)

/-- The internal-complement definition used by the project is equivalent to the source's literal
"not isomorphic to a direct sum of two nonzero representations" definition. -/
theorem Etingof.isIndecomposable_iff_asDirectSum
    (A : Type u) (V : Type v) [Ring A] [AddCommGroup V] [Module A V] :
    Etingof.IsIndecomposable A V ↔ Etingof.IsIndecomposableAsDirectSum A V := by
  sorry

/-- An indecomposable module has no nontrivial direct sum decomposition (negation form).
Useful for proofs that proceed by contradiction on a decomposition. -/
theorem Etingof.IsIndecomposable.not_exists_nontrivial_compl {A : Type*} {V : Type*}
    [Ring A] [AddCommGroup V] [Module A V]
    (h : Etingof.IsIndecomposable A V) :
    ¬ ∃ (M N : Submodule A V), M ≠ ⊥ ∧ N ≠ ⊥ ∧ M ⊔ N = ⊤ ∧ M ⊓ N = ⊥ := by
  rintro ⟨M, N, hM, hN, hSup, hInf⟩
  have hC : IsCompl M N :=
    ⟨disjoint_iff.mpr hInf, codisjoint_iff.mpr (top_le_iff.mp (hSup ▸ le_rfl))⟩
  rcases h.2 M N hC with rfl | rfl
  · exact hM rfl
  · exact hN rfl
