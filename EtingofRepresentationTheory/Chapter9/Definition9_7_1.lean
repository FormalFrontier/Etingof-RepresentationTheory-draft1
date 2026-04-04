import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

universe u v

/-!
# Definition 9.7.1: Morita equivalence

Two finite dimensional algebras A and B are **Morita equivalent** if the categories
A-fmod and B-fmod are equivalent as abelian categories.

## Mathlib correspondence

This can be expressed as `CategoryTheory.Equivalence (ModuleCat R) (ModuleCat S)` in Mathlib,
though the finite-dimensional constraint requires additional bundling.
-/

/-- Morita equivalence of algebras, in the sense of Etingof Definition 9.7.1.
Two algebras A and B are Morita equivalent if their module categories are equivalent.
The book restricts to finite-dimensional modules, but we use the full module category
as Mathlib does not have a standalone finite-dimensional module category. -/
def Etingof.MoritaEquivalent (A : Type u) [Ring A] (B : Type v) [Ring B] : Prop :=
  Nonempty (ModuleCat.{max u v} A ≌ ModuleCat.{max u v} B)

open CategoryTheory

/-- k-linear Morita equivalence of k-algebras.

Two k-algebras A and B are k-linearly Morita equivalent if there exists an
equivalence of their module categories whose functor is k-linear on Hom spaces.

For k-algebras, every categorical equivalence is automatically k-linear
(Eilenberg-Watts theorem), so this is equivalent to bare `MoritaEquivalent`.
We use the k-linear version because Eilenberg-Watts is not yet formalized, and
the k-linearity is needed to upgrade ring isomorphisms to k-algebra isomorphisms.

All Morita equivalences constructed in this project (via the corner functor
`M ↦ eM`) are provably k-linear, so this definition is satisfied by all
concrete instances. -/
def Etingof.KLinearMoritaEquivalent (k : Type*) [Field k]
    (A : Type u) [Ring A] [Algebra k A]
    (B : Type u) [Ring B] [Algebra k B] : Prop :=
  ∃ (E : ModuleCat.{u} A ≌ ModuleCat.{u} B),
    haveI : E.functor.Additive :=
      letI : E.functor.IsEquivalence := E.isEquivalence_functor
      Functor.additive_of_preserves_binary_products E.functor
    E.functor.Linear k

namespace Etingof

/-- k-linear Morita equivalence implies bare Morita equivalence. -/
lemma KLinearMoritaEquivalent.toMoritaEquivalent {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : KLinearMoritaEquivalent k A B) : MoritaEquivalent A B :=
  let ⟨E, _⟩ := h; ⟨E⟩

/-- k-linear Morita equivalence is symmetric. -/
lemma KLinearMoritaEquivalent.symm' {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : KLinearMoritaEquivalent k A B) : KLinearMoritaEquivalent k B A := by
  obtain ⟨E, hlin⟩ := h
  haveI : E.functor.Additive :=
    letI : E.functor.IsEquivalence := E.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E.functor
  haveI := hlin
  haveI : E.inverse.Additive := Equivalence.inverse_additive E
  exact ⟨E.symm, Equivalence.inverseLinear k E⟩

/-- k-linear Morita equivalence is transitive. -/
lemma KLinearMoritaEquivalent.trans' {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    {C : Type u} [Ring C] [Algebra k C]
    (h₁ : KLinearMoritaEquivalent k A B)
    (h₂ : KLinearMoritaEquivalent k B C) : KLinearMoritaEquivalent k A C := by
  obtain ⟨E₁, hlin₁⟩ := h₁
  obtain ⟨E₂, hlin₂⟩ := h₂
  haveI : E₁.functor.Additive :=
    letI : E₁.functor.IsEquivalence := E₁.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E₁.functor
  haveI := hlin₁
  haveI : E₂.functor.Additive :=
    letI : E₂.functor.IsEquivalence := E₂.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E₂.functor
  haveI := hlin₂
  refine ⟨E₁.trans E₂, ?_⟩
  change (E₁.functor ⋙ E₂.functor).Linear k
  infer_instance

end Etingof
