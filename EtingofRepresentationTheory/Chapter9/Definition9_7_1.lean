import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

universe u v

open CategoryTheory

/-!
# Definition 9.7.1: Morita equivalence

Two finite dimensional algebras `A` and `B` are **Morita equivalent** if the categories
`A`-fmod and `B`-fmod are equivalent as abelian categories.

## Mathlib correspondence

For a finite-dimensional `k`-algebra `A`, the book's category `A`-fmod of
finite-dimensional modules is exactly the category of finitely generated `A`-modules:
a finitely generated module over a finite-dimensional algebra is finite dimensional over
`k`, and conversely a finite-dimensional module is finitely generated. This category is
`FGModuleCat A` in Mathlib, so the book's definition is expressed literally as
`Etingof.MoritaEquivalentFmod` below: `Nonempty (FGModuleCat A ≌ FGModuleCat B)`.

We also keep the auxiliary notion `Etingof.MoritaEquivalent`, an equivalence of the
*full* module categories `Nonempty (ModuleCat A ≌ ModuleCat B)`. For finite-dimensional
algebras `ModuleCat A` is the ind-completion of `FGModuleCat A`, so the two notions
agree; the forward implication `MoritaEquivalent → MoritaEquivalentFmod` is
`Etingof.MoritaEquivalent.toFmod` (in `Infrastructure/MoritaFGRestriction.lean`), obtained
by restricting a full-module equivalence to the finitely generated subcategories. The
converse (recovering a full-module equivalence from an equivalence of finite-dimensional
modules) is the Morita reconstruction theorem and is not yet formalized. The full-module
notion is the one produced by the concrete constructions in this project (the corner
functor `M ↦ eM` and `exists_basic_morita_equivalent`), and every book-level conclusion
is exposed on the faithful `fmod` notion via the forward implication.
-/

/-- **Morita equivalence, Etingof Definition 9.7.1 (book-faithful form).**

Two algebras `A` and `B` are Morita equivalent if their categories of
finitely generated modules are equivalent. For finite-dimensional algebras
`FGModuleCat A` is the book's category `A`-fmod of finite-dimensional modules, so this is
the literal book definition. -/
def Etingof.MoritaEquivalentFmod (A : Type u) [Ring A] (B : Type u) [Ring B] : Prop :=
  Nonempty (FGModuleCat.{u} A ≌ FGModuleCat.{u} B)

/-- Morita equivalence of algebras via the full module categories.

Two algebras `A` and `B` are equivalent here if their categories of *all* modules are
equivalent. For finite-dimensional algebras this agrees with the book-faithful
`Etingof.MoritaEquivalentFmod` (the full module category is the ind-completion of the
finite-dimensional one); the forward direction is `Etingof.MoritaEquivalent.toFmod`.
This full-module notion is what the concrete constructions in this project produce. -/
def Etingof.MoritaEquivalent (A : Type u) [Ring A] (B : Type v) [Ring B] : Prop :=
  Nonempty (ModuleCat.{max u v} A ≌ ModuleCat.{max u v} B)

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

/-- k-linear Morita equivalence of k-algebras, book-faithful `fmod` form.

Two k-algebras `A` and `B` are k-linearly Morita equivalent (on finitely generated
modules) if there is an equivalence `FGModuleCat A ≌ FGModuleCat B` whose functor is
k-linear on Hom spaces. This is the k-linear refinement of
`Etingof.MoritaEquivalentFmod`, matching `Etingof.KLinearMoritaEquivalent` on the full
module categories. -/
def Etingof.KLinearMoritaEquivalentFmod (k : Type*) [Field k]
    (A : Type u) [Ring A] [Algebra k A]
    (B : Type u) [Ring B] [Algebra k B] : Prop :=
  ∃ (E : FGModuleCat.{u} A ≌ FGModuleCat.{u} B), E.functor.Linear k

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

/-! ## Book-faithful `fmod` Morita equivalence: reflexivity, symmetry, transitivity -/

/-- Book-faithful Morita equivalence is reflexive. -/
lemma MoritaEquivalentFmod.refl (A : Type u) [Ring A] : MoritaEquivalentFmod A A :=
  ⟨CategoryTheory.Equivalence.refl⟩

/-- Book-faithful Morita equivalence is symmetric. -/
lemma MoritaEquivalentFmod.symm {A : Type u} [Ring A] {B : Type u} [Ring B]
    (h : MoritaEquivalentFmod A B) : MoritaEquivalentFmod B A :=
  h.map CategoryTheory.Equivalence.symm

/-- Book-faithful Morita equivalence is transitive. -/
lemma MoritaEquivalentFmod.trans {A : Type u} [Ring A] {B : Type u} [Ring B]
    {C : Type u} [Ring C]
    (h₁ : MoritaEquivalentFmod A B) (h₂ : MoritaEquivalentFmod B C) :
    MoritaEquivalentFmod A C := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩

/-- k-linear book-faithful Morita equivalence implies the bare book-faithful notion. -/
lemma KLinearMoritaEquivalentFmod.toMoritaEquivalentFmod {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : KLinearMoritaEquivalentFmod k A B) : MoritaEquivalentFmod A B :=
  let ⟨E, _⟩ := h; ⟨E⟩

/-- k-linear book-faithful Morita equivalence is symmetric. -/
lemma KLinearMoritaEquivalentFmod.symm' {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : KLinearMoritaEquivalentFmod k A B) : KLinearMoritaEquivalentFmod k B A := by
  obtain ⟨E, hlin⟩ := h
  haveI := hlin
  exact ⟨E.symm, Equivalence.inverseLinear k E⟩

/-- k-linear book-faithful Morita equivalence is transitive. -/
lemma KLinearMoritaEquivalentFmod.trans' {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    {C : Type u} [Ring C] [Algebra k C]
    (h₁ : KLinearMoritaEquivalentFmod k A B)
    (h₂ : KLinearMoritaEquivalentFmod k B C) : KLinearMoritaEquivalentFmod k A C := by
  obtain ⟨E₁, hlin₁⟩ := h₁
  obtain ⟨E₂, hlin₂⟩ := h₂
  haveI := hlin₁
  haveI := hlin₂
  refine ⟨E₁.trans E₂, ?_⟩
  change (E₁.functor ⋙ E₂.functor).Linear k
  infer_instance

end Etingof
