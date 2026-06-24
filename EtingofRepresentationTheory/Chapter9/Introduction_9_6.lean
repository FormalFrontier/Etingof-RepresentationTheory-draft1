import EtingofRepresentationTheory.Chapter9.Definition9_6_1
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Exact.Basic

universe w u v

/-!
# §9.6 Introduction: k-linear finite abelian categories and finite-dimensional Hom spaces

Etingof §9.6 works with a `k`-linear abelian category `𝒞` in which every object has finite
length and `End(X) = k` for every simple object `X`. The prose then remarks:

> Note that in such a category, Hom spaces are finite dimensional (check it!).

This file does the "check it!". We package the extra data Etingof requires on top of
`Etingof.IsFiniteAbelianCategory` as a new class
`Etingof.IsFiniteAbelianCategoryOverField k C`, carrying

* `k`-linearity (`[Linear k C]`),
* the finite-length condition (every object is built from simples by finitely many
  extensions, encoded by the inductive predicate `Etingof.HasFiniteLength`), and
* `End(X) ≅ k` for every simple `X` (an algebra isomorphism `End X ≃ₐ[k] k`).

The main result, `Etingof.IsFiniteAbelianCategoryOverField.finiteDimensional_hom`, proves
`FiniteDimensional k (X ⟶ Y)` for all objects `X Y`. The proof is the elementary one
indicated by Etingof: a double induction on the lengths of `X` and `Y`, using Schur's
lemma for the simple/simple base case and left-exactness of `Hom` (via the kernel/cokernel
universal properties of a short exact sequence) for the extension steps.

We add this as a *new* class extending the existing `Etingof.IsFiniteAbelianCategory` data,
rather than modifying that class, so every existing consumer (`Theorem9_6_4`,
`Introduction_9_7`, ...) continues to typecheck unchanged.
-/

open CategoryTheory CategoryTheory.Limits

namespace Etingof

/-- `HasFiniteLength X` holds when `X` can be built from simple objects (and the zero
object) by finitely many extensions. This is the categorical "finite length / finite
filtration with simple quotients" condition of Etingof §9.6, packaged as an inductive
predicate so that downstream statements can be proved by induction on the filtration. -/
inductive HasFiniteLength {C : Type u} [Category.{v} C] [Abelian C] : C → Prop
  | of_isZero {X : C} (h : Limits.IsZero X) : HasFiniteLength X
  | of_simple {X : C} (h : Simple X) : HasFiniteLength X
  | of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
      (h₁ : HasFiniteLength S.X₁) (h₃ : HasFiniteLength S.X₃) : HasFiniteLength S.X₂

/-- A `k`-linear finite abelian category in the sense of Etingof §9.6: a finite abelian
category (`Etingof.IsFiniteAbelianCategory`) which is `k`-linear, in which every object has
finite length, and in which `End(X) ≅ k` for every simple object `X`. -/
class IsFiniteAbelianCategoryOverField (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C] [Linear k C] where
  /-- Every object has finite length. -/
  finiteLength : ∀ X : C, HasFiniteLength X
  /-- For every simple object `X`, the endomorphism algebra is `k`. -/
  endSimple : ∀ (X : C), Simple X → Nonempty (End X ≃ₐ[k] k)

variable {k : Type w} [Field k]

section HomFinite

variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]

/-- If `f` and `g` form an exact sequence `A → B → D` of `k`-vector spaces with `A` and `D`
finite dimensional, then so is `B`. (Used with the left-exact Hom sequence of a short exact
sequence in `C`.) -/
theorem finiteDimensional_of_exact
    {A B D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [Module k A] [Module k B] [Module k D]
    {f : A →ₗ[k] B} {g : B →ₗ[k] D} (hexact : Function.Exact f g)
    [FiniteDimensional k A] [FiniteDimensional k D] :
    FiniteDimensional k B := by
  have hker : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp hexact
  haveI : FiniteDimensional k (B ⧸ LinearMap.range f) := by
    rw [← hker]
    exact Module.Finite.equiv (LinearMap.quotKerEquivRange g).symm
  exact Module.Finite.of_submodule_quotient (LinearMap.range f)

/-- Left-exactness of the covariant functor `Hom(X, -)` on a short exact sequence:
`0 → (X ⟶ X₁) → (X ⟶ X₂) → (X ⟶ X₃)` is exact. -/
theorem exact_rightComp (X : C) {S : ShortComplex C} (hS : S.ShortExact) :
    Function.Exact (Linear.rightComp k X S.f) (Linear.rightComp k X S.g) := by
  rw [LinearMap.exact_iff]
  ext b
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hb
    have hb' : b ≫ S.g = 0 := hb
    obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hS.fIsKernel b hb'
    refine ⟨a, ?_⟩
    change a ≫ S.f = b
    simpa using ha
  · rintro ⟨a, rfl⟩
    change (a ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]

/-- Left-exactness of the contravariant functor `Hom(-, Y)` on a short exact sequence:
`0 → (X₃ ⟶ Y) → (X₂ ⟶ Y) → (X₁ ⟶ Y)` is exact. -/
theorem exact_leftComp (Y : C) {S : ShortComplex C} (hS : S.ShortExact) :
    Function.Exact (Linear.leftComp k Y S.g) (Linear.leftComp k Y S.f) := by
  rw [LinearMap.exact_iff]
  ext b
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hb
    have hb' : S.f ≫ b = 0 := hb
    obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel b hb'
    refine ⟨a, ?_⟩
    change S.g ≫ a = b
    simpa using ha
  · rintro ⟨a, rfl⟩
    change S.f ≫ (S.g ≫ a) = 0
    rw [← Category.assoc, S.zero, zero_comp]

/-- Schur's lemma packaged for finite dimensionality: if `End(Z) ≅ k`-finite for every
simple `Z`, then `Hom(X, Y)` is finite dimensional for any two simple objects `X`, `Y`. -/
theorem finiteDimensional_hom_of_simple_simple
    (hfin : ∀ (Z : C), Simple Z → FiniteDimensional k (Z ⟶ Z))
    {X Y : C} (hX : Simple X) (hY : Simple Y) :
    FiniteDimensional k (X ⟶ Y) := by
  by_cases h : Nonempty (X ≅ Y)
  · obtain ⟨e⟩ := h
    haveI := hfin X hX
    refine Module.Finite.equiv (LinearEquiv.ofLinear
      (Linear.rightComp k X e.hom) (Linear.rightComp k X e.inv) ?_ ?_)
    · ext p
      change (p ≫ e.inv) ≫ e.hom = p
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    · ext p
      change (p ≫ e.hom) ≫ e.inv = p
      rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  · haveI := hX
    haveI := hY
    haveI : Subsingleton (X ⟶ Y) := by
      refine ⟨fun f g => ?_⟩
      have hz : ∀ p : X ⟶ Y, p = 0 := by
        intro p
        by_contra hp
        haveI : IsIso p := isIso_of_hom_simple hp
        exact h ⟨asIso p⟩
      rw [hz f, hz g]
    exact Module.Finite.of_finite

/-- `Hom(X, Y)` is finite dimensional when `X` is simple and `Y` has finite length.
By induction on a filtration of `Y`. -/
theorem finiteDimensional_hom_simple_source
    (hfin : ∀ (Z : C), Simple Z → FiniteDimensional k (Z ⟶ Z))
    {X : C} (hX : Simple X) :
    ∀ {Y : C}, HasFiniteLength Y → FiniteDimensional k (X ⟶ Y) := by
  intro Y hY
  induction hY with
  | of_isZero h =>
      haveI : Subsingleton (X ⟶ _) := ⟨fun f g => h.eq_of_tgt f g⟩
      exact Module.Finite.of_finite
  | of_simple hYs =>
      exact finiteDimensional_hom_of_simple_simple hfin hX hYs
  | of_shortExact hS _ _ ih₁ ih₃ =>
      haveI := ih₁
      haveI := ih₃
      exact finiteDimensional_of_exact (exact_rightComp X hS)

/-- `Hom(X, Y)` is finite dimensional when `X` has finite length and `Y` is arbitrary, given
that `Hom(Z, W)` is finite dimensional for simple `Z` and every `W` (and `End` of simples is
`k`-finite). By induction on a filtration of `X`, using `Hom(-, Y)` left-exactness. -/
theorem finiteDimensional_hom_of_hasFiniteLength
    (hfin : ∀ (Z : C), Simple Z → FiniteDimensional k (Z ⟶ Z))
    (hlen : ∀ (Z : C), HasFiniteLength Z) (Y : C) :
    ∀ {X : C}, HasFiniteLength X → FiniteDimensional k (X ⟶ Y) := by
  intro X hX
  induction hX with
  | of_isZero h =>
      haveI : Subsingleton (_ ⟶ Y) := ⟨fun f g => h.eq_of_src f g⟩
      exact Module.Finite.of_finite
  | of_simple hXs =>
      exact finiteDimensional_hom_simple_source hfin hXs (hlen Y)
  | of_shortExact hS _ _ ih₁ ih₃ =>
      haveI := ih₁
      haveI := ih₃
      exact finiteDimensional_of_exact (exact_leftComp Y hS)

end HomFinite

namespace IsFiniteAbelianCategoryOverField

variable {C : Type u} [Category.{v} C] [Etingof.IsFiniteAbelianCategory C] [Linear k C]
  [hCat : IsFiniteAbelianCategoryOverField k C]

/-- From `End(X) ≅ k`, the endomorphism space of a simple object is finite dimensional. -/
theorem endSimple_finiteDimensional (X : C) (hX : Simple X) :
    FiniteDimensional k (X ⟶ X) := by
  obtain ⟨e⟩ := hCat.endSimple X hX
  change FiniteDimensional k (End X)
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- **Etingof §9.6, "check it!"**: in a `k`-linear finite abelian category where every object
has finite length and `End(X) = k` for simple `X`, every `Hom` space is finite dimensional. -/
theorem finiteDimensional_hom (X Y : C) : FiniteDimensional k (X ⟶ Y) :=
  finiteDimensional_hom_of_hasFiniteLength
    (fun Z hZ => endSimple_finiteDimensional Z hZ) hCat.finiteLength Y (hCat.finiteLength X)

end IsFiniteAbelianCategoryOverField

end Etingof
