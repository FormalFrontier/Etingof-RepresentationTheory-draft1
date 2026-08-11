import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Definition 7.9.3: Left Exact, Right Exact, and Exact Functor

An additive functor F : C → D between abelian categories is:
- **Left exact** if 0 → X → Y → Z exact implies 0 → F(X) → F(Y) → F(Z) exact
- **Right exact** if X → Y → Z → 0 exact implies F(X) → F(Y) → F(Z) → 0 exact
- **Exact** if both left and right exact

## Mathlib correspondence

- Left exact: `CategoryTheory.Functor.PreservesFiniteLimits`
- Right exact: `CategoryTheory.Functor.PreservesFiniteColimits`
- Exact: both simultaneously
-/

/-- A left exact functor (preserves finite limits), in the sense of
Etingof Definition 7.9.3. This is `CategoryTheory.Limits.PreservesFiniteLimits`
in Mathlib. -/
abbrev Etingof.LeftExactFunctor {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Limits.PreservesFiniteLimits F

/-- A right exact functor (preserves finite colimits), in the sense of
Etingof Definition 7.9.3. This is `CategoryTheory.Limits.PreservesFiniteColimits`
in Mathlib. -/
abbrev Etingof.RightExactFunctor {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Limits.PreservesFiniteColimits F

/-- An exact functor, in the sense of Etingof Definition 7.9.3: one that is
both left exact and right exact.

Etingof states this for an additive functor between abelian categories, where
left/right exactness are the sequence conditions of the definition. We record
the general-category form: `Etingof.LeftExactFunctor F ∧ Etingof.RightExactFunctor F`,
i.e. `F` preserves finite limits and finite colimits. In the book's
additive/abelian setting these preservation properties are exactly the two
half-exactness conditions, so this specializes to Etingof's notion. -/
def Etingof.ExactFunctor {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F : CategoryTheory.Functor C D) : Prop :=
  Etingof.LeftExactFunctor F ∧ Etingof.RightExactFunctor F

namespace Etingof

variable {C : Type*} {D : Type*} [CategoryTheory.Category C]
  [CategoryTheory.Category D] {F : CategoryTheory.Functor C D}

/-- A functor is exact iff it is both left exact and right exact. -/
theorem exactFunctor_iff :
    ExactFunctor F ↔ LeftExactFunctor F ∧ RightExactFunctor F :=
  Iff.rfl

/-- An exact functor is left exact. -/
theorem ExactFunctor.leftExact (h : ExactFunctor F) : LeftExactFunctor F :=
  h.1

/-- An exact functor is right exact. -/
theorem ExactFunctor.rightExact (h : ExactFunctor F) : RightExactFunctor F :=
  h.2

/-- A functor that is both left exact and right exact is exact. -/
theorem ExactFunctor.mk (hL : LeftExactFunctor F) (hR : RightExactFunctor F) :
    ExactFunctor F :=
  ⟨hL, hR⟩

end Etingof
