import Mathlib
import EtingofRepresentationTheory.Chapter7.Definition7_9_1
import EtingofRepresentationTheory.Chapter7.Definition7_9_3

/-!
# Exercise 7.9.7: Adjoint additive functors are right/left exact

**Exercise 7.9.7.** Show that if `(F, G)` is a pair of adjoint additive functors
between abelian categories, then `F` is right exact and `G` is left exact.

## Formalization

"Right exact" is `Etingof.RightExactFunctor` (Definition 7.9.3), i.e.
`CategoryTheory.Limits.PreservesFiniteColimits`; "left exact" is
`Etingof.LeftExactFunctor`, i.e. `PreservesFiniteLimits`. The mathematical content
is Mathlib's `Adjunction.leftAdjoint_preservesColimits` /
`Adjunction.rightAdjoint_preservesLimits`.
-/

open CategoryTheory

/-- Exercise 7.9.7: for an adjunction `F ⊣ G` of additive functors between abelian
categories, the left adjoint `F` is right exact and the right adjoint `G` is left
exact. -/
theorem Etingof.Exercise7_9_7 {C : Type*} {D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D) (G : D ⥤ C)
    [F.Additive] [G.Additive] (adj : F ⊣ G) :
    Etingof.RightExactFunctor F ∧ Etingof.LeftExactFunctor G := by
  -- A left adjoint preserves all colimits, hence finite ones; a right adjoint
  -- preserves all limits, hence finite ones.
  haveI := adj.leftAdjoint_preservesColimits
  haveI := adj.rightAdjoint_preservesLimits
  exact ⟨inferInstance, inferInstance⟩
