import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Ring.Opposite

universe u

namespace RepresentationTheory.Auxiliary.RingData

/-- An auxiliary property of a ring indexed by a natural number. -/
def auxiliaryRingNatProperty (R : Type u) [Ring R] (d : ℕ) : Prop :=
  ∀ (M : ModuleCat.{u} R), CategoryTheory.HasProjectiveDimensionLE M d

/-- An auxiliary extended-natural-valued invariant of a ring. -/
noncomputable def auxiliaryRingENatInvariant (R : Type u) [Ring R] : ℕ∞ :=
  ⨅ (d : ℕ) (_ : auxiliaryRingNatProperty R d), (d : ℕ∞)

/-- A second auxiliary property of a ring indexed by a natural number. -/
abbrev auxiliaryRingNatPropertyAux (R : Type u) [Ring R] (d : ℕ) : Prop :=
  auxiliaryRingNatProperty R d

/-- A second auxiliary extended-natural-valued invariant of a ring. -/
noncomputable abbrev auxiliaryRingENatInvariantAux (R : Type u) [Ring R] : ℕ∞ :=
  auxiliaryRingENatInvariant R

/-- A third auxiliary property of a ring indexed by a natural number. -/
def auxiliaryRingNatPropertyThird (R : Type u) [Ring R] (d : ℕ) : Prop :=
  auxiliaryRingNatProperty Rᵐᵒᵖ d

/-- A third auxiliary extended-natural-valued invariant of a ring. -/
noncomputable def auxiliaryRingENatInvariantThird (R : Type u) [Ring R] : ℕ∞ :=
  auxiliaryRingENatInvariant Rᵐᵒᵖ

/-- The third auxiliary natural-number-indexed ring property is equivalent to the second one for
the opposite ring. -/
@[simp]
theorem auxiliaryRingNatPropertyThird_opposite_iff (R : Type u) [Ring R] (d : ℕ) :
    auxiliaryRingNatPropertyThird R d ↔ auxiliaryRingNatPropertyAux Rᵐᵒᵖ d :=
  Iff.rfl

/-- The third auxiliary extended-natural-valued ring invariant equals the second one for the
opposite ring. -/
@[simp]
theorem auxiliaryRingENatInvariantThird_opposite (R : Type u) [Ring R] :
    auxiliaryRingENatInvariantThird R = auxiliaryRingENatInvariantAux Rᵐᵒᵖ :=
  rfl

end RepresentationTheory.Auxiliary.RingData
