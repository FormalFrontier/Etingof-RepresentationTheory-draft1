import EtingofRepresentationTheory.Infrastructure.FGModuleCatSubobjectFiniteDimensional

/-!
# Tests for `Etingof.finiteDimensionalOrder_subobject_fgModuleCat`

We exercise the finite-dimensional-order conclusion on the subobject lattice of `FGModuleCat`
objects over rings that are both Noetherian and Artinian.
-/

open CategoryTheory

section Tests

-- Over a field, the subobject lattice of a finite-dimensional vector space is finite dimensional.
example (k : Type) [Field k] (X : FGModuleCat.{0} k) :
    FiniteDimensionalOrder (Subobject X) :=
  Etingof.finiteDimensionalOrder_subobject_fgModuleCat X

-- Over any Noetherian and Artinian ring (in particular a finite-dimensional `k`-algebra).
example (A : Type) [Ring A] [IsNoetherianRing A] [IsArtinianRing A] (X : FGModuleCat.{0} A) :
    FiniteDimensionalOrder (Subobject X) :=
  Etingof.finiteDimensionalOrder_subobject_fgModuleCat X

-- The underlying order embedding into the module's subobject lattice is available.
noncomputable example (A : Type) [Ring A] [IsNoetherianRing A] (X : FGModuleCat.{0} A) :
    Subobject X ↪o Subobject ((forget₂ (FGModuleCat.{0} A) (ModuleCat.{0} A)).obj X) :=
  Etingof.subobjectInclOrderEmbedding X

end Tests

-- Confirm the main result is genuinely sorry-free.
/-- info: 'Etingof.finiteDimensionalOrder_subobject_fgModuleCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Etingof.finiteDimensionalOrder_subobject_fgModuleCat
