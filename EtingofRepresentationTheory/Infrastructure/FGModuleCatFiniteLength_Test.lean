import EtingofRepresentationTheory.Infrastructure.FGModuleCatFiniteLength
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Tests for `Etingof.hasFiniteLength_fgModuleCat`

We exercise the categorical finite-length conclusion on concrete rings that are both Noetherian and
Artinian: the ground field itself (finite-dimensional vector spaces), and an arbitrary
finite-dimensional algebra over a field (the motivating case of Etingof §9.6).
-/

open CategoryTheory

section Tests

-- Over a field, every finite-dimensional vector space has finite length as an object of
-- `FGModuleCat k`.
example (k : Type) [Field k] (X : FGModuleCat.{0} k) : Etingof.HasFiniteLength X :=
  Etingof.hasFiniteLength_fgModuleCat X

-- Over any Noetherian and Artinian ring, every object of `FGModuleCat A` has finite length. A
-- finite-dimensional `k`-algebra `A` supplies both instances (`isArtinian_of_tower k`, then
-- `IsNoetherianRing A` by Hopkins-Levitzki), so this is the motivating case of Etingof §9.6.
example (A : Type) [Ring A] [IsNoetherianRing A] [IsArtinianRing A]
    (X : FGModuleCat.{0} A) : Etingof.HasFiniteLength X :=
  Etingof.hasFiniteLength_fgModuleCat X

-- The submodule short exact sequence used in the proof is genuinely short exact.
example (A : Type) [Ring A] [IsNoetherianRing A] {M : Type} [AddCommGroup M] [Module A M]
    [Module.Finite A M] (N : Submodule A M) [Module.Finite A ↥N] :
    (Etingof.submoduleSES N).ShortExact :=
  Etingof.submoduleSES_shortExact N

end Tests

-- Confirm the main result is genuinely sorry-free (no `sorryAx` in the axiom list).
/-- info: 'Etingof.hasFiniteLength_fgModuleCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Etingof.hasFiniteLength_fgModuleCat
