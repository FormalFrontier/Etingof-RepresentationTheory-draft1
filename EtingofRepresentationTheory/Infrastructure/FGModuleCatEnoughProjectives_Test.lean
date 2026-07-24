import EtingofRepresentationTheory.Infrastructure.FGModuleCatEnoughProjectives
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Tests for `FGModuleCat.enoughProjectives`

We exercise the `EnoughProjectives (FGModuleCat A)` instance on concrete Noetherian rings:
the ground field itself, and an arbitrary finite-dimensional algebra over a field.
-/

open CategoryTheory

section Tests

-- Over a field, `FGModuleCat k` (finite-dimensional vector spaces) has enough projectives.
example (k : Type) [Field k] : EnoughProjectives (FGModuleCat.{0} k) := inferInstance

-- A finite-dimensional algebra over a field is Artinian, hence Noetherian, so `FGModuleCat A`
-- has enough projectives: this is the motivating case of Etingof Definition 9.6.1.
example (k A : Type) [Field k] [Ring A] [Algebra k A] [Module.Finite k A] :
    EnoughProjectives (FGModuleCat.{0} A) := by
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  haveI : IsNoetherianRing A := inferInstance
  infer_instance

-- The supporting projectivity-transfer lemma is available.
example (A : Type) [Ring A] {P : FGModuleCat.{0} A}
    (h : Projective ((FGModuleCat.incl A).obj P)) : Projective P :=
  FGModuleCat.projective_of_forget₂_projective h

end Tests

-- Confirm the instance is genuinely sorry-free (no `sorryAx` in the axiom list).
/-- info: 'FGModuleCat.enoughProjectives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FGModuleCat.enoughProjectives
