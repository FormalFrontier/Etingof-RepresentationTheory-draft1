/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RepresentationTheory.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Equivalences between representation data -/

namespace RepresentationTheory.Algebra.Representation.Equivalences

open scoped MonoidAlgebra

variable (k : Type*) [CommRing k] (G : Type*) [Group G]
    (V : Type*) [AddCommGroup V] [Module k V]

/-- Equivalence from representations to algebra homomorphisms from the monoid algebra into module
endomorphisms. -/
@[source_ref "Chapter2/Example2.3.14_continued" (role := primary)]
noncomputable def representationAlgHomEquiv :
    Representation k G V ≃ (k[G] →ₐ[k] Module.End k V) :=
  MonoidAlgebra.lift k (Module.End k V) G

/-- The algebra homomorphism associated with a representation sends a singleton basis element to
the corresponding action. -/
@[simp]
theorem representationAlgHomEquiv_apply_single (ρ : Representation k G V) (g : G) :
    representationAlgHomEquiv k G V ρ (MonoidAlgebra.single g 1) = ρ g := by
  simp [representationAlgHomEquiv]

/-- Equivalence between homomorphisms from a group to a monoid and homomorphisms to its units. -/
def groupHomUnitsEquiv (M : Type*) [Monoid M] : (G →* M) ≃ (G →* Mˣ) where
  toFun ρ := ρ.toHomUnits
  invFun f := (Units.coeHom M).comp f
  left_inv ρ := by ext g; rfl
  right_inv f := by ext g; rfl

/-- Equivalence from representations to group homomorphisms into linear automorphisms. -/
@[source_ref "Chapter2/Example2.3.14_continued" (role := primary)]
def representationLinearEquivHomEquiv :
    Representation k G V ≃ (G →* (V ≃ₗ[k] V)) :=
  Equiv.trans
    (groupHomUnitsEquiv G (Module.End k V))
    (MulEquiv.monoidHomCongrRightEquiv
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V))

/-- The linear automorphism obtained from a representation acts as the original representation. -/
@[simp, source_ref "Chapter2/Example2.3.14_continued" (role := supporting)]
theorem representationLinearEquivHomEquiv_apply
    (ρ : Representation k G V) (g : G) (v : V) :
    representationLinearEquivHomEquiv k G V ρ g v = ρ g v := rfl

/-- The representation recovered from a homomorphism to linear automorphisms has its specified
action. -/
@[source_ref "Chapter2/Example2.3.14_continued" (role := supporting)]
theorem representationLinearEquivHomEquiv_symm_apply
    (f : G →* (V ≃ₗ[k] V)) (g : G) (v : V) :
    (representationLinearEquivHomEquiv k G V).symm f g v = f g v := rfl

attribute [nolint defsWithUnderscore]
  representationAlgHomEquiv representationLinearEquivHomEquiv groupHomUnitsEquiv

end RepresentationTheory.Algebra.Representation.Equivalences
