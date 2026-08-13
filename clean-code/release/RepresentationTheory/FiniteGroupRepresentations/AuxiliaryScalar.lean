/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar

/-- An auxiliary complex scalar attached to a finite-dimensional complex representation of a
finite group. -/
@[source_ref "Chapter5/Definition5.1.4" (role := supporting),
  source_ref "Chapter5/Introduction" (role := primary)]
noncomputable def auxiliaryRepresentationScalar
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, LinearMap.trace ℂ V (ρ (g * g))

end RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar
