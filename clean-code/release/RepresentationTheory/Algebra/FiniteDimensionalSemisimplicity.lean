/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import RepresentationTheory.RingTheory.SimpleModuleAnnihilator
import RepresentationTheory.Alignment.Attribute

/-! # Finite-dimensional algebra semisimplicity -/

namespace RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity

/-- A module-theoretic semisimplicity condition for a finite-dimensional algebra over a field. -/
@[source_ref "Chapter3/Definition3.5.7" (role := supporting)]
abbrev FiniteAlgebraModuleSemisimple (k A : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] :=
  RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A = ⊥

/-- A finite-dimensional algebra whose underlying ring is semisimple satisfies the module semisimplicity condition. -/
theorem finiteAlgebraModuleSemisimple_of_isSemisimpleRing (k A : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] (h : IsSemisimpleRing A) :
    FiniteAlgebraModuleSemisimple k A := by
  rw [FiniteAlgebraModuleSemisimple,
    RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator,
    Ideal.jacobson_bot]
  exact h.jacobson_eq_bot

/-- An algebra satisfying the finite-dimensional module semisimplicity condition is a semisimple ring. -/
theorem FiniteAlgebraModuleSemisimple.isSemisimpleRing {k A : Type*} [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] (h : FiniteAlgebraModuleSemisimple k A) :
    IsSemisimpleRing A := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  rw [FiniteAlgebraModuleSemisimple,
    RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator,
    Ideal.jacobson_bot, ← IsArtinianRing.isSemisimpleRing_iff_jacobson] at h
  exact h

/-- For a finite-dimensional algebra over a field, the module semisimplicity condition is equivalent to semisimplicity of the underlying ring. -/
@[source_ref "Chapter3/Definition3.5.7" (role := supporting)]
theorem finiteAlgebraModuleSemisimple_iff (k A : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] :
    FiniteAlgebraModuleSemisimple k A ↔ IsSemisimpleRing A :=
  ⟨FiniteAlgebraModuleSemisimple.isSemisimpleRing,
    finiteAlgebraModuleSemisimple_of_isSemisimpleRing k A⟩

end RepresentationTheory.Algebra.FiniteDimensionalSemisimplicity
