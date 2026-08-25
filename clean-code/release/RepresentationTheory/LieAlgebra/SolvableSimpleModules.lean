/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Analysis.Complex.Polynomial.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Simple modules over solvable Lie algebras -/

namespace RepresentationTheory.LieAlgebra.SolvableSimpleModules

open Module (finrank)

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

/-- A nontrivial finite-dimensional module over a solvable complex Lie algebra has dimension one
when its Lie submodules form a simple order. -/
@[source_ref "Chapter2/Problem2.16.1" (role := primary)]
theorem finrank_eq_one_of_isSimpleOrder [LieAlgebra.IsSolvable L]
    [FiniteDimensional ℂ V] [Nontrivial V] (hirr : IsSimpleOrder (LieSubmodule ℂ L V)) :
    finrank ℂ V = 1 := by
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable ℂ L V
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : LieModule.weightSpace V χ)
  rw [LieModule.mem_weightSpace] at hv
  have hv0 : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  let N : LieSubmodule ℂ L V :=
    { __ := Submodule.span ℂ {v}
      lie_mem := fun {x m} hm => by
        have hm' : m ∈ Submodule.span ℂ {v} := hm
        rw [Submodule.mem_span_singleton] at hm'
        obtain ⟨c, rfl⟩ := hm'
        exact Submodule.mem_span_singleton.mpr
          ⟨c * χ x, by rw [lie_smul, hv x, smul_smul]⟩ }
  have hN : N ≠ ⊥ := fun h => hv0 (by
    have : v ∈ N := Submodule.mem_span_singleton_self v
    rwa [h, LieSubmodule.mem_bot] at this)
  have hspan : Submodule.span ℂ {v} = ⊤ := by
    have : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN
    rwa [← LieSubmodule.toSubmodule_eq_top] at this
  rw [← finrank_top ℂ V, ← hspan, finrank_span_singleton hv0]

end RepresentationTheory.LieAlgebra.SolvableSimpleModules
