/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.SimpleModule.Basic
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.LinearAlgebra.ModuleDecompositions

/-! # Auxiliary module predicates -/

set_option linter.dupNamespace false
set_option linter.style.whitespace false

namespace RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate

/-- The enclosing module predicate holds for every simple module. -/
@[source_ref "Chapter2/Discussion_after_Theorem2.1.2" (role := primary),
  source_ref "Chapter2/Discussion_2.1_irreducible_indecomposable" (role := primary),
  source_ref "Chapter2/Discussion_2.1_irreducible_indecomposable/Derived01" (role := primary),
  source_ref "Chapter2/Discussion_irreducible_vs_indecomposable" (role := primary)]
theorem of_isSimpleModule (A V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] (h : IsSimpleModule A V) :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate
      A V := by
  haveI := h
  refine ⟨IsSimpleModule.nontrivial A V, fun W₁ W₂ hC => ?_⟩
  rcases eq_bot_or_eq_top W₁ with hW₁ | hW₁
  · exact Or.inl hW₁
  · refine Or.inr ?_
    subst hW₁
    exact top_disjoint.mp hC.disjoint

end RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate

namespace RepresentationTheory.Algebra.Module.AuxiliaryPredicates.Module

/-- A semisimple module satisfying the auxiliary predicate is simple. -/
@[source_ref "Chapter2/Discussion_after_Theorem2.1.2" (role := supporting)]
theorem isSimpleModule_of_auxiliaryPredicate
    (A V : Type*) [Ring A] [AddCommGroup V] [Module A V] [IsSemisimpleModule A V]
    (h : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate
      A V) :
    IsSimpleModule A V := by
  letI : Nontrivial V := h.1
  refine (isSimpleModule_iff A V).2 { eq_bot_or_eq_top := ?_ }
  intro W
  obtain ⟨P, hP⟩ := ComplementedLattice.exists_isCompl W
  rcases h.2 W P hP with hW | hPbot
  · exact Or.inl hW
  · right
    have hsup : W ⊔ P = ⊤ := codisjoint_iff.mp hP.codisjoint
    simpa [hPbot] using hsup

end RepresentationTheory.Algebra.Module.AuxiliaryPredicates.Module
