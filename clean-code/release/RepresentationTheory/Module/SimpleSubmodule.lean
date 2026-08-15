/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.Artinian.Module
import RepresentationTheory.Alignment.Attribute

/-! # Simple submodules -/

open Polynomial

namespace RepresentationTheory.Module.SimpleSubmodule

section FiniteDimensional

variable {k A V : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V]

/-- Every nontrivial finite-dimensional module contains a subtype that is simple as a module. -/
@[source_ref "Chapter3/Proposition3.1.4/Derived3" (role := primary)]
theorem exists_isSimpleModule_subtype [Module.Finite k V] [Nontrivial V] :
    ∃ S : Submodule A V, IsSimpleModule A S := by
  haveI : IsArtinian k V := inferInstance
  haveI : IsArtinian A V := isArtinian_of_tower k inferInstance
  haveI : Nontrivial (Submodule A V) := (Submodule.nontrivial_iff A).mpr inferInstance
  haveI : IsAtomic (Submodule A V) := isAtomic_of_orderBot_wellFounded_lt IsWellFounded.wf
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A V)
  exact ⟨S, isSimpleModule_iff_isAtom.mpr hS⟩

end FiniteDimensional

/-- Over a field, no subtype of the displayed polynomial module is simple. -/
theorem not_exists_isSimpleModule_polynomial_subtype (k : Type*) [Field k] :
    ¬ ∃ S : Submodule (Polynomial k) (Polynomial k),
        IsSimpleModule (Polynomial k) S := by
  rintro ⟨S, hS⟩
  rw [isSimpleModule_iff_isAtom] at hS
  obtain ⟨s, hsS, hs0⟩ := (Submodule.ne_bot_iff S).mp hS.1
  set T : Submodule (Polynomial k) (Polynomial k) := Submodule.span (Polynomial k) {X * s}
    with hT
  have hXs0 : X * s ≠ 0 := mul_ne_zero X_ne_zero hs0
  have hTle : T ≤ S := by
    rw [hT, Submodule.span_le, Set.singleton_subset_iff]
    exact S.smul_mem X hsS
  have hTne : T ≠ ⊥ := by
    rw [hT, Ne, Submodule.span_singleton_eq_bot]
    exact hXs0
  have hsT : s ∈ T := by
    rcases eq_or_lt_of_le hTle with hTeq | hTlt
    · rw [hTeq]; exact hsS
    · exact absurd (hS.2 T hTlt) hTne
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hsT
  rw [smul_eq_mul, ← mul_assoc] at ha
  have hax : a * X = 1 := by
    have : a * X * s = 1 * s := by rw [ha, one_mul]
    exact mul_right_cancel₀ hs0 this
  exact not_isUnit_X (IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact hax))

end RepresentationTheory.Module.SimpleSubmodule

attribute [source_ref "Chapter2/Problem2.3.15" (role := primary)]
  RepresentationTheory.Module.SimpleSubmodule.exists_isSimpleModule_subtype

attribute [source_ref "Chapter2/Problem2.3.15" (role := supporting)]
  RepresentationTheory.Module.SimpleSubmodule.not_exists_isSimpleModule_polynomial_subtype
