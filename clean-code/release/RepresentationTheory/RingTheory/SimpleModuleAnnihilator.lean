/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Jacobson.Semiprimary
import RepresentationTheory.Alignment.Attribute

/-! # Annihilator of simple modules -/

universe u v

namespace RepresentationTheory.RingTheory.SimpleModuleAnnihilator

/-- The ideal of ring elements that act as zero on every simple module. -/
@[source_ref "Chapter3/Definition3.5.1" (role := supporting)]
abbrev simpleModuleAnnihilator (A : Type*) [Ring A] : Ideal A :=
  Ideal.jacobson ⊥

/-- An element of the simple-module annihilator acts as zero on every simple module, without a universe restriction. -/
theorem simpleModuleAnnihilator_smul_eq_zero {A : Type u} [Ring A] {a : A}
    (ha : a ∈ simpleModuleAnnihilator A) (V : Type v) [AddCommGroup V] [Module A V]
    [IsSimpleModule A V] (v : V) : a • v = 0 := by
  have ha' : a ∈ Ring.jacobson A := by
    rwa [← Ideal.jacobson_bot]
  exact Module.mem_annihilator.mp
    (IsSemisimpleModule.jacobson_le_annihilator (R := A) (M := V) ha') v

/-- An element belongs to the simple-module annihilator exactly when it annihilates every vector in every simple module of the same universe. -/
@[source_ref "Chapter3/Definition3.5.1" (role := primary)]
theorem mem_simpleModuleAnnihilator_iff (A : Type u) [Ring A] (a : A) :
    a ∈ simpleModuleAnnihilator A ↔
      ∀ (V : Type u) [AddCommGroup V] [Module A V] [IsSimpleModule A V] (v : V),
        a • v = 0 := by
  constructor
  · intro ha V _ _ _ v
    exact simpleModuleAnnihilator_smul_eq_zero ha V v
  · intro ha
    rw [simpleModuleAnnihilator, Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
    refine Ideal.mem_sInf.mpr fun I hI ↦ ?_
    letI : IsSimpleModule A (A ⧸ (I : Submodule A A)) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hI)
    have hz := ha (A ⧸ (I : Submodule A A))
      (Submodule.Quotient.mk (p := (I : Submodule A A)) (1 : A))
    rw [← Submodule.Quotient.mk_smul] at hz
    simpa [Submodule.Quotient.mk_eq_zero] using hz

end RepresentationTheory.RingTheory.SimpleModuleAnnihilator
