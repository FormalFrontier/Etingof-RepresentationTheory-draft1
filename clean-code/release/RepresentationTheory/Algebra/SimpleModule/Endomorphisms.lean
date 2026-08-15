/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Endomorphisms of simple modules

Scalarity results for endomorphisms of finite-dimensional simple modules.
-/

set_option linter.style.whitespace false

namespace RepresentationTheory.Algebra.SimpleModule.Endomorphisms

/-- Every linear endomorphism of a finite-dimensional simple module over an algebraically closed
field is scalar multiplication. -/
@[source_ref "Chapter2/Corollary2.3.10" (role := primary),
  source_ref "Chapter2/Discussion_proof_Corollary2.3.10/Derived2" (role := supporting),
  source_ref "Chapter2/Discussion_proof_Corollary2.3.12/Derived2" (role := supporting)]
theorem endomorphism_eq_smul
    {k : Type*} [Field k] [IsAlgClosed k]
    {A : Type*} [Ring A] [Algebra k A]
    {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [IsSimpleModule A V] [FiniteDimensional k V]
    (φ : V →ₗ[A] V) :
    ∃ c : k, ∀ v : V, φ v = c • v := by
  obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).2 φ
  exact ⟨c, fun v => by simp [← hc]⟩

end RepresentationTheory.Algebra.SimpleModule.Endomorphisms
