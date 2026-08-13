/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier
-/
import RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Exact.Basic

universe w u v

/-!
# Finite-length linear abelian categories

This module defines finite-length objects in an abelian category and proves finite-dimensionality
of morphism spaces in linear categories satisfying a Schur-type condition on simple objects.
-/

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.CategoryTheory.Abelian.FiniteLength

/-- Inductive predicate identifying finite-length objects in an abelian category. -/
inductive HasFiniteLength {C : Type u} [Category.{v} C] [Abelian C] : C → Prop
  | of_isZero {X : C} (h : Limits.IsZero X) : HasFiniteLength X
  | of_simple {X : C} (h : Simple X) : HasFiniteLength X
  | of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
      (h₁ : HasFiniteLength S.X₁) (h₃ : HasFiniteLength S.X₃) : HasFiniteLength S.X₂

/-- A condition on a linear category over a field with finite-length objects and scalar
simple-object endomorphisms. -/
class SchurFiniteLengthCategory (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
    [Linear k C] where
  /-- Every object in a Schur finite-length category has finite length. -/
  hasFiniteLength : ∀ X : C, HasFiniteLength X
  /-- In a Schur finite-length category, the endomorphism algebra of a simple object is equivalent
  to the base field. -/
  simpleEndAlgEquiv : ∀ (X : C), Simple X → Nonempty (End X ≃ₐ[k] k)

variable {k : Type w} [Field k]

section HomFinite

variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]

/-- An exact sequence with finite-dimensional endpoints has a finite-dimensional middle space. -/
theorem finiteDimensional_of_exact
    {A B D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [Module k A] [Module k B] [Module k D]
    {f : A →ₗ[k] B} {g : B →ₗ[k] D} (hexact : Function.Exact f g)
    [FiniteDimensional k A] [FiniteDimensional k D] :
    FiniteDimensional k B := by
  have hker : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp hexact
  haveI : FiniteDimensional k (B ⧸ LinearMap.range f) := by
    rw [← hker]
    exact Module.Finite.equiv (LinearMap.quotKerEquivRange g).symm
  exact Module.Finite.of_submodule_quotient (LinearMap.range f)

/-- The maps obtained by right composition from a short exact complex form an exact pair. -/
theorem shortExact_rightComp_exact (X : C) {S : ShortComplex C} (hS : S.ShortExact) :
    Function.Exact (Linear.rightComp k X S.f) (Linear.rightComp k X S.g) := by
  rw [LinearMap.exact_iff]
  ext b
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hb
    have hb' : b ≫ S.g = 0 := hb
    obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hS.fIsKernel b hb'
    refine ⟨a, ?_⟩
    change a ≫ S.f = b
    simpa using ha
  · rintro ⟨a, rfl⟩
    change (a ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]

/-- The maps obtained by left composition from a short exact complex form an exact pair. -/
theorem shortExact_leftComp_exact (Y : C) {S : ShortComplex C} (hS : S.ShortExact) :
    Function.Exact (Linear.leftComp k Y S.g) (Linear.leftComp k Y S.f) := by
  rw [LinearMap.exact_iff]
  ext b
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hb
    have hb' : S.f ≫ b = 0 := hb
    obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel b hb'
    refine ⟨a, ?_⟩
    change S.g ≫ a = b
    exact ha
  · rintro ⟨a, rfl⟩
    change S.f ≫ (S.g ≫ a) = 0
    rw [← Category.assoc, S.zero, zero_comp]

/-- Morphisms between simple objects are finite-dimensional when simple endomorphisms are
finite-dimensional. -/
theorem finiteDimensional_hom_of_simple
    (hfin : ∀ (Z : C), Simple Z → FiniteDimensional k (Z ⟶ Z))
    {X Y : C} (hX : Simple X) (hY : Simple Y) :
    FiniteDimensional k (X ⟶ Y) := by
  by_cases h : Nonempty (X ≅ Y)
  · obtain ⟨e⟩ := h
    haveI := hfin X hX
    refine Module.Finite.equiv (LinearEquiv.ofLinear
      (Linear.rightComp k X e.hom) (Linear.rightComp k X e.inv) ?_ ?_)
    · ext p
      change (p ≫ e.inv) ≫ e.hom = p
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    · ext p
      change (p ≫ e.hom) ≫ e.inv = p
      rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  · haveI := hX
    haveI := hY
    haveI : Subsingleton (X ⟶ Y) := by
      refine ⟨fun f g => ?_⟩
      have hz : ∀ p : X ⟶ Y, p = 0 := by
        intro p
        by_contra hp
        haveI : IsIso p := isIso_of_hom_simple hp
        exact h ⟨asIso p⟩
      rw [hz f, hz g]
    exact Module.Finite.of_finite

/-- Morphisms from a simple object to a finite-length object are finite-dimensional under the
stated hypothesis. -/
theorem finiteDimensional_hom_of_simple_of_hasFiniteLength
    (hfin : ∀ (Z : C), Simple Z → FiniteDimensional k (Z ⟶ Z))
    {X : C} (hX : Simple X) :
    ∀ {Y : C}, HasFiniteLength Y → FiniteDimensional k (X ⟶ Y) := by
  intro Y hY
  induction hY with
  | of_isZero h =>
      haveI : Subsingleton (X ⟶ _) := ⟨fun f g => h.eq_of_tgt f g⟩
      exact Module.Finite.of_finite
  | of_simple hYs =>
      exact finiteDimensional_hom_of_simple hfin hX hYs
  | of_shortExact hS _ _ ih₁ ih₃ =>
      haveI := ih₁
      haveI := ih₃
      exact finiteDimensional_of_exact (shortExact_rightComp_exact X hS)

/-- Finite-length source objects have finite-dimensional morphism spaces under the stated
simple-object hypotheses. -/
theorem finiteDimensional_hom_of_hasFiniteLength
    (hfin : ∀ (Z : C), Simple Z → FiniteDimensional k (Z ⟶ Z))
    (hlen : ∀ (Z : C), HasFiniteLength Z) (Y : C) :
    ∀ {X : C}, HasFiniteLength X → FiniteDimensional k (X ⟶ Y) := by
  intro X hX
  induction hX with
  | of_isZero h =>
      haveI : Subsingleton (_ ⟶ Y) := ⟨fun f g => h.eq_of_src f g⟩
      exact Module.Finite.of_finite
  | of_simple hXs =>
      exact finiteDimensional_hom_of_simple_of_hasFiniteLength hfin hXs (hlen Y)
  | of_shortExact hS _ _ ih₁ ih₃ =>
      haveI := ih₁
      haveI := ih₃
      exact finiteDimensional_of_exact (shortExact_leftComp_exact Y hS)

end HomFinite

namespace SchurFiniteLengthCategory

variable {C : Type u} [Category.{v} C]
  [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
  [Linear k C] [hCat : SchurFiniteLengthCategory k C]

/-- The endomorphism space of a simple object is finite-dimensional in a Schur finite-length
category. -/
theorem finiteDimensional_end (X : C) (hX : Simple X) :
    FiniteDimensional k (X ⟶ X) := by
  obtain ⟨e⟩ := hCat.simpleEndAlgEquiv X hX
  change FiniteDimensional k (End X)
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- Every morphism space in a Schur finite-length category is finite-dimensional. -/
theorem finiteDimensional_hom (X Y : C) : FiniteDimensional k (X ⟶ Y) :=
  finiteDimensional_hom_of_hasFiniteLength
    (fun Z hZ => finiteDimensional_end Z hZ) hCat.hasFiniteLength Y (hCat.hasFiniteLength X)

end SchurFiniteLengthCategory

end RepresentationTheory.CategoryTheory.Abelian.FiniteLength
