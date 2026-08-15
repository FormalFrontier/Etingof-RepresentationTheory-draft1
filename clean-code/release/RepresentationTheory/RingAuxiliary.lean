/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Auxiliary relations between rings and algebras

This module defines auxiliary equivalence relations between module categories and their linear
refinements over a common field.
-/

universe u v

open CategoryTheory

/-- An auxiliary relation between two rings in the same universe. -/
def RepresentationTheory.RingAuxiliary.RingAuxiliary' (A : Type u) [Ring A]
    (B : Type u) [Ring B] : Prop :=
  Nonempty (FGModuleCat.{u} A ≌ FGModuleCat.{u} B)

/-- An auxiliary relation between two rings, with independently varying universe levels. -/
def RepresentationTheory.RingAuxiliary.RingAuxiliary (A : Type u) [Ring A]
    (B : Type v) [Ring B] : Prop :=
  Nonempty (ModuleCat.{max u v} A ≌ ModuleCat.{max u v} B)

/-- An auxiliary relation between two rings equipped with algebra structures over a common field. -/
def RepresentationTheory.RingAuxiliary.AlgebraAuxiliary (k : Type*) [Field k]
    (A : Type u) [Ring A] [Algebra k A]
    (B : Type u) [Ring B] [Algebra k B] : Prop :=
  ∃ (E : ModuleCat.{u} A ≌ ModuleCat.{u} B),
    haveI : E.functor.Additive :=
      letI : E.functor.IsEquivalence := E.isEquivalence_functor
      Functor.additive_of_preserves_binary_products E.functor
    E.functor.Linear k

/-- An auxiliary relation between two rings equipped with algebra structures over a common field. -/
def RepresentationTheory.RingAuxiliary.AlgebraAuxiliary' (k : Type*) [Field k]
    (A : Type u) [Ring A] [Algebra k A]
    (B : Type u) [Ring B] [Algebra k B] : Prop :=
  ∃ (E : FGModuleCat.{u} A ≌ FGModuleCat.{u} B), E.functor.Linear k

namespace RepresentationTheory.RingAuxiliary

/-- The auxiliary algebra relation implies the associated auxiliary relation on the underlying
rings. -/
lemma AlgebraAuxiliary.toRingAuxiliary {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : AlgebraAuxiliary k A B) : RingAuxiliary A B :=
  let ⟨E, _⟩ := h; ⟨E⟩

/-- The auxiliary algebra relation is unchanged when its two ring arguments are exchanged. -/
lemma AlgebraAuxiliary.symm {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : AlgebraAuxiliary k A B) : AlgebraAuxiliary k B A := by
  obtain ⟨E, hlin⟩ := h
  haveI : E.functor.Additive :=
    letI : E.functor.IsEquivalence := E.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E.functor
  haveI := hlin
  haveI : E.inverse.Additive := Equivalence.inverse_additive E
  exact ⟨E.symm, Equivalence.inverseLinear k E⟩

/-- The auxiliary algebra relation composes through an intermediate algebra. -/
lemma AlgebraAuxiliary.trans {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    {C : Type u} [Ring C] [Algebra k C]
    (h₁ : AlgebraAuxiliary k A B)
    (h₂ : AlgebraAuxiliary k B C) : AlgebraAuxiliary k A C := by
  obtain ⟨E₁, hlin₁⟩ := h₁
  obtain ⟨E₂, hlin₂⟩ := h₂
  haveI : E₁.functor.Additive :=
    letI : E₁.functor.IsEquivalence := E₁.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E₁.functor
  haveI := hlin₁
  haveI : E₂.functor.Additive :=
    letI : E₂.functor.IsEquivalence := E₂.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E₂.functor
  haveI := hlin₂
  refine ⟨E₁.trans E₂, ?_⟩
  change (E₁.functor ⋙ E₂.functor).Linear k
  infer_instance

/-- Every ring is related to itself by the auxiliary ring relation. -/
lemma RingAuxiliary'.refl (A : Type u) [Ring A] : RingAuxiliary' A A :=
  ⟨CategoryTheory.Equivalence.refl⟩

/-- The auxiliary ring relation is invariant under swapping its ring arguments. -/
lemma RingAuxiliary'.symm {A : Type u} [Ring A] {B : Type u} [Ring B]
    (h : RingAuxiliary' A B) : RingAuxiliary' B A :=
  h.map CategoryTheory.Equivalence.symm

/-- The auxiliary ring relation composes through an intermediate ring. -/
lemma RingAuxiliary'.trans {A : Type u} [Ring A] {B : Type u} [Ring B]
    {C : Type u} [Ring C]
    (h₁ : RingAuxiliary' A B) (h₂ : RingAuxiliary' B C) :
    RingAuxiliary' A C := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩

/-- The auxiliary algebra relation implies the associated auxiliary relation on the underlying
rings. -/
lemma AlgebraAuxiliary'.toRingAuxiliary {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : AlgebraAuxiliary' k A B) : RingAuxiliary' A B :=
  let ⟨E, _⟩ := h; ⟨E⟩

/-- The auxiliary algebra relation is unchanged when its two ring arguments are exchanged. -/
lemma AlgebraAuxiliary'.symm {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : AlgebraAuxiliary' k A B) : AlgebraAuxiliary' k B A := by
  obtain ⟨E, hlin⟩ := h
  haveI := hlin
  exact ⟨E.symm, Equivalence.inverseLinear k E⟩

/-- The auxiliary algebra relation composes through an intermediate algebra. -/
lemma AlgebraAuxiliary'.trans {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    {C : Type u} [Ring C] [Algebra k C]
    (h₁ : AlgebraAuxiliary' k A B)
    (h₂ : AlgebraAuxiliary' k B C) : AlgebraAuxiliary' k A C := by
  obtain ⟨E₁, hlin₁⟩ := h₁
  obtain ⟨E₂, hlin₂⟩ := h₂
  haveI := hlin₁
  haveI := hlin₂
  refine ⟨E₁.trans E₂, ?_⟩
  change (E₁.functor ⋙ E₂.functor).Linear k
  infer_instance

end RepresentationTheory.RingAuxiliary
