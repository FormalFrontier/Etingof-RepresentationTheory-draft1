/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Auxiliary
import RepresentationTheory.RingAuxiliary
import RepresentationTheory.FieldAlgebraProperties
import RepresentationTheory.MoritaEquivalence
import RepresentationTheory.RingTheory.ElementProperties
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.LinearAlgebra.Dimension.Finrank

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.SimpleModule.Rank

/-! # Finite algebra candidates -/

set_option backward.isDefEq.respectTransparency false

universe u v

namespace RepresentationTheory.Auxiliary.FiniteAlgebraCandidates

variable (k : Type u) [Field k]

/-- The relation holds when both arguments are the same ring. -/
lemma _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary.refl (A : Type u) [Ring A] :
    RepresentationTheory.RingAuxiliary.RingAuxiliary A A :=
  ⟨CategoryTheory.Equivalence.refl⟩

/-- Reverses an instance of the relation between two rings. -/
lemma _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary.symm
    {A : Type u} [Ring A] {B : Type u} [Ring B]
    (h : RepresentationTheory.RingAuxiliary.RingAuxiliary A B) :
    RepresentationTheory.RingAuxiliary.RingAuxiliary B A :=
  h.map CategoryTheory.Equivalence.symm

/-- Composes two compatible instances of the relation between rings. -/
lemma _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary.trans
    {A : Type u} [Ring A] {B : Type u} [Ring B]
    {C : Type u} [Ring C]
    (h₁ : RepresentationTheory.RingAuxiliary.RingAuxiliary A B)
    (h₂ : RepresentationTheory.RingAuxiliary.RingAuxiliary B C) :
    RepresentationTheory.RingAuxiliary.RingAuxiliary A C := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩

/-- The displayed relation holds for a field paired with itself. -/
lemma Auxiliary.relation_self :
    RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty' k k := by
  intro M _ hModA hSimp hModK hST
  have : hModA = hModK := by
    ext c m
    have h := hST.1 c (1 : k) m
    simp only [smul_eq_mul, mul_one, one_smul] at h
    exact h
  subst this
  exact isSimpleModule_iff_finrank_eq_one.mp hSimp

private lemma Auxiliary.idempotent_eq_one_of_cornerSubmodule_eq_top
    {A : Type u} [Ring A] [Algebra k A]
    {e : A} (he : IsIdempotentElem e)
    (htop : RepresentationTheory.RingTheory.Idempotent.sandwichSubmodule (k := k) e = ⊤) :
    e = 1 := by
  have h1 : (1 : A) ∈
      RepresentationTheory.RingTheory.Idempotent.sandwichSubmodule (k := k) e :=
    htop ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ :=
    (RepresentationTheory.RingTheory.Idempotent.mem_sandwichSubmodule_iff e 1).mp h1
  have step1 : e * (e * a * e) = e * e * (a * e) := by
    rw [mul_assoc e a e, ← mul_assoc e e (a * e)]
  have step2 : e * e * (a * e) = e * (a * e) := by
    rw [he.eq]
  have step3 : e * (a * e) = e * a * e := by
    rw [mul_assoc]
  calc e = e * 1 := (mul_one e).symm
    _ = e * (e * a * e) := by rw [ha]
    _ = e * (a * e) := by rw [step1, step2]
    _ = e * a * e := step3
    _ = 1 := ha

private noncomputable def Auxiliary.cornerRingAlgEquivOfUnit
    {A : Type u} [Ring A] [Algebra k A] (he : IsIdempotentElem (1 : A)) :
    @AlgEquiv k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) (1 : A)) A _
      (RepresentationTheory.RingTheory.Idempotent.submodule.ring he).toSemiring _
      (@RepresentationTheory.RingTheory.Idempotent.submodule.algebra k _ A _ _ 1 he) _ := by
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) (1 : A)) :=
    RepresentationTheory.RingTheory.Idempotent.submodule.ring he
  letI : Algebra k
      (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) (1 : A)) :=
    @RepresentationTheory.RingTheory.Idempotent.submodule.algebra k _ A _ _ 1 he
  have hmem : ∀ a : A,
      a ∈ RepresentationTheory.RingTheory.Idempotent.sandwichSubmodule (k := k) (1 : A) :=
    fun a =>
      (RepresentationTheory.RingTheory.Idempotent.mem_sandwichSubmodule_iff 1 a).mpr
        ⟨a, by simp⟩
  exact {
    toFun := fun x => (x : A)
    invFun := fun a => ⟨a, hmem a⟩
    left_inv := fun x => by ext; rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun r => by
      simp only [Algebra.algebraMap_eq_smul_one]
      rfl
  }

/-- Guarantees a finite algebraic candidate meeting the two displayed conditions. -/
theorem Auxiliary.exists_type_with_two_conditions
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] [IsAlgClosed k] :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧
        RepresentationTheory.RingAuxiliary.RingAuxiliary A B :=
  RepresentationTheory.RingTheory.ElementProperties.exists_nested_witnesses_with_two_conditions
    k A

/-- Shows that two candidates satisfying the stated pair of shared conditions are algebra equivalent. -/
theorem Auxiliary.algEquiv_of_two_shared_conditions [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k B₁)
    (_hB₂ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k B₂)
    (h₁ : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B₁)
    (h₂ : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B₂) :
    Nonempty (B₁ ≃ₐ[k] B₂) := by
  have hMor : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k B₁ B₂ :=
    h₁.symm.trans h₂
  obtain ⟨e₁, he₁, ⟨φ₁⟩⟩ :=
    @RepresentationTheory.MoritaEquivalence.exists_algEquiv_subtype_associated_to_element
      k _ _ B₁ _ _ _ B₂ _ _ _ _hB₂ hMor
  obtain ⟨e₂, he₂, ⟨φ₂⟩⟩ :=
    @RepresentationTheory.MoritaEquivalence.exists_algEquiv_subtype_associated_to_element
      k _ _ B₂ _ _ _ B₁ _ _ _ _hB₁ hMor.symm
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e₁) :=
    RepresentationTheory.RingTheory.Idempotent.submodule.ring he₁
  letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e₁) :=
    RepresentationTheory.RingTheory.Idempotent.submodule.algebra he₁
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e₂) :=
    RepresentationTheory.RingTheory.Idempotent.submodule.ring he₂
  letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e₂) :=
    RepresentationTheory.RingTheory.Idempotent.submodule.algebra he₂
  have hle₁ : Module.finrank k B₂ ≤ Module.finrank k B₁ := by
    calc Module.finrank k B₂
        = Module.finrank k
            (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e₁) :=
          LinearEquiv.finrank_eq φ₁.toLinearEquiv
      _ ≤ Module.finrank k B₁ :=
        RepresentationTheory.RingTheory.Idempotent.submodule.finrank_le
  have hle₂ : Module.finrank k B₁ ≤ Module.finrank k B₂ := by
    calc Module.finrank k B₁
        = Module.finrank k
            (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e₂) :=
          LinearEquiv.finrank_eq φ₂.toLinearEquiv
      _ ≤ Module.finrank k B₂ :=
        RepresentationTheory.RingTheory.Idempotent.submodule.finrank_le
  have heq : Module.finrank k
      (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e₁) =
        Module.finrank k B₁ := by
    linarith [LinearEquiv.finrank_eq φ₁.toLinearEquiv]
  have htop :
      RepresentationTheory.RingTheory.Idempotent.sandwichSubmodule (k := k) e₁ = ⊤ :=
    Submodule.eq_top_of_finrank_eq heq
  have he₁_eq : e₁ = 1 :=
    Auxiliary.idempotent_eq_one_of_cornerSubmodule_eq_top (k := k) he₁ htop
  subst he₁_eq
  exact ⟨(φ₁.trans (Auxiliary.cornerRingAlgEquivOfUnit (k := k) he₁)).symm⟩

/-- Bounds the rank of a candidate by that of the ambient algebra under the stated conditions. -/
theorem Auxiliary.finrank_le_of_two_conditions [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B : Type u) [Ring B] [Algebra k B] [Module.Finite k B]
    (_hB : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k B)
    (hMor : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B) :
    Module.finrank k B ≤ Module.finrank k A := by
  obtain ⟨e, he, ⟨φ⟩⟩ :=
    @RepresentationTheory.MoritaEquivalence.exists_algEquiv_subtype_associated_to_element
      k _ _ A _ _ _ B _ _ _ _hB hMor
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) :=
    RepresentationTheory.RingTheory.Idempotent.submodule.ring he
  letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) :=
    RepresentationTheory.RingTheory.Idempotent.submodule.algebra he
  calc Module.finrank k B
      = Module.finrank k
          (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) :=
        LinearEquiv.finrank_eq φ.toLinearEquiv
    _ ≤ Module.finrank k A :=
      RepresentationTheory.RingTheory.Idempotent.submodule.finrank_le

/-- Guarantees a finite algebraic candidate meeting the three displayed conditions. -/
theorem Auxiliary.exists_type_with_three_conditions [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k B ∧
        RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧
          RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B :=
  RepresentationTheory.RingTheory.ElementProperties.exists_nested_witnesses_with_three_conditions
    k A

/-- Shows that two candidates satisfying the other stated pair of shared conditions are algebra equivalent. -/
theorem Auxiliary.algEquiv_of_two_shared_conditions' [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (hB₁ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B₁)
    (hB₂ : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B₂)
    (h₁ : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B₁)
    (h₂ : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B₂) :
    Nonempty (B₁ ≃ₐ[k] B₂) :=
  Auxiliary.algEquiv_of_two_shared_conditions k A B₁ B₂
    hB₁.toAuxiliaryOfIsAlgClosed hB₂.toAuxiliaryOfIsAlgClosed h₁ h₂

/-- Bounds the rank of a candidate by that of the ambient algebra under the other stated conditions. -/
theorem Auxiliary.finrank_le_of_two_conditions' [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B : Type u) [Ring B] [Algebra k B] [Module.Finite k B]
    (hB : RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B)
    (hMor : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B) :
    Module.finrank k B ≤ Module.finrank k A :=
  Auxiliary.finrank_le_of_two_conditions k A B hB.toAuxiliaryOfIsAlgClosed hMor

/-- Produces a finite algebraic candidate satisfying the displayed conditions, with a rank bound and uniqueness up to algebra equivalence among the specified candidates. -/
theorem Auxiliary.exists_type_with_three_conditions_finrank_le_and_unique [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k B ∧
        RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧
          RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B ∧
            Module.finrank k B ≤ Module.finrank k A ∧
              ∀ (B' : Type u) (_ : Ring B') (_ : Algebra k B') (_ : Module.Finite k B'),
                RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B' →
                  RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B' →
                    Nonempty (B' ≃ₐ[k] B) := by
  obtain ⟨B, instR, instA, instF, hsplit, hbasic, hmor⟩ :=
    Auxiliary.exists_type_with_three_conditions k A
  refine ⟨B, instR, instA, instF, hsplit, hbasic, hmor, ?_, ?_⟩
  · exact Auxiliary.finrank_le_of_two_conditions k A B hsplit hmor
  · intro B' _ _ _ hbasic' hmor'
    exact Auxiliary.algEquiv_of_two_shared_conditions k A B' B
      hbasic'.toAuxiliaryOfIsAlgClosed hsplit hmor' hmor

end RepresentationTheory.Auxiliary.FiniteAlgebraCandidates
