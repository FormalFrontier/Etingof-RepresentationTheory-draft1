/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.ConjugacyClassTrace

/-!
# Conjugacy-class cardinality bounds
-/

open MonoidAlgebra

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace RepresentationTheory.GroupTheory.ConjugacyClassBounds

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq G]

/-- A finite linearly independent family of auxiliary linear maps has cardinality bounded by the conjugacy classes. -/
theorem fintypeCard_le_card_conjClasses_of_linearIndependent_auxiliary
    {ι : Type*} [Fintype ι]
    {f : ι → (RepresentationTheory.ConjugacyClassTrace.AuxiliaryClassQuotient k G →ₗ[k] k)}
    (hf : LinearIndependent k f) :
    Fintype.card ι ≤ Nat.card (ConjClasses G) := by
  haveI : Module.Finite k
      (RepresentationTheory.ConjugacyClassTrace.AuxiliaryClassQuotient k G →ₗ[k] k) :=
    inferInstance
  have h1 : Fintype.card ι ≤ Module.finrank k
      (RepresentationTheory.ConjugacyClassTrace.AuxiliaryClassQuotient k G →ₗ[k] k) :=
    hf.fintype_card_le_finrank
  rwa [Module.finrank_linearMap_self,
    RepresentationTheory.ConjugacyClassTrace.finrank_auxiliaryClassQuotient] at h1

/-- A finite linearly independent family of auxiliary linear maps has cardinality bounded by the conjugacy classes. -/
theorem card_le_card_conjClasses_of_linearIndependent_auxiliary
    {ι : Type*} [Finite ι]
    {f : ι → (RepresentationTheory.ConjugacyClassTrace.AuxiliaryClassQuotient k G →ₗ[k] k)}
    (hf : LinearIndependent k f) :
    Nat.card ι ≤ Nat.card (ConjClasses G) := by
  cases nonempty_fintype ι
  rw [Nat.card_eq_fintype_card]
  exact fintypeCard_le_card_conjClasses_of_linearIndependent_auxiliary hf

/-- A finite family with linearly independent associated maps has cardinality bounded by the conjugacy classes. -/
theorem fintypeCard_le_card_conjClasses_of_linearIndependent_family
    {ι : Type*} [Fintype ι]
    {S : ι → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module (MonoidAlgebra k G) (S i)] [∀ i, IsScalarTower k (MonoidAlgebra k G) (S i)]
    [∀ i, Module.Finite k (S i)]
    (h : LinearIndependent k (fun i =>
      (RepresentationTheory.ConjugacyClassTrace.auxiliaryModuleTrace k (S i) :
        RepresentationTheory.ConjugacyClassTrace.AuxiliaryClassQuotient k G →ₗ[k] k))) :
    Fintype.card ι ≤ Nat.card (ConjClasses G) :=
  fintypeCard_le_card_conjClasses_of_linearIndependent_auxiliary h

end RepresentationTheory.GroupTheory.ConjugacyClassBounds
