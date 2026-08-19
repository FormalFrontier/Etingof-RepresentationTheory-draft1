/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! Definitions and basic properties of induction and coinduction of group representations. -/

open Representation

/-- The representation of a group induced from a representation of a subgroup. -/
@[source_ref "Chapter5/Definition5.8.1" (role := supporting)]
noncomputable def RepresentationTheory.InductionAndCoinduction.induced
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) :
    Representation ℂ G (Representation.IndV H.subtype ρ) :=
  Representation.ind H.subtype ρ

/-- The representation of a group induced from a representation of a finite-index subgroup. -/
@[source_ref "Chapter5/Definition5.8.1" (role := supporting),
  source_ref "Chapter5/Introduction_5.8" (role := primary)]
noncomputable def RepresentationTheory.InductionAndCoinduction.finiteIndexInduced
    {G : Type*} [Group G]
    (H : Subgroup G) [H.FiniteIndex]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) :
    Representation ℂ G (Representation.IndV H.subtype ρ) :=
  RepresentationTheory.InductionAndCoinduction.induced H ρ

/-- The coinduced representation of a group on the corresponding equivariant function space. -/
@[source_ref "Chapter5/Definition5.8.1" (role := supporting),
  source_ref "Chapter5/Introduction_5.8" (role := primary)]
noncomputable def RepresentationTheory.InductionAndCoinduction.coinduced
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) :
    Representation ℂ G (Representation.coindV H.subtype ρ) :=
  Representation.coind H.subtype ρ

/-- A function belongs to the coinduced space exactly when it satisfies the subgroup equivariance relation. -/
@[source_ref "Chapter5/Discussion_verification_of_Ind" (role := supporting)]
theorem RepresentationTheory.InductionAndCoinduction.mem_coinducedSpace_iff
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (f : G → V) :
    f ∈ Representation.coindV H.subtype ρ ↔
      ∀ (h : H) (x : G), f (h * x) = ρ h (f x) :=
  Representation.mem_coindV H.subtype ρ f

/-- A function in the coinduced space intertwines left multiplication by a subgroup element with the subgroup action. -/
@[source_ref "Chapter5/Definition5.8.1" (role := supporting),
  source_ref "Chapter5/Discussion_verification_of_Ind" (role := supporting)]
theorem RepresentationTheory.InductionAndCoinduction.coinduced_equivariance
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V)
    (f : Representation.coindV H.subtype ρ) (h : H) (x : G) :
    f.val (h * x) = ρ h (f.val x) :=
  f.prop h x

/-- The coinduced action by a group element evaluates an equivariant function after right multiplication by that element. -/
@[simp, source_ref "Chapter5/Definition5.8.1" (role := supporting),
  source_ref "Chapter5/Discussion_verification_of_Ind" (role := supporting)]
theorem RepresentationTheory.InductionAndCoinduction.coinduced_apply
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V)
    (g : G) (f : Representation.coindV H.subtype ρ) (x : G) :
    (RepresentationTheory.InductionAndCoinduction.coinduced H ρ g f).val x = f.val (x * g) :=
  rfl

/-- The identity element acts trivially in the coinduced representation. -/
@[simp, source_ref "Chapter5/Discussion_verification_of_Ind" (role := supporting)]
theorem RepresentationTheory.InductionAndCoinduction.coinduced_one
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (f : Representation.coindV H.subtype ρ) :
    RepresentationTheory.InductionAndCoinduction.coinduced H ρ 1 f = f := by
  rw [map_one]
  rfl

/-- The coinduced action of a product is the composite of the two coinduced actions. -/
@[source_ref "Chapter5/Discussion_verification_of_Ind" (role := supporting)]
theorem RepresentationTheory.InductionAndCoinduction.coinduced_mul
    {G : Type*} [Group G]
    (H : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (g g' : G)
    (f : Representation.coindV H.subtype ρ) :
    RepresentationTheory.InductionAndCoinduction.coinduced H ρ (g * g') f =
      RepresentationTheory.InductionAndCoinduction.coinduced H ρ g
        (RepresentationTheory.InductionAndCoinduction.coinduced H ρ g' f) := by
  rw [map_mul]
  rfl

/-- For a finite-index subgroup, the induced and coinduced representations are isomorphic. -/
@[source_ref "Chapter5/Definition5.8.1" (role := primary),
  source_ref "Chapter5/Problem5.8.4" (role := supporting)]
noncomputable def RepresentationTheory.InductionAndCoinduction.finiteIndexInducedIsoCoinduced
    {G : Type*} [Group G]
    (H : Subgroup G) [DecidableRel (QuotientGroup.rightRel H)] [H.FiniteIndex]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) :
    Rep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ) ≅
      Rep.of (RepresentationTheory.InductionAndCoinduction.coinduced H ρ) :=
  Rep.indCoindIso (Rep.of ρ)
