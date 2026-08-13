/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Auxiliary relations and types for module categories
-/

universe v u

open CategoryTheory

namespace RepresentationTheory.ModuleCat.Auxiliary

section

variable (R : Type u) [Ring R] [Small.{v} R]

/-- An auxiliary relation on objects of the category of modules over a small ring. -/
def auxiliaryModuleRelation' (X Y : ModuleCat.{v} R) : Prop :=
  Nontrivial (Abelian.Ext X Y 1)

/-- An auxiliary relation on objects of the category of modules over a small ring. -/
def auxiliaryModuleRelation'' (X Y : ModuleCat.{v} R) : Prop :=
  auxiliaryModuleRelation' R X Y ∨ auxiliaryModuleRelation' R Y X

/-- An auxiliary relation on objects of the category of modules over a small ring. -/
def auxiliaryModuleRelation''' (X Y : ModuleCat.{v} R) : Prop :=
  IsSimpleModule R X ∧ IsSimpleModule R Y ∧
    (auxiliaryModuleRelation'' R X Y ∨ Nonempty (X ≅ Y))

/-- An auxiliary relation on objects of the category of modules over a small ring. -/
def auxiliaryModuleRelation (X Y : ModuleCat.{v} R) : Prop :=
  Relation.EqvGen (auxiliaryModuleRelation''' R) X Y

/-- Establishes the auxiliary module relation between simple module objects joined by an isomorphism. -/
theorem auxiliaryModuleRelation_of_iso {X Y : ModuleCat.{v} R}
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y) (e : X ≅ Y) :
    auxiliaryModuleRelation R X Y :=
  Relation.EqvGen.rel _ _ ⟨hX, hY, Or.inr ⟨e⟩⟩

/-- Transfers one auxiliary module relation to another between simple module objects. -/
theorem auxiliaryModuleRelation_of_auxiliaryModuleRelation'' {X Y : ModuleCat.{v} R}
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y)
    (h : auxiliaryModuleRelation'' R X Y) :
    auxiliaryModuleRelation R X Y :=
  Relation.EqvGen.rel _ _ ⟨hX, hY, Or.inl h⟩

/-- The auxiliary relation on module objects is an equivalence relation. -/
theorem auxiliaryModuleRelation_equivalence :
    @Equivalence (ModuleCat.{v} R) (auxiliaryModuleRelation R) :=
  Relation.EqvGen.is_equivalence _

/-- Degree-one extensions between simple module objects form a subsingleton when the auxiliary relation does not hold. -/
theorem subsingleton_ext_one_of_not_auxiliaryModuleRelation {S T : ModuleCat.{v} R}
    (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    (hST : ¬ auxiliaryModuleRelation R S T) :
    Subsingleton (Abelian.Ext S T 1) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  exact hST (auxiliaryModuleRelation_of_auxiliaryModuleRelation'' (R := R) hS hT
    (Or.inl (show auxiliaryModuleRelation' R S T from hnt)))

end

section Blocks

variable (R : Type u) [Ring R] [Small.{v} R]

/-- An auxiliary relation on objects of the category of modules over a ring. -/
def auxiliaryModuleRelationOverRing (M S : ModuleCat.{v} R) : Prop :=
  IsSimpleModule R S ∧ ∃ (N₁ N₂ : Submodule R M) (_ : N₁ ≤ N₂),
    Nonempty ((↥N₂ ⧸ N₁.comap N₂.subtype) ≃ₗ[R] S)

/-- An auxiliary relation on objects of the category of modules over a small ring. -/
def auxiliaryModuleRelation'''' (S M : ModuleCat.{v} R) : Prop :=
  ∀ T : ModuleCat.{v} R, auxiliaryModuleRelationOverRing R M T → auxiliaryModuleRelation R T S

/-- An auxiliary type associated with a ring. -/
def AuxiliaryType : Type (max u (v + 1)) :=
  { X : ModuleCat.{v} R // IsSimpleModule R X }

/-- A setoid on the auxiliary type associated with a small ring. -/
def auxiliaryTypeSetoid : Setoid (AuxiliaryType.{v} R) where
  r X Y := auxiliaryModuleRelation R X.1 Y.1
  iseqv :=
    ⟨fun X => (auxiliaryModuleRelation_equivalence R).refl X.1,
      fun h => (auxiliaryModuleRelation_equivalence R).symm h,
      fun h₁ h₂ => (auxiliaryModuleRelation_equivalence R).trans h₁ h₂⟩

/-- An auxiliary type associated with a small ring. -/
def AuxiliaryModuleType : Type _ :=
  Quotient (auxiliaryTypeSetoid.{v} R)

end Blocks

end RepresentationTheory.ModuleCat.Auxiliary
