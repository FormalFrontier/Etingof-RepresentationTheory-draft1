/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import RepresentationTheory.Algebra.Homology.TensorProductConstruction
import RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses
import RepresentationTheory.Algebra.ModuleCategory.Auxiliary

set_option backward.isDefEq.respectTransparency false

/-!
# Additivity of derived functor constructions

This module proves additivity of projective resolutions and left-derived functors, and applies it
to the degreewise module-group construction in both module arguments.
-/

open CategoryTheory Limits

namespace RepresentationTheory.CategoryTheory.HomologicalAlgebra.DerivedFunctor.Additivity

set_option linter.dupNamespace false

namespace CategoryTheory.HomologicalAlgebra.DerivedFunctor

universe u v u' v'

open RepresentationTheory.Algebra.Homology.TensorProductConstruction
open RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary

section ProjectiveResolutions

variable (C : Type u) [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]

/-- The functor assigning projective resolutions is additive. -/
instance projectiveResolutions_additive :
    (_root_.CategoryTheory.projectiveResolutions C).Additive where
  map_add {X Y f g} := by
    dsimp only [_root_.CategoryTheory.projectiveResolutions]
    rw [← Functor.map_add]
    apply HomotopyCategory.eq_of_homotopy
    refine ProjectiveResolution.liftHomotopy (f + g) _ _ (by simp) ?_
    rw [Preadditive.add_comp, ProjectiveResolution.lift_commutes,
      ProjectiveResolution.lift_commutes, ← Preadditive.comp_add, ← Functor.map_add]

end ProjectiveResolutions

section LeftDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The left-derived functor of an additive functor is additive in every degree. -/
instance leftDerived_additive (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.leftDerived n).Additive := by
  dsimp only [Functor.leftDerived, Functor.leftDerivedToHomotopyCategory]
  infer_instance

omit [HasProjectiveResolutions C] in
/-- Mapping homological complexes sends the sum of natural transformations to the sum of the
induced transformations. -/
lemma mapHomologicalComplex_natTrans_add {I : Type*} (c : ComplexShape I) {F G : C ⥤ D}
    [F.Additive] [G.Additive] (α β : F ⟶ G) :
    NatTrans.mapHomologicalComplex (α + β) c =
      NatTrans.mapHomologicalComplex α c + NatTrans.mapHomologicalComplex β c := by
  ext K i
  rfl

/-- Deriving the sum of two natural transformations agrees with the sum of their derived
transformations. -/
lemma leftDerived_natTrans_add {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α β : F ⟶ G) (n : ℕ) :
    NatTrans.leftDerived (α + β) n = NatTrans.leftDerived α n + NatTrans.leftDerived β n := by
  ext X
  rw [ProjectiveResolution.leftDerived_app_eq (α + β) (projectiveResolution X) n,
    mapHomologicalComplex_natTrans_add]
  change _ ≫ (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
      ((NatTrans.mapHomologicalComplex α _).app _ +
        (NatTrans.mapHomologicalComplex β _).app _) ≫ _ = _
  rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
    ← ProjectiveResolution.leftDerived_app_eq α (projectiveResolution X) n,
    ← ProjectiveResolution.leftDerived_app_eq β (projectiveResolution X) n]
  rfl

end LeftDerived

variable (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ)

/-- The displayed functor is additive. -/
instance objectFunctor_additive :
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor
      A N n).Additive := by
  dsimp only [
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor]
  infer_instance

/-- An isomorphism between the value of the displayed object construction on a binary biproduct and
the biproduct of its values. -/
noncomputable def objectConstruction_biprod (M₁ M₂ : ModuleCat.{u} Aᵐᵒᵖ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup
        A N (M₁ ⊞ M₂) n ≅
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup
          A N M₁ n ⊞
        RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup
          A N M₂ n :=
  letI := preservesBinaryBiproduct_of_preservesBiproduct
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor
      A N n) M₁ M₂
  (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor
    A N n).mapBiprod M₁ M₂

/-- An isomorphism between the displayed object construction on a finite biproduct and the
biproduct of the corresponding functor values. -/
noncomputable def objectFunctor_biproduct {I : Type} [Finite I]
    (M : I → ModuleCat.{u} Aᵐᵒᵖ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup
        A N (⨁ M) n ≅
      ⨁ ((degreewiseModuleGroupFunctor A N n).obj ∘ M) :=
  (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor
    A N n).mapBiproduct M

section SecondArgument

variable {A}
variable {N₁ N₂ : Type u} [AddCommGroup N₁] [Module A N₁]
  [AddCommGroup N₂] [Module A N₂]

/-- Two natural transformations between the displayed tensor-product functors agree when their
components agree on pure tensors. -/
private lemma linearMapToHom_ext {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N']
    {α β :
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
          A N ⟶
        RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
          A N'}
    (h : ∀ (M : ModuleCat.{u} Aᵐᵒᵖ) (m : M) (x : N),
      α.app M
          (TensorProduct.tmul ℤ m x :
            RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
              A N M) =
        β.app M
          (TensorProduct.tmul ℤ m x :
            RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
              A N M)) : α = β := by
  ext M z
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  induction y with
  | zero => simp
  | tmul m x => exact h M m x
  | add a b ha hb =>
    rw [show
        ((a + b : TensorProduct ℤ M N) :
            RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
              A N M) =
          (a :
              RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
                A N M) + b
        from map_add (QuotientAddGroup.mk' _) a b,
      map_add, map_add, ha, hb]

/-- The identity linear map is assigned the identity morphism. -/
@[simp]
lemma linearMapToHom_id (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N] :
    linearMapToAuxiliaryHom A (LinearMap.id : N →ₗ[A] N) =
      𝟙 (moduleConstructionFunctor A N) :=
  linearMapToHom_ext fun _ _ _ => rfl

/-- The morphism assigned to a composite of linear maps is the composite of the assigned
morphisms. -/
@[simp]
lemma linearMapToHom_comp {N₃ : Type u} [AddCommGroup N₃] [Module A N₃]
    (g : N₁ →ₗ[A] N₂) (g' : N₂ →ₗ[A] N₃) :
    linearMapToAuxiliaryHom A (g'.comp g) =
      linearMapToAuxiliaryHom A g ≫ linearMapToAuxiliaryHom A g' :=
  linearMapToHom_ext fun _ _ _ => rfl

/-- The morphism assigned to a sum of linear maps is the sum of the assigned morphisms. -/
@[simp]
lemma linearMapToHom_add (g g' : N₁ →ₗ[A] N₂) :
    linearMapToAuxiliaryHom A (g + g') =
      linearMapToAuxiliaryHom A g + linearMapToAuxiliaryHom A g' :=
  linearMapToHom_ext fun M m x => by
    change
      (TensorProduct.tmul ℤ m (g x + g' x) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
            A N₂ M) = _
    rw [TensorProduct.tmul_add]
    exact map_add
      (QuotientAddGroup.mk'
        (RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup
          A N₂ M)) _ _

variable (M : ModuleCat.{u} Aᵐᵒᵖ)

/-- The objectwise morphism assigned to the identity linear map is the identity morphism. -/
@[simp]
lemma linearMapToObjectHom_id (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (n : ℕ) (M : ModuleCat.{u} Aᵐᵒᵖ) :
    linearMapToAuxiliaryIndexedHom A (LinearMap.id : N →ₗ[A] N) n M = 𝟙 _ := by
  rw [linearMapToAuxiliaryIndexedHom, linearMapToHom_id, NatTrans.leftDerived_id]
  rfl

/-- The objectwise morphism assigned to a composite of linear maps is the composite of the assigned
morphisms. -/
@[simp]
lemma linearMapToObjectHom_comp {N₃ : Type u} [AddCommGroup N₃] [Module A N₃]
    (g : N₁ →ₗ[A] N₂) (g' : N₂ →ₗ[A] N₃) (n : ℕ) :
    linearMapToAuxiliaryIndexedHom A (g'.comp g) n M =
      linearMapToAuxiliaryIndexedHom A g n M ≫
        linearMapToAuxiliaryIndexedHom A g' n M := by
  rw [linearMapToAuxiliaryIndexedHom, linearMapToHom_comp, NatTrans.leftDerived_comp]
  rfl

/-- The objectwise morphism assigned to a sum of linear maps is the sum of the assigned
morphisms. -/
@[simp]
lemma linearMapToObjectHom_add (g g' : N₁ →ₗ[A] N₂) (n : ℕ) :
    linearMapToAuxiliaryIndexedHom A (g + g') n M =
      linearMapToAuxiliaryIndexedHom A g n M +
        linearMapToAuxiliaryIndexedHom A g' n M := by
  rw [linearMapToAuxiliaryIndexedHom, linearMapToHom_add, leftDerived_natTrans_add]
  rfl

/-- An additive homomorphism from linear maps to morphisms between values of the displayed object
construction. -/
noncomputable def linearMapToObjectHom (n : ℕ) :
    (N₁ →ₗ[A] N₂) →+
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup
          A N₁ M n ⟶
        RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup
          A N₂ M n) :=
  AddMonoidHom.mk'
    (fun g => linearMapToAuxiliaryIndexedHom A g n M)
    fun g g' => linearMapToObjectHom_add M g g' n

/-- The objectwise morphism assigned to the zero linear map is zero. -/
@[simp]
lemma linearMapToObjectHom_zero (n : ℕ) :
    linearMapToAuxiliaryIndexedHom A (0 : N₁ →ₗ[A] N₂) n M = 0 :=
  (linearMapToObjectHom M n).map_zero

/-- An isomorphism between the displayed construction on a product of two modules and the
biproduct of its values on the factors. -/
noncomputable def objectConstruction_prod_biprod (n : ℕ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup
        A (N₁ × N₂) M n ≅
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup
          A N₁ M n ⊞
        RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup
          A N₂ M n where
  hom := biprod.lift
    (linearMapToAuxiliaryIndexedHom A (LinearMap.fst A N₁ N₂) n M)
    (linearMapToAuxiliaryIndexedHom A (LinearMap.snd A N₁ N₂) n M)
  inv := biprod.desc
    (linearMapToAuxiliaryIndexedHom A (LinearMap.inl A N₁ N₂) n M)
    (linearMapToAuxiliaryIndexedHom A (LinearMap.inr A N₁ N₂) n M)
  hom_inv_id := by
    rw [biprod.lift_desc, ← linearMapToObjectHom_comp, ← linearMapToObjectHom_comp,
      ← linearMapToObjectHom_add]
    rw [show (LinearMap.inl A N₁ N₂).comp (LinearMap.fst A N₁ N₂) +
        (LinearMap.inr A N₁ N₂).comp (LinearMap.snd A N₁ N₂) = LinearMap.id from by
      ext x <;> simp]
    exact linearMapToObjectHom_id A (N₁ × N₂) n M
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [← linearMapToObjectHom_comp, LinearMap.fst_comp_inl, LinearMap.snd_comp_inl,
        LinearMap.fst_comp_inr, LinearMap.snd_comp_inr]

end SecondArgument

section FiniteSecondArgument

variable {I : Type} [Fintype I] [DecidableEq I]
variable (N : I → Type u) [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]

/-- An isomorphism between the displayed construction on a finite dependent function module and the
biproduct of its values on the factors. -/
noncomputable def objectConstruction_pi_biproduct (M : ModuleCat.{u} Aᵐᵒᵖ) (n : ℕ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup
        A (∀ i, N i) M n ≅
      ⨁ fun i =>
        RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup
          A (N i) M n where
  hom := biproduct.lift fun i =>
    linearMapToAuxiliaryIndexedHom A (LinearMap.proj i) n M
  inv := biproduct.desc fun i =>
    linearMapToAuxiliaryIndexedHom A (LinearMap.single A N i) n M
  hom_inv_id := by
    rw [biproduct.lift_desc]
    have h : ∀ i : I,
        linearMapToAuxiliaryIndexedHom A (LinearMap.proj (R := A) (φ := N) i) n M ≫
            linearMapToAuxiliaryIndexedHom A (LinearMap.single A N i) n M =
          linearMapToObjectHom M n
            ((LinearMap.single A N i).comp (LinearMap.proj i)) :=
      fun i => (linearMapToObjectHom_comp M _ _ n).symm
    simp_rw [h]
    rw [← map_sum (linearMapToObjectHom M n),
      show ∑ i : I, (LinearMap.single A N i).comp (LinearMap.proj i) = LinearMap.id from
        LinearMap.ext fun x => by
          simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
            LinearMap.coe_single, LinearMap.id_apply]
          exact Finset.univ_sum_single x]
    exact linearMapToObjectHom_id A (∀ i, N i) n M
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
    rw [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π,
      ← linearMapToObjectHom_comp, Category.comp_id]
    rcases eq_or_ne i j with rfl | hij
    · rw [LinearMap.proj_comp_single_same, biproduct.ι_π_self, linearMapToObjectHom_id]
    · rw [LinearMap.proj_comp_single_ne A N j i hij.symm, linearMapToObjectHom_zero,
        biproduct.ι_π_ne _ hij]

end FiniteSecondArgument

end CategoryTheory.HomologicalAlgebra.DerivedFunctor

end RepresentationTheory.CategoryTheory.HomologicalAlgebra.DerivedFunctor.Additivity
