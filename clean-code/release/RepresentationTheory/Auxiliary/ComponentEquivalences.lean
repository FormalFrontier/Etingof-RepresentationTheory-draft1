/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID
import RepresentationTheory.CategoryTheory.HomologicalAlgebra.DerivedFunctor.Additivity

universe u

namespace RepresentationTheory.Auxiliary.ComponentEquivalences

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RepresentationTheory.Algebra.Module.DirectSumData

/-- Equivalence between the carrier of a finite biproduct and the corresponding function type. -/
noncomputable def biproductAddEquiv {J : Type} [Finite J] (f : J → AddCommGrpCat.{u}) :
    (⨁ f : AddCommGrpCat.{u}) ≃+ ∀ j, f j :=
  (AddCommGrpCat.biproductIsoPi f).addCommGroupIsoToAddEquiv

section TorCongr

variable {A : Type u} [Ring A]

/-- Transports the displayed construction along an isomorphism of module objects. -/
noncomputable abbrev mapIso (N : Type u) [AddCommGroup N] [Module A N]
    {M₁ M₂ : ModuleCat.{u} Aᵐᵒᵖ} (e : M₁ ≅ M₂) (n : ℕ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup.{u} A N M₁ n ≅ RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup.{u} A N M₂ n :=
  (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor.{u} A N n).mapIso e

/-- Transports the displayed construction along a linear equivalence of coefficient modules. -/
noncomputable def mapLinearEquiv {N₁ N₂ : Type u} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] (e : N₁ ≃ₗ[A] N₂) (M : ModuleCat.{u} Aᵐᵒᵖ) (n : ℕ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup.{u} A N₁ M n ≅ RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup.{u} A N₂ M n where
  hom := RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A (e : N₁ →ₗ[A] N₂) n M
  inv := RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A (e.symm : N₂ →ₗ[A] N₁) n M
  hom_inv_id := by
    rw [← RepresentationTheory.CategoryTheory.HomologicalAlgebra.DerivedFunctor.Additivity.CategoryTheory.HomologicalAlgebra.DerivedFunctor.linearMapToObjectHom_comp M (e : N₁ →ₗ[A] N₂) (e.symm : N₂ →ₗ[A] N₁) n,
      show (e.symm : N₂ →ₗ[A] N₁).comp (e : N₁ →ₗ[A] N₂) = LinearMap.id from
        LinearMap.ext fun x => e.symm_apply_apply x]
    exact RepresentationTheory.CategoryTheory.HomologicalAlgebra.DerivedFunctor.Additivity.CategoryTheory.HomologicalAlgebra.DerivedFunctor.linearMapToObjectHom_id A N₁ n M
  inv_hom_id := by
    rw [← RepresentationTheory.CategoryTheory.HomologicalAlgebra.DerivedFunctor.Additivity.CategoryTheory.HomologicalAlgebra.DerivedFunctor.linearMapToObjectHom_comp M (e.symm : N₂ →ₗ[A] N₁) (e : N₁ →ₗ[A] N₂) n,
      show (e : N₁ →ₗ[A] N₂).comp (e.symm : N₂ →ₗ[A] N₁) = LinearMap.id from
        LinearMap.ext fun x => e.apply_symm_apply x]
    exact RepresentationTheory.CategoryTheory.HomologicalAlgebra.DerivedFunctor.Additivity.CategoryTheory.HomologicalAlgebra.DerivedFunctor.linearMapToObjectHom_id A N₂ n M

end TorCongr

section Reduction

variable {A : Type} [CommRing A] {M N : Type} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

/-- Equivalence from the ambient module to the function of displayed component carriers. -/
noncomputable def _root_.RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData.linearEquiv (D : Module.DirectSumData A M) :
    M ≃ₗ[A] ∀ j : D.summandIndex, (D.summand j : Type) :=
  D.linearEquivFinFunProdQuotient ≪≫ₗ
    (LinearEquiv.sumPiEquivProdPi A (Fin D.natParameter) D.Index
      (fun j => (D.summand j : Type))).symm

/-- Identifies a displayed component with the quotient by the span of its given element. -/
noncomputable def _root_.RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData.componentIso (D : Module.DirectSumData A M) (j : D.summandIndex) :
    D.oppositeSummand j ≅ RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleAsOpposite A (A ⧸ Ideal.span {D.combined_coefficient j}) :=
  (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite A).mapIso (D.component_iso_quotient_span j)

/-- Equivalence between the construction at an ambient object and the family at its indexed components. -/
noncomputable def addEquiv (D : Module.DirectSumData A M) (Y : Type)
    [AddCommGroup Y] [Module A Y] (n : ℕ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A Y (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleAsOpposite A M) n ≃+ ∀ j : D.summandIndex, RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A Y (D.oppositeSummand j) n :=
  (mapIso Y D.oppositeModuleIsoBiproduct n).addCommGroupIsoToAddEquiv.trans
    (((RepresentationTheory.CategoryTheory.HomologicalAlgebra.DerivedFunctor.Additivity.CategoryTheory.HomologicalAlgebra.DerivedFunctor.objectFunctor_biproduct A Y n D.oppositeSummand).addCommGroupIsoToAddEquiv).trans
      (biproductAddEquiv _))

/-- Equivalence from a construction with a module object to its family from displayed carriers. -/
noncomputable def addEquivComponents (E : Module.DirectSumData A N)
    (X : ModuleCat.{0} Aᵐᵒᵖ) (n : ℕ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A N X n ≃+ ∀ l : E.summandIndex, RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A (E.summand l) X n :=
  (mapLinearEquiv E.linearEquiv X n).addCommGroupIsoToAddEquiv.trans
    (((RepresentationTheory.CategoryTheory.HomologicalAlgebra.DerivedFunctor.Additivity.CategoryTheory.HomologicalAlgebra.DerivedFunctor.objectConstruction_pi_biproduct A (fun l : E.summandIndex => (E.summand l : Type)) X n).addCommGroupIsoToAddEquiv).trans
      (biproductAddEquiv _))

/-- Equivalence between one displayed construction and a doubly indexed family of component constructions. -/
noncomputable def addEquivPi (D : Module.DirectSumData A M) (E : Module.DirectSumData A N)
    (n : ℕ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A N (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleAsOpposite A M) n ≃+
      ∀ (j : D.summandIndex) (l : E.summandIndex), RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A (E.summand l) (D.oppositeSummand j) n :=
  (addEquiv D N n).trans
    (AddEquiv.piCongrRight fun j => addEquivComponents E (D.oppositeSummand j) n)

/-- Proves subsingletonness of the ambient value from that of every displayed component. -/
lemma subsingleton_of_componentSubsingleton (D : Module.DirectSumData A M) (Y : Type) [AddCommGroup Y]
    [Module A Y] (n : ℕ) (h : ∀ j, Subsingleton (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A Y (D.oppositeSummand j) n)) :
    Subsingleton (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A Y (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleAsOpposite A M) n) :=
  haveI := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.subsingleton_pi fun j : D.summandIndex => (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A Y (D.oppositeSummand j) n : Type)
  (addEquiv D Y n).toEquiv.subsingleton

end Reduction

end RepresentationTheory.Auxiliary.ComponentEquivalences
