/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.TensorProduct.AuxiliaryScalarAction
import RepresentationTheory.Algebra.Homology.TensorProductConstruction
import Mathlib.Algebra.Category.ModuleCat.Abelian

set_option backward.isDefEq.respectTransparency false

/-!
# Right tensor module functor

This module packages right tensoring with a fixed module as a module-category functor and records
its derived constructions.
-/

open CategoryTheory TensorProduct

namespace RepresentationTheory.ModuleCat.RightTensor

universe u

variable (k : Type u) [CommRing k]
variable (A : Type u) [Ring A] [Algebra k A]
variable (N : Type u) [AddCommGroup N] [Module A N]

/-- Gives the base-ring module structure on the carrier of a module over the opposite ring. -/
noncomputable local instance rightModuleCarrier_restrictScalars
    (M : ModuleCat.{u} Aᵐᵒᵖ) : Module k M :=
  Module.compHom M (algebraMap k Aᵐᵒᵖ)

/-- States the scalar-tower compatibility on the carrier of a right module. -/
local instance rightModuleCarrier_isScalarTower
    (M : ModuleCat.{u} Aᵐᵒᵖ) : IsScalarTower k Aᵐᵒᵖ M :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- States that the base-ring action commutes with the opposite-ring action on a module carrier. -/
local instance rightModuleCarrier_smulComm
    (M : ModuleCat.{u} Aᵐᵒᵖ) : SMulCommClass k Aᵐᵒᵖ M where
  smul_comm c a m := by
    change (algebraMap k Aᵐᵒᵖ c) • (a • m) = a • ((algebraMap k Aᵐᵒᵖ c) • m)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- Describes the value of the induced tensor map on a pure tensor. -/
theorem rightTensorMap_apply_tmul {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M')
    (m : M) (n : N) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionMap A N f
        (QuotientAddGroup.mk (m ⊗ₜ[ℤ] n) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M)
      = (QuotientAddGroup.mk (f.hom m ⊗ₜ[ℤ] n) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
            A N M') := rfl

/-- States that the induced tensor map commutes with scalars from the base ring. -/
theorem rightTensorMap_smul {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') (c : k)
    (z : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
      A N M) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionMap A N f
        (c • z) =
      c • RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionMap
        A N f z := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  induction y with
  | zero => simp
  | tmul m n =>
      have hf : f.hom (c • m) = c • f.hom m := map_smul f.hom (algebraMap k Aᵐᵒᵖ c) m
      rw [RepresentationTheory.TensorProduct.AuxiliaryScalarAction.TensorProduct.Auxiliary.smul_mk,
        TensorProduct.smul_tmul', rightTensorMap_apply_tmul, rightTensorMap_apply_tmul, hf,
        RepresentationTheory.TensorProduct.AuxiliaryScalarAction.TensorProduct.Auxiliary.smul_mk,
        TensorProduct.smul_tmul']
  | add a b ha hb =>
      rw [QuotientAddGroup.mk_add, smul_add, map_add, map_add, ha, hb, smul_add]

/-- Constructs the base-linear map on tensor products induced by a module morphism. -/
noncomputable def rightTensorMapLinear {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M →ₗ[k]
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M' where
  toFun :=
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionMap A N f
  map_add' :=
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionMap
      A N f).map_add
  map_smul' c z := rightTensorMap_smul k A N f c z

/-- Computes the induced base-linear tensor map on a pure tensor. -/
@[simp] theorem rightTensorMapLinear_apply_tmul {M M' : ModuleCat.{u} Aᵐᵒᵖ}
    (f : M ⟶ M') (m : M) (n : N) :
    rightTensorMapLinear k A N f
        (QuotientAddGroup.mk (m ⊗ₜ[ℤ] n) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M)
      = (QuotientAddGroup.mk (f.hom m ⊗ₜ[ℤ] n) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
            A N M') := rfl

/-- Maps right modules to k-modules by tensoring with a fixed left module. -/
noncomputable def rightTensorFunctor : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} k where
  obj M := ModuleCat.of k
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M)
  map {M M'} f := ModuleCat.ofHom (rightTensorMapLinear k A N f)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n => rfl
    | add a b ha hb => rw [QuotientAddGroup.mk_add, map_add, map_add, ha, hb]
  map_comp {M M' M''} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n => rfl
    | add a b ha hb => rw [QuotientAddGroup.mk_add, map_add, map_add, ha, hb]

/-- Describes the image of a pure tensor under the right tensor functor. -/
@[simp] theorem rightTensorFunctor_map_tmul {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M')
    (m : M) (n : N) :
    (rightTensorFunctor k A N).map f
        (QuotientAddGroup.mk (m ⊗ₜ[ℤ] n) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M)
      = (QuotientAddGroup.mk (f.hom m ⊗ₜ[ℤ] n) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
            A N M') := rfl

/-- States that the right tensor functor preserves addition of morphisms. -/
instance rightTensorFunctor_additive : (rightTensorFunctor k A N).Additive where
  map_add {M M' f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [ModuleCat.hom_add, LinearMap.add_apply]
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n =>
        change
          (QuotientAddGroup.mk ((f + g).hom m ⊗ₜ[ℤ] n) :
              RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
                A N M') =
            QuotientAddGroup.mk (f.hom m ⊗ₜ[ℤ] n) +
              QuotientAddGroup.mk (g.hom m ⊗ₜ[ℤ] n)
        rw [← QuotientAddGroup.mk_add, ModuleCat.hom_add, LinearMap.add_apply, add_tmul]
    | add a b ha hb =>
        rw [QuotientAddGroup.mk_add, map_add, map_add, map_add, ha, hb]
        abel

/-- Compares the underlying additive-group functor of right tensoring with a related functor. -/
noncomputable def rightTensorForgetIso :
    rightTensorFunctor k A N ⋙ forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}
      ≅ RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
        A N :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M M' f
    simp only [Functor.comp_map, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

/-- Provides a family of module-category functors indexed by natural numbers. -/
noncomputable def auxiliaryIndexedModuleFunctor (n : ℕ) :
    ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  Functor.leftDerived (rightTensorFunctor k A N) n

/-- Selects the k-module associated with a right-opposite module and an index. -/
noncomputable def auxiliaryIndexedModuleFunctorObj (M : ModuleCat.{u} Aᵐᵒᵖ)
    (n : ℕ) : ModuleCat.{u} k :=
  (auxiliaryIndexedModuleFunctor k A N n).obj M

/-- Identifies an indexed tensor construction with homology of a mapped projective resolution. -/
noncomputable def rightTensorProjectiveResolutionHomologyIso
    (M : ModuleCat.{u} Aᵐᵒᵖ) (P : ProjectiveResolution M) (n : ℕ) :
    auxiliaryIndexedModuleFunctorObj k A N M n ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n).obj
        (((rightTensorFunctor k A N).mapHomologicalComplex _).obj P.complex) :=
  P.isoLeftDerivedObj (rightTensorFunctor k A N) n

end RepresentationTheory.ModuleCat.RightTensor
