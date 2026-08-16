/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.SymmetricAlgebra.ProjectiveResolution
import RepresentationTheory.Algebra.Homology.LinearYoneda
import RepresentationTheory.HomologicalAlgebra.CochainComplexComparison
import RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution
import RepresentationTheory.ModuleCat.RightTensor
import RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction
import RepresentationTheory.Algebra.Module.DirectSumData
import Mathlib.Algebra.Homology.ShortComplex.RightHomology
import Mathlib.LinearAlgebra.TensorProduct.Tower


universe u

open _root_.CategoryTheory Limits

namespace RepresentationTheory.Algebra.Homology.SymmetricAlgebraResolution


/-- For a complex whose differentials all vanish, each homology object is isomorphic to the corresponding component. -/
noncomputable def HomologicalComplex.homologyIsoX_of_d_eq_zero {C : Type u} [Category C] [HasZeroMorphisms C]
    [CategoryWithHomology C] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (hzero : ∀ i j, K.d i j = 0) (i : ι) :
    K.homology i ≅ K.X i :=
  K.homologyIsoSc' (c.prev i) i (c.next i) rfl rfl ≪≫
    (ShortComplex.RightHomologyData.ofZeros (K.sc' (c.prev i) i (c.next i))
      (hzero _ _) (hzero _ _)).homologyIso

section Ext

variable (k : Type u) [Field k]
variable (V : Type u) [AddCommGroup V] [Module k V]
variable {κ : Type u} [LinearOrder κ] [Fintype κ]

local notation "SV" => SymmetricAlgebra k V
local notation "K" => RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V


/-- Symmetric-algebra-linear maps between the displayed modules are linearly equivalent to base-field-linear maps from an exterior power. -/
noncomputable def SymmetricAlgebra.linearMapCurryExteriorPowerEquiv (i : ℕ) :
    (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i →ₗ[SV] K) ≃ₗ[k] (⋀[k]^i V →ₗ[k] K) where
  toFun := RepresentationTheory.HomologicalAlgebra.CochainComplexComparison.scalarExtensionLinearMapEquiv k SV K (⋀[k]^i V)
  invFun := (RepresentationTheory.HomologicalAlgebra.CochainComplexComparison.scalarExtensionLinearMapEquiv k SV K (⋀[k]^i V)).symm
  left_inv := (RepresentationTheory.HomologicalAlgebra.CochainComplexComparison.scalarExtensionLinearMapEquiv k SV K (⋀[k]^i V)).left_inv
  right_inv := (RepresentationTheory.HomologicalAlgebra.CochainComplexComparison.scalarExtensionLinearMapEquiv k SV K (⋀[k]^i V)).right_inv
  map_add' := (RepresentationTheory.HomologicalAlgebra.CochainComplexComparison.scalarExtensionLinearMapEquiv k SV K (⋀[k]^i V)).map_add
  map_smul' c f := by
    ext w
    rfl

/-- The curried linear equivalence evaluates a map on an exterior-power element by applying the original map to its tensor with one. -/
@[simp]
theorem SymmetricAlgebra.linearMapCurryExteriorPowerEquiv_apply (i : ℕ) (f : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i →ₗ[SV] K)
    (w : ⋀[k]^i V) :
    SymmetricAlgebra.linearMapCurryExteriorPowerEquiv k V i f w = f (1 ⊗ₜ[k] w) := rfl


/-- Symmetric-algebra-linear maps between the displayed modules are linearly equivalent to the dual of an exterior power. -/
noncomputable def SymmetricAlgebra.linearMapExteriorPowerDualEquiv (i : ℕ) :
    (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i →ₗ[SV] K) ≃ₗ[k] Module.Dual k (⋀[k]^i V) :=
  SymmetricAlgebra.linearMapCurryExteriorPowerEquiv k V i |>.trans
    (LinearEquiv.arrowCongr (LinearEquiv.refl k (⋀[k]^i V)) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V))

omit [LinearOrder κ] in


/-- Every displayed symmetric-algebra-linear map composed with the basis-dependent map is zero. -/
theorem SymmetricAlgebra.linearMap_comp_basisMap_eq_zero (b : Module.Basis κ k V) (i : ℕ)
    (f : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i →ₗ[SV] K) :
    f.comp (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b i) = 0 := by
  apply RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.linearMap_ext_on_exteriorPowerGenerators
  intro v
  apply (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).injective
  rw [LinearMap.comp_apply, LinearMap.zero_apply, RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.basisIndexedMap_unrendered]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [LinearMap.map_smul_of_tower, map_smul]
  rw [show SymmetricAlgebra.ι k V (v j) ⊗ₜ[k]
      exteriorPower.ιMulti k i (v ∘ j.succAbove) =
      SymmetricAlgebra.ι k V (v j) •
        (1 ⊗ₜ[k] exteriorPower.ιMulti k i (v ∘ j.succAbove)) by
        rw [TensorProduct.smul_tmul']; simp]
  rw [f.map_smul, RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing_smul]
  simp [SymmetricAlgebra.algebraMapInv_ι]


/-- The differential from degree one above the given degree in the displayed projective resolution is the basis-dependent module morphism. -/
theorem SymmetricAlgebra.projectiveResolution_d_eq_basisMap (b : Module.Basis κ k V) (i : ℕ) :
    (RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b).complex.d (i + 1) i = ModuleCat.ofHom (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b i) := by
  change (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex b).d (i + 1) i = _
  exact RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex_d b i


/-- Every differential in the displayed linear Yoneda complex is zero. -/
theorem SymmetricAlgebra.linearYonedaResolution_d_eq_zero (b : Module.Basis κ k V) :
    ∀ i j, ((RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b).complex.linearYonedaObj k
      (ModuleCat.of SV K)).d i j = 0 := by
  intro i j
  rw [ChainComplex.linearYonedaObj_d]
  have hd : Linear.leftComp k (ModuleCat.of SV K)
      ((RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b).complex.d j i) = 0 := by
    by_cases h : j = i + 1
    · subst j
      apply DFunLike.ext _ _
      intro f
      apply ModuleCat.hom_ext
      apply DFunLike.ext _ _
      intro x
      rw [SymmetricAlgebra.projectiveResolution_d_eq_basisMap]
      change f.hom (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b i x) = 0
      exact LinearMap.congr_fun (SymmetricAlgebra.linearMap_comp_basisMap_eq_zero k V b i f.hom) x
    · have hshape : ¬ (ComplexShape.down ℕ).Rel j i := by simpa [eq_comm] using h
      rw [(RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b).complex.shape j i hshape]
      apply DFunLike.ext _ _
      intro f
      apply ModuleCat.hom_ext
      apply DFunLike.ext _ _
      intro x
      change ((0 : (RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b).complex.X j ⟶
        (RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b).complex.X i) ≫ f).hom x = (0 : K)
      rw [zero_comp]
      rfl
  rw [hd]
  rfl


/-- A linear equivalence identifies morphisms between the displayed symmetric-algebra modules with the dual of an exterior power. -/
noncomputable def SymmetricAlgebra.homExteriorPowerDualEquiv (i : ℕ) :
    (ModuleCat.of SV (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) ⟶ ModuleCat.of SV K) ≃ₗ[k]
      Module.Dual k (⋀[k]^i V) where
  toFun f := (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).toLinearMap.comp
    (SymmetricAlgebra.linearMapCurryExteriorPowerEquiv k V i f.hom)
  invFun g := ModuleCat.ofHom ((SymmetricAlgebra.linearMapCurryExteriorPowerEquiv k V i).symm
    ((RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).symm.toLinearMap.comp g))
  left_inv f := by
    apply ModuleCat.hom_ext
    apply (SymmetricAlgebra.linearMapCurryExteriorPowerEquiv k V i).injective
    ext w
    simp
  right_inv g := by
    ext w
    simp
  map_add' f g := by
    ext w
    rfl
  map_smul' c f := by
    ext w
    rfl


/-- Each component of the displayed linear Yoneda complex is isomorphic to the dual of the corresponding exterior power. -/
noncomputable def SymmetricAlgebra.linearYonedaResolutionComponentIsoExteriorPowerDual (b : Module.Basis κ k V) (i : ℕ) :
    ((RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b).complex.linearYonedaObj k (ModuleCat.of SV K)).X i ≅
      ModuleCat.of k (Module.Dual k (⋀[k]^i V)) :=
  eqToIso (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaObjComponent k SV K (RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b).complex i) ≪≫
    eqToIso (congrArg (fun X : ModuleCat SV => ModuleCat.of k
      (X ⟶ ModuleCat.of SV K)) (by rw [RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis_complex, RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex_X])) ≪≫
    (SymmetricAlgebra.homExteriorPowerDualEquiv k V i).toModuleIso


/-- The displayed indexed object is isomorphic to the dual of the corresponding exterior power. -/
noncomputable def SymmetricAlgebra.indexedObjectIsoExteriorPowerDual (b : Module.Basis κ k V) (i : ℕ) :
    RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology k SV (ModuleCat.of SV K) (ModuleCat.of SV K) i ≅
      ModuleCat.of k (Module.Dual k (⋀[k]^i V)) :=
  RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomologyIsoOfProjectiveResolution k SV (ModuleCat.of SV K) (ModuleCat.of SV K)
      (RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b) i ≪≫
    HomologicalComplex.homologyIsoX_of_d_eq_zero _ (SymmetricAlgebra.linearYonedaResolution_d_eq_zero k V b) i ≪≫
    SymmetricAlgebra.linearYonedaResolutionComponentIsoExteriorPowerDual k V b i

end Ext

section Tor

variable (k : Type u) [Field k]
variable (V : Type u) [AddCommGroup V] [Module k V]
variable {κ : Type u} [LinearOrder κ] [Fintype κ]

local notation "SV" => SymmetricAlgebra k V
local notation "K" => RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V

/-- A symmetric-algebra module carries the induced module structure over the base field. -/
noncomputable local instance SymmetricAlgebra.moduleRestrictScalars (M : ModuleCat.{u} SV) : Module k M :=
  Module.compHom M (algebraMap k SV)

/-- The base field, symmetric algebra, and a symmetric-algebra module form a scalar tower. -/
local instance SymmetricAlgebra.module_isScalarTower (M : ModuleCat.{u} SV) : IsScalarTower k SV M :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- An opposite symmetric-algebra module carries the induced module structure over the base field. -/
noncomputable local instance SymmetricAlgebra.opModuleRestrictScalars (M : ModuleCat.{u} SVᵐᵒᵖ) : Module k M :=
  Module.compHom M (algebraMap k SVᵐᵒᵖ)

/-- The base field, opposite symmetric algebra, and an opposite-algebra module form a scalar tower. -/
local instance SymmetricAlgebra.opModule_isScalarTower (M : ModuleCat.{u} SVᵐᵒᵖ) : IsScalarTower k SVᵐᵒᵖ M :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- The base-field action commutes with the opposite symmetric-algebra action on an opposite-algebra module. -/
local instance SymmetricAlgebra.opModule_smulCommClass (M : ModuleCat.{u} SVᵐᵒᵖ) : SMulCommClass k SVᵐᵒᵖ M where
  smul_comm c a m := by
    change (algebraMap k SVᵐᵒᵖ c) • (a • m) = a • ((algebraMap k SVᵐᵒᵖ c) • m)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- The carrier of the functorial image of a symmetric-algebra module carries a symmetric-algebra module structure. -/
noncomputable local instance SymmetricAlgebra.functorObjAlgebraModule (M : ModuleCat.{u} SV) :
    Module SV ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) :=
  Module.compHom ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) (RepresentationTheory.Algebra.Module.DirectSumData.commRingOppositeEquiv SV).symm.toRingHom

/-- The functorial image of a symmetric-algebra module carries a module structure over the base field. -/
noncomputable local instance (priority := 2000) SymmetricAlgebra.functorObjBaseModule
    (M : ModuleCat.{u} SV) : Module k ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) :=
  Module.compHom ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) (algebraMap k SV)

/-- The base field, symmetric algebra, and the functorial image of a module form a scalar tower. -/
local instance SymmetricAlgebra.functorObj_isScalarTower (M : ModuleCat.{u} SV) :
    IsScalarTower k SV ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) where
  smul_assoc c a x := by
    rw [Algebra.smul_def]
    exact mul_smul _ _ _

/-- The scalar action of the base field commutes with the opposite symmetric-algebra action on the functorial image of a module. -/
local instance (priority := 2000) SymmetricAlgebra.functorObj_smulCommClass (M : ModuleCat.{u} SV) :
    SMulCommClass k SVᵐᵒᵖ ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) where
  smul_comm c a x := by
    change (algebraMap k SV c) • (a.unop • x) = a.unop • ((algebraMap k SV c) • x)
    rw [← mul_smul, ← mul_smul, mul_comm]


/-- The carrier of the functorial image of a symmetric-algebra module is linearly equivalent to the original carrier. -/
noncomputable def SymmetricAlgebra.functorObjLinearEquiv (M : ModuleCat.{u} SV) :
    ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) ≃ₗ[SV] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Tensoring the functorial image of a module with the displayed module is linearly equivalent to tensoring the original module with it. -/
noncomputable def SymmetricAlgebra.functorObjTensorEquiv (M : ModuleCat.{u} SV) :
    TensorProduct SV ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) K ≃ₗ[k] TensorProduct SV M K :=
  ((TensorProduct.congr (SymmetricAlgebra.functorObjLinearEquiv k V M) (LinearEquiv.refl SV K) :
    TensorProduct SV ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) K ≃ₗ[SV] TensorProduct SV M K)).restrictScalars k

/-- A linear equivalence exchanges the two displayed factors in a tensor product over the symmetric algebra. -/
noncomputable def SymmetricAlgebra.tensorProductFlipEquiv (i : ℕ) :
    TensorProduct SV (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) K ≃ₗ[k] TensorProduct SV K (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) :=
  ((TensorProduct.comm SV (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) K :
    TensorProduct SV (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) K ≃ₗ[SV]
      TensorProduct SV K (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i))).restrictScalars k

/-- A linear equivalence identifies the displayed tensor product over the symmetric algebra with a tensor product over the base field involving an exterior power. -/
noncomputable def SymmetricAlgebra.tensorProductExteriorPowerEquiv (i : ℕ) :
    TensorProduct SV K (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) ≃ₗ[k] TensorProduct k K (⋀[k]^i V) :=
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange k SV SV K (⋀[k]^i V) :
    TensorProduct SV K (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) ≃ₗ[SV]
      TensorProduct k K (⋀[k]^i V))).restrictScalars k


/-- Scalar multiplication by the opposite of a symmetric-algebra element agrees with scalar multiplication by that element. -/
theorem SymmetricAlgebra.op_smul_eq_smul (M : ModuleCat.{u} SV) (a : SV) (x : M) :
    (MulOpposite.op a • (show (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M from x)) = a • x := by
  change RepresentationTheory.Algebra.Module.DirectSumData.commRingOppositeEquiv SV (MulOpposite.op a) • x = a • x
  rfl


/-- The displayed module is linearly equivalent to a tensor product over the symmetric algebra. -/
noncomputable def SymmetricAlgebra.functorObjTensorProductEquiv (M : ModuleCat.{u} SV) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction SV K ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) ≃ₗ[k]
      TensorProduct SV ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) K where
  toFun := RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductEquivTensorProduct (M := (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) (SymmetricAlgebra.op_smul_eq_smul k V M)
  invFun := (RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductEquivTensorProduct (M := (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M)
    (SymmetricAlgebra.op_smul_eq_smul k V M)).symm
  left_inv := (RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductEquivTensorProduct (M := (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M)
    (SymmetricAlgebra.op_smul_eq_smul k V M)).left_inv
  right_inv := (RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductEquivTensorProduct (M := (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M)
    (SymmetricAlgebra.op_smul_eq_smul k V M)).right_inv
  map_add' := (RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductEquivTensorProduct (M := (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M)
    (SymmetricAlgebra.op_smul_eq_smul k V M)).map_add
  map_smul' c z := by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    induction y with
    | zero => rfl
    | tmul m x => rfl
    | add x y hx hy =>
        simpa only [QuotientAddGroup.mk_add, smul_add, map_add] using congrArg₂ (· + ·) hx hy

/-- The displayed linear equivalence sends the class of a pure tensor to the corresponding tensor over the symmetric algebra. -/
@[simp]
theorem SymmetricAlgebra.functorObjTensorProductEquiv_mk_tmul (M : ModuleCat.{u} SV)
    (m : (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) (c : K) :
    SymmetricAlgebra.functorObjTensorProductEquiv k V M
      (QuotientAddGroup.mk (m ⊗ₜ[ℤ] c)) = m ⊗ₜ[SV] c := rfl


/-- The displayed module obtained from the functorial image is linearly equivalent to the corresponding exterior power. -/
noncomputable def SymmetricAlgebra.functorObjExteriorPowerEquiv (i : ℕ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction SV K ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj (ModuleCat.of SV (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i))) ≃ₗ[k]
      ⋀[k]^i V :=
  SymmetricAlgebra.functorObjTensorProductEquiv k V (ModuleCat.of SV (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)) |>.trans
    (SymmetricAlgebra.functorObjTensorEquiv k V (ModuleCat.of SV (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i))) |>.trans
    (SymmetricAlgebra.tensorProductFlipEquiv k V i) |>.trans
    (SymmetricAlgebra.tensorProductExteriorPowerEquiv k V i) |>.trans
    (TensorProduct.congr (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V)
      (LinearEquiv.refl k (⋀[k]^i V))) |>.trans
    (TensorProduct.lid k (⋀[k]^i V))


/-- A basis determines a projective resolution of the functorial image of the displayed symmetric-algebra module. -/
noncomputable def SymmetricAlgebra.functorObjProjectiveResolution (b : Module.Basis κ k V) :
    ProjectiveResolution ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj (ModuleCat.of SV K)) :=
  (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).mapProjectiveResolution (RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b)

/-- Every canonical symmetric-algebra generator acts as zero on the displayed module. -/
theorem SymmetricAlgebra.generator_smul_eq_zero (v : V) (c : K) :
    SymmetricAlgebra.ι k V v • c = 0 := by
  apply (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).injective
  rw [RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing_smul]
  simp [SymmetricAlgebra.algebraMapInv_ι]

omit [LinearOrder κ] in
/-- The basis-dependent map applied to a pure tensor, then tensored with an element of the displayed module, is zero. -/
theorem SymmetricAlgebra.basisMap_tmul_tmul_eq_zero (b : Module.Basis κ k V) (i : ℕ)
    (s : SV) (w : ⋀[k]^(i + 1) V) (c : K) :
    RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b i (s ⊗ₜ[k] w) ⊗ₜ[SV] c = 0 := by
  rw [RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential_tmul, TensorProduct.sum_tmul]
  apply Finset.sum_eq_zero
  intro a _
  rw [show SymmetricAlgebra.ι k V (b a) * s =
      SymmetricAlgebra.ι k V (b a) • s by rfl]
  rw [show (SymmetricAlgebra.ι k V (b a) • s) ⊗ₜ[k]
      RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction k (b.coord a) i w =
      SymmetricAlgebra.ι k V (b a) •
        (s ⊗ₜ[k] RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction k (b.coord a) i w) by
        rw [TensorProduct.smul_tmul']]
  calc
    (SymmetricAlgebra.ι k V (b a) •
        (s ⊗ₜ[k] RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction k (b.coord a) i w)) ⊗ₜ[SV] c =
      (s ⊗ₜ[k] RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction.exteriorPowerContraction k (b.coord a) i w) ⊗ₜ[SV]
        (SymmetricAlgebra.ι k V (b a) • c) := TensorProduct.smul_tmul _ _ _
    _ = 0 := by rw [SymmetricAlgebra.generator_smul_eq_zero, TensorProduct.tmul_zero]

omit [LinearOrder κ] in
/-- Tensoring the value of the basis-dependent linear map with an element of the displayed module gives zero. -/
theorem SymmetricAlgebra.basisMap_tmul_eq_zero (b : Module.Basis κ k V) (i : ℕ)
    (m : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V (i + 1)) (c : K) : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b i m ⊗ₜ[SV] c = 0 := by
  induction m using TensorProduct.induction_on with
  | zero => rw [map_zero, TensorProduct.zero_tmul]
  | tmul s w => exact SymmetricAlgebra.basisMap_tmul_tmul_eq_zero k V b i s w c
  | add x y hx hy => rw [map_add, TensorProduct.add_tmul, hx, hy, add_zero]

omit [LinearOrder κ] in

/-- Applying the displayed map to the functorial image of the basis-dependent differential gives zero. -/
theorem SymmetricAlgebra.map_basisDifferential_eq_zero (b : Module.Basis κ k V) (i : ℕ) :
    RepresentationTheory.ModuleCat.RightTensor.rightTensorMapLinear k SV K
      ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).map (ModuleCat.ofHom (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential b i))) = 0 := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.zero_apply]
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  induction y with
  | zero => rfl
  | tmul m c =>
      apply (SymmetricAlgebra.functorObjTensorProductEquiv k V
        (ModuleCat.of SV (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i))).injective
      rw [RepresentationTheory.ModuleCat.RightTensor.rightTensorMapLinear_apply_tmul, map_zero]
      rw [SymmetricAlgebra.functorObjTensorProductEquiv_mk_tmul]
      exact SymmetricAlgebra.basisMap_tmul_eq_zero k V b i m c
  | add x y hx hy =>
      rw [QuotientAddGroup.mk_add, map_add, hx, hy, add_zero]


/-- A basis of the vector space determines a chain complex of modules over the base field. -/
noncomputable def SymmetricAlgebra.basisChainComplex (b : Module.Basis κ k V) :
    HomologicalComplex (ModuleCat.{u} k) (ComplexShape.down ℕ) :=
  ((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k SV K).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (SymmetricAlgebra.functorObjProjectiveResolution k V b).complex

/-- Every differential in the basis-dependent chain complex is zero. -/
theorem SymmetricAlgebra.basisChainComplex_d_eq_zero (b : Module.Basis κ k V) :
    ∀ i j, (SymmetricAlgebra.basisChainComplex k V b).d i j = 0 := by
  intro i j
  rw [SymmetricAlgebra.basisChainComplex, Functor.mapHomologicalComplex_obj_d]
  by_cases h : i = j + 1
  · subst i
    change ModuleCat.ofHom (RepresentationTheory.ModuleCat.RightTensor.rightTensorMapLinear k SV K
      ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).map ((RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b).complex.d (j + 1) j))) = 0
    rw [SymmetricAlgebra.projectiveResolution_d_eq_basisMap]
    apply ModuleCat.hom_ext
    exact SymmetricAlgebra.map_basisDifferential_eq_zero k V b j
  · have hshape : ¬(ComplexShape.down ℕ).Rel i j := by simpa [eq_comm] using h
    rw [(SymmetricAlgebra.functorObjProjectiveResolution k V b).complex.shape i j hshape]
    exact (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k SV K).map_zero _ _


/-- Each component of the basis-dependent chain complex is isomorphic to the corresponding exterior power. -/
noncomputable def SymmetricAlgebra.basisChainComplexComponentIsoExteriorPower (b : Module.Basis κ k V) (i : ℕ) :
    (SymmetricAlgebra.basisChainComplex k V b).X i ≅ ModuleCat.of k (⋀[k]^i V) :=
  (SymmetricAlgebra.functorObjExteriorPowerEquiv k V i).toModuleIso


/-- The displayed indexed object is isomorphic to the corresponding exterior power. -/
noncomputable def SymmetricAlgebra.indexedObjectIsoExteriorPower (b : Module.Basis κ k V) (i : ℕ) :
    RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k SV K ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj (ModuleCat.of SV K)) i ≅
      ModuleCat.of k (⋀[k]^i V) :=
  RepresentationTheory.ModuleCat.RightTensor.rightTensorProjectiveResolutionHomologyIso k SV K _ (SymmetricAlgebra.functorObjProjectiveResolution k V b) i ≪≫
    HomologicalComplex.homologyIsoX_of_d_eq_zero _ (SymmetricAlgebra.basisChainComplex_d_eq_zero k V b) i ≪≫
    SymmetricAlgebra.basisChainComplexComponentIsoExteriorPower k V b i

end Tor

end RepresentationTheory.Algebra.Homology.SymmetricAlgebraResolution
