/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.HomologicalAlgebra.TensorProduct
import RepresentationTheory.SymmetricAlgebra.ProjectiveResolution
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import RepresentationTheory.Alignment.Attribute

/-!
# The shear automorphism behind the Koszul bimodule resolution

This file supplies the change-of-rings calculation needed in Problem 8.2.10(iii). On
`SV ⊗[k] SV`, the shear sends a generator in the first factor to the sum of the corresponding
generators in the two factors and fixes the second factor. Restricting the external action on
the augmented Koszul target `k ⊗[k] SV` along this automorphism gives the usual bimodule action
on `SV` by left and right multiplication.

The inverse shear is constructed explicitly, and `tensorCoefficientIso` packages the target
identification as an isomorphism of `SV ⊗[k] SV`-modules. The second half of the file bridges the
restriction-of-scalars tensor instance used by the categorical external tensor construction to
the literal tensor product, then packages the transported exact projective resolution as
`auxiliaryProjectiveResolution`.
-/

open CategoryTheory Limits TensorProduct

universe u
namespace RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison

variable (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V]

/-- The type associated with a field and a module that supplies the coefficient algebra. -/
abbrev CoefficientAlgebra := SymmetricAlgebra k V
/-- The type associated with a field and a module that supplies the acting algebra. -/
abbrev ActingAlgebra := CoefficientAlgebra k V ⊗[k] CoefficientAlgebra k V

/-- A linear map from the original module to the acting algebra. -/
noncomputable def linearMapToActingAlgebra : V →ₗ[k] ActingAlgebra k V :=
  (Algebra.TensorProduct.includeLeft.toLinearMap.comp (SymmetricAlgebra.ι k V)) +
    (Algebra.TensorProduct.includeRight.toLinearMap.comp (SymmetricAlgebra.ι k V))

/-- A second linear map from the original module to the acting algebra. -/
noncomputable def alternateLinearMapToActingAlgebra : V →ₗ[k] ActingAlgebra k V :=
  (Algebra.TensorProduct.includeLeft.toLinearMap.comp (SymmetricAlgebra.ι k V)) -
    (Algebra.TensorProduct.includeRight.toLinearMap.comp (SymmetricAlgebra.ι k V))

/-- A second algebra homomorphism from the coefficient algebra to the acting algebra. -/
noncomputable def alternateCoefficientAlgHom : CoefficientAlgebra k V →ₐ[k] ActingAlgebra k V :=
  SymmetricAlgebra.lift (linearMapToActingAlgebra k V)

/-- An algebra homomorphism from the coefficient algebra to the acting algebra. -/
noncomputable def coefficientAlgHom : CoefficientAlgebra k V →ₐ[k] ActingAlgebra k V :=
  SymmetricAlgebra.lift (alternateLinearMapToActingAlgebra k V)

/-- An algebra endomorphism of the acting algebra. -/
noncomputable def selfAlgHom : ActingAlgebra k V →ₐ[k] ActingAlgebra k V :=
  Algebra.TensorProduct.lift (alternateCoefficientAlgHom k V) Algebra.TensorProduct.includeRight
    (fun _ _ => mul_comm _ _)

/-- A second algebra endomorphism of the acting algebra serving as the inverse candidate. -/
noncomputable def inverseSelfAlgHom : ActingAlgebra k V →ₐ[k] ActingAlgebra k V :=
  Algebra.TensorProduct.lift (coefficientAlgHom k V) Algebra.TensorProduct.includeRight
    (fun _ _ => mul_comm _ _)

/-- The inverse candidate composed with the self algebra homomorphism is the identity. -/
lemma inverse_comp_selfAlgHom : (inverseSelfAlgHom k V).comp (selfAlgHom k V) = AlgHom.id k (ActingAlgebra k V) := by
  ext v <;> simp [inverseSelfAlgHom, selfAlgHom, alternateCoefficientAlgHom, coefficientAlgHom, linearMapToActingAlgebra,
    alternateLinearMapToActingAlgebra, ← Algebra.TensorProduct.one_def]

/-- The self algebra homomorphism composed with its inverse candidate is the identity. -/
lemma selfAlgHom_comp_inverse : (selfAlgHom k V).comp (inverseSelfAlgHom k V) = AlgHom.id k (ActingAlgebra k V) := by
  ext v <;> simp [inverseSelfAlgHom, selfAlgHom, alternateCoefficientAlgHom, coefficientAlgHom, linearMapToActingAlgebra,
    alternateLinearMapToActingAlgebra, ← Algebra.TensorProduct.one_def]

/-- An algebra equivalence from the acting algebra to itself. -/
noncomputable def selfAlgEquiv : ActingAlgebra k V ≃ₐ[k] ActingAlgebra k V :=
  { selfAlgHom k V with
    invFun := inverseSelfAlgHom k V
    left_inv := DFunLike.congr_fun (inverse_comp_selfAlgHom k V)
    right_inv := DFunLike.congr_fun (selfAlgHom_comp_inverse k V) }

attribute [local instance] RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTower RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTowerAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductModule

/-- The module structure of the coefficient algebra over the acting algebra. -/
@[reducible] noncomputable def coefficientModule : Module (ActingAlgebra k V) (CoefficientAlgebra k V) :=
  Module.compHom (CoefficientAlgebra k V) (Algebra.TensorProduct.lmul' k).toRingHom

/-- The action of the acting algebra on the tensor product of the first factor with the coefficient algebra. -/
noncomputable def tensorAct (r : ActingAlgebra k V) (z : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) :=
  (RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V)).toSMul.smul r z

/-- The zero acting element sends every tensor to zero. -/
@[simp] lemma zero_tensorAct (z : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) : tensorAct k V 0 z = 0 := by
  change RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.moduleEndAlgHom k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V) 0 z = 0
  rw [map_zero, LinearMap.zero_apply]

/-- The tensor action is additive in the acting element. -/
lemma add_tensorAct (r t : ActingAlgebra k V) (z : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) :
    tensorAct k V (r + t) z = tensorAct k V r z + tensorAct k V t z := by
  change RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.moduleEndAlgHom k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V) (r + t) z = _
  rw [map_add, LinearMap.add_apply]
  rfl

/-- Every acting element sends the zero tensor to zero. -/
@[simp] lemma tensorAct_zero (r : ActingAlgebra k V) :
    tensorAct k V r (0 : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) = 0 := by
  change RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.moduleEndAlgHom k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V) r 0 = 0
  exact map_zero _

/-- A fixed acting element distributes over addition in the tensor product. -/
lemma tensorAct_add (r : ActingAlgebra k V) (x y : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) :
    tensorAct k V r (x + y) = tensorAct k V r x + tensorAct k V r y := by
  change RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.moduleEndAlgHom k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V) r (x + y) = _
  exact map_add _ _ _

/-- The action of a product is the composite of the actions of its factors. -/
lemma mul_tensorAct (r t : ActingAlgebra k V) (z : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) :
    tensorAct k V (r * t) z = tensorAct k V r (tensorAct k V t z) := by
  change RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.moduleEndAlgHom k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V) (r * t) z = _
  rw [map_mul]
  rfl

/-- Acting by a pure coefficient tensor on a pure tensor acts separately on its two factors. -/
lemma tmul_tensorAct_tmul (a b : CoefficientAlgebra k V) (c : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (s : CoefficientAlgebra k V) :
    tensorAct k V (a ⊗ₜ[k] b) (c ⊗ₜ[k] s) = (a • c) ⊗ₜ[k] (b * s) :=
  RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.smul_tmul k (CoefficientAlgebra k V) (CoefficientAlgebra k V)
    (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V) a b c s

/-- A linear equivalence from the tensor product of the first factor with coefficients to the coefficient algebra. -/
noncomputable def tensorCoefficientLinearEquiv :
    (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) ≃ₗ[k] CoefficientAlgebra k V :=
  TensorProduct.congr (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V) (LinearEquiv.refl k (CoefficientAlgebra k V)) ≪≫ₗ
    TensorProduct.lid k (CoefficientAlgebra k V)

/-- The tensor-coefficient equivalence evaluates a pure tensor by letting its first factor act on the coefficient. -/
@[simp] lemma tensorCoefficientLinearEquiv_tmul (c : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (s : CoefficientAlgebra k V) :
    tensorCoefficientLinearEquiv k V (c ⊗ₜ[k] s) = RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V c • s := by
  simp [tensorCoefficientLinearEquiv]

/-- The tensor-coefficient equivalence turns the action induced by a coefficient homomorphism into coefficient multiplication. -/
lemma tensorCoefficientLinearEquiv_apply_coefficient (a : CoefficientAlgebra k V)
    (z : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) :
    tensorCoefficientLinearEquiv k V (tensorAct k V (alternateCoefficientAlgHom k V a) z) =
      a * tensorCoefficientLinearEquiv k V z := by
  induction a using SymmetricAlgebra.induction generalizing z with
  | algebraMap r =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, tensorAct_add, hx, hy, mul_add]
      | tmul c s =>
        rw [show alternateCoefficientAlgHom k V (algebraMap k (CoefficientAlgebra k V) r) =
            algebraMap k (ActingAlgebra k V) r by simp [alternateCoefficientAlgHom]]
        rw [show algebraMap k (ActingAlgebra k V) r =
            algebraMap k (CoefficientAlgebra k V) r ⊗ₜ[k] 1 by
              simp [Algebra.TensorProduct.algebraMap_apply]]
        rw [tmul_tensorAct_tmul, tensorCoefficientLinearEquiv_tmul, tensorCoefficientLinearEquiv_tmul]
        simp [Algebra.smul_def, mul_assoc]
  | ι v =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, tensorAct_add, hx, hy, mul_add]
      | tmul c s =>
        rw [show alternateCoefficientAlgHom k V (SymmetricAlgebra.ι k V v) =
            SymmetricAlgebra.ι k V v ⊗ₜ[k] 1 +
              1 ⊗ₜ[k] SymmetricAlgebra.ι k V v by
                simp [alternateCoefficientAlgHom, linearMapToActingAlgebra]]
        rw [add_tensorAct, tmul_tensorAct_tmul, tmul_tensorAct_tmul, map_add,
          tensorCoefficientLinearEquiv_tmul, tensorCoefficientLinearEquiv_tmul, tensorCoefficientLinearEquiv_tmul]
        simp [RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing_smul, SymmetricAlgebra.algebraMapInv_ι,
          Algebra.smul_def]
        ring
  | mul a b ha hb =>
      rw [map_mul, mul_tensorAct, ha, hb, mul_assoc]
  | add a b ha hb =>
      rw [map_add, add_tensorAct, map_add, ha, hb, add_mul]

/-- The action of an element of the acting algebra on the coefficient algebra. -/
noncomputable def actOnCoefficient (r : ActingAlgebra k V) (s : CoefficientAlgebra k V) : CoefficientAlgebra k V :=
  (coefficientModule k V).toSMul.smul r s

/-- The zero acting element acts as zero on every coefficient. -/
@[simp] lemma zero_actOnCoefficient (s : CoefficientAlgebra k V) : actOnCoefficient k V 0 s = 0 := by
  exact zero_smul _ _

/-- Acting on a coefficient by a sum is the sum of the two resulting actions. -/
lemma add_actOnCoefficient (r t : ActingAlgebra k V) (s : CoefficientAlgebra k V) :
    actOnCoefficient k V (r + t) s = actOnCoefficient k V r s + actOnCoefficient k V t s := by
  change (coefficientModule k V).toSMul.smul (r + t) s = _
  exact (coefficientModule k V).add_smul r t s

/-- Every acting element sends the zero coefficient to zero. -/
@[simp] lemma actOnCoefficient_zero (r : ActingAlgebra k V) : actOnCoefficient k V r 0 = 0 := by
  exact smul_zero _

/-- The action of a fixed acting element distributes over addition of coefficients. -/
lemma actOnCoefficient_add (r : ActingAlgebra k V) (s t : CoefficientAlgebra k V) :
    actOnCoefficient k V r (s + t) = actOnCoefficient k V r s + actOnCoefficient k V r t := by
  exact smul_add _ _ _

/-- A pure tensor acts on a coefficient by successive multiplication by its two factors. -/
lemma tmul_actOnCoefficient (a b s : CoefficientAlgebra k V) :
    actOnCoefficient k V (a ⊗ₜ[k] b) s = (a * b) * s := by
  rfl

/-- The tensor-coefficient equivalence transports the self-equivalence action to the coefficient action. -/
theorem tensorCoefficientLinearEquiv_apply_selfEquiv (r : ActingAlgebra k V)
    (z : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) :
    tensorCoefficientLinearEquiv k V
      (tensorAct k V (selfAlgEquiv k V r) z) =
      actOnCoefficient k V r (tensorCoefficientLinearEquiv k V z) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, add_tensorAct, map_add, hx, hy]
      rw [add_actOnCoefficient]
  | tmul a b =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [map_add, tensorAct_add, map_add, hx, hy, actOnCoefficient_add]
      | tmul c s =>
        rw [show selfAlgEquiv k V (a ⊗ₜ[k] b) = alternateCoefficientAlgHom k V a *
            Algebra.TensorProduct.includeRight b by rfl,
          mul_tensorAct]
        rw [show tensorAct k V (Algebra.TensorProduct.includeRight b) (c ⊗ₜ[k] s) =
            c ⊗ₜ[k] (b * s) by
              simpa [Algebra.TensorProduct.includeRight_apply] using
                tmul_tensorAct_tmul k V 1 b c s]
        rw [tensorCoefficientLinearEquiv_apply_coefficient]
        rw [tmul_actOnCoefficient]
        change a * ((algebraMap k (CoefficientAlgebra k V)) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V c) * (b * s)) =
          (a * b) * ((algebraMap k (CoefficientAlgebra k V)) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V c) * s)
        ring

/-- The module structure over the acting algebra on the explicit tensor product. -/
@[reducible] noncomputable def tensorActModule :
    Module (ActingAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) := by
  letI : Module (ActingAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) :=
    RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V)
  exact Module.compHom _ (selfAlgEquiv k V).toRingEquiv.toRingHom

/-- The tensor product module object is isomorphic to the coefficient module object over the acting algebra. -/
noncomputable def tensorCoefficientIso :
    @ModuleCat.of (ActingAlgebra k V) _ (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) _
        (tensorActModule k V) ≅
      @ModuleCat.of (ActingAlgebra k V) _ (CoefficientAlgebra k V) _ (coefficientModule k V) := by
  letI : Module (ActingAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) := tensorActModule k V
  letI : Module (ActingAlgebra k V) (CoefficientAlgebra k V) := coefficientModule k V
  exact LinearEquiv.toModuleIso
    { __ := tensorCoefficientLinearEquiv k V
      map_smul' := tensorCoefficientLinearEquiv_apply_selfEquiv k V }

/-! ## The external target bridge and the bimodule resolution -/

/-- A first module category object over the coefficient algebra. -/
noncomputable abbrev FirstCoefficientModuleObject : ModuleCat.{u} (CoefficientAlgebra k V) :=
  ModuleCat.of (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V)

/-- A second module category object over the coefficient algebra. -/
noncomputable abbrev SecondCoefficientModuleObject : ModuleCat.{u} (CoefficientAlgebra k V) :=
  ModuleCat.of (CoefficientAlgebra k V) (CoefficientAlgebra k V)

/-- A module category object over the acting algebra representing the tensor construction. -/
noncomputable abbrev TensorModuleObject : ModuleCat.{u} (ActingAlgebra k V) :=
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (FirstCoefficientModuleObject k V) (SecondCoefficientModuleObject k V)


/-- Combines carriers of the two coefficient module objects into the tensor module carrier. -/
noncomputable def tensorModuleMk (c : FirstCoefficientModuleObject k V) (s : SecondCoefficientModuleObject k V) :
    TensorModuleObject k V :=
  @TensorProduct.tmul k _ (FirstCoefficientModuleObject k V) (SecondCoefficientModuleObject k V) _ _
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier k (CoefficientAlgebra k V) (FirstCoefficientModuleObject k V))
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux k (CoefficientAlgebra k V) (SecondCoefficientModuleObject k V)) c s


/-- Forms a tensor from an element of the first factor and a coefficient. -/
noncomputable def tensorMk (c : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (s : CoefficientAlgebra k V) :
    RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V :=
  @TensorProduct.tmul k _ (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V) _ _
    RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.instModule Algebra.toModule c s

/-- A linear equivalence from the restricted first coefficient module carrier to its underlying factor type. -/
noncomputable def restrictedFirstCoefficientLinearEquiv :
    (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsLeft k (CoefficientAlgebra k V)).obj (FirstCoefficientModuleObject k V) ≃ₗ[k] RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by simp

/-- A linear equivalence from the restricted second coefficient module carrier to the coefficient algebra. -/
noncomputable def restrictedSecondCoefficientLinearEquiv :
    (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsRight k (CoefficientAlgebra k V)).obj (SecondCoefficientModuleObject k V) ≃ₗ[k] CoefficientAlgebra k V where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


/-- A linear equivalence from the tensor module carrier to the corresponding tensor product. -/
noncomputable def tensorModuleLinearEquiv :
    letI : Module k (TensorModuleObject k V) := Module.compHom _ (algebraMap k (ActingAlgebra k V))
    TensorModuleObject k V ≃ₗ[k] RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V :=
  RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsTensorProductLinearEquiv (FirstCoefficientModuleObject k V) (SecondCoefficientModuleObject k V) ≪≫ₗ
    TensorProduct.congr (restrictedFirstCoefficientLinearEquiv k V) (restrictedSecondCoefficientLinearEquiv k V)

/-- The tensor module equivalence sends the module constructor to the tensor constructor. -/
@[simp]
theorem tensorModuleLinearEquiv_apply_mk (c : FirstCoefficientModuleObject k V) (s : SecondCoefficientModuleObject k V) :
    tensorModuleLinearEquiv k V (tensorModuleMk k V c s) =
      tensorMk k V c s := rfl

/-- The tensor module constructor is compatible with scalar multiplication by a pure coefficient tensor. -/
theorem smul_tensorModuleMk (a b : CoefficientAlgebra k V) (c : FirstCoefficientModuleObject k V)
    (s : SecondCoefficientModuleObject k V) :
    (TensorModuleObject k V).isModule.toSMul.smul (a ⊗ₜ[k] b)
        (tensorModuleMk k V c s) =
      tensorModuleMk k V (a • c) (b • s) :=
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.smul_tmul k (CoefficientAlgebra k V) (CoefficientAlgebra k V)
    (FirstCoefficientModuleObject k V) (SecondCoefficientModuleObject k V) a b c s

/-- Scalar multiplication by a pure coefficient tensor is compatible with forming a tensor. -/
theorem smul_tensorMk (a b : CoefficientAlgebra k V) (c : RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V)
    (s : CoefficientAlgebra k V) :
    (RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V)
      (CoefficientAlgebra k V)).toSMul.smul (a ⊗ₜ[k] b) (tensorMk k V c s) =
        tensorMk k V (a • c) (b * s) :=
  RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.smul_tmul k (CoefficientAlgebra k V) (CoefficientAlgebra k V)
    (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V) a b c s


/-- The tensor module linear equivalence preserves scalar multiplication. -/
theorem tensorModuleLinearEquiv_smul (r : ActingAlgebra k V) (z : TensorModuleObject k V) :
    tensorModuleLinearEquiv k V ((TensorModuleObject k V).isModule.toSMul.smul r z) =
      (RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V)
        (CoefficientAlgebra k V)).toSMul.smul r (tensorModuleLinearEquiv k V z) := by
  induction r using TensorProduct.induction_on with
  | zero =>
      change tensorModuleLinearEquiv k V 0 = 0
      simp
  | add x y hx hy =>
      calc
        tensorModuleLinearEquiv k V
            ((TensorModuleObject k V).isModule.toSMul.smul (x + y) z) =
          tensorModuleLinearEquiv k V
            ((TensorModuleObject k V).isModule.toSMul.smul x z +
              (TensorModuleObject k V).isModule.toSMul.smul y z) :=
            congrArg (tensorModuleLinearEquiv k V)
              ((TensorModuleObject k V).isModule.add_smul x y z)
        _ = tensorModuleLinearEquiv k V
              ((TensorModuleObject k V).isModule.toSMul.smul x z) +
            tensorModuleLinearEquiv k V
              ((TensorModuleObject k V).isModule.toSMul.smul y z) := map_add _ _ _
        _ = _ := by
          rw [hx, hy]
          exact (RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V)
            (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V)).add_smul x y _ |>.symm
  | tmul a b =>
      induction z using TensorProduct.induction_on with
      | zero =>
          calc
            tensorModuleLinearEquiv k V
                ((TensorModuleObject k V).isModule.toSMul.smul (a ⊗ₜ[k] b) 0) =
              tensorModuleLinearEquiv k V 0 := congrArg (tensorModuleLinearEquiv k V)
                ((TensorModuleObject k V).isModule.smul_zero _)
            _ = 0 := map_zero _
            _ = _ := ((RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V)
              (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V)).smul_zero _).symm
      | add x y hx hy =>
          calc
            tensorModuleLinearEquiv k V
                ((TensorModuleObject k V).isModule.toSMul.smul (a ⊗ₜ[k] b) (x + y)) =
              tensorModuleLinearEquiv k V
                ((TensorModuleObject k V).isModule.toSMul.smul (a ⊗ₜ[k] b) x +
                  (TensorModuleObject k V).isModule.toSMul.smul (a ⊗ₜ[k] b) y) :=
                    congrArg (tensorModuleLinearEquiv k V)
                      ((TensorModuleObject k V).isModule.smul_add _ x y)
            _ = tensorModuleLinearEquiv k V
                  ((TensorModuleObject k V).isModule.toSMul.smul (a ⊗ₜ[k] b) x) +
                tensorModuleLinearEquiv k V
                  ((TensorModuleObject k V).isModule.toSMul.smul (a ⊗ₜ[k] b) y) := map_add _ _ _
            _ = (RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V)
                  (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V)).toSMul.smul (a ⊗ₜ[k] b)
                  (tensorModuleLinearEquiv k V x + tensorModuleLinearEquiv k V y) := by
                    rw [hx, hy]
                    exact (RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V)
                      (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V)).smul_add _ _ _ |>.symm
            _ = _ := congrArg
              ((RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V)
                (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V)).toSMul.smul (a ⊗ₜ[k] b))
              (map_add (tensorModuleLinearEquiv k V) x y).symm
      | tmul c s =>
          change tensorModuleLinearEquiv k V
              ((TensorModuleObject k V).isModule.toSMul.smul (a ⊗ₜ[k] b)
                (tensorModuleMk k V c s)) =
            (RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V)
              (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V)).toSMul.smul
                (a ⊗ₜ[k] b)
                (tensorModuleLinearEquiv k V (tensorModuleMk k V c s))
          rw [smul_tensorModuleMk, tensorModuleLinearEquiv_apply_mk,
            tensorModuleLinearEquiv_apply_mk, smul_tensorMk]
          simp [smul_eq_mul]


/-- The tensor module object is isomorphic to the module object on its explicit tensor product carrier. -/
noncomputable def tensorModuleIso : TensorModuleObject k V ≅
    @ModuleCat.of (ActingAlgebra k V) _ (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) _
      (RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V)) := by
  let X := TensorModuleObject k V
  change X ≅ _
  letI : Module (ActingAlgebra k V) X := X.isModule
  letI : Module (ActingAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V) :=
    RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) (CoefficientAlgebra k V)
  let e : X ≃ₗ[ActingAlgebra k V] RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V ⊗[k] CoefficientAlgebra k V :=
    { toFun := tensorModuleLinearEquiv k V
      invFun := (tensorModuleLinearEquiv k V).symm
      left_inv := (tensorModuleLinearEquiv k V).left_inv
      right_inv := (tensorModuleLinearEquiv k V).right_inv
      map_add' := (tensorModuleLinearEquiv k V).map_add
      map_smul' := tensorModuleLinearEquiv_smul k V }
  exact e.toModuleIso

/-- An endofunctor of the module category over the acting algebra. -/
noncomputable abbrev scalarEndofunctor :
    ModuleCat.{u} (ActingAlgebra k V) ⥤ ModuleCat.{u} (ActingAlgebra k V) :=
  ModuleCat.restrictScalars (selfAlgEquiv k V).toRingEquiv.toRingHom

/-- A projective resolution of the second coefficient module object. -/
noncomputable def secondCoefficientProjectiveResolution : RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData (SecondCoefficientModuleObject k V) :=
  ProjectiveResolution.self _


/-- The zeroth term of the second coefficient resolution is isomorphic to its resolved module object. -/
noncomputable def secondCoefficientResolutionZeroIso :
    (secondCoefficientProjectiveResolution k V).complex.X 0 ≅ SecondCoefficientModuleObject k V :=
  HomologicalComplex.singleObjXIsoOfEq
    (ComplexShape.down ℕ) 0 (SecondCoefficientModuleObject k V) 0 rfl

/-- A component morphism from a tensor product of resolution terms to the corresponding augmentation target. -/
noncomputable def totalComponentToAugmentation
    {M : ModuleCat.{u} (CoefficientAlgebra k V)} (P : RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData M) (n i₁ i₂ : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = n) :
    ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (CoefficientAlgebra k V) (CoefficientAlgebra k V)).obj (P.complex.X i₁)).obj
        ((secondCoefficientProjectiveResolution k V).complex.X i₂) ⟶
      ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (CoefficientAlgebra k V) (CoefficientAlgebra k V)).obj (P.complex.X n)).obj
        (SecondCoefficientModuleObject k V) := by
  rcases i₂ with _ | i₂
  · have hi : i₁ = n := by simpa using h
    subst i₁
    exact ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (CoefficientAlgebra k V) (CoefficientAlgebra k V)).obj (P.complex.X n)).map
      (secondCoefficientResolutionZeroIso k V).hom
  · exact 0

/-- At second degree zero, the component morphism is induced by the zeroth-term isomorphism. -/
@[simp]
theorem totalComponentToAugmentation_zero
    {M : ModuleCat.{u} (CoefficientAlgebra k V)} (P : RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData M) (n : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (n, 0) = n) :
    totalComponentToAugmentation k V P n n 0 h =
      ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (CoefficientAlgebra k V) (CoefficientAlgebra k V)).obj (P.complex.X n)).map
        (secondCoefficientResolutionZeroIso k V).hom := by
  simp [totalComponentToAugmentation]


/-- Each term of the tensor product complex is isomorphic to the indicated functorial tensor object. -/
noncomputable def tensorResolutionComponentIso
    {M : ModuleCat.{u} (CoefficientAlgebra k V)} (P : RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData M) (n : ℕ) :
    (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct (k := k) P (secondCoefficientProjectiveResolution k V)).X n ≅
      ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (CoefficientAlgebra k V) (CoefficientAlgebra k V)).obj (P.complex.X n)).obj
        (SecondCoefficientModuleObject k V) where
  hom := HomologicalComplex.mapBifunctorDesc (j := n)
    (totalComponentToAugmentation k V P n)
  inv := ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (CoefficientAlgebra k V) (CoefficientAlgebra k V)).obj (P.complex.X n)).map
      (secondCoefficientResolutionZeroIso k V).inv ≫
    HomologicalComplex.ιMapBifunctor P.complex (secondCoefficientProjectiveResolution k V).complex
      (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (CoefficientAlgebra k V) (CoefficientAlgebra k V)) (ComplexShape.down ℕ) n 0 n (by simp)
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    rcases i₂ with _ | i₂
    · have hi : i₁ = n := by simpa using h
      subst i₁
      rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
        totalComponentToAugmentation_zero, ← Category.assoc, ← Functor.map_comp]
      simp
    · have hz : IsZero ((secondCoefficientProjectiveResolution k V).complex.X (i₂ + 1)) := by
        change IsZero (((ChainComplex.single₀ (ModuleCat.{u} (CoefficientAlgebra k V))).obj
          (SecondCoefficientModuleObject k V)).X (i₂ + 1))
        apply HomologicalComplex.isZero_single_obj_X
        simp
      exact (((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (CoefficientAlgebra k V) (CoefficientAlgebra k V)).obj
        (P.complex.X i₁)).map_isZero hz).eq_of_src _ _
  inv_hom_id := by
    rw [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
      totalComponentToAugmentation_zero, ← Functor.map_comp]
    simp

/-! ## Literal terms of the bimodule resolution -/


/-- A natural-number-indexed family of tensor types associated with the field and module. -/
abbrev GradedTensorObject (i : ℕ) := RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i ⊗[k] CoefficientAlgebra k V


/-- A natural-number-indexed family of module category objects over the acting algebra. -/
noncomputable abbrev GradedModuleObject (i : ℕ) : ModuleCat.{u} (ActingAlgebra k V) :=
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k (CoefficientAlgebra k V) (CoefficientAlgebra k V)
    (ModuleCat.of (CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)) (SecondCoefficientModuleObject k V)


/-- The module structure over the acting algebra on a graded tensor object. -/
@[reducible] noncomputable def gradedTensorModule (i : ℕ) :
    Module (ActingAlgebra k V) (GradedTensorObject k V i) :=
  RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (CoefficientAlgebra k V)


/-- An alternate module structure over the acting algebra on each graded tensor object. -/
@[reducible] noncomputable def alternateGradedTensorModule (i : ℕ) :
    Module (ActingAlgebra k V) (GradedTensorObject k V i) := by
  letI : Module (ActingAlgebra k V) (GradedTensorObject k V i) :=
    gradedTensorModule k V i
  exact Module.compHom _ (selfAlgEquiv k V).toRingEquiv.toRingHom


/-- Combines a graded tensor element and a coefficient module element in the graded module object. -/
noncomputable def gradedModuleAction (i : ℕ) (q : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (s : SecondCoefficientModuleObject k V) :
    GradedModuleObject k V i :=
  @TensorProduct.tmul k _ (ModuleCat.of (CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)) (SecondCoefficientModuleObject k V) _ _
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier k (CoefficientAlgebra k V) (ModuleCat.of (CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)))
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux k (CoefficientAlgebra k V) (SecondCoefficientModuleObject k V)) q s


/-- Combines a graded tensor element with a coefficient to produce an element in the corresponding graded object. -/
noncomputable def gradedAct (i : ℕ) (q : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (s : CoefficientAlgebra k V) :
    GradedTensorObject k V i :=
  @TensorProduct.tmul k _ (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (CoefficientAlgebra k V) _ _ inferInstance Algebra.toModule q s

/-- A linear equivalence from the restricted graded tensor module carrier to the graded tensor type. -/
noncomputable def restrictedGradedTensorLinearEquiv (i : ℕ) :
    (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsLeft k (CoefficientAlgebra k V)).obj (ModuleCat.of (CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)) ≃ₗ[k]
      RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by simp


/-- A linear equivalence from a graded module carrier to the corresponding graded tensor object. -/
noncomputable def gradedModuleLinearEquiv (i : ℕ) :
    letI : Module k (GradedModuleObject k V i) := Module.compHom _ (algebraMap k (ActingAlgebra k V))
    GradedModuleObject k V i ≃ₗ[k] GradedTensorObject k V i :=
  RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsTensorProductLinearEquiv (ModuleCat.of (CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)) (SecondCoefficientModuleObject k V) ≪≫ₗ
    TensorProduct.congr (restrictedGradedTensorLinearEquiv k V i) (restrictedSecondCoefficientLinearEquiv k V)

/-- The graded module equivalence sends the module action to the corresponding graded action. -/
@[simp]
theorem gradedModuleLinearEquiv_apply_action (i : ℕ) (q : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (s : SecondCoefficientModuleObject k V) :
    gradedModuleLinearEquiv k V i (gradedModuleAction k V i q s) =
      gradedAct k V i q s := rfl

/-- The graded module action is compatible with scalar multiplication by pure coefficient tensors. -/
theorem smul_gradedModuleAction (i : ℕ) (a b : CoefficientAlgebra k V) (q : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)
    (s : SecondCoefficientModuleObject k V) :
    (GradedModuleObject k V i).isModule.toSMul.smul (a ⊗ₜ[k] b)
        (gradedModuleAction k V i q s) =
      gradedModuleAction k V i (a • q) (b • s) :=
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.smul_tmul k (CoefficientAlgebra k V) (CoefficientAlgebra k V)
    (ModuleCat.of (CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)) (SecondCoefficientModuleObject k V) a b q s

/-- Scalar multiplication by a pure coefficient tensor is compatible with the graded action. -/
theorem smul_gradedAct (i : ℕ) (a b : CoefficientAlgebra k V) (q : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)
    (s : CoefficientAlgebra k V) :
    (gradedTensorModule k V i).toSMul.smul (a ⊗ₜ[k] b)
        (gradedAct k V i q s) =
      gradedAct k V i (a • q) (b * s) :=
  RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.smul_tmul k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (CoefficientAlgebra k V) a b q s


/-- The graded module linear equivalence commutes with scalar multiplication. -/
theorem gradedModuleLinearEquiv_smul (i : ℕ) (r : ActingAlgebra k V)
    (z : GradedModuleObject k V i) :
    gradedModuleLinearEquiv k V i
        ((GradedModuleObject k V i).isModule.toSMul.smul r z) =
      (gradedTensorModule k V i).toSMul.smul r
        (gradedModuleLinearEquiv k V i z) := by
  induction r using TensorProduct.induction_on with
  | zero =>
      change gradedModuleLinearEquiv k V i 0 = 0
      simp
  | add x y hx hy =>
      calc
        gradedModuleLinearEquiv k V i
            ((GradedModuleObject k V i).isModule.toSMul.smul (x + y) z) =
          gradedModuleLinearEquiv k V i
            ((GradedModuleObject k V i).isModule.toSMul.smul x z +
              (GradedModuleObject k V i).isModule.toSMul.smul y z) :=
                congrArg (gradedModuleLinearEquiv k V i)
                  ((GradedModuleObject k V i).isModule.add_smul x y z)
        _ = gradedModuleLinearEquiv k V i
              ((GradedModuleObject k V i).isModule.toSMul.smul x z) +
            gradedModuleLinearEquiv k V i
              ((GradedModuleObject k V i).isModule.toSMul.smul y z) := map_add _ _ _
        _ = _ := by
          rw [hx, hy]
          exact (gradedTensorModule k V i).add_smul x y _ |>.symm
  | tmul a b =>
      induction z using TensorProduct.induction_on with
      | zero =>
          calc
            gradedModuleLinearEquiv k V i
                ((GradedModuleObject k V i).isModule.toSMul.smul (a ⊗ₜ[k] b) 0) =
              gradedModuleLinearEquiv k V i 0 := congrArg (gradedModuleLinearEquiv k V i)
                ((GradedModuleObject k V i).isModule.smul_zero _)
            _ = 0 := map_zero _
            _ = _ := ((gradedTensorModule k V i).smul_zero _).symm
      | add x y hx hy =>
          calc
            gradedModuleLinearEquiv k V i
                ((GradedModuleObject k V i).isModule.toSMul.smul (a ⊗ₜ[k] b) (x + y)) =
              gradedModuleLinearEquiv k V i
                ((GradedModuleObject k V i).isModule.toSMul.smul (a ⊗ₜ[k] b) x +
                  (GradedModuleObject k V i).isModule.toSMul.smul (a ⊗ₜ[k] b) y) :=
                    congrArg (gradedModuleLinearEquiv k V i)
                      ((GradedModuleObject k V i).isModule.smul_add _ x y)
            _ = gradedModuleLinearEquiv k V i
                  ((GradedModuleObject k V i).isModule.toSMul.smul (a ⊗ₜ[k] b) x) +
                gradedModuleLinearEquiv k V i
                  ((GradedModuleObject k V i).isModule.toSMul.smul (a ⊗ₜ[k] b) y) :=
                    map_add _ _ _
            _ = (gradedTensorModule k V i).toSMul.smul (a ⊗ₜ[k] b)
                  (gradedModuleLinearEquiv k V i x + gradedModuleLinearEquiv k V i y) := by
                    rw [hx, hy]
                    exact (gradedTensorModule k V i).smul_add _ _ _ |>.symm
            _ = _ := congrArg
              ((gradedTensorModule k V i).toSMul.smul (a ⊗ₜ[k] b))
              (map_add (gradedModuleLinearEquiv k V i) x y).symm
      | tmul q s =>
          change gradedModuleLinearEquiv k V i
              ((GradedModuleObject k V i).isModule.toSMul.smul (a ⊗ₜ[k] b)
                (gradedModuleAction k V i q s)) =
            (gradedTensorModule k V i).toSMul.smul (a ⊗ₜ[k] b)
              (gradedModuleLinearEquiv k V i (gradedModuleAction k V i q s))
          rw [smul_gradedModuleAction, gradedModuleLinearEquiv_apply_action,
            gradedModuleLinearEquiv_apply_action, smul_gradedAct]
          simp [smul_eq_mul]


/-- The graded module object is isomorphic to the module object formed from its graded carrier. -/
noncomputable def gradedModuleIso (i : ℕ) : GradedModuleObject k V i ≅
    @ModuleCat.of (ActingAlgebra k V) _ (GradedTensorObject k V i) _
      (gradedTensorModule k V i) := by
  let X := GradedModuleObject k V i
  change X ≅ _
  letI : Module (ActingAlgebra k V) X := X.isModule
  letI : Module (ActingAlgebra k V) (GradedTensorObject k V i) :=
    gradedTensorModule k V i
  let e : X ≃ₗ[ActingAlgebra k V] GradedTensorObject k V i :=
    { toFun := gradedModuleLinearEquiv k V i
      invFun := (gradedModuleLinearEquiv k V i).symm
      left_inv := (gradedModuleLinearEquiv k V i).left_inv
      right_inv := (gradedModuleLinearEquiv k V i).right_inv
      map_add' := (gradedModuleLinearEquiv k V i).map_add
      map_smul' := gradedModuleLinearEquiv_smul k V i }
  exact e.toModuleIso


/-- The endofunctor image of each graded module object is isomorphic to its explicit graded tensor module. -/
noncomputable def mappedGradedModuleIso (i : ℕ) :
    (scalarEndofunctor k V).obj (GradedModuleObject k V i) ≅
      @ModuleCat.of (ActingAlgebra k V) _ (GradedTensorObject k V i) _
        (alternateGradedTensorModule k V i) := by
  let X := (scalarEndofunctor k V).obj (GradedModuleObject k V i)
  change X ≅ _
  letI : Module (ActingAlgebra k V) X := X.isModule
  letI : Module (ActingAlgebra k V) (GradedTensorObject k V i) := alternateGradedTensorModule k V i
  let e : X ≃ₗ[ActingAlgebra k V] GradedTensorObject k V i :=
    { toFun := gradedModuleLinearEquiv k V i
      invFun := (gradedModuleLinearEquiv k V i).symm
      left_inv := (gradedModuleLinearEquiv k V i).left_inv
      right_inv := (gradedModuleLinearEquiv k V i).right_inv
      map_add' := (gradedModuleLinearEquiv k V i).map_add
      map_smul' := by
        intro r z
        change gradedModuleLinearEquiv k V i
            ((GradedModuleObject k V i).isModule.toSMul.smul (selfAlgEquiv k V r)
              (show GradedModuleObject k V i from z)) =
          (gradedTensorModule k V i).toSMul.smul (selfAlgEquiv k V r)
            (gradedModuleLinearEquiv k V i (show GradedModuleObject k V i from z))
        exact gradedModuleLinearEquiv_smul k V i (selfAlgEquiv k V r) z }
  exact e.toModuleIso


/-- A natural-number-indexed family of types associated with the field and module. -/
abbrev AuxiliaryGradedObject (i : ℕ) := ActingAlgebra k V ⊗[k] (⋀[k]^i V)


/-- An alternate linear equivalence from a graded tensor object to the auxiliary graded type. -/
noncomputable def alternateAuxiliaryLinearEquiv (i : ℕ) :
    GradedTensorObject k V i ≃ₗ[k] AuxiliaryGradedObject k V i :=
  TensorProduct.assoc k (CoefficientAlgebra k V) (⋀[k]^i V) (CoefficientAlgebra k V) ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl k (CoefficientAlgebra k V))
      (TensorProduct.comm k (⋀[k]^i V) (CoefficientAlgebra k V)) ≪≫ₗ
    (TensorProduct.assoc k (CoefficientAlgebra k V) (CoefficientAlgebra k V) (⋀[k]^i V)).symm


/-- A linear equivalence between a graded tensor object and the corresponding auxiliary graded type. -/
noncomputable def auxiliaryLinearEquiv (i : ℕ) :
    GradedTensorObject k V i ≃ₗ[k] AuxiliaryGradedObject k V i :=
  alternateAuxiliaryLinearEquiv k V i ≪≫ₗ
    TensorProduct.congr (selfAlgEquiv k V).symm.toLinearEquiv
      (LinearEquiv.refl k (⋀[k]^i V))

/-- The auxiliary equivalence sends a graded action on an exterior-power tensor to the displayed pure tensor. -/
@[simp]
theorem auxiliaryLinearEquiv_apply_tmul (i : ℕ) (s t : CoefficientAlgebra k V)
    (x : ⋀[k]^i V) :
    auxiliaryLinearEquiv k V i
        (gradedAct k V i (s ⊗ₜ[k] x) t) =
      (selfAlgEquiv k V).symm (s ⊗ₜ[k] t) ⊗ₜ[k] x := by
  rfl

/-- The zero graded tensor element acts to give zero. -/
@[simp]
theorem gradedAct_zero (i : ℕ) (t : CoefficientAlgebra k V) :
    gradedAct k V i 0 t = 0 :=
  TensorProduct.zero_tmul (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) t

/-- The graded action is additive in its graded tensor argument. -/
theorem gradedAct_add (i : ℕ) (x y : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (t : CoefficientAlgebra k V) :
    gradedAct k V i (x + y) t =
      gradedAct k V i x t + gradedAct k V i y t :=
  TensorProduct.add_tmul _ _ _

/-- The auxiliary equivalence sends a scaled graded action to the corresponding transported scalar action. -/
theorem auxiliaryLinearEquiv_apply_gradedAct (i : ℕ)
    (a b : CoefficientAlgebra k V) (q : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (t : CoefficientAlgebra k V) :
    auxiliaryLinearEquiv k V i
        (gradedAct k V i (a • q) (b * t)) =
      (selfAlgEquiv k V).symm (a ⊗ₜ[k] b) •
        auxiliaryLinearEquiv k V i
          (gradedAct k V i q t) := by
  induction q using TensorProduct.induction_on with
  | zero =>
      rw [smul_zero, gradedAct_zero, gradedAct_zero]
      simp only [map_zero, smul_zero]
  | add x y hx hy =>
      simp only [smul_add]
      change auxiliaryLinearEquiv k V i
          (gradedAct k V i (a • x + a • y) (b * t)) = _
      rw [gradedAct_add, gradedAct_add, map_add, map_add, hx, hy,
        smul_add]
  | tmul s x =>
      rw [TensorProduct.smul_tmul']
      rw [auxiliaryLinearEquiv_apply_tmul,
        auxiliaryLinearEquiv_apply_tmul]
      rw [TensorProduct.smul_tmul']
      congr 1
      change (selfAlgEquiv k V).symm ((a * s) ⊗ₜ[k] (b * t)) =
        (selfAlgEquiv k V).symm (a ⊗ₜ[k] b) * (selfAlgEquiv k V).symm (s ⊗ₜ[k] t)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul]


/-- The auxiliary linear equivalence converts scalar multiplication through the inverse self-equivalence. -/
theorem auxiliaryLinearEquiv_smul (i : ℕ) (r : ActingAlgebra k V)
    (z : GradedTensorObject k V i) :
    auxiliaryLinearEquiv k V i
        ((gradedTensorModule k V i).toSMul.smul r z) =
      (selfAlgEquiv k V).symm r • auxiliaryLinearEquiv k V i z := by
  induction r using TensorProduct.induction_on with
  | zero =>
      calc
        auxiliaryLinearEquiv k V i
            ((gradedTensorModule k V i).toSMul.smul 0 z) =
          auxiliaryLinearEquiv k V i 0 :=
            congrArg (auxiliaryLinearEquiv k V i)
              ((gradedTensorModule k V i).zero_smul z)
        _ = 0 := map_zero _
        _ = (0 : ActingAlgebra k V) • auxiliaryLinearEquiv k V i z :=
          (zero_smul (ActingAlgebra k V) (auxiliaryLinearEquiv k V i z)).symm
        _ = _ := by rw [map_zero]
  | add r t hr ht =>
      calc
        auxiliaryLinearEquiv k V i
            ((gradedTensorModule k V i).toSMul.smul (r + t) z) =
          auxiliaryLinearEquiv k V i
            ((gradedTensorModule k V i).toSMul.smul r z +
              (gradedTensorModule k V i).toSMul.smul t z) :=
                congrArg (auxiliaryLinearEquiv k V i)
                  ((gradedTensorModule k V i).add_smul r t z)
        _ = auxiliaryLinearEquiv k V i
              ((gradedTensorModule k V i).toSMul.smul r z) +
            auxiliaryLinearEquiv k V i
              ((gradedTensorModule k V i).toSMul.smul t z) := map_add _ _ _
        _ = _ := by rw [hr, ht, map_add, add_smul]
  | tmul a b =>
      induction z using TensorProduct.induction_on with
      | zero =>
          calc
            auxiliaryLinearEquiv k V i
                ((gradedTensorModule k V i).toSMul.smul (a ⊗ₜ[k] b) 0) =
              auxiliaryLinearEquiv k V i 0 :=
                congrArg (auxiliaryLinearEquiv k V i)
                  ((gradedTensorModule k V i).smul_zero (a ⊗ₜ[k] b))
            _ = 0 := map_zero _
            _ = _ := (smul_zero _).symm
      | add x y hx hy =>
          calc
            auxiliaryLinearEquiv k V i
                ((gradedTensorModule k V i).toSMul.smul (a ⊗ₜ[k] b)
                  (x + y)) =
              auxiliaryLinearEquiv k V i
                ((gradedTensorModule k V i).toSMul.smul (a ⊗ₜ[k] b) x +
                  (gradedTensorModule k V i).toSMul.smul (a ⊗ₜ[k] b) y) :=
                    congrArg (auxiliaryLinearEquiv k V i)
                      ((gradedTensorModule k V i).smul_add _ x y)
            _ = auxiliaryLinearEquiv k V i
                  ((gradedTensorModule k V i).toSMul.smul (a ⊗ₜ[k] b) x) +
                auxiliaryLinearEquiv k V i
                  ((gradedTensorModule k V i).toSMul.smul (a ⊗ₜ[k] b) y) :=
                    map_add _ _ _
            _ = _ := by
              rw [hx, hy]
              calc
                (selfAlgEquiv k V).symm (a ⊗ₜ[k] b) •
                      auxiliaryLinearEquiv k V i x +
                    (selfAlgEquiv k V).symm (a ⊗ₜ[k] b) •
                      auxiliaryLinearEquiv k V i y =
                  (selfAlgEquiv k V).symm (a ⊗ₜ[k] b) •
                    (auxiliaryLinearEquiv k V i x +
                      auxiliaryLinearEquiv k V i y) := (smul_add _ _ _).symm
                _ = _ := congrArg ((selfAlgEquiv k V).symm (a ⊗ₜ[k] b) • ·)
                  (map_add (auxiliaryLinearEquiv k V i) x y).symm
      | tmul q t =>
          change auxiliaryLinearEquiv k V i
              ((gradedTensorModule k V i).toSMul.smul (a ⊗ₜ[k] b)
                (gradedAct k V i q t)) =
            (selfAlgEquiv k V).symm (a ⊗ₜ[k] b) •
              auxiliaryLinearEquiv k V i (gradedAct k V i q t)
          rw [smul_gradedAct,
            auxiliaryLinearEquiv_apply_gradedAct]


/-- The graded tensor module object is isomorphic to the module object on the auxiliary graded type. -/
noncomputable def gradedAuxiliaryIso (i : ℕ) :
    @ModuleCat.of (ActingAlgebra k V) _ (GradedTensorObject k V i) _
        (alternateGradedTensorModule k V i) ≅
      ModuleCat.of (ActingAlgebra k V) (AuxiliaryGradedObject k V i) := by
  letI : Module (ActingAlgebra k V) (GradedTensorObject k V i) := alternateGradedTensorModule k V i
  let e : GradedTensorObject k V i ≃ₗ[ActingAlgebra k V] AuxiliaryGradedObject k V i :=
    { toFun := auxiliaryLinearEquiv k V i
      invFun := (auxiliaryLinearEquiv k V i).symm
      left_inv := (auxiliaryLinearEquiv k V i).left_inv
      right_inv := (auxiliaryLinearEquiv k V i).right_inv
      map_add' := (auxiliaryLinearEquiv k V i).map_add
      map_smul' := by
        intro r z
        change auxiliaryLinearEquiv k V i
            ((gradedTensorModule k V i).toSMul.smul (selfAlgEquiv k V r) z) =
          r • auxiliaryLinearEquiv k V i z
        rw [auxiliaryLinearEquiv_smul]
        simp }
  exact e.toModuleIso


/-- Every graded tensor object is free as a module over the acting algebra. -/
theorem gradedTensor_free (i : ℕ) :
    letI : Module (ActingAlgebra k V) (GradedTensorObject k V i) := alternateGradedTensorModule k V i
    Module.Free (ActingAlgebra k V) (GradedTensorObject k V i) := by
  letI : Module (ActingAlgebra k V) (GradedTensorObject k V i) := alternateGradedTensorModule k V i
  letI : Module.Free k (⋀[k]^i V) := inferInstance
  letI : Module.Free (ActingAlgebra k V) (AuxiliaryGradedObject k V i) := inferInstance
  exact Module.Free.of_equiv (gradedAuxiliaryIso k V i).symm.toLinearEquiv

/-- A projective resolution of the tensor module object determined by a finite basis. -/
noncomputable def tensorModuleProjectiveResolution
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData (TensorModuleObject k V) :=
  RepresentationTheory.HomologicalAlgebra.TensorProduct.tensorProduct (k := k) (RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b) (secondCoefficientProjectiveResolution k V)

/-- A projective resolution of the endofunctor image of the tensor module object, chosen from a finite basis. -/
noncomputable def mappedTensorProjectiveResolution
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData ((scalarEndofunctor k V).obj (TensorModuleObject k V)) :=
  (scalarEndofunctor k V).mapProjectiveResolution (tensorModuleProjectiveResolution k V b)

/-- The endofunctor image of the tensor module object is isomorphic to the coefficient module object. -/
noncomputable def endofunctorCoefficientIso :
    (scalarEndofunctor k V).obj (TensorModuleObject k V) ≅
      @ModuleCat.of (ActingAlgebra k V) _ (CoefficientAlgebra k V) _ (coefficientModule k V) :=
  (scalarEndofunctor k V).mapIso (tensorModuleIso k V) ≪≫ tensorCoefficientIso k V


/-- A basis-indexed projective resolution of the coefficient module object. -/
noncomputable def auxiliaryProjectiveResolution
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData
      (@ModuleCat.of (ActingAlgebra k V) _ (CoefficientAlgebra k V) _ (coefficientModule k V)) where
  complex := (mappedTensorProjectiveResolution k V b).complex
  projective := (mappedTensorProjectiveResolution k V b).projective
  π := (mappedTensorProjectiveResolution k V b).π ≫
    (ChainComplex.single₀ (ModuleCat.{u} (ActingAlgebra k V))).map (endofunctorCoefficientIso k V).hom
  quasiIso := by infer_instance


/-- Each term of the auxiliary projective resolution is isomorphic to the matching graded tensor module. -/
noncomputable def auxiliaryProjectiveResolutionTermIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (i : ℕ) :
    (auxiliaryProjectiveResolution k V b).complex.X i ≅
      @ModuleCat.of (ActingAlgebra k V) _ (GradedTensorObject k V i) _
        (alternateGradedTensorModule k V i) :=
  (scalarEndofunctor k V).mapIso
      (tensorResolutionComponentIso k V (RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b) i) ≪≫
    mappedGradedModuleIso k V i


/-- Every term of the auxiliary projective resolution is free over the acting algebra. -/
theorem auxiliaryProjectiveResolution_term_free
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (i : ℕ) :
    Module.Free (ActingAlgebra k V) ((auxiliaryProjectiveResolution k V b).complex.X i) := by
  letI : Module (ActingAlgebra k V) (GradedTensorObject k V i) := alternateGradedTensorModule k V i
  letI : Module.Free (ActingAlgebra k V) (GradedTensorObject k V i) := gradedTensor_free k V i
  exact Module.Free.of_equiv (auxiliaryProjectiveResolutionTermIso k V b i).symm.toLinearEquiv


/-- The augmentation of the auxiliary projective resolution is a quasi-isomorphism. -/
theorem auxiliaryProjectiveResolution_quasiIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    QuasiIso (auxiliaryProjectiveResolution k V b).π :=
  (auxiliaryProjectiveResolution k V b).quasiIso


/-- A projective resolution of the coefficient module object selected by a finite basis. -/
@[source_ref "Chapter8/Problem8.2.10" (role := primary)]
noncomputable def coefficientProjectiveResolution
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData
      (@ModuleCat.of (ActingAlgebra k V) _ (CoefficientAlgebra k V) _ (coefficientModule k V)) :=
  auxiliaryProjectiveResolution k V b


/-- The terms of the basis-indexed projective resolution are isomorphic to the corresponding graded module objects. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
noncomputable def coefficientProjectiveResolutionTermIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (i : ℕ) :
    (coefficientProjectiveResolution k V b).complex.X i ≅
      @ModuleCat.of (ActingAlgebra k V) _ (GradedTensorObject k V i) _
        (alternateGradedTensorModule k V i) :=
  auxiliaryProjectiveResolutionTermIso k V b i


/-- Every term in the basis-indexed projective resolution is free over the acting algebra. -/
theorem coefficientProjectiveResolution_term_free
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (i : ℕ) :
    Module.Free (ActingAlgebra k V) ((coefficientProjectiveResolution k V b).complex.X i) :=
  auxiliaryProjectiveResolution_term_free k V b i


/-- The augmentation of the basis-indexed projective resolution is a quasi-isomorphism. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
theorem coefficientProjectiveResolution_quasiIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    QuasiIso (coefficientProjectiveResolution k V b).π :=
  auxiliaryProjectiveResolution_quasiIso k V b

end RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison
