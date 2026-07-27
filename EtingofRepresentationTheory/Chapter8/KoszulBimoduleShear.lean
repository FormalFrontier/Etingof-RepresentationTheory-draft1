import EtingofRepresentationTheory.Chapter8.ExternalTensorResolutionLeft
import EtingofRepresentationTheory.Chapter8.KoszulResolution
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# The shear automorphism behind the Koszul bimodule resolution

This file supplies the change-of-rings calculation needed in Problem 8.2.10(iii). On
`SV ⊗[k] SV`, the shear sends a generator in the first factor to the sum of the corresponding
generators in the two factors and fixes the second factor. Restricting the external action on
the augmented Koszul target `k ⊗[k] SV` along this automorphism gives the usual bimodule action
on `SV` by left and right multiplication.

The inverse shear is constructed explicitly, and `shearedTargetIso` packages the target
identification as an isomorphism of `SV ⊗[k] SV`-modules. The second half of the file bridges the
restriction-of-scalars tensor instance used by the categorical external tensor construction to
the literal tensor product, then packages the transported exact projective resolution as
`koszulBimoduleResolution`.
-/

open CategoryTheory TensorProduct

universe u
namespace Etingof

variable (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V]

abbrev S := SymmetricAlgebra k V
abbrev E := S k V ⊗[k] S k V

noncomputable def leftPlusRightLinear : V →ₗ[k] E k V :=
  (Algebra.TensorProduct.includeLeft.toLinearMap.comp (SymmetricAlgebra.ι k V)) +
    (Algebra.TensorProduct.includeRight.toLinearMap.comp (SymmetricAlgebra.ι k V))

noncomputable def leftSubRightLinear : V →ₗ[k] E k V :=
  (Algebra.TensorProduct.includeLeft.toLinearMap.comp (SymmetricAlgebra.ι k V)) -
    (Algebra.TensorProduct.includeRight.toLinearMap.comp (SymmetricAlgebra.ι k V))

noncomputable def plusAlg : S k V →ₐ[k] E k V :=
  SymmetricAlgebra.lift (leftPlusRightLinear k V)

noncomputable def minusAlg : S k V →ₐ[k] E k V :=
  SymmetricAlgebra.lift (leftSubRightLinear k V)

noncomputable def shearHom : E k V →ₐ[k] E k V :=
  Algebra.TensorProduct.lift (plusAlg k V) Algebra.TensorProduct.includeRight
    (fun _ _ => mul_comm _ _)

noncomputable def unshearHom : E k V →ₐ[k] E k V :=
  Algebra.TensorProduct.lift (minusAlg k V) Algebra.TensorProduct.includeRight
    (fun _ _ => mul_comm _ _)

lemma unshear_shear : (unshearHom k V).comp (shearHom k V) = AlgHom.id k (E k V) := by
  ext v <;> simp [unshearHom, shearHom, plusAlg, minusAlg, leftPlusRightLinear,
    leftSubRightLinear, ← Algebra.TensorProduct.one_def]

lemma shear_unshear : (shearHom k V).comp (unshearHom k V) = AlgHom.id k (E k V) := by
  ext v <;> simp [unshearHom, shearHom, plusAlg, minusAlg, leftPlusRightLinear,
    leftSubRightLinear, ← Algebra.TensorProduct.one_def]

noncomputable def shearEquiv : E k V ≃ₐ[k] E k V :=
  { shearHom k V with
    invFun := unshearHom k V
    left_inv := DFunLike.congr_fun (unshear_shear k V)
    right_inv := DFunLike.congr_fun (shear_unshear k V) }

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL

@[reducible] noncomputable def bimoduleModule : Module (E k V) (S k V) :=
  Module.compHom (S k V) (Algebra.TensorProduct.lmul' k).toRingHom

noncomputable def extAct (r : E k V) (z : KoszulAugModule k V ⊗[k] S k V) :=
  (extTensorModuleLeft k (S k V) (S k V) (KoszulAugModule k V) (S k V)).toSMul.smul r z

@[simp] lemma extAct_zero (z : KoszulAugModule k V ⊗[k] S k V) : extAct k V 0 z = 0 := by
  change extTensorRepLeft k (S k V) (S k V) (KoszulAugModule k V) (S k V) 0 z = 0
  rw [map_zero, LinearMap.zero_apply]

lemma extAct_add (r t : E k V) (z : KoszulAugModule k V ⊗[k] S k V) :
    extAct k V (r + t) z = extAct k V r z + extAct k V t z := by
  change extTensorRepLeft k (S k V) (S k V) (KoszulAugModule k V) (S k V) (r + t) z = _
  rw [map_add, LinearMap.add_apply]
  rfl

@[simp] lemma extAct_apply_zero (r : E k V) :
    extAct k V r (0 : KoszulAugModule k V ⊗[k] S k V) = 0 := by
  change extTensorRepLeft k (S k V) (S k V) (KoszulAugModule k V) (S k V) r 0 = 0
  exact map_zero _

lemma extAct_add_right (r : E k V) (x y : KoszulAugModule k V ⊗[k] S k V) :
    extAct k V r (x + y) = extAct k V r x + extAct k V r y := by
  change extTensorRepLeft k (S k V) (S k V) (KoszulAugModule k V) (S k V) r (x + y) = _
  exact map_add _ _ _

lemma extAct_mul (r t : E k V) (z : KoszulAugModule k V ⊗[k] S k V) :
    extAct k V (r * t) z = extAct k V r (extAct k V t z) := by
  change extTensorRepLeft k (S k V) (S k V) (KoszulAugModule k V) (S k V) (r * t) z = _
  rw [map_mul]
  rfl

lemma extAct_tmul (a b : S k V) (c : KoszulAugModule k V) (s : S k V) :
    extAct k V (a ⊗ₜ[k] b) (c ⊗ₜ[k] s) = (a • c) ⊗ₜ[k] (b * s) :=
  extTensorModuleLeft_smul_tmul k (S k V) (S k V)
    (KoszulAugModule k V) (S k V) a b c s

noncomputable def targetLinearEquiv :
    (KoszulAugModule k V ⊗[k] S k V) ≃ₗ[k] S k V :=
  TensorProduct.congr (KoszulAugModule.equiv k V) (LinearEquiv.refl k (S k V)) ≪≫ₗ
    TensorProduct.lid k (S k V)

@[simp] lemma targetLinearEquiv_tmul (c : KoszulAugModule k V) (s : S k V) :
    targetLinearEquiv k V (c ⊗ₜ[k] s) = KoszulAugModule.equiv k V c • s := by
  simp [targetLinearEquiv]

lemma targetLinearEquiv_plusAlg_smul (a : S k V)
    (z : KoszulAugModule k V ⊗[k] S k V) :
    targetLinearEquiv k V (extAct k V (plusAlg k V a) z) =
      a * targetLinearEquiv k V z := by
  induction a using SymmetricAlgebra.induction generalizing z with
  | algebraMap r =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, extAct_add_right, hx, hy, mul_add]
      | tmul c s =>
        rw [show plusAlg k V (algebraMap k (S k V) r) =
            algebraMap k (E k V) r by simp [plusAlg]]
        rw [show algebraMap k (E k V) r =
            algebraMap k (S k V) r ⊗ₜ[k] 1 by
              simp [Algebra.TensorProduct.algebraMap_apply]]
        rw [extAct_tmul, targetLinearEquiv_tmul, targetLinearEquiv_tmul]
        simp [Algebra.smul_def, mul_assoc]
  | ι v =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, extAct_add_right, hx, hy, mul_add]
      | tmul c s =>
        rw [show plusAlg k V (SymmetricAlgebra.ι k V v) =
            SymmetricAlgebra.ι k V v ⊗ₜ[k] 1 +
              1 ⊗ₜ[k] SymmetricAlgebra.ι k V v by
                simp [plusAlg, leftPlusRightLinear]]
        rw [extAct_add, extAct_tmul, extAct_tmul, map_add,
          targetLinearEquiv_tmul, targetLinearEquiv_tmul, targetLinearEquiv_tmul]
        simp [KoszulAugModule.equiv_smul, SymmetricAlgebra.algebraMapInv_ι,
          Algebra.smul_def]
        ring
  | mul a b ha hb =>
      rw [map_mul, extAct_mul, ha, hb, mul_assoc]
  | add a b ha hb =>
      rw [map_add, extAct_add, map_add, ha, hb, add_mul]

noncomputable def bimodAct (r : E k V) (s : S k V) : S k V :=
  (bimoduleModule k V).toSMul.smul r s

@[simp] lemma bimodAct_zero (s : S k V) : bimodAct k V 0 s = 0 := by
  exact zero_smul _ _

lemma bimodAct_add (r t : E k V) (s : S k V) :
    bimodAct k V (r + t) s = bimodAct k V r s + bimodAct k V t s := by
  change (bimoduleModule k V).toSMul.smul (r + t) s = _
  exact (bimoduleModule k V).add_smul r t s

@[simp] lemma bimodAct_apply_zero (r : E k V) : bimodAct k V r 0 = 0 := by
  exact smul_zero _

lemma bimodAct_add_right (r : E k V) (s t : S k V) :
    bimodAct k V r (s + t) = bimodAct k V r s + bimodAct k V r t := by
  exact smul_add _ _ _

lemma bimodAct_tmul (a b s : S k V) :
    bimodAct k V (a ⊗ₜ[k] b) s = (a * b) * s := by
  rfl

theorem targetLinearEquiv_shear_smul (r : E k V)
    (z : KoszulAugModule k V ⊗[k] S k V) :
    targetLinearEquiv k V
      (extAct k V (shearEquiv k V r) z) =
      bimodAct k V r (targetLinearEquiv k V z) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, extAct_add, map_add, hx, hy]
      rw [bimodAct_add]
  | tmul a b =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [map_add, extAct_add_right, map_add, hx, hy, bimodAct_add_right]
      | tmul c s =>
        rw [show shearEquiv k V (a ⊗ₜ[k] b) = plusAlg k V a *
            Algebra.TensorProduct.includeRight b by rfl,
          extAct_mul]
        rw [show extAct k V (Algebra.TensorProduct.includeRight b) (c ⊗ₜ[k] s) =
            c ⊗ₜ[k] (b * s) by
              simpa [Algebra.TensorProduct.includeRight_apply] using
                extAct_tmul k V 1 b c s]
        rw [targetLinearEquiv_plusAlg_smul]
        rw [bimodAct_tmul]
        change a * ((algebraMap k (S k V)) (KoszulAugModule.equiv k V c) * (b * s)) =
          (a * b) * ((algebraMap k (S k V)) (KoszulAugModule.equiv k V c) * s)
        ring

@[reducible] noncomputable def shearedExtModule :
    Module (E k V) (KoszulAugModule k V ⊗[k] S k V) := by
  letI : Module (E k V) (KoszulAugModule k V ⊗[k] S k V) :=
    extTensorModuleLeft k (S k V) (S k V) (KoszulAugModule k V) (S k V)
  exact Module.compHom _ (shearEquiv k V).toRingEquiv.toRingHom

noncomputable def shearedTargetIso :
    @ModuleCat.of (E k V) _ (KoszulAugModule k V ⊗[k] S k V) _
        (shearedExtModule k V) ≅
      @ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V) := by
  letI : Module (E k V) (KoszulAugModule k V ⊗[k] S k V) := shearedExtModule k V
  letI : Module (E k V) (S k V) := bimoduleModule k V
  exact LinearEquiv.toModuleIso
    { __ := targetLinearEquiv k V
      map_smul' := targetLinearEquiv_shear_smul k V }

/-! ## The external target bridge and the bimodule resolution -/

noncomputable abbrev koszulAugObj : ModuleCat.{u} (S k V) :=
  ModuleCat.of (S k V) (KoszulAugModule k V)

noncomputable abbrev regularObj : ModuleCat.{u} (S k V) :=
  ModuleCat.of (S k V) (S k V)

noncomputable abbrev externalTargetObj : ModuleCat.{u} (E k V) :=
  extTensorFunctorLeftObj k (S k V) (S k V) (koszulAugObj k V) (regularObj k V)

/-- A pure tensor in the categorical external target, with its restriction-of-scalars
instances fixed explicitly. -/
noncomputable def externalTargetTmul (c : koszulAugObj k V) (s : regularObj k V) :
    externalTargetObj k V :=
  @TensorProduct.tmul k _ (koszulAugObj k V) (regularObj k V) _ _
    (restrictModule₁L k (S k V) (koszulAugObj k V))
    (restrictModule₂L k (S k V) (regularObj k V)) c s

/-- A pure tensor in the literal target, with its native scalar instances fixed explicitly. -/
noncomputable def explicitTargetTmul (c : KoszulAugModule k V) (s : S k V) :
    KoszulAugModule k V ⊗[k] S k V :=
  @TensorProduct.tmul k _ (KoszulAugModule k V) (S k V) _ _
    KoszulAugModule.instModule Algebra.toModule c s

noncomputable def koszulAugRestrictEquiv :
    (res₁L k (S k V)).obj (koszulAugObj k V) ≃ₗ[k] KoszulAugModule k V where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by simp

noncomputable def regularRestrictEquiv :
    (res₂L k (S k V)).obj (regularObj k V) ≃ₗ[k] S k V where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identity-on-pure-tensors comparison between the categorical external target and the
literal tensor product used by `shearedTargetIso`. -/
noncomputable def externalTargetBridge :
    letI : Module k (externalTargetObj k V) := Module.compHom _ (algebraMap k (E k V))
    externalTargetObj k V ≃ₗ[k] KoszulAugModule k V ⊗[k] S k V :=
  extRestrictObjEquivL (koszulAugObj k V) (regularObj k V) ≪≫ₗ
    TensorProduct.congr (koszulAugRestrictEquiv k V) (regularRestrictEquiv k V)

@[simp]
theorem externalTargetBridge_tmul (c : koszulAugObj k V) (s : regularObj k V) :
    externalTargetBridge k V (externalTargetTmul k V c s) =
      explicitTargetTmul k V c s := rfl

theorem externalTarget_smul_tmul (a b : S k V) (c : koszulAugObj k V)
    (s : regularObj k V) :
    (externalTargetObj k V).isModule.toSMul.smul (a ⊗ₜ[k] b)
        (externalTargetTmul k V c s) =
      externalTargetTmul k V (a • c) (b • s) :=
  extTensorFunctorLeft_smul_tmul k (S k V) (S k V)
    (koszulAugObj k V) (regularObj k V) a b c s

theorem explicitTarget_smul_tmul (a b : S k V) (c : KoszulAugModule k V)
    (s : S k V) :
    (extTensorModuleLeft k (S k V) (S k V) (KoszulAugModule k V)
      (S k V)).toSMul.smul (a ⊗ₜ[k] b) (explicitTargetTmul k V c s) =
        explicitTargetTmul k V (a • c) (b * s) :=
  extTensorModuleLeft_smul_tmul k (S k V) (S k V)
    (KoszulAugModule k V) (S k V) a b c s

/-- The external-target comparison is equivariant for the full `SV ⊗ SV` action. -/
theorem externalTargetBridge_smul (r : E k V) (z : externalTargetObj k V) :
    externalTargetBridge k V ((externalTargetObj k V).isModule.toSMul.smul r z) =
      (extTensorModuleLeft k (S k V) (S k V) (KoszulAugModule k V)
        (S k V)).toSMul.smul r (externalTargetBridge k V z) := by
  induction r using TensorProduct.induction_on with
  | zero =>
      change externalTargetBridge k V 0 = 0
      simp
  | add x y hx hy =>
      calc
        externalTargetBridge k V
            ((externalTargetObj k V).isModule.toSMul.smul (x + y) z) =
          externalTargetBridge k V
            ((externalTargetObj k V).isModule.toSMul.smul x z +
              (externalTargetObj k V).isModule.toSMul.smul y z) :=
            congrArg (externalTargetBridge k V)
              ((externalTargetObj k V).isModule.add_smul x y z)
        _ = externalTargetBridge k V
              ((externalTargetObj k V).isModule.toSMul.smul x z) +
            externalTargetBridge k V
              ((externalTargetObj k V).isModule.toSMul.smul y z) := map_add _ _ _
        _ = _ := by
          rw [hx, hy]
          exact (extTensorModuleLeft k (S k V) (S k V)
            (KoszulAugModule k V) (S k V)).add_smul x y _ |>.symm
  | tmul a b =>
      induction z using TensorProduct.induction_on with
      | zero =>
          calc
            externalTargetBridge k V
                ((externalTargetObj k V).isModule.toSMul.smul (a ⊗ₜ[k] b) 0) =
              externalTargetBridge k V 0 := congrArg (externalTargetBridge k V)
                ((externalTargetObj k V).isModule.smul_zero _)
            _ = 0 := map_zero _
            _ = _ := ((extTensorModuleLeft k (S k V) (S k V)
              (KoszulAugModule k V) (S k V)).smul_zero _).symm
      | add x y hx hy =>
          calc
            externalTargetBridge k V
                ((externalTargetObj k V).isModule.toSMul.smul (a ⊗ₜ[k] b) (x + y)) =
              externalTargetBridge k V
                ((externalTargetObj k V).isModule.toSMul.smul (a ⊗ₜ[k] b) x +
                  (externalTargetObj k V).isModule.toSMul.smul (a ⊗ₜ[k] b) y) :=
                    congrArg (externalTargetBridge k V)
                      ((externalTargetObj k V).isModule.smul_add _ x y)
            _ = externalTargetBridge k V
                  ((externalTargetObj k V).isModule.toSMul.smul (a ⊗ₜ[k] b) x) +
                externalTargetBridge k V
                  ((externalTargetObj k V).isModule.toSMul.smul (a ⊗ₜ[k] b) y) := map_add _ _ _
            _ = (extTensorModuleLeft k (S k V) (S k V)
                  (KoszulAugModule k V) (S k V)).toSMul.smul (a ⊗ₜ[k] b)
                  (externalTargetBridge k V x + externalTargetBridge k V y) := by
                    rw [hx, hy]
                    exact (extTensorModuleLeft k (S k V) (S k V)
                      (KoszulAugModule k V) (S k V)).smul_add _ _ _ |>.symm
            _ = _ := congrArg
              ((extTensorModuleLeft k (S k V) (S k V)
                (KoszulAugModule k V) (S k V)).toSMul.smul (a ⊗ₜ[k] b))
              (map_add (externalTargetBridge k V) x y).symm
      | tmul c s =>
          change externalTargetBridge k V
              ((externalTargetObj k V).isModule.toSMul.smul (a ⊗ₜ[k] b)
                (externalTargetTmul k V c s)) =
            (extTensorModuleLeft k (S k V) (S k V)
              (KoszulAugModule k V) (S k V)).toSMul.smul
                (a ⊗ₜ[k] b)
                (externalTargetBridge k V (externalTargetTmul k V c s))
          rw [externalTarget_smul_tmul, externalTargetBridge_tmul,
            externalTargetBridge_tmul, explicitTarget_smul_tmul]
          simp [smul_eq_mul]

/-- The categorical external target is the literal external tensor target as an
`SV ⊗ SV`-module. -/
noncomputable def externalTargetIso : externalTargetObj k V ≅
    @ModuleCat.of (E k V) _ (KoszulAugModule k V ⊗[k] S k V) _
      (extTensorModuleLeft k (S k V) (S k V) (KoszulAugModule k V) (S k V)) := by
  let X := externalTargetObj k V
  change X ≅ _
  letI : Module (E k V) X := X.isModule
  letI : Module (E k V) (KoszulAugModule k V ⊗[k] S k V) :=
    extTensorModuleLeft k (S k V) (S k V) (KoszulAugModule k V) (S k V)
  let e : X ≃ₗ[E k V] KoszulAugModule k V ⊗[k] S k V :=
    { toFun := externalTargetBridge k V
      invFun := (externalTargetBridge k V).symm
      left_inv := (externalTargetBridge k V).left_inv
      right_inv := (externalTargetBridge k V).right_inv
      map_add' := (externalTargetBridge k V).map_add
      map_smul' := externalTargetBridge_smul k V }
  exact e.toModuleIso

noncomputable abbrev shearRestrictionFunctor :
    ModuleCat.{u} (E k V) ⥤ ModuleCat.{u} (E k V) :=
  ModuleCat.restrictScalars (shearEquiv k V).toRingEquiv.toRingHom

noncomputable def regularResolution : ProjectiveResolution (regularObj k V) :=
  ProjectiveResolution.self _

noncomputable def externalKoszulResolution
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    ProjectiveResolution (externalTargetObj k V) :=
  extTensorProjectiveResolutionLeft (k := k) (koszulResolution b) (regularResolution k V)

noncomputable def shearedExternalResolution
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    ProjectiveResolution ((shearRestrictionFunctor k V).obj (externalTargetObj k V)) :=
  (shearRestrictionFunctor k V).mapProjectiveResolution (externalKoszulResolution k V b)

noncomputable def actualShearedTargetIso :
    (shearRestrictionFunctor k V).obj (externalTargetObj k V) ≅
      @ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V) :=
  (shearRestrictionFunctor k V).mapIso (externalTargetIso k V) ≪≫ shearedTargetIso k V

/-- **The Koszul bimodule resolution** of `SV`: tensor the Koszul resolution of the trivial
module with the degree-zero resolution of the regular module, then restrict along the shear and
identify the target with `SV` carrying left/right multiplication. -/
noncomputable def koszulBimoduleResolution
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    ProjectiveResolution
      (@ModuleCat.of (E k V) _ (S k V) _ (bimoduleModule k V)) where
  complex := (shearedExternalResolution k V b).complex
  projective := (shearedExternalResolution k V b).projective
  π := (shearedExternalResolution k V b).π ≫
    (ChainComplex.single₀ (ModuleCat.{u} (E k V))).map (actualShearedTargetIso k V).hom
  quasiIso := by infer_instance

end Etingof
