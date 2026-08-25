/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.ModuleCategory.Auxiliary
import RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits

set_option backward.isDefEq.respectTransparency false
set_option linter.dupNamespace false

open CategoryTheory Limits TensorProduct MulOpposite
open RepresentationTheory.Algebra.Homology.TensorProductConstruction
open RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction
open RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary

namespace RepresentationTheory.Algebra.Category.ModuleCat.TensorHom

universe u

namespace ModuleCat

variable (A : Type u) [Ring A]
variable (M : ModuleCat.{u} Aᵐᵒᵖ)

section HomModule

variable (B : Type u) [AddCommGroup B]

/-- The scalar action on additive homomorphisms from a right A-module. -/
instance rightModuleHomSMul : SMul A (M →+ B) where
  smul a f := f.comp (DistribSMul.toAddMonoidHom M (MulOpposite.op a))

/-- Scalar multiplication of an additive homomorphism is evaluated by acting on its input through the opposite ring. -/
@[simp] lemma rightModuleHom_smul_apply (a : A) (f : M →+ B) (m : M) :
    (a • f) m = f (MulOpposite.op a • m) := rfl

/-- The A-module structure on additive homomorphisms from a right A-module to an additive commutative group. -/
instance rightModuleHomModule : Module A (M →+ B) where
  one_smul f := by ext m; simp
  mul_smul a b f := by ext m; simp only [rightModuleHom_smul_apply, MulOpposite.op_mul, mul_smul]
  smul_zero a := by ext m; simp
  smul_add a f g := by ext m; simp
  add_smul a b f := by
    ext m
    simp only [rightModuleHom_smul_apply, MulOpposite.op_add, add_smul, map_add,
      AddMonoidHom.add_apply]
  zero_smul f := by ext m; simp

end HomModule

variable {A M}
variable {N : Type u} [AddCommGroup N] [Module A N]

/-- Converts an additive homomorphism with the displayed domain into a linear family of additive homomorphisms out of the right module. -/
def addMonoidHomToLinearMap {B : Type u} [AddCommGroup B] (φ : ModuleConstruction A N M →+ B) :
    N →ₗ[A] (M →+ B) where
  toFun n := φ.comp ((QuotientAddGroup.mk' _).comp ((TensorProduct.mk ℤ M N).flip n).toAddMonoidHom)
  map_add' n n' := by
    ext m
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearMap.flip_apply, TensorProduct.mk_apply, AddMonoidHom.add_apply]
    rw [tmul_add, map_add, map_add]
  map_smul' a n := by
    ext m
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearMap.flip_apply, TensorProduct.mk_apply, QuotientAddGroup.mk'_apply, RingHom.id_apply,
      rightModuleHom_smul_apply]
    rw [op_smul_tmul (MulOpposite.op a), MulOpposite.unop_op]

/-- Successive evaluation of the resulting linear map agrees with the original additive homomorphism on the class of the corresponding pure tensor. -/
@[simp] lemma addMonoidHomToLinearMap_apply {B : Type u} [AddCommGroup B] (φ : ModuleConstruction A N M →+ B)
    (n : N) (m : M) :
    addMonoidHomToLinearMap φ n m = φ (m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) := rfl

/-- Converts a linear family of additive homomorphisms into an additive homomorphism with the displayed domain. -/
noncomputable def linearMapToAddMonoidHom {B : Type u} [AddCommGroup B] (Ψ : N →ₗ[A] (M →+ B)) :
    ModuleConstruction A N M →+ B :=
  QuotientAddGroup.lift (integerTensorSubgroup A N M)
    (TensorProduct.liftAddHom (AddMonoidHom.flip Ψ.toAddMonoidHom) (fun r m n => by
      simp only [AddMonoidHom.flip_apply, LinearMap.toAddMonoidHom_coe, map_zsmul,
        AddMonoidHom.smul_apply]))
    (by
      refine AddSubgroup.closure_le _ |>.mpr ?_
      rintro _ ⟨a, m, n, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, TensorProduct.liftAddHom_tmul,
        AddMonoidHom.flip_apply, LinearMap.toAddMonoidHom_coe]
      rw [show Ψ (a • n) = a • Ψ n from map_smul Ψ a n, rightModuleHom_smul_apply, sub_self])

/-- On the class of a pure tensor, the resulting additive homomorphism agrees with successive evaluation of the original linear map. -/
@[simp] lemma linearMapToAddMonoidHom_mk_tmul {B : Type u} [AddCommGroup B] (Ψ : N →ₗ[A] (M →+ B))
    (m : M) (n : N) :
    linearMapToAddMonoidHom Ψ (m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) = Ψ n m :=
  rfl

variable (A M)

/-- The functor from additive commutative groups to A-modules associated with a right A-module. -/
noncomputable def rightModuleHomFunctor : AddCommGrpCat.{u} ⥤ ModuleCat.{u} A where
  obj B := ModuleCat.of A (M →+ B)
  map {B B'} g := ModuleCat.ofHom
    { toFun f := g.hom.comp f
      map_add' f f' := by ext m; simp
      map_smul' a f := by ext m; simp }
  map_id B := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    ext m
    simp
  map_comp {B B' B''} g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    ext m
    simp

/-- An adjunction whose right adjoint is the additive-hom functor associated with a right A-module. -/
noncomputable def rightModuleHomAdjunction :
    rightModuleToAddCommGrpFunctor A M ⊣ rightModuleHomFunctor A M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N B =>
        { toFun := fun φ => ModuleCat.ofHom (addMonoidHomToLinearMap φ.hom)
          invFun := fun Ψ => AddCommGrpCat.ofHom (linearMapToAddMonoidHom Ψ.hom)
          left_inv := fun φ => by
            apply AddCommGrpCat.hom_ext
            apply balancedTensorProductHom_ext
            intro m n
            simp
          right_inv := fun Ψ => by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro n
            refine AddMonoidHom.ext fun m => ?_
            simp }
      homEquiv_naturality_left_symm := fun {N' N B} f g => by
        apply AddCommGrpCat.hom_ext
        apply balancedTensorProductHom_ext
        intro m n
        rfl
      homEquiv_naturality_right := fun {N B B'} f g => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro n
        refine AddMonoidHom.ext fun m => ?_
        rfl }

/-- The displayed functor preserves finite colimits. -/
noncomputable instance rightModuleHomLeftAdjoint_preservesFiniteColimits :
    PreservesFiniteColimits (rightModuleToAddCommGrpFunctor A M) := by
  haveI : PreservesColimitsOfSize.{u, u} (rightModuleToAddCommGrpFunctor A M) :=
    (rightModuleHomAdjunction A M).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

end ModuleCat

end RepresentationTheory.Algebra.Category.ModuleCat.TensorHom
