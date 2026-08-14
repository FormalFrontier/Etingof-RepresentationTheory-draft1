/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import RepresentationTheory.Algebra.Homology.TensorProductConstruction
import Mathlib.CategoryTheory.Adjunction.Limits

set_option backward.isDefEq.respectTransparency false

/-!
# The balanced tensor-product adjunction

This module constructs the tensor-hom adjunction for the balanced tensor-product functor and
deduces its preservation of finite colimits.
-/

open CategoryTheory Limits TensorProduct MulOpposite
open RepresentationTheory.Algebra.Homology.TensorProductConstruction

namespace RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction

universe u

variable (A : Type u) [Ring A]
variable (N : Type u) [AddCommGroup N] [Module A N]

section HomModule

variable (B : Type u) [AddCommGroup B]

/-- The opposite-ring scalar action on additive homomorphisms from a fixed module. -/
instance addMonoidHomOppositeSMul : SMul Aᵐᵒᵖ (N →+ B) where
  smul x f := f.comp (DistribSMul.toAddMonoidHom N x.unop)

/-- Opposite scalar multiplication on an additive homomorphism is precomposition by scalar multiplication. -/
@[simp] lemma op_smul_addMonoidHom_apply (x : Aᵐᵒᵖ) (f : N →+ B) (n : N) :
    (x • f) n = f (x.unop • n) := rfl

/-- The opposite-ring module structure on additive homomorphisms from a fixed module. -/
instance addMonoidHomOppositeModule : Module Aᵐᵒᵖ (N →+ B) where
  one_smul f := by ext n; simp
  mul_smul x y f := by ext n; simp [MulOpposite.unop_mul, mul_smul]
  smul_zero x := by ext n; simp
  smul_add x f g := by ext n; simp
  add_smul x y f := by ext n; simp [MulOpposite.unop_add, add_smul]
  zero_smul f := by ext n; simp

end HomModule

variable {A N}
variable {M : Type u} [AddCommGroup M] [Module Aᵐᵒᵖ M]

/-- A scalar may be moved across a pure tensor from the first factor to the second factor. -/
lemma op_smul_tmul (x : Aᵐᵒᵖ) (m : M) (n : N) :
    (((x • m) ⊗ₜ[ℤ] n : TensorProduct ℤ M N) : ModuleConstruction A N M) =
      ((m ⊗ₜ[ℤ] (x.unop • n) : TensorProduct ℤ M N) : ModuleConstruction A N M) := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  apply AddSubgroup.subset_closure
  exact ⟨x.unop, m, n, by rw [MulOpposite.op_unop]⟩

/-- Uncurries an additive map from the balanced tensor product to a balanced bilinear map. -/
def balancedTensorProductUncurry {B : Type u} [AddCommGroup B]
    (φ : ModuleConstruction A N M →+ B) : M →ₗ[Aᵐᵒᵖ] (N →+ B) where
  toFun m := φ.comp ((QuotientAddGroup.mk' _).comp (TensorProduct.mk ℤ M N m).toAddMonoidHom)
  map_add' m m' := by
    ext n
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      TensorProduct.mk_apply, AddMonoidHom.add_apply]
    rw [add_tmul, map_add, map_add]
  map_smul' x m := by
    ext n
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      TensorProduct.mk_apply, QuotientAddGroup.mk'_apply, RingHom.id_apply,
      op_smul_addMonoidHom_apply]
    rw [op_smul_tmul]

/-- The uncurried map sends a pair to the value of the original map on its pure tensor. -/
@[simp] lemma balancedTensorProductUncurry_apply {B : Type u} [AddCommGroup B]
    (φ : ModuleConstruction A N M →+ B) (m : M) (n : N) :
    balancedTensorProductUncurry φ m n = φ (m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) := rfl

/-- Curries a balanced bilinear map into an additive homomorphism from the balanced tensor product. -/
noncomputable def balancedTensorProductCurry {B : Type u} [AddCommGroup B]
    (Φ : M →ₗ[Aᵐᵒᵖ] (N →+ B)) : ModuleConstruction A N M →+ B :=
  QuotientAddGroup.lift (integerTensorSubgroup A N M)
    (TensorProduct.liftAddHom Φ.toAddMonoidHom (fun r m n => by
      simp only [LinearMap.toAddMonoidHom_coe, map_zsmul, AddMonoidHom.smul_apply]))
    (by
      refine AddSubgroup.closure_le _ |>.mpr ?_
      rintro _ ⟨a, m, n, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, TensorProduct.liftAddHom_tmul,
        LinearMap.toAddMonoidHom_coe]
      rw [map_smul, op_smul_addMonoidHom_apply, MulOpposite.unop_op, sub_self])

/-- Evaluating the curried map on a pure tensor agrees with the original bilinear map. -/
@[simp] lemma balancedTensorProductCurry_tmul {B : Type u} [AddCommGroup B]
    (Φ : M →ₗ[Aᵐᵒᵖ] (N →+ B)) (m : M) (n : N) :
    balancedTensorProductCurry Φ (m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) = Φ m n :=
  rfl

/-- Additive homomorphisms out of the balanced tensor product agree when they agree on all pure tensors. -/
lemma balancedTensorProductHom_ext {B : Type u} [AddCommGroup B]
    {f g : ModuleConstruction A N M →+ B}
    (h : ∀ (m : M) (n : N),
      f (m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) = g (m ⊗ₜ[ℤ] n : TensorProduct ℤ M N)) :
    f = g := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  induction y with
  | zero => simp
  | tmul m n => exact h m n
  | add a b ha hb =>
    rw [show ((a + b : TensorProduct ℤ M N) : ModuleConstruction A N M) =
          (a : ModuleConstruction A N M) + b from map_add (QuotientAddGroup.mk' _) a b,
        map_add, map_add, ha, hb]

variable (A N)

/-- The functor sending an additive commutative group to its additive homomorphisms out of a fixed module. -/
noncomputable def addMonoidHomToOppositeModuleFunctor :
    AddCommGrpCat.{u} ⥤ ModuleCat.{u} Aᵐᵒᵖ where
  obj B := ModuleCat.of Aᵐᵒᵖ (N →+ B)
  map {B B'} g := ModuleCat.ofHom
    { toFun f := g.hom.comp f
      map_add' f f' := by ext n; simp
      map_smul' x f := by ext n; simp }
  map_id B := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    ext n
    simp
  map_comp {B B' B''} g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    ext n
    simp

/-- The tensor-product functor maps a pure tensor by applying the morphism to its first factor. -/
@[simp] lemma balancedTensorProductFunctor_map_tmul
    {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') (m : M) (n : N) :
    ((moduleConstructionFunctor A N).map f).hom
        ((m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) : ModuleConstruction A N M) =
      ((f.hom m ⊗ₜ[ℤ] n : TensorProduct ℤ M' N) : ModuleConstruction A N M') :=
  rfl

/-- The functorial image of a morphism acts by postcomposition on additive homomorphisms. -/
@[simp] lemma addMonoidHomToOppositeModuleFunctor_map_apply
    {B B' : AddCommGrpCat.{u}} (g : B ⟶ B') (f : N →+ B) :
    ((addMonoidHomToOppositeModuleFunctor A N).map g).hom f = g.hom.comp f :=
  rfl

/-- The adjunction between the balanced tensor-product functor and the additive-hom functor. -/
noncomputable def balancedTensorProductAdjunction :
    moduleConstructionFunctor A N ⊣ addMonoidHomToOppositeModuleFunctor A N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M B =>
        { toFun := fun φ => ModuleCat.ofHom (balancedTensorProductUncurry φ.hom)
          invFun := fun Φ => AddCommGrpCat.ofHom (balancedTensorProductCurry Φ.hom)
          left_inv := fun φ => by
            apply AddCommGrpCat.hom_ext
            apply balancedTensorProductHom_ext
            intro m n
            simp
          right_inv := fun Φ => by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro m
            refine AddMonoidHom.ext fun n => ?_
            simp }
      homEquiv_naturality_left_symm := fun {M' M B} f g => by
        apply AddCommGrpCat.hom_ext
        apply balancedTensorProductHom_ext
        intro m n
        rfl
      homEquiv_naturality_right := fun {M B B'} f g => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        refine AddMonoidHom.ext fun n => ?_
        rfl }

/-- The balanced tensor-product functor preserves finite colimits. -/
noncomputable instance balancedTensorProductFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (moduleConstructionFunctor A N) := by
  haveI : PreservesColimitsOfSize.{u, u} (moduleConstructionFunctor A N) :=
    (balancedTensorProductAdjunction A N).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

section CommBase

open scoped TensorProduct

/-- Identifies the balanced tensor product with the tensor product over a commutative ring under compatible actions. -/
noncomputable def balancedTensorProductEquivTensorProduct
    {A : Type u} [CommRing A] {N : Type u} [AddCommGroup N] [Module A N]
    {M : Type u} [AddCommGroup M] [Module Aᵐᵒᵖ M] [Module A M]
    (hcompat : ∀ (a : A) (m : M), (MulOpposite.op a • m : M) = a • m) :
    ModuleConstruction A N M ≃+ TensorProduct A M N :=
  let Φ : M →ₗ[Aᵐᵒᵖ] (N →+ TensorProduct A M N) :=
    { toFun := fun m => (TensorProduct.mk A M N m).toAddMonoidHom
      map_add' := fun m m' => by
        ext n
        simp only [map_add, LinearMap.add_apply, LinearMap.toAddMonoidHom_coe,
          TensorProduct.mk_apply, AddMonoidHom.add_apply]
      map_smul' := fun x m => by
        ext n
        simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, RingHom.id_apply,
          op_smul_addMonoidHom_apply]
        rw [show (x • m : M) = x.unop • m by rw [← hcompat, MulOpposite.op_unop],
          TensorProduct.smul_tmul] }
  let mkAdd : TensorProduct ℤ M N →+ ModuleConstruction A N M := QuotientAddGroup.mk' _
  let raw : M →+ N →+ ModuleConstruction A N M :=
    { toFun := fun m => mkAdd.comp (TensorProduct.mk ℤ M N m).toAddMonoidHom
      map_zero' := by ext n; simp
      map_add' := fun m m' => by
        ext n
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.add_apply,
          LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, map_add, AddMonoidHom.add_apply] }
  have hbal : ∀ (a : A) (m : M) (n : N), raw (a • m) n = raw m (a • n) := by
    intro a m n
    change (((a • m) ⊗ₜ[ℤ] n : TensorProduct ℤ M N) : ModuleConstruction A N M) =
      ((m ⊗ₜ[ℤ] (a • n) : TensorProduct ℤ M N) : ModuleConstruction A N M)
    rw [← hcompat a m]
    exact op_smul_tmul (MulOpposite.op a) m n
  { toFun := balancedTensorProductCurry Φ
    invFun := TensorProduct.liftAddHom raw hbal
    left_inv := by
      have h : (TensorProduct.liftAddHom raw hbal).comp (balancedTensorProductCurry Φ) =
          AddMonoidHom.id _ :=
        balancedTensorProductHom_ext fun m n => rfl
      intro z
      rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]
    right_inv := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul m n => rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    map_add' := fun x y => map_add _ x y }

/-- The comparison equivalence takes each pure tensor to the corresponding tensor over the ring. -/
@[simp] lemma balancedTensorProductEquivTensorProduct_tmul
    {A : Type u} [CommRing A] {N : Type u} [AddCommGroup N] [Module A N]
    {M : Type u} [AddCommGroup M] [Module Aᵐᵒᵖ M] [Module A M]
    (hcompat : ∀ (a : A) (m : M), (MulOpposite.op a • m : M) = a • m) (m : M) (n : N) :
    balancedTensorProductEquivTensorProduct hcompat
        ((m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) : ModuleConstruction A N M) =
      m ⊗ₜ[A] n := rfl

end CommBase

end RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction
