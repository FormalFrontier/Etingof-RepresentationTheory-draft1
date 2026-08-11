import EtingofRepresentationTheory.Chapter8.Definition8_2_3
import Mathlib.CategoryTheory.Adjunction.Limits

set_option backward.isDefEq.respectTransparency false

/-!
# Right-exactness of `- ⊗_A N`

The functor `tensorRightFunctor A N : ModuleCat Aᵐᵒᵖ ⥤ AddCommGrpCat` of Definition 8.2.3,
sending a right `A`-module `M` to `M ⊗_A N`, is a left adjoint: its right adjoint sends an
abelian group `B` to the right `A`-module (= left `Aᵐᵒᵖ`-module) `N →+ B`, with action
`(x • f) n = f (x.unop • n)`. This is the tensor–hom adjunction

  `Hom_ℤ(M ⊗_A N, B) ≃ Hom_{Aᵐᵒᵖ}(M, N →+ B)`.

Consequently `- ⊗_A N` preserves all colimits, in particular finite colimits. This is exactly
the input `PreservesFiniteColimits` that `Functor.leftDerivedZeroIsoSelf` needs to identify
`Tor₀ᴬ(-, N)` with `- ⊗_A N` (Problem 8.2.6(i), `Tor` half).
-/

open CategoryTheory Limits TensorProduct MulOpposite

namespace Etingof

universe u

variable (A : Type u) [Ring A]
variable (N : Type u) [AddCommGroup N] [Module A N]

section HomModule

variable (B : Type u) [AddCommGroup B]

/-- The right `A`-action (= left `Aᵐᵒᵖ`-action) on `N →+ B` used as the value of the right
adjoint of `- ⊗_A N`: `(x • f) n = f (x.unop • n)`. -/
instance homMopSMul : SMul Aᵐᵒᵖ (N →+ B) where
  smul x f := f.comp (DistribSMul.toAddMonoidHom N x.unop)

@[simp] lemma homMopSMul_apply (x : Aᵐᵒᵖ) (f : N →+ B) (n : N) :
    (x • f) n = f (x.unop • n) := rfl

/-- `N →+ B` is a right `A`-module (left `Aᵐᵒᵖ`-module). -/
instance homMopModule : Module Aᵐᵒᵖ (N →+ B) where
  one_smul f := by ext n; simp
  mul_smul x y f := by ext n; simp [MulOpposite.unop_mul, mul_smul]
  smul_zero x := by ext n; simp
  smul_add x f g := by ext n; simp
  add_smul x y f := by ext n; simp [MulOpposite.unop_add, add_smul]
  zero_smul f := by ext n; simp

end HomModule

variable {A N}
variable {M : Type u} [AddCommGroup M] [Module Aᵐᵒᵖ M]

/-- The balancing relation `(x • m) ⊗ n = m ⊗ (x.unop • n)` in `M ⊗_A N`, for `x : Aᵐᵒᵖ`. -/
lemma mk_smul_tmul (x : Aᵐᵒᵖ) (m : M) (n : N) :
    (((x • m) ⊗ₜ[ℤ] n : TensorProduct ℤ M N) : tensorOver A N M)
      = ((m ⊗ₜ[ℤ] (x.unop • n) : TensorProduct ℤ M N) : tensorOver A N M) := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  apply AddSubgroup.subset_closure
  exact ⟨x.unop, m, n, by rw [MulOpposite.op_unop]⟩

/-- Forward direction of the tensor–hom adjunction: an additive map `φ : M ⊗_A N →+ B` curries
to the right-`A`-linear map `m ↦ (n ↦ φ (m ⊗ n))`. -/
def homEquivToFun {B : Type u} [AddCommGroup B] (φ : tensorOver A N M →+ B) :
    M →ₗ[Aᵐᵒᵖ] (N →+ B) where
  toFun m := φ.comp ((QuotientAddGroup.mk' _).comp (TensorProduct.mk ℤ M N m).toAddMonoidHom)
  map_add' m m' := by
    ext n
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      TensorProduct.mk_apply, AddMonoidHom.add_apply]
    rw [add_tmul, map_add, map_add]
  map_smul' x m := by
    ext n
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      TensorProduct.mk_apply, QuotientAddGroup.mk'_apply, RingHom.id_apply, homMopSMul_apply]
    rw [mk_smul_tmul]

@[simp] lemma homEquivToFun_apply {B : Type u} [AddCommGroup B] (φ : tensorOver A N M →+ B)
    (m : M) (n : N) :
    homEquivToFun φ m n = φ (m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) := rfl

/-- Inverse direction of the tensor–hom adjunction: a right-`A`-linear map
`Φ : M →ₗ[Aᵐᵒᵖ] (N →+ B)` uncurries to the additive map `M ⊗_A N →+ B`,
`m ⊗ n ↦ Φ m n`. -/
noncomputable def homEquivInvFun {B : Type u} [AddCommGroup B] (Φ : M →ₗ[Aᵐᵒᵖ] (N →+ B)) :
    tensorOver A N M →+ B :=
  QuotientAddGroup.lift (balancedSubgroup A N M)
    (TensorProduct.liftAddHom Φ.toAddMonoidHom (fun r m n => by
      simp only [LinearMap.toAddMonoidHom_coe, map_zsmul, AddMonoidHom.smul_apply]))
    (by
      refine AddSubgroup.closure_le _ |>.mpr ?_
      rintro _ ⟨a, m, n, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, TensorProduct.liftAddHom_tmul,
        LinearMap.toAddMonoidHom_coe]
      rw [map_smul, homMopSMul_apply, MulOpposite.unop_op, sub_self])

@[simp] lemma homEquivInvFun_mk {B : Type u} [AddCommGroup B] (Φ : M →ₗ[Aᵐᵒᵖ] (N →+ B))
    (m : M) (n : N) :
    homEquivInvFun Φ (m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) = Φ m n :=
  rfl

/-- Two additive maps out of `M ⊗_A N` agree once they agree on the pure tensors `m ⊗ n`. -/
lemma tensorOver_hom_ext {B : Type u} [AddCommGroup B] {f g : tensorOver A N M →+ B}
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
    rw [show ((a + b : TensorProduct ℤ M N) : tensorOver A N M)
          = (a : tensorOver A N M) + b from map_add (QuotientAddGroup.mk' _) a b,
        map_add, map_add, ha, hb]

variable (A N)

/-- The right adjoint `B ↦ (N →+ B)` of `- ⊗_A N`, as a functor from abelian groups to right
`A`-modules. -/
noncomputable def homFunctorR : AddCommGrpCat.{u} ⥤ ModuleCat.{u} Aᵐᵒᵖ where
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

@[simp] lemma tensorRightFunctor_map_mk {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M')
    (m : M) (n : N) :
    ((tensorRightFunctor A N).map f).hom
        ((m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) : tensorOver A N M)
      = ((f.hom m ⊗ₜ[ℤ] n : TensorProduct ℤ M' N) : tensorOver A N M') :=
  rfl

@[simp] lemma homFunctorR_map_hom {B B' : AddCommGrpCat.{u}} (g : B ⟶ B') (f : N →+ B) :
    ((homFunctorR A N).map g).hom f = g.hom.comp f :=
  rfl

/-- The tensor–hom adjunction `(- ⊗_A N) ⊣ (N →+ -)`. -/
noncomputable def tensorHomAdjunction : tensorRightFunctor A N ⊣ homFunctorR A N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M B =>
        { toFun := fun φ => ModuleCat.ofHom (homEquivToFun φ.hom)
          invFun := fun Φ => AddCommGrpCat.ofHom (homEquivInvFun Φ.hom)
          left_inv := fun φ => by
            apply AddCommGrpCat.hom_ext
            apply tensorOver_hom_ext
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
        apply tensorOver_hom_ext
        intro m n
        rfl
      homEquiv_naturality_right := fun {M B B'} f g => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        refine AddMonoidHom.ext fun n => ?_
        rfl }

/-- `- ⊗_A N` is a left adjoint, hence preserves finite colimits (it is right exact). -/
noncomputable instance tensorRightFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (tensorRightFunctor A N) := by
  haveI : PreservesColimitsOfSize.{u, u} (tensorRightFunctor A N) :=
    (tensorHomAdjunction A N).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

section CommBase

open scoped TensorProduct

/-- For a commutative ring `A`, the ring tensor product `M ⊗_A N` of Definition 8.2.3 (a
quotient of the ℤ-tensor by the balancing relation) is additively isomorphic to Mathlib's
`TensorProduct A M N`, provided the right `A`-action on `M` (through `Aᵐᵒᵖ`) coincides with a
left `A`-module structure on `M`. This identifies `Tor₀ᴬ(M, N) ≅ tensorOver A N M`
with the honest tensor product `M ⊗[A] N` when `A` is commutative. -/
noncomputable def tensorOverEquivTensor {A : Type u} [CommRing A] {N : Type u} [AddCommGroup N]
    [Module A N] {M : Type u} [AddCommGroup M] [Module Aᵐᵒᵖ M] [Module A M]
    (hcompat : ∀ (a : A) (m : M), (MulOpposite.op a • m : M) = a • m) :
    tensorOver A N M ≃+ TensorProduct A M N :=
  let Φ : M →ₗ[Aᵐᵒᵖ] (N →+ TensorProduct A M N) :=
    { toFun := fun m => (TensorProduct.mk A M N m).toAddMonoidHom
      map_add' := fun m m' => by
        ext n
        simp only [map_add, LinearMap.add_apply, LinearMap.toAddMonoidHom_coe,
          TensorProduct.mk_apply, AddMonoidHom.add_apply]
      map_smul' := fun x m => by
        ext n
        simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, RingHom.id_apply,
          homMopSMul_apply]
        rw [show (x • m : M) = x.unop • m by rw [← hcompat, MulOpposite.op_unop],
          TensorProduct.smul_tmul] }
  let mkAdd : TensorProduct ℤ M N →+ tensorOver A N M := QuotientAddGroup.mk' _
  let raw : M →+ N →+ tensorOver A N M :=
    { toFun := fun m => mkAdd.comp (TensorProduct.mk ℤ M N m).toAddMonoidHom
      map_zero' := by ext n; simp
      map_add' := fun m m' => by
        ext n
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.add_apply,
          LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, map_add, AddMonoidHom.add_apply] }
  have hbal : ∀ (a : A) (m : M) (n : N), raw (a • m) n = raw m (a • n) := by
    intro a m n
    change (((a • m) ⊗ₜ[ℤ] n : TensorProduct ℤ M N) : tensorOver A N M)
       = ((m ⊗ₜ[ℤ] (a • n) : TensorProduct ℤ M N) : tensorOver A N M)
    rw [← hcompat a m]
    exact mk_smul_tmul (MulOpposite.op a) m n
  { toFun := homEquivInvFun Φ
    invFun := TensorProduct.liftAddHom raw hbal
    left_inv := by
      have h : (TensorProduct.liftAddHom raw hbal).comp (homEquivInvFun Φ) = AddMonoidHom.id _ :=
        tensorOver_hom_ext fun m n => rfl
      intro z
      rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]
    right_inv := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul m n => rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    map_add' := fun x y => map_add _ x y }

@[simp] lemma tensorOverEquivTensor_mk {A : Type u} [CommRing A] {N : Type u} [AddCommGroup N]
    [Module A N] {M : Type u} [AddCommGroup M] [Module Aᵐᵒᵖ M] [Module A M]
    (hcompat : ∀ (a : A) (m : M), (MulOpposite.op a • m : M) = a • m) (m : M) (n : N) :
    tensorOverEquivTensor hcompat ((m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) : tensorOver A N M)
      = m ⊗ₜ[A] n := rfl

end CommBase

end Etingof
