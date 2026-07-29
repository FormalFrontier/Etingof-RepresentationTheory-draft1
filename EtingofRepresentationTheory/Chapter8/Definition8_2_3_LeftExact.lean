import EtingofRepresentationTheory.Chapter8.Problem8_2_6_Core
import EtingofRepresentationTheory.Chapter8.Definition8_2_3_RightExact
import Mathlib.CategoryTheory.Adjunction.Limits

set_option backward.isDefEq.respectTransparency false

/-!
# Right-exactness of `M ⊗_A -`

The functor `Etingof.tensorLeftFunctor A M : ModuleCat A ⥤ AddCommGrpCat` (Problem 8.2.6 core),
sending a left `A`-module `N` to `M ⊗_A N`, is a left adjoint: its right adjoint sends an
abelian group `B` to the left `A`-module `M →+ B`, with action `(a • f) m = f (aᵒᵖ • m)`. This is
the tensor–hom adjunction

  `Hom_ℤ(M ⊗_A N, B) ≃ Hom_A(N, M →+ B)`

on the *second* tensor factor (mirroring `Definition8_2_3_RightExact.lean`, which treats the first
factor). Consequently `M ⊗_A -` preserves all colimits, in particular finite colimits. This is the
`PreservesFiniteColimits` input that `Functor.leftDerivedZeroIsoSelf` needs to identify the zeroth
left derived functor of `M ⊗_A -` with `M ⊗_A -` itself: the base case of the balancing theorem
Problem 8.2.6(iv).
-/

open CategoryTheory Limits TensorProduct MulOpposite

namespace Etingof

universe u

variable (A : Type u) [Ring A]
variable (M : ModuleCat.{u} Aᵐᵒᵖ)

section HomModule

variable (B : Type u) [AddCommGroup B]

/-- The left `A`-action on `M →+ B` used as the value of the right adjoint of `M ⊗_A -`:
`(a • f) m = f (aᵒᵖ • m)`, using the right `A`-action `aᵒᵖ • m` on the right module `M`. -/
instance homLSMul : SMul A (M →+ B) where
  smul a f := f.comp (DistribSMul.toAddMonoidHom M (MulOpposite.op a))

@[simp] lemma homLSMul_apply (a : A) (f : M →+ B) (m : M) :
    (a • f) m = f (MulOpposite.op a • m) := rfl

/-- `M →+ B` is a left `A`-module. -/
instance homLModule : Module A (M →+ B) where
  one_smul f := by ext m; simp
  mul_smul a b f := by ext m; simp only [homLSMul_apply, MulOpposite.op_mul, mul_smul]
  smul_zero a := by ext m; simp
  smul_add a f g := by ext m; simp
  add_smul a b f := by ext m; simp only [homLSMul_apply, MulOpposite.op_add, add_smul, map_add,
    AddMonoidHom.add_apply]
  zero_smul f := by ext m; simp

end HomModule

variable {A M}
variable {N : Type u} [AddCommGroup N] [Module A N]

/-- Forward direction of the tensor–hom adjunction (second factor): an additive map
`φ : M ⊗_A N →+ B` curries to the left-`A`-linear map `n ↦ (m ↦ φ (m ⊗ n))`. -/
def homEquivToFunL {B : Type u} [AddCommGroup B] (φ : tensorOver A N M →+ B) :
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
      homLSMul_apply]
    rw [mk_smul_tmul (MulOpposite.op a), MulOpposite.unop_op]

@[simp] lemma homEquivToFunL_apply {B : Type u} [AddCommGroup B] (φ : tensorOver A N M →+ B)
    (n : N) (m : M) :
    homEquivToFunL φ n m = φ (m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) := rfl

/-- Inverse direction of the tensor–hom adjunction (second factor): a left-`A`-linear map
`Ψ : N →ₗ[A] (M →+ B)` uncurries to the additive map `M ⊗_A N →+ B`, `m ⊗ n ↦ Ψ n m`. -/
noncomputable def homEquivInvFunL {B : Type u} [AddCommGroup B] (Ψ : N →ₗ[A] (M →+ B)) :
    tensorOver A N M →+ B :=
  QuotientAddGroup.lift (balancedSubgroup A N M)
    (TensorProduct.liftAddHom (AddMonoidHom.flip Ψ.toAddMonoidHom) (fun r m n => by
      simp only [AddMonoidHom.flip_apply, LinearMap.toAddMonoidHom_coe, map_zsmul,
        AddMonoidHom.smul_apply]))
    (by
      refine AddSubgroup.closure_le _ |>.mpr ?_
      rintro _ ⟨a, m, n, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, TensorProduct.liftAddHom_tmul,
        AddMonoidHom.flip_apply, LinearMap.toAddMonoidHom_coe]
      rw [show Ψ (a • n) = a • Ψ n from map_smul Ψ a n, homLSMul_apply, sub_self])

@[simp] lemma homEquivInvFunL_mk {B : Type u} [AddCommGroup B] (Ψ : N →ₗ[A] (M →+ B))
    (m : M) (n : N) :
    homEquivInvFunL Ψ (m ⊗ₜ[ℤ] n : TensorProduct ℤ M N) = Ψ n m :=
  rfl

variable (A M)

/-- The right adjoint `B ↦ (M →+ B)` of `M ⊗_A -`, as a functor from abelian groups to left
`A`-modules. -/
noncomputable def homFunctorL : AddCommGrpCat.{u} ⥤ ModuleCat.{u} A where
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

/-- The tensor–hom adjunction `(M ⊗_A -) ⊣ (M →+ -)`. -/
noncomputable def tensorHomAdjunctionL : tensorLeftFunctor A M ⊣ homFunctorL A M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N B =>
        { toFun := fun φ => ModuleCat.ofHom (homEquivToFunL φ.hom)
          invFun := fun Ψ => AddCommGrpCat.ofHom (homEquivInvFunL Ψ.hom)
          left_inv := fun φ => by
            apply AddCommGrpCat.hom_ext
            apply tensorOver_hom_ext
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
        apply tensorOver_hom_ext
        intro m n
        rfl
      homEquiv_naturality_right := fun {N B B'} f g => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro n
        refine AddMonoidHom.ext fun m => ?_
        rfl }

/-- `M ⊗_A -` is a left adjoint, hence preserves finite colimits (it is right exact). This is the
input `Functor.leftDerivedZeroIsoSelf` needs for the balancing theorem's degree-0 base case. -/
noncomputable instance tensorLeftFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (tensorLeftFunctor A M) := by
  haveI : PreservesColimitsOfSize.{u, u} (tensorLeftFunctor A M) :=
    (tensorHomAdjunctionL A M).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

end Etingof
