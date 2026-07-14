import EtingofRepresentationTheory.Chapter8.Problem8_2_6
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.Retract

/-!
# Tensoring with a projective right module is exact (flatness of projectives)

The functor `Etingof.tensorLeftFunctor A P : ModuleCat A ⥤ AddCommGrpCat`, `N ↦ P ⊗_A N`
(Problem 8.2.6, `Problem8_2_6.lean`), sends short exact sequences of left `A`-modules to short
exact sequences of abelian groups whenever the right `A`-module `P` is **projective**. This is the
flatness input the `Tor` long exact sequence in the second argument (Problem 8.2.6(iii)) and the
balancing theorem (Problem 8.2.6(iv), #6583) depend on.

## Proof route

`P` projective in `ModuleCat Aᵐᵒᵖ` is a retract of a free module `⊕_ι Aᵐᵒᵖ`.

1. **Unit case.** `tensorOver A N (of Aᵐᵒᵖ Aᵐᵒᵖ) ≅ N` naturally in `N` (the left unitor
   `Aᵐᵒᵖ ⊗_A N ≅ N`, `x ⊗ n ↦ x.unop • n`). So `tensorLeftFunctor A (of Aᵐᵒᵖ)` is naturally
   isomorphic to `forget₂ (ModuleCat A) AddCommGrpCat`, which is exact.
2. **Free case.** A coproduct of exact functors is exact.
3. **Retract case.** A retract of an exact functor preserves short exactness (mono/epi/exact all
   transfer along a retract of short complexes).
-/

open CategoryTheory Limits TensorProduct MulOpposite

namespace Etingof

universe u

variable (A : Type u) [Ring A]

/-! ### Unit case: `Aᵐᵒᵖ ⊗_A N ≅ N` -/

/-- The right-`Aᵐᵒᵖ`-linear map `Aᵐᵒᵖ →ₗ (N →+ N)`, `x ↦ (n ↦ x.unop • n)`, used to build the
left unitor `Aᵐᵒᵖ ⊗_A N ≅ N`. -/
noncomputable def unitorΦ (N : Type u) [AddCommGroup N] [Module A N] :
    Aᵐᵒᵖ →ₗ[Aᵐᵒᵖ] (N →+ N) where
  toFun x := DistribSMul.toAddMonoidHom N x.unop
  map_add' x y := by ext n; simp [MulOpposite.unop_add, add_smul]
  map_smul' a x := by
    ext n
    simp only [DistribSMul.toAddMonoidHom_apply, RingHom.id_apply, homMopSMul_apply]
    rw [smul_eq_mul, MulOpposite.unop_mul, mul_smul]

@[simp] lemma unitorΦ_apply (N : Type u) [AddCommGroup N] [Module A N] (x : Aᵐᵒᵖ) (n : N) :
    unitorΦ A N x n = x.unop • n := rfl

/-- The forward map of the left unitor `Aᵐᵒᵖ ⊗_A N →+ N`, `x ⊗ n ↦ x.unop • n`. -/
noncomputable def unitorHom (N : Type u) [AddCommGroup N] [Module A N] :
    tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) →+ N :=
  homEquivInvFun (unitorΦ A N)

@[simp] lemma unitorHom_mk (N : Type u) [AddCommGroup N] [Module A N] (x : Aᵐᵒᵖ) (n : N) :
    unitorHom A N ((x ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) : tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))
      = x.unop • n := rfl

/-- The inverse map of the left unitor `N →+ Aᵐᵒᵖ ⊗_A N`, `n ↦ 1 ⊗ n`. -/
noncomputable def unitorInv (N : Type u) [AddCommGroup N] [Module A N] :
    N →+ tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) where
  toFun n := ((1 ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) : tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))
  map_zero' := by simp
  map_add' n n' := by
    rw [tmul_add]
    exact map_add (QuotientAddGroup.mk' _) _ _

/-- The left unitor `Aᵐᵒᵖ ⊗_A N ≅ N` as an additive equivalence. -/
noncomputable def unitorEquiv (N : Type u) [AddCommGroup N] [Module A N] :
    tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) ≃+ N where
  toFun := unitorHom A N
  invFun := unitorInv A N
  left_inv := by
    have h : (unitorInv A N).comp (unitorHom A N) = AddMonoidHom.id _ := by
      apply tensorOver_hom_ext
      intro x n
      rw [AddMonoidHom.comp_apply, unitorHom_mk, AddMonoidHom.id_apply]
      change ((1 ⊗ₜ[ℤ] (x.unop • n) : TensorProduct ℤ Aᵐᵒᵖ N) :
          tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) = _
      rw [← mk_smul_tmul x 1 n, smul_eq_mul, mul_one]
    intro z
    rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]
  right_inv n := by
    change unitorHom A N ((1 ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) :
      tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) = n
    rw [unitorHom_mk, MulOpposite.unop_one, one_smul]
  map_add' := map_add _

@[simp] lemma unitorEquiv_apply (N : Type u) [AddCommGroup N] [Module A N] (x : Aᵐᵒᵖ) (n : N) :
    unitorEquiv A N ((x ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) :
      tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) = x.unop • n := rfl

/-- The natural isomorphism `tensorLeftFunctor A (of Aᵐᵒᵖ) ≅ forget₂ (ModuleCat A) AddCommGrpCat`
witnessing the left unitor `Aᵐᵒᵖ ⊗_A N ≅ N`. -/
noncomputable def unitorNatIso :
    tensorLeftFunctor A (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) ≅ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun N => AddEquiv.toAddCommGrpIso (unitorEquiv A N))
    (by
      intro N N' g
      apply AddCommGrpCat.hom_ext
      apply tensorOver_hom_ext
      intro x n
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
        tensorLeftFunctor, AddCommGrpCat.hom_ofHom, AddEquiv.toAddCommGrpIso_hom,
        ModuleCat.forget₂_map]
      rw [AddEquiv.coe_toAddMonoidHom, AddEquiv.coe_toAddMonoidHom, tensorSndMap_mk]
      exact (map_smul g.hom x.unop n).symm)

/-- **Unit case.** Tensoring a short exact sequence with the regular right module `Aᵐᵒᵖ` (i.e.
`A` as a right `A`-module) is short exact: `tensorLeftFunctor A (of Aᵐᵒᵖ) ≅ forget₂`, and the
forgetful functor `ModuleCat A ⥤ AddCommGrpCat` is exact. -/
lemma unit_map_shortExact {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (S.map (tensorLeftFunctor A (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (unitorNatIso A)).symm
    (hS.map_of_exact (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))

end Etingof
