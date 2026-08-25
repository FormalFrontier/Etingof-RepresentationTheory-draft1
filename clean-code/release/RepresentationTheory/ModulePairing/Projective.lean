/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.ModuleCategory.Auxiliary
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Retract
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.BigOperators.Finsupp.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Projective module pairings

The functor associated with a projective opposite-ring module preserves short exact complexes,
and its positive left-derived values vanish.
-/

open CategoryTheory Limits TensorProduct MulOpposite

namespace RepresentationTheory.ModulePairing.Projective

universe u

variable (A : Type u) [Ring A]

/-! ### Stability of short exactness under retracts -/

/-- Short exactness descends from a short complex to any retract of it in an abelian category. -/
lemma CategoryTheory.ShortComplex.shortExact_of_retract {D : Type*} [Category.{u} D] [Abelian D]
    {T U : ShortComplex D} (h : Retract T U) (hU : U.ShortExact) : T.ShortExact := by
  have e₁ : h.i.τ₁ ≫ h.r.τ₁ = 𝟙 _ := by
    rw [← ShortComplex.comp_τ₁, h.retract, ShortComplex.id_τ₁]
  have e₂ : h.i.τ₂ ≫ h.r.τ₂ = 𝟙 _ := by
    rw [← ShortComplex.comp_τ₂, h.retract, ShortComplex.id_τ₂]
  have e₃ : h.i.τ₃ ≫ h.r.τ₃ = 𝟙 _ := by
    rw [← ShortComplex.comp_τ₃, h.retract, ShortComplex.id_τ₃]
  have hf : RetractArrow T.f U.f :=
    { i := Arrow.homMk h.i.τ₁ h.i.τ₂ h.i.comm₁₂
      r := Arrow.homMk h.r.τ₁ h.r.τ₂ h.r.comm₁₂
      retract := Arrow.hom_ext _ _ e₁ e₂ }
  have hg : RetractArrow T.g U.g :=
    { i := Arrow.homMk h.i.τ₂ h.i.τ₃ h.i.comm₂₃
      r := Arrow.homMk h.r.τ₂ h.r.τ₃ h.r.comm₂₃
      retract := Arrow.hom_ext _ _ e₂ e₃ }
  have hexact : T.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    have hz : IsZero U.homology := by
      rw [← ShortComplex.exact_iff_isZero_homology]; exact hU.exact
    have hr : Retract T.homology U.homology := h.map (ShortComplex.homologyFunctor D)
    rw [IsZero.iff_id_eq_zero, ← hr.retract, hz.eq_of_tgt hr.i 0, Limits.zero_comp]
  have hmono : Mono T.f :=
    MorphismProperty.of_retract (P := MorphismProperty.monomorphisms D) hf hU.mono_f
  have hepi : Epi T.g :=
    MorphismProperty.of_retract (P := MorphismProperty.epimorphisms D) hg hU.epi_g
  exact ShortComplex.ShortExact.mk' hexact hmono hepi

/-! ### The regular opposite-ring module -/

/-- The opposite-ring-linear map sending each scalar to its additive action on the coefficient module. -/
noncomputable def ModulePairing.opScalarActionLinearMap (N : Type u) [AddCommGroup N] [Module A N] :
    Aᵐᵒᵖ →ₗ[Aᵐᵒᵖ] (N →+ N) where
  toFun x := DistribSMul.toAddMonoidHom N x.unop
  map_add' x y := by ext n; simp [MulOpposite.unop_add, add_smul]
  map_smul' a x := by
    ext n
    simp only [DistribSMul.toAddMonoidHom_apply, RingHom.id_apply, RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.op_smul_addMonoidHom_apply]
    rw [smul_eq_mul, MulOpposite.unop_mul, mul_smul]

/-- Evaluating the opposite-scalar action map agrees with the action of the underlying ring element. -/
@[simp] lemma ModulePairing.opScalarActionLinearMap_apply (N : Type u) [AddCommGroup N] [Module A N] (x : Aᵐᵒᵖ) (n : N) :
    ModulePairing.opScalarActionLinearMap A N x n = x.unop • n := rfl

/-- An additive map from the displayed construction on the regular opposite-ring module to the coefficient module. -/
noncomputable def ModulePairing.regularModuleTensorToModule (N : Type u) [AddCommGroup N] [Module A N] :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) →+ N :=
  RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry (ModulePairing.opScalarActionLinearMap A N)

/-- The additive map out of the regular-module construction sends a displayed pure tensor to scalar action. -/
@[simp] lemma ModulePairing.regularModuleTensorToModule_tmul (N : Type u) [AddCommGroup N] [Module A N] (x : Aᵐᵒᵖ) (n : N) :
    ModulePairing.regularModuleTensorToModule A N ((x ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))
      = x.unop • n := rfl

/-- An additive map from the coefficient module into the displayed construction associated with the regular opposite-ring module. -/
noncomputable def ModulePairing.Auxiliary.moduleToRegularConstructionAddHom (N : Type u) [AddCommGroup N] [Module A N] :
    N →+ RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) where
  toFun n := ((1 ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))
  map_zero' := by simp
  map_add' n n' := by
    rw [tmul_add]
    exact map_add (QuotientAddGroup.mk' _) _ _

/-- An additive equivalence from the displayed construction on the regular opposite-ring module to the coefficient module. -/
noncomputable def ModulePairing.regularModuleTensorAddEquiv (N : Type u) [AddCommGroup N] [Module A N] :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) ≃+ N where
  toFun := ModulePairing.regularModuleTensorToModule A N
  invFun := ModulePairing.Auxiliary.moduleToRegularConstructionAddHom A N
  left_inv := by
    have h : (ModulePairing.Auxiliary.moduleToRegularConstructionAddHom A N).comp (ModulePairing.regularModuleTensorToModule A N) = AddMonoidHom.id _ := by
      apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
      intro x n
      rw [AddMonoidHom.comp_apply, ModulePairing.regularModuleTensorToModule_tmul, AddMonoidHom.id_apply]
      change ((1 ⊗ₜ[ℤ] (x.unop • n) : TensorProduct ℤ Aᵐᵒᵖ N) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) = _
      rw [← RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.op_smul_tmul x 1 n, smul_eq_mul, mul_one]
    intro z
    rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]
  right_inv n := by
    change ModulePairing.regularModuleTensorToModule A N ((1 ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) :
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) = n
    rw [ModulePairing.regularModuleTensorToModule_tmul, MulOpposite.unop_one, one_smul]
  map_add' := map_add _

/-- The regular-module additive equivalence sends a displayed pure tensor to the action of its underlying scalar. -/
@[simp] lemma ModulePairing.regularModuleTensorAddEquiv_tmul (N : Type u) [AddCommGroup N] [Module A N] (x : Aᵐᵒᵖ) (n : N) :
    ModulePairing.regularModuleTensorAddEquiv A N ((x ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) :
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) = x.unop • n := rfl

/-- The functor associated with the regular opposite-ring module is naturally isomorphic to the forgetful functor to additive commutative groups. -/
noncomputable def ModulePairing.regularModuleFunctorIsoForget :
    RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) ≅ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun N => AddEquiv.toAddCommGrpIso (ModulePairing.regularModuleTensorAddEquiv A N))
    (by
      intro N N' g
      apply AddCommGrpCat.hom_ext
      apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
      intro x n
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
        RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor, AddCommGrpCat.hom_ofHom, AddEquiv.toAddCommGrpIso_hom,
        ModuleCat.forget₂_map]
      rw [AddEquiv.coe_toAddMonoidHom, AddEquiv.coe_toAddMonoidHom, RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryAddMonoidHom_tmul]
      exact (map_smul g.hom x.unop n).symm)

/-- The functor associated with the regular opposite-ring module preserves short exact complexes. -/
lemma ModulePairing.regularModuleFunctor_map_shortExact {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (S.map (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (ModulePairing.regularModuleFunctorIsoForget A)).symm
    (hS.map_of_exact (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))

/-! ### Functoriality in the opposite-ring module -/

/-- A morphism of opposite-ring modules induces a morphism between their associated functors to additive commutative groups. -/
noncomputable def ModulePairing.Auxiliary.moduleFunctorMap {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M ⟶ RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M' where
  app N := AddCommGrpCat.ofHom (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionMap A N f)
  naturality {N N'} g := by
    apply AddCommGrpCat.hom_ext
    apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
    intro m n
    rfl

/-- A functor assigning to each opposite-ring module a functor from modules to additive commutative groups. -/
noncomputable def ModulePairing.Auxiliary.moduleBifunctor :
    ModuleCat.{u} Aᵐᵒᵖ ⥤ (ModuleCat.{u} A ⥤ AddCommGrpCat.{u}) where
  obj M := RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M
  map f := ModulePairing.Auxiliary.moduleFunctorMap A f
  map_id M := by
    refine NatTrans.ext (funext fun N => ?_)
    apply AddCommGrpCat.hom_ext
    apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
    intro m n
    rfl
  map_comp {M M' M''} f f' := by
    refine NatTrans.ext (funext fun N => ?_)
    apply AddCommGrpCat.hom_ext
    apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
    intro m n
    rfl

/-- A retract of opposite-ring modules induces a retract between the short complexes obtained from the associated module functors. -/
noncomputable def ModulePairing.shortComplexMap_retract {S : ShortComplex (ModuleCat.{u} A)} {P F : ModuleCat.{u} Aᵐᵒᵖ}
    (h : Retract P F) :
    Retract (S.map (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A P)) (S.map (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A F)) :=
  let hF : Retract (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A P) (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A F) := h.map (ModulePairing.Auxiliary.moduleBifunctor A)
  { i := S.mapNatTrans hF.i
    r := S.mapNatTrans hF.r
    retract := ShortComplex.hom_ext _ _
      (NatTrans.congr_app hF.retract S.X₁)
      (NatTrans.congr_app hF.retract S.X₂)
      (NatTrans.congr_app hF.retract S.X₃) }

/-! ### Free opposite-ring modules -/

/-- The endofunctor on additive commutative groups given by finitely supported functions on an indexing type. -/
noncomputable def ModulePairing.finsuppFunctor (X : Type u) : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj B := AddCommGrpCat.of (X →₀ B)
  map {B B'} g := AddCommGrpCat.ofHom (Finsupp.mapRange.addMonoidHom g.hom)
  map_id B := by
    apply AddCommGrpCat.hom_ext
    simp only [AddCommGrpCat.hom_ofHom, AddCommGrpCat.hom_id, Finsupp.mapRange.addMonoidHom_id]
  map_comp {B B' B''} g h := by
    apply AddCommGrpCat.hom_ext
    simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
      Finsupp.mapRange.addMonoidHom_comp]

/-- Applying the image of a homomorphism under the finitely supported-function functor agrees with mapping the range. -/
@[simp] lemma ModulePairing.finsuppFunctor_map_apply (X : Type u) {B B' : AddCommGrpCat.{u}} (g : B ⟶ B')
    (p : X →₀ B) :
    ((ModulePairing.finsuppFunctor X).map g).hom p = Finsupp.mapRange.addMonoidHom g.hom p :=
  rfl

/-- The finitely supported-function endofunctor preserves zero morphisms. -/
instance ModulePairing.finsuppFunctor_preservesZeroMorphisms (X : Type u) : (ModulePairing.finsuppFunctor X).PreservesZeroMorphisms where
  map_zero B B' := by
    apply AddCommGrpCat.hom_ext
    change Finsupp.mapRange.addMonoidHom (0 : ↑B →+ ↑B') = 0
    apply Finsupp.addHom_ext
    intro x b
    simp [Finsupp.mapRange.addMonoidHom, Finsupp.mapRange_single]

/-- A short exact complex remains short exact after applying the finitely supported-function functor. -/
lemma ModulePairing.shortExact_map_finsuppFunctor (X : Type u) {T : ShortComplex AddCommGrpCat.{u}}
    (hT : T.ShortExact) : (T.map (ModulePairing.finsuppFunctor X)).ShortExact := by
  have hf : Function.Injective T.f.hom := by
    have := hT.mono_f; rwa [AddCommGrpCat.mono_iff_injective] at this
  have hg : Function.Surjective T.g.hom := by
    have := hT.epi_g; rwa [AddCommGrpCat.epi_iff_surjective] at this
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.ab_exact_iff]
    intro p hp
    change X →₀ ↑T.X₂ at p
    change Finsupp.mapRange.addMonoidHom T.g.hom p = 0 at hp
    have hpx : ∀ x, T.g.hom (p x) = 0 := by
      intro x
      have hx := DFunLike.congr_fun hp x
      simpa [Finsupp.mapRange_apply] using hx
    have hchoose : ∀ x, ∃ y, T.f.hom y = p x := fun x =>
      T.ab_exact_iff.mp hT.exact (p x) (hpx x)
    choose c hc using hchoose
    refine ⟨∑ x ∈ p.support, Finsupp.single x (c x), ?_⟩
    change Finsupp.mapRange.addMonoidHom T.f.hom (∑ x ∈ p.support, Finsupp.single x (c x)) = p
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun x _ => by
      change Finsupp.mapRange T.f.hom (map_zero _) (Finsupp.single x (c x)) = Finsupp.single x (p x)
      rw [Finsupp.mapRange_single, hc])]
    exact Finsupp.sum_single p
  · rw [AddCommGrpCat.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) hf
  · rw [AddCommGrpCat.epi_iff_surjective]
    exact Finsupp.mapRange_surjective _ (map_zero _) hg

/-- The opposite-ring-linear map that sends a finitely supported scalar family to an additive map into coefficient-valued finitely supported functions. -/
noncomputable def ModulePairing.finsuppScalarActionLinearMap (X N : Type u) [AddCommGroup N] [Module A N] :
    (X →₀ Aᵐᵒᵖ) →ₗ[Aᵐᵒᵖ] (N →+ (X →₀ N)) :=
  Finsupp.lift (N →+ (X →₀ N)) Aᵐᵒᵖ X (fun x => Finsupp.singleAddHom x)

/-- On a scalar supported at one index, the finitely supported scalar-action map is the corresponding scalar multiple of the single-coordinate additive map. -/
lemma ModulePairing.finsuppScalarActionLinearMap_single (X N : Type u) [AddCommGroup N] [Module A N] (x : X) (a : Aᵐᵒᵖ) :
    ModulePairing.finsuppScalarActionLinearMap A X N (Finsupp.single x a) = a • Finsupp.singleAddHom x := by
  simp only [ModulePairing.finsuppScalarActionLinearMap, Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul]

/-- Evaluating the finitely supported scalar-action map on a single supported scalar yields a single supported coefficient. -/
@[simp] lemma ModulePairing.finsuppScalarActionLinearMap_single_apply (X N : Type u) [AddCommGroup N] [Module A N]
    (x : X) (a : Aᵐᵒᵖ) (n : N) :
    ModulePairing.finsuppScalarActionLinearMap A X N (Finsupp.single x a) n = Finsupp.single x (a.unop • n) := by
  rw [ModulePairing.finsuppScalarActionLinearMap_single, RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.op_smul_addMonoidHom_apply]; rfl

/-- For each index, an additive map from the coefficient module into the displayed construction associated with a free opposite-ring module. -/
noncomputable def ModulePairing.Auxiliary.freeModuleIndexAddHom (X N : Type u) [AddCommGroup N] [Module A N] (x : X) :
    N →+ RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ)) where
  toFun n := ((Finsupp.single x (1 : Aᵐᵒᵖ) ⊗ₜ[ℤ] n :
    TensorProduct ℤ (X →₀ Aᵐᵒᵖ) N) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ)))
  map_zero' := by simp
  map_add' n n' := by rw [tmul_add]; exact map_add (QuotientAddGroup.mk' _) _ _

/-- An additive equivalence from the displayed construction on a free opposite-ring module to finitely supported functions with values in the coefficient module. -/
noncomputable def ModulePairing.freeModuleTensorAddEquiv (X N : Type u) [AddCommGroup N] [Module A N] :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ)) ≃+ (X →₀ N) where
  toFun := RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry (ModulePairing.finsuppScalarActionLinearMap A X N)
  invFun := Finsupp.liftAddHom (fun x => ModulePairing.Auxiliary.freeModuleIndexAddHom A X N x)
  left_inv := by
    have h : (Finsupp.liftAddHom (fun x => ModulePairing.Auxiliary.freeModuleIndexAddHom A X N x)).comp
        (RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry (ModulePairing.finsuppScalarActionLinearMap A X N)) = AddMonoidHom.id _ := by
      apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
      intro m n
      rw [AddMonoidHom.comp_apply, RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry_tmul, AddMonoidHom.id_apply]
      induction m using Finsupp.induction_linear with
      | zero => simp
      | add p q hp hq =>
        rw [show ModulePairing.finsuppScalarActionLinearMap A X N (p + q) n = ModulePairing.finsuppScalarActionLinearMap A X N p n + ModulePairing.finsuppScalarActionLinearMap A X N q n by rw [map_add]; rfl,
          map_add, hp, hq, add_tmul]
        exact (map_add (QuotientAddGroup.mk' _) _ _).symm
      | single x a =>
        rw [ModulePairing.finsuppScalarActionLinearMap_single_apply]
        change Finsupp.liftAddHom (fun x => ModulePairing.Auxiliary.freeModuleIndexAddHom A X N x) (Finsupp.single x (a.unop • n)) = _
        rw [Finsupp.liftAddHom_apply_single]
        change ((Finsupp.single x (1 : Aᵐᵒᵖ) ⊗ₜ[ℤ] (a.unop • n) :
            TensorProduct ℤ (X →₀ Aᵐᵒᵖ) N) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ))) = _
        rw [← RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.op_smul_tmul a (Finsupp.single x 1) n, Finsupp.smul_single, smul_eq_mul, mul_one]
    intro z
    rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]
  right_inv := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | single x n =>
      rw [Finsupp.liftAddHom_apply_single]
      change RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry (ModulePairing.finsuppScalarActionLinearMap A X N) ((Finsupp.single x (1 : Aᵐᵒᵖ) ⊗ₜ[ℤ] n :
          TensorProduct ℤ (X →₀ Aᵐᵒᵖ) N) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ))) = _
      rw [RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry_tmul, ModulePairing.finsuppScalarActionLinearMap_single_apply, MulOpposite.unop_one, one_smul]
  map_add' := map_add _

/-- The free-module additive equivalence sends a displayed pure tensor to the value of the associated finitely supported scalar-action map. -/
@[simp] lemma ModulePairing.freeModuleTensorAddEquiv_tmul (X N : Type u) [AddCommGroup N] [Module A N]
    (m : X →₀ Aᵐᵒᵖ) (n : N) :
    ModulePairing.freeModuleTensorAddEquiv A X N ((m ⊗ₜ[ℤ] n : TensorProduct ℤ (X →₀ Aᵐᵒᵖ) N) :
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ))) = ModulePairing.finsuppScalarActionLinearMap A X N m n :=
  rfl

/-- The finitely supported scalar-action construction commutes with applying a linear map to the coefficient module. -/
lemma ModulePairing.finsuppScalarActionLinearMap_natural (X : Type u) {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') (m : X →₀ Aᵐᵒᵖ) (n : N) :
    Finsupp.mapRange.addMonoidHom g.toAddMonoidHom (ModulePairing.finsuppScalarActionLinearMap A X N m n) = ModulePairing.finsuppScalarActionLinearMap A X N' m (g n) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [show ModulePairing.finsuppScalarActionLinearMap A X N (p + q) n = ModulePairing.finsuppScalarActionLinearMap A X N p n + ModulePairing.finsuppScalarActionLinearMap A X N q n by rw [map_add]; rfl,
      show ModulePairing.finsuppScalarActionLinearMap A X N' (p + q) (g n) = ModulePairing.finsuppScalarActionLinearMap A X N' p (g n) + ModulePairing.finsuppScalarActionLinearMap A X N' q (g n) by
        rw [map_add]; rfl,
      map_add, hp, hq]
  | single x a =>
    rw [ModulePairing.finsuppScalarActionLinearMap_single_apply, ModulePairing.finsuppScalarActionLinearMap_single_apply]
    change Finsupp.mapRange g.toAddMonoidHom (map_zero _) (Finsupp.single x (a.unop • n)) = _
    rw [Finsupp.mapRange_single]
    exact congrArg (Finsupp.single x) (g.map_smul a.unop n)

/-- The functor attached to a free opposite-ring module is naturally isomorphic to finitely supported functions after forgetting module structure. -/
noncomputable def ModulePairing.freeModuleFunctorIsoFinsupp (X : Type u) :
    RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ)) ≅
      forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ ModulePairing.finsuppFunctor X :=
  NatIso.ofComponents (fun N => AddEquiv.toAddCommGrpIso (ModulePairing.freeModuleTensorAddEquiv A X N))
    (by
      intro N N' g
      apply AddCommGrpCat.hom_ext
      apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
      intro m n
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
        RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor, AddCommGrpCat.hom_ofHom, AddEquiv.toAddCommGrpIso_hom,
        AddEquiv.coe_toAddMonoidHom, Functor.comp_map, ModuleCat.forget₂_map]
      exact (ModulePairing.finsuppScalarActionLinearMap_natural A X g.hom m n).symm)

/-- Applying the functor attached to a free opposite-ring module to a short exact complex preserves short exactness. -/
lemma ModulePairing.freeModuleFunctor_map_shortExact (X : Type u)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (S.map (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A ((ModuleCat.free Aᵐᵒᵖ).obj X))).ShortExact := by
  have hforget : (S.map (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).ShortExact :=
    hS.map_of_exact (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
  have hfs : (S.map (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ ModulePairing.finsuppFunctor X)).ShortExact :=
    ModulePairing.shortExact_map_finsuppFunctor X hforget
  exact ShortComplex.shortExact_of_iso (S.mapNatIso (ModulePairing.freeModuleFunctorIsoFinsupp A X)).symm hfs

/-- The functor associated with a projective opposite-ring module sends short exact complexes to short exact complexes. -/
theorem ModulePairing.projectiveModuleFunctor_map_shortExact (P : ModuleCat.{u} Aᵐᵒᵖ) [Projective P]
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (S.map (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A P)).ShortExact := by
  let ε : (ModuleCat.free Aᵐᵒᵖ).obj ((forget (ModuleCat.{u} Aᵐᵒᵖ)).obj P) ⟶ P :=
    (ModuleCat.adj Aᵐᵒᵖ).counit.app P
  have h : Retract P ((ModuleCat.free Aᵐᵒᵖ).obj ((forget (ModuleCat.{u} Aᵐᵒᵖ)).obj P)) :=
    { i := Projective.factorThru (𝟙 P) ε
      r := ε
      retract := Projective.factorThru_comp (𝟙 P) ε }
  exact CategoryTheory.ShortComplex.shortExact_of_retract (ModulePairing.shortComplexMap_retract A h) (ModulePairing.freeModuleFunctor_map_shortExact A _ hS)

/-- For a projective opposite-ring module, each positive-degree left-derived value of the associated functor is zero. -/
lemma ModulePairing.projectiveModuleFunctor_leftDerived_succ_isZero
    (P : ModuleCat.{u} Aᵐᵒᵖ) [Projective P]
    (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ) :
    IsZero ((Functor.leftDerived (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A P) (n + 1)).obj (ModuleCat.of A N)) := by
  -- `P ⊗_A -` is exact, hence preserves homology.
  haveI : (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A P).PreservesHomology :=
    ((Functor.exact_tfae (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A P)).out 0 2).mp
      (fun _ hS => ModulePairing.projectiveModuleFunctor_map_shortExact A P hS)
  -- Compute the derived functor from a projective resolution of `N`.
  let R : ProjectiveResolution (ModuleCat.of A N) := ProjectiveResolution.of _
  refine IsZero.of_iso ?_ (R.isoLeftDerivedObj (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A P) (n + 1))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff]
  -- The resolution is exact in positive degrees; an exact functor preserves that exactness.
  have hex : (R.complex.sc (n + 1)).Exact := by
    have := R.complex_exactAt_succ n
    rwa [HomologicalComplex.exactAt_iff] at this
  exact hex.map (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A P)

end RepresentationTheory.ModulePairing.Projective
