/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.ModulePairing.Projective

set_option backward.isDefEq.respectTransparency false

/-!
# Auxiliary tensor constructions with finitely supported modules
-/

open CategoryTheory Limits TensorProduct MulOpposite

namespace RepresentationTheory.ModuleCategoryTensorFinsupp

universe u

variable (A : Type u) [Ring A]

/-! ### The ring module -/

/-- The linear map sending a module element to its opposite-ring coefficient-action additive map. -/
noncomputable def auxiliaryCoefficientAction (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] :
    M →ₗ[Aᵐᵒᵖ] (A →+ M) where
  toFun m :=
    { toFun := fun a => MulOpposite.op a • m
      map_zero' := by rw [MulOpposite.op_zero, zero_smul]
      map_add' := fun a a' => by rw [MulOpposite.op_add, add_smul] }
  map_add' m m' := by ext a; simp [smul_add]
  map_smul' x m := by
    ext a
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, RingHom.id_apply,
      RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.op_smul_addMonoidHom_apply]
    rw [smul_smul, smul_eq_mul, MulOpposite.op_mul, MulOpposite.op_unop]

/-- Applying the coefficient-action map evaluates to the opposite-ring scalar action. -/
@[simp] lemma auxiliaryCoefficientAction_apply (M : Type u) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] (m : M) (a : A) :
    auxiliaryCoefficientAction A M m a = MulOpposite.op a • m := rfl

/-- The additive homomorphism from the auxiliary tensor-ring construction to the module. -/
noncomputable def auxiliaryTensorRingToModule (M : Type u) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A A M →+ M :=
  RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry
    (auxiliaryCoefficientAction A M)

/-- The auxiliary tensor-ring map sends a pure tensor to the corresponding scalar action. -/
@[simp] lemma auxiliaryTensorRingToModule_tmul (M : Type u) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] (m : M) (a : A) :
    auxiliaryTensorRingToModule A M
      ((m ⊗ₜ[ℤ] a : TensorProduct ℤ M A) :
        RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A A M) =
      MulOpposite.op a • m :=
  rfl

/-- The additive homomorphism from the module into the auxiliary tensor-ring construction. -/
noncomputable def auxiliaryModuleToTensorRing (M : Type u) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] :
    M →+ RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A A M where
  toFun m := ((m ⊗ₜ[ℤ] (1 : A) : TensorProduct ℤ M A) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A A M)
  map_zero' := by simp
  map_add' m m' := by
    rw [add_tmul]
    exact map_add (QuotientAddGroup.mk' _) _ _

/-- An additive equivalence from the displayed auxiliary tensor construction over the ring to the module. -/
noncomputable def auxiliaryTensorRingAddEquiv (M : Type u) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A A M ≃+ M where
  toFun := auxiliaryTensorRingToModule A M
  invFun := auxiliaryModuleToTensorRing A M
  left_inv := by
    have h : (auxiliaryModuleToTensorRing A M).comp (auxiliaryTensorRingToModule A M) =
        AddMonoidHom.id _ := by
      apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
      intro m a
      rw [AddMonoidHom.comp_apply, auxiliaryTensorRingToModule_tmul, AddMonoidHom.id_apply]
      change (((MulOpposite.op a • m) ⊗ₜ[ℤ] (1 : A) : TensorProduct ℤ M A) :
        RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A A M) = _
      rw [RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.op_smul_tmul
        (MulOpposite.op a) m 1, MulOpposite.unop_op, smul_eq_mul, mul_one]
    intro z
    rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]
  right_inv m := by
    change auxiliaryTensorRingToModule A M
      ((m ⊗ₜ[ℤ] (1 : A) : TensorProduct ℤ M A) :
        RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A A M) = m
    rw [auxiliaryTensorRingToModule_tmul, MulOpposite.op_one, one_smul]
  map_add' := map_add _

/-- The auxiliary tensor-ring additive equivalence evaluates a pure tensor by the opposite-ring action. -/
@[simp] lemma auxiliaryTensorRingAddEquiv_tmul (M : Type u) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] (m : M) (a : A) :
    auxiliaryTensorRingAddEquiv A M
      ((m ⊗ₜ[ℤ] a : TensorProduct ℤ M A) :
        RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A A M) =
      MulOpposite.op a • m := rfl

/-- An isomorphism from the auxiliary functor evaluated at the ring to the additive-group forgetful functor. -/
noncomputable def auxiliaryRingFunctorIso :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A A ≅
      forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun M => AddEquiv.toAddCommGrpIso (auxiliaryTensorRingAddEquiv A M))
    (by
      intro M M' f
      apply AddCommGrpCat.hom_ext
      apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
      intro m a
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
        AddCommGrpCat.hom_ofHom, AddEquiv.toAddCommGrpIso_hom, AddEquiv.coe_toAddMonoidHom,
        ModuleCat.forget₂_map]
      exact (map_smul f.hom (MulOpposite.op a) m).symm)

/-- Short exactness is preserved by the auxiliary functor evaluated at the ring module. -/
lemma auxiliaryShortExact_map_ring {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)}
    (hS : S.ShortExact) :
    (S.map
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
        A A)).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (auxiliaryRingFunctorIso A)).symm
    (hS.map_of_exact (forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u}))

/-! ### Functoriality in the left module -/

/-- The auxiliary assignment from modules to additive-group valued functors. -/
noncomputable def auxiliaryModuleToAddCommGrpFunctor :
    ModuleCat.{u} A ⥤ (ModuleCat.{u} Aᵐᵒᵖ ⥤ AddCommGrpCat.{u}) where
  obj Y :=
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A Y
  map {Y Y'} g :=
    RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom
      A g.hom
  map_id Y := by
    refine NatTrans.ext (funext fun M => ?_)
    apply AddCommGrpCat.hom_ext
    apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
    intro m y
    rfl
  map_comp {Y Y' Y''} g g' := by
    refine NatTrans.ext (funext fun M => ?_)
    apply AddCommGrpCat.hom_ext
    apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
    intro m y
    rfl

/-- A retract is transported between the images of a short complex under the auxiliary functor. -/
noncomputable def auxiliaryShortComplexMapRetract
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} {P F : ModuleCat.{u} A}
    (h : Retract P F) :
    Retract
      (S.map
        (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
          A P))
      (S.map
        (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
          A F)) :=
  let hF : Retract
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A P)
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A F) :=
    h.map (auxiliaryModuleToAddCommGrpFunctor A)
  { i := S.mapNatTrans hF.i
    r := S.mapNatTrans hF.r
    retract := ShortComplex.hom_ext _ _
      (NatTrans.congr_app hF.retract S.X₁)
      (NatTrans.congr_app hF.retract S.X₂)
      (NatTrans.congr_app hF.retract S.X₃) }

/-! ### Finitely supported free modules -/

/-- The linear coefficient-action map from a module into additive maps between finitely supported functions. -/
noncomputable def auxiliaryFinsuppCoefficientAction (X M : Type u) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] :
    M →ₗ[Aᵐᵒᵖ] ((X →₀ A) →+ (X →₀ M)) where
  toFun m := Finsupp.mapRange.addMonoidHom (auxiliaryCoefficientAction A M m)
  map_add' m m' := by
    apply Finsupp.addHom_ext
    intro x a
    simp [Finsupp.mapRange.addMonoidHom, Finsupp.mapRange_single]
  map_smul' x m := by
    apply Finsupp.addHom_ext
    intro y a
    simp only [Finsupp.mapRange.addMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Finsupp.mapRange_single, auxiliaryCoefficientAction_apply, RingHom.id_apply,
      RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.op_smul_addMonoidHom_apply,
      Finsupp.smul_single]
    rw [smul_smul, smul_eq_mul, MulOpposite.op_mul, MulOpposite.op_unop]

/-- The coefficient-action map sends a single-supported input to the corresponding single-supported output. -/
@[simp] lemma auxiliaryFinsuppCoefficientAction_single (X M : Type u) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] (m : M) (x : X) (a : A) :
    auxiliaryFinsuppCoefficientAction A X M m (Finsupp.single x a) =
      Finsupp.single x (MulOpposite.op a • m) := by
  simp [auxiliaryFinsuppCoefficientAction, Finsupp.mapRange.addMonoidHom,
    Finsupp.mapRange_single]

/-- The additive homomorphism associated with one index into the auxiliary finitely supported construction. -/
noncomputable def auxiliaryFinsuppGenerator (X M : Type u) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] (x : X) :
    M →+
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
        A (X →₀ A) M where
  toFun m := ((m ⊗ₜ[ℤ] Finsupp.single x (1 : A) :
    TensorProduct ℤ M (X →₀ A)) :
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
        A (X →₀ A) M)
  map_zero' := by simp
  map_add' m m' := by rw [add_tmul]; exact map_add (QuotientAddGroup.mk' _) _ _

/-- An additive equivalence from the displayed auxiliary construction to finitely supported functions. -/
noncomputable def auxiliaryFinsuppAddEquiv (X M : Type u) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
      A (X →₀ A) M ≃+ (X →₀ M) where
  toFun :=
    RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry
      (auxiliaryFinsuppCoefficientAction A X M)
  invFun := Finsupp.liftAddHom (fun x => auxiliaryFinsuppGenerator A X M x)
  left_inv := by
    have h : (Finsupp.liftAddHom (fun x => auxiliaryFinsuppGenerator A X M x)).comp
        (RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry
          (auxiliaryFinsuppCoefficientAction A X M)) = AddMonoidHom.id _ := by
      apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
      intro m p
      rw [AddMonoidHom.comp_apply,
        RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry_tmul,
        AddMonoidHom.id_apply]
      induction p using Finsupp.induction_linear with
      | zero => simp
      | add p q hp hq =>
        rw [show auxiliaryFinsuppCoefficientAction A X M m (p + q) =
            auxiliaryFinsuppCoefficientAction A X M m p +
              auxiliaryFinsuppCoefficientAction A X M m q from map_add _ p q,
          map_add, hp, hq, tmul_add]
        exact (map_add (QuotientAddGroup.mk' _) _ _).symm
      | single x a =>
        rw [auxiliaryFinsuppCoefficientAction_single]
        change Finsupp.liftAddHom (fun x => auxiliaryFinsuppGenerator A X M x)
          (Finsupp.single x _) = _
        rw [Finsupp.liftAddHom_apply_single]
        change (((MulOpposite.op a • m) ⊗ₜ[ℤ] Finsupp.single x (1 : A) :
            TensorProduct ℤ M (X →₀ A)) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
            A (X →₀ A) M) = _
        rw [RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.op_smul_tmul
          (MulOpposite.op a) m (Finsupp.single x 1), MulOpposite.unop_op,
          Finsupp.smul_single, smul_eq_mul, mul_one]
    intro z
    rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]
  right_inv := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | single x m =>
      rw [Finsupp.liftAddHom_apply_single]
      change RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry
        (auxiliaryFinsuppCoefficientAction A X M)
          ((m ⊗ₜ[ℤ] Finsupp.single x (1 : A) : TensorProduct ℤ M (X →₀ A)) :
            RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
              A (X →₀ A) M) = _
      rw [RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductCurry_tmul,
        auxiliaryFinsuppCoefficientAction_single, MulOpposite.op_one, one_smul]
  map_add' := map_add _

/-- Evaluating the auxiliary additive equivalence on a pure tensor agrees with the coefficient-action map. -/
@[simp] lemma auxiliaryFinsuppAddEquiv_tmul (X M : Type u) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] (m : M) (p : X →₀ A) :
    auxiliaryFinsuppAddEquiv A X M
      ((m ⊗ₜ[ℤ] p : TensorProduct ℤ M (X →₀ A)) :
        RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
          A (X →₀ A) M) = auxiliaryFinsuppCoefficientAction A X M m p :=
  rfl

/-- The coefficient-action map commutes with applying a linear map to its module argument. -/
lemma auxiliaryFinsuppCoefficientAction_map (X : Type u) {M M' : Type u}
    [AddCommGroup M] [Module Aᵐᵒᵖ M] [AddCommGroup M'] [Module Aᵐᵒᵖ M']
    (f : M →ₗ[Aᵐᵒᵖ] M') (m : M) (p : X →₀ A) :
    Finsupp.mapRange.addMonoidHom f.toAddMonoidHom
        (auxiliaryFinsuppCoefficientAction A X M m p) =
      auxiliaryFinsuppCoefficientAction A X M' (f m) p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [show auxiliaryFinsuppCoefficientAction A X M m (p + q) =
        auxiliaryFinsuppCoefficientAction A X M m p +
          auxiliaryFinsuppCoefficientAction A X M m q from map_add _ p q,
      show auxiliaryFinsuppCoefficientAction A X M' (f m) (p + q) =
        auxiliaryFinsuppCoefficientAction A X M' (f m) p +
          auxiliaryFinsuppCoefficientAction A X M' (f m) q from map_add _ p q,
      map_add, hp, hq]
  | single x a =>
    rw [auxiliaryFinsuppCoefficientAction_single, auxiliaryFinsuppCoefficientAction_single]
    change Finsupp.mapRange f.toAddMonoidHom (map_zero _) (Finsupp.single x _) = _
    rw [Finsupp.mapRange_single]
    exact congrArg (Finsupp.single x) (f.map_smul (MulOpposite.op a) m)

/-- An isomorphism identifying the auxiliary functor on a free module with a composite additive-group functor. -/
noncomputable def auxiliaryFreeModuleFunctorIso (X : Type u) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
        A ((ModuleCat.free A).obj X) ≅
      forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u} ⋙
        RepresentationTheory.ModulePairing.Projective.ModulePairing.finsuppFunctor X :=
  NatIso.ofComponents (fun M => AddEquiv.toAddCommGrpIso (auxiliaryFinsuppAddEquiv A X M))
    (by
      intro M M' f
      apply AddCommGrpCat.hom_ext
      apply RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction.balancedTensorProductHom_ext
      intro m p
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
        AddCommGrpCat.hom_ofHom, AddEquiv.toAddCommGrpIso_hom, AddEquiv.coe_toAddMonoidHom,
        Functor.comp_map, ModuleCat.forget₂_map]
      exact (auxiliaryFinsuppCoefficientAction_map A X f.hom m p).symm)

/-- Short exactness is retained after applying the auxiliary functor associated with a free module. -/
lemma auxiliaryFreeModule_shortExact (X : Type u)
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) :
    (S.map
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
        A ((ModuleCat.free A).obj X))).ShortExact := by
  have hforget : (S.map (forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u})).ShortExact :=
    hS.map_of_exact (forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u})
  have hfs : (S.map (forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u} ⋙
      RepresentationTheory.ModulePairing.Projective.ModulePairing.finsuppFunctor X)).ShortExact :=
    RepresentationTheory.ModulePairing.Projective.ModulePairing.shortExact_map_finsuppFunctor
      X hforget
  exact ShortComplex.shortExact_of_iso
    (S.mapNatIso (auxiliaryFreeModuleFunctorIso A X)).symm hfs

/-- A projective module preserves short exactness after the associated auxiliary functor is applied. -/
theorem auxiliaryShortExact_map_of_projective (Y : ModuleCat.{u} A) [Projective Y]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) :
    (S.map
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
        A Y)).ShortExact := by
  let ε : (ModuleCat.free A).obj ((forget (ModuleCat.{u} A)).obj Y) ⟶ Y :=
    (ModuleCat.adj A).counit.app Y
  have h : Retract Y ((ModuleCat.free A).obj ((forget (ModuleCat.{u} A)).obj Y)) :=
    { i := Projective.factorThru (𝟙 Y) ε
      r := ε
      retract := Projective.factorThru_comp (𝟙 Y) ε }
  exact RepresentationTheory.ModulePairing.Projective.CategoryTheory.ShortComplex.shortExact_of_retract
    (auxiliaryShortComplexMapRetract A h) (auxiliaryFreeModule_shortExact A _ hS)

end RepresentationTheory.ModuleCategoryTensorFinsupp
