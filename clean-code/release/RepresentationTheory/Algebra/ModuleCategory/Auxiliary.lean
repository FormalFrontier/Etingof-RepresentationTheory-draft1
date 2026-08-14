import RepresentationTheory.Algebra.Homology.TensorProductConstruction
import RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction

set_option backward.isDefEq.respectTransparency false

namespace RepresentationTheory.Algebra.ModuleCategory.Auxiliary

namespace ModuleCategoryAuxiliary

open CategoryTheory TensorProduct

universe u

/-- Builds an additive homomorphism between displayed auxiliary constructions from a linear map and a right module. -/
noncomputable def linearMapToAuxiliaryAddMonoidHom
    (A : Type u) [Ring A] {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') (M : ModuleCat.{u} Aᵐᵒᵖ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M →+ RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N' M :=
  QuotientAddGroup.map (RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A N M) (RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A N' M)
    (TensorProduct.map (LinearMap.id) g.toAddMonoidHom.toIntLinearMap).toAddMonoidHom
    (by

      refine AddSubgroup.closure_le _ |>.mpr ?_
      rintro x ⟨a, m, n, rfl⟩
      apply AddSubgroup.subset_closure
      refine ⟨a, m, g n, ?_⟩
      simp only [map_sub, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
        LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_toIntLinearMap, map_smul])

/-- The displayed homomorphism maps each pure tensor by applying the linear map to its second entry. -/
@[simp]
lemma linearMapToAuxiliaryAddMonoidHom_tmul
    (A : Type u) [Ring A] {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') (M : ModuleCat.{u} Aᵐᵒᵖ)
    (m : M) (n : N) :
    linearMapToAuxiliaryAddMonoidHom A g M (TensorProduct.tmul ℤ m n : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M)
      = (TensorProduct.tmul ℤ m (g n) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N' M) :=
  rfl

/-- Associates a morphism between the displayed auxiliary objects to a linear map. -/
noncomputable def linearMapToAuxiliaryHom
    (A : Type u) [Ring A] {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N ⟶ RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N' where
  app M := AddCommGrpCat.ofHom (linearMapToAuxiliaryAddMonoidHom A g M)
  naturality {M M'} f := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n => rfl
    | add a b ha hb =>
      rw [show ((a + b : TensorProduct ℤ M N) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M)
            = (a : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M) + b from
          map_add (QuotientAddGroup.mk' (RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A N M)) a b,
        map_add, map_add, ha, hb]

/-- Associates a morphism between auxiliary objects at a natural-number index to a linear map. -/
noncomputable def linearMapToAuxiliaryIndexedHom
    (A : Type u) [Ring A] {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') (n : ℕ) (M : ModuleCat.{u} Aᵐᵒᵖ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A N M n ⟶ RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A N' M n :=
  (NatTrans.leftDerived (linearMapToAuxiliaryHom A g) n).app M

/-- Associates to a right module a functor from left modules to additive commutative groups. -/
noncomputable def rightModuleToAddCommGrpFunctor (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ) :
    ModuleCat.{u} A ⥤ AddCommGrpCat.{u} where
  obj N := AddCommGrpCat.of (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M)
  map {N N'} g := AddCommGrpCat.ofHom (linearMapToAuxiliaryAddMonoidHom A g.hom M)
  map_id N := by
    ext x
    induction x with
    | zero => simp
    | tmul m n => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  map_comp {N N' N''} g g' := by
    ext x
    induction x with
    | zero => simp
    | tmul m n => rfl
    | add a b ha hb => simp only [map_add, ha, hb]

/-- The functor associated with a right module preserves addition of morphisms. -/
instance rightModuleToAddCommGrpFunctor_additive (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (rightModuleToAddCommGrpFunctor A M).Additive where
  map_add {N N' f g} := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n =>
      simp only [rightModuleToAddCommGrpFunctor, AddCommGrpCat.hom_ofHom, AddCommGrpCat.hom_add,
        AddMonoidHom.add_apply, linearMapToAuxiliaryAddMonoidHom_tmul, ModuleCat.hom_add, LinearMap.add_apply,
        tmul_add]
      exact map_add (QuotientAddGroup.mk' (RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A N' M)) _ _
    | add a b ha hb =>
      rw [show ((a + b : TensorProduct ℤ M N) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M)
            = (a : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M) + b from
          map_add (QuotientAddGroup.mk' (RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A N M)) a b,
        map_add, map_add, ha, hb]

end ModuleCategoryAuxiliary

end RepresentationTheory.Algebra.ModuleCategory.Auxiliary
