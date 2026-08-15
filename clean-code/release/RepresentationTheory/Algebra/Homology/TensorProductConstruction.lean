/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Alignment.Attribute
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Module.Opposite

/-!
# A tensor-product construction for module homology
-/

open CategoryTheory TensorProduct

namespace RepresentationTheory.Algebra.Homology.TensorProductConstruction

universe u

variable (A : Type u) [Ring A]
variable (N : Type u) [AddCommGroup N] [Module A N]

/-- An additive subgroup of the integer tensor product of a right module with a fixed left module. -/
def integerTensorSubgroup (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] :
    AddSubgroup (TensorProduct ℤ M N) :=
  AddSubgroup.closure
    {x | ∃ (a : A) (m : M) (n : N),
      x = (MulOpposite.op a • m) ⊗ₜ[ℤ] n - m ⊗ₜ[ℤ] (a • n)}

/-- A type associated with a right module and a fixed left module over a ring. -/
abbrev ModuleConstruction (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] : Type u :=
  TensorProduct ℤ M N ⧸ integerTensorSubgroup A N M

private lemma tensorOver_mk_add {M : Type u} [AddCommGroup M] [Module Aᵐᵒᵖ M]
    (p q : TensorProduct ℤ M N) :
    ((p + q : TensorProduct ℤ M N) : ModuleConstruction A N M)
      = (p : ModuleConstruction A N M) + (q : ModuleConstruction A N M) :=
  map_add (QuotientAddGroup.mk' _) p q

/-- The additive homomorphism between the associated types induced by a morphism of right modules. -/
noncomputable def moduleConstructionMap {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    ModuleConstruction A N M →+ ModuleConstruction A N M' :=
  QuotientAddGroup.map (integerTensorSubgroup A N M) (integerTensorSubgroup A N M')
    (TensorProduct.map f.hom.toAddMonoidHom.toIntLinearMap (LinearMap.id)).toAddMonoidHom
    (by
      refine AddSubgroup.closure_le _ |>.mpr ?_
      rintro x ⟨a, m, n, rfl⟩
      apply AddSubgroup.subset_closure
      refine ⟨a, f.hom m, n, ?_⟩
      simp only [map_sub, TensorProduct.map_tmul,
        LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_toIntLinearMap, LinearMap.id_coe, id_eq,
        map_smul])

@[simp]
private lemma tensorRightMap_mk {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M')
    (m : M) (n : N) :
    moduleConstructionMap A N f (TensorProduct.tmul ℤ m n : ModuleConstruction A N M)
      = (TensorProduct.tmul ℤ (f.hom m) n : ModuleConstruction A N M') :=
  rfl

/-- A functor from right modules to additive commutative groups for a fixed left module. -/
@[source_ref "Chapter8/Definition8.2.3" (role := supporting)]
noncomputable def moduleConstructionFunctor : ModuleCat.{u} Aᵐᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj M := AddCommGrpCat.of (ModuleConstruction A N M)
  map {M M'} f := AddCommGrpCat.ofHom (moduleConstructionMap A N f)
  map_id M := by
    ext x
    induction x with
    | zero => simp
    | tmul m n => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  map_comp {M M' M''} f g := by
    ext x
    induction x with
    | zero => simp
    | tmul m n => simp
    | add a b ha hb => simp only [map_add, ha, hb]

/-- The module construction functor is additive. -/
instance moduleConstructionFunctor_additive : (moduleConstructionFunctor A N).Additive where
  map_add {M M' f g} := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    change moduleConstructionMap A N (f + g) (y : ModuleConstruction A N M)
        = moduleConstructionMap A N f (y : ModuleConstruction A N M)
          + moduleConstructionMap A N g (y : ModuleConstruction A N M)
    induction y with
    | zero => simp
    | tmul m n =>
      rw [tensorRightMap_mk, tensorRightMap_mk, tensorRightMap_mk,
        ModuleCat.hom_add, LinearMap.add_apply, add_tmul]
      exact tensorOver_mk_add A N _ _
    | add p q hp hq =>
      rw [tensorOver_mk_add, map_add, map_add, map_add, hp, hq]
      abel

/-- For a fixed degree, a functor from right modules to additive commutative groups. -/
@[source_ref "Chapter8/Definition8.2.3" (role := supporting),
  source_ref "Chapter8/Introduction_8.2" (role := supporting)]
noncomputable def degreewiseModuleGroupFunctor (n : ℕ) :
    ModuleCat.{u} Aᵐᵒᵖ ⥤ AddCommGrpCat.{u} :=
  Functor.leftDerived (moduleConstructionFunctor A N) n

/-- A degree-indexed additive commutative group attached to a right module and a fixed left module. -/
@[source_ref "Chapter8/Definition8.2.3" (role := supporting)]
noncomputable def degreewiseModuleGroup (M : ModuleCat.{u} Aᵐᵒᵖ) (n : ℕ) : AddCommGrpCat.{u} :=
  (degreewiseModuleGroupFunctor A N n).obj M

/-- An isomorphism from the degree-indexed group to the homology of the fixed functor applied to a projective resolution. -/
@[source_ref "Chapter8/Definition8.2.3" (role := primary)]
noncomputable def degreewiseModuleGroupIsoResolutionHomology (M : ModuleCat.{u} Aᵐᵒᵖ)
    (P : ProjectiveResolution M) (n : ℕ) :
    degreewiseModuleGroup A N M n ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).obj
        (((moduleConstructionFunctor A N).mapHomologicalComplex _).obj P.complex) :=
  P.isoLeftDerivedObj (moduleConstructionFunctor A N) n

end RepresentationTheory.Algebra.Homology.TensorProductConstruction
