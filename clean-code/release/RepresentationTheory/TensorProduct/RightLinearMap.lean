/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.TensorProductPairingMaps

set_option backward.isDefEq.respectTransparency false

/-!
# Right-linear tensor-product maps

This module constructs base-field-linear maps induced by right-linear maps and proves their
compatibility with auxiliary tensor-product comparison maps.
-/

open TensorProduct

namespace RepresentationTheory.TensorProduct.RightLinearMap

universe u

section GenericMap

variable (k : Type u) [Field k]
variable (A : Type u) [Ring A]
variable (P : Type u) [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P]
variable (P' : Type u) [AddCommGroup P'] [Module k P'] [Module Aᵐᵒᵖ P'] [SMulCommClass k Aᵐᵒᵖ P']
variable (N : Type u) [AddCommGroup N] [Module A N]
variable (f : P →ₗ[k] P')

/-- Maps the first component of an integer tensor product into the displayed auxiliary target. -/
noncomputable def auxiliaryTensorProductMap :
    TensorProduct ℤ P N →ₗ[ℤ]
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N P' :=
  (QuotientAddGroup.mk'
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup
        A N P')).toIntLinearMap.comp
    (TensorProduct.map f.toAddMonoidHom.toIntLinearMap LinearMap.id)

omit [Module Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P'] in
/-- On a pure tensor, the auxiliary map applies its input map to the first component. -/
@[simp] theorem auxiliaryTensorProductMap_tmul (p : P) (n : N) :
    auxiliaryTensorProductMap k A P P' N f (p ⊗ₜ[ℤ] n)
      = (QuotientAddGroup.mk (f p ⊗ₜ[ℤ] n) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
            A N P') := by
  simp [auxiliaryTensorProductMap]

omit [Module Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P] in
/-- The auxiliary tensor-product map commutes with multiplication by base-field scalars. -/
theorem auxiliaryTensorProductMap_smul (c : k) (w : TensorProduct ℤ P N) :
    auxiliaryTensorProductMap k A P P' N f (c • w) =
      c • auxiliaryTensorProductMap k A P P' N f w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul p n =>
      rw [TensorProduct.smul_tmul', auxiliaryTensorProductMap_tmul,
        auxiliaryTensorProductMap_tmul, map_smul,
        RepresentationTheory.TensorProduct.AuxiliaryScalarAction.TensorProduct.Auxiliary.smul_mk,
        TensorProduct.smul_tmul']

variable (hf : ∀ (a : Aᵐᵒᵖ) (p : P), f (a • p) = a • f p)
include hf

omit [SMulCommClass k Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P'] in
/-- The auxiliary tensor-product map vanishes on members of the displayed relation. -/
theorem auxiliaryTensorProductMap_eq_zero_of_mem (w : TensorProduct ℤ P N)
    (hw : w ∈
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup
        A N P) :
    auxiliaryTensorProductMap k A P P' N f w = 0 := by
  have hle :
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup
          A N P ≤ (auxiliaryTensorProductMap k A P P' N f).toAddMonoidHom.ker := by
    rw [RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup,
      AddSubgroup.closure_le]
    rintro x ⟨a, p, n, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, map_sub,
      auxiliaryTensorProductMap_tmul, hf, sub_eq_zero]
    rw [QuotientAddGroup.eq_iff_sub_mem]
    exact AddSubgroup.subset_closure ⟨a, f p, n, rfl⟩
  exact hle hw

/-- Constructs the induced base-field-linear map between the displayed auxiliary targets. -/
noncomputable def auxiliaryTensorProductMapInduced :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N P →ₗ[k]
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N P' :=
  RepresentationTheory.Auxiliary.TensorProductPairingMaps.Auxiliary.liftComponentPairing
    k A N P
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N P')
    (auxiliaryTensorProductMap k A P P' N f)
    (auxiliaryTensorProductMap_smul k A P P' N f)
    (auxiliaryTensorProductMap_eq_zero_of_mem k A P P' N f hf)

/-- The induced map sends the class of a pure tensor to the class with its first component mapped. -/
@[simp] theorem auxiliaryTensorProductMapInduced_mk_tmul (p : P) (n : N) :
    auxiliaryTensorProductMapInduced k A P P' N f hf
        (QuotientAddGroup.mk (p ⊗ₜ[ℤ] n))
      = (QuotientAddGroup.mk (f p ⊗ₜ[ℤ] n) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction
            A N P') := by
  rw [auxiliaryTensorProductMapInduced,
    RepresentationTheory.Auxiliary.TensorProductPairingMaps.Auxiliary.liftComponentPairing_mk,
    auxiliaryTensorProductMap_tmul]

end GenericMap

section RestrictK

variable (k : Type u) [Field k]
variable (A : Type u) [Ring A] [Algebra k A]
variable (P P' : Type u)
  [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P] [IsScalarTower k Aᵐᵒᵖ P]
  [AddCommGroup P'] [Module k P'] [Module Aᵐᵒᵖ P'] [IsScalarTower k Aᵐᵒᵖ P']

/-- Views a map linear over an opposite algebra as a map linear over the base field. -/
noncomputable def rightLinearMapToLinearMap (f : P →ₗ[Aᵐᵒᵖ] P') : P →ₗ[k] P' where
  toFun := f
  map_add' := f.map_add
  map_smul' c p := by
    simp only [RingHom.id_apply]
    have h1 : (c • (1 : Aᵐᵒᵖ)) • p = c • p := by rw [smul_assoc, one_smul]
    have h2 : (c • (1 : Aᵐᵒᵖ)) • (f p) = c • f p := by rw [smul_assoc, one_smul]
    rw [← h1, map_smul, h2]

/-- The base-field-linear view has the same value as the original map. -/
@[simp] theorem rightLinearMapToLinearMap_apply (f : P →ₗ[Aᵐᵒᵖ] P') (p : P) :
    rightLinearMapToLinearMap k A P P' f p = f p := rfl

/-- The base-field-linear view still commutes with the displayed right scalar action. -/
theorem rightLinearMapToLinearMap_smul (f : P →ₗ[Aᵐᵒᵖ] P') (a : Aᵐᵒᵖ) (p : P) :
    rightLinearMapToLinearMap k A P P' f (a • p) =
      a • rightLinearMapToLinearMap k A P P' f p := f.map_smul a p

end RestrictK

section Naturality

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (P₁ P₂ P₁' P₂' : Type u)
  [AddCommGroup P₁] [Module k P₁] [Module A₁ᵐᵒᵖ P₁]
    [IsScalarTower k A₁ᵐᵒᵖ P₁] [SMulCommClass k A₁ᵐᵒᵖ P₁]
  [AddCommGroup P₂] [Module k P₂] [Module A₂ᵐᵒᵖ P₂]
    [IsScalarTower k A₂ᵐᵒᵖ P₂] [SMulCommClass k A₂ᵐᵒᵖ P₂]
  [AddCommGroup P₁'] [Module k P₁'] [Module A₁ᵐᵒᵖ P₁']
    [IsScalarTower k A₁ᵐᵒᵖ P₁'] [SMulCommClass k A₁ᵐᵒᵖ P₁']
  [AddCommGroup P₂'] [Module k P₂'] [Module A₂ᵐᵒᵖ P₂']
    [IsScalarTower k A₂ᵐᵒᵖ P₂'] [SMulCommClass k A₂ᵐᵒᵖ P₂']
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instM : Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)]
    [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)]
variable [instM' : Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁' ⊗[k] P₂')]
    [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁' ⊗[k] P₂')]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
variable
  (hM : ∀ (a₁ : A₁) (a₂ : A₂) (p₁ : P₁) (p₂ : P₂),
    (MulOpposite.op (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂)) • (p₁ ⊗ₜ[k] p₂ : P₁ ⊗[k] P₂)
      = (MulOpposite.op a₁ • p₁) ⊗ₜ[k] (MulOpposite.op a₂ • p₂))
  (hM' : ∀ (a₁ : A₁) (a₂ : A₂) (p₁ : P₁') (p₂ : P₂'),
    (MulOpposite.op (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂)) • (p₁ ⊗ₜ[k] p₂ : P₁' ⊗[k] P₂')
      = (MulOpposite.op a₁ • p₁) ⊗ₜ[k] (MulOpposite.op a₂ • p₂))
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))
variable (f₁ : P₁ →ₗ[A₁ᵐᵒᵖ] P₁') (f₂ : P₂ →ₗ[A₂ᵐᵒᵖ] P₂')

omit [SMulCommClass k A₁ᵐᵒᵖ P₁] [SMulCommClass k A₂ᵐᵒᵖ P₂] [SMulCommClass k A₁ᵐᵒᵖ P₁']
  [SMulCommClass k A₂ᵐᵒᵖ P₂'] [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)]
  [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁' ⊗[k] P₂')] in
include hM hM' in
/-- The tensor product of right-linear maps respects the right action induced by tensor-product scalars. -/
theorem tensorProductMap_smul (r : (A₁ ⊗[k] A₂)ᵐᵒᵖ) (x : P₁ ⊗[k] P₂) :
    TensorProduct.map (rightLinearMapToLinearMap k A₁ P₁ P₁' f₁)
        (rightLinearMapToLinearMap k A₂ P₂ P₂' f₂) (r • x)
      = r • TensorProduct.map (rightLinearMapToLinearMap k A₁ P₁ P₁' f₁)
          (rightLinearMapToLinearMap k A₂ P₂ P₂' f₂) x := by
  obtain ⟨g, rfl⟩ : ∃ g, MulOpposite.op g = r := ⟨r.unop, rfl⟩
  induction g using TensorProduct.induction_on generalizing x with
  | zero => simp
  | add g g' ih ih' =>
      rw [MulOpposite.op_add, add_smul, map_add, ih, ih', add_smul]
  | tmul a₁ a₂ =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
      | tmul p₁ p₂ =>
          rw [hM]
          simp only [TensorProduct.map_tmul, rightLinearMapToLinearMap_smul]
          rw [hM']

include hM hM' hN in
/-- The displayed maps and comparison equivalences commute with the tensor-product construction. -/
theorem auxiliaryTensorProductNaturality :
    (TensorProduct.map
          (auxiliaryTensorProductMapInduced k A₁ P₁ P₁' N₁
            (rightLinearMapToLinearMap k A₁ P₁ P₁' f₁)
            (rightLinearMapToLinearMap_smul k A₁ P₁ P₁' f₁))
          (auxiliaryTensorProductMapInduced k A₂ P₂ P₂' N₂
            (rightLinearMapToLinearMap k A₂ P₂ P₂' f₂)
            (rightLinearMapToLinearMap_smul k A₂ P₂ P₂' f₂))).comp
        (RepresentationTheory.Auxiliary.TensorProductPairingMaps.Auxiliary.combinedTensorComponentsEquiv
          k A₁ A₂ P₁ P₂ N₁ N₂ hM hN).toLinearMap
      = (RepresentationTheory.Auxiliary.TensorProductPairingMaps.Auxiliary.combinedTensorComponentsEquiv
            k A₁ A₂ P₁' P₂' N₁ N₂ hM' hN).toLinearMap.comp
          (auxiliaryTensorProductMapInduced k (A₁ ⊗[k] A₂) (P₁ ⊗[k] P₂)
            (P₁' ⊗[k] P₂') (N₁ ⊗[k] N₂)
            (TensorProduct.map (rightLinearMapToLinearMap k A₁ P₁ P₁' f₁)
              (rightLinearMapToLinearMap k A₂ P₂ P₂' f₂))
            (tensorProductMap_smul k A₁ A₂ P₁ P₂ P₁' P₂' hM hM' f₁ f₂)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp only [QuotientAddGroup.mk_add, map_add, hw, hw']
  | tmul x y =>
      induction x using TensorProduct.induction_on generalizing y with
      | zero => simp
      | add x x' hx hx' =>
          simp only [add_tmul, QuotientAddGroup.mk_add, map_add, hx, hx']
      | tmul p₁ p₂ =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add y y' hy hy' =>
              simp only [tmul_add, QuotientAddGroup.mk_add, map_add, hy, hy']
          | tmul n₁ n₂ =>
              simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
                RepresentationTheory.Auxiliary.TensorProductPairingMaps.Auxiliary.combinedTensorComponentsEquiv_mk_tmul_tmul,
                TensorProduct.map_tmul, auxiliaryTensorProductMapInduced_mk_tmul,
                rightLinearMapToLinearMap_apply]

end Naturality

end RepresentationTheory.TensorProduct.RightLinearMap
