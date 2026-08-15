/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.TensorProduct.AuxiliaryScalarAction
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.TensorProduct.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Auxiliary tensor-product pairing maps

This module constructs component pairings and a linear equivalence between a combined auxiliary
tensor-product construction and the tensor product of its two component constructions.
-/

open TensorProduct

namespace RepresentationTheory.Auxiliary.TensorProductPairingMaps.Auxiliary

universe u

section Factor

variable (k : Type u) [Field k]
variable (A : Type u) [Ring A] [Algebra k A]
variable (P : Type u) [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P]
    [IsScalarTower k Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- In the auxiliary target, acting on the right-module factor by an opposite-ring element equals acting on the left-module factor. -/
theorem componentPairing_op_smul_eq_smul (a : A) (p : P) (n : N) :
    (QuotientAddGroup.mk ((MulOpposite.op a • p) ⊗ₜ[ℤ] n) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N P)
      = QuotientAddGroup.mk (p ⊗ₜ[ℤ] (a • n)) := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure ⟨a, p, n, rfl⟩

/-- A base-field scalar acting on the left-module factor can be moved outside its additive quotient representative. -/
theorem componentPairing_smul_right (c : k) (p : P) (n : N) :
    (QuotientAddGroup.mk (p ⊗ₜ[ℤ] (c • n)) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N P)
      = c • (QuotientAddGroup.mk (p ⊗ₜ[ℤ] n)) := by
  rw [RepresentationTheory.TensorProduct.AuxiliaryScalarAction.TensorProduct.Auxiliary.smul_mk, TensorProduct.smul_tmul', QuotientAddGroup.eq]
  have hn : (c • n) = (algebraMap k A c) • n := by
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
  have hp : (c • p) = (MulOpposite.op (algebraMap k A c)) • p := by
    have : (MulOpposite.op (algebraMap k A c)) = c • (1 : Aᵐᵒᵖ) := by
      rw [Algebra.algebraMap_eq_smul_one]; rfl
    rw [this, smul_assoc, one_smul]
  rw [hn, hp]
  exact AddSubgroup.subset_closure ⟨algebraMap k A c, p, n, by abel⟩

/-- Packages the pairing of a right module element and a left module element as successive base-field linear maps. -/
noncomputable def componentPairingBilinear : P →ₗ[k] N →ₗ[k] RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N P :=
  LinearMap.mk₂ k (fun p n => (QuotientAddGroup.mk (p ⊗ₜ[ℤ] n) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N P))
    (fun p₁ p₂ n => by rw [add_tmul]; exact map_add (QuotientAddGroup.mk' _) _ _)
    (fun c p n => by rw [← TensorProduct.smul_tmul', RepresentationTheory.TensorProduct.AuxiliaryScalarAction.TensorProduct.Auxiliary.smul_mk])
    (fun p n₁ n₂ => by rw [tmul_add]; exact map_add (QuotientAddGroup.mk' _) _ _)
    (fun c p n => componentPairing_smul_right k A P N c p n)

/-- Defines the base-field linear map from the tensor product of a right module and a left module to the auxiliary target. -/
noncomputable def componentPairing : (P ⊗[k] N) →ₗ[k] RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N P :=
  TensorProduct.lift (componentPairingBilinear k A P N)

/-- The component pairing sends a pure tensor to its additive quotient representative. -/
@[simp] theorem componentPairing_tmul (p : P) (n : N) :
    componentPairing k A P N (p ⊗ₜ[k] n) = (QuotientAddGroup.mk (p ⊗ₜ[ℤ] n) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N P) :=
  TensorProduct.lift.tmul _ _

end Factor

section Lift

variable (k : Type u) [Field k]
variable (A : Type u) [Ring A]
variable (N : Type u) [AddCommGroup N] [Module A N]
variable (P : Type u) [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P]
variable (M : Type u) [AddCommGroup M] [Module k M]

/-- Lifts an additive map through the component auxiliary type when it respects base-field scalars and vanishes on the displayed relation subset. -/
noncomputable def liftComponentPairing (φ : TensorProduct ℤ P N →ₗ[ℤ] M)
    (hsmul : ∀ (c : k) (w : TensorProduct ℤ P N), φ (c • w) = c • φ w)
    (hker : ∀ w ∈ RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A N P, φ w = 0) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N P →ₗ[k] M where
  toFun := QuotientAddGroup.lift _ φ.toAddMonoidHom hker
  map_add' x y := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [← QuotientAddGroup.mk_add]
    simp only [QuotientAddGroup.lift_mk, map_add]
  map_smul' c z := by
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [RepresentationTheory.TensorProduct.AuxiliaryScalarAction.TensorProduct.Auxiliary.smul_mk]
    simp only [QuotientAddGroup.lift_mk, LinearMap.toAddMonoidHom_coe, RingHom.id_apply]
    exact hsmul c w

/-- The lifted component map evaluates on an additive quotient representative as the original additive map. -/
@[simp] theorem liftComponentPairing_mk (φ : TensorProduct ℤ P N →ₗ[ℤ] M)
    (hsmul : ∀ (c : k) (w : TensorProduct ℤ P N), φ (c • w) = c • φ w)
    (hker : ∀ w ∈ RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A N P, φ w = 0) (w : TensorProduct ℤ P N) :
    liftComponentPairing k A N P M φ hsmul hker (QuotientAddGroup.mk w) = φ w :=
  rfl

end Lift

section Main

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (P₁ P₂ : Type u)
  [AddCommGroup P₁] [Module k P₁] [Module A₁ᵐᵒᵖ P₁]
    [IsScalarTower k A₁ᵐᵒᵖ P₁] [SMulCommClass k A₁ᵐᵒᵖ P₁]
  [AddCommGroup P₂] [Module k P₂] [Module A₂ᵐᵒᵖ P₂]
    [IsScalarTower k A₂ᵐᵒᵖ P₂] [SMulCommClass k A₂ᵐᵒᵖ P₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]

/-- Constructs the linear map that pairs the first module factor with the first target factor and likewise for the second factors. -/
noncomputable def pairTensorFactors :
    (P₁ ⊗[k] P₂) ⊗[k] (N₁ ⊗[k] N₂) →ₗ[k]
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁) ⊗[k] (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂) :=
  (TensorProduct.map (componentPairing k A₁ P₁ N₁) (componentPairing k A₂ P₂ N₂)).comp
    (TensorProduct.tensorTensorTensorComm k P₁ P₂ N₁ N₂).toLinearMap

/-- Pairing four pure factors produces the tensor of the two corresponding additive quotient representatives. -/
@[simp] theorem pairTensorFactors_tmul_tmul (p₁ : P₁) (p₂ : P₂) (n₁ : N₁) (n₂ : N₂) :
    pairTensorFactors k A₁ A₂ P₁ P₂ N₁ N₂ ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[k] (n₁ ⊗ₜ[k] n₂))
      = (QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁)
          ⊗ₜ[k] (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂) := by
  simp [pairTensorFactors]

variable [instM : Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)]
    [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]

variable
  (hM : ∀ (a₁ : A₁) (a₂ : A₂) (p₁ : P₁) (p₂ : P₂),
    (MulOpposite.op (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂)) • (p₁ ⊗ₜ[k] p₂ : P₁ ⊗[k] P₂)
      = (MulOpposite.op a₁ • p₁) ⊗ₜ[k] (MulOpposite.op a₂ • p₂))
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))

omit [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)] in
include hM hN in

/-- Under the stated action rules, pairing tensor factors gives the same result whether the combined scalar acts on the module side or the target side. -/
theorem pairTensorFactors_smul_op_tmul_eq_tmul_smul (g : A₁ ⊗[k] A₂) (m : P₁ ⊗[k] P₂) (n : N₁ ⊗[k] N₂) :
    pairTensorFactors k A₁ A₂ P₁ P₂ N₁ N₂ ((MulOpposite.op g • m) ⊗ₜ[k] n)
      = pairTensorFactors k A₁ A₂ P₁ P₂ N₁ N₂ (m ⊗ₜ[k] (g • n)) := by
  induction g using TensorProduct.induction_on generalizing m n with
  | zero => simp
  | add g₁ g₂ ih₁ ih₂ =>
      simp only [MulOpposite.op_add, add_smul, add_tmul, map_add, ih₁, ih₂, tmul_add]
  | tmul a₁ a₂ =>
      induction m using TensorProduct.induction_on generalizing n with
      | zero => simp
      | add m₁ m₂ ihm₁ ihm₂ =>
          simp only [smul_add, add_tmul, map_add, ihm₁, ihm₂]
      | tmul p₁ p₂ =>
          induction n using TensorProduct.induction_on with
          | zero => simp
          | add n₁ n₂ ihn₁ ihn₂ =>
              simp only [tmul_add, smul_add, map_add, ihn₁, ihn₂]
          | tmul n₁ n₂ =>
              rw [hM, hN, pairTensorFactors_tmul_tmul, pairTensorFactors_tmul_tmul,
                componentPairing_op_smul_eq_smul, componentPairing_op_smul_eq_smul]

/-- Defines an additive lift from tensors of the combined module data to the tensor product of the component auxiliary types. -/
noncomputable def combinedTensorLiftAux :
    TensorProduct ℤ (P₁ ⊗[k] P₂) (N₁ ⊗[k] N₂) →ₗ[ℤ]
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁) ⊗[k] (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂) :=
  TensorProduct.lift <| LinearMap.mk₂ ℤ
    (fun x y => pairTensorFactors k A₁ A₂ P₁ P₂ N₁ N₂ (x ⊗ₜ[k] y))
    (fun x₁ x₂ y => by rw [add_tmul, map_add])
    (fun c x y => by rw [← TensorProduct.smul_tmul', map_zsmul])
    (fun x y₁ y₂ => by rw [tmul_add, map_add])
    (fun c x y => by rw [TensorProduct.tmul_smul, map_zsmul])

omit instM [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)] instN in
/-- On a pure tensor, the additive combined-tensor lift agrees with the displayed factor-pairing map. -/
@[simp] theorem combinedTensorLiftAux_tmul (x : P₁ ⊗[k] P₂) (y : N₁ ⊗[k] N₂) :
    combinedTensorLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ (x ⊗ₜ[ℤ] y)
      = pairTensorFactors k A₁ A₂ P₁ P₂ N₁ N₂ (x ⊗ₜ[k] y) :=
  TensorProduct.lift.tmul _ _

omit instM [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)] instN in
/-- The additive combined-tensor lift commutes with scalar multiplication by the base field. -/
theorem combinedTensorLiftAux_smul (c : k) (w : TensorProduct ℤ (P₁ ⊗[k] P₂) (N₁ ⊗[k] N₂)) :
    combinedTensorLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ (c • w) = c • combinedTensorLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul x y =>
      rw [TensorProduct.smul_tmul', combinedTensorLiftAux_tmul, combinedTensorLiftAux_tmul, ← TensorProduct.smul_tmul', map_smul]

omit [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)] in
include hM hN in

/-- The additive combined-tensor lift vanishes on elements of the displayed relation subset. -/
theorem combinedTensorLiftAux_eq_zero_of_mem (w : TensorProduct ℤ (P₁ ⊗[k] P₂) (N₁ ⊗[k] N₂))
    (hw : w ∈ RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :
    combinedTensorLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ w = 0 := by
  have hle : RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)
      ≤ (combinedTensorLiftAux k A₁ A₂ P₁ P₂ N₁ N₂).toAddMonoidHom.ker := by
    rw [RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup, AddSubgroup.closure_le]
    rintro x ⟨g, m, n, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, map_sub,
      combinedTensorLiftAux_tmul, sub_eq_zero]
    exact pairTensorFactors_smul_op_tmul_eq_tmul_smul k A₁ A₂ P₁ P₂ N₁ N₂ hM hN g m n
  exact hle hw

include hM hN in

/-- Builds a linear map from the auxiliary type for the combined tensor data to the tensor product of the two component auxiliary types. -/
noncomputable def combinedToTensorComponents :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) →ₗ[k]
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁) ⊗[k] (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂) where
  toFun := QuotientAddGroup.lift _ (combinedTensorLiftAux k A₁ A₂ P₁ P₂ N₁ N₂).toAddMonoidHom
    (combinedTensorLiftAux_eq_zero_of_mem k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)
  map_add' x y := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [← QuotientAddGroup.mk_add]
    simp only [QuotientAddGroup.lift_mk, map_add]
  map_smul' c z := by
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [RepresentationTheory.TensorProduct.AuxiliaryScalarAction.TensorProduct.Auxiliary.smul_mk]
    simp only [QuotientAddGroup.lift_mk, LinearMap.toAddMonoidHom_coe, RingHom.id_apply]
    exact combinedTensorLiftAux_smul k A₁ A₂ P₁ P₂ N₁ N₂ c w

/-- The forward map sends a representative built from four pure factors to the tensor of the two component representatives. -/
@[simp] theorem combinedToTensorComponents_mk_tmul (p₁ : P₁) (p₂ : P₂) (n₁ : N₁) (n₂ : N₂) :
    combinedToTensorComponents k A₁ A₂ P₁ P₂ N₁ N₂ hM hN
        (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)))
      = (QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁)
          ⊗ₜ[k] (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂) := by
  simp only [combinedToTensorComponents, LinearMap.coe_mk, AddHom.coe_mk, QuotientAddGroup.lift_mk,
    LinearMap.toAddMonoidHom_coe, combinedTensorLiftAux_tmul, pairTensorFactors_tmul_tmul]

/-- For fixed first-component elements, defines an additive map from raw second-component tensors to the combined auxiliary type. -/
noncomputable def tensorComponentsToCombinedSecondLiftAux (p₁ : P₁) (n₁ : N₁) :
    TensorProduct ℤ P₂ N₂ →ₗ[ℤ] RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) :=
  TensorProduct.lift <| LinearMap.mk₂ ℤ
    (fun p₂ n₂ => (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
        RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)))
    (fun p₂ p₂' n₂ => by rw [tmul_add, add_tmul]; exact map_add (QuotientAddGroup.mk' _) _ _)
    (fun c p₂ n₂ => by
      rw [tmul_smul, ← TensorProduct.smul_tmul']
      exact map_zsmul (QuotientAddGroup.mk' _) _ _)
    (fun p₂ n₂ n₂' => by rw [tmul_add, tmul_add]; exact map_add (QuotientAddGroup.mk' _) _ _)
    (fun c p₂ n₂ => by
      rw [tmul_smul, TensorProduct.tmul_smul]
      exact map_zsmul (QuotientAddGroup.mk' _) _ _)

set_option linter.unusedSectionVars false in
/-- The second additive lift sends a pure tensor to the representative formed from the paired component tensors. -/
@[simp] theorem tensorComponentsToCombinedSecondLiftAux_tmul (p₁ : P₁) (n₁ : N₁) (p₂ : P₂) (n₂ : N₂) :
    tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ (p₂ ⊗ₜ[ℤ] n₂)
      = (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :=
  TensorProduct.lift.tmul _ _

/-- The second additive lift commutes with scalar multiplication on its raw tensor input. -/
theorem tensorComponentsToCombinedSecondLiftAux_smul (p₁ : P₁) (n₁ : N₁) (c : k)
    (w : TensorProduct ℤ P₂ N₂) :
    tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ (c • w)
      = c • tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul p₂ n₂ =>
      rw [TensorProduct.smul_tmul', tensorComponentsToCombinedSecondLiftAux_tmul, tensorComponentsToCombinedSecondLiftAux_tmul, TensorProduct.tmul_smul,
        ← TensorProduct.smul_tmul', ← RepresentationTheory.TensorProduct.AuxiliaryScalarAction.TensorProduct.Auxiliary.smul_mk]

/-- The second additive lift is additive in its fixed first module argument. -/
theorem tensorComponentsToCombinedSecondLiftAux_add_left (p₁ p₁' : P₁) (n₁ : N₁) :
    tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ (p₁ + p₁') n₁
      = tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ + tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁' n₁ := by
  refine TensorProduct.ext' fun p₂ n₂ => ?_
  simp only [tensorComponentsToCombinedSecondLiftAux_tmul, LinearMap.add_apply]
  rw [add_tmul, add_tmul]
  exact map_add (QuotientAddGroup.mk' _) _ _

/-- Integer scaling in the first module argument passes through the second additive lift. -/
theorem tensorComponentsToCombinedSecondLiftAux_zsmul_left (c : ℤ) (p₁ : P₁) (n₁ : N₁) :
    tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ (c • p₁) n₁ = c • tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ := by
  refine TensorProduct.ext' fun p₂ n₂ => ?_
  simp only [tensorComponentsToCombinedSecondLiftAux_tmul, LinearMap.smul_apply]
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul']
  exact map_zsmul (QuotientAddGroup.mk' _) _ _

/-- The second additive lift is additive in its fixed first target argument. -/
theorem tensorComponentsToCombinedSecondLiftAux_add_right (p₁ : P₁) (n₁ n₁' : N₁) :
    tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ (n₁ + n₁')
      = tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ + tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁' := by
  refine TensorProduct.ext' fun p₂ n₂ => ?_
  simp only [tensorComponentsToCombinedSecondLiftAux_tmul, LinearMap.add_apply]
  rw [add_tmul, tmul_add]
  exact map_add (QuotientAddGroup.mk' _) _ _

/-- Integer scaling in the first target argument passes through the second additive lift. -/
theorem tensorComponentsToCombinedSecondLiftAux_zsmul_right (c : ℤ) (p₁ : P₁) (n₁ : N₁) :
    tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ (c • n₁) = c • tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ := by
  refine TensorProduct.ext' fun p₂ n₂ => ?_
  simp only [tensorComponentsToCombinedSecondLiftAux_tmul, LinearMap.smul_apply]
  rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  exact map_zsmul (QuotientAddGroup.mk' _) _ _

/-- Scaling the first module argument scales the resulting second additive lift. -/
theorem tensorComponentsToCombinedSecondLiftAux_smul_left (c : k) (p₁ : P₁) (n₁ : N₁) :
    tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ (c • p₁) n₁ = c • tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ := by
  refine TensorProduct.ext' fun p₂ n₂ => ?_
  simp only [tensorComponentsToCombinedSecondLiftAux_tmul, LinearMap.smul_apply]
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', ← RepresentationTheory.TensorProduct.AuxiliaryScalarAction.TensorProduct.Auxiliary.smul_mk]

include hM hN in

/-- Under the stated tensor-action rules, the second additive lift vanishes on the second displayed relation subset. -/
theorem tensorComponentsToCombinedSecondLiftAux_eq_zero_of_mem (p₁ : P₁) (n₁ : N₁) (w : TensorProduct ℤ P₂ N₂)
    (hw : w ∈ RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A₂ N₂ P₂) :
    tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ w = 0 := by
  have hle : RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A₂ N₂ P₂
      ≤ (tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁).toAddMonoidHom.ker := by
    rw [RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup, AddSubgroup.closure_le]
    rintro x ⟨a₂, p₂, n₂, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, map_sub,
      tensorComponentsToCombinedSecondLiftAux_tmul, sub_eq_zero, QuotientAddGroup.eq_iff_sub_mem]
    apply AddSubgroup.subset_closure
    refine ⟨(1 : A₁) ⊗ₜ[k] a₂, p₁ ⊗ₜ[k] p₂, n₁ ⊗ₜ[k] n₂, ?_⟩
    rw [hM, hN]
    simp [MulOpposite.op_one]
  exact hle hw

include hM hN in

/-- For first-component elements, constructs a base-field linear map from the second component auxiliary type to the combined type. -/
noncomputable def tensorComponentsToCombinedFirstLinear (p₁ : P₁) (n₁ : N₁) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂ →ₗ[k] RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) :=
  liftComponentPairing k A₂ N₂ P₂ _ (tensorComponentsToCombinedSecondLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁)
    (tensorComponentsToCombinedSecondLiftAux_smul k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁)
    (tensorComponentsToCombinedSecondLiftAux_eq_zero_of_mem k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁)

include hM hN in
/-- The first-component linear map sends a pure second-component representative to the paired combined representative. -/
@[simp] theorem tensorComponentsToCombinedFirstLinear_mk_tmul (p₁ : P₁) (n₁ : N₁) (p₂ : P₂) (n₂ : N₂) :
    tensorComponentsToCombinedFirstLinear k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁
        (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂))
      = (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) := by
  rw [tensorComponentsToCombinedFirstLinear, liftComponentPairing_mk, tensorComponentsToCombinedSecondLiftAux_tmul]

include hM hN in

/-- Scaling the first module argument scales the associated map from the second component auxiliary type. -/
theorem tensorComponentsToCombinedFirstLinear_smul_left (c : k) (p₁ : P₁) (n₁ : N₁) :
    tensorComponentsToCombinedFirstLinear k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (c • p₁) n₁
      = c • tensorComponentsToCombinedFirstLinear k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁ := by
  ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
  simp only [tensorComponentsToCombinedFirstLinear, liftComponentPairing_mk, LinearMap.smul_apply]
  exact LinearMap.congr_fun (tensorComponentsToCombinedSecondLiftAux_smul_left k A₁ A₂ P₁ P₂ N₁ N₂ c p₁ n₁) w

include hM hN in

/-- Packages the first pair of component arguments into successive integer-linear maps valued in maps from the second auxiliary type. -/
noncomputable def tensorComponentsToCombinedFirstBilinear :
    P₁ →ₗ[ℤ] N₁ →ₗ[ℤ]
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂ →ₗ[k] RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :=
  LinearMap.mk₂ ℤ (fun p₁ n₁ => tensorComponentsToCombinedFirstLinear k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁)
    (fun p₁ p₁' n₁ => by
      ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
      simp only [tensorComponentsToCombinedFirstLinear, liftComponentPairing_mk, LinearMap.add_apply,
        LinearMap.congr_fun (tensorComponentsToCombinedSecondLiftAux_add_left k A₁ A₂ P₁ P₂ N₁ N₂ p₁ p₁' n₁) w])
    (fun c p₁ n₁ => by
      ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
      simp only [tensorComponentsToCombinedFirstLinear, liftComponentPairing_mk, LinearMap.smul_apply,
        LinearMap.congr_fun (tensorComponentsToCombinedSecondLiftAux_zsmul_left k A₁ A₂ P₁ P₂ N₁ N₂ c p₁ n₁) w])
    (fun p₁ n₁ n₁' => by
      ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
      simp only [tensorComponentsToCombinedFirstLinear, liftComponentPairing_mk, LinearMap.add_apply,
        LinearMap.congr_fun (tensorComponentsToCombinedSecondLiftAux_add_right k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ n₁') w])
    (fun c p₁ n₁ => by
      ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
      simp only [tensorComponentsToCombinedFirstLinear, liftComponentPairing_mk, LinearMap.smul_apply,
        LinearMap.congr_fun (tensorComponentsToCombinedSecondLiftAux_zsmul_right k A₁ A₂ P₁ P₂ N₁ N₂ c p₁ n₁) w])

include hM hN in

/-- Defines the first additive lift, taking a raw first-component tensor to a linear map out of the second component auxiliary type. -/
noncomputable def tensorComponentsToCombinedFirstLiftAux :
    TensorProduct ℤ P₁ N₁ →ₗ[ℤ]
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂ →ₗ[k] RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :=
  TensorProduct.lift (tensorComponentsToCombinedFirstBilinear k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)

include hM hN in
/-- The first additive lift on a pure tensor is the corresponding first-component linear map. -/
@[simp] theorem tensorComponentsToCombinedFirstLiftAux_tmul (p₁ : P₁) (n₁ : N₁) :
    tensorComponentsToCombinedFirstLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (p₁ ⊗ₜ[ℤ] n₁)
      = tensorComponentsToCombinedFirstLinear k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁ :=
  TensorProduct.lift.tmul _ _

include hM hN in

/-- The first additive lift commutes with multiplication by a base-field scalar. -/
theorem tensorComponentsToCombinedFirstLiftAux_smul (c : k) (w : TensorProduct ℤ P₁ N₁) :
    tensorComponentsToCombinedFirstLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (c • w)
      = c • tensorComponentsToCombinedFirstLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ hM hN w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul p₁ n₁ =>
      rw [TensorProduct.smul_tmul', tensorComponentsToCombinedFirstLiftAux_tmul, tensorComponentsToCombinedFirstLiftAux_tmul,
        tensorComponentsToCombinedFirstLinear_smul_left k A₁ A₂ P₁ P₂ N₁ N₂ hM hN c p₁ n₁]

include hM hN in

/-- The first additive lift vanishes on members of the first displayed relation subset. -/
theorem tensorComponentsToCombinedFirstLiftAux_eq_zero_of_mem (w : TensorProduct ℤ P₁ N₁) (hw : w ∈ RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A₁ N₁ P₁) :
    tensorComponentsToCombinedFirstLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ hM hN w = 0 := by
  have hle : RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A₁ N₁ P₁
      ≤ (tensorComponentsToCombinedFirstLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ hM hN).toAddMonoidHom.ker := by
    rw [RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup, AddSubgroup.closure_le]
    rintro x ⟨a₁, p₁, n₁, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, map_sub,
      tensorComponentsToCombinedFirstLiftAux_tmul, sub_eq_zero]
    ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [QuotientAddGroup.mk_add, map_add, ha, hb]
    | tmul p₂ n₂ =>
        simp only [tensorComponentsToCombinedFirstLinear_mk_tmul, QuotientAddGroup.eq_iff_sub_mem]
        apply AddSubgroup.subset_closure
        refine ⟨a₁ ⊗ₜ[k] (1 : A₂), p₁ ⊗ₜ[k] p₂, n₁ ⊗ₜ[k] n₂, ?_⟩
        rw [hM, hN]
        simp [MulOpposite.op_one]
  exact hle hw

include hM hN in

/-- Expresses the component-to-combined construction as a curried pair of linear maps. -/
noncomputable def tensorComponentsToCombinedBilinear :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁ →ₗ[k] RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂ →ₗ[k]
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) :=
  liftComponentPairing k A₁ N₁ P₁ _ (tensorComponentsToCombinedFirstLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)
    (tensorComponentsToCombinedFirstLiftAux_smul k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)
    (tensorComponentsToCombinedFirstLiftAux_eq_zero_of_mem k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)

include hM hN in
/-- The curried component construction on two pure representatives is the representative formed from the paired tensor factors. -/
@[simp] theorem tensorComponentsToCombinedBilinear_mk_tmul_mk_tmul (p₁ : P₁) (n₁ : N₁) (p₂ : P₂) (n₂ : N₂) :
    tensorComponentsToCombinedBilinear k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁))
        (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂))
      = (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) := by
  rw [tensorComponentsToCombinedBilinear, liftComponentPairing_mk, tensorComponentsToCombinedFirstLiftAux_tmul, tensorComponentsToCombinedFirstLinear_mk_tmul]

include hM hN in

/-- Builds a linear map from the tensor product of the component auxiliary types to the combined auxiliary type. -/
noncomputable def tensorComponentsToCombined :
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁) ⊗[k] (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂) →ₗ[k]
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) :=
  TensorProduct.lift (tensorComponentsToCombinedBilinear k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)

include hM hN in
/-- The reverse map sends a tensor of two pure component representatives to their paired combined representative. -/
@[simp] theorem tensorComponentsToCombined_tmul_mk_tmul (p₁ : P₁) (n₁ : N₁) (p₂ : P₂) (n₂ : N₂) :
    tensorComponentsToCombined k A₁ A₂ P₁ P₂ N₁ N₂ hM hN
        ((QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁)
          ⊗ₜ[k] (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂))
      = (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) := by
  rw [tensorComponentsToCombined, TensorProduct.lift.tmul, tensorComponentsToCombinedBilinear_mk_tmul_mk_tmul]

include hM hN in
/-- The forward map on an additive quotient representative is computed by the auxiliary combined-tensor lift. -/
theorem combinedToTensorComponents_mk (w : TensorProduct ℤ (P₁ ⊗[k] P₂) (N₁ ⊗[k] N₂)) :
    combinedToTensorComponents k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (QuotientAddGroup.mk w)
      = combinedTensorLiftAux k A₁ A₂ P₁ P₂ N₁ N₂ w := rfl

include hM hN in

/-- Applying the reverse map after pairing the factors of a pure tensor yields its additive quotient representative. -/
theorem tensorComponentsToCombined_apply_pairTensorFactors_tmul (x : P₁ ⊗[k] P₂) (y : N₁ ⊗[k] N₂) :
    tensorComponentsToCombined k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (pairTensorFactors k A₁ A₂ P₁ P₂ N₁ N₂ (x ⊗ₜ[k] y))
      = QuotientAddGroup.mk (x ⊗ₜ[ℤ] y) := by
  induction x using TensorProduct.induction_on generalizing y with
  | zero => simp
  | add x x' hx hx' =>
      simp only [add_tmul, map_add, hx, hx', QuotientAddGroup.mk_add]
  | tmul p₁ p₂ =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' =>
          simp only [tmul_add, map_add, hy, hy', QuotientAddGroup.mk_add]
      | tmul n₁ n₂ => rw [pairTensorFactors_tmul_tmul, tensorComponentsToCombined_tmul_mk_tmul]

include hM hN in
/-- Mapping the combined auxiliary type to component tensors and back is the identity. -/
theorem tensorComponentsToCombined_comp_combinedToTensorComponents (z : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :
    tensorComponentsToCombined k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (combinedToTensorComponents k A₁ A₂ P₁ P₂ N₁ N₂ hM hN z) = z := by
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [combinedToTensorComponents_mk]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, QuotientAddGroup.mk_add]
  | tmul x y => rw [combinedTensorLiftAux_tmul, tensorComponentsToCombined_apply_pairTensorFactors_tmul]

include hM hN in
/-- The forward map sends the curried component construction to the corresponding pure tensor. -/
theorem combinedToTensorComponents_apply_componentTmul (t₁ : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁) (t₂ : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂) :
    combinedToTensorComponents k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (tensorComponentsToCombinedBilinear k A₁ A₂ P₁ P₂ N₁ N₂ hM hN t₁ t₂) = t₁ ⊗ₜ[k] t₂ := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective t₁
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t₂
  induction u using TensorProduct.induction_on generalizing v with
  | zero => simp
  | add u u' hu hu' =>
      simp only [QuotientAddGroup.mk_add, map_add, LinearMap.add_apply, add_tmul, hu, hu']
  | tmul p₁ n₁ =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v v' hv hv' =>
          simp only [QuotientAddGroup.mk_add, map_add, tmul_add, hv, hv']
      | tmul p₂ n₂ => rw [tensorComponentsToCombinedBilinear_mk_tmul_mk_tmul, combinedToTensorComponents_mk_tmul]

include hM hN in
/-- Mapping component tensors to the combined auxiliary type and back is the identity. -/
theorem combinedToTensorComponents_comp_tensorComponentsToCombined (r : (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁) ⊗[k] (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂)) :
    combinedToTensorComponents k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (tensorComponentsToCombined k A₁ A₂ P₁ P₂ N₁ N₂ hM hN r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r r' hr hr' => simp only [map_add, hr, hr']
  | tmul t₁ t₂ =>
      rw [tensorComponentsToCombined, TensorProduct.lift.tmul]
      exact combinedToTensorComponents_apply_componentTmul k A₁ A₂ P₁ P₂ N₁ N₂ hM hN t₁ t₂

include hM hN in

/-- Constructs a linear equivalence between the combined auxiliary type and the tensor product of the component auxiliary types. -/
noncomputable def combinedTensorComponentsEquiv :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) ≃ₗ[k]
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁) ⊗[k] (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂) :=
  LinearEquiv.ofLinear
    (combinedToTensorComponents k A₁ A₂ P₁ P₂ N₁ N₂ hM hN) (tensorComponentsToCombined k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)
    (LinearMap.ext fun r => by simpa using combinedToTensorComponents_comp_tensorComponentsToCombined k A₁ A₂ P₁ P₂ N₁ N₂ hM hN r)
    (LinearMap.ext fun z => by simpa using tensorComponentsToCombined_comp_combinedToTensorComponents k A₁ A₂ P₁ P₂ N₁ N₂ hM hN z)

include hM hN in
/-- The equivalence sends the representative of four pure factors to the tensor of the two component representatives. -/
@[simp] theorem combinedTensorComponentsEquiv_mk_tmul_tmul (p₁ : P₁) (p₂ : P₂) (n₁ : N₁) (n₂ : N₂) :
    combinedTensorComponentsEquiv k A₁ A₂ P₁ P₂ N₁ N₂ hM hN
        (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)))
      = (QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁)
          ⊗ₜ[k] (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂) :=
  combinedToTensorComponents_mk_tmul k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ p₂ n₁ n₂

include hM hN in
/-- The inverse equivalence sends a tensor of two pure representatives to the combined representative of their four factors. -/
@[simp] theorem combinedTensorComponentsEquiv_symm_tmul_mk_tmul (p₁ : P₁) (n₁ : N₁) (p₂ : P₂) (n₂ : N₂) :
    (combinedTensorComponentsEquiv k A₁ A₂ P₁ P₂ N₁ N₂ hM hN).symm
        ((QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ P₁)
          ⊗ₜ[k] (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ P₂))
      = (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
          RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :=
  tensorComponentsToCombined_tmul_mk_tmul k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁ p₂ n₂

end Main

end RepresentationTheory.Auxiliary.TensorProductPairingMaps.Auxiliary
