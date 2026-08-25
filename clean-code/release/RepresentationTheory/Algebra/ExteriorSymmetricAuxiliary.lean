/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.MutualCentralizers
import RepresentationTheory.LinearAlgebra.ExteriorPower.InvariantSubmodules
import RepresentationTheory.Alignment.Attribute

open scoped TensorProduct
open RepresentationTheory.Auxiliary.MutualCentralizers

variable (k : Type*) [Field k]
  (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- Defines an auxiliary submodule associated with a field, a module, and a natural-number index. -/
noncomputable def RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmodule' :
    Submodule k (auxiliarySpace k V n) :=
  ⨅ σ : Equiv.Perm (Fin n),
    LinearMap.ker ((auxiliarySpacePermutationEquiv k V n σ).toLinearMap - LinearMap.id)

/-- Defines an auxiliary submodule associated with a field, a module, and a natural-number index. -/
noncomputable def RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmodule :
    Submodule k (auxiliarySpace k V n) :=
  ⨅ σ : Equiv.Perm (Fin n),
    LinearMap.ker ((auxiliarySpacePermutationEquiv k V n σ).toLinearMap -
      ((Equiv.Perm.sign σ : ℤ) : k) • LinearMap.id)

namespace RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary

section SymHelpers

variable {k : Type} [Field k]
  {V : Type} [AddCommGroup V] [Module k V]
  {n : ℕ}

private lemma mem_symInvariants_iff (x : auxiliarySpace k V n) :
    x ∈ auxiliarySubmodule' k V n ↔ ∀ σ : Equiv.Perm (Fin n), auxiliarySpacePermutationEquiv k V n σ x = x := by
  simp only [auxiliarySubmodule', Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearEquiv.coe_coe, LinearMap.id_apply, sub_eq_zero]

private lemma mk_symGroupAction_eq (σ : Equiv.Perm (Fin n)) (x : auxiliarySpace k V n) :
    SymmetricPower.mk k (Fin n) V (auxiliarySpacePermutationEquiv k V n σ x) =
    SymmetricPower.mk k (Fin n) V x := by
  have : (SymmetricPower.mk k (Fin n) V).comp (auxiliarySpacePermutationEquiv k V n σ).toLinearMap =
      SymmetricPower.mk k (Fin n) V := by
    ext f
    simp only [LinearMap.comp_apply, LinearMap.coe_compMultilinearMap, Function.comp_apply,
      LinearEquiv.coe_coe, auxiliarySpacePermutationEquiv, PiTensorProduct.reindex_tprod]
    show SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k fun i => f (σ.symm i)) =
      SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f)
    change (⨂ₛ[k] i, f (σ.symm i)) = ⨂ₛ[k] i, f i
    exact SymmetricPower.tprod_equiv σ.symm f
  exact LinearMap.congr_fun this x

private noncomputable def symSum : auxiliarySpace k V n →ₗ[k] auxiliarySpace k V n :=
  ∑ σ : Equiv.Perm (Fin n), (auxiliarySpacePermutationEquiv k V n σ).toLinearMap

private lemma symSum_apply (x : auxiliarySpace k V n) :
    symSum x = ∑ σ : Equiv.Perm (Fin n), auxiliarySpacePermutationEquiv k V n σ x := by
  simp [symSum, LinearMap.sum_apply]

private lemma symGroupAction_comp (σ τ : Equiv.Perm (Fin n)) (x : auxiliarySpace k V n) :
    auxiliarySpacePermutationEquiv k V n τ (auxiliarySpacePermutationEquiv k V n σ x) =
    auxiliarySpacePermutationEquiv k V n (σ.trans τ) x := by
  have h : ((auxiliarySpacePermutationEquiv k V n τ).toLinearMap.comp
      (auxiliarySpacePermutationEquiv k V n σ).toLinearMap) =
    (auxiliarySpacePermutationEquiv k V n (σ.trans τ)).toLinearMap := by
    ext f
    simp [auxiliarySpacePermutationEquiv]
  exact LinearMap.congr_fun h x

private lemma symSum_symGroupAction (e : Equiv.Perm (Fin n)) (x : auxiliarySpace k V n) :
    symSum (auxiliarySpacePermutationEquiv k V n e x) = symSum x := by
  simp only [symSum_apply]
  simp_rw [symGroupAction_comp e _ x]
  exact Fintype.sum_equiv (Equiv.mulRight e) _ _
    (fun σ => by simp [Equiv.Perm.mul_def, Equiv.trans])

private lemma mk_comp_symSum :
    (SymmetricPower.mk k (Fin n) V).comp symSum =
    (Fintype.card (Equiv.Perm (Fin n)) : k) • SymmetricPower.mk k (Fin n) V := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.coe_compMultilinearMap,
    Function.comp_apply, symSum_apply]
  rw [map_sum]
  simp only [mk_symGroupAction_eq, Finset.sum_const, Finset.card_univ]
  rw [Nat.cast_smul_eq_nsmul k]

private lemma mk_symSum (x : auxiliarySpace k V n) :
    SymmetricPower.mk k (Fin n) V (symSum x) =
    (Fintype.card (Equiv.Perm (Fin n)) : k) • SymmetricPower.mk k (Fin n) V x :=
  LinearMap.congr_fun mk_comp_symSum x

private lemma symSum_of_mem_symInvariants (x : auxiliarySpace k V n)
    (hx : x ∈ auxiliarySubmodule' k V n) :
    symSum x = (Fintype.card (Equiv.Perm (Fin n)) : k) • x := by
  rw [symSum_apply]
  simp only [(mem_symInvariants_iff x).mp hx, Finset.sum_const, Finset.card_univ]
  rw [Nat.cast_smul_eq_nsmul k]

private lemma symSum_mem_symInvariants (x : auxiliarySpace k V n) :
    symSum x ∈ auxiliarySubmodule' k V n := by
  rw [mem_symInvariants_iff]
  intro τ
  simp only [symSum_apply, map_sum]
  simp_rw [symGroupAction_comp _ τ]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => by simp [Equiv.Perm.mul_def])

private lemma symSum_rel :
    ∀ a b, SymmetricPower.Rel k (Fin n) V a b → symSum a = symSum b := by
  intro a b hab
  cases hab with
  | perm e f =>
    have : PiTensorProduct.tprod k (fun i => f (e i)) =
        auxiliarySpacePermutationEquiv k V n e⁻¹ (PiTensorProduct.tprod k f) := by
      simp [auxiliarySpacePermutationEquiv, PiTensorProduct.reindex_tprod, Equiv.Perm.inv_def]
    rw [this, symSum_symGroupAction]

private lemma ker_mk_le_ker_symSum :
    LinearMap.ker (SymmetricPower.mk k (Fin n) V) ≤ LinearMap.ker symSum := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  let c : AddCon (⨂[k] (_ : Fin n), V) := AddCon.ker symSum.toAddMonoidHom
  have hle : addConGen (SymmetricPower.Rel k (Fin n) V) ≤ c :=
    AddCon.addConGen_le.mpr (fun a b h => symSum_rel a b h)
  have hrel : (addConGen (SymmetricPower.Rel k (Fin n) V)) x 0 := by
    have hmk : (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) V))) x =
        (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) V))) 0 := by
      change SymmetricPower.mk k (Fin n) V x = SymmetricPower.mk k (Fin n) V 0
      rw [hx, map_zero]
    exact (AddCon.eq _).mp hmk
  have h := hle hrel
  change symSum x = symSum 0 at h
  rwa [map_zero] at h

private lemma perm_card_eq_factorial :
    (Fintype.card (Equiv.Perm (Fin n)) : k) = (n.factorial : k) := by
  simp [Fintype.card_perm]

end SymHelpers

section AltHelpers

variable {k : Type} [Field k]
  {V : Type} [AddCommGroup V] [Module k V]
  {n : ℕ}

private lemma mem_symAntisymmetric_iff (x : auxiliarySpace k V n) :
    x ∈ auxiliarySubmodule k V n ↔
      ∀ σ : Equiv.Perm (Fin n),
        auxiliarySpacePermutationEquiv k V n σ x = ((Equiv.Perm.sign σ : ℤ) : k) • x := by
  simp only [auxiliarySubmodule, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

private noncomputable def altSum : auxiliarySpace k V n →ₗ[k] auxiliarySpace k V n :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : k) • (auxiliarySpacePermutationEquiv k V n σ).toLinearMap

private lemma altSum_apply (x : auxiliarySpace k V n) :
    altSum x = ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : k) • auxiliarySpacePermutationEquiv k V n σ x := by
  simp [altSum, LinearMap.sum_apply, LinearMap.smul_apply]

private lemma sign_sq (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : k) * ((Equiv.Perm.sign σ : ℤ) : k) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

private lemma sign_symm_eq_sign (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ.symm : ℤ) : k) = ((Equiv.Perm.sign σ : ℤ) : k) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [h, Equiv.Perm.sign_symm]

private lemma sign_inv_mul (τ ρ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign (τ⁻¹ * ρ) : ℤ) : k) =
      ((Equiv.Perm.sign τ : ℤ) : k) * ((Equiv.Perm.sign ρ : ℤ) : k) := by
  rw [map_mul, Units.val_mul, Int.cast_mul]
  congr 1
  exact sign_symm_eq_sign τ

private lemma altSum_of_mem_symAntisymmetric (x : auxiliarySpace k V n)
    (hx : x ∈ auxiliarySubmodule k V n) :
    altSum x = (Fintype.card (Equiv.Perm (Fin n)) : k) • x := by
  rw [altSum_apply]
  simp only [(mem_symAntisymmetric_iff x).mp hx, smul_smul, sign_sq, one_smul]
  rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul k]

private lemma altSum_mem_symAntisymmetric (x : auxiliarySpace k V n) :
    altSum x ∈ auxiliarySubmodule k V n := by
  rw [mem_symAntisymmetric_iff]
  intro τ
  rw [altSum_apply, map_sum]
  simp_rw [LinearMapClass.map_smul, symGroupAction_comp _ τ]
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft τ)
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : k) • auxiliarySpacePermutationEquiv k V n (σ.trans τ) x)
    (fun ρ => (((Equiv.Perm.sign τ : ℤ) : k) * ((Equiv.Perm.sign ρ : ℤ) : k)) •
      auxiliarySpacePermutationEquiv k V n ρ x)
    (fun ρ => ?_)
  rw [show ρ.trans τ = τ * ρ from (Equiv.Perm.mul_def τ ρ).symm]
  congr 1
  simp only [Equiv.coe_mulLeft]
  rw [map_mul, Units.val_mul, Int.cast_mul, ← mul_assoc, sign_sq, one_mul]

private noncomputable def π : auxiliarySpace k V n →ₗ[k] ↥(⋀[k]^n V) :=
  PiTensorProduct.lift (exteriorPower.ιMulti k n (M := V)).toMultilinearMap

private lemma π_tprod (v : Fin n → V) :
    π (PiTensorProduct.tprod k v) = exteriorPower.ιMulti k n v := by
  simp [π, PiTensorProduct.lift.tprod]

set_option synthInstance.maxHeartbeats 40000 in
private lemma π_symGroupAction (σ : Equiv.Perm (Fin n)) (x : auxiliarySpace k V n) :
    π (auxiliarySpacePermutationEquiv k V n σ x) = ((Equiv.Perm.sign σ : ℤ) : k) • π x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [auxiliarySpacePermutationEquiv, PiTensorProduct.reindex_tprod, map_smul, π_tprod]
    conv_lhs => rw [show (fun i => v (σ.symm i)) = v ∘ ⇑σ.symm from rfl]
    rw [(exteriorPower.ιMulti k n).map_perm (v) σ.symm]
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k, sign_symm_eq_sign, smul_comm]
  | add x y hx hy => simp [map_add, hx, hy, smul_add]

private lemma altSum_eq_toTensorPower_comp_π :
    altSum = (exteriorPower.toTensorPower k V n).comp π := by
  apply PiTensorProduct.ext
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    altSum_apply, π_tprod, exteriorPower.toTensorPower_apply_ιMulti]
  simp only [auxiliarySpacePermutationEquiv, PiTensorProduct.reindex_tprod]
  conv_rhs => arg 2; ext σ; rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
  refine Fintype.sum_equiv (Equiv.inv _)
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : k) • (PiTensorProduct.tprod k) (fun i => v (σ.symm i)))
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : k) • (PiTensorProduct.tprod k) (fun i => v (σ i)))
    (fun σ => ?_)
  change ((Equiv.Perm.sign σ : ℤ) : k) • (PiTensorProduct.tprod k) (fun i => v (σ.symm i)) =
      ((Equiv.Perm.sign σ⁻¹ : ℤ) : k) • (PiTensorProduct.tprod k) (fun i => v (σ⁻¹ i))
  rw [Equiv.Perm.inv_def, sign_symm_eq_sign]

private lemma π_comp_toTensorPower :
    π.comp (exteriorPower.toTensorPower k V n) =
    (Fintype.card (Equiv.Perm (Fin n)) : k) • LinearMap.id := by
  rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (exteriorPower.ιMulti_span k n V)]
  intro ⟨_, v, rfl⟩
  simp only [LinearMap.comp_apply, exteriorPower.toTensorPower_apply_ιMulti,
    LinearMap.smul_apply, LinearMap.id_apply]
  rw [map_sum]
  simp only [LinearMapClass.map_smul, Units.smul_def, ← Int.cast_smul_eq_zsmul k, π_tprod]
  simp_rw [show ∀ σ : Equiv.Perm (Fin n), (fun i => v (σ i)) = v ∘ ⇑σ from fun _ => rfl]
  simp_rw [(exteriorPower.ιMulti k n).map_perm v, Units.smul_def, ← Int.cast_smul_eq_zsmul k,
    smul_smul, sign_sq, one_smul, Finset.sum_const, Finset.card_univ]
  rw [Nat.cast_smul_eq_nsmul k]

private lemma π_surjective : Function.Surjective (π (k := k) (V := V) (n := n)) := by
  rw [← LinearMap.range_eq_top]
  rw [eq_top_iff, ← exteriorPower.ιMulti_span k n V]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, rfl⟩
  exact ⟨PiTensorProduct.tprod k v, π_tprod v⟩

end AltHelpers

section Equivariance

variable {k : Type} [Field k]
  {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
  {n : ℕ}

/-- Defines the linear map on symmetric powers induced by an endomorphism. -/
noncomputable def symmetricPowerMap (g : V →ₗ[k] V) :
    SymmetricPower k (Fin n) V →ₗ[k] SymmetricPower k (Fin n) V :=
  let F : auxiliarySpace k V n →+ SymmetricPower k (Fin n) V :=
    (AddCon.mk' _).comp (PiTensorProduct.map (fun _ : Fin n => g)).toAddMonoidHom
  { toFun := AddCon.lift _ F (fun x y h => Quotient.sound (by
        induction h with
        | of x y h => cases h with
          | perm e f =>
            simp only [LinearMap.toAddMonoidHom_coe, PiTensorProduct.map_tprod]
            exact AddConGen.Rel.of _ _ (SymmetricPower.Rel.perm e (fun i => g (f i)))
        | refl => exact AddCon.refl _ _
        | symm _ ih => exact AddCon.symm _ ih
        | trans _ _ ih₁ ih₂ => exact AddCon.trans _ ih₁ ih₂
        | add _ _ ih₁ ih₂ => simp only [map_add]; exact AddCon.add _ ih₁ ih₂))
    map_add' := fun x y => by
      refine AddCon.induction_on₂ x y (fun a b => ?_)
      change SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) (a + b))
        = SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) a)
        + SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) b)
      rw [map_add, map_add]
    map_smul' := fun r x => by
      refine AddCon.induction_on x (fun a => ?_)
      change SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) (r • a))
        = r • SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) a)
      rw [map_smul, map_smul] }

omit [Module.Finite k V] in
/-- Evaluates the induced symmetric-power map on a tensor class. -/
@[simp] lemma symmetricPowerMap_mk (g : V →ₗ[k] V) (x : auxiliarySpace k V n) :
    symmetricPowerMap g (SymmetricPower.mk k (Fin n) V x) =
      SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) x) :=
  rfl

/-- Shows that the tensor-product map associated with a linear endomorphism preserves membership in the auxiliary submodule. -/
lemma piTensorProductMap_mem_auxiliarySubmodule' (g : V →ₗ[k] V) {x : auxiliarySpace k V n}
    (hx : x ∈ auxiliarySubmodule' k V n) :
    PiTensorProduct.map (fun _ : Fin n => g) x ∈ auxiliarySubmodule' k V n := by
  rw [mem_symInvariants_iff] at hx ⊢
  intro σ
  have hcomm := LinearMap.congr_fun (auxiliarySpacePermutationEquiv_comp_factorwiseMap k V n σ g) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcomm
  rw [hcomm, hx σ]

/-- Shows that the tensor-product map associated with a linear endomorphism preserves membership in the auxiliary submodule. -/
lemma piTensorProductMap_mem_auxiliarySubmodule (g : V →ₗ[k] V) {x : auxiliarySpace k V n}
    (hx : x ∈ auxiliarySubmodule k V n) :
    PiTensorProduct.map (fun _ : Fin n => g) x ∈ auxiliarySubmodule k V n := by
  rw [mem_symAntisymmetric_iff] at hx ⊢
  intro σ
  have hcomm := LinearMap.congr_fun (auxiliarySpacePermutationEquiv_comp_factorwiseMap k V n σ g) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcomm
  rw [hcomm, hx σ, map_smul]

omit [Module.Finite k V] in

/-- Shows that an auxiliary map to an exterior power commutes with tensor-power maps. -/
lemma auxiliaryToExteriorPower_map (g : V →ₗ[k] V) (x : auxiliarySpace k V n) :
    π (PiTensorProduct.map (fun _ : Fin n => g) x) = exteriorPower.map n g (π x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, PiTensorProduct.map_tprod, π_tprod, exteriorPower.map_apply_ιMulti,
      Function.comp_def]
  | add x y hx hy => simp only [map_add, hx, hy]

end Equivariance

/-- Constructs a linear equivalence from an auxiliary submodule to the nth symmetric power. -/
@[source_ref "Chapter5/Example5.19.3" (role := supporting)]
noncomputable def auxiliarySubmoduleEquivSymmetricPower
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    auxiliarySubmodule' k V n ≃ₗ[k] SymmetricPower k (Fin n) V := by
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : k) ≠ 0 := by
    simp [Fintype.card_perm, Nat.factorial_ne_zero]
  exact LinearEquiv.ofBijective
    ((SymmetricPower.mk k (Fin n) V).comp (auxiliarySubmodule' k V n).subtype)
    ⟨fun a b hab => by
      ext1
      have hmk : SymmetricPower.mk k (Fin n) V (a.1 - b.1) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr hab
      have hmem : a.1 - b.1 ∈ auxiliarySubmodule' k V n := sub_mem a.2 b.2
      have h1 : symSum (a.1 - b.1) = 0 :=
        ker_mk_le_ker_symSum (LinearMap.mem_ker.mpr hmk)
      have h2 : symSum (a.1 - b.1) = (Fintype.card (Equiv.Perm (Fin n)) : k) • (a.1 - b.1) :=
        symSum_of_mem_symInvariants _ hmem
      rw [h2] at h1
      exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left hcard),
    fun y => by
      obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp (SymmetricPower.range_mk k (Fin n) V) y
      refine ⟨⟨(Fintype.card (Equiv.Perm (Fin n)) : k)⁻¹ • symSum x,
        Submodule.smul_mem _ _ (symSum_mem_symInvariants x)⟩, ?_⟩
      simp only [LinearMap.comp_apply, Submodule.coe_subtype, map_smul,
        mk_symSum, smul_smul, inv_mul_cancel₀ hcard, one_smul, hx]⟩

/-- Evaluates the symmetric-power equivalence on an element of the auxiliary submodule. -/
@[simp] lemma auxiliarySubmoduleEquivSymmetricPower_apply
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (x : auxiliarySubmodule' k V n) :
    auxiliarySubmoduleEquivSymmetricPower n x = SymmetricPower.mk k (Fin n) V x.val :=
  rfl

/-- Shows that an auxiliary submodule is linearly equivalent to the nth symmetric power. -/
theorem auxiliarySubmoduleEquivSymmetricPower_nonempty
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Nonempty (auxiliarySubmodule' k V n ≃ₗ[k] SymmetricPower k (Fin n) V) :=
  ⟨auxiliarySubmoduleEquivSymmetricPower n⟩

/-- Associates a linear endomorphism with a linear endomorphism of the auxiliary submodule. -/
noncomputable def auxiliarySubmoduleMap'
    {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] {n : ℕ}
    (g : V →ₗ[k] V) : auxiliarySubmodule' k V n →ₗ[k] auxiliarySubmodule' k V n :=
  (PiTensorProduct.map (fun _ : Fin n => g)).restrict (fun _ hx => piTensorProductMap_mem_auxiliarySubmodule' g hx)

/-- Shows that the symmetric-power equivalence commutes with induced linear maps. -/
@[source_ref "Chapter5/Example5.19.3" (role := supporting)]
theorem auxiliarySubmoduleEquivSymmetricPower_map
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (g : V →ₗ[k] V) (x : auxiliarySubmodule' k V n) :
    auxiliarySubmoduleEquivSymmetricPower n (auxiliarySubmoduleMap' g x) =
      symmetricPowerMap g (auxiliarySubmoduleEquivSymmetricPower n x) := by
  simp only [auxiliarySubmoduleEquivSymmetricPower_apply, symmetricPowerMap_mk, auxiliarySubmoduleMap',
    LinearMap.coe_restrict_apply]

/-- Constructs a linear equivalence from an auxiliary submodule to the nth exterior power. -/
@[source_ref "Chapter5/Example5.19.3" (role := supporting)]
noncomputable def auxiliarySubmoduleEquivExteriorPower
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    auxiliarySubmodule k V n ≃ₗ[k] ⋀[k]^n V := by
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : k) ≠ 0 := by
    simp [Fintype.card_perm, Nat.factorial_ne_zero]
  exact LinearEquiv.ofBijective
    (π.comp (auxiliarySubmodule k V n).subtype)
    ⟨fun a b hab => by
      ext1
      have hπ : π (a.1 - b.1) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr hab
      have h1 : altSum (a.1 - b.1) = 0 := by
        rw [altSum_eq_toTensorPower_comp_π, LinearMap.comp_apply, hπ, map_zero]
      have h2 : altSum (a.1 - b.1) = (Fintype.card (Equiv.Perm (Fin n)) : k) • (a.1 - b.1) :=
        altSum_of_mem_symAntisymmetric _ (sub_mem a.2 b.2)
      rw [h2] at h1
      exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left hcard),
    fun y => by
      obtain ⟨z, hz⟩ := π_surjective y
      refine ⟨⟨(Fintype.card (Equiv.Perm (Fin n)) : k)⁻¹ • altSum z,
        Submodule.smul_mem _ _ (altSum_mem_symAntisymmetric z)⟩, ?_⟩
      simp only [LinearMap.comp_apply, Submodule.coe_subtype, map_smul]
      rw [altSum_eq_toTensorPower_comp_π, LinearMap.comp_apply, hz]
      rw [show π ((exteriorPower.toTensorPower k V n) y) =
          (Fintype.card (Equiv.Perm (Fin n)) : k) • y from
        LinearMap.congr_fun π_comp_toTensorPower y]
      rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]⟩

/-- Evaluates the exterior-power equivalence on an element of the auxiliary submodule. -/
@[simp] lemma auxiliarySubmoduleEquivExteriorPower_apply
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (x : auxiliarySubmodule k V n) :
    auxiliarySubmoduleEquivExteriorPower n x = π x.val :=
  rfl

/-- Shows that an auxiliary submodule is linearly equivalent to the nth exterior power. -/
theorem auxiliarySubmoduleEquivExteriorPower_nonempty
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Nonempty (auxiliarySubmodule k V n ≃ₗ[k] ⋀[k]^n V) :=
  ⟨auxiliarySubmoduleEquivExteriorPower n⟩

/-- Associates a linear endomorphism with a linear endomorphism of the auxiliary submodule. -/
noncomputable def auxiliarySubmoduleMap
    {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] {n : ℕ}
    (g : V →ₗ[k] V) : auxiliarySubmodule k V n →ₗ[k] auxiliarySubmodule k V n :=
  (PiTensorProduct.map (fun _ : Fin n => g)).restrict (fun _ hx => piTensorProductMap_mem_auxiliarySubmodule g hx)

/-- Shows that the exterior-power equivalence commutes with induced linear maps. -/
@[source_ref "Chapter5/Example5.19.3" (role := supporting)]
theorem auxiliarySubmoduleEquivExteriorPower_map
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (g : V →ₗ[k] V) (x : auxiliarySubmodule k V n) :
    auxiliarySubmoduleEquivExteriorPower n (auxiliarySubmoduleMap g x) =
      exteriorPower.map n g (auxiliarySubmoduleEquivExteriorPower n x) := by
  simp only [auxiliarySubmoduleEquivExteriorPower_apply, auxiliarySubmoduleMap, LinearMap.coe_restrict_apply]
  exact auxiliaryToExteriorPower_map g x.val

/-- The nth exterior power is subsingleton when n exceeds the finrank. -/
@[source_ref "Chapter5/Example5.19.3" (role := primary)]
theorem exteriorPower_subsingleton_of_finrank_lt
    {k : Type} [Field k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n : ℕ} (hn : Module.finrank k V < n) :
    Subsingleton (⋀[k]^n V) := by
  have h0 : Module.finrank k (⋀[k]^n V) = 0 := by
    rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt hn]
  exact Module.finrank_zero_iff.mp h0

/-- An invariant submodule of an exterior power is either bottom or top. -/
@[source_ref "Chapter4/Problem4.12.3" (role := primary),
  source_ref "Chapter5/Example5.19.3" (role := primary)]
theorem exteriorPower_invariantSubmodule_eq_bot_or_top
    {k : Type} [Field k] [CharZero k] {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    ∀ W : Submodule k (⋀[k]^n V),
    (∀ g : V ≃ₗ[k] V, ∀ w ∈ W, exteriorPower.map n (g : V →ₗ[k] V) w ∈ W) →
      W = ⊥ ∨ W = ⊤ :=
  fun W hW => RepresentationTheory.LinearAlgebra.ExteriorPower.InvariantSubmodules.eq_bot_or_eq_top_of_exteriorPower_invariant W hW

end RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary
