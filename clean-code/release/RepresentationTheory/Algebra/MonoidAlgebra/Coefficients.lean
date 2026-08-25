/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial
import RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich

namespace RepresentationTheory.Algebra.MonoidAlgebra.Coefficients

open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.PartitionAuxiliary
open RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra
open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
open RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra
open
  RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter

/-- A monoid algebra over a semiring coerces to its coefficient function. -/
local instance monoidAlgebraCoeFun {R M : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R M) (fun _ => M → R) :=
  ⟨fun a => a.coeff⟩

noncomputable section
open Classical in
private lemma partitionSymmetrizer_coeff_cast (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    (partitionSymmetrizer ℚ n la σ : ℂ) = auxiliaryPartitionGroupAlgebraElementC n la σ := by
  rw [partitionSymmetrizer_eq_map_int ℚ n la, complexPartitionSymmetrizer_eq_map_int n la]
  simp only [MonoidAlgebra.coeff_mapRingHom]
  exact_mod_cast rfl

private lemma partitionSymmetrizer_sq_complex (n : ℕ) (la : Nat.Partition n)
    (α : ℚ) (hα : partitionSymmetrizer ℚ n la * partitionSymmetrizer ℚ n la =
      α • partitionSymmetrizer ℚ n la) :
    auxiliaryPartitionGroupAlgebraElementC n la *
        auxiliaryPartitionGroupAlgebraElementC n la =
      (α : ℂ) • auxiliaryPartitionGroupAlgebraElementC n la := by
  set cZ := integralPartitionSymmetrizer n la
  set β : ℤ := (cZ * cZ) 1
  set φ_ℚ := MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℚ)
  set φ_ℂ := MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℂ)
  have h_ℚ : partitionSymmetrizer ℚ n la = φ_ℚ cZ :=
    partitionSymmetrizer_eq_map_int ℚ n la
  have h_ℂ : auxiliaryPartitionGroupAlgebraElementC n la = φ_ℂ cZ :=
    complexPartitionSymmetrizer_eq_map_int n la
  have hcZ1 : cZ 1 = 1 := integralPartitionSymmetrizer_coeff_one n la
  have hmul_ℚ : φ_ℚ (cZ * cZ) = α • φ_ℚ cZ := by
    rw [map_mul]
    exact h_ℚ ▸ hα
  have hα_eq : α = (β : ℚ) := by
    have h1 := congrArg (fun x => x.coeff 1) hmul_ℚ
    simp only [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_smul_apply,
      smul_eq_mul, hcZ1, map_one, mul_one, φ_ℚ] at h1
    exact h1.symm
  have hZ : cZ * cZ = β • cZ := by
    ext σ
    have h1 := congrArg (fun x => x.coeff σ) hmul_ℚ
    simp only [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_smul_apply,
      smul_eq_mul, hα_eq, φ_ℚ] at h1
    have h2 : ((cZ * cZ) σ : ℚ) = ((β * cZ σ : ℤ) : ℚ) := by
      push_cast
      exact h1
    have h3 : (cZ * cZ) σ = β * cZ σ := Int.cast_injective h2
    rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, h3]
  rw [h_ℂ, ← map_mul, hZ, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
  congr 1
  exact_mod_cast hα_eq.symm

private def mulLeftOnPartitionSubtype (n : ℕ) (c : natIndexedType n)
    (la' : Nat.Partition n) :
    ↑(partitionSubmodule n la') →ₗ[ℂ] ↑(partitionSubmodule n la') :=
  LinearMap.codRestrict ((partitionSubmodule n la').restrictScalars ℂ)
    ((LinearMap.mulLeft ℂ c).comp
      ((partitionSubmodule n la').restrictScalars ℂ).subtype)
    (fun v => (partitionSubmodule n la').smul_mem c v.prop)

private lemma mulLeftOnPartitionSubtype_of (n : ℕ) (la' : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    mulLeftOnPartitionSubtype n (MonoidAlgebra.of ℂ _ σ) la' =
      auxiliarySubtypePermutationEndomorphism n la' σ := by
  ext ⟨m, hm⟩
  rfl

private noncomputable def mulLeftOnPartitionSubtypeLinear (n : ℕ)
    (la' : Nat.Partition n) :
    natIndexedType n →ₗ[ℂ]
      (↑(partitionSubmodule n la') →ₗ[ℂ] ↑(partitionSubmodule n la')) where
  toFun c := mulLeftOnPartitionSubtype n c la'
  map_add' a b := by
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    exact add_mul a b m
  map_smul' r c := by
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    exact smul_mul_assoc r c m

private lemma sum_coeff_auxiliaryValue_eq_trace (n : ℕ) (la' : Nat.Partition n)
    (c : natIndexedType n) :
    ∑ σ : Equiv.Perm (Fin n), c σ * auxiliaryPartitionPermutationValue n la' σ =
      LinearMap.trace ℂ _ (mulLeftOnPartitionSubtype n c la') := by
  symm
  have key : (LinearMap.trace ℂ _) (mulLeftOnPartitionSubtype n c la') =
      ∑ σ ∈ c.coeff.support, c σ * auxiliaryPartitionPermutationValue n la' σ := by
    have hlin : mulLeftOnPartitionSubtype n c la' =
        (mulLeftOnPartitionSubtypeLinear n la') c := rfl
    rw [hlin]
    simp_rw [auxiliaryPartitionPermutationValue,
      ← mulLeftOnPartitionSubtype_of n la']
    have hc : c = ∑ σ ∈ c.coeff.support,
        c σ • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ := by
      conv_lhs => rw [← MonoidAlgebra.sum_coeff_single c]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
    conv_lhs =>
      rw [show (mulLeftOnPartitionSubtypeLinear n la') c =
        (mulLeftOnPartitionSubtypeLinear n la')
          (∑ σ ∈ c.coeff.support, c σ • MonoidAlgebra.of ℂ _ σ) from by rw [← hc]]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [map_smul, LinearMap.map_smul, smul_eq_mul]
    rfl
  rw [key]
  apply Finset.sum_subset (Finset.subset_univ c.coeff.support)
  intro σ _ hσ
  have : c σ = 0 := by
    rwa [Finsupp.mem_support_iff, not_not] at hσ
  simp [this]

set_option maxHeartbeats 1600000 in
-- Constructing and comparing the subtype-valued intertwiner is elaboration-intensive.
private lemma mulLeft_partitionSymmetrizer_eq_zero_of_ne (n : ℕ)
    (la la' : Nat.Partition n) (hne : la ≠ la') :
    mulLeftOnPartitionSubtype n (auxiliaryPartitionGroupAlgebraElementC n la) la' = 0 := by
  by_contra hT
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : partitionSubmodule n la',
      mulLeftOnPartitionSubtype n (auxiliaryPartitionGroupAlgebraElementC n la) la' w₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hT (LinearMap.ext hall)
  set φ : partitionSubmodule n la →ₗ[natIndexedType n] partitionSubmodule n la' :=
    { toFun := fun v =>
        ⟨(v : natIndexedType n) * (w₀ : natIndexedType n),
          (partitionSubmodule n la').smul_mem (v : natIndexedType n) w₀.prop⟩
      map_add' := fun a b => Subtype.ext (add_mul (a : natIndexedType n) b w₀)
      map_smul' := fun a v => Subtype.ext (mul_assoc a (v : natIndexedType n) w₀) }
  have hφ_ne : φ ≠ 0 := by
    intro h
    apply hw₀
    let e : partitionSubmodule n la :=
      ⟨auxiliaryPartitionGroupAlgebraElementC n la, Submodule.subset_span rfl⟩
    have he := LinearMap.congr_fun h e
    apply Subtype.ext
    change auxiliaryPartitionGroupAlgebraElementC n la * (w₀ : natIndexedType n) = 0
    have hev := congrArg Subtype.val he
    change auxiliaryPartitionGroupAlgebraElementC n la * (w₀ : natIndexedType n) = 0 at hev
    exact hev
  haveI : IsSimpleModule (natIndexedType n) (partitionSubmodule n la) :=
    partitionSubmodule_isSimpleModule n la
  haveI : IsSimpleModule (natIndexedType n) (partitionSubmodule n la') :=
    partitionSubmodule_isSimpleModule n la'
  have hφ_bij := LinearMap.bijective_of_ne_zero hφ_ne
  exact (isEmpty_linearEquiv_of_ne_partition n la la' hne).false
    (LinearEquiv.ofBijective φ hφ_bij)

private lemma partitionSymmetrizer_coeff_one (n : ℕ) (la : Nat.Partition n) :
    (auxiliaryPartitionGroupAlgebraElementC n la :
      MonoidAlgebra ℂ (Equiv.Perm (Fin n))) 1 = 1 := by
  rw [complexPartitionSymmetrizer_eq_map_int]
  simp [MonoidAlgebra.coeff_mapRingHom, integralPartitionSymmetrizer_coeff_one]

private lemma mul_mem_partitionSubtype_proportional (n : ℕ) (la : Nat.Partition n)
    (v : ↑(partitionSubmodule n la)) :
    auxiliaryPartitionGroupAlgebraElementC n la * v.val =
      (auxiliaryPartitionGroupAlgebraElementC n la * v.val) 1 •
        auxiliaryPartitionGroupAlgebraElementC n la := by
  classical
  set c := auxiliaryPartitionGroupAlgebraElementC n la
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp v.prop
  rw [smul_eq_mul] at ha
  obtain ⟨ℓ, hℓ⟩ := exists_sign_fixed_sandwich_eq_smul n la
  have h_sandwich : ∀ x,
      c * x * c =
        ℓ (auxiliaryPartitionGroupAlgebraElementB n la *
          (x * auxiliaryPartitionGroupAlgebraElementA n la)) • c := by
    intro x
    change auxiliaryPartitionGroupAlgebraElementA n la *
        auxiliaryPartitionGroupAlgebraElementB n la * x *
          (auxiliaryPartitionGroupAlgebraElementA n la *
            auxiliaryPartitionGroupAlgebraElementB n la) = _
    rw [show auxiliaryPartitionGroupAlgebraElementA n la *
          auxiliaryPartitionGroupAlgebraElementB n la * x *
            (auxiliaryPartitionGroupAlgebraElementA n la *
              auxiliaryPartitionGroupAlgebraElementB n la) =
        auxiliaryPartitionGroupAlgebraElementA n la *
          (auxiliaryPartitionGroupAlgebraElementB n la *
            (x * auxiliaryPartitionGroupAlgebraElementA n la)) *
              auxiliaryPartitionGroupAlgebraElementB n la from by
        simp only [mul_assoc]]
    rw [hℓ]
  have hsand := h_sandwich a
  conv_lhs at hsand => rw [mul_assoc]
  conv_lhs => rw [show v.val = a * c from ha.symm, hsand]
  conv_rhs => rw [show v.val = a * c from ha.symm, hsand]
  congr 1
  rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, partitionSymmetrizer_coeff_one,
    mul_one]

private lemma trace_mulLeft_partitionSymmetrizer_eq (n : ℕ) (la : Nat.Partition n)
    (α : ℂ) (_hα_ne : α ≠ 0)
    (hα_sq : auxiliaryPartitionGroupAlgebraElementC n la *
      auxiliaryPartitionGroupAlgebraElementC n la =
        α • auxiliaryPartitionGroupAlgebraElementC n la) :
    LinearMap.trace ℂ _
      (mulLeftOnPartitionSubtype n (auxiliaryPartitionGroupAlgebraElementC n la) la) =
        α := by
  set c := auxiliaryPartitionGroupAlgebraElementC n la with hc_def
  set V := partitionSubmodule n la
  set T := mulLeftOnPartitionSubtype n c la
  have hc_mem : c ∈ V := Submodule.subset_span rfl
  set e : V := ⟨c, hc_mem⟩
  let ι : ℂ →ₗ[ℂ] V := LinearMap.lsmul ℂ V |>.flip e
  let π : V →ₗ[ℂ] ℂ :=
    { toFun := fun v => (c * v.val) 1
      map_add' := fun x y => by simp [mul_add]
      map_smul' := fun r x => by
        change (c * (r • x.val)) 1 = r * (c * x.val) 1
        rw [Algebra.mul_smul_comm, MonoidAlgebra.coeff_smul_apply, smul_eq_mul] }
  have hT_eq : T = ι.comp π := by
    apply LinearMap.ext
    intro ⟨v, hv⟩
    apply Subtype.ext
    exact mul_mem_partitionSubtype_proportional n la ⟨v, hv⟩
  rw [hT_eq, LinearMap.trace_comp_comm']
  have h_comp : π.comp ι = α • LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (c * (x • c)) 1 = α * x
    rw [Algebra.mul_smul_comm, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    rw [hα_sq, MonoidAlgebra.coeff_smul_apply, smul_eq_mul,
      partitionSymmetrizer_coeff_one, mul_one, mul_comm]
  rw [h_comp]
  simp [map_smul, LinearMap.trace_id, Module.finrank_self]

/-- If the displayed element squares to a scalar multiple of itself, the indicated
coefficient-weighted sum is that scalar when the partitions agree and zero otherwise. -/
theorem weighted_coeff_sum_eq_ite_of_mul_self_eq_smul (n : ℕ)
    (la la' : Nat.Partition n) (α : ℚ)
    (hα_sq : partitionSymmetrizer ℚ n la * partitionSymmetrizer ℚ n la =
      α • partitionSymmetrizer ℚ n la) :
    ∑ σ : Equiv.Perm (Fin n),
      (partitionSymmetrizer ℚ n la σ : ℂ) *
        auxiliaryPartitionPermutationValue n la' σ =
      if la = la' then (α : ℂ) else 0 := by
  conv_lhs =>
    arg 2
    ext σ
    rw [partitionSymmetrizer_coeff_cast]
  have hα_ℂ := partitionSymmetrizer_sq_complex n la α hα_sq
  have hα_ne : (α : ℂ) ≠ 0 := by
    exact_mod_cast ne_zero_of_partitionSymmetrizer_sq_eq_smul n la α hα_sq
  rw [sum_coeff_auxiliaryValue_eq_trace]
  split_ifs with h
  · subst h
    exact trace_mulLeft_partitionSymmetrizer_eq n la (α : ℂ) hα_ne hα_ℂ
  · rw [mulLeft_partitionSymmetrizer_eq_zero_of_ne n la la' h, map_zero]

end

end RepresentationTheory.Algebra.MonoidAlgebra.Coefficients
