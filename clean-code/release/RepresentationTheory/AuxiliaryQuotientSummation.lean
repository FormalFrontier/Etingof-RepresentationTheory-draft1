/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import Mathlib
import RepresentationTheory.AuxiliaryUnavailableStatement
import RepresentationTheory.InductionCoinduction.FiniteIndexEquivalences
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary quotient summation

This module provides auxiliary identities relating subgroup-invariant finite-group sums to sums
over chosen right-quotient representatives.
-/

open Representation

namespace RepresentationTheory.AuxiliaryQuotientSummation

variable {G : Type*} [Group G] [Fintype G]
  (H : Subgroup G) [DecidablePred (· ∈ H)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
  (ρ : Representation ℂ H V)

omit [Fintype G] [Module.Finite ℂ V] in
/-- An additional auxiliary result whose formal statement is unavailable. -/
@[source_ref "Chapter5/Theorem5.9.1" (role := supporting)]
theorem auxiliary_additional_result (g : G) (h₀ : H) (x : G) :
    (if h : (↑h₀ * x) * g * (↑h₀ * x)⁻¹ ∈ H then
        LinearMap.trace ℂ V (ρ ⟨(↑h₀ * x) * g * (↑h₀ * x)⁻¹, h⟩) else 0)
      = (if h : x * g * x⁻¹ ∈ H then
        LinearMap.trace ℂ V (ρ ⟨x * g * x⁻¹, h⟩) else 0) := by
  have hconj : (↑h₀ * x) * g * (↑h₀ * x)⁻¹ = ↑h₀ * (x * g * x⁻¹) * (↑h₀ : G)⁻¹ := by group
  have hiff : (↑h₀ * x) * g * (↑h₀ * x)⁻¹ ∈ H ↔ x * g * x⁻¹ ∈ H := by
    rw [hconj]
    constructor
    · intro hc
      have h1 : (↑h₀ : G)⁻¹ * (↑h₀ * (x * g * x⁻¹) * (↑h₀ : G)⁻¹) * ↑h₀ = x * g * x⁻¹ := by group
      rw [← h1]
      exact H.mul_mem (H.mul_mem (H.inv_mem h₀.2) hc) h₀.2
    · intro hx
      exact H.mul_mem (H.mul_mem h₀.2 hx) (H.inv_mem h₀.2)
  by_cases hx : x * g * x⁻¹ ∈ H
  · rw [dif_pos (hiff.mpr hx), dif_pos hx]
    set a : H := ⟨x * g * x⁻¹, hx⟩ with ha
    have hsub : (⟨(↑h₀ * x) * g * (↑h₀ * x)⁻¹, hiff.mpr hx⟩ : H) = h₀ * a * h₀⁻¹ := by
      apply Subtype.ext
      change (↑h₀ * x) * g * (↑h₀ * x)⁻¹ = ↑h₀ * (x * g * x⁻¹) * (↑h₀ : G)⁻¹
      exact hconj
    rw [hsub, map_mul ρ (h₀ * a) h₀⁻¹, map_mul ρ h₀ a, LinearMap.trace_mul_cycle,
      ← map_mul ρ h₀⁻¹ h₀, inv_mul_cancel, map_one, one_mul]
  · rw [dif_neg (fun hc => hx (hiff.mp hc)), dif_neg hx]

omit [Fintype G] [Module.Finite ℂ V] in
/-- A further auxiliary result whose formal statement is unavailable. -/
@[source_ref "Chapter5/Theorem5.9.1" (role := supporting)]
theorem auxiliary_other_result (g : G) {x y : G}
    (hxy : (Quotient.mk'' x : Quotient (QuotientGroup.rightRel H)) = Quotient.mk'' y) :
    (if h : x * g * x⁻¹ ∈ H then LinearMap.trace ℂ V (ρ ⟨x * g * x⁻¹, h⟩) else 0)
      = (if h : y * g * y⁻¹ ∈ H then LinearMap.trace ℂ V (ρ ⟨y * g * y⁻¹, h⟩) else 0) := by
  have hrel : y * x⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.eq''.mp hxy)
  have hyx : ((⟨y * x⁻¹, hrel⟩ : H) : G) * x = y := by
    change (y * x⁻¹) * x = y
    group
  rw [← hyx, auxiliary_additional_result]

/-- For a subgroup-invariant complex-valued function, the normalized sum over the group equals the sum over chosen quotient representatives. -/
@[source_ref "Chapter5/Remark5.9.2" (role := primary),
  source_ref "Chapter5/Discussion_proof_of_Theorem5.9.1" (role := primary)]
theorem inv_card_mul_sum_eq_sum_quotient [Fintype (Quotient (QuotientGroup.rightRel H))]
    (F : G → ℂ) (hF : ∀ (h₀ : H) (x : G), F (↑h₀ * x) = F x) :
    (Fintype.card H : ℂ)⁻¹ * ∑ x : G, F x
      = ∑ q : Quotient (QuotientGroup.rightRel H), F q.out := by
  classical
  have hbij : Function.Bijective
      (fun p : H × Quotient (QuotientGroup.rightRel H) => (↑p.1 * p.2.out : G)) := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun x =>
      (RepresentationTheory.InductionCoinduction.FiniteIndexEquivalences.rightCosetCorrection H x,
        Quotient.mk'' x), ?_, ?_⟩
    · rintro ⟨h, q⟩
      have hmk : (Quotient.mk'' (↑h * q.out) : Quotient (QuotientGroup.rightRel H)) = q := by
        have hrel : (Quotient.mk'' (↑h * q.out) : Quotient (QuotientGroup.rightRel H))
            = Quotient.mk'' q.out :=
          Quotient.eq''.mpr (QuotientGroup.rightRel_apply.mpr (by
            have hs : q.out * (↑h * q.out)⁻¹ = ((↑h : G))⁻¹ := by group
            rw [hs]; exact inv_mem h.2))
        rw [hrel, Quotient.out_eq']
      have htw :
          RepresentationTheory.InductionCoinduction.FiniteIndexEquivalences.rightCosetCorrection
              H (↑h * q.out) = h := by
        apply Subtype.ext
        rw [RepresentationTheory.InductionCoinduction.FiniteIndexEquivalences.rightCosetCorrection_val,
          show (Quotient.mk'' (↑h * q.out)
            : Quotient (QuotientGroup.rightRel H)).out = q.out from by rw [hmk]]
        group
      change
        (RepresentationTheory.InductionCoinduction.FiniteIndexEquivalences.rightCosetCorrection
            H (↑h * q.out), Quotient.mk'' (↑h * q.out)) = (h, q)
      rw [Prod.mk.injEq]
      exact ⟨htw, hmk⟩
    · intro x
      change
        (↑(RepresentationTheory.InductionCoinduction.FiniteIndexEquivalences.rightCosetCorrection H x) : G) *
            (Quotient.mk'' x).out = x
      rw [RepresentationTheory.InductionCoinduction.FiniteIndexEquivalences.rightCosetCorrection_val]; group
  have hsum : ∑ x : G, F x
      = ∑ p : H × Quotient (QuotientGroup.rightRel H), F (↑p.1 * p.2.out) :=
    (Fintype.sum_bijective _ hbij (fun p => F (↑p.1 * p.2.out)) F (fun _ => rfl)).symm
  rw [hsum, Fintype.sum_prod_type]
  simp_rw [hF]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := H)).ne'), one_mul]

set_option linter.unusedFintypeInType false in
/-- An auxiliary result whose formal statement is unavailable. -/
@[source_ref "Chapter5/Introduction_5.9" (role := supporting),
  source_ref "Chapter5/Theorem5.9.1" (role := supporting),
  source_ref "Chapter5/Discussion_proof_of_Theorem5.9.1" (role := supporting)]
theorem auxiliary_theorem [Fintype (Quotient (QuotientGroup.rightRel H))] (g : G) :
    LinearMap.trace ℂ (Representation.IndV H.subtype ρ)
        (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ g)
      = ∑ q : Quotient (QuotientGroup.rightRel H),
          if h : q.out * g * q.out⁻¹ ∈ H then
            LinearMap.trace ℂ V (ρ ⟨q.out * g * q.out⁻¹, h⟩)
          else 0 := by
  rw [RepresentationTheory.AuxiliaryUnavailableStatement.auxiliary_theorem H ρ g]
  exact inv_card_mul_sum_eq_sum_quotient H
    (fun x => if h : x * g * x⁻¹ ∈ H then LinearMap.trace ℂ V (ρ ⟨x * g * x⁻¹, h⟩) else 0)
    (fun h₀ x => auxiliary_additional_result H ρ g h₀ x)

end RepresentationTheory.AuxiliaryQuotientSummation
