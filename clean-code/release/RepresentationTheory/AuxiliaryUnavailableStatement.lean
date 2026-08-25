/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.InductionAndCoinduction
import RepresentationTheory.RepresentationAveragingTrace
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary Unavailable Statement

An auxiliary trace identity for an induced representation.
-/

open Representation
open scoped TensorProduct

set_option maxHeartbeats 800000 in
/-- An auxiliary result whose formal statement is unavailable. -/
@[source_ref "Chapter5/Discussion_proof_of_Theorem5.9.1" (role := supporting),
  source_ref "Chapter5/Remark5.9.2" (role := supporting)]
theorem RepresentationTheory.AuxiliaryUnavailableStatement.auxiliary_theorem
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [DecidablePred (· ∈ H)]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H V)
    (g : G) :
    LinearMap.trace ℂ (Representation.IndV H.subtype ρ)
        (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ g)
      = (Fintype.card H : ℂ)⁻¹ *
          ∑ x : G,
            if h : x * g * x⁻¹ ∈ H then
              LinearMap.trace ℂ V (ρ ⟨x * g * x⁻¹, h⟩)
            else 0 := by
  classical
  haveI : Invertible (Fintype.card H : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Fintype.card_pos (α := H)).ne')
  rw [show RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ g =
      Representation.ind H.subtype ρ g from rfl,
    Representation.ind_apply,
    RepresentationTheory.RepresentationAveragingTrace.trace_coinvariantsMap_eq_average_trace]
  congr 1
  set τ : Representation ℂ H ((MonoidAlgebra ℂ G) ⊗[ℂ] V) :=
    Representation.tprod ((Representation.leftRegular ℂ G).comp H.subtype) ρ with hτ
  have hτh : ∀ h : H,
      τ h = TensorProduct.map (Representation.leftRegular ℂ G (↑h : G)) (ρ h) := by
    intro h; rw [hτ, Representation.tprod_apply]; rfl
  have hshift : ∀ h : H,
      Representation.leftRegular ℂ G (↑h : G) ∘ₗ
          MonoidAlgebra.mapDomainLinearMap ℂ ℂ (· * g⁻¹) =
        MonoidAlgebra.mapDomainLinearMap ℂ ℂ (fun x => (↑h : G) * x * g⁻¹) := by
    intro h
    ext y
    simp [Representation.leftRegular, Representation.ofMulAction_single, mul_assoc]
  have hper : ∀ h : H,
      LinearMap.trace ℂ ((MonoidAlgebra ℂ G) ⊗[ℂ] V)
          (τ h ∘ₗ (MonoidAlgebra.mapDomainLinearMap ℂ ℂ (· * g⁻¹)).rTensor V)
        = (∑ x : G, if (↑h : G) * x * g⁻¹ = x then (1 : ℂ) else 0)
            * LinearMap.trace ℂ V (ρ h) := by
    intro h
    have hmap : τ h ∘ₗ (MonoidAlgebra.mapDomainLinearMap ℂ ℂ (· * g⁻¹)).rTensor V
        = TensorProduct.map
            (MonoidAlgebra.mapDomainLinearMap ℂ ℂ (fun x => (↑h : G) * x * g⁻¹)) (ρ h) := by
      rw [hτh h, LinearMap.rTensor_def, ← TensorProduct.map_comp, hshift h, LinearMap.comp_id]
    rw [hmap, LinearMap.trace_tensorProduct',
      RepresentationTheory.RepresentationAveragingTrace.trace_monoidAlgebra_mapDomain_eq_sum_fixedPoints]
  rw [Finset.sum_congr rfl (fun h _ => hper h)]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcollapse : ∀ h : H,
      (if (↑h : G) * x * g⁻¹ = x then (1 : ℂ) else 0) * LinearMap.trace ℂ V (ρ h)
        = if (↑h : G) = x * g * x⁻¹ then LinearMap.trace ℂ V (ρ h) else 0 := by
    intro h
    have hiff : ((↑h : G) * x * g⁻¹ = x) ↔ ((↑h : G) = x * g * x⁻¹) := by
      rw [mul_inv_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq]
    by_cases hc : (↑h : G) = x * g * x⁻¹
    · rw [if_pos (hiff.mpr hc), if_pos hc, one_mul]
    · rw [if_neg (fun hh => hc (hiff.mp hh)), if_neg hc, zero_mul]
  rw [Finset.sum_congr rfl (fun h _ => hcollapse h),
    RepresentationTheory.RepresentationAveragingTrace.auxiliary_theorem H (x * g * x⁻¹)
      (fun h => LinearMap.trace ℂ V (ρ h))]
