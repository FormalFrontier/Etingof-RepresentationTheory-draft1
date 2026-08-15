/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.InductionAndCoinduction
import RepresentationTheory.Alignment.Attribute

/-!
# Subgroup characters in group algebras

This file constructs the representation, group-algebra element, and submodule associated with a
character of a subgroup, and relates the induced representation to that submodule.
-/

namespace RepresentationTheory.SubgroupCharacters

open scoped Classical
open Representation MonoidAlgebra

variable {G : Type*} [Group G] [Fintype G] (K : Subgroup G)

/-- Associates a complex representation of a subgroup to a character with values in complex units. -/
@[source_ref "Chapter5/Exercise5.8.5" (role := supporting)]
noncomputable def representationOfSubgroupCharacter (χ : K →* ℂˣ) : Representation ℂ K ℂ where
  toFun k := ((χ k : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' k₁ k₂ := by
    apply LinearMap.ext; intro z
    change ((χ (k₁ * k₂) : ℂˣ) : ℂ) * z = ((χ k₁ : ℂˣ) : ℂ) * (((χ k₂ : ℂˣ) : ℂ) * z)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- Associates an element of the group algebra to a subgroup character. -/
@[source_ref "Chapter5/Exercise5.8.5" (role := supporting)]
noncomputable def groupAlgebraElementOfSubgroupCharacter (χ : K →* ℂˣ) : MonoidAlgebra ℂ G :=
  (Nat.card K : ℂ)⁻¹ •
    ∑ g : K, ((χ g : ℂˣ)⁻¹ : ℂ) • MonoidAlgebra.of ℂ G (g : G)

/-- Associates a submodule of the group algebra to a subgroup character. -/
@[source_ref "Chapter5/Exercise5.8.5" (role := supporting)]
noncomputable def submoduleOfSubgroupCharacter (χ : K →* ℂˣ) :
    Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
  Submodule.span (MonoidAlgebra ℂ G) {groupAlgebraElementOfSubgroupCharacter K χ}

section Proof

variable (χ : K →* ℂˣ)

/-- The tensor-product representation whose coinvariants realize the induced representation. -/
private noncomputable abbrev indRep :=
  Representation.tprod ((leftRegular ℂ G).comp K.subtype) (representationOfSubgroupCharacter K χ)

omit [Fintype G] in
private lemma chiRep_apply (k : K) (z : ℂ) :
    representationOfSubgroupCharacter K χ k z = ((χ k : ℂˣ) : ℂ) • z := rfl

private lemma of_smul_idempotentOfChar (k : K) :
    MonoidAlgebra.of ℂ G (k : G) * groupAlgebraElementOfSubgroupCharacter K χ
      = ((χ k : ℂˣ) : ℂ) • groupAlgebraElementOfSubgroupCharacter K χ := by
  classical
  have ha : ((χ k : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [groupAlgebraElementOfSubgroupCharacter, mul_smul_comm, smul_comm]
  congr 1
  rw [Finset.mul_sum, Finset.smul_sum,
    ← Equiv.sum_comp (Equiv.mulLeft k)
      (fun g : K => ((χ k : ℂˣ) : ℂ) • (((χ g : ℂˣ)⁻¹ : ℂ) • MonoidAlgebra.of ℂ G (g : G)))]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  simp only [Equiv.coe_mulLeft]
  rw [mul_smul_comm, ← map_mul, ← Subgroup.coe_mul, smul_smul]
  congr 1
  have hb : ((χ g : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [map_mul, Units.val_mul]
  field_simp

private lemma idempotentOfChar_mul_self :
    groupAlgebraElementOfSubgroupCharacter K χ *
        groupAlgebraElementOfSubgroupCharacter K χ =
      groupAlgebraElementOfSubgroupCharacter K χ := by
  classical
  have hn : (Nat.card K : ℂ) ≠ 0 := by
    have : 0 < Nat.card K := Nat.card_pos
    exact_mod_cast this.ne'
  have hdef : groupAlgebraElementOfSubgroupCharacter K χ
      = (Nat.card K : ℂ)⁻¹ • ∑ g : K, ((χ g : ℂˣ)⁻¹ : ℂ) • MonoidAlgebra.of ℂ G (g : G) := rfl
  nth_rewrite 1 [hdef]
  rw [Finset.smul_sum, Finset.sum_mul]
  have hstep : ∀ g : K, ((Nat.card K : ℂ)⁻¹ • ((χ g : ℂˣ)⁻¹ : ℂ) •
      MonoidAlgebra.of ℂ G (g : G)) * groupAlgebraElementOfSubgroupCharacter K χ
      = (Nat.card K : ℂ)⁻¹ • groupAlgebraElementOfSubgroupCharacter K χ := by
    intro g
    rw [smul_mul_assoc, smul_mul_assoc, of_smul_idempotentOfChar, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ (Units.ne_zero (χ g)), mul_one]
  rw [Finset.sum_congr rfl (fun g _ => hstep g), Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.card_eq_fintype_card, smul_smul,
    mul_inv_cancel₀ hn, one_smul]

private noncomputable def fwdFin : MonoidAlgebra ℂ G →ₗ[ℂ] MonoidAlgebra ℂ G :=
  Finsupp.linearCombination ℂ
      (fun g : G => MonoidAlgebra.of ℂ G g⁻¹ * groupAlgebraElementOfSubgroupCharacter K χ) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] private lemma fwdFin_single (x : G) (c : ℂ) :
    fwdFin K χ (MonoidAlgebra.single x c) =
      c • (MonoidAlgebra.of ℂ G x⁻¹ * groupAlgebraElementOfSubgroupCharacter K χ) := by
  rw [fwdFin, LinearMap.comp_apply]
  change (Finsupp.linearCombination ℂ
    (fun g : G => MonoidAlgebra.of ℂ G g⁻¹ * groupAlgebraElementOfSubgroupCharacter K χ))
      (Finsupp.single x c) = _
  exact Finsupp.linearCombination_single ℂ c x

private lemma fwdFin_leftRegular (k : K) (a : MonoidAlgebra ℂ G) :
    ((χ k : ℂˣ) : ℂ) • fwdFin K χ ((leftRegular ℂ G) (K.subtype k) a) = fwdFin K χ a := by
  classical
  have ha : ((χ k : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, smul_add, hp, hq]
  | single x c =>
    simp only [Subgroup.coe_subtype, ofMulAction_single, smul_eq_mul, fwdFin_single]
    rw [smul_smul, mul_comm ((χ k : ℂˣ) : ℂ) c, ← smul_smul]
    congr 1
    rw [mul_inv_rev, ← Subgroup.coe_inv, map_mul, mul_assoc, of_smul_idempotentOfChar,
      mul_smul_comm, smul_smul, map_inv, Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ ha, one_smul]

private noncomputable def fwd :
    Representation.IndV K.subtype (representationOfSubgroupCharacter K χ) →ₗ[ℂ]
      MonoidAlgebra ℂ G :=
  Coinvariants.lift (indRep K χ)
    ((fwdFin K χ) ∘ₗ (TensorProduct.rid ℂ (MonoidAlgebra ℂ G)).toLinearMap)
    (by
      intro k
      refine TensorProduct.ext' (fun a z => ?_)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, indRep, Representation.tprod_apply,
        TensorProduct.map_tmul, TensorProduct.rid_tmul, chiRep_apply, MonoidHom.comp_apply,
        smul_eq_mul, map_smul]
      rw [mul_comm ((χ k : ℂˣ) : ℂ) z, ← smul_smul, fwdFin_leftRegular])

private lemma fwd_mk (h : G) (z : ℂ) :
    fwd K χ (Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) h z)
      = z • (MonoidAlgebra.of ℂ G h⁻¹ * groupAlgebraElementOfSubgroupCharacter K χ) := by
  simp only [fwd, Representation.IndV.mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.mk_apply, Coinvariants.lift_mk, TensorProduct.rid_tmul, map_smul,
    fwdFin_single, one_smul]

private lemma fwdFin_eq (y : MonoidAlgebra ℂ G) :
    fwdFin K χ y
      = (Finsupp.linearCombination ℂ (fun g : G => MonoidAlgebra.of ℂ G g⁻¹) y.coeff) *
        groupAlgebraElementOfSubgroupCharacter K χ := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
      rw [map_add, hp, hq, MonoidAlgebra.coeff_add, map_add, add_mul]
  | single x c =>
    rw [fwdFin_single, MonoidAlgebra.coeff_single,
      Finsupp.linearCombination_single, smul_mul_assoc]

private lemma fwd_mem (x : Representation.IndV K.subtype (representationOfSubgroupCharacter K χ)) :
    fwd K χ x ∈ submoduleOfSubgroupCharacter K χ := by
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective (indRep K χ) x
  have hfx : fwd K χ (Coinvariants.mk (indRep K χ) v)
      = (Finsupp.linearCombination ℂ (fun g : G => MonoidAlgebra.of ℂ G g⁻¹)
          ((TensorProduct.rid ℂ (MonoidAlgebra ℂ G)) v).coeff) *
        groupAlgebraElementOfSubgroupCharacter K χ := by
    rw [show fwd K χ (Coinvariants.mk (indRep K χ) v)
        = fwdFin K χ ((TensorProduct.rid ℂ (MonoidAlgebra ℂ G)) v) from rfl, fwdFin_eq]
  rw [hfx, submoduleOfSubgroupCharacter]
  exact Submodule.mem_span_singleton.2 ⟨_, smul_eq_mul _ _⟩

omit [Fintype G] in
private noncomputable def bwd :
    MonoidAlgebra ℂ G →ₗ[ℂ] Representation.IndV K.subtype
      (representationOfSubgroupCharacter K χ) :=
  Finsupp.linearCombination ℂ
      (fun g : G => Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) g⁻¹ 1) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

omit [Fintype G] in
private lemma bwd_of (x : G) :
    bwd K χ (MonoidAlgebra.of ℂ G x) =
      Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) x⁻¹ 1 := by
  change Finsupp.linearCombination ℂ
      (fun g : G => Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) g⁻¹ 1)
        (Finsupp.single x 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

omit [Fintype G] in
private lemma indV_mk_smul (κ : K) (x : G) (w : ℂ) :
    Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) ((κ : G) * x)
      (((χ κ : ℂˣ) : ℂ) • w) =
    Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) x w := by
  have h := Coinvariants.mk_self_apply (indRep K χ) κ
    (MonoidAlgebra.single x (1 : ℂ) ⊗ₜ[ℂ] w)
  simpa only [Representation.IndV.mk, LinearMap.comp_apply, TensorProduct.mk_apply, indRep,
    Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.comp_apply,
    Subgroup.coe_subtype, ofMulAction_single, smul_eq_mul, chiRep_apply] using h

private lemma bwd_of_inv_mul_idem (h : G) :
    bwd K χ (MonoidAlgebra.of ℂ G h⁻¹ * groupAlgebraElementOfSubgroupCharacter K χ)
      = Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) h 1 := by
  classical
  have hn : (Nat.card K : ℂ) ≠ 0 := by
    have : 0 < Nat.card K := Nat.card_pos
    exact_mod_cast this.ne'
  rw [groupAlgebraElementOfSubgroupCharacter, mul_smul_comm, map_smul, Finset.mul_sum, map_sum]
  have hsummand : ∀ g : K,
      bwd K χ (MonoidAlgebra.of ℂ G h⁻¹ *
          (((χ g : ℂˣ)⁻¹ : ℂ) • MonoidAlgebra.of ℂ G (g : G)))
        = Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) h 1 := by
    intro g
    rw [mul_smul_comm, map_smul, ← map_mul, bwd_of, mul_inv_rev, inv_inv, ← Subgroup.coe_inv,
      ← indV_mk_smul K χ g⁻¹ h 1, ← map_smul]
    congr 1
    rw [map_inv, Units.val_inv_eq_inv_val]
  rw [Finset.sum_congr rfl (fun g _ => hsummand g), Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.card_eq_fintype_card, smul_smul,
    inv_mul_cancel₀ hn, one_smul]

private lemma fwd_bwd (x : MonoidAlgebra ℂ G) :
    fwd K χ (bwd K χ x) = x * groupAlgebraElementOfSubgroupCharacter K χ := by
  induction x using MonoidAlgebra.induction_on with
  | hM g => rw [bwd_of, fwd_mk, inv_inv, one_smul]
  | hadd p q hp hq => rw [map_add, map_add, hp, hq, add_mul]
  | hsmul r p hp => rw [map_smul, map_smul, hp, smul_mul_assoc]

end Proof

/-- Provides an auxiliary compatibility map associated with a subgroup character. -/
@[source_ref "Chapter5/Exercise5.8.5" (role := supporting)]
theorem auxiliary_equivariant_map_of_subgroup_character (χ : K →* ℂˣ) :
    ∃ e : Representation.IndV K.subtype (representationOfSubgroupCharacter K χ) ≃ₗ[ℂ]
        ↥(submoduleOfSubgroupCharacter K χ),
      ∀ (g : G) x,
        (e (RepresentationTheory.InductionAndCoinduction.induced K
          (representationOfSubgroupCharacter K χ) g x) : MonoidAlgebra ℂ G)
          = MonoidAlgebra.of ℂ G g * (e x : MonoidAlgebra ℂ G) := by
  classical
  have hpt_left : ∀ (h : G) (z : ℂ),
      bwd K χ (fwd K χ (Representation.IndV.mk K.subtype
        (representationOfSubgroupCharacter K χ) h z))
        = Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) h z := by
    intro h z
    rw [fwd_mk, map_smul, bwd_of_inv_mul_idem, ← map_smul, smul_eq_mul, mul_one]
  have key_left : bwd K χ ∘ₗ fwd K χ = LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro h
    apply LinearMap.ext
    intro z
    change bwd K χ (fwd K χ (Representation.IndV.mk K.subtype
      (representationOfSubgroupCharacter K χ) h z))
        = Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) h z
    exact hpt_left h z
  refine ⟨LinearEquiv.ofLinear
      ((fwd K χ).codRestrict ((submoduleOfSubgroupCharacter K χ).restrictScalars ℂ)
        (fun x => fwd_mem K χ x))
      ((bwd K χ).comp ((submoduleOfSubgroupCharacter K χ).subtype.restrictScalars ℂ)) ?_ ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change fwd K χ (bwd K χ (x : MonoidAlgebra ℂ G)) = (x : MonoidAlgebra ℂ G)
    rw [fwd_bwd]
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1
      ((Submodule.restrictScalars_mem ℂ _ _).1 x.2)
    rw [← hr, smul_eq_mul, mul_assoc, idempotentOfChar_mul_self]
  · apply LinearMap.ext
    intro y
    change bwd K χ (fwd K χ y) = y
    exact LinearMap.congr_fun key_left y
  · intro g x
    have hpt : ∀ (h : G) (z : ℂ),
        fwd K χ (Representation.ind K.subtype (representationOfSubgroupCharacter K χ) g
            (Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) h z))
          = MonoidAlgebra.of ℂ G g *
              fwd K χ (Representation.IndV.mk K.subtype
                (representationOfSubgroupCharacter K χ) h z) := by
      intro h z
      rw [Representation.ind_mk, fwd_mk, fwd_mk, mul_inv_rev, inv_inv, map_mul, mul_assoc,
        mul_smul_comm]
    have key_intw : (fwd K χ) ∘ₗ
        (Representation.ind K.subtype (representationOfSubgroupCharacter K χ) g)
        = (LinearMap.mulLeft ℂ (MonoidAlgebra.of ℂ G g)) ∘ₗ (fwd K χ) := by
      apply Representation.IndV.hom_ext
      intro h
      apply LinearMap.ext
      intro z
      change fwd K χ (Representation.ind K.subtype (representationOfSubgroupCharacter K χ) g
          (Representation.IndV.mk K.subtype (representationOfSubgroupCharacter K χ) h z))
          = MonoidAlgebra.of ℂ G g *
              fwd K χ (Representation.IndV.mk K.subtype
                (representationOfSubgroupCharacter K χ) h z)
      exact hpt h z
    simp only [LinearEquiv.ofLinear_apply]
    exact LinearMap.congr_fun key_intw x

end RepresentationTheory.SubgroupCharacters
