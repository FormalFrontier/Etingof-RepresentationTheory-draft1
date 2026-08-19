/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

open Representation Module

namespace RepresentationTheory.InductionCoinduction.FiniteIndexEquivalences

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The subgroup element correcting a group element by its chosen right-coset representative. -/
noncomputable def rightCosetCorrection (H : Subgroup G) (g : G) : H :=
  ⟨g * (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)).out⁻¹,
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out' (s₁ := QuotientGroup.rightRel H) g)⟩

/-- The value of the right-coset correction is the group element times the inverse chosen representative. -/
@[simp] lemma rightCosetCorrection_val (H : Subgroup G) (g : G) :
    (rightCosetCorrection H g : G)
      = g * (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)).out⁻¹ := rfl

/-- The coinduced representation is linearly equivalent to functions from right cosets. -/
@[source_ref "Chapter5/Remark5.8.3" (role := supporting)]
noncomputable def coindVEquivRightCosetFunctions (H : Subgroup G) (ρ : Representation ℂ H V) :
    Representation.coindV H.subtype ρ ≃ₗ[ℂ]
      (Quotient (QuotientGroup.rightRel H) → V) where
  toFun f q := f.1 q.out
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun φ :=
    ⟨fun g => ρ (rightCosetCorrection H g) (φ (Quotient.mk'' g)), by
      rw [Representation.mem_coindV]
      intro s g
      have hmk : (Quotient.mk'' (H.subtype s * g) : Quotient (QuotientGroup.rightRel H))
          = Quotient.mk'' g :=
        Quotient.eq''.mpr (QuotientGroup.rightRel_apply.mpr (by
          have hs : g * (H.subtype s * g)⁻¹ = (s : G)⁻¹ := by
            rw [Subgroup.subtype_apply]; group
          rw [hs]
          exact inv_mem s.2))
      have hout : (Quotient.mk'' (H.subtype s * g)).out = (Quotient.mk'' g).out :=
        congrArg Quotient.out hmk
      have h2 : rightCosetCorrection H (H.subtype s * g) = s * rightCosetCorrection H g := by
        apply Subtype.ext
        simp only [rightCosetCorrection_val, Subgroup.coe_mul]
        rw [hout, Subgroup.subtype_apply]
        group
      change ρ (rightCosetCorrection H (H.subtype s * g)) (φ (Quotient.mk'' (H.subtype s * g)))
          = ρ s (ρ (rightCosetCorrection H g) (φ (Quotient.mk'' g)))
      rw [hmk, h2, map_mul]
      rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    change ρ (rightCosetCorrection H g)
        (f.1 (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)).out) = f.1 g
    have hf := (Representation.mem_coindV H.subtype ρ f.1).mp f.2
        (rightCosetCorrection H g) (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)).out
    have heq : H.subtype (rightCosetCorrection H g)
        * (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)).out = g := by
      rw [Subgroup.subtype_apply, rightCosetCorrection_val]; group
    conv_rhs => rw [← heq]
    exact hf.symm
  right_inv φ := by
    funext q
    change ρ (rightCosetCorrection H q.out) (φ (Quotient.mk'' q.out)) = φ q
    have hq : (Quotient.mk'' q.out : Quotient (QuotientGroup.rightRel H)) = q :=
      Quotient.out_eq' q
    have h1 : rightCosetCorrection H q.out = 1 := by
      apply Subtype.ext
      rw [rightCosetCorrection_val, show (Quotient.mk'' q.out).out = q.out from by rw [hq]]
      simp
    rw [h1, hq, map_one]
    rfl

/-- A linear equivalence between induced and coinduced representations of a finite-index subgroup. -/
noncomputable def indVEquivCoindV (H : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel H)] [H.FiniteIndex] (ρ : Representation ℂ H V) :
    Representation.IndV H.subtype ρ ≃ₗ[ℂ] Representation.coindV H.subtype ρ :=
  LinearEquiv.ofLinear
    (Rep.indToCoind (Rep.of ρ)) (Rep.coindToInd (Rep.of ρ))
    (Rep.coindToInd_indToCoind (Rep.of ρ)) (Rep.indToCoind_coindToInd (Rep.of ρ))

/-- The dimension of a coinduced representation is the subgroup index times the original dimension. -/
@[source_ref "Chapter5/Remark5.8.3" (role := supporting)]
theorem finrank_coindV (H : Subgroup G) [H.FiniteIndex] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) :
    finrank ℂ (Representation.coindV H.subtype ρ) = finrank ℂ V * H.index := by
  classical
  letI : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel H)) := inferInstance
  rw [(coindVEquivRightCosetFunctions H ρ).finrank_eq,
    Module.finrank_pi_fintype (R := ℂ), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    QuotientGroup.card_quotient_rightRel H, Subgroup.index_eq_card, Nat.card_eq_fintype_card,
    Nat.mul_comm]

/-- The dimension of an induced representation is the subgroup index times the original dimension. -/
@[source_ref "Chapter5/Remark5.8.3" (role := primary)]
theorem finrank_indV (H : Subgroup G) [H.FiniteIndex] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) :
    finrank ℂ (Representation.IndV H.subtype ρ) = finrank ℂ V * H.index := by
  classical
  rw [(indVEquivCoindV H ρ).finrank_eq, finrank_coindV H ρ]

end RepresentationTheory.InductionCoinduction.FiniteIndexEquivalences
