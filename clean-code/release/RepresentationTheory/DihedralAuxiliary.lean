/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.AuxiliaryRepresentationIsomorphisms
import RepresentationTheory.GroupTheory.ZMod.ComplexCharacters
import RepresentationTheory.ComplexUnitCharacters
import RepresentationTheory.FiniteDimensional.Equivalences
import RepresentationTheory.Alignment.Attribute

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Module

namespace RepresentationTheory.DihedralAuxiliary

variable (N : ℕ) [NeZero N]

/-- Defines an auxiliary automorphism of multiplicative residues modulo N. -/
def auxiliaryMulAut : MulAut (Multiplicative (ZMod N)) := MulEquiv.inv (Multiplicative (ZMod N))

omit [NeZero N] in
/-- The auxiliary automorphism sends each multiplicative residue to its inverse. -/
@[simp] lemma auxiliaryMulAut_apply (a : Multiplicative (ZMod N)) : auxiliaryMulAut N a = a⁻¹ := rfl

omit [NeZero N] in
/-- The square of the auxiliary automorphism is the identity. -/
lemma auxiliaryMulAut_sq : auxiliaryMulAut N * auxiliaryMulAut N = 1 := by
  ext a; simp

/-- Defines an action of multiplicative residues modulo two by automorphisms of multiplicative residues modulo N. -/
def multiplicativeZModAction : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod N)) :=
  MonoidHom.mk' (fun g => if Multiplicative.toAdd g = 0 then 1 else auxiliaryMulAut N) <| by
    intro a b
    have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    simp only [toAdd_mul]
    rcases h2 (Multiplicative.toAdd a) with ha | ha <;>
      rcases h2 (Multiplicative.toAdd b) with hb | hb <;> simp only [ha, hb]
    · simp
    · simp
    · simp
    · exact (auxiliaryMulAut_sq N).symm

omit [NeZero N] in
/-- The identity residue acts trivially on multiplicative residues. -/
@[simp] lemma multiplicativeZModAction_one_apply (a : Multiplicative (ZMod N)) :
    (multiplicativeZModAction N (1 : Multiplicative (ZMod 2))) a = a := by
  simp only [multiplicativeZModAction, MonoidHom.mk'_apply]
  rw [if_pos]; · rfl
  rfl

omit [NeZero N] in
/-- The action of the multiplicative image of one sends a multiplicative residue to its inverse. -/
@[simp] lemma multiplicativeZModAction_ofAdd_one_apply (a : Multiplicative (ZMod N)) :
    (multiplicativeZModAction N (Multiplicative.ofAdd (1 : ZMod 2))) a = a⁻¹ := by
  simp only [multiplicativeZModAction, MonoidHom.mk'_apply, toAdd_ofAdd]
  rw [if_neg (by decide)]; rfl

/-- An auxiliary type indexed by a natural number. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
abbrev Auxiliary : Type := Multiplicative (ZMod N) ⋊[multiplicativeZModAction N] Multiplicative (ZMod 2)

/-- Constructs a multiplicative equivalence from a dihedral group to an auxiliary type. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
def dihedralAuxiliaryMulEquiv : DihedralGroup N ≃* Auxiliary N where
  toFun x := match x with
    | .r i => ⟨Multiplicative.ofAdd i, 1⟩
    | .sr i => ⟨Multiplicative.ofAdd (-i), Multiplicative.ofAdd (1 : ZMod 2)⟩
  invFun p :=
    if Multiplicative.toAdd p.right = 0
    then DihedralGroup.r (Multiplicative.toAdd p.left)
    else DihedralGroup.sr (- Multiplicative.toAdd p.left)
  left_inv x := by
    cases x with
    | r i => simp
    | sr i => simp [(by decide : (1 : ZMod 2) ≠ 0)]
  right_inv p := by
    obtain ⟨a, g⟩ := p
    have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases h2 (Multiplicative.toAdd g) with hg | hg
    · have : g = 1 := by
        rw [← ofAdd_toAdd g, hg]; rfl
      subst this; simp
    · have : g = Multiplicative.ofAdd (1 : ZMod 2) := by
        rw [← ofAdd_toAdd g, hg]
      subst this
      simp only [toAdd_ofAdd, (by decide : (1 : ZMod 2) ≠ 0), if_false, neg_neg,
        ofAdd_toAdd]
  map_mul' x y := by
    cases x <;> cases y <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr] <;>
      apply SemidirectProduct.ext <;>
      simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right, ← ofAdd_neg, ← ofAdd_add,
        sub_eq_add_neg, add_comm, show (1 : ZMod 2) + 1 = 0 from by decide, ofAdd_zero]

/-- Defines an equivalence between representation categories for an auxiliary type and a dihedral group. -/
def auxiliaryRepresentationEquivalence :
    FDRep ℂ (Auxiliary N) ≌ FDRep ℂ (DihedralGroup N) :=
  RepresentationTheory.FiniteDimensional.Equivalences.fdRepEquivalenceOfMulEquiv (dihedralAuxiliaryMulEquiv N)

omit [NeZero N] in

/-- The representation-category equivalence preserves complex dimension. -/
lemma auxiliaryRepresentationEquivalence_finrank (V : FDRep ℂ (Auxiliary N)) :
    finrank ℂ ((auxiliaryRepresentationEquivalence N).functor.obj V : Type) = finrank ℂ (V : Type) := rfl

open Classical in

/-- Provides simple complex representation representatives of an auxiliary group with the displayed dimension and parity-dependent counts. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
theorem exists_auxiliarySimpleRepresentatives :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (Auxiliary N)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (Auxiliary N), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      (∀ i, finrank ℂ (W i : Type) = 1 ∨ finrank ℂ (W i : Type) = 2) ∧
      (Odd N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 2 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 1) / 2) ∧
      (Even N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 4 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 2) / 2) := by
  classical
  obtain ⟨dualSmul, hdual, stab, hstab, V, transport, hi, hii, hiii, hiv, hv, hvi,
      hvii, hviii, hix⟩ :=
    RepresentationTheory.AuxiliaryRepresentationIsomorphisms.auxiliary_theorem (Multiplicative (ZMod 2)) (Multiplicative (ZMod N)) (multiplicativeZModAction N)

  have hgen_inv : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide

  have hdual_gen : ∀ χ : Multiplicative (ZMod N) →* ℂˣ,
      dualSmul (Multiplicative.ofAdd 1) χ = χ⁻¹ := by
    intro χ
    refine MonoidHom.ext (fun a => ?_)
    rw [hdual, hgen_inv, multiplicativeZModAction_ofAdd_one_apply, map_inv, MonoidHom.inv_apply]

  have hdual_one : ∀ χ : Multiplicative (ZMod N) →* ℂˣ,
      dualSmul (1 : Multiplicative (ZMod 2)) χ = χ := by
    intro χ
    refine MonoidHom.ext (fun a => ?_)
    rw [hdual, inv_one, multiplicativeZModAction_one_apply]

  have hstab_gen : ∀ χ : Multiplicative (ZMod N) →* ℂˣ,
      (Multiplicative.ofAdd 1 ∈ stab χ) ↔ χ⁻¹ = χ := by
    intro χ; rw [hstab χ (Multiplicative.ofAdd 1), hdual_gen]

  have hG2 : ∀ g : Multiplicative (ZMod 2), g = 1 ∨ g = Multiplicative.ofAdd 1 := by
    intro g
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (Multiplicative.toAdd g) with h | h
    · left; rw [← ofAdd_toAdd g, h]; rfl
    · right; rw [← ofAdd_toAdd g, h]

  have hstab_top : ∀ χ : Multiplicative (ZMod N) →* ℂˣ, χ⁻¹ = χ → stab χ = ⊤ := by
    intro χ hχ
    rw [eq_top_iff]; intro g _
    rcases hG2 g with rfl | rfl
    · exact one_mem _
    · exact (hstab_gen χ).mpr hχ
  have hstab_bot : ∀ χ : Multiplicative (ZMod N) →* ℂˣ, χ⁻¹ ≠ χ → stab χ = ⊥ := by
    intro χ hχ
    rw [eq_bot_iff]; intro g hg
    rcases hG2 g with rfl | rfl
    · exact Subgroup.mem_bot.mpr rfl
    · exact absurd ((hstab_gen χ).mp hg) hχ

  haveI : Fintype (Multiplicative (ZMod N) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype (Multiplicative (ZMod 2) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} := Fintype.ofFinite _

  have hcardG2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

  have hdim_self : ∀ (χ : Multiplicative (ZMod N) →* ℂˣ), χ⁻¹ = χ →
      ∀ ρ : Multiplicative (ZMod 2) →* ℂˣ,
      finrank ℂ (V χ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (ρ.comp (stab χ).subtype)) : Type) = 1 := by
    intro χ hχ ρ
    rw [hv, hstab_top χ hχ, Subgroup.index_top, RepresentationTheory.ComplexUnitCharacters.finrank_fdRepOfComplexUnitCharacter, mul_one]
  have hdim_free : ∀ (χ : Multiplicative (ZMod N) →* ℂˣ), χ⁻¹ ≠ χ →
      finrank ℂ (V χ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ) →* ℂˣ)) : Type) = 2 := by
    intro χ hχ
    rw [hv, hstab_bot χ hχ, Subgroup.index_bot, RepresentationTheory.ComplexUnitCharacters.finrank_fdRepOfComplexUnitCharacter, mul_one,
      hcardG2]

  let key : (Multiplicative (ZMod N) →* ℂˣ) → ℕ := fun χ => (Fintype.equivFin _ χ).val
  have key_inj : Function.Injective key := fun a b h =>
    (Fintype.equivFin (Multiplicative (ZMod N) →* ℂˣ)).injective (Fin.val_injective h)
  have hinv_inv (χ : Multiplicative (ZMod N) →* ℂˣ) : χ⁻¹⁻¹ = χ := by
    ext a
    simp

  let T := {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹ ∧ key χ < key χ⁻¹}
  haveI : Fintype T := Fintype.ofFinite _

  let toFree : T ⊕ T → {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} :=
    Sum.elim (fun t => ⟨t.1, t.2.1⟩)
      (fun t => ⟨t.1⁻¹, by rw [hinv_inv]; exact t.2.1.symm⟩)
  have htoFree_inj : Function.Injective toFree := by
    rintro (⟨χ, hχ, hk⟩ | ⟨χ, hχ, hk⟩) (⟨χ', hχ', hk'⟩ | ⟨χ', hχ', hk'⟩) hxy <;>
      simp only [toFree, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at hxy
    · exact congrArg Sum.inl (Subtype.ext hxy)
    · exfalso

      have e1 : key χ < key χ⁻¹ := hk
      have e2 : key χ' < key χ'⁻¹ := hk'
      rw [hxy] at e1
      rw [hinv_inv] at e1
      omega
    · exfalso
      have e1 : key χ < key χ⁻¹ := hk
      have e2 : key χ' < key χ'⁻¹ := hk'
      rw [← hxy] at e2
      rw [hinv_inv] at e2
      omega
    · refine congrArg Sum.inr (Subtype.ext ?_)
      exact inv_injective hxy
  have htoFree_surj : Function.Surjective toFree := by
    rintro ⟨χ, hχ⟩
    rcases lt_or_gt_of_ne (fun h => hχ (key_inj h)) with h | h
    · exact ⟨Sum.inl ⟨χ, hχ, h⟩, rfl⟩
    · refine ⟨Sum.inr ⟨χ⁻¹, ?_, ?_⟩, Subtype.ext (inv_inv χ)⟩
      · rw [hinv_inv]; exact hχ.symm
      · rw [hinv_inv]; exact h

  have hTfree : Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} = 2 * Nat.card T := by
    rw [← Nat.card_congr (Equiv.ofBijective toFree ⟨htoFree_inj, htoFree_surj⟩),
      Nat.card_sum, two_mul]
  have hcardT : Nat.card T = (N - Nat.gcd 2 N) / 2 := by
    have hfop := RepresentationTheory.GroupTheory.ZMod.ComplexCharacters.card_non_self_inverse_complex_characters_div_two N
    rw [hTfree, Nat.mul_div_cancel_left _ (by norm_num)] at hfop
    exact hfop

  have rep : ∀ (χ : Multiplicative (ZMod N) →* ℂˣ), χ ≠ χ⁻¹ →
      ∃ t : T, t.1 = χ ∨ t.1 = χ⁻¹ := by
    intro χ hχ
    rcases lt_or_gt_of_ne (fun h => hχ (key_inj h)) with h | h
    · exact ⟨⟨χ, hχ, h⟩, Or.inl rfl⟩
    · exact ⟨⟨χ⁻¹, by rw [hinv_inv]; exact hχ.symm,
        by rw [hinv_inv]; exact h⟩, Or.inr rfl⟩

  let ι := ({χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} × (Multiplicative (ZMod 2) →* ℂˣ)) ⊕ T
  let F : ι → FDRep ℂ (Auxiliary N) :=
    Sum.elim
      (fun x => V x.1.1 (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (x.2.comp (stab x.1.1).subtype)))
      (fun t => V t.1 (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab t.1) →* ℂˣ)))
  have hFsimple : ∀ a : ι, Simple (F a) := by
    rintro (⟨⟨χ, hχ⟩, ρ⟩ | t)
    · exact hi _ _ (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _)
    · exact hi _ _ (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _)
  have hFdim1 : ∀ (x : {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹}
        × (Multiplicative (ZMod 2) →* ℂˣ)),
      finrank ℂ (F (Sum.inl x) : Type) = 1 := by
    rintro ⟨⟨χ, hχ⟩, ρ⟩
    exact hdim_self χ hχ.symm ρ
  have hFdim2 : ∀ (t : T), finrank ℂ (F (Sum.inr t) : Type) = 2 := by
    rintro ⟨χ, hχ, _⟩
    exact hdim_free χ (fun h => hχ h.symm)
  have hFdim : ∀ a : ι, finrank ℂ (F a : Type) = 1 ∨ finrank ℂ (F a : Type) = 2 := by
    rintro (x | t)
    · exact Or.inl (hFdim1 x)
    · exact Or.inr (hFdim2 t)

  have hiso_finrank : ∀ {a b : ι}, Nonempty (F a ≅ F b) →
      finrank ℂ (F a : Type) = finrank ℂ (F b : Type) := by
    rintro a b ⟨α⟩
    have hc := congrFun (FDRep.char_iso α) 1
    rw [FDRep.char_one, FDRep.char_one] at hc
    exact_mod_cast hc

  have hFinj : ∀ a b : ι, Nonempty (F a ≅ F b) → a = b := by
    rintro (⟨⟨χ, hχ⟩, ρ⟩ | ⟨χ, hχ, hk⟩) (⟨⟨χ', hχ'⟩, ρ'⟩ | ⟨χ', hχ', hk'⟩) ⟨α⟩
    ·
      obtain ⟨g, hg, ⟨β⟩⟩ := hii χ χ' _ _
        (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _) (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _) ⟨α⟩
      have hχχ' : χ = χ' := by
        rcases hG2 g with rfl | rfl
        · rw [← hg, hdual_one]
        · rw [← hg, hdual_gen]; exact hχ
      subst hχχ'
      have hcentral : ∀ x : Multiplicative (ZMod 2), g * x = x * g := fun x => mul_comm g x
      have hUiso : Nonempty (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (ρ'.comp (stab χ).subtype) ≅
          RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (ρ.comp (stab χ).subtype)) :=
        ⟨β ≪≫ (hviii χ g hg _ hcentral).some⟩
      have hρρ' : ρ'.comp (stab χ).subtype = ρ.comp (stab χ).subtype :=
        RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter_iso_iff.mp hUiso
      have hρeq : ρ' = ρ := by
        refine MonoidHom.ext fun x => ?_
        have hx : x ∈ stab χ := by rw [hstab_top χ hχ.symm]; exact Subgroup.mem_top x
        have hval := DFunLike.congr_fun hρρ' (⟨x, hx⟩ : ↥(stab χ))
        simpa using hval
      rw [hρeq]
    ·
      exfalso
      have h := hiso_finrank ⟨α⟩
      rw [hFdim1 (⟨χ, hχ⟩, ρ), hFdim2 ⟨χ', hχ', hk'⟩] at h
      exact absurd h (by norm_num)
    ·
      exfalso
      have h := hiso_finrank ⟨α⟩
      rw [hFdim2 ⟨χ, hχ, hk⟩, hFdim1 (⟨χ', hχ'⟩, ρ')] at h
      exact absurd h (by norm_num)
    ·
      obtain ⟨g, hg, -⟩ := hii χ χ' _ _
        (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _) (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _) ⟨α⟩
      have hor : χ' = χ ∨ χ' = χ⁻¹ := by
        rcases hG2 g with rfl | rfl
        · left; rw [← hg, hdual_one]
        · right; rw [← hg, hdual_gen]
      have hχχ' : χ = χ' := by
        rcases hor with h | h
        · exact h.symm
        · exfalso
          have e1 : key χ < key χ⁻¹ := hk
          have e2 : key χ' < key χ'⁻¹ := hk'
          rw [h] at e2
          rw [hinv_inv] at e2
          omega
      subst hχχ'
      rfl

  have hFcomplete : ∀ S : FDRep ℂ (Auxiliary N), Simple S → ∃ a : ι, Nonempty (S ≅ F a) := by
    intro S hS
    obtain ⟨χ, U, hU, hSU⟩ := hiii S hS
    haveI : Simple U := hU
    by_cases hχ : χ = χ⁻¹
    ·
      obtain ⟨ξ, hξ⟩ := RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter U
      let eStab : ↥(stab χ) ≃* Multiplicative (ZMod 2) :=
        (MulEquiv.subgroupCongr (hstab_top χ hχ.symm)).trans Subgroup.topEquiv
      have heStab : ∀ s, eStab s = ((stab χ).subtype s) := fun s => rfl
      refine ⟨Sum.inl (⟨χ, hχ⟩, ξ.comp eStab.symm.toMonoidHom), ?_⟩
      have hρξ : (ξ.comp eStab.symm.toMonoidHom).comp (stab χ).subtype = ξ := by
        refine MonoidHom.ext fun s => ?_
        change ξ (eStab.symm ((stab χ).subtype s)) = ξ s
        rw [← heStab s, MulEquiv.symm_apply_apply]
      have hFeq : F (Sum.inl (⟨χ, hχ⟩, ξ.comp eStab.symm.toMonoidHom))
          = V χ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ) := by
        change V χ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
            ((ξ.comp eStab.symm.toMonoidHom).comp (stab χ).subtype))
          = V χ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ)
        rw [hρξ]
      rw [hFeq]
      exact ⟨hSU.some ≪≫ (hvi χ U (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ) hξ).some⟩
    ·
      obtain ⟨t, htor⟩ := rep χ hχ
      obtain ⟨g, hg⟩ : ∃ g : Multiplicative (ZMod 2), dualSmul g χ = t.1 := by
        rcases htor with h | h
        · exact ⟨1, by rw [hdual_one]; exact h.symm⟩
        · exact ⟨Multiplicative.ofAdd 1, by rw [hdual_gen]; exact h.symm⟩
      haveI : Simple (transport g χ t.1 hg U) := hix χ t.1 U g hg hU
      haveI hsub : Subsingleton ↥(stab t.1) := by
        have hbot : stab t.1 = ⊥ := hstab_bot t.1 (fun e => t.2.1 e.symm)
        rw [hbot]
        exact ⟨fun a b => Subtype.ext (by
          rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
      obtain ⟨ξ, hξ⟩ := RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter (transport g χ t.1 hg U)
      have hξ1 : ξ = 1 := by
        refine MonoidHom.ext fun x => ?_
        rw [Subsingleton.elim x 1]; simp
      rw [hξ1] at hξ
      exact ⟨Sum.inr t, ⟨hSU.some ≪≫ (hvii χ t.1 U g hg).some
        ≪≫ (hvi t.1 (transport g χ t.1 hg U) _ hξ).some⟩⟩

  have hcardGhat : Fintype.card (Multiplicative (ZMod 2) →* ℂˣ) = 2 := by
    rw [← Nat.card_eq_fintype_card, RepresentationTheory.ComplexUnitCharacters.natCard_complexUnitCharacters_eq, hcardG2]
  have hcardSelf : Fintype.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹}
      = Nat.gcd 2 N := by
    rw [← Nat.card_eq_fintype_card, RepresentationTheory.GroupTheory.ZMod.ComplexCharacters.card_self_inverse_complex_characters]
  have hcardT' : Fintype.card T = (N - Nat.gcd 2 N) / 2 := by
    rw [← Nat.card_eq_fintype_card, hcardT]

  have hsum1 : (∑ a : ι, if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0)
      = Fintype.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} * 2 := by
    rw [Fintype.sum_sum_type]
    have hL : ∀ x, (if finrank ℂ (F (Sum.inl x) : Type) = 1 then (1 : ℕ) else 0) = 1 := by
      intro x; rw [if_pos (hFdim1 x)]
    have hR : ∀ t, (if finrank ℂ (F (Sum.inr t) : Type) = 1 then (1 : ℕ) else 0) = 0 := by
      intro t; have : finrank ℂ (F (Sum.inr t) : Type) ≠ 1 := by rw [hFdim2 t]; norm_num
      rw [if_neg this]
    simp only [hL, hR, Finset.sum_const, mul_zero, smul_eq_mul, mul_one, add_zero,
      Finset.card_univ, Fintype.card_prod, hcardGhat]
  have hsum2 : (∑ a : ι, if finrank ℂ (F a : Type) = 2 then (1 : ℕ) else 0)
      = Fintype.card T := by
    rw [Fintype.sum_sum_type]
    have hL : ∀ x, (if finrank ℂ (F (Sum.inl x) : Type) = 2 then (1 : ℕ) else 0) = 0 := by
      intro x; have : finrank ℂ (F (Sum.inl x) : Type) ≠ 2 := by rw [hFdim1 x]; norm_num
      rw [if_neg this]
    have hR : ∀ t, (if finrank ℂ (F (Sum.inr t) : Type) = 2 then (1 : ℕ) else 0) = 1 := by
      intro t; rw [if_pos (hFdim2 t)]
    simp only [hL, hR, Finset.sum_const, mul_zero, smul_eq_mul, mul_one, zero_add,
      Finset.card_univ]

  set e := Fintype.equivFin ι with he
  refine ⟨Fintype.card ι, fun i => F (e.symm i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hFsimple _
  · intro i j hij
    exact e.symm.injective (hFinj _ _ hij)
  · intro S hS
    obtain ⟨a, ha⟩ := hFcomplete S hS
    exact ⟨e a, by simpa only [Equiv.symm_apply_apply] using ha⟩
  · exact fun i => hFdim (e.symm i)
  ·
    intro hpar
    have hg1 : Nat.gcd 2 N = 1 := by rw [Nat.gcd_rec, Nat.odd_iff.mp hpar]; simp
    refine ⟨?_, ?_⟩
    · rw [Finset.card_filter, Equiv.sum_comp e.symm
          (fun a => if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0), hsum1, hcardSelf, hg1]
    · rw [Finset.card_filter, Equiv.sum_comp e.symm
          (fun a => if finrank ℂ (F a : Type) = 2 then (1 : ℕ) else 0), hsum2, hcardT', hg1]
  ·
    intro hpar
    have hg2 : Nat.gcd 2 N = 2 := by rw [Nat.gcd_rec, Nat.even_iff.mp hpar]; simp
    refine ⟨?_, ?_⟩
    · rw [Finset.card_filter, Equiv.sum_comp e.symm
          (fun a => if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0), hsum1, hcardSelf, hg2]
    · rw [Finset.card_filter, Equiv.sum_comp e.symm
          (fun a => if finrank ℂ (F a : Type) = 2 then (1 : ℕ) else 0), hsum2, hcardT', hg2]

open Classical in

/-- Provides simple complex representation representatives of a dihedral group with the displayed dimension and parity-dependent counts. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := primary)]
theorem exists_dihedralSimpleRepresentatives :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (DihedralGroup N)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (DihedralGroup N), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      (∀ i, finrank ℂ (W i : Type) = 1 ∨ finrank ℂ (W i : Type) = 2) ∧
      (Odd N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 2 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 1) / 2) ∧
      (Even N →
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = 4 ∧
        (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 2)).card = (N - 2) / 2) := by
  classical
  obtain ⟨n, V, hSimple, hInj, hComplete, hDim, hOdd, hEven⟩ := exists_auxiliarySimpleRepresentatives N
  obtain ⟨W, hW1, hW2, hW3, hWdim⟩ :=
    RepresentationTheory.FiniteDimensional.Equivalences.exists_simple_representatives_preserving_finrank (dihedralAuxiliaryMulEquiv N) V hSimple hInj hComplete
  have hfilt : ∀ d : ℕ, (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = d)) =
      (Finset.univ.filter (fun i => finrank ℂ (V i : Type) = d)) :=
    fun d => RepresentationTheory.FiniteDimensional.Equivalences.filter_univ_finrank_eq_of_forall_eq hWdim d
  refine ⟨n, W, hW1, hW2, hW3, ?_, ?_, ?_⟩
  ·
    intro i
    rw [hWdim i]; exact hDim i
  ·
    intro hpar
    rw [hfilt, hfilt]; exact hOdd hpar
  · intro hpar
    rw [hfilt, hfilt]; exact hEven hpar

end RepresentationTheory.DihedralAuxiliary
