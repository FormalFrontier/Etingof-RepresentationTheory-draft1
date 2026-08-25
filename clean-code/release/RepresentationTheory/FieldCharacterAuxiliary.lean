/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.AuxiliaryRepresentationIsomorphisms
import RepresentationTheory.ComplexUnitCharacters
import RepresentationTheory.FiniteDimensional.Equivalences
import RepresentationTheory.AffineGroupRepresentations
import RepresentationTheory.Alignment.Attribute

noncomputable section

open CategoryTheory Module

namespace RepresentationTheory.FieldCharacterAuxiliary
variable (K : Type) [Field K] [Fintype K]

/-- Defines the action of field units by multiplicative automorphisms. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
def unitAction : Kˣ →* MulAut (Multiplicative K) :=
  (MulAutMultiplicative K).symm.toMonoidHom.comp (AddAut.mulLeft (R := K))

omit [Fintype K] in
/-- Evaluates the unit action after converting a field element to multiplicative form. -/
@[simp] lemma unitAction_apply (a : Kˣ) (b : K) :
    Multiplicative.toAdd ((unitAction K a) (Multiplicative.ofAdd b)) = (a : K) * b := rfl

/-- An auxiliary type attached to a field. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
abbrev Auxiliary : Type := Multiplicative K ⋊[unitAction K] Kˣ

/-- Transforms a complex-valued multiplicative character using a field unit. -/
def unitCharacterTransform (g : Kˣ) (χ : Multiplicative K →* ℂˣ) : Multiplicative K →* ℂˣ :=
  χ.comp (unitAction K g⁻¹).toMonoidHom

omit [Fintype K] in
/-- Evaluates the unit-induced character transform at a multiplicative field element. -/
@[simp] lemma unitCharacterTransform_apply (g : Kˣ) (χ : Multiplicative K →* ℂˣ) (x : Multiplicative K) :
    unitCharacterTransform K g χ x = χ ((unitAction K g⁻¹) x) := rfl

omit [Fintype K] in

/-- Describes the unit action on a multiplicative field element. -/
@[simp] lemma unitAction_apply_multiplicative (a : Kˣ) (x : Multiplicative K) :
    (unitAction K a) x = Multiplicative.ofAdd ((a : K) * Multiplicative.toAdd x) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  conv_lhs => rw [← ofAdd_toAdd x]
  rw [unitAction_apply]

omit [Fintype K] in

/-- The unit-induced transform preserves the trivial character. -/
@[simp] lemma unitCharacterTransform_one (g : Kˣ) :
    unitCharacterTransform K g (1 : Multiplicative K →* ℂˣ) = 1 := by
  ext x; simp [unitCharacterTransform]

omit [Fintype K] in

private lemma toMonoidHomEquiv_one :
    AddChar.toMonoidHomEquiv (1 : AddChar K ℂˣ) = (1 : Multiplicative K →* ℂˣ) := by
  ext x; simp

omit [Fintype K] in

private lemma toAddChar_ne_one {χ : Multiplicative K →* ℂˣ} (hχ : χ ≠ 1) :
    AddChar.toMonoidHomEquiv.symm χ ≠ (1 : AddChar K ℂˣ) := by
  intro h
  apply hχ
  have := congrArg AddChar.toMonoidHomEquiv h
  rw [Equiv.apply_symm_apply, toMonoidHomEquiv_one] at this
  exact this

omit [Fintype K] in

/-- Expresses the unit-induced character transform as an additive-character shift. -/
lemma unitCharacterTransform_eq_mulShift (g : Kˣ) (χ : Multiplicative K →* ℂˣ) :
    unitCharacterTransform K g χ =
      AddChar.toMonoidHomEquiv
        (AddChar.mulShift (AddChar.toMonoidHomEquiv.symm χ) ((g⁻¹ : Kˣ) : K)) := by
  refine MonoidHom.ext (fun x => ?_)
  rw [unitCharacterTransform_apply, unitAction_apply_multiplicative, AddChar.toMonoidHomEquiv_apply,
    AddChar.mulShift_apply, AddChar.toMonoidHomEquiv_symm_apply]

omit [Fintype K] in

/-- For a nontrivial character, character invariance under the transform is equivalent to a trivial unit. -/
lemma unitCharacterTransform_eq_self_iff (g : Kˣ) {χ : Multiplicative K →* ℂˣ} (hχ : χ ≠ 1) :
    unitCharacterTransform K g χ = χ ↔ g = 1 := by
  have hprim : (AddChar.toMonoidHomEquiv.symm χ).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (toAddChar_ne_one K hχ)
  rw [unitCharacterTransform_eq_mulShift]
  constructor
  · intro h
    have h2 : AddChar.mulShift (AddChar.toMonoidHomEquiv.symm χ) ((g⁻¹ : Kˣ) : K)
        = AddChar.toMonoidHomEquiv.symm χ := by
      apply AddChar.toMonoidHomEquiv.injective
      rw [h, Equiv.apply_symm_apply]
    have h3 : ((g⁻¹ : Kˣ) : K) = 1 :=
      AddChar.to_mulShift_inj_of_isPrimitive hprim
        (by rw [AddChar.mulShift_one]; exact h2)
    rw [Units.val_eq_one] at h3
    exact inv_eq_one.mp h3
  · rintro rfl
    simp only [inv_one, Units.val_one, AddChar.mulShift_one, Equiv.apply_symm_apply]

/-- Any two nontrivial characters over a finite field are related by a unit-induced transform. -/
lemma exists_unitCharacterTransform_eq {χ₁ χ₂ : Multiplicative K →* ℂˣ}
    (h1 : χ₁ ≠ 1) (h2 : χ₂ ≠ 1) : ∃ g : Kˣ, unitCharacterTransform K g χ₁ = χ₂ := by
  classical
  set ψ₁ := AddChar.toMonoidHomEquiv.symm χ₁ with hψ₁
  have hprim : ψ₁.IsPrimitive := AddChar.IsPrimitive.of_ne_one (toAddChar_ne_one K h1)

  let F : K → (Multiplicative K →* ℂˣ) := fun r => AddChar.toMonoidHomEquiv (AddChar.mulShift ψ₁ r)
  have hFinj : Function.Injective F := fun a b hab =>
    AddChar.to_mulShift_inj_of_isPrimitive hprim (AddChar.toMonoidHomEquiv.injective hab)

  haveI : Fintype (Multiplicative K →* ℂˣ) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (Multiplicative K →* ℂˣ) := by
    have := RepresentationTheory.ComplexUnitCharacters.natCard_complexUnitCharacters_eq (G := Multiplicative K)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
    simpa [Fintype.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)] using this.symm
  have hFsurj : Function.Surjective F :=
    ((Fintype.bijective_iff_injective_and_card F).mpr ⟨hFinj, hcard⟩).surjective
  obtain ⟨c, hc⟩ := hFsurj χ₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h2
    rw [← hc]
    simp [F, AddChar.mulShift_zero, toMonoidHomEquiv_one]
  refine ⟨(Ne.isUnit hc0).unit⁻¹, ?_⟩
  rw [unitCharacterTransform_eq_mulShift, ← hψ₁]
  simp only [inv_inv, IsUnit.unit_spec]
  exact hc

open Classical in

/-- For a finite field with more than two elements, supplies pairwise nonisomorphic simple representatives with the displayed dimension counts. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
theorem exists_simpleRepresentatives_of_two_lt_card (hq : 2 < Fintype.card K) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (Auxiliary K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (Auxiliary K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = Fintype.card K ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = Fintype.card K - 1 ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = Fintype.card K - 1)).card = 1 := by
  classical
  haveI : Nonempty Kˣ := ⟨1⟩
  obtain ⟨dualSmul, hdual, stab, hstab, V, transport,
    hi, hii, hiii, hiv, hv, hvi, hvii, hviii, hix⟩ :=
    RepresentationTheory.AuxiliaryRepresentationIsomorphisms.auxiliary_theorem Kˣ (Multiplicative K) (unitAction K)

  have hds : ∀ (g : Kˣ) (χ : Multiplicative K →* ℂˣ), dualSmul g χ = unitCharacterTransform K g χ := by
    intro g χ
    refine MonoidHom.ext fun a => ?_
    rw [hdual g χ a, unitCharacterTransform_apply]

  have hstab_triv : stab (1 : Multiplicative K →* ℂˣ) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact (hstab 1 g).mpr (by rw [hds]; exact unitCharacterTransform_one K g)

  have hstab_ntriv : ∀ {χ : Multiplicative K →* ℂˣ}, χ ≠ 1 → stab χ = ⊥ := by
    intro χ hχ
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hgχ : unitCharacterTransform K g χ = χ := by rw [← hds]; exact (hstab χ g).mp hg
    exact (unitCharacterTransform_eq_self_iff K g hχ).mp hgχ

  have hconj : ∀ h g : Kˣ, h * g * h⁻¹ = g := fun h g => by
    rw [mul_right_comm, mul_inv_cancel, one_mul]
  haveI : Fintype (Multiplicative K →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype (Kˣ →* ℂˣ) := Fintype.ofFinite _

  have hcardHom : Fintype.card (Multiplicative K →* ℂˣ) = Fintype.card K := by
    have h := RepresentationTheory.ComplexUnitCharacters.natCard_complexUnitCharacters_eq (G := Multiplicative K)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    rwa [Fintype.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)] at h

  have hcardDual : Fintype.card (Kˣ →* ℂˣ) = Fintype.card K - 1 := by
    rw [← Nat.card_eq_fintype_card, RepresentationTheory.ComplexUnitCharacters.natCard_complexUnitCharacters_eq,
      Nat.card_eq_fintype_card, Fintype.card_units]

  haveI : Nontrivial (Multiplicative K →* ℂˣ) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hcardHom]; omega
  obtain ⟨χ₀, hχ₀⟩ := exists_ne (1 : Multiplicative K →* ℂˣ)

  set F : (Kˣ →* ℂˣ) ⊕ Unit → FDRep ℂ (Auxiliary K) := fun a =>
    a.elim
      (fun ρ => V (1 : Multiplicative K →* ℂˣ)
        (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)))
      (fun _ => V χ₀ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ))) with hF

  have fixed_char : ∀ (ρ : Kˣ →* ℂˣ) (a : Multiplicative K) (g : Kˣ),
      (V (1 : Multiplicative K →* ℂˣ)
        (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
          (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype))).character ⟨a, g⟩
      = (ρ g : ℂ) := by
    intro ρ a g
    have hSimpleU := RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter
      (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)
    have hmemg : g ∈ stab (1 : Multiplicative K →* ℂˣ) := by
      rw [hstab_triv]; exact Subgroup.mem_top g
    have hmemall : ∀ h : Kˣ, h * g * h⁻¹ ∈ stab (1 : Multiplicative K →* ℂˣ) := by
      intro h; rw [hstab_triv]; exact Subgroup.mem_top _
    have hcard : Fintype.card ↥(stab (1 : Multiplicative K →* ℂˣ)) = Fintype.card Kˣ := by
      rw [hstab_triv]; exact Fintype.card_congr Subgroup.topEquiv.toEquiv
    have hterm : ∀ h : Kˣ,
        (if hh : h * g * h⁻¹ ∈ stab (1 : Multiplicative K →* ℂˣ)
          then ((1 : Multiplicative K →* ℂˣ)
                ((unitAction K h : MulAut (Multiplicative K)) a) : ℂ)
              * (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
                  (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)).character
                  ⟨h * g * h⁻¹, hh⟩
          else 0)
        = (ρ g : ℂ) := by
      intro h
      rw [dif_pos (hmemall h),
        show (⟨h * g * h⁻¹, hmemall h⟩ : ↥(stab (1 : Multiplicative K →* ℂˣ))) = ⟨g, hmemg⟩ from
          Subtype.ext (hconj h g),
        RepresentationTheory.ComplexUnitCharacters.character_fdRepOfComplexUnitCharacter, MonoidHom.one_apply, Units.val_one, one_mul]
      rfl
    rw [hiv 1 _ hSimpleU a g, Finset.sum_congr rfl (fun h _ => hterm h),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
      inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

  have hdim_inl : ∀ ρ : Kˣ →* ℂˣ, finrank ℂ (F (Sum.inl ρ) : Type) = 1 := by
    intro ρ
    change finrank ℂ (V (1 : Multiplicative K →* ℂˣ)
      (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
        (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) : Type) = 1
    rw [hv, RepresentationTheory.ComplexUnitCharacters.finrank_fdRepOfComplexUnitCharacter, mul_one, hstab_triv, Subgroup.index_top]
  have hdim_inr : finrank ℂ (F (Sum.inr () : (Kˣ →* ℂˣ) ⊕ Unit) : Type) = Fintype.card K - 1 := by
    change finrank ℂ (V χ₀ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
      (1 : ↥(stab χ₀) →* ℂˣ)) : Type) = Fintype.card K - 1
    rw [hv, RepresentationTheory.ComplexUnitCharacters.finrank_fdRepOfComplexUnitCharacter, mul_one, hstab_ntriv hχ₀,
      Subgroup.index_bot, Nat.card_eq_fintype_card, Fintype.card_units]

  have hFsimple : ∀ a, Simple (F a) := by
    rintro (ρ | _)
    · exact hi 1 _ (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _)
    · exact hi χ₀ _ (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _)

  have hFinj : ∀ a b, Nonempty (F a ≅ F b) → a = b := by
    rintro (ρ₁ | _) (ρ₂ | _) ⟨α⟩
    · 

      have hchar := FDRep.char_iso α
      have hρ : ρ₁ = ρ₂ := by
        refine MonoidHom.ext fun g => ?_
        have h := congrFun hchar ⟨(1 : Multiplicative K), g⟩
        rw [show F (Sum.inl ρ₁) = V (1 : Multiplicative K →* ℂˣ)
            (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
              (ρ₁.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
          show F (Sum.inl ρ₂) = V (1 : Multiplicative K →* ℂˣ)
            (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
              (ρ₂.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
          fixed_char ρ₁ 1 g, fixed_char ρ₂ 1 g] at h
        exact Units.ext h
      rw [hρ]
    · 

      exfalso
      have h := congrFun (FDRep.char_iso α) 1
      rw [FDRep.char_one, FDRep.char_one, hdim_inl ρ₁, hdim_inr, Nat.cast_inj] at h
      omega
    · 

      exfalso
      have h := congrFun (FDRep.char_iso α) 1
      rw [FDRep.char_one, FDRep.char_one, hdim_inl ρ₂, hdim_inr, Nat.cast_inj] at h
      omega
    · 

      exact congrArg Sum.inr (Subsingleton.elim _ _)

  have hFcomplete : ∀ S : FDRep ℂ (Auxiliary K), Simple S → ∃ a, Nonempty (S ≅ F a) := by
    intro S hS
    obtain ⟨χ, U, hU, hSU⟩ := hiii S hS
    haveI : Simple U := hU
    by_cases hχ : χ = 1
    · 

      subst hχ
      obtain ⟨ξ, hξ⟩ := RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter U
      let eStab : ↥(stab (1 : Multiplicative K →* ℂˣ)) ≃* Kˣ :=
        (MulEquiv.subgroupCongr hstab_triv).trans Subgroup.topEquiv
      have heStab : ∀ s, eStab s = ((stab (1 : Multiplicative K →* ℂˣ)).subtype s) := fun _ => rfl
      refine ⟨Sum.inl (ξ.comp eStab.symm.toMonoidHom), ?_⟩
      have hρξ : (ξ.comp eStab.symm.toMonoidHom).comp
          (stab (1 : Multiplicative K →* ℂˣ)).subtype = ξ := by
        refine MonoidHom.ext fun s => ?_
        change ξ (eStab.symm ((stab (1 : Multiplicative K →* ℂˣ)).subtype s)) = ξ s
        rw [← heStab s, MulEquiv.symm_apply_apply]
      have hFeq : F (Sum.inl (ξ.comp eStab.symm.toMonoidHom))
          = V (1 : Multiplicative K →* ℂˣ) (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ) := by
        change V (1 : Multiplicative K →* ℂˣ) (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
            ((ξ.comp eStab.symm.toMonoidHom).comp (stab (1 : Multiplicative K →* ℂˣ)).subtype))
          = V (1 : Multiplicative K →* ℂˣ) (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ)
        rw [hρξ]
      rw [hFeq]
      exact ⟨hSU.some ≪≫ (hvi 1 U (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ) hξ).some⟩
    · 

      refine ⟨Sum.inr (), ?_⟩
      obtain ⟨g, hg⟩ := exists_unitCharacterTransform_eq K hχ₀ hχ
      have hg' : dualSmul g χ₀ = χ := by rw [hds]; exact hg
      haveI : Subsingleton ↥(stab χ) := by
        rw [hstab_ntriv hχ]
        exact ⟨fun a b => Subtype.ext
          (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩

      obtain ⟨ξ, hξ⟩ := RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter U
      have hξ1 : ξ = 1 := by
        refine MonoidHom.ext fun x => ?_; rw [Subsingleton.elim x 1]; simp
      rw [hξ1] at hξ

      haveI : Simple (transport g χ₀ χ hg' (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
          (1 : ↥(stab χ₀) →* ℂˣ))) :=
        hix χ₀ χ _ g hg' (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _)
      obtain ⟨ζ, hζ⟩ := RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter
        (transport g χ₀ χ hg' (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ)))
      have hζ1 : ζ = 1 := by
        refine MonoidHom.ext fun x => ?_; rw [Subsingleton.elim x 1]; simp
      rw [hζ1] at hζ

      have step1 : Nonempty (V χ₀ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ))
          ≅ V χ (transport g χ₀ χ hg'
              (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ)))) :=
        hvii χ₀ χ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter 1) g hg'
      have step2 : Nonempty (V χ (transport g χ₀ χ hg'
            (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ)))
          ≅ V χ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ) →* ℂˣ))) :=
        hvi χ _ _ hζ
      have step3 : Nonempty (V χ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ) →* ℂˣ))
          ≅ V χ U) :=
        hvi χ _ _ ⟨hξ.some.symm⟩
      change Nonempty (S ≅ V χ₀ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ)))
      exact ⟨hSU.some ≪≫ step3.some.symm ≪≫ step2.some.symm ≪≫ step1.some.symm⟩

  set e := Fintype.equivFin ((Kˣ →* ℂˣ) ⊕ Unit) with he
  refine ⟨Fintype.card ((Kˣ →* ℂˣ) ⊕ Unit), fun i => F (e.symm i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hFsimple _
  · intro i j hij; exact e.symm.injective (hFinj _ _ hij)
  · intro S hS
    obtain ⟨a, ha⟩ := hFcomplete S hS
    exact ⟨e a, by simpa only [Equiv.symm_apply_apply] using ha⟩
  · rw [Fintype.card_sum, Fintype.card_unit, hcardDual]; omega
  · 

    have hL1 : ∀ ρ : Kˣ →* ℂˣ,
        (if finrank ℂ (F (Sum.inl ρ) : Type) = 1 then (1 : ℕ) else 0) = 1 :=
      fun ρ => if_pos (hdim_inl ρ)
    have hR1 : ∀ u : Unit,
        (if finrank ℂ (F (Sum.inr u) : Type) = 1 then (1 : ℕ) else 0) = 0 := by
      rintro ⟨⟩; exact if_neg (by rw [hdim_inr]; omega)
    rw [Finset.card_filter,
      Equiv.sum_comp e.symm (fun a => if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0),
      Fintype.sum_sum_type]
    simp only [hL1, hR1, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      mul_zero, add_zero, hcardDual]
  · 

    have hLp : ∀ ρ : Kˣ →* ℂˣ,
        (if finrank ℂ (F (Sum.inl ρ) : Type) = Fintype.card K - 1 then (1 : ℕ) else 0) = 0 :=
      fun ρ => if_neg (by rw [hdim_inl ρ]; omega)
    have hRp : ∀ u : Unit,
        (if finrank ℂ (F (Sum.inr u) : Type) = Fintype.card K - 1 then (1 : ℕ) else 0) = 1 := by
      rintro ⟨⟩; exact if_pos hdim_inr
    rw [Finset.card_filter,
      Equiv.sum_comp e.symm
        (fun a => if finrank ℂ (F a : Type) = Fintype.card K - 1 then (1 : ℕ) else 0),
      Fintype.sum_sum_type]
    simp only [hLp, hRp, Finset.sum_const, Finset.card_univ, Fintype.card_unit, smul_eq_mul,
      mul_one, mul_zero, zero_add]

open Classical in

/-- Provides two one-dimensional simple representatives when the field has cardinality two. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
theorem exists_simpleRepresentatives_of_card_eq_two (hq : Fintype.card K = 2) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (Auxiliary K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (Auxiliary K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = 2 ∧
      (∀ i, finrank ℂ (W i : Type) = 1) := by
  classical
  haveI : Nonempty Kˣ := ⟨1⟩
  obtain ⟨dualSmul, hdual, stab, hstab, V, transport,
    hi, hii, hiii, hiv, hv, hvi, hvii, hviii, hix⟩ :=
    RepresentationTheory.AuxiliaryRepresentationIsomorphisms.auxiliary_theorem Kˣ (Multiplicative K) (unitAction K)

  have hds : ∀ (g : Kˣ) (χ : Multiplicative K →* ℂˣ), dualSmul g χ = unitCharacterTransform K g χ := by
    intro g χ
    refine MonoidHom.ext fun a => ?_
    rw [hdual g χ a, unitCharacterTransform_apply]

  have hstab_triv : stab (1 : Multiplicative K →* ℂˣ) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact (hstab 1 g).mpr (by rw [hds]; exact unitCharacterTransform_one K g)

  have hstab_ntriv : ∀ {χ : Multiplicative K →* ℂˣ}, χ ≠ 1 → stab χ = ⊥ := by
    intro χ hχ
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hgχ : unitCharacterTransform K g χ = χ := by rw [← hds]; exact (hstab χ g).mp hg
    exact (unitCharacterTransform_eq_self_iff K g hχ).mp hgχ

  have hconj : ∀ h g : Kˣ, h * g * h⁻¹ = g := fun h g => by
    rw [mul_right_comm, mul_inv_cancel, one_mul]

  have hcardUnits : Fintype.card Kˣ = 1 := by rw [Fintype.card_units, hq]
  haveI : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  haveI : Unique Kˣ := ⟨⟨1⟩, fun a => Subsingleton.elim a 1⟩
  haveI : Fintype (Multiplicative K →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype (Kˣ →* ℂˣ) := Fintype.ofFinite _

  have hcardHom : Fintype.card (Multiplicative K →* ℂˣ) = Fintype.card K := by
    have h := RepresentationTheory.ComplexUnitCharacters.natCard_complexUnitCharacters_eq (G := Multiplicative K)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    rwa [Fintype.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)] at h

  have hcardDual : Fintype.card (Kˣ →* ℂˣ) = Fintype.card K - 1 := by
    rw [← Nat.card_eq_fintype_card, RepresentationTheory.ComplexUnitCharacters.natCard_complexUnitCharacters_eq,
      Nat.card_eq_fintype_card, Fintype.card_units]

  haveI : Nontrivial (Multiplicative K →* ℂˣ) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hcardHom]; omega
  obtain ⟨χ₀, hχ₀⟩ := exists_ne (1 : Multiplicative K →* ℂˣ)

  set F : (Kˣ →* ℂˣ) ⊕ Unit → FDRep ℂ (Auxiliary K) := fun a =>
    a.elim
      (fun ρ => V (1 : Multiplicative K →* ℂˣ)
        (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)))
      (fun _ => V χ₀ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ))) with hF

  have fixed_char : ∀ (ρ : Kˣ →* ℂˣ) (a : Multiplicative K) (g : Kˣ),
      (V (1 : Multiplicative K →* ℂˣ)
        (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
          (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype))).character ⟨a, g⟩
      = (ρ g : ℂ) := by
    intro ρ a g
    have hSimpleU := RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter
      (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)
    have hmemg : g ∈ stab (1 : Multiplicative K →* ℂˣ) := by
      rw [hstab_triv]; exact Subgroup.mem_top g
    have hmemall : ∀ h : Kˣ, h * g * h⁻¹ ∈ stab (1 : Multiplicative K →* ℂˣ) := by
      intro h; rw [hstab_triv]; exact Subgroup.mem_top _
    have hcard : Fintype.card ↥(stab (1 : Multiplicative K →* ℂˣ)) = Fintype.card Kˣ := by
      rw [hstab_triv]; exact Fintype.card_congr Subgroup.topEquiv.toEquiv
    have hterm : ∀ h : Kˣ,
        (if hh : h * g * h⁻¹ ∈ stab (1 : Multiplicative K →* ℂˣ)
          then ((1 : Multiplicative K →* ℂˣ)
                ((unitAction K h : MulAut (Multiplicative K)) a) : ℂ)
              * (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
                  (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)).character
                  ⟨h * g * h⁻¹, hh⟩
          else 0)
        = (ρ g : ℂ) := by
      intro h
      rw [dif_pos (hmemall h),
        show (⟨h * g * h⁻¹, hmemall h⟩ : ↥(stab (1 : Multiplicative K →* ℂˣ))) = ⟨g, hmemg⟩ from
          Subtype.ext (hconj h g),
        RepresentationTheory.ComplexUnitCharacters.character_fdRepOfComplexUnitCharacter, MonoidHom.one_apply, Units.val_one, one_mul]
      rfl
    rw [hiv 1 _ hSimpleU a g, Finset.sum_congr rfl (fun h _ => hterm h),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
      inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

  have free_char : ∀ a : Multiplicative K,
      (V χ₀ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ))).character ⟨a, 1⟩
      = (χ₀ a : ℂ) := by
    intro a
    have hSimpleU := RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ)
    have hcardstab : Fintype.card ↥(stab χ₀) = 1 := by
      have hle : Fintype.card ↥(stab χ₀) ≤ Fintype.card Kˣ :=
        Fintype.card_le_of_injective _ Subtype.val_injective
      have hpos : 0 < Fintype.card ↥(stab χ₀) := Fintype.card_pos
      omega
    have hh1 : ∀ h : Kˣ, h * 1 * h⁻¹ = 1 := fun h => by rw [mul_one, mul_inv_cancel]

    have hterm : ∀ h : Kˣ,
        (if hh : h * 1 * h⁻¹ ∈ stab χ₀
          then (χ₀ ((unitAction K h : MulAut (Multiplicative K)) a) : ℂ)
            * (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ)).character ⟨h * 1 * h⁻¹, hh⟩
          else 0)
        = (χ₀ a : ℂ) := by
      intro h
      rw [dif_pos (by rw [hh1 h]; exact one_mem _),
        show (⟨h * 1 * h⁻¹, by rw [hh1 h]; exact one_mem _⟩ : ↥(stab χ₀)) = 1 from
          Subtype.ext (by simp ),
        RepresentationTheory.ComplexUnitCharacters.character_fdRepOfComplexUnitCharacter, MonoidHom.one_apply, Units.val_one, mul_one,
        Subsingleton.elim h 1, map_one]
      rfl
    rw [hiv χ₀ _ hSimpleU a 1, Finset.sum_congr rfl (fun h _ => hterm h),
      Finset.sum_const, Finset.card_univ, hcardUnits, one_smul,
      hcardstab, Nat.cast_one, inv_one, one_mul]

  have hdim_inl : ∀ ρ : Kˣ →* ℂˣ, finrank ℂ (F (Sum.inl ρ) : Type) = 1 := by
    intro ρ
    change finrank ℂ (V (1 : Multiplicative K →* ℂˣ)
      (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
        (ρ.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) : Type) = 1
    rw [hv, RepresentationTheory.ComplexUnitCharacters.finrank_fdRepOfComplexUnitCharacter, mul_one, hstab_triv, Subgroup.index_top]
  have hdim_inr : finrank ℂ (F (Sum.inr () : (Kˣ →* ℂˣ) ⊕ Unit) : Type) = 1 := by
    change finrank ℂ (V χ₀ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
      (1 : ↥(stab χ₀) →* ℂˣ)) : Type) = 1
    rw [hv, RepresentationTheory.ComplexUnitCharacters.finrank_fdRepOfComplexUnitCharacter, mul_one, hstab_ntriv hχ₀,
      Subgroup.index_bot, Nat.card_eq_fintype_card, hcardUnits]

  have hFsimple : ∀ a, Simple (F a) := by
    rintro (ρ | _)
    · exact hi 1 _ (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _)
    · exact hi χ₀ _ (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _)

  have hFinj : ∀ a b, Nonempty (F a ≅ F b) → a = b := by

    obtain ⟨a₀, ha₀⟩ := DFunLike.ne_iff.mp hχ₀
    rw [MonoidHom.one_apply] at ha₀
    have ha₀' : (χ₀ a₀ : ℂ) ≠ 1 := fun h => ha₀ (Units.ext h)
    rintro (ρ₁ | _) (ρ₂ | _) ⟨α⟩
    · 

      have hchar := FDRep.char_iso α
      have hρ : ρ₁ = ρ₂ := by
        refine MonoidHom.ext fun g => ?_
        have h := congrFun hchar ⟨(1 : Multiplicative K), g⟩
        rw [show F (Sum.inl ρ₁) = V (1 : Multiplicative K →* ℂˣ)
            (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
              (ρ₁.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
          show F (Sum.inl ρ₂) = V (1 : Multiplicative K →* ℂˣ)
            (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
              (ρ₂.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
          fixed_char ρ₁ 1 g, fixed_char ρ₂ 1 g] at h
        exact Units.ext h
      rw [hρ]
    · 

      exfalso
      have h := congrFun (FDRep.char_iso α) ⟨a₀, 1⟩
      rw [show F (Sum.inl ρ₁) = V (1 : Multiplicative K →* ℂˣ)
          (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
            (ρ₁.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
        show F (Sum.inr ()) = V χ₀ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
            (1 : ↥(stab χ₀) →* ℂˣ)) from rfl,
        fixed_char ρ₁ a₀ 1, free_char a₀, map_one, Units.val_one] at h
      exact ha₀' h.symm
    · 

      exfalso
      have h := congrFun (FDRep.char_iso α) ⟨a₀, 1⟩
      rw [show F (Sum.inl ρ₂) = V (1 : Multiplicative K →* ℂˣ)
          (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
            (ρ₂.comp (stab (1 : Multiplicative K →* ℂˣ)).subtype)) from rfl,
        show F (Sum.inr ()) = V χ₀ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
            (1 : ↥(stab χ₀) →* ℂˣ)) from rfl,
        fixed_char ρ₂ a₀ 1, free_char a₀, map_one, Units.val_one] at h
      exact ha₀' h
    · 

      exact congrArg Sum.inr (Subsingleton.elim _ _)

  have hFcomplete : ∀ S : FDRep ℂ (Auxiliary K), Simple S → ∃ a, Nonempty (S ≅ F a) := by
    intro S hS
    obtain ⟨χ, U, hU, hSU⟩ := hiii S hS
    haveI : Simple U := hU
    by_cases hχ : χ = 1
    · 

      subst hχ
      obtain ⟨ξ, hξ⟩ := RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter U
      let eStab : ↥(stab (1 : Multiplicative K →* ℂˣ)) ≃* Kˣ :=
        (MulEquiv.subgroupCongr hstab_triv).trans Subgroup.topEquiv
      have heStab : ∀ s, eStab s = ((stab (1 : Multiplicative K →* ℂˣ)).subtype s) := fun _ => rfl
      refine ⟨Sum.inl (ξ.comp eStab.symm.toMonoidHom), ?_⟩
      have hρξ : (ξ.comp eStab.symm.toMonoidHom).comp
          (stab (1 : Multiplicative K →* ℂˣ)).subtype = ξ := by
        refine MonoidHom.ext fun s => ?_
        change ξ (eStab.symm ((stab (1 : Multiplicative K →* ℂˣ)).subtype s)) = ξ s
        rw [← heStab s, MulEquiv.symm_apply_apply]
      have hFeq : F (Sum.inl (ξ.comp eStab.symm.toMonoidHom))
          = V (1 : Multiplicative K →* ℂˣ) (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ) := by
        change V (1 : Multiplicative K →* ℂˣ) (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
            ((ξ.comp eStab.symm.toMonoidHom).comp (stab (1 : Multiplicative K →* ℂˣ)).subtype))
          = V (1 : Multiplicative K →* ℂˣ) (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ)
        rw [hρξ]
      rw [hFeq]
      exact ⟨hSU.some ≪≫ (hvi 1 U (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ) hξ).some⟩
    · 

      refine ⟨Sum.inr (), ?_⟩
      obtain ⟨g, hg⟩ := exists_unitCharacterTransform_eq K hχ₀ hχ
      have hg' : dualSmul g χ₀ = χ := by rw [hds]; exact hg
      haveI : Subsingleton ↥(stab χ) := by
        rw [hstab_ntriv hχ]
        exact ⟨fun a b => Subtype.ext
          (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
      obtain ⟨ξ, hξ⟩ := RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter U
      have hξ1 : ξ = 1 := by
        refine MonoidHom.ext fun x => ?_; rw [Subsingleton.elim x 1]; simp
      rw [hξ1] at hξ
      haveI : Simple (transport g χ₀ χ hg' (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
          (1 : ↥(stab χ₀) →* ℂˣ))) :=
        hix χ₀ χ _ g hg' (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _)
      obtain ⟨ζ, hζ⟩ := RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter
        (transport g χ₀ χ hg' (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ)))
      have hζ1 : ζ = 1 := by
        refine MonoidHom.ext fun x => ?_; rw [Subsingleton.elim x 1]; simp
      rw [hζ1] at hζ
      have step1 : Nonempty (V χ₀ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ))
          ≅ V χ (transport g χ₀ χ hg'
              (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ)))) :=
        hvii χ₀ χ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter 1) g hg'
      have step2 : Nonempty (V χ (transport g χ₀ χ hg'
            (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ)))
          ≅ V χ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ) →* ℂˣ))) :=
        hvi χ _ _ hζ
      have step3 : Nonempty (V χ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ) →* ℂˣ))
          ≅ V χ U) :=
        hvi χ _ _ ⟨hξ.some.symm⟩
      change Nonempty (S ≅ V χ₀ (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab χ₀) →* ℂˣ)))
      exact ⟨hSU.some ≪≫ step3.some.symm ≪≫ step2.some.symm ≪≫ step1.some.symm⟩

  set e := Fintype.equivFin ((Kˣ →* ℂˣ) ⊕ Unit) with he
  refine ⟨Fintype.card ((Kˣ →* ℂˣ) ⊕ Unit), fun i => F (e.symm i), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hFsimple _
  · intro i j hij; exact e.symm.injective (hFinj _ _ hij)
  · intro S hS
    obtain ⟨a, ha⟩ := hFcomplete S hS
    exact ⟨e a, by simpa only [Equiv.symm_apply_apply] using ha⟩
  · rw [Fintype.card_sum, Fintype.card_unit, hcardDual, hq]
  · 

    have hall : ∀ a, finrank ℂ (F a : Type) = 1 := by
      rintro (ρ | ⟨⟩)
      · exact hdim_inl ρ
      · exact hdim_inr
    exact fun i => hall (e.symm i)

/-- Constructs a multiplicative equivalence to an auxiliary field-dependent type. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
def auxiliaryMulEquiv : RepresentationTheory.AffineGroupRepresentations.AffineGroup K ≃* Auxiliary K where
  toFun g := ⟨Multiplicative.ofAdd g.translationPart, g.linearPart⟩
  invFun y := ⟨y.right, Multiplicative.toAdd y.left⟩
  left_inv g := rfl
  right_inv y := rfl
  map_mul' g h := by
    refine SemidirectProduct.ext ?_ rfl
    change Multiplicative.ofAdd ((g.linearPart : K) * h.translationPart + g.translationPart)
      = Multiplicative.ofAdd g.translationPart * (unitAction K g.linearPart) (Multiplicative.ofAdd h.translationPart)
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_mul, toAdd_ofAdd, unitAction_apply]
    exact add_comm _ _

omit [Fintype K] in
/-- Describes the value of the auxiliary multiplicative equivalence. -/
@[simp] lemma auxiliaryMulEquiv_apply (g : RepresentationTheory.AffineGroupRepresentations.AffineGroup K) :
    auxiliaryMulEquiv K g = ⟨Multiplicative.ofAdd g.translationPart, g.linearPart⟩ := rfl

open Classical in

/-- For a finite field with more than two elements, provides simple representation representatives and the displayed dimension counts for an auxiliary group. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
theorem exists_auxiliarySimpleRepresentatives_of_two_lt_card (hq : 2 < Fintype.card K) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (RepresentationTheory.AffineGroupRepresentations.AffineGroup K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (RepresentationTheory.AffineGroupRepresentations.AffineGroup K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = Fintype.card K ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = Fintype.card K - 1 ∧
      (Finset.univ.filter
        (fun i => finrank ℂ (W i : Type) = Fintype.card K - 1)).card = 1 := by
  classical
  obtain ⟨n, V, hSimple, hInj, hComplete, hn, hcard1, hcardq⟩ := exists_simpleRepresentatives_of_two_lt_card K hq
  obtain ⟨W, hW1, hW2, hW3, hWdim⟩ :=
    RepresentationTheory.FiniteDimensional.Equivalences.exists_simple_representatives_preserving_finrank (auxiliaryMulEquiv K) V hSimple hInj hComplete
  have hfilt : ∀ d : ℕ, (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = d)) =
      (Finset.univ.filter (fun i => finrank ℂ (V i : Type) = d)) :=
    fun d => RepresentationTheory.FiniteDimensional.Equivalences.filter_univ_finrank_eq_of_forall_eq hWdim d
  refine ⟨n, W, hW1, hW2, hW3, hn, ?_, ?_⟩
  · rw [hfilt]; exact hcard1
  · rw [hfilt]; exact hcardq

open Classical in

/-- Provides two one-dimensional simple representatives for an auxiliary group when the field has cardinality two. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
theorem exists_auxiliarySimpleRepresentatives_of_card_eq_two (hq : Fintype.card K = 2) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (RepresentationTheory.AffineGroupRepresentations.AffineGroup K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (RepresentationTheory.AffineGroupRepresentations.AffineGroup K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = 2 ∧
      (∀ i, finrank ℂ (W i : Type) = 1) := by
  classical
  obtain ⟨n, V, hSimple, hInj, hComplete, hn, hdim⟩ := exists_simpleRepresentatives_of_card_eq_two K hq
  obtain ⟨W, hW1, hW2, hW3, hWdim⟩ :=
    RepresentationTheory.FiniteDimensional.Equivalences.exists_simple_representatives_preserving_finrank (auxiliaryMulEquiv K) V hSimple hInj hComplete
  exact ⟨n, W, hW1, hW2, hW3, hn, fun i => by rw [hWdim i]; exact hdim i⟩

/-- Defines an auxiliary finite-dimensional complex representation for a finite field. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
def auxiliaryRepresentation : FDRep ℂ (RepresentationTheory.AffineGroupRepresentations.AffineGroup K) :=
  FDRep.of (RepresentationTheory.AffineGroupRepresentations.augmentationSubrepresentation (K := K)).toRepresentation

/-- Computes the complex dimension of an auxiliary representation. -/
lemma auxiliaryRepresentation_finrank :
    finrank ℂ (auxiliaryRepresentation K : Type) = Fintype.card K - 1 :=
  RepresentationTheory.AffineGroupRepresentations.cardinalityFormula_011444 (K := K)

/-- The auxiliary finite-dimensional representation is simple. -/
lemma auxiliaryRepresentation_simple : Simple (auxiliaryRepresentation K) :=
  haveI := RepresentationTheory.AffineGroupRepresentations.simpleRepresentation_011266 (K := K) Fintype.one_lt_card
  RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule _

open Classical in

/-- For a finite field with more than two elements, provides simple representatives with the displayed character and dimension classification. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
theorem exists_classifiedAuxiliarySimpleRepresentatives_of_two_lt_card (hq : 2 < Fintype.card K) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (RepresentationTheory.AffineGroupRepresentations.AffineGroup K)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (RepresentationTheory.AffineGroupRepresentations.AffineGroup K), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = Fintype.card K ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = Fintype.card K - 1 ∧
      (Finset.univ.filter
        (fun i => finrank ℂ (W i : Type) = Fintype.card K - 1)).card = 1 ∧
      (∀ i, finrank ℂ (W i : Type) = 1 → ∃ χ : RepresentationTheory.AffineGroupRepresentations.AffineGroup K →* ℂˣ,
        Nonempty (W i ≅ FDRep.of (RepresentationTheory.AffineGroupRepresentations.characterRepresentation χ))) ∧
      (∀ i, finrank ℂ (W i : Type) = Fintype.card K - 1 →
        Nonempty (W i ≅ auxiliaryRepresentation K)) ∧
      (∀ χ : RepresentationTheory.AffineGroupRepresentations.AffineGroup K →* ℂˣ,
        ∃ i, Nonempty (FDRep.of (RepresentationTheory.AffineGroupRepresentations.characterRepresentation χ) ≅ W i)) ∧
      (∃ i, Nonempty (auxiliaryRepresentation K ≅ W i)) := by
  classical
  obtain ⟨n, W, hSimple, hInj, hComplete, hn, hcard1, hcardq⟩ := exists_auxiliarySimpleRepresentatives_of_two_lt_card K hq
  refine ⟨n, W, hSimple, hInj, hComplete, hn, hcard1, hcardq, ?_, ?_, ?_, ?_⟩
  · 

    intro i hi
    obtain ⟨ξ, hξ⟩ := RepresentationTheory.FiniteDimensional.Equivalences.exists_iso_to_representation_of_finrank_eq_one (W i) hi
    exact ⟨ξ, hξ⟩
  · 

    intro i hi
    haveI := auxiliaryRepresentation_simple K
    obtain ⟨j, hj⟩ := hComplete (auxiliaryRepresentation K) inferInstance
    have hjdim : finrank ℂ (W j : Type) = Fintype.card K - 1 := by
      rw [← LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hj.some)]
      exact auxiliaryRepresentation_finrank K

    have hij : i = j := by
      have hmem : ∀ l : Fin n, finrank ℂ (W l : Type) = Fintype.card K - 1 →
          l ∈ Finset.univ.filter (fun l => finrank ℂ (W l : Type) = Fintype.card K - 1) :=
        fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩
      exact Finset.card_le_one.mp (le_of_eq hcardq) i (hmem i hi) j (hmem j hjdim)
    exact ⟨hij ▸ hj.some.symm⟩
  · 

    intro χ
    haveI : Simple (FDRep.of (RepresentationTheory.AffineGroupRepresentations.characterRepresentation χ)) := RepresentationTheory.AffineGroupRepresentations.simpleRepresentation_011303 χ
    exact hComplete _ inferInstance
  · 

    haveI := auxiliaryRepresentation_simple K
    exact hComplete _ inferInstance

end RepresentationTheory.FieldCharacterAuxiliary
