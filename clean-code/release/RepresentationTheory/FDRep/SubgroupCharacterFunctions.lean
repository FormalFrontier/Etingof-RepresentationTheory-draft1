/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib

/-!
# Function-space representations from subgroup characters

This file constructs a finite-dimensional representation on a covariance submodule of
complex-valued functions on a finite group. It also develops an averaging projection, computes
the corresponding trace, and relates characters transformed by subgroup normalizer elements.
-/

noncomputable section

namespace RepresentationTheory.FDRep.SubgroupCharacterFunctions

open Finset

variable {G : Type} [Group G] (H : Subgroup G) (lam : ↥H →* ℂˣ)

/-- A complex submodule of functions on a group associated with a subgroup character. -/
def subgroupCharacterFunctionSubmodule : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ (h : ↥H) (g : G), f (h.val * g) = (lam h : ℂ) * f g}
  add_mem' {f f'} hf hf' := by
    intro h g; simp only [Pi.add_apply]; rw [hf h g, hf' h g, mul_add]
  zero_mem' := by intro h g; simp
  smul_mem' c f hf := by
    intro h g; simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf h g, mul_left_comm]

/-- A function belongs to the subgroup-character submodule exactly when left multiplication by a
subgroup element scales it by the character value. -/
lemma mem_subgroupCharacterFunctionSubmodule_iff (f : G → ℂ) :
    f ∈ subgroupCharacterFunctionSubmodule H lam ↔
      ∀ (h : ↥H) (g : G), f (h.val * g) = (lam h : ℂ) * f g :=
  Iff.rfl

/-- Right translation by a group element as a complex-linear map on functions on the group. -/
def rightTranslationLinearMap (a : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := fun g => f (g * a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Right translation sends a function to its evaluation after right multiplication by the
translating element. -/
@[simp]
lemma rightTranslationLinearMap_apply (a : G) (f : G → ℂ) (g : G) :
    rightTranslationLinearMap a f g = f (g * a) := rfl

/-- The subgroup-character function submodule is stable under every right translation. -/
lemma rightTranslationLinearMap_mem {f : G → ℂ}
    (hf : f ∈ subgroupCharacterFunctionSubmodule H lam) (a : G) :
    rightTranslationLinearMap a f ∈ subgroupCharacterFunctionSubmodule H lam := by
  intro h g
  change f (h.val * g * a) = (lam h : ℂ) * f (g * a)
  rw [mul_assoc]; exact hf h (g * a)

/-- A complex representation of the group on the subgroup-character function submodule. -/
def subgroupCharacterFunctionRepresentation :
    Representation ℂ G (subgroupCharacterFunctionSubmodule H lam) where
  toFun a :=
    { toFun := fun f =>
        ⟨rightTranslationLinearMap a f.val, rightTranslationLinearMap_mem H lam f.2 a⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  map_one' := by
    apply LinearMap.ext; intro f
    exact Subtype.ext (funext fun g => congr_arg f.val (mul_one g))
  map_mul' a b := by
    apply LinearMap.ext; intro f
    exact Subtype.ext (funext fun g => congr_arg f.val (mul_assoc g a b).symm)

/-- The representation action evaluates a function after right multiplication of its argument. -/
@[simp]
lemma subgroupCharacterFunctionRepresentation_apply (a : G)
    (f : ↥(subgroupCharacterFunctionSubmodule H lam)) (g : G) :
    ((subgroupCharacterFunctionRepresentation H lam a f :
      ↥(subgroupCharacterFunctionSubmodule H lam)) : G → ℂ) g =
      (f : G → ℂ) (g * a) := rfl

/-! Normalizer transformations. -/

/-- A subgroup character obtained from a character and an element of the subgroup normalizer. -/
def subgroupCharacterOfNormalizer (s : G) (hs : s ∈ Subgroup.normalizer H) : ↥H →* ℂˣ where
  toFun h := lam ⟨s * h * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs h).mp h.2⟩
  map_one' := by
    rw [← map_one lam]
    apply congrArg lam
    ext
    simp
  map_mul' a b := by
    rw [← map_mul]
    apply congrArg lam
    ext
    simp only [Subgroup.coe_mul]
    group

/-- A linear equivalence between the function submodules associated with a subgroup character and
its normalizer transform. -/
def subgroupCharacterFunctionLinearEquivOfNormalizer (s : G)
    (hs : s ∈ Subgroup.normalizer H) :
    subgroupCharacterFunctionSubmodule H lam ≃ₗ[ℂ]
      subgroupCharacterFunctionSubmodule H (subgroupCharacterOfNormalizer H lam s hs) where
  toFun f := ⟨fun g => f.val (s * g), by
    intro h g
    change f.val (s * (h * g)) =
      (lam ⟨s * h * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs h).mp h.2⟩ : ℂ) * f.val (s * g)
    have hf := f.2 ⟨s * h * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs h).mp h.2⟩ (s * g)
    convert hf using 1; group⟩
  invFun f := ⟨fun g => f.val (s⁻¹ * g), by
    intro h g
    have hs_inv : s⁻¹ ∈ Subgroup.normalizer H := inv_mem hs
    have hmem : s⁻¹ * (h : G) * s ∈ H := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hs_inv h).mp h.2
    let h' : H := ⟨s⁻¹ * (h : G) * s, hmem⟩
    change f.val (s⁻¹ * ((h : G) * g)) = (lam h : ℂ) * f.val (s⁻¹ * g)
    have hf := f.2 h' (s⁻¹ * g)
    change f.val ((h' : G) * (s⁻¹ * g)) =
      (lam ⟨s * (h' : G) * s⁻¹,
        (Subgroup.mem_normalizer_iff.mp hs h').mp h'.2⟩ : ℂ) * f.val (s⁻¹ * g) at hf
    simpa [h', mul_assoc] using hf⟩
  left_inv f := by ext g; simp
  right_inv f := by ext g; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The normalizer linear equivalence sends a function to evaluation after left multiplication by
the normalizing element. -/
@[simp]
lemma subgroupCharacterFunctionLinearEquivOfNormalizer_apply (s : G)
    (hs : s ∈ Subgroup.normalizer H) (f : subgroupCharacterFunctionSubmodule H lam) (g : G) :
    ((subgroupCharacterFunctionLinearEquivOfNormalizer H lam s hs f :
      subgroupCharacterFunctionSubmodule H (subgroupCharacterOfNormalizer H lam s hs)) :
      G → ℂ) g = f.val (s * g) := rfl

variable [Fintype G] [DecidablePred (· ∈ H)]

/-- A finite-dimensional complex representation associated with a subgroup and a character into
the complex units. -/
def representationFromSubgroupCharacter : FDRep ℂ G :=
  FDRep.of (subgroupCharacterFunctionRepresentation H lam)

/-- A representation isomorphism associated with transforming a subgroup character by a
normalizing element. -/
def representationIsoOfNormalizer (s : G) (hs : s ∈ Subgroup.normalizer H) :
    representationFromSubgroupCharacter H lam ≅
      representationFromSubgroupCharacter H (subgroupCharacterOfNormalizer H lam s hs) :=
  Action.mkIso (subgroupCharacterFunctionLinearEquivOfNormalizer H lam s hs).toFGModuleCatIso
    (fun a => by
      ext f
      change subgroupCharacterFunctionLinearEquivOfNormalizer H lam s hs
          (subgroupCharacterFunctionRepresentation H lam a f) =
        subgroupCharacterFunctionRepresentation H (subgroupCharacterOfNormalizer H lam s hs) a
          (subgroupCharacterFunctionLinearEquivOfNormalizer H lam s hs f)
      apply Subtype.ext
      funext g
      rw [subgroupCharacterFunctionLinearEquivOfNormalizer_apply,
        subgroupCharacterFunctionRepresentation_apply,
        subgroupCharacterFunctionRepresentation_apply,
        subgroupCharacterFunctionLinearEquivOfNormalizer_apply, mul_assoc])

/-! Averaging into the subgroup-character submodule. -/

/-- A complex-linear endomorphism of complex-valued functions on the group associated with finite
subgroup character data. -/
def subgroupCharacterAveraging : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := fun g => (Fintype.card ↥H : ℂ)⁻¹ *
    ∑ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) * f (h.val * g)
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring

/-- At each group element, the averaging map is the normalized subgroup sum weighted by inverse
character values. -/
lemma subgroupCharacterAveraging_apply (f : G → ℂ) (g : G) :
    subgroupCharacterAveraging H lam f g =
      (Fintype.card ↥H : ℂ)⁻¹ *
        ∑ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) * f (h.val * g) := rfl

/-- The subgroup-character average of any function belongs to the associated function submodule. -/
lemma subgroupCharacterAveraging_mem (f : G → ℂ) :
    subgroupCharacterAveraging H lam f ∈ subgroupCharacterFunctionSubmodule H lam := by
  intro h₀ g
  rw [subgroupCharacterAveraging_apply, subgroupCharacterAveraging_apply, ← mul_assoc,
    mul_comm ((lam h₀ : ℂˣ) : ℂ), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h₀) _ _ ?_
  intro h
  have hlam : (((lam (h * h₀))⁻¹ : ℂˣ) : ℂ) =
      (((lam h)⁻¹ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ) := by
    rw [map_mul, mul_inv, Units.val_mul]
  have hcancel : ((lam h₀ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ) = 1 :=
    Units.mul_inv _
  change (((lam h)⁻¹ : ℂˣ) : ℂ) * f ((h : G) * (h₀.val * g)) =
    ((lam h₀ : ℂˣ) : ℂ) *
      ((((lam (h * h₀))⁻¹ : ℂˣ) : ℂ) * f (((h * h₀ : ↥H) : G) * g))
  rw [hlam, show ((h * h₀ : ↥H) : G) = (h : G) * (h₀ : G) from rfl,
    ← mul_assoc (h : G) (h₀ : G) g]
  set X := f ((h : G) * (h₀ : G) * g)
  calc
    (((lam h)⁻¹ : ℂˣ) : ℂ) * X =
        (((lam h₀ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ)) *
          ((((lam h)⁻¹ : ℂˣ) : ℂ) * X) := by
      rw [hcancel, one_mul]
    _ = ((lam h₀ : ℂˣ) : ℂ) *
        ((((lam h)⁻¹ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ) * X) := by
      ring

/-- The subgroup-character averaging map fixes every function in the associated submodule. -/
lemma subgroupCharacterAveraging_eq_self {f : G → ℂ}
    (hf : f ∈ subgroupCharacterFunctionSubmodule H lam) :
    subgroupCharacterAveraging H lam f = f := by
  funext g
  rw [subgroupCharacterAveraging_apply]
  have hterm : ∀ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) * f (h.val * g) = f g := by
    intro h
    rw [hf h g, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [Finset.sum_congr rfl fun h _ => hterm h, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-! Trace transport. -/

/-- A family of linear maps from all complex-valued functions on the group into the
subgroup-character function submodule. -/
def toSubgroupCharacterFunctionSubmoduleAt (a : G) :
    (G → ℂ) →ₗ[ℂ] ↥(subgroupCharacterFunctionSubmodule H lam) :=
  LinearMap.codRestrict (subgroupCharacterFunctionSubmodule H lam)
    (subgroupCharacterAveraging H lam ∘ₗ rightTranslationLinearMap a)
    fun _ => subgroupCharacterAveraging_mem H lam _

/-- Restricting the map into the subgroup-character function submodule agrees with the associated
representation action. -/
lemma toSubgroupCharacterFunctionSubmoduleAt_comp_subtype (a : G) :
    toSubgroupCharacterFunctionSubmoduleAt H lam a ∘ₗ
        (subgroupCharacterFunctionSubmodule H lam).subtype =
      subgroupCharacterFunctionRepresentation H lam a := by
  apply LinearMap.ext; intro f
  apply Subtype.ext
  change subgroupCharacterAveraging H lam (rightTranslationLinearMap a f.val) =
    rightTranslationLinearMap a f.val
  exact subgroupCharacterAveraging_eq_self H lam
    (rightTranslationLinearMap_mem H lam f.2 a)

/-- Including the submodule-valued map into all functions equals subgroup-character averaging
after right translation. -/
lemma subtype_comp_toSubgroupCharacterFunctionSubmoduleAt (a : G) :
    (subgroupCharacterFunctionSubmodule H lam).subtype ∘ₗ
        toSubgroupCharacterFunctionSubmoduleAt H lam a =
      subgroupCharacterAveraging H lam ∘ₗ rightTranslationLinearMap a := rfl

/-- The trace of the subgroup-character function representation equals the trace of averaging
composed with right translation on the full function space. -/
lemma trace_subgroupCharacterFunctionRepresentation_eq (a : G) :
    LinearMap.trace ℂ _ (subgroupCharacterFunctionRepresentation H lam a) =
      LinearMap.trace ℂ (G → ℂ)
        (subgroupCharacterAveraging H lam ∘ₗ rightTranslationLinearMap a) := by
  rw [← toSubgroupCharacterFunctionSubmoduleAt_comp_subtype H lam a,
    LinearMap.trace_comp_comm' (subgroupCharacterFunctionSubmodule H lam).subtype
      (toSubgroupCharacterFunctionSubmoduleAt H lam a),
    subtype_comp_toSubgroupCharacterFunctionSubmoduleAt]

/-! Diagonal trace calculation. -/

/-- The diagonal summand is supported at the uniquely determined subgroup element. -/
private lemma sum_indicator [DecidableEq G] (a g : G) :
    ∑ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) *
        (if (h : G) * g * a = g then (1 : ℂ) else 0) =
      if hm : g * a⁻¹ * g⁻¹ ∈ H then
        (((lam ⟨g * a⁻¹ * g⁻¹, hm⟩)⁻¹ : ℂˣ) : ℂ) else 0 := by
  by_cases hm : g * a⁻¹ * g⁻¹ ∈ H
  · rw [dif_pos hm]
    set h₀ : ↥H := ⟨g * a⁻¹ * g⁻¹, hm⟩ with hh₀
    have hcond : ∀ h : ↥H, ((h : G) * g * a = g) ↔ h = h₀ := by
      intro h
      constructor
      · intro hh
        apply Subtype.ext
        change (h : G) = g * a⁻¹ * g⁻¹
        have h2 : (h : G) * (g * a) = g := by rw [← mul_assoc]; exact hh
        rw [eq_mul_inv_of_mul_eq h2]
        group
      · rintro rfl
        change (g * a⁻¹ * g⁻¹) * g * a = g
        group
    rw [Finset.sum_congr rfl fun h _ => by rw [if_congr (hcond h) rfl rfl],
      Finset.sum_eq_single h₀
        (fun h _ hne => by rw [if_neg hne, mul_zero])
        (fun hnm => absurd (Finset.mem_univ h₀) hnm),
      if_pos rfl, mul_one]
  · rw [dif_neg hm]
    refine Finset.sum_eq_zero fun h _ => ?_
    rw [if_neg, mul_zero]
    intro hh
    apply hm
    have h2 : (h : G) * (g * a) = g := by rw [← mul_assoc]; exact hh
    have h3 : (h : G) = g * a⁻¹ * g⁻¹ := by rw [eq_mul_inv_of_mul_eq h2]; group
    exact h3 ▸ h.2

/-- Compute the trace of averaged right translation in the standard function basis. -/
private lemma trace_proj_comp (a : G) :
    LinearMap.trace ℂ (G → ℂ)
        (subgroupCharacterAveraging H lam ∘ₗ rightTranslationLinearMap a) =
      (Fintype.card ↥H : ℂ)⁻¹ * ∑ g : G,
        if hm : g * a⁻¹ * g⁻¹ ∈ H then
          (((lam ⟨g * a⁻¹ * g⁻¹, hm⟩)⁻¹ : ℂˣ) : ℂ)
        else 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ G), Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
  change subgroupCharacterAveraging H lam (rightTranslationLinearMap a (Pi.single g 1)) g = _
  rw [subgroupCharacterAveraging_apply, ← sum_indicator H lam a g]
  refine congrArg _ (Finset.sum_congr rfl fun h _ => ?_)
  rw [rightTranslationLinearMap_apply, Pi.single_apply]

/-! Character and dimension formulas. -/

/-- An auxiliary result involving the representation associated with subgroup character data. -/
theorem auxiliary_representationFromSubgroupCharacter (a : G) :
    (representationFromSubgroupCharacter H lam).character a =
      (Fintype.card ↥H : ℂ)⁻¹ * ∑ x : G,
        if hm : x⁻¹ * a * x ∈ H then
          ((lam ⟨x⁻¹ * a * x, hm⟩ : ℂˣ) : ℂ) else 0 := by
  change LinearMap.trace ℂ _ (subgroupCharacterFunctionRepresentation H lam a) = _
  rw [trace_subgroupCharacterFunctionRepresentation_eq, trace_proj_comp]
  refine congrArg _ (Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_)
  change (if hm : g * a⁻¹ * g⁻¹ ∈ H then
      (((lam ⟨g * a⁻¹ * g⁻¹, hm⟩)⁻¹ : ℂˣ) : ℂ) else 0) =
    if hm : g⁻¹⁻¹ * a * g⁻¹ ∈ H then
      ((lam ⟨g⁻¹⁻¹ * a * g⁻¹, hm⟩ : ℂˣ) : ℂ) else 0
  have hinv : (g * a⁻¹ * g⁻¹)⁻¹ = g⁻¹⁻¹ * a * g⁻¹ := by group
  by_cases hm : g * a⁻¹ * g⁻¹ ∈ H
  · have hm' : g⁻¹⁻¹ * a * g⁻¹ ∈ H := hinv ▸ H.inv_mem hm
    rw [dif_pos hm, dif_pos hm',
      show (⟨g⁻¹⁻¹ * a * g⁻¹, hm'⟩ : ↥H) =
          (⟨g * a⁻¹ * g⁻¹, hm⟩ : ↥H)⁻¹ from
        Subtype.ext hinv.symm,
      map_inv]
  · have hm' : ¬ (g⁻¹⁻¹ * a * g⁻¹ ∈ H) := fun hc => hm (by
      have := H.inv_mem hc
      rwa [show (g⁻¹⁻¹ * a * g⁻¹)⁻¹ = g * a⁻¹ * g⁻¹ from by group] at this)
    rw [dif_neg hm, dif_neg hm']

/-- The dimension of the representation associated with subgroup character data is the group
cardinality divided by the subgroup cardinality. -/
theorem finrank_representationFromSubgroupCharacter :
    Module.finrank ℂ (representationFromSubgroupCharacter H lam) =
      Fintype.card G / Fintype.card ↥H := by
  have hdvd : Fintype.card ↥H ∣ Fintype.card G := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  obtain ⟨m, hm⟩ := hdvd
  have hpos : (0 : ℕ) < Fintype.card ↥H := Fintype.card_pos
  have hchar := auxiliary_representationFromSubgroupCharacter H lam 1
  rw [FDRep.char_one] at hchar
  have hsum : ∑ x : G,
      (if hmem : x⁻¹ * (1 : G) * x ∈ H then
        ((lam ⟨x⁻¹ * (1 : G) * x, hmem⟩ : ℂˣ) : ℂ)
        else 0) = (Fintype.card G : ℂ) := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => show
        (if hmem : x⁻¹ * (1 : G) * x ∈ H then
          ((lam ⟨x⁻¹ * (1 : G) * x, hmem⟩ : ℂˣ) : ℂ)
          else 0) = (1 : ℂ) from by
      have hx : x⁻¹ * (1 : G) * x = 1 := by group
      simp only [hx, dif_pos H.one_mem]
      rw [show (⟨(1 : G), H.one_mem⟩ : ↥H) = 1 from rfl, map_one, Units.val_one],
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hsum, hm] at hchar
  have hne : (Fintype.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hcast : (Module.finrank ℂ (representationFromSubgroupCharacter H lam) : ℂ) =
      (m : ℂ) := by
    rw [hchar]; push_cast;
    field_simp
  have hfin : Module.finrank ℂ (representationFromSubgroupCharacter H lam) = m :=
    Nat.cast_injective hcast
  rw [hfin, hm, Nat.mul_div_cancel_left m hpos]

end RepresentationTheory.FDRep.SubgroupCharacterFunctions
