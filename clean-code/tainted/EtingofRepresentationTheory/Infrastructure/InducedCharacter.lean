import Mathlib

/-!
# Induction of a linear character from a subgroup, and the Frobenius character formula

For a finite group `G`, a subgroup `H ≤ G` and a multiplicative character
`lam : H →* ℂˣ`, this file constructs `Ind_H^G ℂ_lam` as an honest finite-dimensional
representation and computes its character.

The model is the covariance submodule

```
{f : G → ℂ | ∀ h ∈ H, ∀ g, f (h * g) = lam h * f g}
```

inside `G → ℂ`, with `G` acting by right translation. This is the same model
`Chapter5/Theorem5_25_2.lean` uses for the principal series of `GL₂(𝔽_q)`; here it is
set up once for an arbitrary subgroup, so that the elliptic-torus induction of
Chapter 5 can reuse it.

## Key results

* `Etingof.InducedChar.ind` — the induced representation as an `FDRep ℂ G`.
* `Etingof.InducedChar.character_ind` — the Frobenius character formula

  ```
  (ind H lam).character a
    = (Fintype.card H : ℂ)⁻¹ * ∑ x : G, if h : x⁻¹ * a * x ∈ H then lam ⟨_, h⟩ else 0
  ```

* `Etingof.InducedChar.finrank_ind` — `finrank ℂ (ind H lam) = card G / card H`.

## Implementation notes

The character is computed by transporting the trace off the submodule. The averaging
operator

```
(P f) g = |H|⁻¹ * ∑ h : H, (lam h)⁻¹ * f (h * g)
```

is an idempotent of `G → ℂ` whose image is the covariance submodule, and it commutes
with right translation. Writing `P ∘ R a` as `subtype ∘ₗ S a` with
`S a : (G → ℂ) →ₗ V` and using `LinearMap.trace_comp_comm'`, the trace of the action on
`V` becomes the trace of `P ∘ R a` on all of `G → ℂ`, where it is a short computation
in the standard basis of delta functions.
-/

noncomputable section

namespace Etingof.InducedChar

open Finset

variable {G : Type} [Group G] (H : Subgroup G) (lam : ↥H →* ℂˣ)

/-- The covariance submodule `{f : G → ℂ | f (h * g) = lam h * f g}` of `G → ℂ`.
This carries the induced representation `Ind_H^G ℂ_lam`. -/
def submodule : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ (h : ↥H) (g : G), f (h.val * g) = (lam h : ℂ) * f g}
  add_mem' {f f'} hf hf' := by
    intro h g; simp only [Pi.add_apply]; rw [hf h g, hf' h g, mul_add]
  zero_mem' := by intro h g; simp
  smul_mem' c f hf := by
    intro h g; simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf h g, mul_left_comm]

lemma mem_submodule_iff (f : G → ℂ) :
    f ∈ submodule H lam ↔ ∀ (h : ↥H) (g : G), f (h.val * g) = (lam h : ℂ) * f g :=
  Iff.rfl

/-- Right translation `f ↦ (g ↦ f (g * a))` on `G → ℂ`. -/
def rightTranslation (a : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := fun g => f (g * a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma rightTranslation_apply (a : G) (f : G → ℂ) (g : G) :
    rightTranslation a f g = f (g * a) := rfl

/-- Right translation preserves the covariance submodule. -/
lemma rightTranslation_mem {f : G → ℂ} (hf : f ∈ submodule H lam) (a : G) :
    rightTranslation a f ∈ submodule H lam := by
  intro h g
  change f (h.val * g * a) = (lam h : ℂ) * f (g * a)
  rw [mul_assoc]; exact hf h (g * a)

/-- `Ind_H^G ℂ_lam` as a representation of `G` by right translation on the covariance
submodule. -/
def rep : Representation ℂ G (submodule H lam) where
  toFun a :=
    { toFun := fun f => ⟨rightTranslation a f.val, rightTranslation_mem H lam f.2 a⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  map_one' := by
    apply LinearMap.ext; intro f
    exact Subtype.ext (funext fun g => congr_arg f.val (mul_one g))
  map_mul' a b := by
    apply LinearMap.ext; intro f
    exact Subtype.ext (funext fun g => congr_arg f.val (mul_assoc g a b).symm)

@[simp]
lemma rep_apply_coe (a : G) (f : ↥(submodule H lam)) (g : G) :
    ((rep H lam a f : ↥(submodule H lam)) : G → ℂ) g = (f : G → ℂ) (g * a) := rfl

/-! ### Conjugating the inducing character -/

/-- Conjugate a character of `H` by an element of its normalizer. -/
def conjugateCharacter (s : G) (hs : s ∈ Subgroup.normalizer H) : ↥H →* ℂˣ where
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

/-- Left translation by a normalizing element identifies the two covariance spaces. -/
def conjugateLinearEquiv (s : G) (hs : s ∈ Subgroup.normalizer H) :
    submodule H lam ≃ₗ[ℂ] submodule H (conjugateCharacter H lam s hs) where
  toFun f := ⟨fun g => f.val (s * g), by
    intro h g
    change f.val (s * (h * g)) =
      (lam ⟨s * h * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs h).mp h.2⟩ : ℂ) * f.val (s * g)
    have hf := f.2 ⟨s * h * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs h).mp h.2⟩ (s * g)
    convert hf using 1; group⟩
  invFun f := ⟨fun g => f.val (s⁻¹ * g), by
    intro h g
    have hs_inv : s⁻¹ ∈ Subgroup.normalizer H := inv_mem hs
    have hmem : s⁻¹ * (h : G) * s ∈ H :=
      by simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hs_inv h).mp h.2
    let h' : H := ⟨s⁻¹ * (h : G) * s, hmem⟩
    change f.val (s⁻¹ * ((h : G) * g)) =
      (lam h : ℂ) * f.val (s⁻¹ * g)
    have hf := f.2 h' (s⁻¹ * g)
    change f.val ((h' : G) * (s⁻¹ * g)) =
      (lam ⟨s * (h' : G) * s⁻¹,
        (Subgroup.mem_normalizer_iff.mp hs h').mp h'.2⟩ : ℂ) * f.val (s⁻¹ * g) at hf
    simpa [h', mul_assoc] using hf⟩
  left_inv f := by ext g; simp
  right_inv f := by ext g; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma conjugateLinearEquiv_apply (s : G) (hs : s ∈ Subgroup.normalizer H)
    (f : submodule H lam) (g : G) :
    ((conjugateLinearEquiv H lam s hs f : submodule H
      (conjugateCharacter H lam s hs)) : G → ℂ) g = f.val (s * g) := rfl

variable [Fintype G] [DecidablePred (· ∈ H)]

/-- The induced representation `Ind_H^G ℂ_lam` as a finite-dimensional representation. -/
def ind : FDRep ℂ G := FDRep.of (rep H lam)

/-- Induction is unchanged when the inducing character is conjugated by an element of
the subgroup normalizer. -/
def indConjugateIso (s : G) (hs : s ∈ Subgroup.normalizer H) :
    ind H lam ≅ ind H (conjugateCharacter H lam s hs) :=
  Action.mkIso (conjugateLinearEquiv H lam s hs).toFGModuleCatIso (fun a => by
    ext f
    change conjugateLinearEquiv H lam s hs (rep H lam a f) =
      rep H (conjugateCharacter H lam s hs) a (conjugateLinearEquiv H lam s hs f)
    apply Subtype.ext
    funext g
    rw [conjugateLinearEquiv_apply, rep_apply_coe, rep_apply_coe,
      conjugateLinearEquiv_apply, mul_assoc])

/-! ### The averaging projection onto the covariance submodule -/

/-- The averaging operator `(P f) g = |H|⁻¹ ∑_{h ∈ H} (lam h)⁻¹ * f (h * g)`. It is an
idempotent of `G → ℂ` whose image is `submodule H lam`. -/
def proj : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := fun g => (Fintype.card ↥H : ℂ)⁻¹ *
    ∑ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) * f (h.val * g)
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring

lemma proj_apply (f : G → ℂ) (g : G) :
    proj H lam f g =
      (Fintype.card ↥H : ℂ)⁻¹ * ∑ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) * f (h.val * g) := rfl

/-- The image of the averaging operator lies in the covariance submodule. -/
lemma proj_mem (f : G → ℂ) : proj H lam f ∈ submodule H lam := by
  intro h₀ g
  rw [proj_apply, proj_apply, ← mul_assoc, mul_comm ((lam h₀ : ℂˣ) : ℂ), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h₀) _ _ ?_
  intro h
  have hlam : (((lam (h * h₀))⁻¹ : ℂˣ) : ℂ)
      = (((lam h)⁻¹ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ) := by
    rw [map_mul, mul_inv, Units.val_mul]
  have hcancel : ((lam h₀ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ) = 1 := Units.mul_inv _
  change (((lam h)⁻¹ : ℂˣ) : ℂ) * f ((h : G) * (h₀.val * g))
    = ((lam h₀ : ℂˣ) : ℂ) *
      ((((lam (h * h₀))⁻¹ : ℂˣ) : ℂ) * f (((h * h₀ : ↥H) : G) * g))
  rw [hlam, show ((h * h₀ : ↥H) : G) = (h : G) * (h₀ : G) from rfl,
    ← mul_assoc (h : G) (h₀ : G) g]
  set X := f ((h : G) * (h₀ : G) * g)
  calc (((lam h)⁻¹ : ℂˣ) : ℂ) * X
      = (((lam h₀ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ)) * ((((lam h)⁻¹ : ℂˣ) : ℂ) * X) := by
        rw [hcancel, one_mul]
    _ = ((lam h₀ : ℂˣ) : ℂ) *
        ((((lam h)⁻¹ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ) * X) := by ring

/-- The averaging operator restricts to the identity on the covariance submodule. -/
lemma proj_eq_self {f : G → ℂ} (hf : f ∈ submodule H lam) : proj H lam f = f := by
  funext g
  rw [proj_apply]
  have hterm : ∀ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) * f (h.val * g) = f g := by
    intro h
    rw [hf h g, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [Finset.sum_congr rfl fun h _ => hterm h, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-! ### Transporting the trace -/

/-- The averaging operator composed with right translation, viewed as a map into the
covariance submodule. -/
def projTo (a : G) : (G → ℂ) →ₗ[ℂ] ↥(submodule H lam) :=
  LinearMap.codRestrict (submodule H lam) (proj H lam ∘ₗ rightTranslation a)
    fun _ => proj_mem H lam _

lemma projTo_comp_subtype (a : G) :
    projTo H lam a ∘ₗ (submodule H lam).subtype = rep H lam a := by
  apply LinearMap.ext; intro f
  apply Subtype.ext
  change proj H lam (rightTranslation a f.val) = rightTranslation a f.val
  exact proj_eq_self H lam (rightTranslation_mem H lam f.2 a)

lemma subtype_comp_projTo (a : G) :
    (submodule H lam).subtype ∘ₗ projTo H lam a = proj H lam ∘ₗ rightTranslation a := rfl

/-- The trace of the induced action equals the trace of `P ∘ R a` on all of `G → ℂ`. -/
lemma trace_rep (a : G) :
    LinearMap.trace ℂ _ (rep H lam a)
      = LinearMap.trace ℂ (G → ℂ) (proj H lam ∘ₗ rightTranslation a) := by
  rw [← projTo_comp_subtype H lam a,
    LinearMap.trace_comp_comm' (submodule H lam).subtype (projTo H lam a),
    subtype_comp_projTo]

/-! ### The diagonal sum -/

/-- Only `h = g a⁻¹ g⁻¹` contributes to the `g`-th diagonal entry. -/
private lemma sum_indicator [DecidableEq G] (a g : G) :
    ∑ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) * (if (h : G) * g * a = g then (1 : ℂ) else 0)
      = if hm : g * a⁻¹ * g⁻¹ ∈ H then (((lam ⟨g * a⁻¹ * g⁻¹, hm⟩)⁻¹ : ℂˣ) : ℂ) else 0 := by
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

/-- The trace of `P ∘ R a` in the standard basis of `G → ℂ`. -/
private lemma trace_proj_comp (a : G) :
    LinearMap.trace ℂ (G → ℂ) (proj H lam ∘ₗ rightTranslation a)
      = (Fintype.card ↥H : ℂ)⁻¹ * ∑ g : G,
          if hm : g * a⁻¹ * g⁻¹ ∈ H then (((lam ⟨g * a⁻¹ * g⁻¹, hm⟩)⁻¹ : ℂˣ) : ℂ)
          else 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ G), Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
  change proj H lam (rightTranslation a (Pi.single g 1)) g = _
  rw [proj_apply, ← sum_indicator H lam a g]
  refine congrArg _ (Finset.sum_congr rfl fun h _ => ?_)
  rw [rightTranslation_apply, Pi.single_apply]

/-! ### Main results -/

/-- **Frobenius character formula** for the induced representation `Ind_H^G ℂ_lam`. -/
theorem character_ind (a : G) :
    (ind H lam).character a
      = (Fintype.card ↥H : ℂ)⁻¹ * ∑ x : G,
          if hm : x⁻¹ * a * x ∈ H then ((lam ⟨x⁻¹ * a * x, hm⟩ : ℂˣ) : ℂ) else 0 := by
  change LinearMap.trace ℂ _ (rep H lam a) = _
  rw [trace_rep, trace_proj_comp]
  refine congrArg _ (Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_)
  change (if hm : g * a⁻¹ * g⁻¹ ∈ H then (((lam ⟨g * a⁻¹ * g⁻¹, hm⟩)⁻¹ : ℂˣ) : ℂ) else 0)
    = if hm : g⁻¹⁻¹ * a * g⁻¹ ∈ H then ((lam ⟨g⁻¹⁻¹ * a * g⁻¹, hm⟩ : ℂˣ) : ℂ) else 0
  have hinv : (g * a⁻¹ * g⁻¹)⁻¹ = g⁻¹⁻¹ * a * g⁻¹ := by group
  by_cases hm : g * a⁻¹ * g⁻¹ ∈ H
  · have hm' : g⁻¹⁻¹ * a * g⁻¹ ∈ H := hinv ▸ H.inv_mem hm
    rw [dif_pos hm, dif_pos hm',
      show (⟨g⁻¹⁻¹ * a * g⁻¹, hm'⟩ : ↥H) = (⟨g * a⁻¹ * g⁻¹, hm⟩ : ↥H)⁻¹ from
        Subtype.ext hinv.symm,
      map_inv]
  · have hm' : ¬ (g⁻¹⁻¹ * a * g⁻¹ ∈ H) := fun hc => hm (by
      have := H.inv_mem hc
      rwa [show (g⁻¹⁻¹ * a * g⁻¹)⁻¹ = g * a⁻¹ * g⁻¹ from by group] at this)
    rw [dif_neg hm, dif_neg hm']

/-- The induced representation has dimension `[G : H]`. -/
theorem finrank_ind :
    Module.finrank ℂ (ind H lam) = Fintype.card G / Fintype.card ↥H := by
  have hdvd : Fintype.card ↥H ∣ Fintype.card G := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  obtain ⟨m, hm⟩ := hdvd
  have hpos : (0 : ℕ) < Fintype.card ↥H := Fintype.card_pos
  have hchar := character_ind H lam 1
  rw [FDRep.char_one] at hchar
  have hsum : ∑ x : G,
      (if hmem : x⁻¹ * (1 : G) * x ∈ H then ((lam ⟨x⁻¹ * (1 : G) * x, hmem⟩ : ℂˣ) : ℂ)
        else 0) = (Fintype.card G : ℂ) := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => show
        (if hmem : x⁻¹ * (1 : G) * x ∈ H then ((lam ⟨x⁻¹ * (1 : G) * x, hmem⟩ : ℂˣ) : ℂ)
          else 0) = (1 : ℂ) from by
      have hx : x⁻¹ * (1 : G) * x = 1 := by group
      simp only [hx, dif_pos H.one_mem]
      rw [show (⟨(1 : G), H.one_mem⟩ : ↥H) = 1 from rfl, map_one, Units.val_one],
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hsum, hm] at hchar
  have hne : (Fintype.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hcast : (Module.finrank ℂ (ind H lam) : ℂ) = (m : ℂ) := by
    rw [hchar]; push_cast; field_simp
  have hfin : Module.finrank ℂ (ind H lam) = m := Nat.cast_injective hcast
  rw [hfin, hm, Nat.mul_div_cancel_left m hpos]

end Etingof.InducedChar
