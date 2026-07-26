import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_25_2
import EtingofRepresentationTheory.Chapter5.GL2CharacterValues
import EtingofRepresentationTheory.Infrastructure.FDRepCharacterBiprod

/-!
# Identifying the `GL₂(𝔽_q)` character formulas with actual representations

`Chapter5/GL2CharacterValues.lean` introduces the two building blocks of the complementary-series
virtual character as **bare functions** `GL₂(𝔽_q) → ℂ`:

* `Etingof.GL2.charVα₁ p n α` — the Frobenius sum `|B|⁻¹ ∑_{x ∈ G} [x⁻¹gx ∈ B] · α((x⁻¹gx)₀₀)`;
* `Etingof.GL2.charW₁ p n` — the fixed-point count of `g` on `P¹(𝔽_q)`, minus one.

`Chapter5/Theorem5_25_2.lean` constructs the corresponding objects of `FDRep ℂ (GL₂ 𝔽_q)`:
`Etingof.GL2.principalSeries p n χ₁ χ₂ = Ind_B^G ℂ_{χ₁,χ₂}` and `Etingof.GL2.complementW p n μ`,
the augmentation kernel `W_μ ⊆ V(μ, μ)`.

This file connects the two halves:

* `Etingof.GL2.character_principalSeries` : `(principalSeries p n α 1).character = charVα₁ p n α`;
* `Etingof.GL2.character_complementW` : `(complementW p n 1).character = charW₁ p n`.

The common engine is `Etingof.GL2.principalSeries_character_apply`, the coset form of the
character of `V(χ₁, χ₂)`: evaluating covariant functions at the coset representatives
`Etingof.GL2.cosetRep` identifies `V(χ₁, χ₂)` with `P¹(𝔽_q) → ℂ`, and in that basis only the
representatives with `B r_i g = B r_i` contribute to the trace,

  `χ_{V(χ₁,χ₂)}(g) = ∑_{i ∈ P¹} [idx(r_i g) = i] · λ(borel(r_i g))`.

Two reindexings turn this into the two statements above. For `charVα₁` the bijection
`G ≃ B × P¹` (`Etingof.GL2.borelCosetEquiv`) converts the sum over `P¹` into the average over
`G`, using `|B| = (q−1)²q` (`Etingof.GL2.card_borelSubgroup`). For `charW₁` the character of
`V(1, 1)` counts the `i ∈ P¹` fixed by `g`, and the involution `t ↦ −t⁻¹` of `P¹`
(`Etingof.GL2.projInvol`) matches that count with the affine-chart count `charW₁` uses: the
coset parametrization tracks the *row* line `[g₁₀ : g₁₁]`, while `charW₁` tracks the *column*
line, and the two fixed-point sets correspond under `t ↦ −t⁻¹`. Subtracting the trivial summand
`ℂ_1` of `V(1, 1)` gives `charW₁`.
-/

open CategoryTheory CategoryTheory.Limits Classical

noncomputable section

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 (p n : ℕ) [Fact (Nat.Prime p)] :=
  Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

namespace Etingof.GL2

-- ============================================================
-- The coset form of the principal-series character
-- ============================================================

/-- Evaluation of a covariant function at the coset representatives of `B \ GL₂(𝔽_q)`. -/
def psEval (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2) →ₗ[ℂ]
      (Option (GaloisField p n) → ℂ) where
  toFun f i := (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n i)
  map_add' _ _ := funext fun _ => rfl
  map_smul' _ _ := funext fun _ => rfl

lemma psEval_bijective (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Function.Bijective (Etingof.GL2.psEval p n chi1 chi2) := by
  constructor
  · intro f g hfg
    have h : f - g = 0 :=
      Etingof.GL2.principalSeries_eval_injective p n chi1 chi2 (f - g) fun i => by
        have := congr_fun hfg i
        simp only [Etingof.GL2.psEval, LinearMap.coe_mk, AddHom.coe_mk] at this
        simpa using sub_eq_zero.mpr this
    exact sub_eq_zero.mp h
  · intro c
    exact ⟨⟨Etingof.GL2.mkCovariantFun p n chi1 chi2 c,
        Etingof.GL2.mkCovariantFun_mem p n chi1 chi2 c⟩,
      funext fun i => Etingof.GL2.mkCovariantFun_eval p n chi1 chi2 c i⟩

/-- Evaluation at the coset representatives identifies `V(χ₁, χ₂)` with `P¹(𝔽_q) → ℂ`. -/
def psEquiv (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2) ≃ₗ[ℂ]
      (Option (GaloisField p n) → ℂ) :=
  LinearEquiv.ofBijective _ (Etingof.GL2.psEval_bijective p n chi1 chi2)

lemma psEquiv_symm_apply (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : Option (GaloisField p n) → ℂ) :
    ((Etingof.GL2.psEquiv p n chi1 chi2).symm c : GL2 p n → ℂ) =
      Etingof.GL2.mkCovariantFun p n chi1 chi2 c := by
  have h : (Etingof.GL2.psEquiv p n chi1 chi2).symm c =
      ⟨Etingof.GL2.mkCovariantFun p n chi1 chi2 c,
        Etingof.GL2.mkCovariantFun_mem p n chi1 chi2 c⟩ := by
    apply (Etingof.GL2.psEquiv p n chi1 chi2).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (funext fun i => Etingof.GL2.mkCovariantFun_eval p n chi1 chi2 c i).symm
  rw [h]

/-- **Coset form of the principal-series character.** Only the coset representatives `r_i` with
`B r_i g = B r_i` contribute to the trace of `g` on `V(χ₁, χ₂)`, and the contribution of such an
`r_i` is the value of the Borel character on `r_i g r_i⁻¹`. -/
theorem principalSeries_character_apply
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (g : GL2 p n) :
    (Etingof.GL2.principalSeries p n chi1 chi2).character g =
      ∑ i : Option (GaloisField p n),
        if Etingof.GL2.cosetIndex p n (Etingof.GL2.cosetRep p n i * g) = i then
          Etingof.GL2.borelCharValue p n chi1 chi2
            (Etingof.GL2.cosetBorel p n (Etingof.GL2.cosetRep p n i * g))
        else 0 := by
  show LinearMap.trace ℂ ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2)
      (Etingof.GL2.principalSeriesRep p n chi1 chi2 g) = _
  rw [← LinearMap.trace_conj' (Etingof.GL2.principalSeriesRep p n chi1 chi2 g)
      (Etingof.GL2.psEquiv p n chi1 chi2),
    LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Option (GaloisField p n)))]
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
    LinearEquiv.conj_apply]
  have hval : ((Etingof.GL2.psEquiv p n chi1 chi2)
      (Etingof.GL2.principalSeriesRep p n chi1 chi2 g
        ((Etingof.GL2.psEquiv p n chi1 chi2).symm (Pi.single i 1)))) i =
      Etingof.GL2.mkCovariantFun p n chi1 chi2 (Pi.single i 1)
        (Etingof.GL2.cosetRep p n i * g) := by
    rw [show (Etingof.GL2.psEquiv p n chi1 chi2) = fun f => Etingof.GL2.psEval p n chi1 chi2 f from
      rfl]
    simp only [Etingof.GL2.psEval, LinearMap.coe_mk, AddHom.coe_mk]
    change ((Etingof.GL2.psEquiv p n chi1 chi2).symm (Pi.single i 1) : GL2 p n → ℂ)
      (Etingof.GL2.cosetRep p n i * g) = _
    rw [Etingof.GL2.psEquiv_symm_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_toLinearMap] at hval ⊢
  rw [hval, Etingof.GL2.mkCovariantFun, Pi.single_apply]
  by_cases h : Etingof.GL2.cosetIndex p n (Etingof.GL2.cosetRep p n i * g) = i <;> simp [h]

-- ============================================================
-- The bijection `G ≃ B × P¹` and the order of `B`
-- ============================================================

/-- The coset decomposition `g = borel(g) · r_{idx(g)}` as a bijection `G ≃ B × P¹(𝔽_q)`. -/
def borelCosetEquiv :
    GL2 p n ≃ ↥(Etingof.GL2.BorelSubgroup p n) × Option (GaloisField p n) where
  toFun x := (Etingof.GL2.cosetBorel p n x, Etingof.GL2.cosetIndex p n x)
  invFun bi := bi.1.val * Etingof.GL2.cosetRep p n bi.2
  left_inv x := (Etingof.GL2.cosetBorel_mul_cosetRep p n x).symm
  right_inv := by
    rintro ⟨b, i⟩
    have h1 : Etingof.GL2.cosetIndex p n (b.val * Etingof.GL2.cosetRep p n i) = i := by
      rw [Etingof.GL2.cosetIndex_borel_mul, Etingof.GL2.cosetIndex_cosetRep]
    have h2 : Etingof.GL2.cosetBorel p n (b.val * Etingof.GL2.cosetRep p n i) = b := by
      rw [Etingof.GL2.cosetBorel_borel_mul, Etingof.GL2.cosetBorel_cosetRep]
      exact Subtype.ext (by simp)
    exact Prod.ext h2 h1

/-- An upper-triangular invertible matrix is determined by its two (invertible) diagonal entries
and its upper-right entry. -/
def borelEntriesEquiv :
    ↥(Etingof.GL2.BorelSubgroup p n) ≃
      (GaloisField p n)ˣ × (GaloisField p n)ˣ × GaloisField p n where
  toFun b :=
    (Units.mk0 _ (Etingof.GL2.borel_diag00_ne_zero p n b),
     Units.mk0 _ (Etingof.GL2.borel_diag11_ne_zero p n b),
     (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 1)
  invFun adc :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(adc.1 : GaloisField p n), adc.2.2; 0, (adc.2.1 : GaloisField p n)]
        (by simp [Matrix.det_fin_two]),
      by
        show ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(adc.1 : GaloisField p n), adc.2.2; 0, (adc.2.1 : GaloisField p n)]
          (by simp [Matrix.det_fin_two])).val :
            Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0
        simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
          Matrix.unitOfDetInvertible]⟩
  left_inv b := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible, hb10]
  right_inv adc := by
    obtain ⟨a, d, c⟩ := adc
    refine Prod.ext (Units.ext ?_) (Prod.ext (Units.ext ?_) ?_) <;>
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible]

/-- `|B| = (q − 1)² q`: an element of the Borel subgroup is a pair of invertible diagonal
entries together with an arbitrary upper-right entry. -/
theorem card_borelSubgroup [Fintype ↥(Etingof.GL2.BorelSubgroup p n)] :
    Fintype.card ↥(Etingof.GL2.BorelSubgroup p n) =
      (Fintype.card (GaloisField p n) - 1) ^ 2 * Fintype.card (GaloisField p n) := by
  rw [Fintype.card_congr (Etingof.GL2.borelEntriesEquiv p n), Fintype.card_prod,
    Fintype.card_prod, Fintype.card_units]
  ring

-- ============================================================
-- Deliverable 1 : the character of the principal series is `charVα₁`
-- ============================================================

/-- The Borel character is a class function on `B`. -/
lemma borelCharValue_conj (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (b y : ↥(Etingof.GL2.BorelSubgroup p n)) :
    Etingof.GL2.borelCharValue p n chi1 chi2 (b * y * b⁻¹) =
      Etingof.GL2.borelCharValue p n chi1 chi2 y := by
  have hmul : ∀ u v : ↥(Etingof.GL2.BorelSubgroup p n),
      Etingof.GL2.borelCharValue p n chi1 chi2 (u * v) =
        Etingof.GL2.borelCharValue p n chi1 chi2 u *
          Etingof.GL2.borelCharValue p n chi1 chi2 v := fun u v =>
    Etingof.GL2.borelCharValue_mul p n chi1 chi2 u v
  have hone : Etingof.GL2.borelCharValue p n chi1 chi2 1 = 1 :=
    Etingof.GL2.borelCharValue_one p n chi1 chi2
  have hinv : Etingof.GL2.borelCharValue p n chi1 chi2 b *
      Etingof.GL2.borelCharValue p n chi1 chi2 b⁻¹ = 1 := by
    rw [← hmul, mul_inv_cancel, hone]
  rw [hmul, hmul]
  calc Etingof.GL2.borelCharValue p n chi1 chi2 b *
        Etingof.GL2.borelCharValue p n chi1 chi2 y *
        Etingof.GL2.borelCharValue p n chi1 chi2 b⁻¹
      = (Etingof.GL2.borelCharValue p n chi1 chi2 b *
          Etingof.GL2.borelCharValue p n chi1 chi2 b⁻¹) *
        Etingof.GL2.borelCharValue p n chi1 chi2 y := by ring
    _ = Etingof.GL2.borelCharValue p n chi1 chi2 y := by rw [hinv, one_mul]

/-- The Borel character extended by zero off `B`, the integrand of the Frobenius formula. -/
def borelCharExt (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (y : GL2 p n) : ℂ :=
  if h : y ∈ Etingof.GL2.BorelSubgroup p n then
    Etingof.GL2.borelCharValue p n chi1 chi2 ⟨y, h⟩
  else 0

lemma borelCharExt_conj (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (b : ↥(Etingof.GL2.BorelSubgroup p n)) (y : GL2 p n) :
    Etingof.GL2.borelCharExt p n chi1 chi2 (b.val * y * b.val⁻¹) =
      Etingof.GL2.borelCharExt p n chi1 chi2 y := by
  simp only [Etingof.GL2.borelCharExt]
  by_cases hy : y ∈ Etingof.GL2.BorelSubgroup p n
  · have hc : b.val * y * b.val⁻¹ ∈ Etingof.GL2.BorelSubgroup p n :=
      (Etingof.GL2.BorelSubgroup p n).mul_mem
        ((Etingof.GL2.BorelSubgroup p n).mul_mem b.prop hy)
        ((Etingof.GL2.BorelSubgroup p n).inv_mem b.prop)
    rw [dif_pos hc, dif_pos hy]
    have := Etingof.GL2.borelCharValue_conj p n chi1 chi2 b ⟨y, hy⟩
    rw [← this]
    congr 1
  · have hc : b.val * y * b.val⁻¹ ∉ Etingof.GL2.BorelSubgroup p n := by
      intro hmem
      apply hy
      have : y = b.val⁻¹ * (b.val * y * b.val⁻¹) * b.val := by group
      rw [this]
      exact (Etingof.GL2.BorelSubgroup p n).mul_mem
        ((Etingof.GL2.BorelSubgroup p n).mul_mem
          ((Etingof.GL2.BorelSubgroup p n).inv_mem b.prop) hmem) b.prop
    rw [dif_neg hc, dif_neg hy]

/-- The contribution of the coset representative `r_i` to the Frobenius sum. -/
lemma borelCharExt_cosetRep (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (g : GL2 p n) (i : Option (GaloisField p n)) :
    Etingof.GL2.borelCharExt p n chi1 chi2
        (Etingof.GL2.cosetRep p n i * g * (Etingof.GL2.cosetRep p n i)⁻¹) =
      if Etingof.GL2.cosetIndex p n (Etingof.GL2.cosetRep p n i * g) = i then
        Etingof.GL2.borelCharValue p n chi1 chi2
          (Etingof.GL2.cosetBorel p n (Etingof.GL2.cosetRep p n i * g))
      else 0 := by
  set r := Etingof.GL2.cosetRep p n i with hr
  have hdecomp := Etingof.GL2.cosetBorel_mul_cosetRep p n (r * g)
  by_cases h : Etingof.GL2.cosetIndex p n (r * g) = i
  · rw [if_pos h]
    have hrg : r * g = (Etingof.GL2.cosetBorel p n (r * g)).val * r := by
      conv_lhs => rw [hdecomp]
      rw [h]
    have hb : r * g * r⁻¹ = (Etingof.GL2.cosetBorel p n (r * g)).val := by
      conv_lhs => rw [hrg]
      rw [mul_inv_cancel_right]
    have hmem : r * g * r⁻¹ ∈ Etingof.GL2.BorelSubgroup p n := by
      rw [hb]; exact (Etingof.GL2.cosetBorel p n (r * g)).prop
    rw [Etingof.GL2.borelCharExt, dif_pos hmem]
    congr 1
    exact Subtype.ext hb
  · rw [if_neg h, Etingof.GL2.borelCharExt, dif_neg]
    intro hmem
    apply h
    have h1 := Etingof.GL2.cosetIndex_borel_mul p n
      (⟨r * g * r⁻¹, hmem⟩ : ↥(Etingof.GL2.BorelSubgroup p n)) r
    simp only [inv_mul_cancel_right] at h1
    rw [h1, hr, Etingof.GL2.cosetIndex_cosetRep]

/-- **Frobenius character formula for the principal series** in its raw form: summing the
Borel character (extended by zero) over all of `G` gives `|B|` times the character. -/
theorem sum_borelCharExt_conj
    [Fintype (GL2 p n)] [Fintype ↥(Etingof.GL2.BorelSubgroup p n)]
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (g : GL2 p n) :
    ∑ x : GL2 p n, Etingof.GL2.borelCharExt p n chi1 chi2 (x * g * x⁻¹) =
      (Fintype.card ↥(Etingof.GL2.BorelSubgroup p n) : ℂ) *
        (Etingof.GL2.principalSeries p n chi1 chi2).character g := by
  rw [Etingof.GL2.principalSeries_character_apply]
  rw [← Equiv.sum_comp (Etingof.GL2.borelCosetEquiv p n).symm
    (fun x => Etingof.GL2.borelCharExt p n chi1 chi2 (x * g * x⁻¹))]
  rw [Fintype.sum_prod_type]
  have hstep : ∀ (b : ↥(Etingof.GL2.BorelSubgroup p n)) (i : Option (GaloisField p n)),
      Etingof.GL2.borelCharExt p n chi1 chi2
        ((Etingof.GL2.borelCosetEquiv p n).symm (b, i) * g *
          ((Etingof.GL2.borelCosetEquiv p n).symm (b, i))⁻¹) =
      if Etingof.GL2.cosetIndex p n (Etingof.GL2.cosetRep p n i * g) = i then
        Etingof.GL2.borelCharValue p n chi1 chi2
          (Etingof.GL2.cosetBorel p n (Etingof.GL2.cosetRep p n i * g))
      else 0 := by
    intro b i
    have hx : (Etingof.GL2.borelCosetEquiv p n).symm (b, i) =
        b.val * Etingof.GL2.cosetRep p n i := rfl
    rw [hx]
    have hrw : b.val * Etingof.GL2.cosetRep p n i * g *
        (b.val * Etingof.GL2.cosetRep p n i)⁻¹ =
        b.val * (Etingof.GL2.cosetRep p n i * g * (Etingof.GL2.cosetRep p n i)⁻¹) * b.val⁻¹ := by
      group
    rw [hrw, Etingof.GL2.borelCharExt_conj, Etingof.GL2.borelCharExt_cosetRep]
  simp only [hstep]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Deliverable 1.** The character of the principal series `V(α, 1) = Ind_B^G ℂ_α` is the
Frobenius sum `Etingof.GL2.charVα₁`. -/
theorem character_principalSeries
    [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)]
    (alpha : (GaloisField p n)ˣ →* ℂˣ) (g : GL2 p n) :
    (Etingof.GL2.principalSeries p n alpha 1).character g =
      Etingof.GL2.charVα₁ p n alpha g := by
  classical
  -- The summand of `charVα₁` is the Borel character extended by zero.
  have hsummand : ∀ x : GL2 p n,
      (if ((x⁻¹ * g * x : GL2 p n).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 then
        (if h : ((x⁻¹ * g * x : GL2 p n).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 ≠ 0
          then (alpha (Units.mk0 _ h) : ℂ) else 0)
      else 0) = Etingof.GL2.borelCharExt p n alpha 1 (x⁻¹ * g * x) := by
    intro x
    rw [Etingof.GL2.borelCharExt]
    by_cases hx : (x⁻¹ * g * x : GL2 p n) ∈ Etingof.GL2.BorelSubgroup p n
    · have hx' : ((x⁻¹ * g * x : GL2 p n).val :
          Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := hx
      have h00 := Etingof.GL2.borel_diag00_ne_zero p n ⟨_, hx⟩
      rw [dif_pos hx, if_pos hx', dif_pos h00, Etingof.GL2.borelCharValue]
      simp
    · have hx' : ¬ ((x⁻¹ * g * x : GL2 p n).val :
          Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := hx
      rw [dif_neg hx, if_neg hx']
  -- Move from `x⁻¹ g x` to `x g x⁻¹` and apply the Frobenius formula.
  have hsum : ∑ x : GL2 p n, Etingof.GL2.borelCharExt p n alpha 1 (x⁻¹ * g * x) =
      (Fintype.card ↥(Etingof.GL2.BorelSubgroup p n) : ℂ) *
        (Etingof.GL2.principalSeries p n alpha 1).character g := by
    rw [← Etingof.GL2.sum_borelCharExt_conj p n alpha 1 g]
    exact Fintype.sum_equiv (Equiv.inv (GL2 p n)) _ _ fun x => by simp
  rw [Etingof.GL2.charVα₁]
  simp only [hsummand, hsum]
  have hcard : ((((Fintype.card (GaloisField p n) - 1) ^ 2 *
      Fintype.card (GaloisField p n) : ℕ) : ℂ)) =
      (Fintype.card ↥(Etingof.GL2.BorelSubgroup p n) : ℂ) := by
    rw [Etingof.GL2.card_borelSubgroup]
  rw [hcard, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (Fintype.card_pos (α := ↥(Etingof.GL2.BorelSubgroup p n))).ne'

end Etingof.GL2

end
