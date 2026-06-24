import Mathlib
import EtingofRepresentationTheory.Chapter5.CauchyDetQuotient
import EtingofRepresentationTheory.Chapter5.SimpleSubrepExtraction

/-!
# Assembly of the kernel lemma (K′)

This file discharges the genuine research-level core of the det⁻¹-elimination
kernel lemma (K′) by assembling the pieces built in sibling files:

* the **simple-constituent extraction** keystone
  `exists_simple_subrep_of_quotDetRep` (`SimpleSubrepExtraction.lean`, issue #4922):
  every nonzero `GL_N`-invariant submodule of `A/det = k[Xᵢⱼ]/(det)` contains a
  simple finite-dimensional constituent `L` with an injective equivariant
  `φ : L →ₗ[k] A/det`;
* the **`ν_N = 0` Cauchy content**
  `quotDetRep_irreducible_constituent_lastWeight_zero` (`CauchyDetQuotient.lean`,
  issue #4896 part (a)): such an `L` has `formalCharacter k N L = schurPoly N ν`
  for an antitone `ν` with `(0 : ℕ) ∈ Set.range ν`;
* the **twist weight-shift** `glWeightSpaceℤ_quotDetTwist` and the elementary
  glue `glWeightSpaceℤ_neg_not_mem_nonneg_span` (`KernelLemmaKPrime.lean`).

Because `CauchyDetQuotient` and `SimpleSubrepExtraction` both *import*
`KernelLemmaKPrime`, the assembly cannot live in `KernelLemmaKPrime.lean` itself
(it would create an import cycle). It is therefore collected here, together with
the two downstream consumers `kernelLemmaK'` and `kernelLemmaK'_submodule` that
depend on it.

## The assembly (issue #4923)

`quotDetTwist_nonzero_subrep_has_neg_weight`: for `r ≥ 1`, every *nonzero*
subrepresentation `W` of the twist `(A/det) ⊗ χ⁻ʳ` contains a nonzero torus-weight
vector whose weight has a negative coordinate. The argument:

1. **Untwist `W`.** The character twist `χ⁻ʳ` only rescales each `g`-action by the
   nonzero scalar `det(g)⁻ʳ`, so `W.toSubmodule` is `quotDetRep`-invariant.
2. **Extract a simple constituent** `L`, `φ` from `W.toSubmodule` (#4922).
3. **`ν_N = 0`** from part (a): `formalCharacter k N L = schurPoly N ν` with
   `0 ∈ Set.range ν`.
4. **Highest-weight vector.** `finrank (glWeightSpace k N L ν) =
   (schurPoly N ν).coeff ν ≠ 0` (the highest weight occurs with multiplicity one,
   `schurPoly_coeff_self_ne_zero`), so there is a nonzero weight-`ν` vector `w`.
5. **Push through `φ`.** `φ w ∈ W.toSubmodule`, `φ w ≠ 0`, and equivariance places
   `φ w` in `glWeightSpaceℤ k N (quotDetRep k N) (↑ν)`.
6. **Twist shift.** `glWeightSpaceℤ_quotDetTwist` with `μ = ↑ν − r` lands `φ w` in
   `glWeightSpaceℤ k N (quotDetTwistRep k N r) (↑ν − r)`, whose coordinate at an
   index where `ν = 0` is `0 − r = −r < 0`.
-/

noncomputable section

open MvPolynomial Etingof Etingof.PolynomialGLAction

namespace Etingof.KernelLemmaKPrime

variable {k : Type} [Field k] {N : ℕ}

/-! ### The genuine core of (K′)

The highest-weight multiplicity-one coefficient `x^λ` of `schurPoly N λ` is
nonzero (the Kostka number `K_{λλ} = 1`); this is `Etingof.schurPoly_coeff_self_ne_zero`
(`Proposition5_21_1.lean`, issue #4949), used directly in step 4 below. -/

/-- **The genuine core of (K′).** For `r ≥ 1`, every *nonzero* subrepresentation
`W` of the twisted quotient `(A/det) ⊗ χ⁻ʳ` contains a nonzero torus-weight vector
whose weight has a negative coordinate.

Assembled from the simple-constituent extraction (#4922), the `ν_N = 0` Cauchy
content (#4896 part (a)), and the twist weight-shift. -/
theorem quotDetTwist_nonzero_subrep_has_neg_weight (k : Type) [Field k]
    [IsAlgClosed k] [CharZero k] (N : ℕ) (r : ℕ) (hr : 1 ≤ r)
    (W : Subrepresentation (quotDetTwistRep k N r)) (hW : W ≠ ⊥) :
    ∃ μ : Fin N → ℤ, (∃ i, μ i < 0) ∧
      ∃ v ∈ W.toSubmodule, v ≠ 0 ∧
        v ∈ glWeightSpaceℤ k N (quotDetTwistRep k N r) μ := by
  classical
  -- `W.toSubmodule` is nonzero.
  have hW₀ne : W.toSubmodule ≠ ⊥ := by
    intro h
    -- v4.31: `simpa` no longer normalizes `⊥.toSubmodule` to `⊥`, but they are defeq,
    -- so `exact h` closes the `W.toSubmodule = ⊥.toSubmodule` goal directly.
    exact hW (Subrepresentation.toSubmodule_injective h)
  -- The scalar attached to the twist is nonzero.
  -- `W.toSubmodule` is `quotDetRep`-invariant: the twist only rescales by a unit.
  have hW_inv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ w ∈ W.toSubmodule, quotDetRep k N g w ∈ W.toSubmodule := by
    intro g w hw
    set c : kˣ := (detChar k N ^ (-(r : ℤ))) g with hc
    have htwist : quotDetTwistRep k N r g w = (c : k) • quotDetRep k N g w := rfl
    have hmem : quotDetTwistRep k N r g w ∈ W.toSubmodule :=
      W.apply_mem_toSubmodule g hw
    have hcc1 : ((c⁻¹ : kˣ) : k) * ((c : k)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have : quotDetRep k N g w = ((c⁻¹ : kˣ) : k) • quotDetTwistRep k N r g w := by
      rw [htwist, smul_smul, hcc1, one_smul]
    rw [this]
    exact W.toSubmodule.smul_mem _ hmem
  -- Extract a simple constituent `L`, `φ` with image inside `W.toSubmodule`.
  obtain ⟨L, φ, hLsimp, hφ_inj, hφ_equiv, hφ_range⟩ :=
    exists_simple_subrep_of_quotDetRep k N hW_inv hW₀ne
  -- `ν_N = 0` from part (a).
  obtain ⟨ν, hν_anti, hν_zero, hν_char⟩ :=
    quotDetRep_irreducible_constituent_lastWeight_zero k N L hLsimp φ hφ_inj hφ_equiv
  -- An index `i₀` with `ν i₀ = 0`.
  obtain ⟨i₀, hi₀⟩ := hν_zero
  -- The highest-weight space is nonzero.
  have hcoeff : (schurPoly N ν).coeff (Finsupp.equivFunOnFinite.symm ν) ≠ 0 :=
    Etingof.schurPoly_coeff_self_ne_zero N ν hν_anti
  have hfin_ne : Module.finrank k
      (glWeightSpace k N L (fun i => (Finsupp.equivFunOnFinite.symm ν) i)) ≠ 0 := by
    have hcc := formalCharacter_coeff k N L (Finsupp.equivFunOnFinite.symm ν)
    rw [hν_char] at hcc
    intro h
    rw [h] at hcc
    simp only [Nat.cast_zero] at hcc
    exact hcoeff hcc
  have hfun : (fun i => (Finsupp.equivFunOnFinite.symm ν) i) = ν := rfl
  rw [hfun] at hfin_ne
  have hws_ne : glWeightSpace k N L ν ≠ ⊥ := by
    intro h
    apply hfin_ne
    rw [h]
    simp
  obtain ⟨w, hwmem, hw0⟩ := (Submodule.ne_bot_iff _).mp hws_ne
  -- `w` is a weight-`ν` vector: `L.ρ (diagUnit i t) w = (t : k) ^ ν i • w`.
  have hw_wt : ∀ (i : Fin N) (t : kˣ),
      L.ρ (diagUnit k N i t) w = ((t : k) ^ ν i) • w := by
    intro i t
    have hk : w ∈ LinearMap.ker
        (L.ρ (diagUnit k N i t) - ((t : k) ^ ν i) • LinearMap.id) :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hwmem i) t
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hk
    exact hk
  -- Push `w` through `φ`.
  set v : MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N := φ w with hv
  have hvmem : v ∈ W.toSubmodule := hφ_range ⟨w, rfl⟩
  have hv0 : v ≠ 0 := by
    rw [hv]
    intro hh
    exact hw0 (hφ_inj (hh.trans (map_zero φ).symm))
  -- `v` lies in the integer weight space of `quotDetRep` at `↑ν`.
  have hv_wt : v ∈ glWeightSpaceℤ k N (quotDetRep k N) (fun i => (ν i : ℤ)) := by
    rw [glWeightSpaceℤ]
    refine (Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun t => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
    have hcast : (((t ^ (ν i : ℤ) : kˣ) : k)) = (t : k) ^ ν i := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hcast, hv, ← hφ_equiv, hw_wt i t, map_smul]
  -- Apply the twist shift with `μ = ↑ν − r`.
  refine ⟨fun i => (ν i : ℤ) - r, ⟨i₀, by simp only [hi₀]; omega⟩, v, hvmem, hv0, ?_⟩
  rw [glWeightSpaceℤ_quotDetTwist k N r (fun i => (ν i : ℤ) - r)]
  have hshift : (fun i => (ν i : ℤ) - r + r) = (fun i => (ν i : ℤ)) := by
    funext i; ring
  rw [hshift]
  exact hv_wt

/-! ### The kernel lemma (K′) -/

/-- **Kernel lemma (K′).** For `r ≥ 1`, every right-`GL_N`-**subrepresentation**
`W` of the twisted quotient `(A/det) ⊗ χ⁻ʳ` all of whose right-torus weights are
nonnegative is `⊥`.

By the core `quotDetTwist_nonzero_subrep_has_neg_weight`, a nonzero such `W` would
contain a negative-weight vector, contradicting the glue lemma
`glWeightSpaceℤ_neg_not_mem_nonneg_span`. -/
theorem kernelLemmaK' (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)
    (r : ℕ) (hr : 1 ≤ r) (W : Subrepresentation (quotDetTwistRep k N r))
    (hW : W.toSubmodule ≤ ⨆ (μ : Fin N → ℕ),
      glWeightSpaceℤ k N (quotDetTwistRep k N r) (fun i => (μ i : ℤ))) :
    W = ⊥ := by
  by_contra hne
  obtain ⟨μ, hμneg, v, hvW, hv0, hvμ⟩ :=
    quotDetTwist_nonzero_subrep_has_neg_weight k N r hr W hne
  exact glWeightSpaceℤ_neg_not_mem_nonneg_span k N r μ hμneg hv0 hvμ (hW hvW)

/-- Consumable form of (K′): every `GL_N`-**invariant** submodule of
`(A/det) ⊗ χ⁻ʳ` all of whose torus weights lie in `ℕ^N` is `⊥`.

The `GL_N`-invariance hypothesis `hW_inv` is essential — without it the statement
is false (see the note on `kernelLemmaK'` in `KernelLemmaKPrime.lean`). -/
theorem kernelLemmaK'_submodule (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N : ℕ) (r : ℕ) (hr : 1 ≤ r)
    {W : Submodule k (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N)}
    (hW_inv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ w ∈ W, quotDetTwistRep k N r g w ∈ W)
    (hW : W ≤ ⨆ (μ : Fin N → ℕ),
      glWeightSpaceℤ k N (quotDetTwistRep k N r) (fun i => (μ i : ℤ))) :
    W = ⊥ := by
  let W' : Subrepresentation (quotDetTwistRep k N r) :=
    ⟨W, fun g _ hw => hW_inv g _ hw⟩
  have hW'bot : W' = ⊥ := kernelLemmaK' k N r hr W' hW
  have : W'.toSubmodule = (⊥ : Subrepresentation (quotDetTwistRep k N r)).toSubmodule :=
    congrArg Subrepresentation.toSubmodule hW'bot
  -- v4.31: `simpa` leaves `⊥.toSubmodule` unreduced; `W'.toSubmodule` is defeq `W` and
  -- `⊥.toSubmodule` is defeq `⊥`, so `exact this` closes the `W = ⊥` goal.
  exact this

end Etingof.KernelLemmaKPrime

end
