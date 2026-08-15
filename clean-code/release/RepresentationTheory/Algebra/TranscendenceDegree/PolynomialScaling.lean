/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.TranscendenceDegree.PolynomialFractionFields
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Polynomial scaling
-/

open MvPolynomial Polynomial Cardinal

namespace RepresentationTheory.Algebra.TranscendenceDegree.PolynomialScaling

/-- The fraction field of a multivariate polynomial ring over a field has transcendence degree equal to the number of variables when the variable type is finite. -/
theorem trdeg_fractionRing_mvPolynomial_eq_card {k : Type} [Field k] (τ : Type) [Fintype τ] :
    Algebra.trdeg k (FractionRing (MvPolynomial τ k)) = (Fintype.card τ : Cardinal) := by
  haveI halg : Algebra.IsAlgebraic (MvPolynomial τ k) (FractionRing (MvPolynomial τ k)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial τ k))
  have hz : Algebra.trdeg (MvPolynomial τ k) (FractionRing (MvPolynomial τ k)) = 0 :=
    trdeg_eq_zero
  have htower := trdeg_add_eq k (MvPolynomial τ k)
    (A := FractionRing (MvPolynomial τ k))
  rw [hz, add_zero, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Cardinal.lift_natCast]
    at htower
  exact htower.symm

/-- Let an infinite field's multivariate polynomial algebra on a finite variable type embed into a field extension. If a unit-indexed family of algebra automorphisms fixes the embedded variables and sends some nonzero element to its scalar multiple by the indexing unit, then every finite cardinal bound on the extension's transcendence degree is strictly larger than the number of source variables. -/
theorem card_lt_of_injective_mvPolynomial_algHom_of_scaled_element_of_fixed_generators
    {k : Type} [Field k] [Infinite k] {σ τ : Type} [Fintype σ] [Fintype τ]
    {K : Type} [Field K] [Algebra k K]
    (f : MvPolynomial σ k →ₐ[k] K) (hf : Function.Injective f)
    (g : K) (hg : g ≠ 0)
    (scale : kˣ → (K ≃ₐ[k] K))
    (hscale_g : ∀ μ : kˣ, scale μ g = (μ : k) • g)
    (hscale_f : ∀ (μ : kˣ) (s : σ), scale μ (f (X s)) = f (X s))
    (htr : Algebra.trdeg k K ≤ (Fintype.card τ : Cardinal)) :
    Fintype.card σ < Fintype.card τ := by
  classical
  have hf_indep : AlgebraicIndependent k (fun s : σ => f (X s)) := by
    simpa [Function.comp_def] using (MvPolynomial.algebraicIndependent_X σ k).map' hf
  set x : σ → K := fun s => f (X s) with hx
  set R' : Subalgebra k K := Algebra.adjoin k (Set.range x) with hR'
  have hfix : ∀ (μ : kˣ) {c : K}, c ∈ R' → scale μ c = c := by
    intro μ c hc
    induction hc using Algebra.adjoin_induction with
    | mem y hy => obtain ⟨s, rfl⟩ := hy; exact hscale_f μ s
    | algebraMap r => exact (scale μ).commutes r
    | add a b _ _ iha ihb => rw [map_add, iha, ihb]
    | mul a b _ _ iha ihb => rw [map_mul, iha, ihb]
  have hRinj : Function.Injective (algebraMap (↥R') K) := Subtype.val_injective
  have htrans : Transcendental (↥R') g := by
    rw [transcendental_iff]
    intro p hp
    set pK : K[X] := p.map (algebraMap (↥R') K) with hpK
    set Q : K[X] := pK.comp (Polynomial.C g * Polynomial.X) with hQ
    have hroot : ∀ μ : kˣ, Q.eval (algebraMap k K (μ : k)) = 0 := by
      intro μ
      have hcomp : (scale μ).toRingHom.comp (algebraMap (↥R') K) = algebraMap (↥R') K := by
        ext c
        exact hfix μ (SetLike.coe_mem c)
      have hzero : scale μ (aeval g p) = 0 := by rw [hp, map_zero]
      have hpush : scale μ (aeval g p)
          = pK.eval ((algebraMap k K (μ : k)) * g) := by
        rw [Polynomial.aeval_def]
        rw [show (scale μ) (Polynomial.eval₂ (algebraMap (↥R') K) g p)
            = (scale μ).toRingHom (Polynomial.eval₂ (algebraMap (↥R') K) g p) from rfl]
        rw [Polynomial.hom_eval₂, hcomp]
        have hg' : (scale μ).toRingHom g = (algebraMap k K (μ : k)) * g := by
          change scale μ g = _
          rw [hscale_g, Algebra.smul_def]
        rw [hg', Polynomial.eval₂_eq_eval_map, ← hpK]
      rw [hzero] at hpush
      have hQeval : Q.eval (algebraMap k K (μ : k))
          = pK.eval ((algebraMap k K (μ : k)) * g) := by
        rw [hQ, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X, mul_comm]
      rw [hQeval, ← hpush]
    have hQ0 : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.infinite_of_injOn_mapsTo (f := algebraMap k K)
        (s := {μ : k | μ ≠ 0}) (t := {z | Q.IsRoot z})
      · exact (algebraMap k K).injective.injOn
      · intro μ hμ
        have := hroot (Units.mk0 μ hμ)
        simpa [Set.mem_setOf_eq, Polynomial.IsRoot.def] using this
      · have : {μ : k | μ ≠ 0} = ({0} : Set k)ᶜ := by ext z; simp
        rw [this]
        exact (Set.finite_singleton (0 : k)).infinite_compl
    have hpK0 : pK = 0 := by
      have hback : pK = Q.comp (Polynomial.C g⁻¹ * Polynomial.X) := by
        rw [hQ, Polynomial.comp_assoc]
        have hsub : (Polynomial.C g * Polynomial.X).comp
            (Polynomial.C g⁻¹ * Polynomial.X) = Polynomial.X := by
          rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc,
            ← Polynomial.C_mul, mul_inv_cancel₀ hg, map_one, one_mul]
        rw [hsub, Polynomial.comp_X]
      rw [hback, hQ0, Polynomial.zero_comp]
    exact (Polynomial.map_eq_zero_iff hRinj).mp hpK0
  have hoption : AlgebraicIndependent k (fun o : Option σ => o.elim g x) :=
    (hf_indep.option_iff_transcendental g).mpr htrans
  have hcard : (#(Option σ) : Cardinal) ≤ Algebra.trdeg k K := hoption.cardinalMk_le_trdeg
  rw [Cardinal.mk_option, Cardinal.mk_fintype σ] at hcard
  have hchain : ((Fintype.card σ : Cardinal) + 1) ≤ (Fintype.card τ : Cardinal) :=
    le_trans hcard htr
  have : (Fintype.card σ + 1 : ℕ) ≤ (Fintype.card τ : ℕ) := by
    exact_mod_cast hchain
  omega

/-- Over an infinite field, suppose a polynomial algebra on a finite variable type embeds into the fraction field of a polynomial algebra on another finite variable type. If algebra automorphisms indexed by scalar units fix all embedded variables while scaling a fixed nonzero fraction by their indexing units, then the source variable type has strictly smaller cardinality than the target variable type. -/
theorem card_lt_of_injective_mvPolynomial_algHom_to_fractionRing_of_scaled_element_of_fixed_generators
    {k : Type} [Field k] [Infinite k] {σ τ : Type} [Fintype σ] [Fintype τ]
    (f : MvPolynomial σ k →ₐ[k] FractionRing (MvPolynomial τ k))
    (hf : Function.Injective f)
    (g : FractionRing (MvPolynomial τ k)) (hg : g ≠ 0)
    (scale : kˣ → (FractionRing (MvPolynomial τ k) ≃ₐ[k] FractionRing (MvPolynomial τ k)))
    (hscale_g : ∀ μ : kˣ, scale μ g = (μ : k) • g)
    (hscale_f : ∀ (μ : kˣ) (s : σ), scale μ (f (X s)) = f (X s)) :
    Fintype.card σ < Fintype.card τ :=
  card_lt_of_injective_mvPolynomial_algHom_of_scaled_element_of_fixed_generators
    f hf g hg scale hscale_g hscale_f
    (le_of_eq (trdeg_fractionRing_mvPolynomial_eq_card τ))

end RepresentationTheory.Algebra.TranscendenceDegree.PolynomialScaling
