import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_21_1

/-!
# Proposition 5.21.2: Schur Polynomials at Geometric Progressions

S_λ(1, z, z², …, z^{N-1}) = ∏_{1 ≤ i < j ≤ N} (z^{λᵢ-i} - z^{λⱼ-j}) / (z^{-i} - z^{-j})

In the limit z → 1 (by L'Hôpital):
S_λ(1, …, 1) = ∏_{1 ≤ i < j ≤ N} (λᵢ - λⱼ + j - i) / (j - i)

## Scope of the first formula

The source works with a complex variable `z`. Schur polynomials are built here with
rational coefficients, so the specialization is stated for an arbitrary characteristic-zero
field `K` (`evalGeometricAt`), with `ℂ` and `ℚ` recorded as corollaries:

* `Proposition5_21_2_geometric_mul` — the cross-multiplied identity, valid for every `z`
  with no nonvanishing hypothesis;
* `Proposition5_21_2_geometric_field` — the quotient form over `K`;
* `Proposition5_21_2_geometric_complex`, `Proposition5_21_2_geometric_complex_zpow` — the
  source's complex setting, the latter in the book's own (negative) integer exponents;
* `Proposition5_21_2_geometric` — the rational case, used for the `z = 1` limit.

## Mathlib correspondence

Uses `MvPolynomial.eval` for evaluation and `Finset.prod` for the product formula.
Schur polynomials are defined in `Proposition5_21_1`.
-/

open Finset MvPolynomial Matrix

noncomputable section

namespace Etingof

/-- Evaluation of an `MvPolynomial` at a geometric progression (1, z, z², …, z^{N-1}). -/
def evalGeometric (N : ℕ) (z : ℚ) : MvPolynomial (Fin N) ℚ →+* ℚ :=
  MvPolynomial.eval (fun i => z ^ (i : ℕ))

/-- Alternant determinant under `evalGeometric` equals a Vandermonde product.
The evaluated alternant matrix is the transpose of a Vandermonde matrix in `z^{e_j}`. -/
private lemma evalGeometric_alternantMatrix_det (N : ℕ) (e : Fin N → ℕ) (z : ℚ) :
    evalGeometric N z (alternantMatrix N e).det =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (z ^ e j - z ^ e i) := by
  rw [RingHom.map_det]
  have h : (evalGeometric N z).mapMatrix (alternantMatrix N e) =
      (vandermonde (fun j : Fin N => z ^ e j))ᵀ := by
    ext i j
    change (evalGeometric N z) ((alternantMatrix N e) i j) = _
    simp only [alternantMatrix, Matrix.of_apply, evalGeometric, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, vandermonde_apply, Matrix.transpose_apply]
    ring
  rw [h, det_transpose, det_vandermonde]

/-- Convert between the double-indexed product `∏ i, ∏ j ∈ Ioi i, f i j` and
the pair-indexed product `∏ p ∈ filter (p.1 < p.2) univ, f p.1 p.2`. -/
private lemma prod_Ioi_eq_prod_filter {M : Type*} [CommMonoid M] {N : ℕ}
    (f : Fin N → Fin N → M) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
      ∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        f p.1 p.2 := by
  rw [← Finset.prod_finset_product']
  intro p
  simp [Finset.mem_filter, Finset.mem_Ioi]

/-- Reversing each difference in a Vandermonde-ordered nested product introduces a
single global sign `(-1)^{#pairs}`. -/
private lemma prod_Ioi_sub_eq_neg_pow_mul {R : Type*} [CommRing R] {N : ℕ} (f : Fin N → R) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (f j - f i)) =
      (-1) ^ (Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ).card *
        ∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
          (f p.1 - f p.2) := by
  rw [prod_Ioi_eq_prod_filter (fun i j => f j - f i)]
  set F := Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ
  conv_lhs => arg 2; ext p; rw [show f p.2 - f p.1 = (-1) * (f p.1 - f p.2) by ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-! ### The geometric specialization over an arbitrary characteristic-zero field

The source states Proposition 5.21.2 for a complex variable `z`. Schur polynomials are
built here with rational coefficients, so the natural home for the specialization is any
field `K` of characteristic zero (equivalently, any field receiving `ℚ`), with `ℂ` and `ℚ`
as instances. -/

/-- Evaluation of a rational-coefficient `MvPolynomial` at the geometric progression
`(1, z, z², …, z^{N-1})`, where `z` ranges over an arbitrary characteristic-zero field.
For `K = ℚ` this is `evalGeometric` (see `evalGeometricAt_rat`). -/
def evalGeometricAt (N : ℕ) (K : Type*) [Field K] [CharZero K] (z : K) :
    MvPolynomial (Fin N) ℚ →+* K :=
  MvPolynomial.eval₂Hom (Rat.castHom K) (fun i : Fin N => z ^ (i : ℕ))

@[simp] lemma evalGeometricAt_rat (N : ℕ) (z : ℚ) :
    evalGeometricAt N ℚ z = evalGeometric N z := by
  have h : (Rat.castHom ℚ) = RingHom.id ℚ := RingHom.ext fun q => Rat.cast_id q
  rw [evalGeometricAt, h]
  rfl

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- Alternant determinant under `evalGeometricAt` equals a Vandermonde product.
The evaluated alternant matrix is the transpose of a Vandermonde matrix in `z^{e_j}`. -/
private lemma evalGeometricAt_alternantMatrix_det (N : ℕ) (e : Fin N → ℕ) (z : K) :
    evalGeometricAt N K z (alternantMatrix N e).det =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (z ^ e j - z ^ e i) := by
  rw [RingHom.map_det]
  have h : (evalGeometricAt N K z).mapMatrix (alternantMatrix N e) =
      (vandermonde (fun j : Fin N => z ^ e j))ᵀ := by
    ext i j
    change (evalGeometricAt N K z) ((alternantMatrix N e) i j) = _
    simp only [alternantMatrix, Matrix.of_apply, evalGeometricAt, map_pow,
      MvPolynomial.eval₂Hom_X', vandermonde_apply, Matrix.transpose_apply]
    ring
  rw [h, det_transpose, det_vandermonde]

/-- Cross-multiplied form of the geometric specialization of Proposition 5.21.2.

This carries no nonvanishing hypothesis: it is the polynomial identity underlying the
displayed quotient, and specializing it is how the quotient forms below are obtained. -/
theorem Proposition5_21_2_geometric_mul (N : ℕ) (lam : Fin N → ℕ) (z : K) :
    evalGeometricAt N K z (schurPoly N lam) *
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) =
      ∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ))) := by
  set F := Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ with hF
  -- Apply the ring hom to the fundamental identity `S_λ · Δ = det(x_i^{λ_j + δ_j})`.
  have h_eval : evalGeometricAt N K z (schurPoly N lam) *
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (z ^ vandermondeExps N j - z ^ vandermondeExps N i)) =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (z ^ shiftedExps N lam j - z ^ shiftedExps N lam i) := by
    rw [← evalGeometricAt_alternantMatrix_det, ← evalGeometricAt_alternantMatrix_det,
      ← map_mul, schurPoly_mul_vandermonde]
  -- Reverse both nested products; the two global signs cancel.
  rw [prod_Ioi_sub_eq_neg_pow_mul (fun j => z ^ vandermondeExps N j),
    prod_Ioi_sub_eq_neg_pow_mul (fun j => z ^ shiftedExps N lam j), ← hF] at h_eval
  have hsign : ((-1 : K)) ^ F.card ≠ 0 := pow_ne_zero _ (by norm_num)
  have h_cancel : evalGeometricAt N K z (schurPoly N lam) *
      (∏ p ∈ F, (z ^ vandermondeExps N p.1 - z ^ vandermondeExps N p.2)) =
      ∏ p ∈ F, (z ^ shiftedExps N lam p.1 - z ^ shiftedExps N lam p.2) :=
    mul_left_cancel₀ hsign (by linear_combination h_eval)
  -- Match the exponents: `vandermondeExps N j = N - 1 - j`, `shiftedExps N lam j = λ_j + N - 1 - j`.
  have hden : (∏ p ∈ F, (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) =
      ∏ p ∈ F, (z ^ vandermondeExps N p.1 - z ^ vandermondeExps N p.2) := rfl
  have hnum :
      (∏ p ∈ F, (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ)))) =
      ∏ p ∈ F, (z ^ shiftedExps N lam p.1 - z ^ shiftedExps N lam p.2) :=
    Finset.prod_congr rfl fun p _ => by
      congr 1 <;> (congr 1; simp only [shiftedExps]; omega)
  rw [hden, hnum]
  exact h_cancel

/-- Schur polynomial at a geometric progression, over any characteristic-zero field:
S_λ(1, z, …, z^{N-1}) = ∏_{i<j} (z^{λᵢ + N - 1 - i} - z^{λⱼ + N - 1 - j}) /
                          ∏_{i<j} (z^{N - 1 - i} - z^{N - 1 - j}).

The hypothesis `hz` is exactly what is needed to interpret the displayed quotient: every
denominator factor is nonzero (it fails only when `z = 0` or `z` is a root of unity of
small order). The product is over pairs `(i, j)` with `i < j` in `Fin N`.
(Etingof Proposition 5.21.2, first part) -/
theorem Proposition5_21_2_geometric_field
    (N : ℕ) (lam : Fin N → ℕ) (z : K)
    (hz : ∀ (i j : Fin N), i < j → z ^ (N - 1 - (i : ℕ)) - z ^ (N - 1 - (j : ℕ)) ≠ 0) :
    evalGeometricAt N K z (schurPoly N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ)))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) := by
  refine (eq_div_iff ?_).mpr (Proposition5_21_2_geometric_mul N lam z)
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact hz p.1 p.2 hp

/-- The source's own exponents. In the book the indices run over `1 ≤ i < j ≤ N`, so the
zero-based index `i : Fin N` carries the exponent `λᵢ - (i+1)`, and the displayed identity
is a ratio of products of `z^{λᵢ - i} - z^{λⱼ - j}` over `z^{-i} - z^{-j}` with *integer*
(in general negative) exponents. This is the literal form of Proposition 5.21.2. -/
theorem Proposition5_21_2_geometric_zpow
    (N : ℕ) (lam : Fin N → ℕ) (z : K) (hz0 : z ≠ 0)
    (hz : ∀ (i j : Fin N), i < j →
      z ^ (-((i : ℕ) : ℤ) - 1) - z ^ (-((j : ℕ) : ℤ) - 1) ≠ 0) :
    evalGeometricAt N K z (schurPoly N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ ((lam p.1 : ℤ) - ((p.1 : ℕ) : ℤ) - 1) -
          z ^ ((lam p.2 : ℤ) - ((p.2 : ℕ) : ℤ) - 1))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (-((p.1 : ℕ) : ℤ) - 1) - z ^ (-((p.2 : ℕ) : ℤ) - 1))) := by
  set F := Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ with hF
  -- Each integer-exponent factor is `z^{-N}` times the corresponding natural-exponent factor.
  have key : ∀ (c : Fin N → ℕ) (p : Fin N × Fin N), p ∈ F →
      z ^ ((c p.1 : ℤ) - ((p.1 : ℕ) : ℤ) - 1) - z ^ ((c p.2 : ℤ) - ((p.2 : ℕ) : ℤ) - 1) =
      z ^ (-(N : ℤ)) *
        (z ^ (c p.1 + N - 1 - (p.1 : ℕ)) - z ^ (c p.2 + N - 1 - (p.2 : ℕ))) := by
    intro c p hp
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have h1 : (p.1 : ℕ) < N := p.1.isLt
    have h2 : (p.2 : ℕ) < N := p.2.isLt
    have e1 : ((c p.1 + N - 1 - (p.1 : ℕ) : ℕ) : ℤ) = (c p.1 : ℤ) - (p.1 : ℕ) - 1 + N := by
      omega
    have e2 : ((c p.2 + N - 1 - (p.2 : ℕ) : ℕ) : ℤ) = (c p.2 : ℤ) - (p.2 : ℕ) - 1 + N := by
      omega
    rw [mul_sub, ← zpow_natCast z (c p.1 + N - 1 - (p.1 : ℕ)),
      ← zpow_natCast z (c p.2 + N - 1 - (p.2 : ℕ)), e1, e2,
      ← zpow_add₀ hz0, ← zpow_add₀ hz0]
    ring_nf
  -- The numerator and denominator both pick up the same factor `(z^{-N})^{#F}`.
  have hnum := Finset.prod_congr rfl (key lam)
  have hden := Finset.prod_congr rfl (key (fun _ => 0))
  simp only [Nat.zero_add, Nat.cast_zero, zero_sub] at hden
  rw [hnum, hden, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    mul_div_mul_left _ _ (pow_ne_zero _ (zpow_ne_zero _ hz0))]
  refine Proposition5_21_2_geometric_field N lam z fun i j hij => ?_
  have hkey := key (fun _ => 0) (i, j) (by simp [hF, hij])
  simp only [Nat.zero_add, Nat.cast_zero, zero_sub] at hkey
  intro h0
  exact hz i j hij (by rw [hkey, h0, mul_zero])

end Field

/-- Schur polynomial at a geometric progression, for rational `z`:
S_λ(1, z, …, z^{N-1}) = ∏_{i<j} (z^{λᵢ + N - 1 - i} - z^{λⱼ + N - 1 - j}) /
                          ∏_{i<j} (z^{N - 1 - i} - z^{N - 1 - j}).

A corollary of `Proposition5_21_2_geometric_field`, kept because the `z = 1` limit
(`Proposition5_21_2_dimension`) is worked out over `ℚ`.
(Etingof Proposition 5.21.2, first part) -/
theorem Proposition5_21_2_geometric
    (N : ℕ) (lam : Fin N → ℕ) (z : ℚ)
    (_hN : 1 ≤ N)
    -- z is not a root of unity (ensures the Vandermonde denominator is nonzero)
    (hz : ∀ (i j : Fin N), i < j → z ^ (N - 1 - (i : ℕ)) - z ^ (N - 1 - (j : ℕ)) ≠ 0) :
    evalGeometric N z (schurPoly N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ)))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) := by
  rw [← evalGeometricAt_rat]
  exact Proposition5_21_2_geometric_field N lam z hz

/-- The source's complex-variable specialization: `S_λ(1, z, …, z^{N-1})` for `z : ℂ`.
(Etingof Proposition 5.21.2, first part) -/
theorem Proposition5_21_2_geometric_complex
    (N : ℕ) (lam : Fin N → ℕ) (z : ℂ)
    (hz : ∀ (i j : Fin N), i < j → z ^ (N - 1 - (i : ℕ)) - z ^ (N - 1 - (j : ℕ)) ≠ 0) :
    evalGeometricAt N ℂ z (schurPoly N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ)))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) :=
  Proposition5_21_2_geometric_field N lam z hz

/-- The source's complex-variable specialization in the book's own integer exponents:
`S_λ(1, z, …, z^{N-1}) = ∏_{i<j} (z^{λᵢ-i} - z^{λⱼ-j}) / (z^{-i} - z^{-j})` for `z : ℂ`.
(Etingof Proposition 5.21.2, first part) -/
theorem Proposition5_21_2_geometric_complex_zpow
    (N : ℕ) (lam : Fin N → ℕ) (z : ℂ) (hz0 : z ≠ 0)
    (hz : ∀ (i j : Fin N), i < j →
      z ^ (-((i : ℕ) : ℤ) - 1) - z ^ (-((j : ℕ) : ℤ) - 1) ≠ 0) :
    evalGeometricAt N ℂ z (schurPoly N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ ((lam p.1 : ℤ) - ((p.1 : ℕ) : ℤ) - 1) -
          z ^ ((lam p.2 : ℤ) - ((p.2 : ℕ) : ℤ) - 1))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (-((p.1 : ℕ) : ℤ) - 1) - z ^ (-((p.2 : ℕ) : ℤ) - 1))) :=
  Proposition5_21_2_geometric_zpow N lam z hz0 hz

/-- Factor `z^a - z^b = (1 - z) * (z^a * ∑ k < b-a, z^k)` for `a ≤ b`. -/
private lemma pow_sub_eq_mul_geom_sum (z : ℚ) {a b : ℕ} (hab : a ≤ b) :
    z ^ a - z ^ b = (1 - z) * (z ^ a * ∑ k ∈ Finset.range (b - a), z ^ k) := by
  have h := geom_sum_mul_neg z (b - a)
  have h2 : z ^ a * (1 - z ^ (b - a)) = z ^ a - z ^ b := by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hab]
  rw [← h2, ← h]; ring

/-- Factor `(1-z)` out of a nested product: `∏ i, ∏ j∈Ioi i, ((1-z)*g i j) = (1-z)^M * ∏∏ g`. -/
private lemma nested_prod_factor_const {N : ℕ} (c : ℚ) (g : Fin N → Fin N → ℚ) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (c * g i j)) =
    c ^ (Finset.univ.sum (fun i : Fin N => (Finset.Ioi i).card)) *
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, g i j) := by
  conv_lhs => arg 2; ext i; rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- The geometric embedding: maps `MvPolynomial (Fin N) ℚ` to `Polynomial ℚ` via `X_i ↦ X^i`. -/
private def geomEmbed (N : ℕ) : MvPolynomial (Fin N) ℚ →ₐ[ℚ] Polynomial ℚ :=
  MvPolynomial.aeval (fun i : Fin N => (Polynomial.X : Polynomial ℚ) ^ (i : ℕ))

private lemma geomEmbed_eval (N : ℕ) (z : ℚ) (p : MvPolynomial (Fin N) ℚ) :
    (geomEmbed N p).eval z = evalGeometric N z p := by
  have h : (Polynomial.evalRingHom z).comp (geomEmbed N).toRingHom =
      (evalGeometric N z : MvPolynomial (Fin N) ℚ →+* ℚ) :=
    MvPolynomial.ringHom_ext
      (fun r => by simp [geomEmbed, evalGeometric, Polynomial.eval_C,
        RingHom.comp_apply])
      (fun i => by simp [geomEmbed, evalGeometric, MvPolynomial.aeval_X, Polynomial.eval_pow,
        Polynomial.eval_X, RingHom.comp_apply])
  exact RingHom.congr_fun h p

/-- Schur polynomial dimension formula (specialization at z = 1):
S_λ(1, …, 1) = ∏_{i<j} (λᵢ - λⱼ + j - i) / (j - i).

This follows from `Proposition5_21_2_geometric` by factoring `(1-z)` from each
Vandermonde factor via geometric sums, cancelling in `Polynomial ℚ` (an integral
domain), and evaluating at `z = 1`.

Here `lam` is a weakly decreasing sequence (partition), so `λᵢ - λⱼ + j - i > 0`
whenever `i < j`.
(Etingof Proposition 5.21.2, second part) -/
theorem Proposition5_21_2_dimension
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    MvPolynomial.eval (fun _ : Fin N => (1 : ℚ)) (schurPoly N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        ((lam p.1 : ℚ) - (lam p.2 : ℚ) + ((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ))) := by
  -- ═══════════════════════════════════════════════════════════════════════
  -- Strategy: Lift the identity schurPoly * vandDet = shiftedDet to Polynomial ℚ
  -- via the geometric embedding X_i ↦ X^i. Factor (1-X) from each Vandermonde
  -- factor using geom_sum. Cancel (1-X)^M in the polynomial integral domain.
  -- Evaluate at X = 1.
  -- ═══════════════════════════════════════════════════════════════════════
  let φ := geomEmbed N
  -- Notation for the pair set
  set F := Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ with hF_def
  -- ── Step 1: eval z ∘ φ = evalGeometric ────────────────────────────────
  -- ── Step 2: eval 1 ∘ φ = eval (fun _ => 1) ───────────────────────────
  have hφ1 : ∀ p : MvPolynomial (Fin N) ℚ,
      Polynomial.eval 1 (φ p) = MvPolynomial.eval (fun _ : Fin N => (1 : ℚ)) p := by
    intro p; rw [geomEmbed_eval]; unfold evalGeometric; simp [one_pow]
  -- ── Step 3: Fundamental identity in Polynomial ℚ ─────────────────────
  have h_fund : φ (schurPoly N lam) * φ (alternantMatrix N (vandermondeExps N)).det =
      φ (alternantMatrix N (shiftedExps N lam)).det := by
    have := congr_arg φ (schurPoly_mul_vandermonde N lam)
    rwa [map_mul] at this
  -- ── Step 4: Fundamental identity at any z ∈ ℚ ────────────────────────
  have h_eval_z : ∀ z : ℚ,
      (φ (schurPoly N lam)).eval z *
        (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (z ^ vandermondeExps N j - z ^ vandermondeExps N i)) =
        (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (z ^ shiftedExps N lam j - z ^ shiftedExps N lam i)) := by
    intro z
    have hv : (φ (alternantMatrix N (vandermondeExps N)).det).eval z =
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (z ^ vandermondeExps N j - z ^ vandermondeExps N i) := by
      rw [geomEmbed_eval, evalGeometric_alternantMatrix_det]
    have hs : (φ (alternantMatrix N (shiftedExps N lam)).det).eval z =
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (z ^ shiftedExps N lam j - z ^ shiftedExps N lam i) := by
      rw [geomEmbed_eval, evalGeometric_alternantMatrix_det]
    have h := congr_arg (Polynomial.eval z) h_fund
    simp only [Polynomial.eval_mul] at h
    rw [hv, hs] at h; exact h
  -- ── Step 5: Define the "cancelled" polynomials ────────────────────────
  -- D = ∏_{i<j} X^{N-1-j} * geom_sum(j-i)  (Vandermonde without (1-X) factors)
  -- Num = ∏_{i<j} X^{sE_j} * geom_sum(sE_i-sE_j)  (shifted without (1-X) factors)
  let D : Polynomial ℚ := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
    (Polynomial.X ^ (N - 1 - (j : ℕ)) *
     ∑ k ∈ Finset.range ((j : ℕ) - (i : ℕ)), Polynomial.X ^ k)
  let Num : Polynomial ℚ := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
    (Polynomial.X ^ (shiftedExps N lam j) *
     ∑ k ∈ Finset.range (shiftedExps N lam i - shiftedExps N lam j), Polynomial.X ^ k)
  -- ── Step 6: Show φ(schurPoly) * D = Num by polynomial extensionality ─
  have h_cancel : φ (schurPoly N lam) * D = Num := by
    -- It suffices to show the difference has infinitely many roots
    suffices h : φ (schurPoly N lam) * D - Num = 0 from sub_eq_zero.mp h
    apply Polynomial.eq_zero_of_infinite_isRoot
    -- The set {z : ℚ | z ≠ 1} is infinite and consists of roots
    apply (Set.Finite.infinite_compl (Set.finite_singleton (1 : ℚ))).mono
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul]
    -- For z ≠ 1, the factored identity holds by algebraic manipulation
    -- Factor each Vandermonde difference: z^a - z^b = (1-z) * (z^a * geom_sum)
    have h_vand : ∀ (i : Fin N) (j : Fin N), j ∈ Finset.Ioi i →
        z ^ vandermondeExps N j - z ^ vandermondeExps N i =
        (1 - z) * (z ^ (N - 1 - (j : ℕ)) *
          ∑ k ∈ Finset.range ((j : ℕ) - (i : ℕ)), z ^ k) := by
      intro i j hj
      have hij := Finset.mem_Ioi.mp hj
      simp only [vandermondeExps]
      have hab : N - 1 - (j : ℕ) ≤ N - 1 - (i : ℕ) := by omega
      have heq : (N - 1 - (i : ℕ)) - (N - 1 - (j : ℕ)) = (j : ℕ) - (i : ℕ) := by omega
      rw [← heq]; exact pow_sub_eq_mul_geom_sum z hab
    -- Factor each shifted difference similarly
    have h_shift : ∀ (i : Fin N) (j : Fin N), j ∈ Finset.Ioi i →
        z ^ shiftedExps N lam j - z ^ shiftedExps N lam i =
        (1 - z) * (z ^ shiftedExps N lam j *
          ∑ k ∈ Finset.range (shiftedExps N lam i - shiftedExps N lam j), z ^ k) := by
      intro i j hj
      have hij := Finset.mem_Ioi.mp hj
      have h_lam : lam j ≤ lam i := hlam (by omega : (i : ℕ) ≤ (j : ℕ))
      have hab : shiftedExps N lam j ≤ shiftedExps N lam i := by
        simp only [shiftedExps]; omega
      exact pow_sub_eq_mul_geom_sum z hab
    -- Rewrite the fundamental identity using these factorizations
    have h_vand_prod : ∀ (i : Fin N),
        ∏ j ∈ Finset.Ioi i, (z ^ vandermondeExps N j - z ^ vandermondeExps N i) =
        ∏ j ∈ Finset.Ioi i,
          ((1 - z) * (z ^ (N - 1 - (j : ℕ)) *
            ∑ k ∈ Finset.range ((j : ℕ) - (i : ℕ)), z ^ k)) := by
      intro i; apply Finset.prod_congr rfl; intro j hj; exact h_vand i j hj
    have h_shift_prod : ∀ (i : Fin N),
        ∏ j ∈ Finset.Ioi i, (z ^ shiftedExps N lam j - z ^ shiftedExps N lam i) =
        ∏ j ∈ Finset.Ioi i,
          ((1 - z) * (z ^ shiftedExps N lam j *
            ∑ k ∈ Finset.range (shiftedExps N lam i - shiftedExps N lam j), z ^ k)) := by
      intro i; apply Finset.prod_congr rfl; intro j hj; exact h_shift i j hj
    -- Set M = number of pairs
    set M := Finset.univ.sum (fun i : Fin N => (Finset.Ioi i).card) with hM_def
    -- Rewrite the fundamental identity
    have h_factored := h_eval_z z
    simp_rw [h_vand_prod] at h_factored
    simp_rw [h_shift_prod] at h_factored
    rw [nested_prod_factor_const] at h_factored
    rw [nested_prod_factor_const] at h_factored
    -- Now h_factored : eval * ((1-z)^M * D_eval) = (1-z)^M * Num_eval
    -- Cancel (1-z)^M (nonzero since z ≠ 1)
    have h1z : (1 - z) ^ M ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hz))
    -- h_factored is about ℚ values; D and Num are Polynomial objects, but eval z D matches
    -- Relate eval z D to the ℚ product
    have hD_eval : D.eval z = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (z ^ (N - 1 - (j : ℕ)) * ∑ k ∈ Finset.range ((j : ℕ) - (i : ℕ)), z ^ k) := by
      simp only [D, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_finsetSum]
    have hNum_eval : Num.eval z = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (z ^ shiftedExps N lam j *
          ∑ k ∈ Finset.range (shiftedExps N lam i - shiftedExps N lam j), z ^ k) := by
      simp only [Num, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_finsetSum]
    rw [← hD_eval, ← hNum_eval] at h_factored
    -- h_factored : eval z (φ schurPoly) * ((1-z)^M * D.eval z) = (1-z)^M * Num.eval z
    have h_cancel' : (φ (schurPoly N lam)).eval z * D.eval z = Num.eval z := by
      have h2 : (1 - z) ^ M * ((φ (schurPoly N lam)).eval z * D.eval z) =
          (1 - z) ^ M * Num.eval z := by linear_combination h_factored
      exact mul_left_cancel₀ h1z h2
    linarith
  -- ── Step 7: Evaluate at z = 1 ────────────────────────────────────────
  have h_at_1 : (φ (schurPoly N lam)).eval 1 * D.eval 1 = Num.eval 1 := by
    have := congr_arg (Polynomial.eval (1 : ℚ)) h_cancel
    simp only [Polynomial.eval_mul] at this
    exact this
  -- ── Step 8: Compute D.eval 1 and Num.eval 1 ──────────────────────────
  have hD1 : D.eval 1 = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      ((j : ℕ) - (i : ℕ) : ℚ) := by
    simp only [D, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow, one_mul, Polynomial.eval_finsetSum]
    apply Finset.prod_congr rfl; intro i _
    apply Finset.prod_congr rfl; intro j hj
    have hij : (i : ℕ) ≤ (j : ℕ) := (Finset.mem_Ioi.mp hj).le
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_sub hij]
  have hNum1 : Num.eval 1 = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (shiftedExps N lam i - shiftedExps N lam j : ℚ) := by
    simp only [Num, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow, one_mul, Polynomial.eval_finsetSum]
    apply Finset.prod_congr rfl; intro i _
    apply Finset.prod_congr rfl; intro j hj
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hij := Finset.mem_Ioi.mp hj
    exact Nat.cast_sub (by simp only [shiftedExps]; have := hlam (le_of_lt hij); omega)
  -- ── Step 9: Denominator is nonzero ────────────────────────────────────
  have hD1_ne : D.eval 1 ≠ 0 := by
    rw [hD1]
    apply Finset.prod_ne_zero_iff.mpr; intro i _
    apply Finset.prod_ne_zero_iff.mpr; intro j hj
    have hij := Finset.mem_Ioi.mp hj
    exact ne_of_gt (sub_pos.mpr (Nat.cast_lt.mpr hij))
  -- ── Step 10: Derive the formula ───────────────────────────────────────
  -- Convert Ioi products to filter products for D.eval 1
  have hD1_filter : D.eval 1 =
      ∏ p ∈ F, (((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ)) := by
    rw [hD1, prod_Ioi_eq_prod_filter]
  -- Convert Ioi products to filter products for Num.eval 1
  have hNum1_filter : Num.eval 1 =
      ∏ p ∈ F, ((lam p.1 : ℚ) - (lam p.2 : ℚ) + ((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ)) := by
    rw [hNum1, prod_Ioi_eq_prod_filter]
    apply Finset.prod_congr rfl; intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [shiftedExps]
    have h_lam : lam p.2 ≤ lam p.1 := hlam (by omega : (p.1 : ℕ) ≤ (p.2 : ℕ))
    push_cast
    rw [Nat.cast_sub (by omega : (p.1 : ℕ) ≤ N - 1)]
    rw [Nat.cast_sub (by omega : (p.2 : ℕ) ≤ N - 1)]
    rw [Nat.cast_sub (by omega)]
    ring
  -- Denominator is nonzero (in filter form)
  have hD1_filter_ne : (∏ p ∈ F, (((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ))) ≠ 0 := by
    rw [← hD1_filter]; exact hD1_ne
  -- From h_at_1: eval schurPoly = Num / D
  rw [← hφ1, eq_div_iff hD1_filter_ne, ← hNum1_filter, ← hD1_filter, ← h_at_1]

end Etingof
