import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_15_1

/-!
# Remark 5.15.2: the Laurent-polynomial form of the Frobenius character formula

Etingof's Remark 5.15.2 records an equivalent formulation of Theorem 5.15.1:
`χ_{V_λ}(C_i)` is the coefficient of `x^λ` in the **Laurent** polynomial

  `∏_{i < j} (1 - x_j / x_i) · ∏_{m ≥ 1} H_m(x)^{i_m}`.

Theorem 5.15.1 extracts the coefficient of `x^{λ+ρ}` from the honest polynomial
`Δ(x) · ∏_m H_m(x)^{i_m}`. The two agree because

  `Δ(x) = ∏_{i<j} (x_i - x_j) = x^ρ · ∏_{i<j} (1 - x_j / x_i)`,

so dividing by the monomial `x^ρ` shifts the extracted exponent from `λ+ρ` down
to `λ`. The quotient is no longer a polynomial, which is why the remark has to be
stated in a Laurent ring.

## Contents

* `MvLaurent n`: Laurent polynomials in `n` variables over `ℂ`, modelled as the
  group algebra `ℂ[ℤ^n]` of the exponent group `Fin n →₀ ℤ`.
* `toLaurent`: the ring embedding of `MvPolynomial (Fin n) ℂ` into `MvLaurent n`.
* `frobeniusLaurentFactor n`: the factor `∏_{i<j} (1 - x_j / x_i)`.
* `rho_monomial_mul_frobeniusLaurentFactor`: the identity
  `x^ρ · ∏_{i<j}(1 - x_j/x_i) = ∏_{i<j}(x_i - x_j)`, which is the whole content
  of the remark.
* `Remark5_15_2_equiv_Theorem5_15_1`: the two coefficient extractions agree, for
  an arbitrary polynomial factor. This is the "equivalent formulation" claim,
  proved without reference to characters.
* `Remark5_15_2`: the character statement itself, `χ_{V_λ}(σ) = [x^λ] (…)`.

## Sign conventions

`Etingof.vandermondePoly n` is Mathlib-oriented, `∏_{i<j} (x_j - x_i)`, whereas the
book's `Δ` is `∏_{i<j} (x_i - x_j)`; the two differ by `sign(rev)`, which is why
`Theorem5_15_1` carries a `sign(rev) •` factor. That factor cancels here: the book's
`∏_{i<j}(1 - x_j/x_i)` is built from the book's `Δ`, so `Remark5_15_2` is sign-free,
exactly as printed in the book.

As in `Theorem5_15_1`, the book's `H_m` is the power sum `p_m` (Etingof p. 116),
represented by `Etingof.cycleTypePsumProduct`.
-/

namespace Etingof

noncomputable section

open Finset

/-! ## Laurent polynomials in several variables -/

/-- Laurent polynomials in `n` variables over `ℂ`: the group algebra of the exponent
group `Fin n →₀ ℤ`. This is the same construction as `MvPolynomial (Fin n) ℂ`, which is
`AddMonoidAlgebra ℂ (Fin n →₀ ℕ)`, with the exponents allowed to go negative. -/
abbrev MvLaurent (n : ℕ) : Type := AddMonoidAlgebra ℂ (Fin n →₀ ℤ)

namespace MvLaurent

/-- The Laurent monomial `c · x^e` for an integer exponent vector `e`. -/
def monomial {n : ℕ} (e : Fin n →₀ ℤ) (c : ℂ) : MvLaurent n := AddMonoidAlgebra.single e c

/-- The coefficient of `x^e` in a Laurent polynomial. -/
def coeff {n : ℕ} (e : Fin n →₀ ℤ) (f : MvLaurent n) : ℂ :=
  (AddMonoidAlgebra.coeff f) e

/-- The variable `x i`. -/
def X {n : ℕ} (i : Fin n) : MvLaurent n := monomial (Finsupp.single i 1) 1

/-- The inverse variable `x i⁻¹`. This is what takes us outside `MvPolynomial`. -/
def Xinv {n : ℕ} (i : Fin n) : MvLaurent n := monomial (Finsupp.single i (-1)) 1

@[simp] theorem monomial_mul {n : ℕ} (e f : Fin n →₀ ℤ) (c d : ℂ) :
    monomial e c * monomial f d = monomial (e + f) (c * d) := by
  simp only [monomial]
  exact AddMonoidAlgebra.single_mul_single (R := ℂ) (M := Fin n →₀ ℤ) e f c d

@[simp] theorem monomial_zero_one {n : ℕ} : monomial (0 : Fin n →₀ ℤ) 1 = 1 := by
  simp [monomial, AddMonoidAlgebra.one_def]

/-- `x i · x i⁻¹ = 1`: the variables really are invertible. -/
@[simp] theorem X_mul_Xinv {n : ℕ} (i : Fin n) : X i * Xinv i = 1 := by
  rw [X, Xinv, monomial_mul]
  simp

theorem monomial_prod {n : ℕ} (s : Finset (Fin n)) (g : Fin n → (Fin n →₀ ℤ)) :
    ∏ i ∈ s, monomial (g i) (1 : ℂ) = monomial (∑ i ∈ s, g i) 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, monomial_mul, one_mul]

theorem monomial_pow {n : ℕ} (e : Fin n →₀ ℤ) (k : ℕ) :
    monomial e (1 : ℂ) ^ k = monomial (k • e) 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, monomial_mul, succ_nsmul, one_mul]

/-- Multiplying by the monomial `x^e` shifts coefficient extraction by `e`. -/
theorem coeff_monomial_mul {n : ℕ} (e a : Fin n →₀ ℤ) (c : ℂ) (f : MvLaurent n) :
    coeff (e + a) (monomial e c * f) = c * coeff a f := by
  rw [coeff, coeff, monomial, AddMonoidAlgebra.coeff_single_mul_apply]
  simp

end MvLaurent

/-! ## Embedding polynomials into Laurent polynomials -/

/-- The inclusion of `ℕ`-valued exponent vectors into `ℤ`-valued ones. -/
def expEmbed (n : ℕ) : (Fin n →₀ ℕ) →+ (Fin n →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

@[simp] theorem expEmbed_apply (n : ℕ) (e : Fin n →₀ ℕ) (i : Fin n) :
    expEmbed n e i = (e i : ℤ) := by
  simp [expEmbed]

theorem expEmbed_injective (n : ℕ) : Function.Injective (expEmbed n) := by
  intro a b h
  ext i
  have := congrArg (fun f => f i) h
  simpa using this

/-- A polynomial is a Laurent polynomial: the exponents are just reinterpreted in `ℤ`. -/
def toLaurent (n : ℕ) : MvPolynomial (Fin n) ℂ →+* MvLaurent n :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (expEmbed n)

/-- Coefficients are unchanged by `toLaurent`. -/
theorem coeff_toLaurent (n : ℕ) (P : MvPolynomial (Fin n) ℂ) (e : Fin n →₀ ℕ) :
    MvLaurent.coeff (expEmbed n e) (toLaurent n P) = MvPolynomial.coeff e P := by
  change Finsupp.mapDomain (expEmbed n) (AddMonoidAlgebra.coeff P) (expEmbed n e) = _
  rw [Finsupp.mapDomain_apply (expEmbed_injective n)]
  rfl

/-- `toLaurent` is injective, so passing to the Laurent ring loses nothing and the target
is not a degenerate ring. -/
theorem toLaurent_injective (n : ℕ) : Function.Injective (toLaurent n) := by
  intro P Q h
  ext e
  rw [← coeff_toLaurent n P e, ← coeff_toLaurent n Q e, h]

@[simp] theorem toLaurent_X (n : ℕ) (i : Fin n) :
    toLaurent n (MvPolynomial.X i) = MvLaurent.X i := by
  rw [MvPolynomial.X, MvPolynomial.monomial]
  change AddMonoidAlgebra.mapDomain (expEmbed n)
      (AddMonoidAlgebra.single (Finsupp.single i 1) (1 : ℂ)) =
    AddMonoidAlgebra.single (Finsupp.single i 1) (1 : ℂ)
  rw [AddMonoidAlgebra.mapDomain_single]
  congr 1
  ext j
  simp [expEmbed]

/-! ## The book's Vandermonde product and its Laurent factorisation -/

/-- The book's Vandermonde polynomial `Δ(x) = ∏_{i<j} (x_i - x_j)`.

`Etingof.vandermondePoly` uses the opposite factor order, `∏_{i<j} (x_j - x_i)`. -/
def bookVandermondePoly (n : ℕ) : MvPolynomial (Fin n) ℂ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (MvPolynomial.X i - MvPolynomial.X j)

/-- The book's Laurent factor `∏_{i<j} (1 - x_j / x_i)` from Remark 5.15.2. -/
def frobeniusLaurentFactor (n : ℕ) : MvLaurent n :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (1 - MvLaurent.X j * MvLaurent.Xinv i)

/-- `sign(rev)` is `-1` once for each pair `i < j`: reversal inverts every pair. -/
theorem sign_revPerm_eq_prod (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm (n := n)) =
      ∏ i : Fin n, ∏ _j ∈ Finset.Ioi i, (-1 : ℤˣ) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
  have hij : i < j := Finset.mem_Ioi.mp hj
  simp only [Fin.revPerm_apply]
  rw [if_neg (asymm (Fin.rev_lt_rev.mpr hij))]

/-- The cast of `sign(rev)` into any commutative ring, as a product of `-1`s over pairs. -/
theorem cast_sign_revPerm (n : ℕ) (R : Type*) [CommRing R] :
    ((Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) : R) =
      ∏ i : Fin n, ∏ _j ∈ Finset.Ioi i, (-1 : R) := by
  rw [sign_revPerm_eq_prod]
  push_cast
  simp

/-- The book's `Δ` and `Etingof.vandermondePoly` differ by `sign(rev)`. -/
theorem bookVandermondePoly_eq_smul (n : ℕ) :
    bookVandermondePoly n =
      (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) • vandermondePoly n := by
  have hprod : bookVandermondePoly n =
      (∏ i : Fin n, ∏ _j ∈ Finset.Ioi i, (-1 : MvPolynomial (Fin n) ℂ)) * vandermondePoly n := by
    rw [bookVandermondePoly, vandermondePoly, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by ring
  rw [hprod, ← cast_sign_revPerm n (MvPolynomial (Fin n) ℂ), ← zsmul_eq_mul]

/-- `x^ρ` as a Laurent monomial, where `ρ = (n-1, …, 1, 0)`. -/
theorem rhoShift_eq_sum_single (n : ℕ) :
    expEmbed n (rhoShift n) = ∑ i : Fin n, Finsupp.single i (#(Finset.Ioi i) : ℤ) := by
  ext j
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Fin.card_Ioi,
    rhoShift]

/-- `x^ρ = ∏_{i<j} x_i`: the variable `x_i` occurs once for each `j > i`. -/
theorem monomial_rho_eq_prod (n : ℕ) :
    MvLaurent.monomial (expEmbed n (rhoShift n)) 1 =
      ∏ i : Fin n, ∏ _j ∈ Finset.Ioi i, MvLaurent.X i := by
  rw [rhoShift_eq_sum_single, ← MvLaurent.monomial_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_const, MvLaurent.X, MvLaurent.monomial_pow]
  congr 1
  ext j
  simp [Finsupp.single_apply]

/-- **The content of Remark 5.15.2**: multiplying the book's Laurent factor by the
monomial `x^ρ` recovers the book's Vandermonde polynomial `Δ(x) = ∏_{i<j}(x_i - x_j)`.

Dividing `Δ` by `x^ρ` is exactly what turns the `x^{λ+ρ}`-coefficient of Theorem 5.15.1
into the `x^λ`-coefficient of the remark. -/
theorem rho_monomial_mul_frobeniusLaurentFactor (n : ℕ) :
    MvLaurent.monomial (expEmbed n (rhoShift n)) 1 * frobeniusLaurentFactor n =
      toLaurent n (bookVandermondePoly n) := by
  rw [monomial_rho_eq_prod, frobeniusLaurentFactor, ← Finset.prod_mul_distrib]
  rw [bookVandermondePoly, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_sub, toLaurent_X, toLaurent_X, mul_sub, mul_one]
  congr 1
  rw [← mul_assoc, mul_comm (MvLaurent.X i) (MvLaurent.X j), mul_assoc,
    MvLaurent.X_mul_Xinv, mul_one]

/-! ## The two coefficient extractions agree -/

set_option backward.isDefEq.respectTransparency false in
/-- **Remark 5.15.2, equivalence with Theorem 5.15.1.** For any polynomial factor `P`,
the coefficient of `x^e` in `∏_{i<j}(1 - x_j/x_i) · P` equals `sign(rev)` times the
coefficient of `x^{e+ρ}` in `Δ(x) · P`, where `Δ = Etingof.vandermondePoly`.

Both sides are computed here, with no reference to representation theory; this is the
machine-checked form of the book's "here is an equivalent formulation". -/
theorem Remark5_15_2_equiv_Theorem5_15_1 (n : ℕ) (e : Fin n →₀ ℕ)
    (P : MvPolynomial (Fin n) ℂ) :
    MvLaurent.coeff (expEmbed n e) (frobeniusLaurentFactor n * toLaurent n P) =
      (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) •
        MvPolynomial.coeff (e + rhoShift n) (vandermondePoly n * P) := by
  have hsmul : (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) •
      MvPolynomial.coeff (e + rhoShift n) (vandermondePoly n * P) =
      MvPolynomial.coeff (e + rhoShift n)
        (((Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) • vandermondePoly n) * P) := by
    rw [smul_mul_assoc, MvPolynomial.coeff_smul]
  rw [hsmul, ← bookVandermondePoly_eq_smul, ← coeff_toLaurent, map_mul,
    ← rho_monomial_mul_frobeniusLaurentFactor, map_add, mul_assoc,
    add_comm (expEmbed n e) (expEmbed n (rhoShift n)),
    MvLaurent.coeff_monomial_mul, one_mul]

/-- **Remark 5.15.2** (Etingof): the character of the Specht module `V_λ` at a permutation
`σ` of cycle type `i` is the coefficient of `x^λ` in the Laurent polynomial

  `∏_{i<j} (1 - x_j/x_i) · ∏_{m≥1} H_m(x)^{i_m}`.

Unlike `Theorem5_15_1` this carries no sign correction: the book's Laurent factor uses the
book's factor order `∏_{i<j}(x_i - x_j)`, and the resulting `sign(rev)` cancels the one in
`Theorem5_15_1`. -/
theorem Remark5_15_2 (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacter n la σ =
      MvLaurent.coeff (expEmbed n (Nat.Partition.toFinsupp la))
        (frobeniusLaurentFactor n * toLaurent n (cycleTypePsumProduct n σ)) := by
  rw [Remark5_15_2_equiv_Theorem5_15_1, ← Theorem5_15_1, smul_smul]
  simp

end

end Etingof
