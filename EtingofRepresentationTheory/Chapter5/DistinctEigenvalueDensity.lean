import Mathlib

/-!
# The distinct-eigenvalue locus is Zariski-dense in `GL_N(ℂ)`

This file provides the *witness polynomial* for the Zariski-density engine
`MvPolynomial.eq_zero_of_eval_eq_zero_off_zeroLocus`
(`EtingofRepresentationTheory.Chapter5.EvalEqOnGL`): the discriminant of the
characteristic polynomial, viewed as a polynomial `discrPoly N` in the matrix
entries `Xᵢⱼ`. The two pieces required by the assembly of
`trace_combination_vanishes_of_torus_vanishes` (#4925, sub-B #4931) are:

* `Matrix.discrPoly_ne_zero` — `discrPoly N` is a *nonzero* polynomial. The
  witness is a diagonal matrix `diag(0, 1, …, N-1)`, whose characteristic
  polynomial `∏ᵢ (X - i)` is separable, hence has nonzero discriminant.
* `Matrix.charpoly_separable_of_discr_ne_zero` /
  `Matrix.card_roots_charpoly_of_discr_ne_zero` — a matrix with nonzero
  discriminant has separable characteristic polynomial, hence (over `ℂ`)
  exactly `N` distinct eigenvalues.

Feeding `Q = discrPoly N` (after clearing the `det⁻¹` denominator, i.e.
`Q = detPoly · discrPoly`) to the density engine gives "a regular function on
`GL_N(ℂ)` vanishing on every matrix with `N` distinct eigenvalues vanishes on
all of `GL_N`".

The genuine Mathlib gap closed here is `Polynomial.discr_ne_zero_iff_separable`:
Mathlib has the discriminant API (`Polynomial.discr`, `Polynomial.resultant`)
and `Polynomial.Separable` separately, but no link between them. We supply it
through `Polynomial.resultant_deriv` (`discr = ± leadingCoeff⁻¹ · res(f, f')`)
and `Polynomial.resultant_eq_zero_iff`/`resultant_ne_zero`
(`res(f, f') ≠ 0 ↔ IsCoprime f f' = Separable f`).
-/

open Polynomial

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The discriminant commutes with a ring homomorphism on **monic** polynomials.

For monic `f`, `discr f = (-1)^k · resultant f f'`, and both the resultant
(`resultant_map_map`) and the leading coefficient (monic ↦ monic) are preserved
by `φ`, while `natDegree` is preserved because `f` is monic. -/
theorem Monic.discr_map [Nontrivial S] {f : R[X]} (hf : f.Monic) (φ : R →+* S) :
    (f.map φ).discr = φ f.discr := by
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · -- Constant case: a monic polynomial of degree `0` is `1`.
    obtain rfl := eq_one_of_monic_natDegree_zero hf h0
    rw [Polynomial.map_one, show (1 : S[X]).discr = 1 from by rw [← C_1, discr_C],
      show (1 : R[X]).discr = 1 from by rw [← C_1, discr_C], map_one]
  · have hmap_monic : (f.map φ).Monic := hf.map φ
    have hnd : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
    have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
    have hdeg' : 0 < (f.map φ).degree := natDegree_pos_iff_degree_pos.mp (hnd ▸ hpos)
    have e1 := resultant_deriv (f := f) hdeg
    rw [hf.leadingCoeff, mul_one] at e1
    have e2 := resultant_deriv (f := f.map φ) hdeg'
    rw [hmap_monic.leadingCoeff, mul_one, derivative_map, hnd, resultant_map_map, e1] at e2
    rw [map_mul, map_pow, map_neg, map_one] at e2
    -- `(-1)^k` is a unit (its own inverse), so it cancels even though `S` need
    -- not be a domain.
    have hu : IsUnit ((-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2)) :=
      (isUnit_one.neg).pow _
    exact ((hu.mul_right_inj).mp e2).symm

/-- **Discriminant nonvanishing detects separability.** Over a field, for a
polynomial of positive degree whose derivative has the expected degree
`natDegree f - 1` (automatic in characteristic zero), the discriminant is
nonzero iff the polynomial is separable.

The forward direction (`discr ≠ 0 → Separable`) is the genuine Mathlib gap
consumed by the distinct-eigenvalue assembly; the reverse is used to exhibit
the nonvanishing witness. -/
theorem discr_ne_zero_iff_separable {K : Type*} [Field K] {f : K[X]}
    (hpos : 0 < f.natDegree) (hd : f.derivative.natDegree = f.natDegree - 1) :
    f.discr ≠ 0 ↔ f.Separable := by
  have hf0 : f ≠ 0 := fun h => by simp [h] at hpos
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hres := resultant_deriv (f := f) hdeg
  have hunit : ((-1 : K)) ^ (f.natDegree * (f.natDegree - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  -- The default degree arguments of `resultant f f'` agree with the explicit
  -- ones appearing in `resultant_deriv`, using `hd`.
  have hreseq : resultant f f.derivative
      = resultant f f.derivative f.natDegree (f.natDegree - 1) := by rw [hd]
  constructor
  · intro hdiscr
    have hne : resultant f f.derivative ≠ 0 := by
      rw [hreseq, hres]
      exact mul_ne_zero (mul_ne_zero hunit hlc) hdiscr
    rw [separable_def]
    by_contra hcop
    exact hne (resultant_eq_zero_iff.mpr ⟨Or.inl hf0, hcop⟩)
  · intro hsep
    have hcop : IsCoprime f (derivative f) := (separable_def f).mp hsep
    have hne : resultant f f.derivative ≠ 0 := resultant_ne_zero f f.derivative hcop
    rw [hreseq, hres] at hne
    intro hd0
    exact hne (by rw [hd0, mul_zero])

end Polynomial

namespace Matrix

open Polynomial MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- Over a characteristic-zero field, a matrix whose discriminant is nonzero has
separable characteristic polynomial. -/
theorem charpoly_separable_of_discr_ne_zero [CharZero k] (M : Matrix (Fin N) (Fin N) k)
    (hN : 0 < N) (h : M.discr ≠ 0) : M.charpoly.Separable := by
  have hpos : 0 < M.charpoly.natDegree := by
    rw [M.charpoly_natDegree_eq_dim]; simpa using hN
  have hd : M.charpoly.derivative.natDegree = M.charpoly.natDegree - 1 :=
    natDegree_eq_of_degree_eq_some (degree_derivative_eq _ hpos)
  exact (discr_ne_zero_iff_separable hpos hd).mp h

/-- Over a characteristic-zero field, the eigenvalues (roots of the characteristic
polynomial) of a matrix with nonzero discriminant are distinct. -/
theorem charpoly_roots_nodup_of_discr_ne_zero [CharZero k] (M : Matrix (Fin N) (Fin N) k)
    (hN : 0 < N) (h : M.discr ≠ 0) : M.charpoly.roots.Nodup :=
  Polynomial.nodup_roots (charpoly_separable_of_discr_ne_zero M hN h)

/-- Over an algebraically closed characteristic-zero field, a matrix with nonzero
discriminant has exactly `N` distinct eigenvalues. -/
theorem card_roots_charpoly_of_discr_ne_zero [IsAlgClosed k] [CharZero k] [DecidableEq k]
    (M : Matrix (Fin N) (Fin N) k)
    (hN : 0 < N) (h : M.discr ≠ 0) : M.charpoly.roots.toFinset.card = N := by
  rw [Multiset.toFinset_card_of_nodup (charpoly_roots_nodup_of_discr_ne_zero M hN h),
    ← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots, M.charpoly_natDegree_eq_dim,
    Fintype.card_fin]

/-- The discriminant of the characteristic polynomial, as a polynomial in the
matrix entries `Xᵢⱼ`: the evaluation of `discrPoly k N` at a matrix `M` is
`M.discr` (`Matrix.eval_discrPoly`). -/
noncomputable def discrPoly (k : Type*) [Field k] (N : ℕ) : MvPolynomial (Fin N × Fin N) k :=
  (mvPolynomialX (Fin N) (Fin N) k).discr

/-- Evaluating `discrPoly k N` at the entries of a matrix `M` returns `M.discr`. -/
theorem eval_discrPoly (N : ℕ) (x : Fin N × Fin N → k) :
    MvPolynomial.eval x (discrPoly k N) = (Matrix.of fun i j => x (i, j)).discr := by
  set M : Matrix (Fin N) (Fin N) k := Matrix.of fun i j => x (i, j) with hM
  have hMmap : (mvPolynomialX (Fin N) (Fin N) k).map (MvPolynomial.eval x) = M := by
    ext i j
    simp only [Matrix.map_apply, mvPolynomialX_apply, MvPolynomial.eval_X, hM, Matrix.of_apply]
  have hchar : M.charpoly
      = (mvPolynomialX (Fin N) (Fin N) k).charpoly.map (MvPolynomial.eval x) := by
    rw [← hMmap, charpoly_map]
  rw [discrPoly]
  simp only [Matrix.discr]
  rw [hchar, (charpoly_monic _).discr_map (MvPolynomial.eval x)]

/-- **The entry-wise charpoly-discriminant is a nonzero polynomial.** Hence the
distinct-eigenvalue locus is the complement of a proper hypersurface, i.e.
Zariski-dense, in the space of `N × N` matrices. (Characteristic zero is used both
for the witness `diag(0,1,…,N-1)` to have distinct entries and for the derivative
degree to drop by exactly one.) -/
theorem discrPoly_ne_zero [CharZero k] (N : ℕ) (hN : 0 < N) : discrPoly k N ≠ 0 := by
  intro hzero
  set d : Fin N → k := fun i => (i.val : k) with hd
  set x : Fin N × Fin N → k := fun p => if p.1 = p.2 then d p.1 else 0 with hx
  have hM : (Matrix.of fun i j => x (i, j)) = Matrix.diagonal d := by
    ext i j; simp [hx, Matrix.diagonal_apply, Matrix.of_apply]
  have heval : MvPolynomial.eval x (discrPoly k N) = (Matrix.diagonal d).discr := by
    rw [eval_discrPoly, hM]
  rw [hzero, map_zero] at heval
  have hinj : Function.Injective d := by
    intro a b hab
    apply Fin.val_injective
    have : (a.val : k) = (b.val : k) := hab
    exact_mod_cast this
  have hsep : (Matrix.diagonal d).charpoly.Separable := by
    rw [charpoly_diagonal]
    exact separable_prod_X_sub_C_iff.mpr hinj
  have hpos : 0 < (Matrix.diagonal d).charpoly.natDegree := by
    rw [charpoly_natDegree_eq_dim]; simpa using hN
  have hdd : (Matrix.diagonal d).charpoly.derivative.natDegree
      = (Matrix.diagonal d).charpoly.natDegree - 1 :=
    natDegree_eq_of_degree_eq_some (degree_derivative_eq _ hpos)
  have hdisc : (Matrix.diagonal d).discr ≠ 0 := by
    rw [Matrix.discr]
    exact (discr_ne_zero_iff_separable hpos hdd).mpr hsep
  exact hdisc heval.symm

end Matrix
