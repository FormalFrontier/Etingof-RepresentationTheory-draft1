import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.FreeAlgebra
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod

/-!
# Problem 2.8.11: Hilbert series of graded algebras

For a `ℤ₊`-graded algebra `A = ⨁ₙ A[n]` with each `A[n]` finite dimensional, the **Hilbert
series** is `h_A(t) = ∑ₙ (dim A[n]) tⁿ`. The problem asks for the Hilbert series of four
graded algebras. We render the book's *answers* — the closed rational functions — as the
statement (spec). Each is captured two ways: the closed formula for the graded dimension
`dim A[n]` (the coefficient of `tⁿ`), and, where clean, the closed rational form of the
generating function `h_A` as a formal power series identity.

The four answers (Etingof Problem 2.8.11):

* (a) `A = k[x₁,…,x_m]`, graded by degree: `h_A(t) = 1/(1-t)^m`, i.e. `dim A[n] = C(n+m-1, m-1)`.
* (b) `A = k⟨x₁,…,x_m⟩` (free algebra), graded by word length: `h_A(t) = 1/(1-mt)`,
  i.e. `dim A[n] = mⁿ`.
* (c) `A = ⋀_k[x₁,…,x_m]` (exterior algebra), graded by degree: `h_A(t) = (1+t)^m`,
  i.e. `dim A[n] = C(m, n)`.
* (d) `A = P_Q` (path algebra), `deg pᵢ = 0`, `deg a_h = 1`: `dim A[n]` is the number of paths
  of length `n`, i.e. the `(i,j)`-entry of `M_Q^n` summed over `i, j`, where `M_Q` is the
  adjacency matrix. The generating function is `∑ₙ (𝟙ᵀ M_Q^n 𝟙) tⁿ = 𝟙ᵀ (I - t M_Q)⁻¹ 𝟙`.

These are statement-only (proofs deferred to a later phase).
-/

namespace Etingof.Problem2_8_11

open scoped ExteriorAlgebra

/-! ## (a) Polynomial algebra `k[x₁,…,x_m]` -/

/-- **(a)** The degree-`n` graded piece of `k[x₁,…,x_m]` has dimension `C(n+m-1, m-1)`, the number
of monomials of degree `n` in `m` variables. Equivalently the Hilbert series is `1/(1-t)^m`. -/
theorem finrank_homogeneous_mvPolynomial (k : Type*) [Field k] (m n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin m) k n) = (n + m - 1).choose (m - 1) :=
  sorry

/-- **(a)**, generating-function form: the Hilbert series of `k[x₁,…,x_m]` is `1/(1-t)^m`,
expressed as the power-series identity `(1 - t)^m · h_A = 1`. -/
theorem hilbertSeries_mvPolynomial (k : Type*) [Field k] (m : ℕ) :
    (1 - PowerSeries.X : PowerSeries k) ^ m *
      PowerSeries.mk (fun n => ((n + m - 1).choose (m - 1) : k)) = 1 :=
  sorry

/-! ## (b) Free algebra `k⟨x₁,…,x_m⟩` -/

/-- **(b)** The number of words of length `n` in `m` letters is `mⁿ`; this is the dimension of the
length-`n` graded piece of the free algebra `k⟨x₁,…,x_m⟩` (whose basis is the set of words).
Equivalently the Hilbert series is `1/(1-mt)`. -/
theorem card_words_length (m n : ℕ) :
    Nat.card {l : List (Fin m) // l.length = n} = m ^ n := by
  -- A length-`n` word over `Fin m` is exactly a `List.Vector (Fin m) n`, equivalent to
  -- `Fin n → Fin m`, of which there are `mⁿ`.
  have e : {l : List (Fin m) // l.length = n} ≃ (Fin n → Fin m) :=
    Equiv.vectorEquivFin (Fin m) n
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

/-- **(b)**, generating-function form: the Hilbert series of `k⟨x₁,…,x_m⟩` is `1/(1-mt)`,
expressed as the power-series identity `(1 - m·t) · h_A = 1`. -/
theorem hilbertSeries_freeAlgebra (k : Type*) [Field k] (m : ℕ) :
    (1 - (m : ℕ) • PowerSeries.X : PowerSeries k) *
      PowerSeries.mk (fun n => ((m ^ n : ℕ) : k)) = 1 := by
  -- Geometric series `(1 - m·X)·∑ mⁿ Xⁿ = 1`, checked coefficient by coefficient.
  ext d
  rw [sub_mul, one_mul, smul_mul_assoc, map_sub, map_nsmul, PowerSeries.coeff_mk,
    PowerSeries.coeff_one]
  rcases d with _ | e
  · -- constant coefficient: `m⁰ - m·(coeff₀ (X·h)) = 1 - 0 = 1`
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · -- coefficient of `t^(e+1)`: `m^(e+1) - m·m^e = 0`
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, nsmul_eq_mul]
    push_cast [pow_succ]
    ring

/-! ## (c) Exterior (Grassmann) algebra `⋀_k[x₁,…,x_m]` -/

/-- **(c)** The degree-`n` graded piece of the exterior algebra on `m` generators is the `n`-th
exterior power of the `m`-dimensional space, of dimension `C(m, n)`. Equivalently the Hilbert
series is `(1+t)^m`. -/
theorem finrank_exteriorPower (k : Type*) [Field k] (m n : ℕ) :
    Module.finrank k (⋀[k]^n (Fin m → k)) = m.choose n := by
  -- `⋀^n` of a rank-`m` free module has rank `C(m, n)`; here `finrank k (Fin m → k) = m`.
  rw [exteriorPower.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- **(c)**, generating-function form: the Hilbert series of the exterior algebra on `m`
generators is the polynomial `(1+t)^m`. -/
theorem hilbertSeries_exteriorAlgebra (k : Type*) [Field k] (m : ℕ) :
    PowerSeries.mk (fun n => ((m.choose n : ℕ) : k)) = (1 + PowerSeries.X : PowerSeries k) ^ m := by
  -- Coerce the polynomial identity `((1 + X)^m).coeff n = C(m, n)` to power series and match
  -- coefficients: `(1 + X)^m` as a power series is the coercion of the polynomial `(1 + X)^m`.
  have hcoe : ((1 + PowerSeries.X : PowerSeries k) ^ m) =
      ((((1 + Polynomial.X) ^ m : Polynomial k) : PowerSeries k)) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [hcoe]
  ext n
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-! ## (d) Path algebra `P_Q` -/

/-- The adjacency matrix of a finite quiver `Q`: the `(i,j)`-entry is the number of arrows
`i ⟶ j`. -/
def adjacencyMatrix (Q : Type*) [Quiver Q] [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)] :
    Matrix Q Q ℕ :=
  fun i j => Fintype.card (i ⟶ j)

/-- A path of length `n + 1` from `i` to `j` decomposes uniquely as a length-`n` path
`i ⟶* b` followed by a final arrow `b ⟶ j` (matching the `Matrix.mul_apply` decomposition of
`M_Q ^ (n+1) = M_Q ^ n * M_Q`). -/
def pathSuccEquiv {Q : Type*} [Quiver Q] (i j : Q) (n : ℕ) :
    {p : Quiver.Path i j // p.length = n + 1} ≃
      Σ b : Q, {p : Quiver.Path i b // p.length = n} × (b ⟶ j) where
  toFun p := by
    obtain ⟨p, h⟩ := p
    cases p with
    | nil => simp [Quiver.Path.length_nil] at h
    | cons p' e => exact ⟨_, ⟨p', by rw [Quiver.Path.length_cons] at h; omega⟩, e⟩
  invFun x := ⟨x.2.1.1.cons x.2.2, by rw [Quiver.Path.length_cons, x.2.1.2]⟩
  left_inv p := by
    obtain ⟨p, h⟩ := p
    cases p with
    | nil => simp [Quiver.Path.length_nil] at h
    | cons p' e => rfl
  right_inv x := by
    obtain ⟨b, ⟨p', hp'⟩, e⟩ := x
    rfl

/-- The set of paths of a fixed length between two vertices of a finite quiver is finite. -/
instance instFinitePathLen {Q : Type*} [Quiver Q] [Finite Q] [∀ i j : Q, Finite (i ⟶ j)]
    (i j : Q) (n : ℕ) : Finite {p : Quiver.Path i j // p.length = n} := by
  induction n generalizing j with
  | zero =>
    haveI : Subsingleton {p : Quiver.Path i j // p.length = 0} := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨p, hp⟩ := a
      obtain ⟨q, hq⟩ := b
      have hij : i = j := Quiver.Path.eq_of_length_zero p hp
      subst hij
      rw [Subtype.mk_eq_mk, Quiver.Path.eq_nil_of_length_zero p hp,
        Quiver.Path.eq_nil_of_length_zero q hq]
    exact Finite.of_injective (fun _ => (0 : Fin 1)) fun a b _ => Subsingleton.elim a b
  | succ n ih =>
    haveI : ∀ b : Q, Finite {p : Quiver.Path i b // p.length = n} := ih
    exact Finite.of_equiv _ (pathSuccEquiv i j n).symm

/-- **(d)** The number of paths of length `n` from `i` to `j` in a finite quiver equals the
`(i,j)`-entry of the `n`-th power of the adjacency matrix. This is the graded-piece dimension of
the path algebra: the closed answer to the Hilbert series in terms of `M_Q`. -/
theorem card_paths_length_eq_adjacencyMatrix_pow (Q : Type*) [Quiver Q] [Fintype Q]
    [DecidableEq Q] [∀ i j : Q, Fintype (i ⟶ j)] (i j : Q) (n : ℕ) :
    Nat.card {p : Quiver.Path i j // p.length = n} = (adjacencyMatrix Q ^ n) i j := by
  induction n generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      haveI : Nonempty {p : Quiver.Path i i // p.length = 0} :=
        ⟨⟨Quiver.Path.nil, Quiver.Path.length_nil⟩⟩
      haveI : Subsingleton {p : Quiver.Path i i // p.length = 0} :=
        ⟨fun a b => Subtype.ext ((Quiver.Path.eq_nil_of_length_zero _ a.2).trans
          (Quiver.Path.eq_nil_of_length_zero _ b.2).symm)⟩
      exact Nat.card_unique
    · rw [if_neg h]
      haveI : IsEmpty {p : Quiver.Path i j // p.length = 0} :=
        ⟨fun p => h (Quiver.Path.eq_of_length_zero p.1 p.2)⟩
      exact Nat.card_of_isEmpty
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Nat.card_congr (pathSuccEquiv i j n), Nat.card_sigma]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Nat.card_prod, ih b, Nat.card_eq_fintype_card]
    rfl

/-- **(d)** The dimension of the degree-`n` graded piece of the path algebra `P_Q` is the total
number of paths of length `n`, i.e. the sum of all entries of `M_Q^n`. -/
theorem dim_pathAlgebra_degree (Q : Type*) [Quiver Q] [Fintype Q] [DecidableEq Q]
    [∀ i j : Q, Fintype (i ⟶ j)] (n : ℕ) :
    ∑ i : Q, ∑ j : Q, Nat.card {p : Quiver.Path i j // p.length = n}
      = ∑ i : Q, ∑ j : Q, (adjacencyMatrix Q ^ n) i j := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact card_paths_length_eq_adjacencyMatrix_pow Q i j n

end Etingof.Problem2_8_11
