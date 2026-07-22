import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.FreeAlgebra

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
    Nat.card {l : List (Fin m) // l.length = n} = m ^ n :=
  sorry

/-- **(b)**, generating-function form: the Hilbert series of `k⟨x₁,…,x_m⟩` is `1/(1-mt)`,
expressed as the power-series identity `(1 - m·t) · h_A = 1`. -/
theorem hilbertSeries_freeAlgebra (k : Type*) [Field k] (m : ℕ) :
    (1 - (m : ℕ) • PowerSeries.X : PowerSeries k) *
      PowerSeries.mk (fun n => ((m ^ n : ℕ) : k)) = 1 :=
  sorry

/-! ## (c) Exterior (Grassmann) algebra `⋀_k[x₁,…,x_m]` -/

/-- **(c)** The degree-`n` graded piece of the exterior algebra on `m` generators is the `n`-th
exterior power of the `m`-dimensional space, of dimension `C(m, n)`. Equivalently the Hilbert
series is `(1+t)^m`. -/
theorem finrank_exteriorPower (k : Type*) [Field k] (m n : ℕ) :
    Module.finrank k (⋀[k]^n (Fin m → k)) = m.choose n :=
  sorry

/-- **(c)**, generating-function form: the Hilbert series of the exterior algebra on `m`
generators is the polynomial `(1+t)^m`. -/
theorem hilbertSeries_exteriorAlgebra (k : Type*) [Field k] (m : ℕ) :
    PowerSeries.mk (fun n => ((m.choose n : ℕ) : k)) = (1 + PowerSeries.X : PowerSeries k) ^ m :=
  sorry

/-! ## (d) Path algebra `P_Q` -/

/-- The adjacency matrix of a finite quiver `Q`: the `(i,j)`-entry is the number of arrows
`i ⟶ j`. -/
def adjacencyMatrix (Q : Type*) [Quiver Q] [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)] :
    Matrix Q Q ℕ :=
  fun i j => Fintype.card (i ⟶ j)

/-- **(d)** The number of paths of length `n` from `i` to `j` in a finite quiver equals the
`(i,j)`-entry of the `n`-th power of the adjacency matrix. This is the graded-piece dimension of
the path algebra: the closed answer to the Hilbert series in terms of `M_Q`. -/
theorem card_paths_length_eq_adjacencyMatrix_pow (Q : Type*) [Quiver Q] [Fintype Q]
    [DecidableEq Q] [∀ i j : Q, Fintype (i ⟶ j)] (i j : Q) (n : ℕ) :
    Nat.card {p : Quiver.Path i j // p.length = n} = (adjacencyMatrix Q ^ n) i j :=
  sorry

/-- **(d)** The dimension of the degree-`n` graded piece of the path algebra `P_Q` is the total
number of paths of length `n`, i.e. the sum of all entries of `M_Q^n`. -/
theorem dim_pathAlgebra_degree (Q : Type*) [Quiver Q] [Fintype Q] [DecidableEq Q]
    [∀ i j : Q, Fintype (i ⟶ j)] (n : ℕ) :
    ∑ i : Q, ∑ j : Q, Nat.card {p : Quiver.Path i j // p.length = n}
      = ∑ i : Q, ∑ j : Q, (adjacencyMatrix Q ^ n) i j :=
  sorry

end Etingof.Problem2_8_11
