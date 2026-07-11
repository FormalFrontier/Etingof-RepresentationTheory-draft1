import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import EtingofRepresentationTheory.Chapter9.Definition9_3_1
import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import EtingofRepresentationTheory.Chapter9.Problem9_3_2
import EtingofRepresentationTheory.Chapter9.TruncatedPolynomial

/-!
# Problem 9.4.5: Cartan determinant and some homological dimensions

Etingof Problem 9.4.5 has two parts.

* **(i)** If a finite dimensional algebra `A` has finite homological dimension `d`, and `C` is
  the Cartan matrix of `A`, then `det(C) = ±1`.

* **(ii)** Compute the homological dimension of `k[t]/tⁿ` (`n > 1`) and of the algebra of
  Problem 9.3.2. Both are **infinite**: `k[t]/tⁿ` with `n > 1` is a self-injective but
  non-semisimple algebra, so it has infinite global dimension; the four dimensional algebra
  `A = ℂ⟨g, x⟩/(gx+xg, x², g²-1)` of Problem 9.3.2 (which contains `k[x]/x²` and is likewise
  non-semisimple with a nonsplit self-extension) also has infinite homological dimension.

## Statement-pass note

Part (i) uses `Etingof.algebraCartanMatrix` (Definition 9.3.1) for the Cartan matrix and
`Etingof.homologicalDimension` (Definition 9.4.3) for the homological dimension; the entries
of the Cartan matrix are natural numbers, so `det(C) = ±1` is stated after casting the matrix
into `ℤ`. Part (ii) records the two concrete values as `homologicalDimension = ⊤`. Proofs are
deferred (`sorry`).
-/

universe u

open scoped Polynomial

namespace Etingof.Problem945

/-- **Problem 9.4.5 (i).** If the finite dimensional algebra `A` has finite homological
dimension, then the determinant of its Cartan matrix `C` is `±1`. The Cartan matrix
`Etingof.algebraCartanMatrix P` (Definition 9.3.1) is built from the family `P` of projective
covers of the simple modules; its `ℕ`-entries are cast to `ℤ` to take the determinant. -/
theorem cartan_det_eq_pm_one
    {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    (hfin : Etingof.homologicalDimension A ≠ ⊤) :
    ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).det = 1 ∨
      ((Etingof.algebraCartanMatrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).det = -1 := by
  sorry

/-- **Problem 9.4.5 (ii), first algebra.** For `n > 1`, the truncated polynomial algebra
`k[t]/tⁿ` has infinite homological dimension. -/
theorem homologicalDimension_polynomial_quotient_eq_top
    (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) :
    Etingof.homologicalDimension (k[X] ⧸ Ideal.span {(Polynomial.X : k[X]) ^ n}) = ⊤ :=
  Etingof.TruncatedPoly.homologicalDimension_eq_top_truncated k n hn

/-- **Problem 9.4.5 (ii), second algebra.** The four dimensional algebra
`A = ℂ⟨g, x⟩/(gx+xg, x², g²-1)` of Problem 9.3.2 has infinite homological dimension. -/
theorem homologicalDimension_problem932_eq_top :
    Etingof.homologicalDimension Etingof.Problem932.A = ⊤ := by
  sorry

end Etingof.Problem945
