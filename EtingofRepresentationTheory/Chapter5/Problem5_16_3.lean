import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Irreducible

/-!
# Problem 5.16.3: the sum `(12) + ⋯ + (1n)` of transpositions through `1`

**Problem 5.16.3.** (a) Let `V` be any finite-dimensional representation of `S_n`. Show that the
element `E := (12) + ⋯ + (1n)` is diagonalizable and has integer eigenvalues on `V` which are
between `1 - n` and `n - 1`.

*Hint.* Represent `E` as `C_n − C_{n-1}`, where `C_n = C` is the element from Problem 5.16.2.

(b) Show that the element `(12) + ⋯ + (1n)` acts on `V_λ` by a scalar if and only if `λ` is a
rectangular Young diagram, and compute this scalar.

## Formalization

`E = (12) + ⋯ + (1n)` is the sum of the transpositions through the first point. In the
`0`-indexed model `Fin n`, the first point is `0` and the transpositions `(1 j)` are
`Equiv.swap 0 j` for `j ≠ 0`; so `sumTranspositionsWith1 n = ∑_{0 < j} (0 j) ∈ ℂ[S_n]`.

* **(a)** For a representation `ρ : Representation ℂ S_n V` on a finite-dimensional `V`, `E` acts
  by the endomorphism `T = ρ.asAlgebraHom E`. The claim is that `T` is diagonalizable — there is a
  basis of `V` consisting of eigenvectors — and every eigenvalue is an integer `m` with
  `1 - n ≤ m ≤ n - 1`.
* **(b)** `E` acts on the Specht module `V_λ = ℂ[S_n]·c_λ` (by left multiplication) by a scalar if
  and only if `λ` is **rectangular** (`IsRectangular`: the parts multiset is `r` copies of a
  single value `c`).

Statement pass: the proofs are left as `sorry`.
-/

namespace Etingof

open scoped Classical

/-- `E = (12) + ⋯ + (1n) = ∑_{0 < j} (0 j)`: the sum of transpositions through the first point,
as an element of `ℂ[S_n]`. -/
noncomputable def sumTranspositionsWith1 (n : ℕ) [NeZero n] : SymGroupAlgebra n :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => (0 : Fin n) < j),
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap 0 j)

/-- A partition is **rectangular** if its Young diagram is a rectangle: the parts multiset is a
constant multiset `Multiset.replicate r c` (`r` rows each of length `c`). -/
def IsRectangular {n : ℕ} (la : Nat.Partition n) : Prop :=
  ∃ r c : ℕ, la.parts = Multiset.replicate r c

/-- Problem 5.16.3(a). For any finite-dimensional representation `ρ` of `S_n`, the element
`E = (12) + ⋯ + (1n)` acts as a diagonalizable endomorphism `T = ρ.asAlgebraHom E` (there is a
basis of eigenvectors) whose eigenvalues are all integers `m` with `1 - n ≤ m ≤ n - 1`. -/
theorem sumTranspositionsWith1_diagonalizable_integer_eigenvalues
    (n : ℕ) [NeZero n]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    (∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V),
        ∀ i, ∃ μ : ℂ, (Representation.asAlgebraHom ρ) (sumTranspositionsWith1 n) (b i) = μ • b i) ∧
      (∀ μ : ℂ, Module.End.HasEigenvalue
          ((Representation.asAlgebraHom ρ) (sumTranspositionsWith1 n)) μ →
        ∃ m : ℤ, μ = (m : ℂ) ∧ (1 - (n : ℤ)) ≤ m ∧ m ≤ (n : ℤ) - 1) := by
  sorry

/-- Problem 5.16.3(b). The element `E = (12) + ⋯ + (1n)` acts on the Specht module
`V_λ = ℂ[S_n]·c_λ` (by left multiplication) by a scalar if and only if `λ` is a rectangular
Young diagram. -/
theorem sumTranspositionsWith1_acts_scalar_iff_rectangular
    (n : ℕ) [NeZero n] (la : Nat.Partition n) :
    (∃ c : ℂ, ∀ x ∈ SpechtModule n la, sumTranspositionsWith1 n * x = c • x) ↔
      IsRectangular la := by
  sorry

end Etingof
