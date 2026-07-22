import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Irreducible
import EtingofRepresentationTheory.Chapter5.Definition5_14_2

/-!
# Problem 5.16.2: the sum of transpositions acts on `V_λ` by the content

**Problem 5.16.2.** The **content** `c(λ)` of a Young diagram `λ` is the sum
`∑_j ∑_{i=1}^{λ_j} (i - j)`. Let `C = ∑_{i < j} (ij) ∈ ℂ[S_n]` be the sum of all
transpositions. Show that `C` acts on the Specht module `V_λ` by multiplication by `c(λ)`.

## Formalization

* `sumTranspositions n : ℂ[S_n]` is `∑_{i < j} (i j)`, the sum over ordered pairs `i < j` of
  the transposition `Equiv.swap i j`.
* `content la : ℤ` is `∑_{(i,j) ∈ cells} (j - i)`, summing `col − row` over the cells of the
  Young diagram of `λ` (cells are `0`-indexed `(row, col)`, so `col − row` matches the book's
  `i − j` with `i` = column, `j` = row).

`C` is central in `ℂ[S_n]` (a sum over a full conjugacy class), so left multiplication by `C`
preserves the left ideal `V_λ = ℂ[S_n]·c_λ` and, `V_λ` being irreducible, acts as a scalar.
The claim is that this scalar is `c(λ)`: for every `x ∈ V_λ`, `C · x = c(λ) • x`.

Statement pass: the proof is left as `sorry`.
-/

namespace Etingof

open scoped Classical

/-- `C = ∑_{i < j} (i j)`: the sum of all transpositions in `ℂ[S_n]`. -/
noncomputable def sumTranspositions (n : ℕ) : SymGroupAlgebra n :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap p.1 p.2)

/-- The content `c(λ) = ∑_{cells (i,j)} (j − i)` of the Young diagram of `λ`
(cells are `0`-indexed `(row, col)`; `j − i = col − row`). -/
noncomputable def content {n : ℕ} (la : Nat.Partition n) : ℤ :=
  ∑ c ∈ la.toYoungDiagram.cells, ((c.2 : ℤ) - (c.1 : ℤ))

/-- Problem 5.16.2. The sum of all transpositions `C = ∑_{i<j}(ij)` acts on the Specht module
`V_λ = ℂ[S_n]·c_λ` (by left multiplication) as multiplication by the content `c(λ)`. -/
theorem sumTranspositions_mul_eq_content_smul
    (n : ℕ) (la : Nat.Partition n)
    (x : SymGroupAlgebra n) (hx : x ∈ SpechtModule n la) :
    sumTranspositions n * x = (content la : ℂ) • x := by
  sorry

end Etingof
