import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4

/-!
# Problem 6.1.3: Dynkin diagrams (setup)

> **Problem 6.1.3. Dynkin diagrams.** Let `Γ` be a graph, i.e. a finite set of
> points (vertices) connected with a certain number of edges (we allow multiple
> edges). We assume that `Γ` is connected (any vertex can be connected to any
> other by a path of edges) and has no self-loops (edges from a vertex to
> itself). Suppose the vertices of `Γ` are labeled by integers `1, …, n`. Then
> one can assign to `Γ` an `n × n` matrix `R = (rᵢⱼ)`, where `rᵢⱼ` is the number
> of edges connecting vertices `i` and `j`. This matrix is obviously symmetric
> and is called the **adjacency matrix**. Define the matrix `A = 2·Id - R`,
> where `Id` is the identity matrix.

This is the setup blob that introduces the objects used throughout Problem 6.1.3
(parts (a)–(g), split across the continuation blobs) and by Definition 6.1.4:
the adjacency matrix `R` of a graph, and the **Cartan-type matrix** `A = 2·Id - R`
whose associated quadratic form governs whether `Γ` is a Dynkin diagram.

The only assertion in this blob is that `A` is symmetric whenever `R` is
(the book: "this matrix is obviously symmetric"). We record the construction of
`A` and that symmetry, in a form compatible with `Etingof.IsDynkinDiagram`
(Definition 6.1.4), which is stated over the same `2 • 1 - R`.
-/

namespace Etingof.Problem6_1_3

open Matrix

/-- The Cartan-type matrix `A = 2·Id - R` of a graph with (integer) adjacency
matrix `R`. Matches the matrix used in `Etingof.IsDynkinDiagram`
(Definition 6.1.4). -/
def cartanMatrix {n : ℕ} (R : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  2 • (1 : Matrix (Fin n) (Fin n) ℤ) - R

/-- `cartanMatrix R = 2 • Id - R`, the defining identity `A = 2·Id - R`. -/
theorem cartanMatrix_eq {n : ℕ} (R : Matrix (Fin n) (Fin n) ℤ) :
    cartanMatrix R = 2 • (1 : Matrix (Fin n) (Fin n) ℤ) - R := rfl

/-- The diagonal of `A = 2·Id - R` is `2` when `R` has no self-loops
(`R i i = 0`), since each vertex contributes `2` from `2·Id`. -/
theorem cartanMatrix_diag {n : ℕ} {R : Matrix (Fin n) (Fin n) ℤ}
    (hloop : ∀ i, R i i = 0) (i : Fin n) : cartanMatrix R i i = 2 := by
  rw [cartanMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, hloop i]
  norm_num

/-- **The adjacency-derived matrix `A = 2·Id - R` is symmetric** whenever the
adjacency matrix `R` is symmetric (Etingof: "this matrix is obviously
symmetric"). -/
theorem cartanMatrix_isSymm {n : ℕ} {R : Matrix (Fin n) (Fin n) ℤ}
    (hR : R.IsSymm) : (cartanMatrix R).IsSymm := by
  unfold Matrix.IsSymm cartanMatrix
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hR.eq]

end Etingof.Problem6_1_3
