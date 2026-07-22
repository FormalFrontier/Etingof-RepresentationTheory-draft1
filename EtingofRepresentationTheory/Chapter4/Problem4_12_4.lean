import Mathlib

/-!
# Problem 4.12.4: Nonabelian automorphism group forces repeated adjacency eigenvalues

**Problem 4.12.4.** Recall that the adjacency matrix of a graph `Γ` (without multiple
edges) is the matrix in which the `ij`th entry is `1` if the vertices `i` and `j` are
connected with an edge, and zero otherwise. Let `Γ` be a finite graph whose automorphism
group is nonabelian. Show that the adjacency matrix of `Γ` must have repeated eigenvalues.

## Formalization

We work with a finite `SimpleGraph Γ` on a vertex type `W`. Its adjacency matrix
`Γ.adjMatrix ℝ` is a real symmetric matrix, so it is diagonalizable and its eigenvalues
are exactly the roots of its characteristic polynomial. "Has a repeated eigenvalue" is
formalized as: the characteristic polynomial is **not squarefree** — equivalently (for a
symmetric matrix) some eigenvalue occurs with multiplicity `≥ 2`.

The hypothesis that the automorphism group is nonabelian is expressed as the existence
of two automorphisms that do not commute.

The representation-theoretic content (which is the point of the exercise): each
eigenspace of the adjacency matrix is a real representation of `Aut(Γ)`, and a nonabelian
finite group has a representation of dimension `≥ 2`, forcing some eigenspace to have
dimension `≥ 2`.
-/

/-- **Problem 4.12.4.** If a finite simple graph `Γ` has a nonabelian automorphism group,
then its adjacency matrix has a repeated eigenvalue: the characteristic polynomial (over
`ℝ`) is not squarefree. The automorphism group is `Γ ≃g Γ` (graph isomorphisms of `Γ`
with itself), and "nonabelian" is expressed by exhibiting two non-commuting elements. -/
theorem Etingof.Problem4_12_4 {W : Type*} [Fintype W] [DecidableEq W]
    (Γ : SimpleGraph W) [DecidableRel Γ.Adj]
    (hAut : ∃ σ τ : Γ ≃g Γ, σ * τ ≠ τ * σ) :
    ¬ Squarefree (Γ.adjMatrix ℝ).charpoly := by
  sorry
