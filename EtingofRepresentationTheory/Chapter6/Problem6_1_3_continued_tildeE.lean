import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.DynkinTypes
import EtingofRepresentationTheory.Chapter6.Theorem_Dynkin_classification
import EtingofRepresentationTheory.Chapter6.Problem6_1_3_continued_E7_E8

/-!
# Problem 6.1.3 (continued): affine Dynkin diagrams and parts (e)–(g)

> The **extended (affine) Dynkin diagrams** `Ẽ₆, Ẽ₇, Ẽ₈` (and `Ãₙ, D̃ₙ`) carry
> the vertex labels (marks) shown in the book.
>
> **(e)** Show that `det(A) = 0` for all the extended graphs `Γ` below (the
> hint: the numbers labeling the vertices are the kernel vector of `A`).
>
> **(f)** Deduce from (a)–(e) the **classification theorem** for Dynkin diagrams:
> `Γ` is a Dynkin diagram iff it is one of `Aₙ (n ≥ 1)`, `Dₙ (n ≥ 4)`, `E₆, E₇, E₈`.
>
> **(g)** A (simply laced) **affine Dynkin diagram** is a connected graph without
> self-loops such that the quadratic form defined by `A` is positive
> semidefinite but not positive definite. **Classify** affine Dynkin diagrams:
> they are exactly the extended (forbidden) diagrams `Ãₙ, D̃ₙ, Ẽ₆, Ẽ₇, Ẽ₈`.

The marks are the standard positive integers making each `A = 2·Id - R` have a
positive null vector, so `A` is positive semidefinite but degenerate.
-/

namespace Etingof.Problem6_1_3_tildeE

open Matrix Finset

/-! ## The affine Dynkin diagram predicate (part (g) definition) -/

/-- **(g)** An **affine (simply laced) Dynkin diagram** on `n` vertices: a
connected simple graph (symmetric `0/1` adjacency, no self-loops) whose Cartan
form `A = 2·Id - R` is positive *semidefinite* but *not* positive definite. -/
def IsAffineDynkinDiagram (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  adj.IsSymm ∧
  (∀ i, adj i i = 0) ∧
  (∀ i j, adj i j = 0 ∨ adj i j = 1) ∧
  (∀ i j : Fin n, ∃ path : List (Fin n),
    path.head? = some i ∧ path.getLast? = some j ∧
    ∀ k, (h : k + 1 < path.length) →
      adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) ∧
  -- positive semidefinite
  (∀ x : Fin n → ℤ, 0 ≤ dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x)) ∧
  -- but not positive definite: some nonzero `x` makes the form vanish
  (∃ x : Fin n → ℤ, x ≠ 0 ∧
    dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) = 0)

/-! ## The extended (affine) Dynkin types, with their marks

We enumerate the affine simply-laced types. `Ãₙ` is the `(n+1)`-cycle; `D̃ₙ`
has a fork at each end of a chain; `Ẽ₆, Ẽ₇, Ẽ₈` are the three exceptional ones.
Each carries a positive `marks` vector spanning the kernel of its Cartan matrix.
-/

/-- The simply-laced affine Dynkin types. -/
inductive AffineType where
  | Atilde (n : ℕ) (hn : 3 ≤ n)      -- the `n`-cycle `Ãₙ₋₁`
  | Dtilde (n : ℕ) (hn : 4 ≤ n)      -- affine `D̃ₙ`, rank `n + 1`
  | E6tilde
  | E7tilde
  | E8tilde

/-- Number of vertices of an affine diagram. -/
def AffineType.rank : AffineType → ℕ
  | .Atilde n _ => n
  | .Dtilde n _ => n + 1
  | .E6tilde => 7
  | .E7tilde => 8
  | .E8tilde => 9

/-- Adjacency matrix of each affine Dynkin type.

- `Ãₙ`: the `n`-cycle `i — (i±1 mod n)`.
- `D̃ₙ` (rank `n+1`, vertices `0..n`): leaves `0,1` on node `2`, chain
  `2—3—⋯—(n-2)`, leaves `(n-1),n` on node `n-2`.
- `Ẽ₆` (rank 7): central node `0` with three arms `0—1—2`, `0—3—4`, `0—5—6`.
- `Ẽ₇` (rank 8): path `0—1—⋯—6` with a branch `3—7` at the center.
- `Ẽ₈` (rank 9): path `0—1—⋯—7` with a branch `5—8`. -/
def AffineType.adj : (t : AffineType) → Matrix (Fin t.rank) (Fin t.rank) ℤ
  | .Atilde n _ => fun i j =>
      if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then 1 else 0
  | .Dtilde n _ => fun i j =>
      let a := min i.val j.val; let b := max i.val j.val
      if (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
         (2 ≤ a ∧ b ≤ n - 2 ∧ a + 1 = b) ∨
         (a = n - 2 ∧ b = n - 1) ∨ (a = n - 2 ∧ b = n)
      then 1 else 0
  | .E6tilde => fun i j =>
      let a := min i.val j.val; let b := max i.val j.val
      if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 0 ∧ b = 3) ∨
         (a = 3 ∧ b = 4) ∨ (a = 0 ∧ b = 5) ∨ (a = 5 ∧ b = 6)
      then 1 else 0
  | .E7tilde => fun i j =>
      let a := min i.val j.val; let b := max i.val j.val
      if (b = a + 1 ∧ b ≤ 6) ∨ (a = 3 ∧ b = 7)
      then 1 else 0
  | .E8tilde => fun i j =>
      let a := min i.val j.val; let b := max i.val j.val
      if (b = a + 1 ∧ b ≤ 7) ∨ (a = 5 ∧ b = 8)
      then 1 else 0

/-- The **marks** (vertex labels): a positive integer vector spanning the kernel
of the Cartan matrix `2·Id - adj`.

- `Ãₙ`: all `1`.
- `D̃ₙ`: `1` at the four leaves `0,1,n-1,n`, `2` on the chain.
- `Ẽ₆`: center `3`, mid-arm `2`, leaves `1` → `(3,2,1,2,1,2,1)`.
- `Ẽ₇`: `(1,2,3,4,3,2,1)` on the path, branch `2` → index `7 ↦ 2`.
- `Ẽ₈`: `(1,2,3,4,5,6,4,2)` on the path, branch `3` → index `8 ↦ 3`. -/
def AffineType.marks : (t : AffineType) → (Fin t.rank → ℤ)
  | .Atilde _ _ => fun _ => 1
  | .Dtilde n _ => fun i =>
      if i.val = 0 ∨ i.val = 1 ∨ i.val = n - 1 ∨ i.val = n then 1 else 2
  | .E6tilde => fun i => ![3, 2, 1, 2, 1, 2, 1] i
  | .E7tilde => fun i => ![1, 2, 3, 4, 3, 2, 1, 2] i
  | .E8tilde => fun i => ![1, 2, 3, 4, 5, 6, 4, 2, 3] i

/-! ## Part (e)/(g): the marks are the kernel vector, so `det A = 0` -/

/-- The marks are (strictly) positive. -/
theorem marks_pos (t : AffineType) (i : Fin t.rank) : 0 < t.marks i := by
  sorry

/-- **(e)** The marks span the kernel of the Cartan matrix: `(2·Id - R)·marks = 0`
("the numbers labeling the vertices are the null vector"). -/
theorem cartan_mulVec_marks_eq_zero (t : AffineType) :
    (2 • (1 : Matrix (Fin t.rank) (Fin t.rank) ℤ) - t.adj).mulVec t.marks = 0 := by
  sorry

/-- **(e)** Consequently `det A = 0` for every extended diagram. -/
theorem cartan_det_zero (t : AffineType) :
    (2 • (1 : Matrix (Fin t.rank) (Fin t.rank) ℤ) - t.adj).det = 0 := by
  sorry

/-- **(g, one direction)** Each extended diagram really is an affine Dynkin
diagram (its Cartan form is positive semidefinite but degenerate). -/
theorem isAffineDynkinDiagram_of_type (t : AffineType) :
    IsAffineDynkinDiagram t.rank t.adj := by
  sorry

/-! ## Part (f): the classification of Dynkin diagrams -/

/-- **(f)** **Classification of Dynkin diagrams.** A connected simply-laced
graph on `n ≥ 1` vertices is a Dynkin diagram iff it is (graph-isomorphic to)
one of `Aₙ, Dₙ, E₆, E₇, E₈`. This is `Etingof.Theorem_Dynkin_classification`. -/
theorem dynkin_classification (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n) :
    IsDynkinDiagram n adj ↔
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n, ∀ i j, adj (σ i) (σ j) = t.adj i j :=
  Etingof.Theorem_Dynkin_classification n adj hn

/-! ## Part (g): the classification of affine Dynkin diagrams -/

/-- **(g)** **Classification of affine Dynkin diagrams.** A connected simply-laced
graph on `n ≥ 1` vertices is an affine Dynkin diagram iff it is
(graph-isomorphic to) one of `Ãₙ, D̃ₙ, Ẽ₆, Ẽ₇, Ẽ₈` — exactly the "forbidden"
extended diagrams of parts (c)–(e). -/
theorem affine_dynkin_classification (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n) :
    IsAffineDynkinDiagram n adj ↔
    ∃ t : AffineType, ∃ σ : Fin t.rank ≃ Fin n, ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  sorry

end Etingof.Problem6_1_3_tildeE
