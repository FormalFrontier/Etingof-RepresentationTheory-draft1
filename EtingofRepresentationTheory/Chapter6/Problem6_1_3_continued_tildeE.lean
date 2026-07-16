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
  cases t with
  | Atilde n hn => simp [AffineType.marks]
  | Dtilde n hn =>
      simp only [AffineType.marks]
      split <;> norm_num
  | E6tilde => fin_cases i <;> simp [AffineType.marks]
  | E7tilde => fin_cases i <;> simp [AffineType.marks]
  | E8tilde => fin_cases i <;> simp [AffineType.marks]

/-- The neighbour-sum identity `∑ⱼ adj i j · marks j = 2 · marks i` for the affine
`D̃ₙ` type at `n = m + 6` (rank `m + 7`), where the two forks are well separated
(`n ≥ 6`), so the vertex classes — the four leaves, the two forks, and the interior
chain — are handled uniformly. This is the crux of `cartan_mulVec_marks_eq_zero` for
`D̃ₙ`; the small cases `n = 4, 5` (where the forks coincide or are adjacent) are
dispatched by `decide`. -/
private theorem dtilde_key (m : ℕ) (hn : 4 ≤ m + 6) (i : Fin (AffineType.Dtilde (m+6) hn).rank) :
    ∑ j, (AffineType.Dtilde (m+6) hn).adj i j * (AffineType.Dtilde (m+6) hn).marks j
      = 2 * (AffineType.Dtilde (m+6) hn).marks i := by
  have hrank : (AffineType.Dtilde (m+6) hn).rank = m + 7 := by simp [AffineType.rank]
  have hlt : i.val < m + 7 := hrank ▸ i.isLt
  have adj_val : ∀ (a b : Fin (AffineType.Dtilde (m+6) hn).rank),
      (AffineType.Dtilde (m+6) hn).adj a b
        = if min a.val b.val = 0 ∧ max a.val b.val = 2 ∨ min a.val b.val = 1 ∧ max a.val b.val = 2 ∨
             2 ≤ min a.val b.val ∧ max a.val b.val ≤ (m+6)-2
               ∧ min a.val b.val + 1 = max a.val b.val ∨
             min a.val b.val = (m+6)-2 ∧ max a.val b.val = (m+6)-1 ∨
             min a.val b.val = (m+6)-2 ∧ max a.val b.val = (m+6) then 1 else 0 := fun _ _ => rfl
  have mval : ∀ (j : Fin (AffineType.Dtilde (m+6) hn).rank),
      (AffineType.Dtilde (m+6) hn).marks j
        = if j.val = 0 ∨ j.val = 1 ∨ j.val = m+5 ∨ j.val = m+6 then 1 else 2 := fun _ => rfl
  have hclass : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ (3 ≤ i.val ∧ i.val ≤ m+3) ∨
      i.val = m+4 ∨ i.val = m+5 ∨ i.val = m+6 := by omega
  rcases hclass with hi | hi | hi | ⟨hlo, hhi⟩ | hi | hi | hi
  · -- v = 0 : nbr {2}
    have h2 : (2:ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    rw [← Finset.sum_subset (Finset.subset_univ {(⟨2,h2⟩ : Fin _)})
        (fun x _ hx => by rw [adj_val, if_neg]; · ring
                          · simp only [mem_singleton, Fin.ext_iff] at hx; omega),
        Finset.sum_singleton]
    rw [show (AffineType.Dtilde (m+6) hn).adj i ⟨2,h2⟩ = 1 from by
        rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨2,h2⟩ = 2 from by
            rw [mval, if_neg]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks i = 1 from by
            rw [mval, if_pos]; omega]
    norm_num
  · -- v = 1 : nbr {2}
    have h2 : (2:ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    rw [← Finset.sum_subset (Finset.subset_univ {(⟨2,h2⟩ : Fin _)})
        (fun x _ hx => by rw [adj_val, if_neg]; · ring
                          · simp only [mem_singleton, Fin.ext_iff] at hx; omega),
        Finset.sum_singleton]
    rw [show (AffineType.Dtilde (m+6) hn).adj i ⟨2,h2⟩ = 1 from by
        rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨2,h2⟩ = 2 from by
            rw [mval, if_neg]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks i = 1 from by
            rw [mval, if_pos]; omega]
    norm_num
  · -- v = 2 : nbrs {0,1,3}
    have h0 : (0:ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    have h1 : (1:ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    have h3 : (3:ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    rw [← Finset.sum_subset (Finset.subset_univ
          {(⟨0,h0⟩ : Fin _), ⟨1,h1⟩, ⟨3,h3⟩})
        (fun x _ hx => by rw [adj_val, if_neg]; · ring
                          · simp only [mem_insert, mem_singleton, Fin.ext_iff] at hx; omega),
        Finset.sum_insert (by simp only [mem_insert, mem_singleton, Fin.ext_iff]; omega),
        Finset.sum_insert (by simp only [mem_singleton, Fin.ext_iff]; omega), Finset.sum_singleton]
    rw [show (AffineType.Dtilde (m+6) hn).adj i ⟨0,h0⟩ = 1 from by
        rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).adj i ⟨1,h1⟩ = 1 from by
            rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).adj i ⟨3,h3⟩ = 1 from by
            rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨0,h0⟩ = 1 from by
            rw [mval, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨1,h1⟩ = 1 from by
            rw [mval, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨3,h3⟩ = 2 from by
            rw [mval, if_neg]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks i = 2 from by
            rw [mval, if_neg]; omega]
    norm_num
  · -- interior : 3 ≤ v ≤ m+3, nbrs {v-1, v+1}
    have hp : (i.val - 1 : ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    have hs : (i.val + 1 : ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    rw [← Finset.sum_subset (Finset.subset_univ {(⟨i.val-1,hp⟩ : Fin _), ⟨i.val+1,hs⟩})
        (fun x _ hx => by rw [adj_val, if_neg]; · ring
                          · simp only [mem_insert, mem_singleton, Fin.ext_iff] at hx; omega),
        Finset.sum_insert (by simp only [mem_singleton, Fin.ext_iff]; omega), Finset.sum_singleton]
    rw [show (AffineType.Dtilde (m+6) hn).adj i ⟨i.val-1,hp⟩ = 1 from by
        rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).adj i ⟨i.val+1,hs⟩ = 1 from by
            rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨i.val-1,hp⟩ = 2 from by
            rw [mval, if_neg]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨i.val+1,hs⟩ = 2 from by
            rw [mval, if_neg]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks i = 2 from by
            rw [mval, if_neg]; omega]
    norm_num
  · -- v = m+4 : nbrs {m+3, m+5, m+6}
    have h3 : (m+3 : ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    have h5 : (m+5 : ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    have h6 : (m+6 : ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    rw [← Finset.sum_subset (Finset.subset_univ
          {(⟨m+3,h3⟩ : Fin _), ⟨m+5,h5⟩, ⟨m+6,h6⟩})
        (fun x _ hx => by rw [adj_val, if_neg]; · ring
                          · simp only [mem_insert, mem_singleton, Fin.ext_iff] at hx; omega),
        Finset.sum_insert (by simp only [mem_insert, mem_singleton, Fin.ext_iff]; omega),
        Finset.sum_insert (by simp only [mem_singleton, Fin.ext_iff]; omega), Finset.sum_singleton]
    rw [show (AffineType.Dtilde (m+6) hn).adj i ⟨m+3,h3⟩ = 1 from by
        rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).adj i ⟨m+5,h5⟩ = 1 from by
            rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).adj i ⟨m+6,h6⟩ = 1 from by
            rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨m+3,h3⟩ = 2 from by
            rw [mval, if_neg]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨m+5,h5⟩ = 1 from by
            rw [mval, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨m+6,h6⟩ = 1 from by
            rw [mval, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks i = 2 from by
            rw [mval, if_neg]; omega]
    norm_num
  · -- v = m+5 : nbr {m+4}
    have h4 : (m+4 : ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    rw [← Finset.sum_subset (Finset.subset_univ {(⟨m+4,h4⟩ : Fin _)})
        (fun x _ hx => by rw [adj_val, if_neg]; · ring
                          · simp only [mem_singleton, Fin.ext_iff] at hx; omega),
        Finset.sum_singleton]
    rw [show (AffineType.Dtilde (m+6) hn).adj i ⟨m+4,h4⟩ = 1 from by
        rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨m+4,h4⟩ = 2 from by
            rw [mval, if_neg]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks i = 1 from by
            rw [mval, if_pos]; omega]
    norm_num
  · -- v = m+6 : nbr {m+4}
    have h4 : (m+4 : ℕ) < (AffineType.Dtilde (m+6) hn).rank := by omega
    rw [← Finset.sum_subset (Finset.subset_univ {(⟨m+4,h4⟩ : Fin _)})
        (fun x _ hx => by rw [adj_val, if_neg]; · ring
                          · simp only [mem_singleton, Fin.ext_iff] at hx; omega),
        Finset.sum_singleton]
    rw [show (AffineType.Dtilde (m+6) hn).adj i ⟨m+4,h4⟩ = 1 from by
        rw [adj_val, if_pos]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks ⟨m+4,h4⟩ = 2 from by
            rw [mval, if_neg]; first | omega | (dsimp only []; omega),
        show (AffineType.Dtilde (m+6) hn).marks i = 1 from by
            rw [mval, if_pos]; omega]
    norm_num

/-- **(e)** The marks span the kernel of the Cartan matrix: `(2·Id - R)·marks = 0`
("the numbers labeling the vertices are the null vector"). -/
theorem cartan_mulVec_marks_eq_zero (t : AffineType) :
    (2 • (1 : Matrix (Fin t.rank) (Fin t.rank) ℤ) - t.adj).mulVec t.marks = 0 := by
  cases t with
  | Atilde n hn =>
      exact Etingof.Problem6_1_3_E7E8.cycle_cartan_mulVec_one_eq_zero n hn
  | Dtilde n hn =>
      match n, hn with
      | 4, _ =>
          funext i
          fin_cases i <;>
            simp only [AffineType.adj, AffineType.marks, AffineType.rank, Pi.zero_apply] <;>
            decide +revert
      | 5, _ =>
          funext i
          fin_cases i <;>
            simp only [AffineType.adj, AffineType.marks, AffineType.rank, Pi.zero_apply] <;>
            decide +revert
      | (m + 6), hn =>
          funext i
          have hrow : ((2 • (1 : Matrix (Fin (AffineType.Dtilde (m+6) hn).rank)
                (Fin (AffineType.Dtilde (m+6) hn).rank) ℤ)
                - (AffineType.Dtilde (m+6) hn).adj).mulVec
              (AffineType.Dtilde (m+6) hn).marks) i
              = 2 * (AffineType.Dtilde (m+6) hn).marks i
                - ∑ j, (AffineType.Dtilde (m+6) hn).adj i j
                    * (AffineType.Dtilde (m+6) hn).marks j := by
            rw [sub_mulVec, smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply]
            simp only [Matrix.mulVec, dotProduct, two_smul, two_mul]
          rw [Pi.zero_apply, hrow, dtilde_key m hn i, sub_self]
  | E6tilde => decide
  | E7tilde => decide
  | E8tilde => decide

/-- **(e)** Consequently `det A = 0` for every extended diagram. -/
theorem cartan_det_zero (t : AffineType) :
    (2 • (1 : Matrix (Fin t.rank) (Fin t.rank) ℤ) - t.adj).det = 0 := by
  have hr : 0 < t.rank := by cases t <;> simp only [AffineType.rank] <;> omega
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨t.marks, ?_, cartan_mulVec_marks_eq_zero t⟩
  intro h
  have h0 := congrFun h ⟨0, hr⟩
  have hp := marks_pos t ⟨0, hr⟩
  simp only [Pi.zero_apply] at h0
  rw [h0] at hp
  exact lt_irrefl 0 hp

/-! ## A reusable positive-semidefiniteness criterion

A symmetric integer matrix whose off-diagonal entries are all nonpositive and
which annihilates a strictly positive vector is positive semidefinite. This is
the weighted graph-Laplacian positivity fact underlying every affine Cartan form.
-/

/-- **Weighted-Laplacian positivity.** If a symmetric matrix `A` has nonpositive
off-diagonal entries and `A · m = 0` for a *strictly positive* vector `m`, then
the quadratic form `x ↦ xᵀ A x` is positive semidefinite. The proof is the
sum-of-squares identity
`2·(xᵀ A x) = ∑_{i,j} (-Aᵢⱼ) mᵢ mⱼ (xᵢ/mᵢ - xⱼ/mⱼ)²`,
worked over `ℚ` (so we may divide by the marks) and cast back to `ℤ`. -/
theorem posSemidef_of_nonpos_offDiag_kernel {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hsymm : A.IsSymm)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (m : Fin n → ℤ) (hm : ∀ i, 0 < m i) (hker : A.mulVec m = 0)
    (x : Fin n → ℤ) :
    0 ≤ dotProduct x (A.mulVec x) := by
  suffices h : (0:ℚ) ≤ ((dotProduct x (A.mulVec x) : ℤ) : ℚ) by exact_mod_cast h
  -- rational rescaled variables `y i = x i / m i`
  set y : Fin n → ℚ := fun i => (x i : ℚ) / (m i : ℚ) with hy
  have hm0 : ∀ i, (m i : ℚ) ≠ 0 := fun i => by exact_mod_cast (ne_of_gt (hm i))
  have hmy : ∀ i, (m i : ℚ) * y i = (x i : ℚ) := fun i => by
    have hmi := hm0 i
    change (m i : ℚ) * ((x i : ℚ) / (m i : ℚ)) = (x i : ℚ)
    field_simp
  -- the quadratic form as an explicit double sum
  have hq : ((dotProduct x (A.mulVec x) : ℤ) : ℚ)
      = ∑ i, ∑ j, (A i j : ℚ) * (x i) * (x j) := by
    simp only [dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  -- each row of `A` is orthogonal to `m` over `ℚ`
  have hrow : ∀ i, (∑ j, (A i j : ℚ) * (m j)) = 0 := by
    intro i
    have h1 : (∑ j, (A i j : ℚ) * (m j)) = (((A.mulVec m) i : ℤ) : ℚ) := by
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
    rw [h1, hker]; simp
  -- each column of `A` is orthogonal to `m` (using symmetry)
  have hcol : ∀ j, (∑ i, (A i j : ℚ) * (m i)) = 0 := by
    intro j
    have hsymm' : ∀ i, A i j = A j i := fun i => (hsymm.apply j i)
    calc (∑ i, (A i j : ℚ) * (m i)) = ∑ i, (A j i : ℚ) * (m i) := by
            apply Finset.sum_congr rfl; intro i _; rw [hsymm' i]
      _ = 0 := hrow j
  -- the sum-of-squares form
  set S : ℚ := ∑ i, ∑ j, (-(A i j : ℚ)) * (m i) * (m j) * (y i - y j)^2 with hS
  have hSnonneg : 0 ≤ S := by
    rw [hS]
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · have h1 : (0:ℚ) ≤ -(A i j : ℚ) := by
        have := hoff i j h; exact_mod_cast neg_nonneg.mpr this
      have h2 : (0:ℚ) ≤ (m i : ℚ) := le_of_lt (by exact_mod_cast hm i)
      have h3 : (0:ℚ) ≤ (m j : ℚ) := le_of_lt (by exact_mod_cast hm j)
      have h4 : (0:ℚ) ≤ (y i - y j)^2 := sq_nonneg _
      positivity
  -- split `S` into the three double sums
  set A1 : ℚ := ∑ i, ∑ j, (-(A i j : ℚ)) * (m i) * (m j) * (y i)^2 with hA1
  set A3 : ℚ := ∑ i, ∑ j, (-(A i j : ℚ)) * (m i) * (m j) * (y j)^2 with hA3
  set A2 : ℚ := ∑ i, ∑ j, (-(A i j : ℚ)) * ((m i) * (y i)) * ((m j) * (y j)) with hA2
  have hSeq : S = A1 + A3 - 2 * A2 := by
    have e1 : A1 + A3 = ∑ i, ∑ j,
        ((-(A i j:ℚ))*(m i)*(m j)*(y i)^2 + (-(A i j:ℚ))*(m i)*(m j)*(y j)^2) := by
      rw [hA1, hA3, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_add_distrib]
    have e2 : 2 * A2 = ∑ i, ∑ j,
        2 * ((-(A i j:ℚ)) * ((m i)*(y i)) * ((m j)*(y j))) := by
      rw [hA2, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
    rw [hS, e1, e2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  -- `A1 = 0` (rows orthogonal to `m`)
  have hA1z : A1 = 0 := by
    rw [hA1]; apply Finset.sum_eq_zero; intro i _
    have : (∑ j, (-(A i j:ℚ))*(m i)*(m j)*(y i)^2)
        = (-(m i:ℚ) * (y i)^2) * ∑ j, (A i j:ℚ) * (m j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [this, hrow, mul_zero]
  -- `A3 = 0` (columns orthogonal to `m`)
  have hA3z : A3 = 0 := by
    rw [hA3, Finset.sum_comm]; apply Finset.sum_eq_zero; intro j _
    have : (∑ i, (-(A i j:ℚ))*(m i)*(m j)*(y j)^2)
        = (-(m j:ℚ) * (y j)^2) * ∑ i, (A i j:ℚ) * (m i) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hcol, mul_zero]
  -- `A2 = -(xᵀ A x)` (undo the rescaling: `m i * y i = x i`)
  have hA2eq : A2 = -(∑ i, ∑ j, (A i j : ℚ) * (x i) * (x j)) := by
    rw [hA2, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [hmy i, hmy j]; ring
  -- assemble: `S = 2·(xᵀ A x) ≥ 0`
  have hStwo : S = 2 * (∑ i, ∑ j, (A i j : ℚ) * (x i) * (x j)) := by
    rw [hSeq, hA1z, hA3z, hA2eq]; ring
  rw [hq]
  linarith [hStwo ▸ hSnonneg]

/-! ## Structural clauses for the extended diagrams -/

/-- Each extended adjacency matrix is symmetric. -/
theorem AffineType.adj_isSymm (t : AffineType) : t.adj.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  cases t with
  | Atilde n hn =>
      simp only [AffineType.adj]; split_ifs <;> first | rfl | tauto
  | Dtilde n hn =>
      simp only [AffineType.adj, min_comm i.val j.val, max_comm i.val j.val]
  | E6tilde => simp only [AffineType.adj, min_comm i.val j.val, max_comm i.val j.val]
  | E7tilde => simp only [AffineType.adj, min_comm i.val j.val, max_comm i.val j.val]
  | E8tilde => simp only [AffineType.adj, min_comm i.val j.val, max_comm i.val j.val]

/-- No extended diagram has a self-loop. -/
theorem AffineType.adj_diag (t : AffineType) (i : Fin t.rank) : t.adj i i = 0 := by
  cases t with
  | Atilde n hn =>
      have hlt : i.val < n := i.isLt
      have hb : (i.val + 1) % n = if i.val + 1 = n then 0 else i.val + 1 := by
        by_cases h : i.val + 1 = n
        · rw [if_pos h, h, Nat.mod_self]
        · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]
      have hmod : ¬ ((i.val + 1) % n = i.val) := by
        rw [hb]; split_ifs <;> omega
      simp only [AffineType.adj]
      rw [if_neg (by tauto)]
  | Dtilde n hn =>
      simp only [AffineType.adj, min_self, max_self]
      rw [if_neg (by omega)]
  | E6tilde => fin_cases i <;> decide
  | E7tilde => fin_cases i <;> decide
  | E8tilde => fin_cases i <;> decide

/-- Every extended adjacency entry is `0` or `1` (a simple graph). -/
theorem AffineType.adj_zero_or_one (t : AffineType) (i j : Fin t.rank) :
    t.adj i j = 0 ∨ t.adj i j = 1 := by
  cases t <;> (simp only [AffineType.adj]; split_ifs <;> simp)

/-- The edge relation of a `0/1` adjacency matrix. Reducible so `decide` can see
through it on the finite exceptional diagrams. -/
private abbrev AdjEdge {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) : Prop :=
  adj a b = 1

/-- Convert reflexive-transitive `adj`-reachability into the explicit edge-path
required by `IsAffineDynkinDiagram`'s connectivity clause. -/
private theorem clause_of_reflTransGen {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    {i j : Fin n} (h : Relation.ReflTransGen (AdjEdge adj) i j) :
    ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (hk : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, hk⟩) = 1 := by
  obtain ⟨l, hne, hchain, hhead, hlast⟩ :=
    List.exists_isChain_ne_nil_of_relationReflTransGen h
  refine ⟨l, ?_, ?_, ?_⟩
  · rw [List.head?_eq_some_head hne, hhead]
  · rw [List.getLast?_eq_some_getLast hne, hlast]
  · intro k hk
    have hget := List.isChain_iff_getElem.mp hchain k hk
    simpa [List.get_eq_getElem, AdjEdge] using hget

/-- `adj`-reachability is symmetric when the matrix is symmetric (so every edge
can be traversed in both directions). -/
private theorem reflTransGen_symm {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hsymm : adj.IsSymm) {i j : Fin n}
    (h : Relation.ReflTransGen (AdjEdge adj) i j) :
    Relation.ReflTransGen (AdjEdge adj) j i := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih =>
      refine Relation.ReflTransGen.head ?_ ih
      change adj _ _ = 1
      rw [hsymm.apply]; exact hbc

/-- Reachability to any vertex, via a base point, gives full connectivity. -/
private theorem connected_of_reach_base {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hsymm : adj.IsSymm) (b : Fin n)
    (hreach : ∀ k, Relation.ReflTransGen (AdjEdge adj) b k) (i j : Fin n) :
    Relation.ReflTransGen (AdjEdge adj) i j :=
  (reflTransGen_symm hsymm (hreach i)).trans (hreach j)

/-- Connectivity of each extended diagram: any two vertices are joined by an
edge-path. -/
theorem AffineType.adj_connected (t : AffineType) (i j : Fin t.rank) :
    ∃ path : List (Fin t.rank),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        t.adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1 := by
  apply clause_of_reflTransGen
  cases t with
  | Atilde n hn =>
      have h0 : 0 < n := by omega
      have reach : ∀ m (hm : m < n),
          Relation.ReflTransGen (AdjEdge (AffineType.Atilde n hn).adj)
            ⟨0, h0⟩ ⟨m, hm⟩ := by
        intro m
        induction m with
        | zero => intro hm; exact .refl
        | succ p ih =>
            intro hm
            have hp : p < n := by omega
            refine (ih hp).tail ?_
            change (AffineType.Atilde n hn).adj ⟨p, hp⟩ ⟨p + 1, hm⟩ = 1
            simp only [AffineType.adj]
            rw [if_pos (Or.inl (Nat.mod_eq_of_lt hm))]
      exact (reflTransGen_symm (AffineType.adj_isSymm _) (reach i.val i.isLt)).trans
        (reach j.val j.isLt)
  | Dtilde n hn =>
      have hrank : (AffineType.Dtilde n hn).rank = n + 1 := rfl
      -- An edge of `D̃ₙ` from the explicit adjacency condition.
      have dEdge : ∀ (a b : ℕ) (ha : a < n + 1) (hb : b < n + 1),
          (min a b = 0 ∧ max a b = 2 ∨ min a b = 1 ∧ max a b = 2 ∨
           2 ≤ min a b ∧ max a b ≤ n - 2 ∧ min a b + 1 = max a b ∨
           min a b = n - 2 ∧ max a b = n - 1 ∨ min a b = n - 2 ∧ max a b = n) →
          (AffineType.Dtilde n hn).adj ⟨a, ha⟩ ⟨b, hb⟩ = 1 := by
        intro a b ha hb hcond
        simp only [AffineType.adj]
        rw [if_pos hcond]
      -- Reach along the central chain `2 — 3 — ⋯ — (n-2)`.
      have chainReach : ∀ (m : ℕ) (_ : 2 ≤ m) (hmn : m ≤ n - 2),
          Relation.ReflTransGen (AdjEdge (AffineType.Dtilde n hn).adj)
            ⟨2, by omega⟩ ⟨m, by omega⟩ := by
        intro m
        induction m with
        | zero => intro h _; omega
        | succ p ih =>
            intro hm2 hmn
            rcases Nat.lt_or_ge p 2 with hp | hp
            · have hp1 : p = 1 := by omega
              subst hp1; exact .refl
            · refine (ih hp (by omega)).tail ?_
              exact dEdge p (p + 1) (by omega) (by omega)
                (by right; right; left; exact ⟨by omega, by omega, by omega⟩)
      -- The leaf `0` connects to the chain start `2`.
      have e02 : Relation.ReflTransGen (AdjEdge (AffineType.Dtilde n hn).adj)
          ⟨0, by omega⟩ ⟨2, by omega⟩ :=
        .single (dEdge 0 2 (by omega) (by omega) (by left; exact ⟨by omega, by omega⟩))
      -- Reach from `0` to any vertex, by cases on which class it belongs to.
      have reachVal : ∀ (v : ℕ) (hv : v < n + 1),
          Relation.ReflTransGen (AdjEdge (AffineType.Dtilde n hn).adj)
            ⟨0, by omega⟩ ⟨v, hv⟩ := by
        intro v hv
        have hcl : v = 0 ∨ v = 1 ∨ (2 ≤ v ∧ v ≤ n - 2) ∨ v = n - 1 ∨ v = n := by omega
        rcases hcl with h | h | ⟨h2, h3⟩ | h | h
        · subst h; exact .refl
        · subst h
          exact e02.tail (dEdge 2 1 (by omega) (by omega)
            (by right; left; exact ⟨by omega, by omega⟩))
        · exact e02.trans (chainReach v h2 h3)
        · subst h
          exact (e02.trans (chainReach (n - 2) (by omega) (by omega))).tail
            (dEdge (n - 2) (n - 1) (by omega) (by omega)
              (by right; right; right; left; exact ⟨by omega, by omega⟩))
        · have hvn : (⟨v, hv⟩ : Fin (AffineType.Dtilde n hn).rank) = ⟨n, by omega⟩ :=
            Fin.ext (by omega)
          rw [hvn]
          exact (e02.trans (chainReach (n - 2) (by omega) (by omega))).tail
            (dEdge (n - 2) n (by omega) (by omega)
              (by right; right; right; right; exact ⟨by omega, by omega⟩))
      refine connected_of_reach_base (AffineType.adj_isSymm _) ⟨0, by omega⟩ ?_ i j
      intro k
      exact reachVal k.val k.isLt
  | E6tilde =>
      refine connected_of_reach_base (AffineType.adj_isSymm _) ⟨0, by decide⟩ ?_ i j
      intro k
      fin_cases k
      · exact .refl
      · exact .single (by decide)
      · refine .head (b := ⟨1, by decide⟩) ?_ (.single ?_) <;> decide
      · exact .single (by decide)
      · refine .head (b := ⟨3, by decide⟩) ?_ (.single ?_) <;> decide
      · exact .single (by decide)
      · refine .head (b := ⟨5, by decide⟩) ?_ (.single ?_) <;> decide
  | E7tilde =>
      refine connected_of_reach_base (AffineType.adj_isSymm _) ⟨0, by decide⟩ ?_ i j
      intro k
      fin_cases k
      · exact .refl
      · exact .single (by decide)
      · refine .head (b := ⟨1, by decide⟩) ?_ (.single ?_) <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_
          (.single ?_)) <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_
          (.head (b := ⟨3, by decide⟩) ?_ (.single ?_))) <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_
          (.head (b := ⟨3, by decide⟩) ?_ (.head (b := ⟨4, by decide⟩) ?_
            (.single ?_)))) <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_
          (.head (b := ⟨3, by decide⟩) ?_ (.head (b := ⟨4, by decide⟩) ?_
            (.head (b := ⟨5, by decide⟩) ?_ (.single ?_))))) <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_
          (.head (b := ⟨3, by decide⟩) ?_ (.single ?_))) <;> decide
  | E8tilde =>
      refine connected_of_reach_base (AffineType.adj_isSymm _) ⟨0, by decide⟩ ?_ i j
      intro k
      fin_cases k
      · exact .refl
      · exact .single (by decide)
      · refine .head (b := ⟨1, by decide⟩) ?_ (.single ?_) <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_
          (.single ?_)) <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_
          (.head (b := ⟨3, by decide⟩) ?_ (.single ?_))) <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_
          (.head (b := ⟨3, by decide⟩) ?_ (.head (b := ⟨4, by decide⟩) ?_
            (.single ?_)))) <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_
          (.head (b := ⟨3, by decide⟩) ?_ (.head (b := ⟨4, by decide⟩) ?_
            (.head (b := ⟨5, by decide⟩) ?_ (.single ?_))))) <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_
          (.head (b := ⟨3, by decide⟩) ?_ (.head (b := ⟨4, by decide⟩) ?_
            (.head (b := ⟨5, by decide⟩) ?_ (.head (b := ⟨6, by decide⟩) ?_
              (.single ?_)))))) <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.head (b := ⟨2, by decide⟩) ?_
          (.head (b := ⟨3, by decide⟩) ?_ (.head (b := ⟨4, by decide⟩) ?_
            (.head (b := ⟨5, by decide⟩) ?_ (.single ?_))))) <;> decide

/-- **(g, one direction)** Each extended diagram really is an affine Dynkin
diagram (its Cartan form is positive semidefinite but degenerate). -/
theorem isAffineDynkinDiagram_of_type (t : AffineType) :
    IsAffineDynkinDiagram t.rank t.adj := by
  have hsymm : t.adj.IsSymm := AffineType.adj_isSymm t
  refine ⟨hsymm, AffineType.adj_diag t, AffineType.adj_zero_or_one t,
    AffineType.adj_connected t, ?_, ?_⟩
  · -- positive semidefinite via the weighted-Laplacian criterion
    intro x
    have cartan_symm :
        (2 • (1 : Matrix (Fin t.rank) (Fin t.rank) ℤ) - t.adj).IsSymm :=
      (isSymm_one.smul 2).sub hsymm
    have cartan_off : ∀ i j, i ≠ j →
        (2 • (1 : Matrix (Fin t.rank) (Fin t.rank) ℤ) - t.adj) i j ≤ 0 := by
      intro i j hij
      have h1 : (1 : Matrix (Fin t.rank) (Fin t.rank) ℤ) i j = 0 :=
        Matrix.one_apply_ne hij
      have hval : (2 • (1 : Matrix (Fin t.rank) (Fin t.rank) ℤ) - t.adj) i j
          = - t.adj i j := by
        rw [Matrix.sub_apply, Matrix.smul_apply, h1, smul_zero, zero_sub]
      rw [hval]
      rcases AffineType.adj_zero_or_one t i j with h | h <;> rw [h] <;> omega
    exact posSemidef_of_nonpos_offDiag_kernel _ cartan_symm cartan_off t.marks
      (marks_pos t) (cartan_mulVec_marks_eq_zero t) x
  · -- degenerate: the marks are a nonzero null vector of the Cartan form
    refine ⟨t.marks, ?_, ?_⟩
    · intro h
      have hr : 0 < t.rank := by cases t <;> simp only [AffineType.rank] <;> omega
      have h0 := congrFun h ⟨0, hr⟩
      have hp := marks_pos t ⟨0, hr⟩
      simp only [Pi.zero_apply] at h0
      rw [h0] at hp
      exact lt_irrefl 0 hp
    · rw [cartan_mulVec_marks_eq_zero t, dotProduct_zero]

/-! ## Part (f): the classification of Dynkin diagrams -/

/-- **(f)** **Classification of Dynkin diagrams.** A connected simply-laced
graph on `n ≥ 1` vertices is a Dynkin diagram iff it is (graph-isomorphic to)
one of `Aₙ, Dₙ, E₆, E₇, E₈`. This is `Etingof.Theorem_Dynkin_classification`. -/
theorem dynkin_classification (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n) :
    IsDynkinDiagram n adj ↔
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n, ∀ i j, adj (σ i) (σ j) = t.adj i j :=
  Etingof.Theorem_Dynkin_classification n adj hn

/-! ## Part (g): the classification of affine Dynkin diagrams -/

/-- **Graph-isomorphism invariance of the affine predicate.** If `adj'` is the
image of `adj` under a graph isomorphism `σ`, and `adj` is an affine Dynkin
diagram, then so is `adj'`. This is the affine analogue of
`Etingof.isDynkinDiagram_of_graph_iso`: the six defining clauses (symmetry, zero
diagonal, `0/1` entries, connectivity, positive-semidefiniteness, degeneracy) are
each preserved by reindexing the quadratic form and the connectivity paths along
`σ`; the null vector witnessing degeneracy is transported by `x ↦ x ∘ σ.symm`. -/
lemma isAffineDynkinDiagram_of_graph_iso {n m : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    {adj' : Matrix (Fin m) (Fin m) ℤ} (σ : Fin n ≃ Fin m)
    (hiso : ∀ i j, adj' (σ i) (σ j) = adj i j)
    (hD : IsAffineDynkinDiagram n adj) : IsAffineDynkinDiagram m adj' := by
  obtain ⟨hsymm, hdiag, h01, hconn, hpos, hdeg⟩ := hD
  have rw_adj' : ∀ i j : Fin m, adj' i j = adj (σ.symm i) (σ.symm j) := by
    intro i j
    conv_lhs => rw [show i = σ (σ.symm i) from (σ.apply_symm_apply i).symm,
      show j = σ (σ.symm j) from (σ.apply_symm_apply j).symm]
    exact hiso _ _
  -- The quadratic form is invariant under reindexing by `σ`; used for both the
  -- positive-semidefinite and the degeneracy clauses.
  have hform : ∀ x : Fin m → ℤ,
      dotProduct x ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj').mulVec x) =
        dotProduct (x ∘ σ)
          ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (x ∘ σ)) := by
    intro x
    simp only [dotProduct, mulVec, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Function.comp]
    symm
    apply Fintype.sum_equiv σ; intro i; congr 1
    apply Fintype.sum_equiv σ; intro j
    simp only [hiso, σ.injective.eq_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Symmetry
    exact Matrix.IsSymm.ext (fun i j => by rw [rw_adj', rw_adj']; exact hsymm.apply _ _)
  · -- Zero diagonal
    intro i; rw [rw_adj']; exact hdiag _
  · -- 0-1 entries
    intro i j; rw [rw_adj']; exact h01 _ _
  · -- Connectivity
    intro i j
    obtain ⟨path, hhead, hlast, hedges⟩ := hconn (σ.symm i) (σ.symm j)
    refine ⟨path.map σ, ?_, ?_, ?_⟩
    · cases path with
      | nil => exact absurd hhead (by simp)
      | cons a _ =>
        simp only [List.map, List.head?]; rw [List.head?] at hhead
        exact congr_arg _ (Option.some.inj hhead ▸ σ.apply_symm_apply i)
    · rw [List.getLast?_map, hlast]; simp [σ.apply_symm_apply]
    · intro k hk
      have hk' : k + 1 < path.length := by rwa [List.length_map] at hk
      change adj' (path.map σ)[k] (path.map σ)[k + 1] = 1
      rw [List.getElem_map, List.getElem_map, hiso]
      exact hedges k hk'
  · -- Positive semidefinite
    intro x; rw [hform x]; exact hpos (x ∘ σ)
  · -- Degenerate: transport the null vector by `x ∘ σ.symm`
    obtain ⟨x, hx_ne, hx0⟩ := hdeg
    refine ⟨x ∘ σ.symm, ?_, ?_⟩
    · intro h; apply hx_ne; ext i
      have := congr_fun h (σ i); simpa [Function.comp] using this
    · rw [hform (x ∘ σ.symm)]
      have hxx : (x ∘ σ.symm) ∘ σ = x := by ext i; simp [Function.comp]
      rw [hxx]; exact hx0

/-- **Discrete Perron–Frobenius for an affine Dynkin diagram.** The Cartan form
`A = 2·Id − adj` of an affine Dynkin diagram is positive semidefinite but
degenerate, and — because the graph is connected (irreducibility) — its kernel is
spanned by a *strictly positive* integer vector `w` (the marks). Concretely there
is `w : Fin n → ℤ` with every `w i > 0` and `A ·ᵥ w = 0`.

The proof is the standard sign-folding argument. From a degenerate null vector `x`
(the form vanishes on it) the entrywise absolute value `w = |x|` still makes the
form vanish: replacing `xᵢxⱼ` by `|xᵢ||xⱼ| ≥ xᵢxⱼ` can only *lower* the value
`2∑xᵢ² − ∑adjᵢⱼxᵢxⱼ`, while positive-semidefiniteness bounds it below by `0`, so
`A(w) = 0` too. Polarization at each basis vector `eₖ` (using that the quadratic
coefficient `A(w) = 0` kills the `t²` term of `A(t·w + eₖ) ≥ 0`) forces
`(A ·ᵥ w) k = 0`, i.e. `A ·ᵥ w = 0`. Finally the zero-set of `w` is closed under
adjacency (`2wₚ = ∑ⱼ adjₚⱼ wⱼ` with `wₚ = 0` and all terms nonnegative forces every
neighbour's weight to vanish); connectivity then propagates `w = 0` from any zero
entry to the nonzero entry witnessing `x ≠ 0`, a contradiction. Hence `w > 0`. -/
lemma affineNullVector_pos {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n)
    (hD : IsAffineDynkinDiagram n adj) :
    ∃ w : Fin n → ℤ, (∀ i, 0 < w i) ∧
      (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec w = 0 := by
  classical
  obtain ⟨hsymm, hdiag, h01, hconn, hpos, hdeg⟩ := hD
  obtain ⟨x, hx_ne, hx0⟩ := hdeg
  set M := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) with hM_def
  -- Entries of the Cartan matrix.
  have hMij : ∀ i j, M i j = (if i = j then 2 else 0) - adj i j := by
    intro i j
    rw [hM_def, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, nsmul_eq_mul]
    split_ifs <;> norm_num
  have hMsym_ij : ∀ i j, M i j = M j i := by
    intro i j
    have hsymm' : adj i j = adj j i := by
      have h := congrFun (congrFun hsymm j) i
      rw [Matrix.transpose_apply] at h; exact h
    rw [hMij i j, hMij j i, hsymm']
    rcases eq_or_ne i j with h | h
    · rw [h]
    · rw [if_neg h, if_neg (fun hji => h hji.symm)]
  -- Bilinear form expansion `uᵀ M v = ∑ᵢ∑ⱼ uᵢ Mᵢⱼ vⱼ`.
  have Bform : ∀ u v : Fin n → ℤ,
      dotProduct u (M.mulVec v) = ∑ i, ∑ j, u i * M i j * v j := by
    intro u v
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  -- Symmetry of the form.
  have hdotcomm : ∀ u v : Fin n → ℤ,
      dotProduct u (M.mulVec v) = dotProduct v (M.mulVec u) := by
    intro u v
    rw [Bform u v, Bform v u, Finset.sum_comm]
    exact Finset.sum_congr rfl
      (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hMsym_ij b a]; ring))
  -- The nonnegative folded vector `w = |x|`.
  set w : Fin n → ℤ := fun i => |x i| with hw
  have hwi : ∀ i, w i = |x i| := by intro i; rw [hw]
  have hw_nonneg : ∀ i, 0 ≤ w i := by intro i; rw [hwi i]; exact abs_nonneg _
  -- Termwise the folded form dominates from below: `wᵢMᵢⱼwⱼ ≤ xᵢMᵢⱼxⱼ`.
  have habs_le : ∀ a b : ℤ, a * b ≤ |a| * |b| := by
    intro a b; rw [← abs_mul]; exact le_abs_self _
  have hterm : ∀ i j, w i * M i j * w j ≤ x i * M i j * x j := by
    intro i j
    rw [hwi i, hwi j, hMij i j]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hdiag i]
      nlinarith [abs_mul_abs_self (x i)]
    · rw [if_neg hij]
      have ha : 0 ≤ adj i j := by rcases h01 i j with h | h <;> omega
      have hb : x i * x j ≤ |x i| * |x j| := habs_le (x i) (x j)
      nlinarith [ha, hb, mul_nonneg ha (sub_nonneg.mpr hb)]
  -- Hence `A(w) ≤ A(x) = 0`, and `A(w) ≥ 0`, so `A(w) = 0`.
  have hle : dotProduct w (M.mulVec w) ≤ dotProduct x (M.mulVec x) := by
    rw [Bform w w, Bform x x]
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
  have hQw0 : dotProduct w (M.mulVec w) = 0 :=
    le_antisymm (hle.trans_eq hx0) (hpos w)
  -- Polarization: `A(w) = 0` and semidefiniteness force `A ·ᵥ w = 0`.
  have hsingle : ∀ (k : Fin n) (u : Fin n → ℤ),
      dotProduct (Pi.single k (1:ℤ)) u = u k := by
    intro k u
    simp only [dotProduct]
    rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same, one_mul]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hMkk : ∀ k : Fin n, (M.mulVec (Pi.single k (1:ℤ))) k = 2 := by
    intro k
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same, mul_one, hMij, if_pos rfl, hdiag k, sub_zero]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hMw : M.mulVec w = 0 := by
    funext k
    have hbil : ∀ t : ℤ,
        dotProduct (t • w + Pi.single k (1:ℤ)) (M.mulVec (t • w + Pi.single k (1:ℤ)))
          = 2 * t * (M.mulVec w) k + 2 := by
      intro t
      have expand : dotProduct (t • w + Pi.single k (1:ℤ))
            (M.mulVec (t • w + Pi.single k (1:ℤ)))
          = t * (t * dotProduct w (M.mulVec w))
            + t * dotProduct w (M.mulVec (Pi.single k (1:ℤ)))
            + t * dotProduct (Pi.single k (1:ℤ)) (M.mulVec w)
            + dotProduct (Pi.single k (1:ℤ)) (M.mulVec (Pi.single k (1:ℤ))) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
        simp only [dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul,
          smul_eq_mul]
        ring
      rw [expand, hQw0, hdotcomm w (Pi.single k (1:ℤ)),
        hsingle k (M.mulVec w), hsingle k (M.mulVec (Pi.single k (1:ℤ))), hMkk k]
      ring
    have hge : ∀ t : ℤ, 0 ≤ 2 * t * (M.mulVec w) k + 2 := by
      intro t; rw [← hbil t]; exact hpos _
    have h1 := hge 2
    have h2 := hge (-2)
    have hzero : (M.mulVec w) k = 0 := by omega
    simpa using hzero
  -- Strict positivity via connectivity (irreducibility).
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a
    rw [Matrix.transpose_apply] at h; exact h
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => adj i j = 1
      symm := ⟨fun i j h => by rw [hsymm' j i]; exact h⟩
      loopless := ⟨fun i h => by rw [hdiag i] at h; exact absurd h (by norm_num)⟩ }
  have hGadj : ∀ a b, adj a b = 1 → G.Adj a b := fun _ _ h => h
  haveI hNe : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hpre : G.Preconnected := by
    intro i j
    obtain ⟨p, hhead, hlast, hpath⟩ := hconn i j
    have hne : p ≠ [] := by rintro rfl; simp at hhead
    have hchain : List.IsChain (fun a b => adj a b = 1) p := by
      rw [List.isChain_iff_getElem]; intro k hk; exact hpath k hk
    have hi : p.head hne = i :=
      Option.some_inj.mp ((List.head?_eq_some_head hne).symm.trans hhead)
    have hj : p.getLast hne = j := by
      have := (List.getLast?_eq_getLast_of_ne_nil hne).symm.trans hlast
      exact Option.some_inj.mp this
    have hrtg := List.relationReflTransGen_of_exists_isChain p hchain hne
    rw [hi, hj] at hrtg
    exact (SimpleGraph.reachable_iff_reflTransGen i j).mpr
      (Relation.ReflTransGen.mono (fun a b h => hGadj a b h) hrtg)
  have hconn' : G.Connected := ⟨hpre⟩
  -- Edge propagation of the zero-set: an edge out of a zero entry lands on a zero entry.
  have hprop : ∀ p q, G.Adj p q → w p = 0 → w q = 0 := by
    intro p q hpq hwp
    have hpq' : adj p q = 1 := hpq
    have h0 : (M.mulVec w) p = 0 := by rw [hMw]; rfl
    have hrow : (M.mulVec w) p = ∑ j, ((if p = j then 2 else 0) - adj p j) * w j := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl (fun j _ => by rw [hMij p j])
    rw [hrow] at h0
    have hsplit : ∑ j, ((if p = j then (2:ℤ) else 0) - adj p j) * w j
        = (∑ j, (if p = j then (2:ℤ) else 0) * w j) - ∑ j, adj p j * w j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hdiagsum : ∑ j, (if p = j then (2:ℤ) else 0) * w j = 0 := by
      rw [Finset.sum_eq_single p
        (fun b _ hb => by rw [if_neg (fun h => hb h.symm), zero_mul])
        (fun h => absurd (Finset.mem_univ p) h)]
      rw [if_pos rfl, hwp, mul_zero]
    rw [hsplit, hdiagsum] at h0
    have hsum0 : ∑ j, adj p j * w j = 0 := by linarith [h0]
    have hnn : ∀ j, 0 ≤ adj p j * w j := by
      intro j; rcases h01 p j with h | h
      · rw [h, zero_mul]
      · rw [h, one_mul]; exact hw_nonneg j
    have hterm0 : adj p q * w q = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).mp hsum0 q (Finset.mem_univ q)
    rw [hpq', one_mul] at hterm0
    exact hterm0
  -- `x ≠ 0` gives a strictly positive entry of `w`.
  obtain ⟨m, hm⟩ : ∃ m, x m ≠ 0 := by
    obtain ⟨m, hm⟩ := Function.ne_iff.mp hx_ne
    exact ⟨m, by simpa using hm⟩
  have hwm : 0 < w m := by rw [hwi m]; exact abs_pos.mpr hm
  refine ⟨w, ?_, hMw⟩
  intro i
  rcases lt_or_eq_of_le (hw_nonneg i) with h | h
  · exact h
  · exfalso
    have hzero : w i = 0 := h.symm
    have hreach : Relation.ReflTransGen G.Adj i m :=
      (SimpleGraph.reachable_iff_reflTransGen i m).mp (hconn'.preconnected i m)
    have hprop_chain : ∀ v, Relation.ReflTransGen G.Adj i v → w v = 0 := by
      intro v hv
      induction hv with
      | refl => exact hzero
      | tail _ hadj ih => exact hprop _ _ hadj ih
    rw [hprop_chain m hreach] at hwm
    exact lt_irrefl 0 hwm

/-! ## Minimality: proper connected induced subgraphs are finite Dynkin

Step 2 of the ⟹ direction of `affine_dynkin_classification`. Deleting any single
vertex `v` from an affine Dynkin diagram turns its (positive-semidefinite,
degenerate) Cartan form into a positive-*definite* one on the surviving vertices:
the strictly-positive null vector `w` (`affineNullVector_pos`) spans the whole
kernel, and it has `w v > 0`, so no nonzero vector supported off `v` can lie in
the kernel. Hence every proper connected induced subgraph is a finite Dynkin
diagram, classified by `dynkin_classification`. -/

/-- **Radical = kernel.** For the Cartan form `A = 2·Id − adj` of an affine Dynkin
diagram (positive semidefinite, symmetric, zero diagonal so `A_{kk} = 2`), a vector
on which the quadratic form vanishes lies in the kernel: `yᵀ A y = 0 → A ·ᵥ y = 0`.
Polarization: `A(t·y + eₖ) = 2t·(A ·ᵥ y)_k + 2 ≥ 0` for all `t` forces `(A ·ᵥ y)_k = 0`. -/
lemma affine_cartan_mulVec_eq_zero_of_form_zero {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ) (hD : IsAffineDynkinDiagram n adj)
    {y : Fin n → ℤ}
    (hy : dotProduct y ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec y) = 0) :
    (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec y = 0 := by
  classical
  obtain ⟨hsymm, hdiag, h01, hconn, hpos, hdeg⟩ := hD
  set M := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) with hM_def
  have hMij : ∀ i j, M i j = (if i = j then 2 else 0) - adj i j := by
    intro i j
    rw [hM_def, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, nsmul_eq_mul]
    split_ifs <;> norm_num
  have hMsym_ij : ∀ i j, M i j = M j i := by
    intro i j
    have hsymm' : adj i j = adj j i := by
      have h := congrFun (congrFun hsymm j) i
      rw [Matrix.transpose_apply] at h; exact h
    rw [hMij i j, hMij j i, hsymm']
    rcases eq_or_ne i j with h | h
    · rw [h]
    · rw [if_neg h, if_neg (fun hji => h hji.symm)]
  have Bform : ∀ u v : Fin n → ℤ,
      dotProduct u (M.mulVec v) = ∑ i, ∑ j, u i * M i j * v j := by
    intro u v
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hdotcomm : ∀ u v : Fin n → ℤ,
      dotProduct u (M.mulVec v) = dotProduct v (M.mulVec u) := by
    intro u v
    rw [Bform u v, Bform v u, Finset.sum_comm]
    exact Finset.sum_congr rfl
      (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hMsym_ij b a]; ring))
  have hsingle : ∀ (k : Fin n) (u : Fin n → ℤ),
      dotProduct (Pi.single k (1:ℤ)) u = u k := by
    intro k u
    simp only [dotProduct]
    rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same, one_mul]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hMkk : ∀ k : Fin n, (M.mulVec (Pi.single k (1:ℤ))) k = 2 := by
    intro k
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same, mul_one, hMij, if_pos rfl, hdiag k, sub_zero]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  funext k
  have hbil : ∀ t : ℤ,
      dotProduct (t • y + Pi.single k (1:ℤ)) (M.mulVec (t • y + Pi.single k (1:ℤ)))
        = 2 * t * (M.mulVec y) k + 2 := by
    intro t
    have expand : dotProduct (t • y + Pi.single k (1:ℤ))
          (M.mulVec (t • y + Pi.single k (1:ℤ)))
        = t * (t * dotProduct y (M.mulVec y))
          + t * dotProduct y (M.mulVec (Pi.single k (1:ℤ)))
          + t * dotProduct (Pi.single k (1:ℤ)) (M.mulVec y)
          + dotProduct (Pi.single k (1:ℤ)) (M.mulVec (Pi.single k (1:ℤ))) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      simp only [dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      ring
    rw [expand, hy, hdotcomm y (Pi.single k (1:ℤ)),
      hsingle k (M.mulVec y), hsingle k (M.mulVec (Pi.single k (1:ℤ))), hMkk k]
    ring
  have hge : ∀ t : ℤ, 0 ≤ 2 * t * (M.mulVec y) k + 2 := by
    intro t; rw [← hbil t]; exact hpos _
  have h1 := hge 2
  have h2 := hge (-2)
  have hzero : (M.mulVec y) k = 0 := by omega
  simpa using hzero

/-- **Kernel is a line.** If the affine Cartan form vanishes on an integer vector
`y` which is zero at some vertex `v`, then `y = 0`. Indeed `A ·ᵥ y = 0`
(`affine_cartan_mulVec_eq_zero_of_form_zero`); with the strictly-positive kernel
vector `w` from `affineNullVector_pos`, take `p` minimizing `yₚ/wₚ` so that
`z := wₚ·y − yₚ·w ≥ 0` is a nonnegative kernel vector with `zₚ = 0`; edge
propagation along the connected graph forces `z = 0`, i.e. `y` is proportional to
`w`. Since `w v > 0` and `y v = 0`, the proportionality constant is `0`, so `y = 0`. -/
lemma affine_kernel_off_vertex_eq_zero {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj)
    {y : Fin n → ℤ}
    (hy : dotProduct y ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec y) = 0)
    {v : Fin n} (hyv : y v = 0) : y = 0 := by
  classical
  obtain ⟨w, hw_pos, hMw⟩ := affineNullVector_pos adj hn hD
  have hMy : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec y = 0 :=
    affine_cartan_mulVec_eq_zero_of_form_zero adj hD hy
  obtain ⟨hsymm, hdiag, h01, hconn, _, _⟩ := hD
  set M := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) with hM_def
  have hMij : ∀ i j, M i j = (if i = j then 2 else 0) - adj i j := by
    intro i j
    rw [hM_def, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, nsmul_eq_mul]
    split_ifs <;> norm_num
  -- Choose `p` minimizing the ratio `yᵢ / wᵢ` over `ℚ`.
  have hwq : ∀ i, (0:ℚ) < (w i : ℚ) := fun i => by exact_mod_cast hw_pos i
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ
      (fun i => (y i : ℚ) / (w i : ℚ)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  -- The integer vector `z i = wₚ·yᵢ − yₚ·wᵢ`.
  set z : Fin n → ℤ := fun i => w p * y i - y p * w i with hz_def
  have hzp : z p = 0 := by simp only [hz_def]; ring
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    have hpi := hp i (Finset.mem_univ i)
    rw [div_le_div_iff₀ (hwq p) (hwq i)] at hpi
    have hcast : (y p : ℤ) * w i ≤ y i * w p := by exact_mod_cast hpi
    simp only [hz_def]; linarith
  have hz_eq : z = w p • y - y p • w := by
    funext i; simp only [hz_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hMz : M.mulVec z = 0 := by
    rw [hz_eq, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hMy, hMw,
      smul_zero, smul_zero, sub_zero]
  -- Edge propagation of the zero-set of `z` along the connected graph.
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a
    rw [Matrix.transpose_apply] at h; exact h
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => adj i j = 1
      symm := ⟨fun i j h => by rw [hsymm' j i]; exact h⟩
      loopless := ⟨fun i h => by rw [hdiag i] at h; exact absurd h (by norm_num)⟩ }
  have hGadj : ∀ a b, adj a b = 1 → G.Adj a b := fun _ _ h => h
  haveI hNe : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hpre : G.Preconnected := by
    intro i j
    obtain ⟨q, hhead, hlast, hpath⟩ := hconn i j
    have hne : q ≠ [] := by rintro rfl; simp at hhead
    have hchain : List.IsChain (fun a b => adj a b = 1) q := by
      rw [List.isChain_iff_getElem]; intro k hk; exact hpath k hk
    have hi : q.head hne = i :=
      Option.some_inj.mp ((List.head?_eq_some_head hne).symm.trans hhead)
    have hj : q.getLast hne = j := by
      have := (List.getLast?_eq_getLast_of_ne_nil hne).symm.trans hlast
      exact Option.some_inj.mp this
    have hrtg := List.relationReflTransGen_of_exists_isChain q hchain hne
    rw [hi, hj] at hrtg
    exact (SimpleGraph.reachable_iff_reflTransGen i j).mpr
      (Relation.ReflTransGen.mono (fun a b h => hGadj a b h) hrtg)
  have hconn' : G.Connected := ⟨hpre⟩
  have hprop : ∀ a b, G.Adj a b → z a = 0 → z b = 0 := by
    intro a b hab hza
    have hab' : adj a b = 1 := hab
    have h0 : (M.mulVec z) a = 0 := by rw [hMz]; rfl
    have hrow : (M.mulVec z) a = ∑ j, ((if a = j then 2 else 0) - adj a j) * z j := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl (fun j _ => by rw [hMij a j])
    rw [hrow] at h0
    have hsplit : ∑ j, ((if a = j then (2:ℤ) else 0) - adj a j) * z j
        = (∑ j, (if a = j then (2:ℤ) else 0) * z j) - ∑ j, adj a j * z j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hdiagsum : ∑ j, (if a = j then (2:ℤ) else 0) * z j = 0 := by
      rw [Finset.sum_eq_single a
        (fun b _ hb => by rw [if_neg (fun h => hb h.symm), zero_mul])
        (fun h => absurd (Finset.mem_univ a) h)]
      rw [if_pos rfl, hza, mul_zero]
    rw [hsplit, hdiagsum] at h0
    have hsum0 : ∑ j, adj a j * z j = 0 := by linarith [h0]
    have hnn : ∀ j, 0 ≤ adj a j * z j := by
      intro j; rcases h01 a j with h | h
      · rw [h, zero_mul]
      · rw [h, one_mul]; exact hz_nonneg j
    have hterm0 : adj a b * z b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).mp hsum0 b (Finset.mem_univ b)
    rw [hab', one_mul] at hterm0
    exact hterm0
  have hz0 : ∀ i, z i = 0 := by
    have hchainprop : ∀ i, Relation.ReflTransGen G.Adj p i → z i = 0 := by
      intro i hv
      induction hv with
      | refl => exact hzp
      | tail _ hadj ih => exact hprop _ _ hadj ih
    intro i
    exact hchainprop i
      ((SimpleGraph.reachable_iff_reflTransGen p i).mp (hconn'.preconnected p i))
  -- `z = 0` means `wₚ·y = yₚ·w`; specialize at `v` and use `w > 0`.
  have key : ∀ i, w p * y i = y p * w i := by
    intro i; have hzi := hz0 i; simp only [hz_def] at hzi; linarith
  have hyp0 : y p = 0 := by
    have hv := key v
    rw [hyv, mul_zero] at hv
    rcases mul_eq_zero.mp hv.symm with h | h
    · exact h
    · exact absurd h (ne_of_gt (hw_pos v))
  funext i
  have hi := key i
  rw [hyp0, zero_mul] at hi
  rcases mul_eq_zero.mp hi with h | h
  · exact absurd h (ne_of_gt (hw_pos p))
  · simpa using h

/-- **Restricted positive-definiteness.** Along any injection `e : Fin m ↪ Fin n`
that misses some vertex `v`, the induced Cartan form `2·Id − adj∘(e,e)` is
positive *definite*: the extension-by-zero `x̂` of a nonzero `x` is a nonzero
vector supported off `v` on which the affine form would have to vanish, impossible
by `affine_kernel_off_vertex_eq_zero`. -/
lemma affine_restrict_posDef {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n)
    (hD : IsAffineDynkinDiagram n adj) {m : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) {v : Fin n} (hv : ∀ i, e i ≠ v) :
    ∀ x : Fin m → ℤ, x ≠ 0 →
      0 < dotProduct x
        ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj.submatrix e e).mulVec x) := by
  classical
  intro x hx
  set N := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) with hN
  set Nsub := (2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj.submatrix e e) with hNsub_def
  set xhat : Fin n → ℤ := Function.extend e x 0 with hxhat
  have hxe : ∀ i, xhat (e i) = x i := by
    intro i; rw [hxhat]; exact he.extend_apply x 0 i
  have hxv : xhat v = 0 := by
    rw [hxhat, Function.extend_apply' x (0 : Fin n → ℤ) v
      (by rintro ⟨i, rfl⟩; exact hv i rfl)]; rfl
  have hNsub : ∀ i j, Nsub i j = N (e i) (e j) := by
    intro i j
    simp only [hNsub_def, hN, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.submatrix_apply, he.eq_iff]
  -- Reindex: sums against `xhat` collapse to sums over `e`.
  have hreindex : ∀ F : Fin n → ℤ, (∑ k, xhat k * F k) = ∑ i, x i * F (e i) := by
    intro F
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨e, he⟩))
          (fun k _ hk => by
            have hk' : ¬ ∃ i, e i = k := by
              simpa [Finset.mem_map] using hk
            rw [hxhat, Function.extend_apply' x (0 : Fin n → ℤ) k hk']; simp)]
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl (fun i _ => by
      simp only [Function.Embedding.coeFn_mk]; rw [hxe i])
  have hform : dotProduct xhat (N.mulVec xhat) = dotProduct x (Nsub.mulVec x) := by
    calc dotProduct xhat (N.mulVec xhat)
        = ∑ k, xhat k * (∑ l, N k l * xhat l) := by
              simp only [dotProduct, Matrix.mulVec]
      _ = ∑ i, x i * (∑ l, N (e i) l * xhat l) := hreindex _
      _ = ∑ i, x i * (∑ j, x j * N (e i) (e j)) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              congr 1
              rw [show (∑ l, N (e i) l * xhat l) = ∑ l, xhat l * N (e i) l from
                Finset.sum_congr rfl (fun l _ => mul_comm _ _)]
              exact hreindex (fun l => N (e i) l)
      _ = ∑ i, x i * (∑ j, Nsub i j * x j) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              congr 1
              exact Finset.sum_congr rfl (fun j _ => by rw [hNsub i j]; ring)
      _ = dotProduct x (Nsub.mulVec x) := by simp only [dotProduct, Matrix.mulVec]
  have hpos := hD.2.2.2.2.1
  have hge : 0 ≤ dotProduct xhat (N.mulVec xhat) := hpos xhat
  rw [hform] at hge
  rcases lt_or_eq_of_le hge with h | h
  · exact h
  · exfalso
    have hxhat0form : dotProduct xhat (N.mulVec xhat) = 0 := by rw [hform]; exact h.symm
    have hxhat0 : xhat = 0 :=
      affine_kernel_off_vertex_eq_zero adj hn hD hxhat0form hxv
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact hi (by rw [← hxe i, hxhat0]; rfl)

/-- **Minimality (finite-Dynkin restriction).** Any *proper* connected induced
subgraph of an affine Dynkin diagram is a finite Dynkin diagram: along an
injection `e` missing a vertex `v`, if the induced adjacency `adj∘(e,e)` is itself
connected, then it satisfies `IsDynkinDiagram`. This is the key exported fact for
the cyclic/tree case analyses (#6792, #6793). -/
lemma affine_properInduced_isDynkin {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj) {m : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) {v : Fin n} (hv : ∀ i, e i ≠ v)
    (hconn : ∀ i j : Fin m, ∃ path : List (Fin m),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        (adj.submatrix e e) (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) :
    IsDynkinDiagram m (adj.submatrix e e) := by
  have hsymm := hD.1
  have hdiag := hD.2.1
  have h01 := hD.2.2.1
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a
    rw [Matrix.transpose_apply] at h; exact h
  refine ⟨?_, ?_, ?_, hconn, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
    exact hsymm' (e j) (e i)
  · intro i; simp only [Matrix.submatrix_apply]; exact hdiag (e i)
  · intro i j; simp only [Matrix.submatrix_apply]; exact h01 (e i) (e j)
  · exact affine_restrict_posDef adj hn hD e he hv

/-- **Minimality, classified form.** A proper connected induced subgraph of an
affine Dynkin diagram is graph-isomorphic to one of the finite types
`Aₖ, Dₖ, E₆, E₇, E₈` (via `dynkin_classification`). -/
lemma affine_properInduced_finiteDynkin {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj) {m : ℕ} (hm : 1 ≤ m)
    (e : Fin m → Fin n) (he : Function.Injective e) {v : Fin n} (hv : ∀ i, e i ≠ v)
    (hconn : ∀ i j : Fin m, ∃ path : List (Fin m),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        (adj.submatrix e e) (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) :
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin m,
      ∀ i j, (adj.submatrix e e) (σ i) (σ j) = t.adj i j :=
  (dynkin_classification m (adj.submatrix e e) hm).mp
    (affine_properInduced_isDynkin adj hn hD e he hv hconn)

/-! ### Cyclic case: a connected `2`-regular graph is the cycle `Ãₙ`

The remaining combinatorial content behind the cyclic branch of the ⟹ direction
(#6792, #6847). We walk around the cycle: at a vertex `b` reached from `a`, the
"other neighbour" `otherNbr adj b a` is the unique neighbour of `b` distinct from
`a`. Iterating the pair-map `(a, b) ↦ (b, otherNbr adj b a)` traces the cycle;
`Function.minimalPeriod` supplies the wrap-around, connectivity the surjectivity,
and a minimal-gap induction the injectivity. -/

open Classical in
/-- The **other neighbour** of `b` relative to `a`: when `a` is a neighbour of `b`
and `b` has exactly two neighbours, this is the unique neighbour of `b` other than
`a`; otherwise it is `a`. Defined so that `a ↦ otherNbr adj b a` is the involution
swapping `b`'s two neighbours (and fixing everything else). -/
noncomputable def otherNbr {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (b a : Fin n) :
    Fin n :=
  if h : a ∈ univ.filter (fun j => adj b j = 1) ∧
         ((univ.filter (fun j => adj b j = 1)).erase a).Nonempty
  then h.2.choose else a

variable {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}

/-- If `a` is a neighbour of `b` with `b` of degree `2`, then `otherNbr adj b a`
lies in the neighbour set with `a` deleted. -/
private lemma otherNbr_mem_erase {b a : Fin n}
    (hcard : (univ.filter (fun j => adj b j = 1)).card = 2)
    (ha : a ∈ univ.filter (fun j => adj b j = 1)) :
    otherNbr adj b a ∈ (univ.filter (fun j => adj b j = 1)).erase a := by
  have hne : ((univ.filter (fun j => adj b j = 1)).erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha, hcard]; omega
  rw [otherNbr, dif_pos ⟨ha, hne⟩]
  exact hne.choose_spec

/-- `otherNbr adj b a` is a neighbour of `b`. -/
private lemma otherNbr_adj {b a : Fin n}
    (hcard : (univ.filter (fun j => adj b j = 1)).card = 2)
    (ha : adj b a = 1) : adj b (otherNbr adj b a) = 1 := by
  have ha' : a ∈ univ.filter (fun j => adj b j = 1) := by simp [ha]
  have := otherNbr_mem_erase hcard ha'
  rw [Finset.mem_erase, Finset.mem_filter] at this
  exact this.2.2

/-- `otherNbr adj b a ≠ a` when `a` is a neighbour of `b`. -/
private lemma otherNbr_ne {b a : Fin n}
    (hcard : (univ.filter (fun j => adj b j = 1)).card = 2)
    (ha : adj b a = 1) : otherNbr adj b a ≠ a := by
  have ha' : a ∈ univ.filter (fun j => adj b j = 1) := by simp [ha]
  have := otherNbr_mem_erase hcard ha'
  rw [Finset.mem_erase] at this
  exact this.1

/-- The characterisation: the other neighbour is *the* neighbour distinct from `a`. -/
private lemma otherNbr_eq {b a c : Fin n}
    (hcard : (univ.filter (fun j => adj b j = 1)).card = 2)
    (ha : adj b a = 1) (hc : adj b c = 1) (hca : c ≠ a) :
    otherNbr adj b c = a := by
  have ha' : a ∈ univ.filter (fun j => adj b j = 1) := by simp [ha]
  have hc' : c ∈ univ.filter (fun j => adj b j = 1) := by simp [hc]
  -- `erase c` has card `1`; both `a` and `otherNbr adj b c` lie in it, hence equal.
  have hcard1 : ((univ.filter (fun j => adj b j = 1)).erase c).card = 1 := by
    rw [Finset.card_erase_of_mem hc', hcard]
  have hle : ((univ.filter (fun j => adj b j = 1)).erase c).card ≤ 1 := by omega
  have ha_erase : a ∈ (univ.filter (fun j => adj b j = 1)).erase c :=
    Finset.mem_erase.mpr ⟨hca.symm, ha'⟩
  have ho_erase := otherNbr_mem_erase hcard hc'
  exact (Finset.card_le_one.mp hle _ ho_erase _ ha_erase)

/-- Off the neighbour set, `otherNbr` is the identity. -/
private lemma otherNbr_eq_self {b a : Fin n}
    (ha : a ∉ univ.filter (fun j => adj b j = 1)) : otherNbr adj b a = a := by
  rw [otherNbr, dif_neg]
  rintro ⟨h, -⟩; exact ha h

/-- `a ↦ otherNbr adj b a` is an involution (when every vertex has degree `2`). -/
private lemma otherNbr_involutive
    (hdeg : ∀ v, (univ.filter (fun j => adj v j = 1)).card = 2) (b a : Fin n) :
    otherNbr adj b (otherNbr adj b a) = a := by
  by_cases ha : a ∈ univ.filter (fun j => adj b j = 1)
  · have ha1 : adj b a = 1 := by simpa using (Finset.mem_filter.mp ha).2
    have hc1 : adj b (otherNbr adj b a) = 1 := otherNbr_adj (hdeg b) ha1
    have hcne : otherNbr adj b a ≠ a := otherNbr_ne (hdeg b) ha1
    exact otherNbr_eq (hdeg b) ha1 hc1 hcne
  · rw [otherNbr_eq_self ha, otherNbr_eq_self ha]

/-- The pair-map is injective (hence a permutation of the finite type). -/
private lemma stepPair_injective
    (hdeg : ∀ v, (univ.filter (fun j => adj v j = 1)).card = 2) :
    Function.Injective (fun p : Fin n × Fin n => (p.2, otherNbr adj p.2 p.1)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hb, ho⟩ := h
  subst hb
  have haa : a = a' := by
    have := congrArg (otherNbr adj b) ho
    rwa [otherNbr_involutive hdeg, otherNbr_involutive hdeg] at this
  simp [haa]

/-- **(g), cyclic case.** A connected `2`-regular simply-laced graph on `Fin n`
(`n ≥ 3`) is graph-isomorphic to the `n`-cycle `Ãₙ`. -/
lemma two_regular_connected_iso_Atilde {n : ℕ} (hn : 3 ≤ n)
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (hdeg : ∀ v, vertexDegree adj v = 2) :
    ∃ σ : Fin (AffineType.Atilde n hn).rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = (AffineType.Atilde n hn).adj i j := by
  classical
  -- Degree hypothesis in `Finset`-card form, and `adj` symmetry as a plain equation.
  have hdeg' : ∀ v, (univ.filter (fun j => adj v j = 1)).card = 2 := hdeg
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a
    rw [Matrix.transpose_apply] at h; exact h
  -- Base vertex `0` and a chosen neighbour `start1`.
  have h0lt : 0 < n := by omega
  set v0 : Fin n := ⟨0, h0lt⟩ with hv0def
  have hv0 : (univ.filter (fun j => adj v0 j = 1)).Nonempty := by
    rw [← Finset.card_pos, hdeg' v0]; omega
  set start1 : Fin n := hv0.choose with hstart1def
  have hstart1 : adj v0 start1 = 1 := by
    have := hv0.choose_spec; simpa using (Finset.mem_filter.mp this).2
  -- The pair-step map and the walk `f k = (Tᵏ e0).1`.
  set T : Fin n × Fin n → Fin n × Fin n := fun p => (p.2, otherNbr adj p.2 p.1) with hT
  set e0 : Fin n × Fin n := (v0, start1) with he0
  set f : ℕ → Fin n := fun k => (T^[k] e0).1 with hf
  -- The second coordinate is the next vertex.
  have hf2 : ∀ k, (T^[k] e0).2 = f (k + 1) := by
    intro k
    have hrw : f (k + 1) = (T (T^[k] e0)).1 := by
      simp only [hf, Function.iterate_succ_apply']
    rw [hrw]; simp only [hT]
  -- The three-term recurrence.
  have hstep : ∀ t, f (t + 2) = otherNbr adj (f (t + 1)) (f t) := by
    intro t
    have hA : f (t + 2) = (T (T (T^[t] e0))).1 := by
      simp only [hf, Function.iterate_succ_apply']
    rw [hA]; simp only [hT, hf2, hf]
  -- Consecutive vertices are adjacent.
  have hadj : ∀ k, adj (f k) (f (k + 1)) = 1 := by
    intro k
    induction k with
    | zero => simpa [hf, he0] using hstart1
    | succ t ih =>
        rw [hstep t]
        have hft : adj (f (t + 1)) (f t) = 1 := by rw [hsymm']; exact ih
        exact otherNbr_adj (hdeg' _) hft
  -- No immediate backtrack.
  have hback : ∀ k, f (k + 2) ≠ f k := by
    intro k
    rw [hstep k]
    have hft : adj (f (k + 1)) (f k) = 1 := by rw [hsymm']; exact hadj k
    exact otherNbr_ne (hdeg' _) hft
  -- The two neighbours of `f (k+1)` are exactly `f k` and `f (k+2)`.
  have hnbr_iff : ∀ k w, adj (f (k + 1)) w = 1 ↔ (w = f k ∨ w = f (k + 2)) := by
    intro k w
    sorry
  -- `T` is a permutation, so `e0` is a periodic point.
  have hTinj : Function.Injective T := by
    rw [hT]; exact stepPair_injective hdeg'
  have hper_pt : e0 ∈ Function.periodicPts T := hTinj.mem_periodicPts e0
  set p : ℕ := Function.minimalPeriod T e0 with hpdef
  have hp_pos : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts hper_pt
  have hTp : T^[p] e0 = e0 := Function.iterate_minimalPeriod
  -- Wrap-around.
  have hwrap0 : f p = f 0 := by simp only [hf, hTp, Function.iterate_zero_apply]
  have hwrap1 : f (p + 1) = f 1 := by
    simp only [hf, Function.iterate_succ_apply', hTp]
  -- Full periodicity.
  have hper : ∀ k, f (k + p) = f k := by
    intro k
    simp only [hf, Function.iterate_add_apply, hTp]
  -- Injectivity of the pair-walk on `[0, p)`.
  have hpairinj : ∀ a b, a < p → b < p → f a = f b → f (a + 1) = f (b + 1) → a = b := by
    intro a b ha hb hfab hfab1
    have hpair : T^[a] e0 = T^[b] e0 := by
      apply Prod.ext
      · exact hfab
      · rw [hf2 a, hf2 b]; exact hfab1
    exact Function.iterate_injOn_Iio_minimalPeriod (Set.mem_Iio.mpr ha)
      (Set.mem_Iio.mpr hb) hpair
  -- Surjectivity: every vertex is visited.
  have hsurj : ∀ v : Fin n, ∃ k, k < p ∧ f k = v := by
    sorry
  -- Injectivity of `f` on `[0, p)` (minimal-gap induction).
  have hfinj : ∀ i j, i < p → j < p → f i = f j → i = j := by
    sorry
  -- Hence `p = n`.
  have hpn : p = n := by
    sorry
  -- Assemble the equivalence.
  sorry

/-- **(g)** **Classification of affine Dynkin diagrams.** A connected simply-laced
graph on `n ≥ 1` vertices is an affine Dynkin diagram iff it is
(graph-isomorphic to) one of `Ãₙ, D̃ₙ, Ẽ₆, Ẽ₇, Ẽ₈` — exactly the "forbidden"
extended diagrams of parts (c)–(e). -/
theorem affine_dynkin_classification (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n) :
    IsAffineDynkinDiagram n adj ↔
    ∃ t : AffineType, ∃ σ : Fin t.rank ≃ Fin n, ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  constructor
  · -- (⟹) The classification proper: a positive-semidefinite-but-degenerate
    -- connected simply-laced graph is graph-isomorphic to one of the five
    -- extended types. This is the deep content (see the sub-issue).
    sorry
  · -- (⟸) Each extended type is an affine Dynkin diagram (`isAffineDynkinDiagram_of_type`),
    -- transported along the graph isomorphism `σ`.
    rintro ⟨t, σ, hσ⟩
    exact isAffineDynkinDiagram_of_graph_iso σ hσ (isAffineDynkinDiagram_of_type t)

end Etingof.Problem6_1_3_tildeE
