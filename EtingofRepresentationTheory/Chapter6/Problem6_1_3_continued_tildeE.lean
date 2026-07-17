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
  have hf2 : ∀ k, (T^[k] e0).2 = f (k + 1) := fun k => by
    simp only [hf, Function.iterate_succ_apply', hT]
  -- The three-term recurrence.
  have hstep : ∀ t, f (t + 2) = otherNbr adj (f (t + 1)) (f t) := fun t => by
    rw [← hf2 (t + 1)]
    simp only [hf, Function.iterate_succ_apply', hT]
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
    have hk_nbr : adj (f (k + 1)) (f k) = 1 := by rw [hsymm']; exact hadj k
    have hk2_nbr : adj (f (k + 1)) (f (k + 2)) = 1 := hadj (k + 1)
    have hne : f k ≠ f (k + 2) := fun h => hback k h.symm
    have hsub : ({f k, f (k + 2)} : Finset (Fin n)) ⊆
        univ.filter (fun j => adj (f (k + 1)) j = 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h <;> subst h <;> simp [hk_nbr, hk2_nbr]
    have hcard2 : ({f k, f (k + 2)} : Finset (Fin n)).card = 2 := Finset.card_pair hne
    have heq : univ.filter (fun j => adj (f (k + 1)) j = 1) = {f k, f (k + 2)} :=
      (Finset.eq_of_subset_of_card_le hsub
        (le_of_eq (by rw [hdeg' (f (k + 1)), hcard2]))).symm
    constructor
    · intro hw
      have hmem : w ∈ univ.filter (fun j => adj (f (k + 1)) j = 1) := by simp [hw]
      rw [heq] at hmem
      simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
    · intro hw
      have hmem : w ∈ univ.filter (fun j => adj (f (k + 1)) j = 1) := by
        rw [heq]; simpa [Finset.mem_insert, Finset.mem_singleton] using hw
      simpa using (Finset.mem_filter.mp hmem).2
  -- `T` is a permutation, so `e0` is a periodic point.
  have hTinj : Function.Injective T := by
    rw [hT]; exact stepPair_injective hdeg'
  have hper_pt : e0 ∈ Function.periodicPts T := hTinj.mem_periodicPts e0
  set p : ℕ := Function.minimalPeriod T e0 with hpdef
  have hp_pos : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts hper_pt
  have hTp : T^[p] e0 = e0 := Function.iterate_minimalPeriod
  -- Wrap-around.
  have hwrap0 : f p = f 0 := by
    have h1 : f p = (T^[p] e0).1 := by simp only [hf]
    have h2 : f 0 = e0.1 := by simp only [hf]; rfl
    rw [h1, h2, hTp]
  have hwrap1 : f (p + 1) = f 1 := by
    have h1 : f (p + 1) = (T (T^[p] e0)).1 := by
      simp only [hf, Function.iterate_succ_apply']
    have h2 : f 1 = (T e0).1 := by simp only [hf]; rfl
    rw [h1, h2, hTp]
  -- Full periodicity.
  have hper : ∀ k, f (k + p) = f k := by
    intro k
    simp only [hf, Function.iterate_add_apply, hTp]
  have hpp : ∀ t k, f (k + p * t) = f k := by
    intro t
    induction t with
    | zero => intro k; simp
    | succ s ih =>
        intro k
        have hrw : k + p * (s + 1) = (k + p * s) + p := by ring
        rw [hrw, hper, ih]
  have hmod : ∀ m, f m = f (m % p) := by
    intro m
    conv_lhs => rw [← Nat.mod_add_div m p]
    rw [hpp]
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
    -- Closure of the visited set under adjacency.
    have hclosure : ∀ m w, adj (f m) w = 1 → ∃ j, f j = w := by
      intro m w hw
      have hmp : f m = f (m + p) := (hper m).symm
      have h1 : (m + p - 1) + 1 = m + p := by omega
      have hadjw : adj (f ((m + p - 1) + 1)) w = 1 := by rw [h1, ← hmp]; exact hw
      rcases (hnbr_iff (m + p - 1) w).mp hadjw with h | h
      · exact ⟨m + p - 1, h.symm⟩
      · exact ⟨m + p - 1 + 2, h.symm⟩
    have hclosed : ∀ a b, (∃ m, f m = a) → adj a b = 1 → ∃ j, f j = b := by
      rintro a b ⟨m, rfl⟩ hab; exact hclosure m b hab
    intro v
    -- Reachability from the base vertex, in `ReflTransGen` form.
    have hreach : Relation.ReflTransGen (AdjEdge adj) v0 v := by
      obtain ⟨path, hhead, hlast, hpath⟩ := hconn v0 v
      have hne : path ≠ [] := by rintro rfl; simp at hhead
      have hchain : List.IsChain (fun a b => adj a b = 1) path := by
        rw [List.isChain_iff_getElem]; intro k hk; exact hpath k hk
      have hi : path.head hne = v0 :=
        Option.some_inj.mp ((List.head?_eq_some_head hne).symm.trans hhead)
      have hj : path.getLast hne = v := by
        have := (List.getLast?_eq_getLast_of_ne_nil hne).symm.trans hlast
        exact Option.some_inj.mp this
      have hrtg := List.relationReflTransGen_of_exists_isChain path hchain hne
      rw [hi, hj] at hrtg
      exact hrtg
    have hex : ∃ m, f m = v := by
      induction hreach with
      | refl => exact ⟨0, by simp [hf, he0]⟩
      | tail _ hbc ih => exact hclosed _ _ ih hbc
    obtain ⟨m, hm⟩ := hex
    exact ⟨m % p, Nat.mod_lt _ hp_pos, by rw [← hmod m]; exact hm⟩
  -- Injectivity of `f` on `[0, p)` (minimal-gap induction: a coincidence at gap
  -- `d ≥ 3` produces one at gap `d - 2`, while gaps `1, 2` are ruled out directly).
  have hgap : ∀ d i j, j = i + d → i < p → j < p → f i = f j → d = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i j hj hi hjp hfij
      rcases Nat.lt_or_ge d 3 with hd3 | hd3
      · interval_cases d
        · rfl
        · -- gap 1: adjacency plus `f i = f (i+1)` forces a self-loop.
          exfalso; subst hj
          have h1 := hadj i
          rw [← hfij, hdiag (f i)] at h1
          norm_num at h1
        · -- gap 2: contradicts the no-backtrack lemma.
          exfalso; subst hj
          exact hback i hfij.symm
      · -- gap `d ≥ 3`: swap to the gap-`(d-2)` coincidence `f (i+1) = f (j-1)`.
        exfalso
        have hj1 : (j - 1) + 1 = j := by omega
        have hj2 : (j - 1) + 2 = j + 1 := by omega
        have hneigh : adj (f ((j - 1) + 1)) (f (i + 1)) = 1 := by
          rw [hj1, ← hfij]; exact hadj i
        have hor := (hnbr_iff (j - 1) (f (i + 1))).mp hneigh
        rw [hj2] at hor
        have hne_succ : f (i + 1) ≠ f (j + 1) := by
          intro hcon
          have : i = j := hpairinj i j hi hjp hfij hcon
          omega
        have hswap : f (i + 1) = f (j - 1) := by
          rcases hor with h | h
          · exact h
          · exact absurd h hne_succ
        have hz : d - 2 = 0 :=
          ih (d - 2) (by omega) (i + 1) (j - 1) (by omega) (by omega) (by omega) hswap
        omega
  have hfinj : ∀ i j, i < p → j < p → f i = f j → i = j := by
    intro i j hi hj hfij
    rcases le_total i j with hle | hle
    · have hd := hgap (j - i) i j (by omega) hi hj hfij
      omega
    · have hd := hgap (i - j) j i (by omega) hj hi hfij.symm
      omega
  -- Hence `p = n`.
  have hφinj : Function.Injective (fun i : Fin p => f i.val) := fun a b hab =>
    Fin.ext (hfinj a.val b.val a.isLt b.isLt hab)
  have hφsurj : Function.Surjective (fun i : Fin p => f i.val) := by
    intro v; obtain ⟨k, hk, hkv⟩ := hsurj v; exact ⟨⟨k, hk⟩, hkv⟩
  have hpn : p = n := by
    have h1 : p ≤ n := by simpa using Fintype.card_le_of_injective _ hφinj
    have h2 : n ≤ p := by simpa using Fintype.card_le_of_surjective _ hφsurj
    omega
  -- Adjacency in terms of the cyclic successor/predecessor.
  have hcorr : ∀ a b, a < p → b < p →
      (adj (f a) (f b) = 1 ↔ (b = (a + p - 1) % p ∨ b = (a + 1) % p)) := by
    intro a b ha hb
    have hap : (a + p - 1) + 1 = a + p := by omega
    have hfa : f ((a + p - 1) + 1) = f a := by rw [hap]; exact hper a
    have hidx : (a + p - 1) + 2 = (a + 1) + p := by omega
    constructor
    · intro hw
      have hadjw : adj (f ((a + p - 1) + 1)) (f b) = 1 := by rw [hfa]; exact hw
      rcases (hnbr_iff (a + p - 1) (f b)).mp hadjw with h | h
      · exact Or.inl (hfinj b _ hb (Nat.mod_lt _ hp_pos) (h.trans (hmod (a + p - 1))))
      · refine Or.inr (hfinj b _ hb (Nat.mod_lt _ hp_pos) ?_)
        rw [h, hidx, hper (a + 1)]; exact hmod (a + 1)
    · intro hb'
      rcases hb' with h | h
      · have hfb : f b = f (a + p - 1) := by rw [h]; exact (hmod (a + p - 1)).symm
        have hn := (hnbr_iff (a + p - 1) (f (a + p - 1))).mpr (Or.inl rfl)
        rw [hfa] at hn; rw [hfb]; exact hn
      · have hfb : f b = f ((a + p - 1) + 2) := by
          rw [h, hidx, hper (a + 1)]; exact (hmod (a + 1)).symm
        have hn := (hnbr_iff (a + p - 1) (f ((a + p - 1) + 2))).mpr (Or.inr rfl)
        rw [hfa] at hn; rw [hfb]; exact hn
  -- The predecessor index, rewritten as a `+1` modular condition.
  have hpred : ∀ a b, a < p → b < p → (b = (a + p - 1) % p ↔ (b + 1) % p = a) := by
    intro a b ha hb
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0
      rw [show (0 + p - 1) = p - 1 by omega, Nat.mod_eq_of_lt (by omega : p - 1 < p)]
      constructor
      · intro h; subst h; rw [show (p - 1) + 1 = p by omega, Nat.mod_self]
      · intro h
        by_contra hne
        rw [Nat.mod_eq_of_lt (by omega : b + 1 < p)] at h; omega
    · have hmod1 : (a + p - 1) % p = a - 1 := by
        rw [show a + p - 1 = (a - 1) + p by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [hmod1]
      constructor
      · intro h; subst h; rw [show (a - 1) + 1 = a by omega, Nat.mod_eq_of_lt ha]
      · intro h
        rcases (by omega : b + 1 < p ∨ b + 1 = p) with hlt | heq
        · rw [Nat.mod_eq_of_lt hlt] at h; omega
        · rw [heq, Nat.mod_self] at h; omega
  have hstep_adj : ∀ a b, a < p → b < p →
      (adj (f a) (f b) = 1 ↔ ((a + 1) % p = b ∨ (b + 1) % p = a)) := by
    intro a b ha hb
    rw [hcorr a b ha hb, hpred a b ha hb]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h
  -- Assemble the equivalence.
  have hφ'bij : Function.Bijective (fun i : Fin n => f i.val) := by
    apply Finite.injective_iff_bijective.mp
    intro a b hab
    exact Fin.ext (hfinj a.val b.val (by rw [hpn]; exact a.isLt)
      (by rw [hpn]; exact b.isLt) hab)
  refine ⟨Equiv.ofBijective (fun i : Fin n => f i.val) hφ'bij, ?_⟩
  intro i j
  simp only [Equiv.ofBijective_apply]
  have hi : (i.val : ℕ) < p := by rw [hpn]; exact i.isLt
  have hj : (j.val : ℕ) < p := by rw [hpn]; exact j.isLt
  have hiff := hstep_adj i.val j.val hi hj
  rw [hpn] at hiff
  have hRHS : (AffineType.Atilde n hn).adj i j
      = if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then (1 : ℤ) else 0 := by
    simp only [AffineType.adj]
  rw [hRHS]
  by_cases hcond : (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val
  · rw [if_pos hcond]; exact hiff.mpr hcond
  · rw [if_neg hcond]
    rcases h01 (f i.val) (f j.val) with h | h
    · exact h
    · exact absurd (hiff.mp h) hcond

/-- **Affine degree bound.** In an affine Dynkin diagram every vertex has degree
at most `4`. This mirrors the finite `dynkin_degree_le_three`, but uses the
*semidefinite* (rather than definite) form: the test vector `x = 2·eᵢ + Σ_{j∼i} eⱼ`
gives `B(x, x) = 2·(4 − deg i)`, which must be `≥ 0`, so `deg i ≤ 4`. The extremal
value `deg = 4` is realised only by the `D̃₄` star. -/
lemma affine_vertexDegree_le_four {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hD : IsAffineDynkinDiagram n adj) (i : Fin n) :
    Etingof.Problem6_1_3_E7E8.vertexDegree adj i ≤ 4 := by
  by_contra hge; rw [not_le] at hge
  obtain ⟨hsymm, hdiag, h01, _, hpos, _⟩ := hD
  -- Extract 5 neighbours of `i`.
  set N := Finset.univ.filter (fun j => adj i j = 1) with hN_def
  have hcard : 5 ≤ N.card := hge
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
  have hi_not_S : i ∉ S := by
    intro hi; have := (Finset.mem_filter.mp (hSsub hi)).2; linarith [hdiag i]
  -- Test vector: `2` at `i`, `1` at the five neighbours, `0` elsewhere.
  set x : Fin n → ℤ := fun j => if j = i then 2 else if j ∈ S then 1 else 0
  have hx_val_i : x i = 2 := by simp [x]
  have adj_x_nonneg : ∀ a b, 0 ≤ adj a b * x b := fun a b =>
    mul_nonneg (by rcases h01 a b with h | h <;> omega)
      (by simp only [x]; split_ifs <;> omega)
  have adj_x_S : ∀ b, b ∈ S → adj i b * x b = 1 := by
    intro b hb
    have h1 : adj i b = 1 := (Finset.mem_filter.mp (hSsub hb)).2
    have h2 : x b = 1 := by
      have : b ≠ i := fun h => hi_not_S (h ▸ hb)
      simp [x, this, hb]
    rw [h1, h2, mul_one]
  -- `Σ_b adj(i,b)·x(b) ≥ 5` (each of the five neighbours contributes `1`).
  have sum_i_ge : (5 : ℤ) ≤ ∑ b, adj i b * x b := by
    have hS_sum : ∑ b ∈ S, adj i b * x b = 5 := by
      rw [show (5 : ℤ) = ∑ _b ∈ S, (1 : ℤ) from by simp [hScard]]
      exact Finset.sum_congr rfl (fun b hb => adj_x_S b hb)
    calc (5 : ℤ) = ∑ b ∈ S, adj i b * x b := hS_sum.symm
      _ ≤ ∑ b, adj i b * x b :=
          Finset.sum_le_univ_sum_of_nonneg (fun b => adj_x_nonneg i b)
  -- For each neighbour `a ∈ S`, `Σ_b adj(a,b)·x(b) ≥ 2` (from `adj(a,i)·x(i) = 1·2`).
  have sum_a_ge : ∀ a, a ∈ S → (2 : ℤ) ≤ ∑ b, adj a b * x b := by
    intro a ha
    have ha_adj_i : adj a i = 1 := by
      have := (Finset.mem_filter.mp (hSsub ha)).2; exact hsymm.apply i a ▸ this
    have hxi : x i = 2 := by simp [x]
    have : adj a i * x i = 2 := by rw [ha_adj_i, hxi]; ring
    calc (2 : ℤ) = adj a i * x i := this.symm
      _ = ∑ b ∈ ({i} : Finset (Fin n)), adj a b * x b := by simp
      _ ≤ ∑ b, adj a b * x b :=
          Finset.sum_le_univ_sum_of_nonneg (fun b => adj_x_nonneg a b)
  have mulVec_eq : ∀ a, ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) a =
      2 * x a - ∑ b, adj a b * x b := by
    intro a; simp only [mulVec, dotProduct]
    rw [show ∑ b, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) a b * x b =
        ∑ b, (2 * (1 : Matrix _ _ ℤ) a b * x b - adj a b * x b) from
      Finset.sum_congr rfl (fun b _ => by
        simp only [Matrix.sub_apply, Matrix.smul_apply]; ring)]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [show ∑ b, 2 * (1 : Matrix (Fin n) (Fin n) ℤ) a b * x b =
        ∑ b, if a = b then 2 * x b else 0 from
      Finset.sum_congr rfl (fun b _ => by
        simp only [Matrix.one_apply]; split_ifs <;> simp)]
    simp
  -- `B(x,x) = Σ_a x(a)·(2·x(a) − Σ_b adj(a,b)·x(b))`.
  have hBxx : dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x)
      = ∑ a, x a * (2 * x a - ∑ b, adj a b * x b) := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl (fun a _ => by rw [mulVec_eq])
  -- Split off the centre term `a = i`.
  have hsplit : (∑ a, x a * (2 * x a - ∑ b, adj a b * x b))
      = x i * (2 * x i - ∑ b, adj i b * x b)
        + ∑ a ∈ univ.erase i, x a * (2 * x a - ∑ b, adj a b * x b) :=
    (Finset.add_sum_erase univ _ (Finset.mem_univ i)).symm
  -- Centre term `≤ -2`; every other term `≤ 0`.
  have hi_term : x i * (2 * x i - ∑ b, adj i b * x b) ≤ -2 := by
    rw [hx_val_i]; nlinarith [sum_i_ge]
  have hrest : ∑ a ∈ univ.erase i, x a * (2 * x a - ∑ b, adj a b * x b) ≤ 0 := by
    apply Finset.sum_nonpos; intro a ha
    rw [Finset.mem_erase] at ha
    by_cases haS : a ∈ S
    · have hxa : x a = 1 := by simp only [x]; rw [if_neg ha.1, if_pos haS]
      rw [hxa]; nlinarith [sum_a_ge a haS]
    · have hxa : x a = 0 := by simp [x, ha.1, haS]
      rw [hxa]; simp
  have hneg : dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) ≤ -2 := by
    rw [hBxx, hsplit]; linarith [hi_term, hrest]
  linarith [hpos x, hneg]

/-- **Hub connectivity.** If every vertex is either `c` or `sub`-adjacent to the
hub `c` (both directions), then the `List`-path connectivity clause required by
`affine_properInduced_isDynkin` holds: route every pair through `c`. -/
private lemma star_hconn {m : ℕ} (sub : Matrix (Fin m) (Fin m) ℤ) (c : Fin m)
    (hc : ∀ a, a ≠ c → sub c a = 1) (hc' : ∀ a, a ≠ c → sub a c = 1) :
    ∀ i j : Fin m, ∃ path : List (Fin m),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        sub (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1 := by
  intro i j
  by_cases hij : i = j
  · exact ⟨[i], by simp, by simp [hij], by intro k h; simp at h⟩
  by_cases hic : i = c
  · refine ⟨[i, j], by simp, by simp, ?_⟩
    intro k h
    simp only [List.length_cons, List.length_nil] at h
    obtain rfl : k = 0 := by omega
    simp only [List.get_cons_succ]
    rw [hic]; exact hc j (fun hh => hij (hic.trans hh.symm))
  by_cases hjc : j = c
  · refine ⟨[i, c], by simp, by simp [hjc], ?_⟩
    intro k h
    simp only [List.length_cons, List.length_nil] at h
    obtain rfl : k = 0 := by omega
    simp only [List.get_cons_succ]
    exact hc' i hic
  · refine ⟨[i, c, j], by simp, by simp, ?_⟩
    intro k h
    simp only [List.length_cons, List.length_nil] at h
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simp only [List.get_cons_succ]
      exact hc' i hic
    · simp only [List.get_cons_succ]
      exact hc j hjc

/-- **Degree-4 dichotomy (tree case, step of `affine_dynkin_classification`).**
For a connected affine Dynkin diagram `adj` on `Fin n`, **either** it is
graph-isomorphic to the affine star `D̃₄` (`K_{1,4}`), **or** every vertex has
degree `≤ 3`.

The argument uses only the affine minimality lemma
(`affine_properInduced_finiteDynkin`), so no separate acyclicity hypothesis is
needed: if some vertex `v` has degree `4` (the maximum, by
`affine_vertexDegree_le_four`), the star `{v} ∪ N(v)` on `5` vertices would be a
*proper* connected induced subgraph whenever `n > 5`, hence a finite Dynkin
diagram — impossible, since it has a degree-`4` vertex while every finite Dynkin
diagram has all degrees `≤ 3` (`dynkin_degree_le_three`). So `n = 5`, and any
edge between two neighbours of `v` would give a triangle (a proper connected
induced subgraph that is not a tree, contradicting minimality via
`isDynkinDiagram_isTree`); thus `adj` is exactly the `D̃₄` star. -/
lemma affine_degree_four_dichotomy {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj) :
    (∃ σ : Fin (AffineType.Dtilde 4 (by norm_num)).rank ≃ Fin n,
        ∀ i j, adj (σ i) (σ j) = (AffineType.Dtilde 4 (by norm_num)).adj i j)
    ∨ (∀ v, Etingof.Problem6_1_3_E7E8.vertexDegree adj v ≤ 3) := by
  by_cases hex : ∃ v, Etingof.Problem6_1_3_E7E8.vertexDegree adj v = 4
  · left
    obtain ⟨v, hv4⟩ := hex
    have hdiag : ∀ i, adj i i = 0 := hD.2.1
    have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
      have h := congrFun (congrFun hD.1 b) a
      rwa [Matrix.transpose_apply] at h
    -- The 4 neighbours of `v`, enumerated by `g : Fin 4 → Fin n`.
    set N := univ.filter (fun j => adj v j = 1) with hN
    have hNcard : N.card = 4 := hv4
    set eN := N.equivFinOfCardEq hNcard with heN
    set g : Fin 4 → Fin n := fun i => (eN.symm i : Fin n) with hg
    have hg_mem : ∀ i, g i ∈ N := fun i => (eN.symm i).2
    have hg_adj : ∀ i, adj v (g i) = 1 := fun i => (Finset.mem_filter.mp (hg_mem i)).2
    have hg_inj : Function.Injective g := fun a b hab =>
      eN.symm.injective (Subtype.ext hab)
    have hv_notin_N : v ∉ N := fun h => by
      have := (Finset.mem_filter.mp h).2; rw [hdiag v] at this; exact absurd this (by norm_num)
    -- The star `e : Fin 5 → Fin n` with hub `e 0 = v`, leaves `e (i.succ) = g i`.
    set e : Fin 5 → Fin n := Fin.cons v g with he_def
    have he0 : e 0 = v := Fin.cons_zero _ _
    have hesucc : ∀ i, e i.succ = g i := fun i => Fin.cons_succ _ _ _
    have he : Function.Injective e := by
      rw [he_def, Fin.cons_injective_iff]
      exact ⟨fun ⟨i, hi⟩ => hv_notin_N (hi ▸ hg_mem i), hg_inj⟩
    -- The submatrix (induced subgraph on the star) and its hub connectivity.
    set sub := adj.submatrix e e with hsub
    have hhub0 : ∀ a : Fin 5, a ≠ 0 → adj v (e a) = 1 := by
      intro a ha
      induction a using Fin.cases with
      | zero => exact absurd rfl ha
      | succ i => rw [hesucc]; exact hg_adj i
    have hc : ∀ a : Fin 5, a ≠ 0 → sub 0 a = 1 := by
      intro a ha; rw [hsub, Matrix.submatrix_apply, he0]; exact hhub0 a ha
    have hc' : ∀ a : Fin 5, a ≠ 0 → sub a 0 = 1 := by
      intro a ha; rw [hsub, Matrix.submatrix_apply, he0, hsymm' (e a) v]; exact hhub0 a ha
    have hconn := star_hconn sub 0 hc hc'
    -- Degree of the hub `0` in the star submatrix is `4`.
    have hdeg4 : Etingof.vertexDegree sub 0 = 4 := by
      unfold Etingof.vertexDegree
      have hset : (univ.filter (fun j : Fin 5 => sub 0 j = 1)) = univ.erase 0 := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
        rw [hsub, Matrix.submatrix_apply, he0]
        induction j using Fin.cases with
        | zero => simp [he0, hdiag]
        | succ i => simp [hesucc, hg_adj i, Fin.succ_ne_zero]
      rw [hset, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
        Fintype.card_fin]
    -- `5 ≤ n` from the injective star, `n ≤ 5` from affine minimality.
    have h5le : 5 ≤ n := by
      have := Fintype.card_le_of_injective e he; simpa using this
    have hnle : n ≤ 5 := by
      by_contra hgt
      have hgt' : 5 < n := not_le.mp hgt
      obtain ⟨w, hw⟩ : ∃ w, w ∉ Finset.univ.image e := by
        have hcard : (Finset.univ.image e).card = 5 := by
          rw [Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fin]
        by_contra hcon
        have himg : Finset.univ.image e = Finset.univ := by
          rw [Finset.eq_univ_iff_forall]; intro x; by_contra hx; exact hcon ⟨x, hx⟩
        rw [himg, Finset.card_univ, Fintype.card_fin] at hcard; omega
      have hv_w : ∀ i, e i ≠ w := fun i hi =>
        hw (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
      have hDsub : Etingof.IsDynkinDiagram 5 sub :=
        affine_properInduced_isDynkin adj hn hD e he hv_w hconn
      have hdeg3 := Etingof.dynkin_degree_le_three hDsub 0
      omega
    have hn5 : n = 5 := le_antisymm hnle h5le
    subst hn5
    -- `e` is now a self-map of `Fin 5`, hence a bijection.
    have hebij : Function.Bijective e := (Finite.injective_iff_bijective).mp he
    set eEquiv := Equiv.ofBijective e hebij with heE
    -- No edges between two distinct neighbours: a triangle `{v, eₐ, e_b}` would be a
    -- proper connected induced subgraph, hence a finite Dynkin diagram, yet it has
    -- `6` half-edges while a tree on `3` vertices has `2·(3−1) = 4`.
    have he_mem : ∀ a : Fin 5, a ≠ 0 → e a ∈ N := by
      intro a ha
      induction a using Fin.cases with
      | zero => exact absurd rfl ha
      | succ i => rw [hesucc]; exact hg_mem i
    have hnoedge : ∀ a b : Fin 5, a ≠ 0 → b ≠ 0 → a ≠ b → sub a b = 0 := by
      intro a b ha hb hab
      rcases hD.2.2.1 (e a) (e b) with h0 | h1
      · rw [hsub, Matrix.submatrix_apply]; exact h0
      · exfalso
        -- The triangle `{v, eₐ, e_b}`.
        set e3 : Fin 3 → Fin 5 := ![v, e a, e b] with he3
        have hva : v ≠ e a := fun h => hv_notin_N (h.symm ▸ he_mem a ha)
        have hvb : v ≠ e b := fun h => hv_notin_N (h.symm ▸ he_mem b hb)
        have heab : e a ≠ e b := fun h => hab (he h)
        have e30 : e3 0 = v := by simp [he3]
        have e31 : e3 1 = e a := by simp [he3]
        have e32 : e3 2 = e b := by simp [he3]
        have he3inj : Function.Injective e3 := by
          have h1inj : Function.Injective (![e a, e b] : Fin 2 → Fin 5) := by
            rw [show (![e a, e b] : Fin 2 → Fin 5) = Fin.cons (e a) ![e b] from rfl,
              Fin.cons_injective_iff]
            refine ⟨?_, ?_⟩
            · rintro ⟨i, hi⟩; fin_cases i; exact heab hi.symm
            · intro x y _; exact Subsingleton.elim x y
          rw [he3, show (![v, e a, e b] : Fin 3 → Fin 5) = Fin.cons v ![e a, e b] from rfl,
            Fin.cons_injective_iff]
          refine ⟨?_, h1inj⟩
          rintro ⟨i, hi⟩
          fin_cases i
          · exact hva hi.symm
          · exact hvb hi.symm
        obtain ⟨w3, hw3⟩ : ∃ w, w ∉ Finset.univ.image e3 := by
          have hc3 : (Finset.univ.image e3).card = 3 := by
            rw [Finset.card_image_of_injective _ he3inj, Finset.card_univ, Fintype.card_fin]
          by_contra hcon
          have himg : Finset.univ.image e3 = Finset.univ := by
            rw [Finset.eq_univ_iff_forall]; intro x; by_contra hx; exact hcon ⟨x, hx⟩
          rw [himg, Finset.card_univ, Fintype.card_fin] at hc3; omega
        have hv_w3 : ∀ i, e3 i ≠ w3 := fun i hi =>
          hw3 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
        have a1 : adj v (e a) = 1 := hhub0 a ha
        have a2 : adj v (e b) = 1 := hhub0 b hb
        have a3 : adj (e a) v = 1 := by rw [hsymm']; exact a1
        have a4 : adj (e b) v = 1 := by rw [hsymm']; exact a2
        have a6 : adj (e b) (e a) = 1 := by rw [hsymm']; exact h1
        have hc3 : ∀ x : Fin 3, x ≠ 0 → (adj.submatrix e3 e3) 0 x = 1 := by
          intro x hx
          fin_cases x
          · exact absurd rfl hx
          · simpa [Matrix.submatrix_apply, he3] using a1
          · simpa [Matrix.submatrix_apply, he3] using a2
        have hc3' : ∀ x : Fin 3, x ≠ 0 → (adj.submatrix e3 e3) x 0 = 1 := by
          intro x hx
          fin_cases x
          · exact absurd rfl hx
          · simpa [Matrix.submatrix_apply, he3] using a3
          · simpa [Matrix.submatrix_apply, he3] using a4
        have hconn3 := star_hconn (adj.submatrix e3 e3) 0 hc3 hc3'
        have hDsub3 : Etingof.IsDynkinDiagram 3 (adj.submatrix e3 e3) :=
          affine_properInduced_isDynkin adj hn hD e3 he3inj hv_w3 hconn3
        have htree := Etingof.Problem6_1_3_E7E8.isDynkinDiagram_isTree
          (by norm_num : (1 : ℕ) ≤ 3) hDsub3
        have hsum6 : (∑ i, ∑ j, (adj.submatrix e3 e3) i j) = 6 := by
          simp only [Fin.sum_univ_three, Matrix.submatrix_apply, e30, e31, e32, hdiag,
            a1, a2, a3, a4, h1, a6]
          norm_num
        rw [htree] at hsum6; norm_num at hsum6
    -- Full description of the star submatrix.
    have hsubval : ∀ a b : Fin 5,
        sub a b = if a = b then 0 else if a = 0 ∨ b = 0 then 1 else 0 := by
      intro a b
      by_cases hab : a = b
      · subst hab; rw [if_pos rfl, hsub, Matrix.submatrix_apply]; exact hdiag (e a)
      · rw [if_neg hab]
        by_cases ha0 : a = 0
        · subst ha0; rw [if_pos (Or.inl rfl)]; exact hc b (fun h => hab h.symm)
        · by_cases hb0 : b = 0
          · subst hb0; rw [if_pos (Or.inr rfl)]; exact hc' a ha0
          · rw [if_neg (by tauto)]; exact hnoedge a b ha0 hb0 hab
    -- Reindexing permutation: `D̃₄` center `2 ↦` hub `0`, leaves `{0,1,3,4} ↦ {1,2,3,4}`.
    let ρf : Fin 5 → Fin 5 := ![1, 2, 0, 3, 4]
    let ρg : Fin 5 → Fin 5 := ![2, 0, 1, 3, 4]
    let ρ : Fin 5 ≃ Fin 5 := ⟨ρf, ρg, by decide, by decide⟩
    refine ⟨ρ.trans eEquiv, ?_⟩
    intro i j
    change adj (e (ρf i)) (e (ρf j)) = (AffineType.Dtilde 4 (by norm_num)).adj i j
    rw [show adj (e (ρf i)) (e (ρf j)) = sub (ρf i) (ρf j) from by
        rw [hsub, Matrix.submatrix_apply], hsubval]
    fin_cases i <;> fin_cases j <;> decide
  · right
    intro v
    have hle := affine_vertexDegree_le_four adj hD v
    have hne : Etingof.Problem6_1_3_E7E8.vertexDegree adj v ≠ 4 := fun h => hex ⟨v, h⟩
    omega

/-- **(g), cyclic case.** An affine Dynkin diagram whose associated graph contains
a cycle — encoded as having at least `n` edges, `2·n ≤ ∑ᵢ∑ⱼ adjᵢⱼ` (a connected
graph is a tree, i.e. acyclic, exactly when it has `n − 1` edges; having `≥ n`
edges is the complementary "contains a cycle" condition) — is `2`-regular with
`n ≥ 3`, hence graph-isomorphic to the cycle `Ãₙ`.

Testing positive semidefiniteness against the all-ones vector gives
`0 ≤ 1ᵀ(2·Id − adj)1 = 2n − ∑ᵢ∑ⱼadjᵢⱼ`; combined with `hcyc` this forces the
affine form to vanish on `1`, so the radical-equals-kernel lemma
`affine_cartan_mulVec_eq_zero_of_form_zero` gives `(2·Id − adj)·ᵥ1 = 0`. Reading
off row `i`, `2 − ∑ⱼ adjᵢⱼ = 0`, i.e. every vertex has degree `2`. The
combinatorial core `two_regular_connected_iso_Atilde` (#6847) then produces the
graph isomorphism onto `Ãₙ`. This is the cyclic branch of the ⟹ direction of
`affine_dynkin_classification` (#6792); the tree case (#6793) handles the
complementary `∑ᵢ∑ⱼ adjᵢⱼ = 2(n − 1)`. -/
lemma affine_cyclic_case {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n)
    (hD : IsAffineDynkinDiagram n adj)
    (hcyc : 2 * (n : ℤ) ≤ ∑ i, ∑ j, adj i j) :
    ∃ (h3 : 3 ≤ n) (σ : Fin (AffineType.Atilde n h3).rank ≃ Fin n),
      ∀ i j, adj (σ i) (σ j) = (AffineType.Atilde n h3).adj i j := by
  classical
  have hsymm := hD.1
  have hdiag := hD.2.1
  have h01 := hD.2.2.1
  have hconn := hD.2.2.2.1
  have hpos := hD.2.2.2.2.1
  -- Row sums of `2·Id − adj` against the all-ones vector (as in `isDynkinDiagram_isTree`).
  have hone : ∀ i j : Fin n,
      (2 • (1 : Matrix (Fin n) (Fin n) ℤ)) i j = if i = j then 2 else 0 := by
    intro i j; simp only [Matrix.smul_apply, Matrix.one_apply, two_nsmul]
    split_ifs <;> norm_num
  have hrow : ∀ i : Fin n,
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun _ => 1)) i
        = 2 - ∑ j, adj i j := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, hone, mul_one,
      Finset.sum_sub_distrib]
    rw [Finset.sum_ite_eq univ i (fun _ => (2 : ℤ))]; simp
  -- Value of the affine form on the all-ones vector: `2n − ∑ᵢ∑ⱼ adjᵢⱼ`.
  have hval : dotProduct (fun _ : Fin n => (1 : ℤ))
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun _ => 1))
      = 2 * (n : ℤ) - ∑ i, ∑ j, adj i j := by
    simp only [dotProduct, hrow, one_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- Semidefiniteness bounds the form below by `0`, `hcyc` bounds it above by `0`:
  -- the form vanishes on the all-ones vector.
  have hform0 : dotProduct (fun _ : Fin n => (1 : ℤ))
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun _ => 1)) = 0 := by
    have hge := hpos (fun _ => 1)
    rw [hval] at hge ⊢
    linarith
  -- Radical = kernel: the all-ones vector lies in the kernel of the Cartan matrix.
  have hker : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun _ => 1) = 0 :=
    affine_cartan_mulVec_eq_zero_of_form_zero adj hD hform0
  -- Hence every row sum of `adj` is `2`.
  have hrowsum : ∀ v : Fin n, (∑ j, adj v j) = 2 := by
    intro v
    have h := congrFun hker v
    rw [hrow v] at h
    have h0 : (2 : ℤ) - ∑ j, adj v j = 0 := h
    omega
  -- Translate the row sum into the `Finset`-card degree used by the combinatorial core.
  have hvd : ∀ v : Fin n, vertexDegree adj v = 2 := by
    intro v
    have hsum : (∑ j, adj v j)
        = ((univ.filter (fun j => adj v j = 1)).card : ℤ) := by
      rw [← Finset.sum_boole]
      exact Finset.sum_congr rfl (fun j _ => by rcases h01 v j with h | h <;> simp [h])
    have hz : ((vertexDegree adj v : ℤ)) = 2 := by
      simp only [vertexDegree]; rw [← hsum]; exact hrowsum v
    exact_mod_cast hz
  -- `n ≥ 3`: vertex `0` has two distinct neighbours, none equal to itself.
  have h3 : 3 ≤ n := by
    set v : Fin n := ⟨0, by omega⟩ with hv_def
    have hcard : (univ.filter (fun j => adj v j = 1)).card = 2 := hvd v
    have hvmem : v ∈ (univ : Finset (Fin n)) := Finset.mem_univ _
    have hsub : univ.filter (fun j => adj v j = 1) ⊆ univ.erase v := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      rw [hdiag v] at hj
      exact absurd hj.2 (by norm_num)
    have hle := Finset.card_le_card hsub
    rw [hcard, Finset.card_erase_of_mem hvmem, Finset.card_univ, Fintype.card_fin] at hle
    omega
  exact ⟨h3, two_regular_connected_iso_Atilde h3 adj hsymm hdiag h01 hconn hvd⟩

/-! ### Tree case: the degree-`≤ 3` core

The remaining branch of the ⟹ direction, after the cyclic case (`affine_cyclic_case`,
which covers `∑ᵢ∑ⱼ adjᵢⱼ ≥ 2n`, i.e. a graph with at least `n` edges — a cycle) and the
degree-`4` dichotomy (`affine_degree_four_dichotomy`, which peels off the degree-4 star `D̃₄`).

What is left is an **acyclic** (tree: `∑ᵢ∑ⱼ adjᵢⱼ < 2n`, i.e. `n - 1` edges) connected
affine Dynkin diagram in which every vertex has degree `≤ 3`. This is the degenerate-boundary
analogue of the finite branch analysis in `Chapter6/Theorem_Dynkin_classification.lean`
(`branch_classification`, `tree_branch_iso`, `arm_length_solutions`).

The analysis is organised exactly as in the finite case:

1. **Branch count** (`affine_tree_branch_count`): a connected acyclic affine diagram with all
   degrees `≤ 3` has **one or two** degree-3 (branch) vertices. Zero branch vertices ⟹ a path ⟹
   the finite type `Aₙ` (positive *definite*), contradicting degeneracy. Three or more ⟹ a proper
   induced subgraph that is not finite Dynkin, contradicting `affine_properInduced_finiteDynkin`.
2. **Two branch vertices ⟹ D̃ₙ** (`affine_tree_two_branch_iso`): a chain with a two-leaf fork at
   each end; reindex onto `AffineType.Dtilde`. Mirrors the finite `tree_branch_iso`.
3. **One branch vertex ⟹ Ẽ₆/Ẽ₇/Ẽ₈** (`affine_tree_one_branch_iso`): three arms of lengths
   `(p, q, r)` meet at the branch vertex; the degeneracy forces the affine Diophantine identity
   `1/(p+1) + 1/(q+1) + 1/(r+1) = 1`, whose only solutions are `(2,2,2) → Ẽ₆`, `(1,3,3) → Ẽ₇`,
   `(1,2,5) → Ẽ₈` (arm lengths; equivalently marks `(3,3,3)/(2,4,4)/(2,3,6)`). Reindex onto the
   corresponding `AffineType.E6tilde/E7tilde/E8tilde`. Mirrors the finite `branch_classification`
   together with a new *equality* analogue of `arm_length_solutions`.

The main lemma `affine_tree_degree_le_three_iso` dispatches on the branch count. The three pieces
below are each substantial (the finite `branch_classification` alone is ~700 lines) and are tracked
as separate sub-issues; their statements are fixed here so downstream work has stable interfaces. -/

/-- **Affine degree balance.** For an affine Dynkin diagram there is a strictly positive vector
`w` (the marks) with `∑ⱼ (deg j − 2)·wⱼ = 0`. Sum the null equation `(2·Id − adj)·ᵥw = 0` over all
rows and use `∑ₐ adjₐⱼ = deg j`. This is the affine analogue of the finite handshake identity and
is the source of both the "at least one branch" and "leaf exists" facts below. -/
lemma affine_degree_balance {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n)
    (hD : IsAffineDynkinDiagram n adj) :
    ∃ w : Fin n → ℤ, (∀ i, 0 < w i) ∧
      ∑ j, ((Etingof.vertexDegree adj j : ℤ) - 2) * w j = 0 := by
  classical
  have hsymm := hD.1
  have h01 := hD.2.2.1
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a
    rw [Matrix.transpose_apply] at h; exact h
  obtain ⟨w, hw_pos, hMw⟩ := affineNullVector_pos adj hn hD
  refine ⟨w, hw_pos, ?_⟩
  have mulVec_eq : ∀ a, ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec w) a =
      2 * w a - ∑ b, adj a b * w b := by
    intro a; simp only [mulVec, dotProduct]
    rw [show ∑ b, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) a b * w b =
        ∑ b, (2 * (1 : Matrix _ _ ℤ) a b * w b - adj a b * w b) from
      Finset.sum_congr rfl (fun b _ => by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring)]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [show ∑ b, 2 * (1 : Matrix (Fin n) (Fin n) ℤ) a b * w b =
        ∑ b, if a = b then 2 * w b else 0 from
      Finset.sum_congr rfl (fun b _ => by
        simp only [Matrix.one_apply]; split_ifs <;> simp <;> ring)]
    simp [Finset.sum_ite_eq']
  have hrow0 : ∀ a, 2 * w a - ∑ b, adj a b * w b = 0 := by
    intro a; rw [← mulVec_eq a]; simpa using congrFun hMw a
  have hsum : ∑ a, (2 * w a - ∑ b, adj a b * w b) = 0 :=
    Finset.sum_eq_zero (fun a _ => hrow0 a)
  have e1 : ∑ a, (2 * w a - ∑ b, adj a b * w b)
      = 2 * (∑ a, w a) - ∑ a, ∑ b, adj a b * w b := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have e2 : ∑ a, ∑ b, adj a b * w b = ∑ b, (Etingof.vertexDegree adj b : ℤ) * w b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.sum_mul]
    congr 1
    rw [show (∑ a, adj a b) = ∑ a, adj b a from Finset.sum_congr rfl (fun a _ => hsymm' a b)]
    exact adj_sum_eq_degree h01 b
  rw [e1, e2] at hsum
  rw [show (∑ j, ((Etingof.vertexDegree adj j : ℤ) - 2) * w j)
      = (∑ j, (Etingof.vertexDegree adj j : ℤ) * w j) - 2 * ∑ j, w j from by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)]
  linarith

/-- **Deleting a leaf leaves a finite Dynkin diagram.** Removing a degree-1 vertex `u` (indexing
the survivors by `u.succAbove`) from an affine Dynkin diagram gives a proper connected induced
subgraph, which is finite Dynkin by `affine_properInduced_isDynkin`. Connectivity is preserved
because `u` is a leaf (`SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one`). -/
lemma affine_delete_leaf_isDynkin {k : ℕ} (adj : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hD : IsAffineDynkinDiagram (k + 1) adj) (u : Fin (k + 1))
    (hu_deg : Etingof.vertexDegree adj u = 1) :
    IsDynkinDiagram k (adj.submatrix u.succAbove u.succAbove) := by
  classical
  have hsymm := hD.1
  have hdiag := hD.2.1
  have h01 := hD.2.2.1
  have hconn := hD.2.2.2.1
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a
    rw [Matrix.transpose_apply] at h; exact h
  let G : SimpleGraph (Fin (k + 1)) :=
    { Adj := fun i j => adj i j = 1
      symm := ⟨fun i j (h : adj i j = 1) => by change adj j i = 1; rw [hsymm' j i]; exact h⟩
      loopless := ⟨fun i (h : adj i i = 1) => by rw [hdiag i] at h; exact absurd h (by norm_num)⟩ }
  haveI : DecidableRel G.Adj := fun i j => decEq (adj i j) 1
  haveI : Nonempty (Fin (k + 1)) := ⟨u⟩
  have hG_conn : G.Connected := ⟨fun a b => by
    obtain ⟨path, hhead, hlast, hedges⟩ := hconn a b
    exact list_path_reachable G path a b hhead hlast (fun m hm => hedges m hm)⟩
  have hG_deg : G.degree u = 1 := by
    have hdegeq : G.degree u = Etingof.vertexDegree adj u := by
      rw [SimpleGraph.degree]
      unfold Etingof.vertexDegree
      congr 1
      ext j
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl
    rw [hdegeq]; exact hu_deg
  have hG' := hG_conn.induce_compl_singleton_of_degree_eq_one hG_deg
  refine affine_properInduced_isDynkin adj (by omega) hD u.succAbove
    Fin.succAbove_right_injective (fun i => Fin.succAbove_ne u i) ?_
  intro a b
  have ha_ne : u.succAbove a ≠ u := Fin.succAbove_ne u a
  have hb_ne : u.succAbove b ≠ u := Fin.succAbove_ne u b
  have ha_mem : u.succAbove a ∈ ({u}ᶜ : Set (Fin (k + 1))) :=
    Set.mem_compl_singleton_iff.mpr ha_ne
  have hb_mem : u.succAbove b ∈ ({u}ᶜ : Set (Fin (k + 1))) :=
    Set.mem_compl_singleton_iff.mpr hb_ne
  obtain ⟨walk⟩ := hG'.preconnected ⟨u.succAbove a, ha_mem⟩ ⟨u.succAbove b, hb_mem⟩
  let toFink : ↥({u}ᶜ : Set (Fin (k + 1))) → Fin k :=
    fun ⟨x, hx⟩ => (Fin.exists_succAbove_eq (Set.mem_compl_singleton_iff.mp hx)).choose
  have htoFink_spec : ∀ (x : ↥({u}ᶜ : Set (Fin (k + 1)))),
      u.succAbove (toFink x) = x.val :=
    fun ⟨x, hx⟩ => (Fin.exists_succAbove_eq (Set.mem_compl_singleton_iff.mp hx)).choose_spec
  have htoFink_adj : ∀ (x y : ↥({u}ᶜ : Set (Fin (k + 1)))),
      (G.induce ({u}ᶜ : Set _)).Adj x y →
      (adj.submatrix u.succAbove u.succAbove) (toFink x) (toFink y) = 1 := by
    intro x y hadj_xy
    simp only [Matrix.submatrix_apply, SimpleGraph.induce_adj] at hadj_xy ⊢
    rw [htoFink_spec x, htoFink_spec y]; exact hadj_xy
  suffices h_walk : ∀ (a b : ↥({u}ᶜ : Set (Fin (k + 1))))
      (w' : (G.induce ({u}ᶜ : Set _)).Walk a b),
      ∃ path : List (Fin k),
        path.head? = some (toFink a) ∧
        path.getLast? = some (toFink b) ∧
        ∀ m, (hm : m + 1 < path.length) →
          (adj.submatrix u.succAbove u.succAbove)
            (path.get ⟨m, by omega⟩) (path.get ⟨m + 1, hm⟩) = 1 by
    obtain ⟨path, hhead, hlast, hedges⟩ := h_walk _ _ walk
    refine ⟨path, ?_, ?_, hedges⟩
    · convert hhead using 2
      exact (Fin.succAbove_right_injective
        (htoFink_spec ⟨u.succAbove a, ha_mem⟩)).symm
    · convert hlast using 2
      exact (Fin.succAbove_right_injective
        (htoFink_spec ⟨u.succAbove b, hb_mem⟩)).symm
  intro a b w'
  induction w' with
  | nil =>
    exact ⟨[toFink _], rfl, rfl, fun m hm => absurd hm (by simp)⟩
  | @cons c d _ hadj_edge rest ih =>
    obtain ⟨path_rest, hhead_rest, hlast_rest, hedges_rest⟩ := ih
    refine ⟨toFink c :: path_rest, by simp, ?_, ?_⟩
    · cases path_rest with
      | nil => simp at hhead_rest hlast_rest ⊢
      | cons y ys => simp only [List.getLast?_cons_cons]; exact hlast_rest
    · intro m hm
      match m with
      | 0 =>
        simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ]
        have h0 : 0 < path_rest.length := by
          simp only [List.length_cons] at hm; omega
        have hd_eq : path_rest[0] = toFink d := by
          cases path_rest with
          | nil => simp at h0
          | cons y ys =>
            simp only [List.head?, Option.some.injEq] at hhead_rest
            simp only [List.getElem_cons_zero]; exact hhead_rest
        rw [hd_eq]; exact htoFink_adj c d hadj_edge
      | m' + 1 =>
        simp only [List.get_eq_getElem, List.getElem_cons_succ]
        exact hedges_rest m' (by simp only [List.length_cons] at hm; omega)

/-- **At least one branch.** An affine Dynkin diagram whose Cartan form is acyclic
(`∑∑adj < 2n`) and has every degree `≤ 3` must contain a degree-3 vertex: otherwise the balance
`∑ⱼ(deg j − 2)wⱼ = 0` with `wⱼ > 0` and every `deg j ≤ 2` forces all degrees `= 2`, whence
`∑∑adj = 2n`, contradicting acyclicity. -/
lemma affine_tree_exists_branch {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n)
    (hD : IsAffineDynkinDiagram n adj)
    (hacyc : (∑ i, ∑ j, adj i j) < 2 * (n : ℤ))
    (hdeg3 : ∀ v, Etingof.vertexDegree adj v ≤ 3) :
    ∃ v, Etingof.vertexDegree adj v = 3 := by
  classical
  have h01 := hD.2.2.1
  obtain ⟨w, hw_pos, hbal⟩ := affine_degree_balance adj hn hD
  by_contra hno
  push_neg at hno
  have hle2 : ∀ v, Etingof.vertexDegree adj v ≤ 2 := fun v => by
    have h1 := hdeg3 v; have h2 := hno v; omega
  have hterm_nonpos : ∀ v, ((Etingof.vertexDegree adj v : ℤ) - 2) * w v ≤ 0 := by
    intro v
    have hd2 : (Etingof.vertexDegree adj v : ℤ) ≤ 2 := by exact_mod_cast hle2 v
    nlinarith [hw_pos v]
  have hall2 : ∀ v, Etingof.vertexDegree adj v = 2 := by
    intro v
    have hz : ((Etingof.vertexDegree adj v : ℤ) - 2) * w v = 0 := by
      by_contra hne
      have hlt : ((Etingof.vertexDegree adj v : ℤ) - 2) * w v < 0 :=
        lt_of_le_of_ne (hterm_nonpos v) hne
      have hsum_lt : ∑ j, ((Etingof.vertexDegree adj j : ℤ) - 2) * w j
          < ∑ _j : Fin n, (0 : ℤ) :=
        Finset.sum_lt_sum (fun j _ => hterm_nonpos j) ⟨v, Finset.mem_univ v, by simpa using hlt⟩
      rw [Finset.sum_const_zero] at hsum_lt
      linarith [hbal]
    have hwv := hw_pos v
    rcases mul_eq_zero.mp hz with h | h
    · have : (Etingof.vertexDegree adj v : ℤ) = 2 := by linarith
      exact_mod_cast this
    · exact absurd h (ne_of_gt hwv)
  have hsumadj : (∑ i, ∑ j, adj i j) = 2 * (n : ℤ) := by
    have hstep : (∑ i, ∑ j, adj i j) = ∑ _i : Fin n, (2 : ℤ) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [adj_sum_eq_degree h01 i, hall2 i]; norm_num
    rw [hstep, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  linarith [hacyc, hsumadj]

/-- **Branch count.** A connected acyclic affine Dynkin diagram with every vertex of degree `≤ 3`
has exactly one or two degree-3 (branch) vertices.

*Proof route.* Being a tree with maximum degree `3`, the leaf count equals the branch count plus
`2`; degeneracy rules out a path (which would be the positive-definite `Aₙ`), giving at least one
branch vertex, and minimality (`affine_properInduced_finiteDynkin`: every proper connected induced
subgraph is finite Dynkin, so has at most one branch vertex via `dynkin_unique_degree_three`) rules
out three or more. -/
lemma affine_tree_branch_count {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj)
    (hacyc : (∑ i, ∑ j, adj i j) < 2 * (n : ℤ))
    (hdeg3 : ∀ v, Etingof.Problem6_1_3_E7E8.vertexDegree adj v ≤ 3) :
    (∃ v, Etingof.Problem6_1_3_E7E8.vertexDegree adj v = 3 ∧
        ∀ w, Etingof.Problem6_1_3_E7E8.vertexDegree adj w = 3 → w = v)
      ∨ (∃ v w, v ≠ w ∧
        Etingof.Problem6_1_3_E7E8.vertexDegree adj v = 3 ∧
        Etingof.Problem6_1_3_E7E8.vertexDegree adj w = 3 ∧
        ∀ u, Etingof.Problem6_1_3_E7E8.vertexDegree adj u = 3 → u = v ∨ u = w) := by
  classical
  -- The two `vertexDegree` definitions are definitionally equal; work with `Etingof.vertexDegree`.
  have hVD : ∀ (m : ℕ) (M : Matrix (Fin m) (Fin m) ℤ) (v : Fin m),
      Etingof.Problem6_1_3_E7E8.vertexDegree M v = Etingof.vertexDegree M v := fun _ _ _ => rfl
  simp only [hVD] at hdeg3 ⊢
  have hsymm := hD.1
  have hdiag := hD.2.1
  have h01 := hD.2.2.1
  have hconn := hD.2.2.2.1
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a
    rw [Matrix.transpose_apply] at h; exact h
  -- Reindex `n = k + 1` for the leaf-deletion machinery.
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- The branch set.
  set S : Finset (Fin (k + 1)) :=
    Finset.univ.filter (fun v => Etingof.vertexDegree adj v = 3) with hS_def
  have hmemS : ∀ v, v ∈ S ↔ Etingof.vertexDegree adj v = 3 := fun v => by
    simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and]
  -- **At least one branch.**
  obtain ⟨vbr, hvbr⟩ := affine_tree_exists_branch adj (by omega) hD hacyc hdeg3
  have hlo : 1 ≤ S.card := Finset.card_pos.mpr ⟨vbr, (hmemS vbr).mpr hvbr⟩
  -- **A leaf `u` (degree 1) exists**, via the tree structure.
  obtain ⟨u, hu_deg⟩ : ∃ u, Etingof.vertexDegree adj u = 1 := by
    let G : SimpleGraph (Fin (k + 1)) :=
      { Adj := fun i j => adj i j = 1
        symm := ⟨fun i j (h : adj i j = 1) => by rw [hsymm' j i]; exact h⟩
        loopless := ⟨fun i (h : adj i i = 1) => by
          rw [hdiag i] at h; exact absurd h (by norm_num)⟩ }
    haveI : DecidableRel G.Adj := fun i j => decEq (adj i j) 1
    haveI : Nonempty (Fin (k + 1)) := ⟨⟨0, by omega⟩⟩
    have hG_conn : G.Connected := ⟨fun a b => by
      obtain ⟨path, hhead, hlast, hedges⟩ := hconn a b
      exact list_path_reachable G path a b hhead hlast (fun m hm => hedges m hm)⟩
    have hcount : (∑ i, ∑ j, adj i j) = 2 * (#G.edgeFinset : ℤ) := by
      have hterm : ∀ p : Fin (k + 1) × Fin (k + 1),
          adj p.1 p.2 = (if adj p.1 p.2 = 1 then (1 : ℤ) else 0) := by
        intro p; rcases h01 p.1 p.2 with h | h <;> simp [h]
      calc (∑ i, ∑ j, adj i j)
          = ∑ p : Fin (k + 1) × Fin (k + 1), adj p.1 p.2 := (Fintype.sum_prod_type' adj).symm
        _ = ∑ p : Fin (k + 1) × Fin (k + 1), (if adj p.1 p.2 = 1 then (1 : ℤ) else 0) :=
              Finset.sum_congr rfl (fun p _ => hterm p)
        _ = ((univ.filter fun p : Fin (k + 1) × Fin (k + 1) => adj p.1 p.2 = 1).card : ℤ) := by
              rw [Finset.sum_boole]
        _ = ((2 * #G.edgeFinset : ℕ) : ℤ) := by rw [G.two_mul_card_edgeFinset]
        _ = 2 * (#G.edgeFinset : ℤ) := by push_cast; ring
    have hlb : k + 1 ≤ #G.edgeFinset + 1 := by
      have h := hG_conn.card_vert_le_card_edgeSet_add_one
      rwa [Nat.card_fin, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h
    have hub : (#G.edgeFinset : ℤ) < (k + 1 : ℤ) := by
      have h2 : 2 * (#G.edgeFinset : ℤ) < 2 * ((k + 1 : ℕ) : ℤ) := by
        rw [← hcount]; exact hacyc
      push_cast at h2; linarith
    have hub' : #G.edgeFinset < k + 1 := by exact_mod_cast hub
    have hedge_eq : #G.edgeFinset = k := by omega
    have hTree : G.IsTree := by
      rw [SimpleGraph.isTree_iff_connected_and_card]
      refine ⟨hG_conn, ?_⟩
      have hNatEdge : Nat.card G.edgeSet = k := by
        rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hedge_eq]
      rw [hNatEdge, Nat.card_fin]
    -- ≥ 4 vertices, so `Fin (k+1)` is nontrivial.
    have hk3 : 3 ≤ k := by
      have hcnt : Etingof.vertexDegree adj vbr ≤ (Finset.univ.erase vbr).card := by
        unfold Etingof.vertexDegree
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        refine Finset.mem_erase.mpr ⟨fun h' => ?_, Finset.mem_univ _⟩
        subst h'; rw [hdiag x] at hx; exact absurd hx (by norm_num)
      rw [Finset.card_erase_of_mem (Finset.mem_univ vbr), Finset.card_univ,
        Fintype.card_fin] at hcnt
      rw [hvbr] at hcnt; omega
    haveI : Nontrivial (Fin (k + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨u, hu⟩ := hTree.exists_vert_degree_one_of_nontrivial
    refine ⟨u, ?_⟩
    have hdegeq : G.degree u = Etingof.vertexDegree adj u := by
      rw [SimpleGraph.degree]
      unfold Etingof.vertexDegree
      congr 1
      ext j
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl
    rw [hdegeq] at hu; exact hu
  -- Delete the leaf: a finite Dynkin diagram on the survivors.
  have hDsub : IsDynkinDiagram k (adj.submatrix u.succAbove u.succAbove) :=
    affine_delete_leaf_isDynkin adj hD u hu_deg
  -- **At most two branches.**
  have hhi : S.card ≤ 2 := by
    have hpart := Finset.card_filter_add_card_filter_not (s := S) (p := fun v => adj u v = 1)
    have hA : (S.filter (fun v => adj u v = 1)).card ≤ 1 := by
      have hsub : S.filter (fun v => adj u v = 1) ⊆
          Finset.univ.filter (fun j => adj u j = 1) := by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact hv.2
      have hc := Finset.card_le_card hsub
      have hdegu : (Finset.univ.filter (fun j => adj u j = 1)).card = 1 := hu_deg
      omega
    -- A branch vertex not adjacent to `u` keeps degree 3 in the subdiagram.
    have hsubdeg : ∀ (x : Fin (k + 1)) (x' : Fin k), u.succAbove x' = x →
        Etingof.vertexDegree adj x = 3 → ¬ adj u x = 1 →
        Etingof.vertexDegree (adj.submatrix u.succAbove u.succAbove) x' = 3 := by
      intro x x' hx hx3 hxu
      have himg : (Finset.univ.filter
            (fun j : Fin k => (adj.submatrix u.succAbove u.succAbove) x' j = 1)).image u.succAbove
          = Finset.univ.filter (fun c => adj x c = 1) := by
        ext c
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Matrix.submatrix_apply, hx]
        constructor
        · rintro ⟨j, hj, rfl⟩; exact hj
        · intro hc
          have hcu : c ≠ u := by
            intro hcu_eq; rw [hcu_eq, hsymm' x u] at hc; exact hxu hc
          obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hcu
          exact ⟨j, by rw [hj]; exact hc, hj⟩
      have hcardN : (Finset.univ.filter (fun c => adj x c = 1)).card = 3 := hx3
      change (Finset.univ.filter
        (fun j : Fin k => (adj.submatrix u.succAbove u.succAbove) x' j = 1)).card = 3
      rw [← Finset.card_image_of_injective _ Fin.succAbove_right_injective, himg, hcardN]
    have hB : (S.filter (fun v => ¬ adj u v = 1)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      obtain ⟨haS, haU⟩ := ha
      obtain ⟨hbS, hbU⟩ := hb
      have ha3 : Etingof.vertexDegree adj a = 3 := (hmemS a).mp haS
      have hb3 : Etingof.vertexDegree adj b = 3 := (hmemS b).mp hbS
      have hau : a ≠ u := by rintro rfl; rw [hu_deg] at ha3; omega
      have hbu : b ≠ u := by rintro rfl; rw [hu_deg] at hb3; omega
      obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq hau
      obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hbu
      have hda' := hsubdeg a a' ha' ha3 haU
      have hdb' := hsubdeg b b' hb' hb3 hbU
      have hab' : a' = b' := dynkin_unique_degree_three hDsub a' b' hda' hdb'
      rw [← ha', ← hb', hab']
    omega
  -- **Assemble** the disjunction from `S.card ∈ {1, 2}`.
  rcases Nat.lt_or_ge S.card 2 with hcard | hcard
  · have hc1 : S.card = 1 := by omega
    obtain ⟨a, haS⟩ := Finset.card_eq_one.mp hc1
    left
    refine ⟨a, (hmemS a).mp (by rw [haS]; exact Finset.mem_singleton_self a), ?_⟩
    intro w hw
    have hwmem : w ∈ S := (hmemS w).mpr hw
    rw [haS, Finset.mem_singleton] at hwmem; exact hwmem
  · have hc2 : S.card = 2 := by omega
    obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.mp hc2
    right
    refine ⟨a, b, hab,
      (hmemS a).mp (by rw [hSab]; exact Finset.mem_insert_self a _),
      (hmemS b).mp (by rw [hSab]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)),
      ?_⟩
    intro w hw
    have hwmem : w ∈ S := (hmemS w).mpr hw
    rw [hSab, Finset.mem_insert, Finset.mem_singleton] at hwmem; exact hwmem

/-- **A leaf sits at a branch vertex.** In a connected acyclic affine Dynkin diagram with all
degrees `≤ 3` and exactly two branch (degree-3) vertices `v, w`, some leaf (degree-1 vertex) is
adjacent to `v` or to `w`.

*Proof.* A leaf `u` exists because the graph is a tree (`hacyc`); deleting it yields a finite
Dynkin diagram (`affine_delete_leaf_isDynkin`), which has at most one degree-3 vertex
(`dynkin_unique_degree_three`). A branch vertex not adjacent to `u` keeps degree 3 in the deletion,
so if `u` touched neither `v` nor `w`, both would remain degree 3 there — contradicting uniqueness.
Hence `u` is adjacent to `v` or `w`. -/
lemma affine_two_branch_has_leaf {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj)
    (hacyc : (∑ i, ∑ j, adj i j) < 2 * (n : ℤ))
    (hdeg3 : ∀ v, Etingof.Problem6_1_3_E7E8.vertexDegree adj v ≤ 3)
    (v w : Fin n) (hvw : v ≠ w)
    (hv : Etingof.Problem6_1_3_E7E8.vertexDegree adj v = 3)
    (hw : Etingof.Problem6_1_3_E7E8.vertexDegree adj w = 3) :
    ∃ ℓ, Etingof.Problem6_1_3_E7E8.vertexDegree adj ℓ = 1 ∧
      (adj v ℓ = 1 ∨ adj w ℓ = 1) := by
  classical
  -- The two `vertexDegree` definitions are definitionally equal; work with `Etingof.vertexDegree`.
  have hVD : ∀ (m : ℕ) (M : Matrix (Fin m) (Fin m) ℤ) (x : Fin m),
      Etingof.Problem6_1_3_E7E8.vertexDegree M x = Etingof.vertexDegree M x := fun _ _ _ => rfl
  simp only [hVD] at hv hw ⊢
  have hsymm := hD.1
  have hdiag := hD.2.1
  have h01 := hD.2.2.1
  have hconn := hD.2.2.2.1
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a
    rw [Matrix.transpose_apply] at h; exact h
  -- Reindex `n = k + 1` for the leaf-deletion machinery.
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- **A leaf `u` (degree 1) exists**, via the tree structure (same derivation as
  -- `affine_tree_branch_count`).
  obtain ⟨u, hu_deg⟩ : ∃ u, Etingof.vertexDegree adj u = 1 := by
    let G : SimpleGraph (Fin (k + 1)) :=
      { Adj := fun i j => adj i j = 1
        symm := ⟨fun i j (h : adj i j = 1) => by rw [hsymm' j i]; exact h⟩
        loopless := ⟨fun i (h : adj i i = 1) => by
          rw [hdiag i] at h; exact absurd h (by norm_num)⟩ }
    haveI : DecidableRel G.Adj := fun i j => decEq (adj i j) 1
    haveI : Nonempty (Fin (k + 1)) := ⟨⟨0, by omega⟩⟩
    have hG_conn : G.Connected := ⟨fun a b => by
      obtain ⟨path, hhead, hlast, hedges⟩ := hconn a b
      exact list_path_reachable G path a b hhead hlast (fun m hm => hedges m hm)⟩
    have hcount : (∑ i, ∑ j, adj i j) = 2 * (#G.edgeFinset : ℤ) := by
      have hterm : ∀ p : Fin (k + 1) × Fin (k + 1),
          adj p.1 p.2 = (if adj p.1 p.2 = 1 then (1 : ℤ) else 0) := by
        intro p; rcases h01 p.1 p.2 with h | h <;> simp [h]
      calc (∑ i, ∑ j, adj i j)
          = ∑ p : Fin (k + 1) × Fin (k + 1), adj p.1 p.2 := (Fintype.sum_prod_type' adj).symm
        _ = ∑ p : Fin (k + 1) × Fin (k + 1), (if adj p.1 p.2 = 1 then (1 : ℤ) else 0) :=
              Finset.sum_congr rfl (fun p _ => hterm p)
        _ = ((univ.filter fun p : Fin (k + 1) × Fin (k + 1) => adj p.1 p.2 = 1).card : ℤ) := by
              rw [Finset.sum_boole]
        _ = ((2 * #G.edgeFinset : ℕ) : ℤ) := by rw [G.two_mul_card_edgeFinset]
        _ = 2 * (#G.edgeFinset : ℤ) := by push_cast; ring
    have hub : (#G.edgeFinset : ℤ) < (k + 1 : ℤ) := by
      have h2 : 2 * (#G.edgeFinset : ℤ) < 2 * ((k + 1 : ℕ) : ℤ) := by
        rw [← hcount]; exact hacyc
      push_cast at h2; linarith
    have hub' : #G.edgeFinset < k + 1 := by exact_mod_cast hub
    have hlb : k + 1 ≤ #G.edgeFinset + 1 := by
      have h := hG_conn.card_vert_le_card_edgeSet_add_one
      rwa [Nat.card_fin, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h
    have hedge_eq : #G.edgeFinset = k := by omega
    have hTree : G.IsTree := by
      rw [SimpleGraph.isTree_iff_connected_and_card]
      refine ⟨hG_conn, ?_⟩
      have hNatEdge : Nat.card G.edgeSet = k := by
        rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hedge_eq]
      rw [hNatEdge, Nat.card_fin]
    haveI : Nontrivial (Fin (k + 1)) := ⟨⟨v, w, hvw⟩⟩
    obtain ⟨u, hu⟩ := hTree.exists_vert_degree_one_of_nontrivial
    refine ⟨u, ?_⟩
    have hdegeq : G.degree u = Etingof.vertexDegree adj u := by
      rw [SimpleGraph.degree]
      unfold Etingof.vertexDegree
      congr 1
      ext j
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl
    rw [hdegeq] at hu; exact hu
  -- Delete the leaf: a finite Dynkin diagram on the survivors.
  have hDsub : IsDynkinDiagram k (adj.submatrix u.succAbove u.succAbove) :=
    affine_delete_leaf_isDynkin adj hD u hu_deg
  -- `v, w` are not the leaf (degree 3 ≠ 1).
  have hvu : v ≠ u := by rintro rfl; rw [hu_deg] at hv; omega
  have hwu : w ≠ u := by rintro rfl; rw [hu_deg] at hw; omega
  -- A branch vertex not adjacent to `u` keeps degree 3 in the deletion.
  have hsubdeg : ∀ (x : Fin (k + 1)) (x' : Fin k), u.succAbove x' = x →
      Etingof.vertexDegree adj x = 3 → ¬ adj u x = 1 →
      Etingof.vertexDegree (adj.submatrix u.succAbove u.succAbove) x' = 3 := by
    intro x x' hx hx3 hxu
    have himg : (Finset.univ.filter
          (fun j : Fin k => (adj.submatrix u.succAbove u.succAbove) x' j = 1)).image u.succAbove
        = Finset.univ.filter (fun c => adj x c = 1) := by
      ext c
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Matrix.submatrix_apply, hx]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro hc
        have hcu : c ≠ u := by
          intro hcu_eq; rw [hcu_eq, hsymm' x u] at hc; exact hxu hc
        obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hcu
        exact ⟨j, by rw [hj]; exact hc, hj⟩
    have hcardN : (Finset.univ.filter (fun c => adj x c = 1)).card = 3 := hx3
    change (Finset.univ.filter
      (fun j : Fin k => (adj.submatrix u.succAbove u.succAbove) x' j = 1)).card = 3
    rw [← Finset.card_image_of_injective _ Fin.succAbove_right_injective, himg, hcardN]
  -- Conclude: the leaf `u` is adjacent to `v` or `w`.
  refine ⟨u, hu_deg, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnv, hnw⟩ := hcon
  have hnv' : ¬ adj u v = 1 := by rw [hsymm' u v]; exact hnv
  have hnw' : ¬ adj u w = 1 := by rw [hsymm' u w]; exact hnw
  obtain ⟨v', hv'⟩ := Fin.exists_succAbove_eq hvu
  obtain ⟨w', hw'⟩ := Fin.exists_succAbove_eq hwu
  have hdv' := hsubdeg v v' hv' hv hnv'
  have hdw' := hsubdeg w w' hw' hw hnw'
  have hv'w' : v' = w' := dynkin_unique_degree_three hDsub v' w' hdv' hdw'
  exact hvw (by rw [← hv', ← hw', hv'w'])

/-- **Fork-shift adjacency identity.** Deleting the fork-leaf `0` from `D̃ₖ` and shifting every
surviving index down by one turns the survivor graph into the finite `Dₖ`. Pointwise: for indices
`x, y` of `D̃ₖ` with `x = a + 1`, `y = b + 1` (so `a, b` survive as vertices of `Dₖ`),
`Dₖ.adj a b = D̃ₖ.adj x y`. This is a pure identity between the two standard adjacency matrices; it
carries no geometry and is the reindexing engine's arithmetic core. -/
private lemma dtilde_shift_adj' {k : ℕ} (hk : 4 ≤ k)
    (x y : Fin (AffineType.Dtilde k hk).rank) (a b : Fin (DynkinType.D k hk).rank)
    (hxa : x.val = a.val + 1) (hyb : y.val = b.val + 1) :
    (DynkinType.D k hk).adj a b = (AffineType.Dtilde k hk).adj x y := by
  show (if ((a.val + 1 = b.val ∧ b.val ≤ k - 2) ∨ (b.val + 1 = a.val ∧ a.val ≤ k - 2)) ∨
           ((a.val = k - 3 ∧ b.val = k - 1) ∨ (b.val = k - 3 ∧ a.val = k - 1)) then (1 : ℤ) else 0)
     = (if (min x.val y.val = 0 ∧ max x.val y.val = 2) ∨
           (min x.val y.val = 1 ∧ max x.val y.val = 2) ∨
           (2 ≤ min x.val y.val ∧ max x.val y.val ≤ k - 2 ∧ min x.val y.val + 1 = max x.val y.val) ∨
           (min x.val y.val = k - 2 ∧ max x.val y.val = k - 1) ∨
           (min x.val y.val = k - 2 ∧ max x.val y.val = k) then (1 : ℤ) else 0)
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

/-- **Reindexing engine for the two-fork (D̃ₖ) case.** Degeneracy-independent: it takes the finite
classification of the leaf-deleted diagram as explicit hypotheses. Given a symmetric `0/1` graph
`adj` on `Fin (k+1)`, a fork-leaf `u` attached at `u.succAbove v'`, and a graph isomorphism `σ'`
identifying the survivors `adj.submatrix u.succAbove u.succAbove` with the finite `Dₖ` in which the
reattach point `v'` sits one step in from the far single-leaf end (`σ'.symm v' = 1`), it reattaches
`u` to rebuild the affine `D̃ₖ`, producing a graph isomorphism onto `AffineType.Dtilde k`.

This is the affine analogue of the finite `Etingof.tree_branch_iso`; the reattached fork-leaf lands
at `D̃ₖ`-index `0`, and every survivor `p ≥ 1` maps through `σ'` after the index shift `p ↦ p - 1`
(`dtilde_shift_adj'`). -/
lemma affine_two_fork_reindex {k : ℕ} (hk : 4 ≤ k)
    (adj : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hsymm : adj.IsSymm) (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (u : Fin (k + 1)) (v' : Fin k)
    (hu_adj : adj u (u.succAbove v') = 1)
    (hu_unique : ∀ w, adj u w = 1 → w = u.succAbove v')
    (σ' : Fin (DynkinType.D k hk).rank ≃ Fin k)
    (hσ' : ∀ i j, (adj.submatrix u.succAbove u.succAbove) (σ' i) (σ' j)
                    = (DynkinType.D k hk).adj i j)
    (hv'pos : σ'.symm v' = ⟨1, by have h : (DynkinType.D k hk).rank = k := rfl; omega⟩) :
    ∃ σ : Fin (AffineType.Dtilde k hk).rank ≃ Fin (k + 1),
      ∀ i j, adj (σ i) (σ j) = (AffineType.Dtilde k hk).adj i j := by
  classical
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a
    rw [Matrix.transpose_apply] at h; exact h
  -- Index bound for the down-shift `p ↦ p - 1` into `Fin (Dₖ).rank = Fin k`.
  have hidx : ∀ (p : Fin (AffineType.Dtilde k hk).rank), p.val - 1 < (DynkinType.D k hk).rank := by
    intro p
    have h4 : (DynkinType.D k hk).rank = k := rfl
    have h5 : (AffineType.Dtilde k hk).rank = k + 1 := rfl
    have := p.isLt
    omega
  -- Evaluate the target `D̃ₖ` adjacency in decidable arithmetic form.
  have dtilde_eval : ∀ x y : Fin (AffineType.Dtilde k hk).rank,
      (AffineType.Dtilde k hk).adj x y
        = if (min x.val y.val = 0 ∧ max x.val y.val = 2) ∨
             (min x.val y.val = 1 ∧ max x.val y.val = 2) ∨
             (2 ≤ min x.val y.val ∧ max x.val y.val ≤ k - 2 ∧
                min x.val y.val + 1 = max x.val y.val) ∨
             (min x.val y.val = k - 2 ∧ max x.val y.val = k - 1) ∨
             (min x.val y.val = k - 2 ∧ max x.val y.val = k) then (1 : ℤ) else 0 :=
    fun _ _ => rfl
  -- Forward map: `D̃ₖ`-index `0 ↦ u` (the reattached fork-leaf); index `p ≥ 1 ↦ u.succAbove (σ' (p-1))`.
  let fwd : Fin (AffineType.Dtilde k hk).rank → Fin (k + 1) := fun p =>
    if _ : 0 < p.val then u.succAbove (σ' ⟨p.val - 1, hidx p⟩) else u
  have fwd_inj : Function.Injective fwd := by
    intro p q hpq
    simp only [fwd] at hpq
    by_cases hp : 0 < p.val <;> by_cases hq : 0 < q.val
    · rw [dif_pos hp, dif_pos hq] at hpq
      have h1 := Fin.succAbove_right_injective hpq
      have h2 := σ'.injective h1
      rw [Fin.mk.injEq] at h2
      exact Fin.ext (by omega)
    · rw [dif_pos hp, dif_neg hq] at hpq
      exact absurd hpq (Fin.succAbove_ne u _)
    · rw [dif_neg hp, dif_pos hq] at hpq
      exact absurd hpq.symm (Fin.succAbove_ne u _)
    · exact Fin.ext (by omega)
  refine ⟨Equiv.ofBijective fwd ((Finite.injective_iff_bijective).mp fwd_inj), fun p q => ?_⟩
  change adj (fwd p) (fwd q) = (AffineType.Dtilde k hk).adj p q
  simp only [fwd]
  by_cases hp : 0 < p.val <;> by_cases hq : 0 < q.val
  · -- Both survivors: reduce to `Dₖ` via `σ'`, then the shift identity.
    rw [dif_pos hp, dif_pos hq]
    have hsub := hσ' ⟨p.val - 1, hidx p⟩ ⟨q.val - 1, hidx q⟩
    rw [Matrix.submatrix_apply] at hsub
    rw [hsub]
    exact dtilde_shift_adj' hk p q ⟨p.val - 1, hidx p⟩ ⟨q.val - 1, hidx q⟩
      (by show p.val = p.val - 1 + 1; omega) (by show q.val = q.val - 1 + 1; omega)
  · -- `p` survivor, `q = 0` (the reattached leaf).
    rw [dif_pos hp, dif_neg hq]
    have hq0 : q.val = 0 := by omega
    have hLHS : adj (u.succAbove (σ' ⟨p.val - 1, hidx p⟩)) u = if p.val = 2 then (1 : ℤ) else 0 := by
      by_cases hp2 : p.val = 2
      · rw [if_pos hp2]
        have hidxp : (⟨p.val - 1, hidx p⟩ : Fin (DynkinType.D k hk).rank) = σ'.symm v' := by
          rw [hv'pos]; apply Fin.ext; show p.val - 1 = 1; omega
        rw [hidxp, σ'.apply_symm_apply, hsymm' (u.succAbove v') u, hu_adj]
      · rw [if_neg hp2]
        have hne : σ' ⟨p.val - 1, hidx p⟩ ≠ v' := by
          intro heq
          have hsv : (⟨p.val - 1, hidx p⟩ : Fin (DynkinType.D k hk).rank) = σ'.symm v' := by
            rw [← heq, σ'.symm_apply_apply]
          rw [hv'pos, Fin.mk.injEq] at hsv
          omega
        rcases h01 (u.succAbove (σ' ⟨p.val - 1, hidx p⟩)) u with h0 | h1
        · exact h0
        · rw [hsymm' _ u] at h1
          exact absurd (hu_unique _ h1) (fun h => hne (Fin.succAbove_right_injective h))
    rw [hLHS, dtilde_eval p q]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  · -- `p = 0` (the reattached leaf), `q` survivor.
    rw [dif_neg hp, dif_pos hq]
    have hp0 : p.val = 0 := by omega
    have hLHS : adj u (u.succAbove (σ' ⟨q.val - 1, hidx q⟩)) = if q.val = 2 then (1 : ℤ) else 0 := by
      by_cases hq2 : q.val = 2
      · rw [if_pos hq2]
        have hidxq : (⟨q.val - 1, hidx q⟩ : Fin (DynkinType.D k hk).rank) = σ'.symm v' := by
          rw [hv'pos]; apply Fin.ext; show q.val - 1 = 1; omega
        rw [hidxq, σ'.apply_symm_apply, hu_adj]
      · rw [if_neg hq2]
        have hne : σ' ⟨q.val - 1, hidx q⟩ ≠ v' := by
          intro heq
          have hsv : (⟨q.val - 1, hidx q⟩ : Fin (DynkinType.D k hk).rank) = σ'.symm v' := by
            rw [← heq, σ'.symm_apply_apply]
          rw [hv'pos, Fin.mk.injEq] at hsv
          omega
        rcases h01 u (u.succAbove (σ' ⟨q.val - 1, hidx q⟩)) with h0 | h1
        · exact h0
        · exact absurd (hu_unique _ h1) (fun h => hne (Fin.succAbove_right_injective h))
    rw [hLHS, dtilde_eval p q]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  · -- Both `= 0`: the reattached leaf against itself.
    rw [dif_neg hp, dif_neg hq, hdiag u]
    have hp0 : p.val = 0 := by omega
    have hq0 : q.val = 0 := by omega
    rw [dtilde_eval p q]
    split_ifs with h1 <;> first | rfl | (exfalso; omega)

/-- **Leaf-deleted two-branch affine diagram is a finite `Dₖ`, with the reattach point one step
in from the far leaf.** This is the *classification crux* of `affine_tree_two_branch_iso`: given a
connected acyclic affine Dynkin diagram on `Fin (k+1)` with all degrees `≤ 3` and exactly two branch
(degree-3) vertices `v, w`, and a leaf `ℓ` attached to `v`, deleting `ℓ` yields a finite Dynkin
diagram on `Fin k` (`affine_delete_leaf_isDynkin`) whose classification (`branch_classification`) is
forced to be the **`Dₖ`** family — the E-types `E₆/E₇/E₈` are *ruled out* — and the reattach point
`v'` (the survivor index of `v`) sits at `Dₖ`-position `1`, one step in from the far single-leaf
end (index `0`).

Ruling out the E-types is the affine-degeneracy step: because `w` is untouched by the deletion it
keeps degree 3, so the survivor has a unique branch vertex and is `Dₖ`, `E₆`, `E₇`, or `E₈`; the
positive-semidefinite-but-degenerate Cartan form of the affine diagram pins the two fork-arms at
`w` to length `1` each (equivalently, `w`'s branch vertex in the survivor has *two* leaf-neighbours,
true only for `Dₖ`, not for any E branch vertex). Formalizing that discriminator requires the
two-branch analogue of the one-branch arm-length machinery (`affine_arm_length_solutions`,
`affine_tree_one_arm_reciprocal`) and is split off as its own sub-issue; the surrounding scaffolding
(leaf extraction, deletion, and the reindexing engine `affine_two_fork_reindex`) is complete.

`sorry`-tracked: see the sub-issue for the E-ruling-out + reattach-point localization. -/
lemma affine_two_branch_deleted_isD {k : ℕ} (adj : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hD : IsAffineDynkinDiagram (k + 1) adj)
    (hacyc : (∑ i, ∑ j, adj i j) < 2 * ((k + 1 : ℕ) : ℤ))
    (hdeg3 : ∀ x, Etingof.Problem6_1_3_E7E8.vertexDegree adj x ≤ 3)
    (v w : Fin (k + 1)) (hvw : v ≠ w)
    (hv : Etingof.Problem6_1_3_E7E8.vertexDegree adj v = 3)
    (hw : Etingof.Problem6_1_3_E7E8.vertexDegree adj w = 3)
    (huniq : ∀ u, Etingof.Problem6_1_3_E7E8.vertexDegree adj u = 3 → u = v ∨ u = w)
    (ℓ : Fin (k + 1)) (hℓdeg : Etingof.Problem6_1_3_E7E8.vertexDegree adj ℓ = 1)
    (hℓv : adj v ℓ = 1) :
    ∃ (hk : 4 ≤ k) (v' : Fin k), ℓ.succAbove v' = v ∧
      ∃ σ' : Fin (DynkinType.D k hk).rank ≃ Fin k,
        (∀ i j, (adj.submatrix ℓ.succAbove ℓ.succAbove) (σ' i) (σ' j)
                  = (DynkinType.D k hk).adj i j) ∧
        σ'.symm v' = ⟨1, by have h : (DynkinType.D k hk).rank = k := rfl; omega⟩ := by
  sorry

/-- **Two branch vertices ⟹ D̃ₙ.** A connected acyclic affine Dynkin diagram with all degrees `≤ 3`
and exactly two branch (degree-3) vertices is graph-isomorphic to `AffineType.Dtilde n` for some
`n ≥ 4` (a chain with a two-leaf fork at each end). Affine analogue of the finite
`tree_branch_iso`.

*Proof.* A leaf `ℓ` sits at one of the two branch vertices (`affine_two_branch_has_leaf`); call that
one `v`. Deleting `ℓ` and classifying the survivor pins it to the finite `Dₖ` with `v` reattached
one step in from the far leaf (`affine_two_branch_deleted_isD`); the reindexing engine
`affine_two_fork_reindex` then reattaches `ℓ` to rebuild `AffineType.Dtilde k`. The leaf sitting at
`w` instead of `v` is the same argument with `v, w` swapped. -/
lemma affine_tree_two_branch_iso {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj)
    (hacyc : (∑ i, ∑ j, adj i j) < 2 * (n : ℤ))
    (hdeg3 : ∀ v, Etingof.Problem6_1_3_E7E8.vertexDegree adj v ≤ 3)
    (v w : Fin n) (hvw : v ≠ w)
    (hv : Etingof.Problem6_1_3_E7E8.vertexDegree adj v = 3)
    (hw : Etingof.Problem6_1_3_E7E8.vertexDegree adj w = 3)
    (huniq : ∀ u, Etingof.Problem6_1_3_E7E8.vertexDegree adj u = 3 → u = v ∨ u = w) :
    ∃ t : AffineType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  classical
  -- Reindex `n = k + 1` for the leaf-deletion machinery.
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hD.1 b) a
    rw [Matrix.transpose_apply] at h; exact h
  -- A leaf `ℓ` is adjacent to one of the two branch vertices `v, w`.
  obtain ⟨ℓ, hℓdeg, hℓadj⟩ := affine_two_branch_has_leaf adj hn hD hacyc hdeg3 v w hvw hv hw
  -- A degree-1 vertex has a unique neighbour.
  have huniqueN : ∀ (t : Fin (k + 1)), adj ℓ t = 1 → ∀ w', adj ℓ w' = 1 → w' = t := by
    intro t ht w' hw'
    have hcard : (univ.filter (fun j => adj ℓ j = 1)).card = 1 := hℓdeg
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have htmem : t ∈ univ.filter (fun j => adj ℓ j = 1) :=
      Finset.mem_filter.mpr ⟨mem_univ _, ht⟩
    have hw'mem : w' ∈ univ.filter (fun j => adj ℓ j = 1) :=
      Finset.mem_filter.mpr ⟨mem_univ _, hw'⟩
    rw [ha, Finset.mem_singleton] at htmem hw'mem
    rw [hw'mem, htmem]
  -- WLOG the leaf is attached to the vertex we call `v`.
  rcases hℓadj with hℓv | hℓw
  · -- Leaf attached to `v`.
    have hℓv' : adj ℓ v = 1 := by rw [hsymm']; exact hℓv
    obtain ⟨hk, v', hv'eq, σ', hσ', hv'pos⟩ :=
      affine_two_branch_deleted_isD adj hD hacyc hdeg3 v w hvw hv hw huniq ℓ hℓdeg hℓv
    have hu_adj : adj ℓ (ℓ.succAbove v') = 1 := by rw [hv'eq]; exact hℓv'
    have hu_unique : ∀ w', adj ℓ w' = 1 → w' = ℓ.succAbove v' := by
      intro w' hw'; rw [hv'eq]; exact huniqueN v hℓv' w' hw'
    obtain ⟨σ, hσ⟩ :=
      affine_two_fork_reindex hk adj hD.1 hD.2.1 hD.2.2.1 ℓ v' hu_adj hu_unique σ' hσ' hv'pos
    exact ⟨AffineType.Dtilde k hk, σ, hσ⟩
  · -- Leaf attached to `w`: same argument with the two branch vertices swapped.
    have hℓw' : adj ℓ w = 1 := by rw [hsymm']; exact hℓw
    obtain ⟨hk, v', hv'eq, σ', hσ', hv'pos⟩ :=
      affine_two_branch_deleted_isD adj hD hacyc hdeg3 w v (Ne.symm hvw) hw hv
        (fun u hu => (huniq u hu).symm) ℓ hℓdeg hℓw
    have hu_adj : adj ℓ (ℓ.succAbove v') = 1 := by rw [hv'eq]; exact hℓw'
    have hu_unique : ∀ w', adj ℓ w' = 1 → w' = ℓ.succAbove v' := by
      intro w' hw'; rw [hv'eq]; exact huniqueN w hℓw' w' hw'
    obtain ⟨σ, hσ⟩ :=
      affine_two_fork_reindex hk adj hD.1 hD.2.1 hD.2.2.1 ℓ v' hu_adj hu_unique σ' hσ' hv'pos
    exact ⟨AffineType.Dtilde k hk, σ, hσ⟩

/-- **Affine arm-length Diophantine.** The equality analogue of the finite
`Etingof.Problem6_1_3_E7E8.arm_length_solutions` (`DynkinForward.lean`): the only solutions of
`1/(p+1) + 1/(q+1) + 1/(r+1) = 1` with `1 ≤ p ≤ q ≤ r` are `(2,2,2)`, `(1,3,3)`, `(1,2,5)` —
the arm lengths of `Ẽ₆`, `Ẽ₇`, `Ẽ₈` respectively. The reciprocal identity is presented in the
cleared-denominator form `(q+1)(r+1) + (p+1)(r+1) + (p+1)(q+1) = (p+1)(q+1)(r+1)`.

Unlike the finite case (a strict inequality `> 1` with an infinite family `(1,1,r)`), the affine
equality has exactly these three solutions: the degeneracy of the Cartan form pins the reciprocal
sum to `1` on the nose. Note `p ≥ 1` here, since `p = 0` would make the branch vertex degree `≤ 2`.
-/
lemma affine_arm_length_solutions (p q r : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hrecip : (q + 1) * (r + 1) + (p + 1) * (r + 1) + (p + 1) * (q + 1) =
              (p + 1) * (q + 1) * (r + 1)) :
    (p = 2 ∧ q = 2 ∧ r = 2) ∨ (p = 1 ∧ q = 3 ∧ r = 3) ∨
    (p = 1 ∧ q = 2 ∧ r = 5) := by
  -- Upper bound `p ≤ 2`: if `p ≥ 3` then `p+1, q+1, r+1 ≥ 4`, so `3·(p+1)(q+1)(r+1) ≥ 4·(sum of
  -- pairwise products)`, forcing the reciprocal sum `≤ 3/4 < 1`, contradicting the equality.
  have hp_le : p ≤ 2 := by
    by_contra hp_big
    have hr3 : 3 ≤ r := by omega
    have hq3 : 3 ≤ q := by omega
    have h1 : 4 * ((q + 1) * (r + 1)) ≤ (p + 1) * ((q + 1) * (r + 1)) := by gcongr; omega
    have h2 : 4 * ((p + 1) * (r + 1)) ≤ (q + 1) * ((p + 1) * (r + 1)) := by gcongr; omega
    have h3 : 4 * ((p + 1) * (q + 1)) ≤ (r + 1) * ((p + 1) * (q + 1)) := by gcongr; omega
    have hpos : 1 ≤ (q + 1) * (r + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith [h1, h2, h3, hpos]
  interval_cases p
  · -- `p = 1`: bound `q ≤ 3` (if `q ≥ 4` then `1/2 + 1/5 + 1/5 = 9/10 < 1`), then the equality
    -- pins `r` linearly in each remaining case.
    have hq_le : q ≤ 3 := by
      by_contra hq_big
      have hr4 : 4 ≤ r := le_trans (by omega) hqr
      have h2 : 5 * (r + 1) ≤ (q + 1) * (r + 1) := by gcongr; omega
      nlinarith [h2]
    interval_cases q
    · exfalso; omega          -- `q = 1`: `1/2 + 1/2 + 1/(r+1) = 1` has no solution.
    · right; right; exact ⟨rfl, rfl, by omega⟩   -- `q = 2` ⟹ `r = 5` (`Ẽ₈`).
    · right; left; exact ⟨rfl, rfl, by omega⟩    -- `q = 3` ⟹ `r = 3` (`Ẽ₇`).
  · -- `p = 2`: bound `q ≤ 2` (if `q ≥ 3` then `1/3 + 1/4 + 1/4 = 5/6 < 1`), giving `q = 2, r = 2`.
    have hq_le : q ≤ 2 := by
      by_contra hq_big
      have hr3 : 3 ≤ r := le_trans (by omega) hqr
      have h2 : 4 * (r + 1) ≤ (q + 1) * (r + 1) := by gcongr; omega
      nlinarith [h2]
    interval_cases q
    · left; exact ⟨rfl, rfl, by omega⟩          -- `q = 2` ⟹ `r = 2` (`Ẽ₆`).

/-- **Arm-layout adjacency pattern.** With `n = 1 + p + q + r`, a one-branch tree is laid out along
`Fin n` as follows: the `p`-arm on indices `0 … p-1` (tip → hub-neighbour), the hub at index `p`,
the `q`-arm on `p+1 … p+q` (hub-neighbour → tip), and the `r`-arm on `p+q+1 … p+q+r`
(hub-neighbour → tip) attached to the hub. This predicate is the resulting edge relation on indices:
the two arms `p, q` join through the hub into a single path `0 … p+q`, and the `r`-arm hangs off the
hub (index `p`) starting at index `p+q+1`. -/
def armAdjIdx (p q r i j : ℕ) : Prop :=
  ((i + 1 = j ∨ j + 1 = i) ∧ i ≤ p + q ∧ j ≤ p + q) ∨
  ((i = p ∧ j = p + q + 1) ∨ (j = p ∧ i = p + q + 1)) ∨
  ((i + 1 = j ∨ j + 1 = i) ∧ p + q + 1 ≤ i ∧ p + q + 1 ≤ j)

instance (p q r i j : ℕ) : Decidable (armAdjIdx p q r i j) := by
  unfold armAdjIdx; infer_instance

/-- **Linearity of a harmonic arm.** If `f 0, f 1, …, f L` is a sequence with `2·f 0 = f 1` (leaf
condition) and `2·f i = f (i-1) + f (i+1)` at every interior index `1 ≤ i ≤ L-1`, then
`f i = (i+1)·f 0`. Applied to the strictly-positive null vector restricted to an arm: the null-vector
harmonic relation makes it linear from the tip to the hub. -/
private lemma arm_linear (f : ℕ → ℤ) (L : ℕ) (hleaf : 2 * f 0 = f 1)
    (hint : ∀ i, 1 ≤ i → i + 1 ≤ L → 2 * f i = f (i - 1) + f (i + 1)) :
    ∀ i, i ≤ L → f i = (i + 1 : ℤ) * f 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    match i with
    | 0 => simp
    | 1 => push_cast; linarith [hleaf]
    | (k + 2) =>
      have e1 := ih (k + 1) (by omega) (by omega)
      have e0 := ih k (by omega) (by omega)
      have hrec : 2 * f (k + 1) = f k + f (k + 2) := by
        have h := hint (k + 1) (by omega) (by omega)
        simpa using h
      have hval : f (k + 2) = 2 * f (k + 1) - f k := by linarith [hrec]
      rw [hval, e1, e0]; push_cast; ring

/-- **Arm-length reciprocal from the null vector.** Pure arithmetic: if the strictly-positive hub
value `W` factors as `(p+1)·a = (q+1)·b = (r+1)·c` (arm linearity: `W` is `arm-length + 1` times the
tip value on each of the three arms) and the three tip values sum to `W` (hub harmonicity), then the
cleared-denominator reciprocal equality holds. -/
private lemma reciprocal_of_arm_data (p q r : ℕ) (W a b c : ℤ) (hW : 0 < W)
    (hpa : W = (p + 1) * a) (hqb : W = (q + 1) * b) (hrc : W = (r + 1) * c)
    (hsum : a + b + c = W) :
    (q + 1) * (r + 1) + (p + 1) * (r + 1) + (p + 1) * (q + 1)
      = (p + 1) * (q + 1) * (r + 1) := by
  have key : (((q + 1) * (r + 1) + (p + 1) * (r + 1) + (p + 1) * (q + 1) : ℕ) : ℤ) * W
      = (((p + 1) * (q + 1) * (r + 1) : ℕ) : ℤ) * W := by
    push_cast
    linear_combination (((p : ℤ) + 1) * (q + 1) * (r + 1)) * hsum
      + ((q : ℤ) + 1) * (r + 1) * hpa + ((p : ℤ) + 1) * (r + 1) * hqb
      + ((p : ℤ) + 1) * (q + 1) * hrc
  have := mul_right_cancel₀ (ne_of_gt hW) key
  exact_mod_cast this

/-- **Arm layout of a one-branch affine tree (structural extraction).** A connected acyclic affine
Dynkin diagram with all degrees `≤ 3` and a *unique* degree-3 vertex `v` is, up to re-indexing `σ`,
laid out in the `armAdjIdx` pattern: three arms of lengths `1 ≤ p ≤ q ≤ r` emanating from the hub
(at index `p`), with `n = 1 + p + q + r`. The two shorter arms `p, q` join through the hub into a
single path `0 … p+q`; the arm `r` hangs off the hub (index `p`) starting at index `p+q+1`.

This is the pure graph-combinatorial core: walk each arm from the hub via the degree-`≤ 2`
neighbour structure (cf. `path_walk_construction`, `two_regular_connected_iso_Atilde`, `otherNbr`),
order the three arm lengths, and assemble the re-indexing. The reciprocal equality is *not* proved
here — that is `affine_tree_one_arm_reciprocal`, which consumes this layout and the null vector. -/
lemma affine_one_branch_arm_layout {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj)
    (hacyc : (∑ i, ∑ j, adj i j) < 2 * (n : ℤ))
    (hdeg3 : ∀ v, Etingof.Problem6_1_3_E7E8.vertexDegree adj v ≤ 3)
    (v : Fin n) (hv : Etingof.Problem6_1_3_E7E8.vertexDegree adj v = 3)
    (huniq : ∀ w, Etingof.Problem6_1_3_E7E8.vertexDegree adj w = 3 → w = v) :
    ∃ (p q r : ℕ) (σ : Fin n ≃ Fin n),
      1 ≤ p ∧ p ≤ q ∧ q ≤ r ∧ n = 1 + p + q + r ∧
      (σ.symm v).val = p ∧
      (∀ i j, adj (σ i) (σ j) = 1 ↔ armAdjIdx p q r i.val j.val) := by
  -- Sub-issue: three-arm walk + reindexing onto the `armAdjIdx` layout. See the doc comment.
  sorry

/-- **Three arms from the single branch vertex + the reciprocal equality (piece (b) of Ẽ₆/Ẽ₇/Ẽ₈).**
From a connected acyclic affine Dynkin diagram with all degrees `≤ 3` and a *unique* branch
(degree-3) vertex `v`, extract the three arms of lengths `1 ≤ p ≤ q ≤ r` emanating from `v`, laid
out along a re-indexing `σ` in the `armAdjIdx` pattern (hub at index `p`), with `n = 1 + p + q + r`.
Testing the (degenerate) Cartan form against its strictly-positive null vector
(`affineNullVector_pos`) — which is linear along each arm — pins the reciprocal sum to `1` on the
nose, giving the cleared-denominator equality
`(q+1)(r+1) + (p+1)(r+1) + (p+1)(q+1) = (p+1)(q+1)(r+1)`.

The arm-length triple is then classified by `affine_arm_length_solutions` and reindexed onto
`Ẽ₆/Ẽ₇/Ẽ₈` in `affine_tree_one_branch_iso` (piece (c)). -/
lemma affine_tree_one_arm_reciprocal {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj)
    (hacyc : (∑ i, ∑ j, adj i j) < 2 * (n : ℤ))
    (hdeg3 : ∀ v, Etingof.Problem6_1_3_E7E8.vertexDegree adj v ≤ 3)
    (v : Fin n) (hv : Etingof.Problem6_1_3_E7E8.vertexDegree adj v = 3)
    (huniq : ∀ w, Etingof.Problem6_1_3_E7E8.vertexDegree adj w = 3 → w = v) :
    ∃ (p q r : ℕ) (σ : Fin n ≃ Fin n),
      1 ≤ p ∧ p ≤ q ∧ q ≤ r ∧ n = 1 + p + q + r ∧
      (q + 1) * (r + 1) + (p + 1) * (r + 1) + (p + 1) * (q + 1)
          = (p + 1) * (q + 1) * (r + 1) ∧
      (σ.symm v).val = p ∧
      (∀ i j, adj (σ i) (σ j) = 1 ↔ armAdjIdx p q r i.val j.val) := by
  classical
  -- Strictly-positive null vector of the (degenerate) Cartan form.
  obtain ⟨w, hw_pos, hw_ker⟩ := affineNullVector_pos adj hn hD
  -- **Arm layout** (structural extraction): the three arms laid out along `σ`.
  obtain ⟨p, q, r, σ, hp, hpq, hqr, hn_eq, hhub, hadj_iff⟩ :=
    affine_one_branch_arm_layout adj hn hD hacyc hdeg3 v hv huniq
  refine ⟨p, q, r, σ, hp, hpq, hqr, hn_eq, ?_, hhub, hadj_iff⟩
  -- === Reciprocal equality from harmonicity of the positive null vector ===
  have h01 := hD.2.2.1
  -- Full adjacency in the arm layout.
  have hadj_val : ∀ i j : Fin n,
      adj (σ i) (σ j) = if armAdjIdx p q r i.val j.val then 1 else 0 := by
    intro i j
    by_cases h : armAdjIdx p q r i.val j.val
    · rw [if_pos h]; exact (hadj_iff i j).mpr h
    · rw [if_neg h]
      rcases h01 (σ i) (σ j) with h0 | h1
      · exact h0
      · exact absurd ((hadj_iff i j).mp h1) h
  -- The null-vector row (harmonic) equation `2 wₓ = ∑ⱼ adjₓⱼ wⱼ`.
  have hker : ∀ x : Fin n, 2 * w x = ∑ j, adj x j * w j := by
    intro x
    have hx := congrFun hw_ker x
    simp only [Pi.zero_apply] at hx
    have hMij : ∀ j, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) x j
        = (if x = j then (2:ℤ) else 0) - adj x j := by
      intro j
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, nsmul_eq_mul]
      split_ifs <;> norm_num
    have hrow_eq : ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec w) x
        = ∑ j, ((if x = j then (2:ℤ) else 0) - adj x j) * w j := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl (fun j _ => by rw [hMij j])
    rw [hrow_eq] at hx
    have hsplit : ∑ j, ((if x = j then (2:ℤ) else 0) - adj x j) * w j
        = (∑ j, (if x = j then (2:ℤ) else 0) * w j) - ∑ j, adj x j * w j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hdiagsum : ∑ j, (if x = j then (2:ℤ) else 0) * w j = 2 * w x := by
      rw [Finset.sum_eq_single x]
      · rw [if_pos rfl]
      · intro b _ hb; rw [if_neg (fun h => hb h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ x) h
    rw [hsplit, hdiagsum] at hx
    linarith [hx]
  -- Reindexed harmonic equation along `σ`, in terms of the `armAdjIdx` neighbour pattern.
  have hlap : ∀ m : Fin n,
      2 * w (σ m) = ∑ j, (if armAdjIdx p q r m.val j.val then w (σ j) else 0) := by
    intro m
    have h := hker (σ m)
    rw [← Equiv.sum_comp σ (fun j => adj (σ m) j * w j)] at h
    rw [h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hadj_val m j]
    split_ifs with hh <;> simp
  -- Null vector as a function of the (natural-number) arm index.
  set wσ : ℕ → ℤ := fun t => if h : t < n then w (σ ⟨t, h⟩) else 0 with hwσ_def
  have hwσ : ∀ t (h : t < n), wσ t = w (σ ⟨t, h⟩) := by
    intro t h; simp only [hwσ_def]; rw [dif_pos h]
  -- Neighbour-sum reduction: a vertex's harmonic sum equals the sum over its explicit neighbours.
  have hlap' : ∀ (m : ℕ) (hm : m < n) (S : Finset (Fin n)),
      (∀ j : Fin n, armAdjIdx p q r m j.val ↔ j ∈ S) →
      2 * wσ m = ∑ j ∈ S, w (σ j) := by
    intro m hm S hS
    rw [hwσ m hm, hlap ⟨m, hm⟩, ← Finset.sum_filter]
    congr 1
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hS j
  have hlap_one : ∀ (m a : ℕ), m < n → (ha : a < n) →
      (∀ J, J < n → (armAdjIdx p q r m J ↔ J = a)) → 2 * wσ m = wσ a := by
    intro m a hm ha hiff
    have hS : ∀ j : Fin n, armAdjIdx p q r m j.val ↔ j ∈ ({⟨a, ha⟩} : Finset (Fin n)) := by
      intro j; rw [Finset.mem_singleton, Fin.ext_iff]; exact hiff j.val j.isLt
    have hsum := hlap' m hm _ hS
    rw [Finset.sum_singleton] at hsum
    rw [hsum, hwσ a ha]
  have hlap_two : ∀ (m a b : ℕ), m < n → (ha : a < n) → (hb : b < n) → a ≠ b →
      (∀ J, J < n → (armAdjIdx p q r m J ↔ J = a ∨ J = b)) →
      2 * wσ m = wσ a + wσ b := by
    intro m a b hm ha hb hab hiff
    have hS : ∀ j : Fin n, armAdjIdx p q r m j.val
        ↔ j ∈ ({⟨a, ha⟩, ⟨b, hb⟩} : Finset (Fin n)) := by
      intro j; simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      exact hiff j.val j.isLt
    have hsum := hlap' m hm _ hS
    rw [Finset.sum_insert (by simp only [Finset.mem_singleton, Fin.ext_iff]; exact hab),
        Finset.sum_singleton] at hsum
    rw [hwσ a ha, hwσ b hb]; exact hsum
  have hlap_three : ∀ (m a b c : ℕ), m < n → (ha : a < n) → (hb : b < n) → (hc : c < n) →
      a ≠ b → a ≠ c → b ≠ c →
      (∀ J, J < n → (armAdjIdx p q r m J ↔ J = a ∨ J = b ∨ J = c)) →
      2 * wσ m = wσ a + wσ b + wσ c := by
    intro m a b c hm ha hb hc hab hac hbc hiff
    have hS : ∀ j : Fin n, armAdjIdx p q r m j.val
        ↔ j ∈ ({⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩} : Finset (Fin n)) := by
      intro j; simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      exact hiff j.val j.isLt
    have hsum := hlap' m hm _ hS
    rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; omega),
        Finset.sum_insert (by simp only [Finset.mem_singleton, Fin.ext_iff]; omega),
        Finset.sum_singleton] at hsum
    rw [hwσ a ha, hwσ b hb, hwσ c hc]; linarith [hsum]
  -- The hub is at index `p`, with value `W = w v`.
  have hplt : p < n := by omega
  have hhub_eq : σ ⟨p, hplt⟩ = v := by
    rw [show (⟨p, hplt⟩ : Fin n) = σ.symm v from Fin.ext hhub.symm, Equiv.apply_symm_apply]
  have hWp : wσ p = w v := by rw [hwσ p hplt, hhub_eq]
  -- === Arm P (indices 0 … p, tip → hub): linearity of `wσ`. ===
  have hleafP : 2 * wσ 0 = wσ 1 :=
    hlap_one 0 1 (by omega) (by omega) (fun J hJ => by simp only [armAdjIdx]; omega)
  have hlinP := arm_linear wσ p hleafP (fun i hi1 hip =>
    hlap_two i (i - 1) (i + 1) (by omega) (by omega) (by omega) (by omega)
      (fun J hJ => by simp only [armAdjIdx]; omega))
  have hpa : w v = ((p : ℤ) + 1) * wσ 0 := by
    have h := hlinP p (le_refl p); rw [hWp] at h; exact h
  have hPnbr : wσ (p - 1) = (p : ℤ) * wσ 0 := by
    rw [hlinP (p - 1) (by omega)]; congr 1; omega
  -- === Arm Q (indices p … p+q via `p+q-j`, tip → hub): linearity. ===
  have hleafQ : 2 * wσ (p + q) = wσ (p + q - 1) :=
    hlap_one (p + q) (p + q - 1) (by omega) (by omega) (fun J hJ => by simp only [armAdjIdx]; omega)
  have hlinQ := arm_linear (fun j => wσ (p + q - j)) q (by simpa using hleafQ)
    (fun i hi1 hiq => by
      show 2 * wσ (p + q - i) = wσ (p + q - (i - 1)) + wσ (p + q - (i + 1))
      rw [show p + q - (i - 1) = (p + q - i) + 1 from by omega,
          show p + q - (i + 1) = (p + q - i) - 1 from by omega]
      exact hlap_two (p + q - i) ((p + q - i) + 1) ((p + q - i) - 1)
        (by omega) (by omega) (by omega) (by omega)
        (fun J hJ => by simp only [armAdjIdx]; omega))
  have hqb : w v = ((q : ℤ) + 1) * wσ (p + q) := by
    have h := hlinQ q (le_refl q)
    rw [show p + q - q = p from by omega, Nat.sub_zero, hWp] at h
    exact h
  have hQnbr : wσ (p + 1) = (q : ℤ) * wσ (p + q) := by
    have h := hlinQ (q - 1) (by omega)
    rw [show p + q - (q - 1) = p + 1 from by omega, Nat.sub_zero] at h
    rw [h]; congr 1; omega
  -- === Arm R (indices p+q+1 … p+q+r, tip → hub-neighbour; hub plugged as `wσ p`): linearity. ===
  have hlinR := arm_linear (fun j => if j < r then wσ (p + q + r - j) else wσ p) r
    (by
      show 2 * (if (0 : ℕ) < r then wσ (p + q + r - 0) else wσ p)
         = (if (1 : ℕ) < r then wσ (p + q + r - 1) else wσ p)
      rw [if_pos (show (0 : ℕ) < r by omega), Nat.sub_zero]
      by_cases hr1 : 1 < r
      · rw [if_pos hr1]
        exact hlap_one (p + q + r) (p + q + r - 1) (by omega) (by omega)
          (fun J hJ => by simp only [armAdjIdx]; omega)
      · rw [if_neg hr1]
        exact hlap_one (p + q + r) p (by omega) (by omega)
          (fun J hJ => by simp only [armAdjIdx]; omega))
    (by
      intro i hi1 hir
      show 2 * (if i < r then wσ (p + q + r - i) else wσ p)
         = (if i - 1 < r then wσ (p + q + r - (i - 1)) else wσ p)
         + (if i + 1 < r then wσ (p + q + r - (i + 1)) else wσ p)
      rw [if_pos (show i < r by omega), if_pos (show i - 1 < r by omega),
          show p + q + r - (i - 1) = (p + q + r - i) + 1 from by omega]
      by_cases hir2 : i + 1 < r
      · rw [if_pos hir2, show p + q + r - (i + 1) = (p + q + r - i) - 1 from by omega]
        exact hlap_two (p + q + r - i) ((p + q + r - i) + 1) ((p + q + r - i) - 1)
          (by omega) (by omega) (by omega) (by omega)
          (fun J hJ => by simp only [armAdjIdx]; omega)
      · rw [if_neg hir2, show p + q + r - i = p + q + 1 from by omega]
        exact hlap_two (p + q + 1) ((p + q + 1) + 1) p
          (by omega) (by omega) (by omega) (by omega)
          (fun J hJ => by unfold armAdjIdx; omega))
  have hrc : w v = ((r : ℤ) + 1) * wσ (p + q + r) := by
    have h := hlinR r (le_refl r)
    rw [if_neg (show ¬ r < r by omega), if_pos (show (0 : ℕ) < r by omega), Nat.sub_zero, hWp] at h
    exact h
  have hRnbr : wσ (p + q + 1) = (r : ℤ) * wσ (p + q + r) := by
    have h := hlinR (r - 1) (by omega)
    rw [if_pos (show r - 1 < r by omega), if_pos (show (0 : ℕ) < r by omega), Nat.sub_zero,
        show p + q + r - (r - 1) = p + q + 1 from by omega] at h
    rw [h]; congr 1; omega
  -- === Hub harmonicity: the three tip values sum to `W`. ===
  have hHub0 : 2 * wσ p = wσ (p - 1) + wσ (p + 1) + wσ (p + q + 1) :=
    hlap_three p (p - 1) (p + 1) (p + q + 1) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (fun J hJ => by unfold armAdjIdx; omega)
  have e1 : (p : ℤ) * wσ 0 = w v - wσ 0 := by rw [hpa]; ring
  have e2 : (q : ℤ) * wσ (p + q) = w v - wσ (p + q) := by rw [hqb]; ring
  have e3 : (r : ℤ) * wσ (p + q + r) = w v - wσ (p + q + r) := by rw [hrc]; ring
  have hsum : wσ 0 + wσ (p + q) + wσ (p + q + r) = w v := by
    have hH := hHub0
    rw [hWp] at hH
    rw [hPnbr, hQnbr, hRnbr, e1, e2, e3] at hH
    linarith [hH]
  exact reciprocal_of_arm_data p q r (w v) (wσ 0) (wσ (p + q)) (wσ (p + q + r))
    (hw_pos v) hpa hqb hrc hsum

/-- **One branch vertex ⟹ Ẽ₆/Ẽ₇/Ẽ₈.** A connected acyclic affine Dynkin diagram with all degrees
`≤ 3` and exactly one branch (degree-3) vertex is graph-isomorphic to `AffineType.E6tilde`,
`E7tilde`, or `E8tilde`. The three arms have lengths solving the affine Diophantine identity
`1/(p+1) + 1/(q+1) + 1/(r+1) = 1` (the solutions are enumerated in `affine_arm_length_solutions`).
Affine analogue of the finite `branch_classification`. -/
lemma affine_tree_one_branch_iso {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj)
    (hacyc : (∑ i, ∑ j, adj i j) < 2 * (n : ℤ))
    (hdeg3 : ∀ v, Etingof.Problem6_1_3_E7E8.vertexDegree adj v ≤ 3)
    (v : Fin n) (hv : Etingof.Problem6_1_3_E7E8.vertexDegree adj v = 3)
    (huniq : ∀ w, Etingof.Problem6_1_3_E7E8.vertexDegree adj w = 3 → w = v) :
    ∃ t : AffineType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  -- Sub-issue: arm-length Diophantine `1/(p+1)+1/(q+1)+1/(r+1) = 1` (equality analogue of
  -- `arm_length_solutions`) + arm reindexing onto `AffineType.E6tilde/E7tilde/E8tilde`.
  sorry

/-- **(g), tree case, degree-`≤ 3` core.** A connected acyclic affine Dynkin diagram in which every
vertex has degree `≤ 3` is graph-isomorphic to one of `D̃ₙ (n ≥ 5)`, `Ẽ₆`, `Ẽ₇`, `Ẽ₈`.

Dispatches on the branch count (`affine_tree_branch_count`): one branch vertex gives an exceptional
`Ẽ` type (`affine_tree_one_branch_iso`), two give `D̃ₙ` (`affine_tree_two_branch_iso`). -/
lemma affine_tree_degree_le_three_iso {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj)
    (hacyc : (∑ i, ∑ j, adj i j) < 2 * (n : ℤ))
    (hdeg3 : ∀ v, Etingof.Problem6_1_3_E7E8.vertexDegree adj v ≤ 3) :
    ∃ t : AffineType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  rcases affine_tree_branch_count adj hn hD hacyc hdeg3 with
    ⟨v, hv, huniq⟩ | ⟨v, w, hvw, hv, hw, huniq⟩
  · exact affine_tree_one_branch_iso adj hn hD hacyc hdeg3 v hv huniq
  · exact affine_tree_two_branch_iso adj hn hD hacyc hdeg3 v w hvw hv hw huniq

/-- **(g), tree case.** A connected *acyclic* affine Dynkin diagram on `Fin n` is
graph-isomorphic to one of `D̃ₙ (n ≥ 4)`, `Ẽ₆`, `Ẽ₇`, `Ẽ₈`. Acyclicity is expressed
via the edge-sum bound `∑ᵢ∑ⱼ adjᵢⱼ < 2n`, complementary to the cyclic case
`affine_cyclic_case` (`2n ≤ ∑ᵢ∑ⱼ adjᵢⱼ`).

The proof is a case split on the degree-4 dichotomy
(`affine_degree_four_dichotomy`): a degree-4 vertex forces `D̃₄` directly (`D̃₄` is
`D̃ₙ` at `n = 4`); otherwise every vertex has degree `≤ 3` and
`affine_tree_degree_le_three_iso` classifies the diagram as `D̃ₙ/Ẽ₆/Ẽ₇/Ẽ₈`.

This is the tree branch of the ⟹ direction of `affine_dynkin_classification`,
consumed by the final assembly (#6785 step 5). -/
lemma affine_tree_case {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hD : IsAffineDynkinDiagram n adj)
    (hacyc : (∑ i, ∑ j, adj i j) < 2 * (n : ℤ)) :
    ∃ t : AffineType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  rcases affine_degree_four_dichotomy adj hn hD with ⟨σ, hσ⟩ | hdeg3
  · -- Degree-4 vertex: the dichotomy hands us a `D̃₄` isomorphism directly.
    exact ⟨_, σ, hσ⟩
  · -- All degrees `≤ 3`: the arm-length core classifies the tree.
    exact affine_tree_degree_le_three_iso adj hn hD hacyc hdeg3

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
    -- extended types. Case split on whether the diagram contains a cycle,
    -- measured by the edge count `∑ᵢ∑ⱼ adjᵢⱼ`: a connected graph is a tree
    -- (acyclic) exactly when it has `n − 1` edges (`∑ᵢ∑ⱼ adjᵢⱼ = 2(n−1)`),
    -- so `2n ≤ ∑ᵢ∑ⱼ adjᵢⱼ` is the "contains a cycle" branch.
    intro hD
    rcases le_or_gt (2 * (n : ℤ)) (∑ i, ∑ j, adj i j) with hcyc | hacyc
    · -- Cyclic branch: graph-iso to the cycle `Ãₙ` (#6792).
      obtain ⟨h3, σ, hσ⟩ := affine_cyclic_case adj hn hD hcyc
      exact ⟨AffineType.Atilde n h3, σ, hσ⟩
    · -- Tree branch: graph-iso to `D̃ₙ/Ẽ₆/Ẽ₇/Ẽ₈` (#6793).
      exact affine_tree_case adj hn hD hacyc
  · -- (⟸) Each extended type is an affine Dynkin diagram (`isAffineDynkinDiagram_of_type`),
    -- transported along the graph isomorphism `σ`.
    rintro ⟨t, σ, hσ⟩
    exact isAffineDynkinDiagram_of_graph_iso σ hσ (isAffineDynkinDiagram_of_type t)

end Etingof.Problem6_1_3_tildeE
