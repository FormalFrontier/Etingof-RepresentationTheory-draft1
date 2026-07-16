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
    show (m i : ℚ) * ((x i : ℚ) / (m i : ℚ)) = (x i : ℚ)
    field_simp
  -- the quadratic form as an explicit double sum
  have hq : ((dotProduct x (A.mulVec x) : ℤ) : ℚ)
      = ∑ i, ∑ j, (A i j : ℚ) * (x i) * (x j) := by
    simp only [dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    push_cast; ring
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
  · rw [List.head?_eq_head hne, hhead]
  · rw [List.getLast?_eq_getLast hne, hlast]
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
      · refine .single ?_ <;> decide
      · refine .head (b := ⟨1, by decide⟩) ?_ (.single ?_) <;> decide
      · refine .single ?_ <;> decide
      · refine .head (b := ⟨3, by decide⟩) ?_ (.single ?_) <;> decide
      · refine .single ?_ <;> decide
      · refine .head (b := ⟨5, by decide⟩) ?_ (.single ?_) <;> decide
  | E7tilde =>
      refine connected_of_reach_base (AffineType.adj_isSymm _) ⟨0, by decide⟩ ?_ i j
      intro k
      fin_cases k
      · exact .refl
      · refine .single ?_ <;> decide
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
      · refine .single ?_ <;> decide
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

/-- **(g)** **Classification of affine Dynkin diagrams.** A connected simply-laced
graph on `n ≥ 1` vertices is an affine Dynkin diagram iff it is
(graph-isomorphic to) one of `Ãₙ, D̃ₙ, Ẽ₆, Ẽ₇, Ẽ₈` — exactly the "forbidden"
extended diagrams of parts (c)–(e). -/
theorem affine_dynkin_classification (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n) :
    IsAffineDynkinDiagram n adj ↔
    ∃ t : AffineType, ∃ σ : Fin t.rank ≃ Fin n, ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  sorry

end Etingof.Problem6_1_3_tildeE
