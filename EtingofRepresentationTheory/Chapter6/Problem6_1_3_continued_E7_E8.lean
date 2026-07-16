import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.DynkinTypes
import EtingofRepresentationTheory.Chapter6.Problem6_1_3

/-!
# Problem 6.1.3 (continued): `E₇`, `E₈`, and parts (a)–(d)

> - `E₇`, `E₈`: the two remaining exceptional diagrams (a path with a branch at
>   the third vertex).
>
> **(a)** Compute the determinant of `A` where `Γ = Aₙ, Dₙ`. (Use the row
> decomposition rule, and write down a recursive equation for it.) Deduce by
> Sylvester's criterion that `Aₙ, Dₙ` are Dynkin diagrams.
>
> **(b)** Compute the determinants of `A` for `E₆, E₇, E₈` (use row decomposition
> and reduce to (a)). Show they are Dynkin diagrams.
>
> **(c)** Show that if `Γ` is a Dynkin diagram, it cannot have cycles. For this,
> show that `det(A) = 0` for the cycle graph (all vertices labeled `1`), by
> showing the sum of rows is `0`. Thus `Γ` has to be a tree.
>
> **(d)** Show that if `Γ` is a Dynkin diagram, it cannot have vertices with four
> or more incoming edges and that `Γ` can have no more than one vertex with three
> incoming edges.

Here `A = 2·Id - R` is the Cartan-type matrix of Problem 6.1.3, and
`Etingof.IsDynkinDiagram` (Definition 6.1.4) is exactly "`A` is positive
definite". The determinant values are the standard connection indices:
`det Aₙ = n+1`, `det Dₙ = 4`, `det E₆ = 3`, `det E₇ = 2`, `det E₈ = 1`.

We reuse the standard adjacency matrices `Etingof.DynkinType.adj`.
-/

namespace Etingof.Problem6_1_3_E7E8

open Matrix Finset

/-- The Cartan matrix `A = 2·Id - adj(t)` of a standard Dynkin type `t`. -/
def cartan (t : DynkinType) : Matrix (Fin t.rank) (Fin t.rank) ℤ :=
  2 • (1 : Matrix (Fin t.rank) (Fin t.rank) ℤ) - t.adj

/-- The degree (number of incident edges) of vertex `v` in the graph with
adjacency matrix `adj`. -/
def vertexDegree {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) : ℕ :=
  (univ.filter (fun j => adj v j = 1)).card

/-! ## Part (a): determinants of `Aₙ` and `Dₙ`, and they are Dynkin diagrams -/

/-- **(a)** `det A = n + 1` for the path graph `Aₙ`. -/
theorem det_cartan_A (n : ℕ) (hn : 1 ≤ n) :
    (cartan (DynkinType.A n hn)).det = (n : ℤ) + 1 := by
  sorry

/-- **(a)** `det A = 4` for `Dₙ`. -/
theorem det_cartan_D (n : ℕ) (hn : 4 ≤ n) :
    (cartan (DynkinType.D n hn)).det = 4 := by
  sorry

/-- **(a)** `Aₙ` is a Dynkin diagram (its Cartan form is positive definite),
deduced from `det > 0` of all leading minors via Sylvester's criterion. -/
theorem isDynkinDiagram_A (n : ℕ) (hn : 1 ≤ n) :
    IsDynkinDiagram (DynkinType.A n hn).rank (DynkinType.A n hn).adj := by
  sorry

/-- **(a)** `Dₙ` is a Dynkin diagram. -/
theorem isDynkinDiagram_D (n : ℕ) (hn : 4 ≤ n) :
    IsDynkinDiagram (DynkinType.D n hn).rank (DynkinType.D n hn).adj := by
  sorry

/-! ## Part (b): determinants of `E₆, E₇, E₈`, and they are Dynkin diagrams -/

/-- The two-stage tactic for an explicit sparse Cartan determinant. Stage 1
expands the cofactor recursion (`det_succ_row_zero`) while keeping index
arithmetic in symbolic `0`/`.succ` form via `succ_succAbove_succ`, so that the
`0 * _` factors of zero entries prune the expansion before it reaches `n!`
terms. Stage 2 (`norm_num` with `Fin.succAbove`/`Fin.lt_def`) evaluates the
small residual `succAbove` indices numerically and finishes the arithmetic. -/
macro "cartan_det" : tactic =>
  `(tactic|
    (simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.zero_succAbove,
        Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, Fin.val_zero, Fin.val_succ,
        Matrix.cons_val_succ, Matrix.head_cons, Matrix.head_fin_const, mul_zero, zero_mul,
        add_zero, zero_add, neg_zero, mul_neg, neg_neg, mul_one, one_mul, pow_zero, pow_succ]
     <;>
     norm_num [Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.head_fin_const, Matrix.vecHead,
        Matrix.vecTail]))

/-- **(b)** `det A = 3` for `E₆`. -/
theorem det_cartan_E6 : (cartan DynkinType.E6).det = 3 := by
  have hC : cartan DynkinType.E6 =
      !![2,-1,0,0,0,0; -1,2,-1,0,0,0; 0,-1,2,-1,0,-1;
         0,0,-1,2,-1,0; 0,0,0,-1,2,0; 0,0,-1,0,0,2] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  rw [hC]; cartan_det

/-- **(b)** `det A = 2` for `E₇`. -/
theorem det_cartan_E7 : (cartan DynkinType.E7).det = 2 := by
  have hC : cartan DynkinType.E7 =
      !![2,-1,0,0,0,0,0; -1,2,-1,0,0,0,0; 0,-1,2,-1,0,0,-1;
         0,0,-1,2,-1,0,0; 0,0,0,-1,2,-1,0; 0,0,0,0,-1,2,0;
         0,0,-1,0,0,0,2] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  rw [hC]; cartan_det

/-- **(b)** `det A = 1` for `E₈`. -/
theorem det_cartan_E8 : (cartan DynkinType.E8).det = 1 := by
  have hC : cartan DynkinType.E8 =
      !![2,-1,0,0,0,0,0,0; -1,2,-1,0,0,0,0,0; 0,-1,2,-1,0,0,0,-1;
         0,0,-1,2,-1,0,0,0; 0,0,0,-1,2,-1,0,0; 0,0,0,0,-1,2,-1,0;
         0,0,0,0,0,-1,2,0; 0,0,-1,0,0,0,0,2] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  rw [hC]; cartan_det

/-- **(b)** `E₆, E₇, E₈` are Dynkin diagrams. -/
theorem isDynkinDiagram_E :
    IsDynkinDiagram DynkinType.E6.rank DynkinType.E6.adj ∧
    IsDynkinDiagram DynkinType.E7.rank DynkinType.E7.adj ∧
    IsDynkinDiagram DynkinType.E8.rank DynkinType.E8.adj :=
  ⟨isDynkinDiagram_of_type .E6, isDynkinDiagram_of_type .E7, isDynkinDiagram_of_type .E8⟩

/-! ## Part (c): a Dynkin diagram is a tree (no cycles) -/

/-- The adjacency matrix of the `n`-cycle `Ãₙ₋₁`: vertex `i` is joined to
`i ± 1 (mod n)`. -/
def cycleAdj (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then 1 else 0

/-- **(c)** The all-ones vector lies in the kernel of the cycle's Cartan matrix:
each row of `2·Id - R` sums to `0` because every vertex of a cycle has degree `2`
("the sum of rows is `0`"). -/
theorem cycle_cartan_mulVec_one_eq_zero (n : ℕ) (hn : 3 ≤ n) :
    (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - cycleAdj n).mulVec (fun _ => 1) = 0 := by
  have hn0 : 0 < n := by omega
  funext i
  -- Every vertex of the `n`-cycle has exactly two neighbours (`i+1` and `i-1`,
  -- distinct for `n ≥ 3`), so its degree — the row sum of `R` — is `2`.
  have hdeg : ∑ j : Fin n, cycleAdj n i j = (2 : ℤ) := by
    -- `omega` cannot reason about `% n` for a variable modulus, so first rewrite
    -- each `(m+1) % n` (with `m < n`) into the elementary `if`-branch form.
    have hmod : ∀ m : ℕ, m < n → (m + 1) % n = if m + 1 = n then 0 else m + 1 := by
      intro m hm
      by_cases h : m + 1 = n
      · rw [if_pos h, h]; exact Nat.mod_self n
      · rw [if_neg h]; exact Nat.mod_eq_of_lt (by omega)
    have hlt1 : (i.val + 1) % n < n := Nat.mod_lt _ hn0
    have hlt2 : (if i.val = 0 then n - 1 else i.val - 1) < n := by split <;> omega
    have hfil : (Finset.univ.filter
          (fun j : Fin n => (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val))
        = {(⟨(i.val + 1) % n, hlt1⟩ : Fin n),
            ⟨if i.val = 0 then n - 1 else i.val - 1, hlt2⟩} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff, Fin.val_mk]
      rw [hmod i.val i.isLt, hmod j.val j.isLt]
      split_ifs <;> omega
    have hab : (⟨(i.val + 1) % n, hlt1⟩ : Fin n)
        ≠ ⟨if i.val = 0 then n - 1 else i.val - 1, hlt2⟩ := by
      simp only [ne_eq, Fin.mk.injEq]
      rw [hmod i.val i.isLt]
      split_ifs <;> omega
    have hsum : ∑ j : Fin n, cycleAdj n i j
        = ∑ j : Fin n,
            if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then (1 : ℤ) else 0 := by
      simp only [cycleAdj]
    rw [hsum, Finset.sum_boole, hfil, Finset.card_pair hab]
    norm_num
  -- The all-ones row sum of `2·Id - R` is `2 - deg = 0`.
  have h1 : ∑ j : Fin n, (2 • (1 : Matrix (Fin n) (Fin n) ℤ)) i j = (2 : ℤ) := by
    simp [Matrix.smul_apply, Matrix.one_apply, Finset.sum_ite_eq]
  simp only [mulVec, dotProduct, mul_one, Matrix.sub_apply, Pi.zero_apply]
  rw [Finset.sum_sub_distrib, h1, hdeg]
  norm_num

/-- **(c)** Consequently the Cartan matrix of a cycle is singular: `det A = 0`,
so a cycle is never a Dynkin diagram. -/
theorem cycle_cartan_det_zero (n : ℕ) (hn : 3 ≤ n) :
    (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - cycleAdj n).det = 0 := by
  have hn0 : 0 < n := by omega
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun _ => 1, ?_, cycle_cartan_mulVec_one_eq_zero n hn⟩
  intro h
  have := congrFun h ⟨0, hn0⟩
  simp at this

/-- **(c)** A Dynkin diagram is a **tree**: being connected (part of
`IsDynkinDiagram`) and positive definite forces the number of edges to be
`n - 1` (equivalently, `Γ` has no cycle). We record the tree condition as
"the total number of ordered adjacent pairs is `2·(n-1)`". -/
theorem isDynkinDiagram_isTree {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) :
    (∑ i, ∑ j, adj i j) = 2 * ((n : ℤ) - 1) := by
  sorry

/-! ## Part (d): degree restrictions on a Dynkin diagram -/

/-- **(d)** A Dynkin diagram has no vertex with four or more incident edges. -/
theorem isDynkinDiagram_degree_le_three {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (v : Fin n) : vertexDegree adj v ≤ 3 := by
  sorry

/-- **(d)** A Dynkin diagram has at most one vertex of degree three (at most one
branch point). -/
theorem isDynkinDiagram_unique_degree_three {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (v w : Fin n)
    (hv : vertexDegree adj v = 3) (hw : vertexDegree adj w = 3) : v = w := by
  sorry

end Etingof.Problem6_1_3_E7E8
