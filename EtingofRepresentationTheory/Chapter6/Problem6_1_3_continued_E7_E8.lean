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

/-! ## Part (a): determinants of `Aₙ` and `Dₙ`, and they are Dynkin diagrams

The book strategy for `Aₙ` is "row decomposition + recursive equation". Concretely,
the `Aₙ` Cartan matrix is the tridiagonal `(2, -1)` matrix, and expanding the cofactor
along the first row (twice) gives the classical continuant recursion
`det(Aₙ₊₂) = 2·det(Aₙ₊₁) − det(Aₙ)`, whose solution with `det(A₁) = 2`, `det(A₂) = 3`
is `det(Aₙ) = n + 1`. For `Dₙ`, peeling the pendant fork vertex reduces to `Aₖ`
determinants and yields the constant `4`.

To run the induction without the `1 ≤ n` proof obligation cluttering the index
arithmetic, we work with a bare tridiagonal matrix `pathCartan n` (defined for every
`n`) and only relate it back to the `DynkinType.A` Cartan matrix at the very end.
-/

/-- The bare `Aₙ` Cartan matrix: the tridiagonal matrix with `2` on the diagonal and
`-1` on the two off-diagonals, defined for every `n` with no `DynkinType` wrapper. -/
private def pathCartan (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i.val = j.val then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

/-- Diagonal entry of `pathCartan`. -/
private lemma pathCartan_diag {n : ℕ} {i j : Fin n} (h : i.val = j.val) :
    pathCartan n i j = 2 := by simp only [pathCartan, if_pos h]

/-- Off-diagonal (adjacent) entry of `pathCartan`. -/
private lemma pathCartan_offdiag {n : ℕ} {i j : Fin n}
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) : pathCartan n i j = -1 := by
  have hne : ¬ (i.val = j.val) := by omega
  simp only [pathCartan, if_neg hne, if_pos h]

/-- Distant (non-adjacent, off-diagonal) entry of `pathCartan`. -/
private lemma pathCartan_far {n : ℕ} {i j : Fin n} (h1 : ¬ (i.val = j.val))
    (h2 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) : pathCartan n i j = 0 := by
  simp only [pathCartan, if_neg h1, if_neg h2]

/-- The `DynkinType.A` Cartan matrix is exactly the bare tridiagonal `pathCartan`. -/
private lemma cartan_A_eq_pathCartan (n : ℕ) (hn : 1 ≤ n) :
    cartan (DynkinType.A n hn) = pathCartan n := by
  ext i j
  simp only [cartan, pathCartan, DynkinType.adj, Matrix.sub_apply, two_nsmul,
    Matrix.add_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- Deleting the first row and column of `pathCartan (m+1)` returns `pathCartan m`:
the tridiagonal structure only depends on index differences. -/
private lemma pathCartan_submatrix_succ (m : ℕ) :
    (pathCartan (m + 1)).submatrix Fin.succ Fin.succ = pathCartan m := by
  ext i j
  simp only [pathCartan, Matrix.submatrix_apply, Fin.val_succ]
  split_ifs <;> omega

/-- The second cofactor (the `j = 1` term of the row-`0` expansion): its column `0`
has a single nonzero entry `-1`, and peeling it off leaves `pathCartan n`, so the
minor's determinant is `-det(pathCartan n)`. -/
private lemma det_pathCartan_minor_one (n : ℕ) :
    ((pathCartan (n + 2)).submatrix Fin.succ (Fin.succ (0 : Fin (n + 1))).succAbove).det
      = -(pathCartan n).det := by
  have hz : ∀ i : Fin n,
      ((pathCartan (n + 2)).submatrix Fin.succ (Fin.succ (0 : Fin (n + 1))).succAbove)
        (Fin.succ i) 0 = 0 := by
    intro i
    rw [Matrix.submatrix_apply, Fin.succ_succAbove_zero]
    exact pathCartan_far (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (by simp only [Fin.val_succ, Fin.val_zero]; omega)
  have e0 : ((pathCartan (n + 2)).submatrix Fin.succ (Fin.succ (0 : Fin (n + 1))).succAbove)
      0 0 = -1 := by
    rw [Matrix.submatrix_apply, Fin.succ_succAbove_zero]
    exact pathCartan_offdiag (Or.inr (by simp only [Fin.val_succ, Fin.val_zero]))
  have hsub : ((pathCartan (n + 2)).submatrix Fin.succ
      (Fin.succ (0 : Fin (n + 1))).succAbove).submatrix Fin.succ Fin.succ = pathCartan n := by
    ext i j
    simp only [Matrix.submatrix_apply, Fin.succ_succAbove_succ, Fin.zero_succAbove, pathCartan,
      Fin.val_succ]
    split_ifs <;> omega
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, e0,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, hsub]
  ring

/-- The continuant recursion `det(pathCartan (n+2)) = 2·det(pathCartan (n+1)) −
det(pathCartan n)`, obtained by expanding the determinant along the first row. -/
private lemma det_pathCartan_rec (n : ℕ) :
    (pathCartan (n + 2)).det = 2 * (pathCartan (n + 1)).det - (pathCartan n).det := by
  have hz : ∀ j : Fin n, pathCartan (n + 2) 0 (Fin.succ (Fin.succ j)) = 0 := fun j =>
    pathCartan_far (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (by simp only [Fin.val_succ, Fin.val_zero]; omega)
  have e0 : pathCartan (n + 2) 0 0 = 2 := pathCartan_diag rfl
  have e1 : pathCartan (n + 2) 0 (Fin.succ 0) = -1 :=
    pathCartan_offdiag (Or.inl (by simp only [Fin.val_succ, Fin.val_zero]))
  have hs0 : (pathCartan (n + 2)).submatrix Fin.succ (0 : Fin (n + 2)).succAbove
      = pathCartan (n + 1) := by
    rw [Fin.succAbove_zero]; exact pathCartan_submatrix_succ (n + 1)
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, e0, e1, hs0,
    det_pathCartan_minor_one, Fin.val_zero, Fin.val_succ, zero_add, pow_zero, one_mul]
  ring

/-- The determinant of the bare tridiagonal `pathCartan n` is `n + 1`, by the
two-step continuant recursion. -/
private lemma det_pathCartan : ∀ n : ℕ, (pathCartan n).det = (n : ℤ) + 1
  | 0 => by simp
  | 1 => by rw [Matrix.det_fin_one]; norm_num [pathCartan]
  | (n + 2) => by
      rw [det_pathCartan_rec, det_pathCartan (n + 1), det_pathCartan n]
      push_cast; ring

/-- **(a)** `det A = n + 1` for the path graph `Aₙ`. -/
theorem det_cartan_A (n : ℕ) (hn : 1 ≤ n) :
    (cartan (DynkinType.A n hn)).det = (n : ℤ) + 1 := by
  rw [cartan_A_eq_pathCartan n hn, det_pathCartan n]

/-! ### `Dₙ`: the same leaf-peeling recursion, but reducing to the constant `4`

Vertex `0` of `Dₙ` is a leaf attached to vertex `1` (the fork is at the far end),
so its row is again `(2, -1, 0, …, 0)` and the identical double-cofactor argument
gives `det(Dₙ) = 2·det(Dₙ₋₁) − det(Dₙ₋₂)`. With base cases `det(D₄) = det(D₅) = 4`
the two-step induction yields the constant `4`. As with `Aₙ`, we use a bare matrix
`dCartan n` to keep the `4 ≤ n` obligation out of the index arithmetic. -/

/-- The bare `Dₙ` Cartan matrix: the path `0—1—⋯—(n-2)` with the fork edge
`(n-3)—(n-1)`, `2` on the diagonal and `-1` on edges, defined for every `n`. -/
private def dCartan (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i.val = j.val then 2
    else if (i.val + 1 = j.val ∧ j.val ≤ n - 2) ∨ (j.val + 1 = i.val ∧ i.val ≤ n - 2) ∨
            (i.val = n - 3 ∧ j.val = n - 1) ∨ (j.val = n - 3 ∧ i.val = n - 1) then -1
    else 0

/-- Diagonal entry of `dCartan`. -/
private lemma dCartan_diag {n : ℕ} {i j : Fin n} (h : i.val = j.val) :
    dCartan n i j = 2 := by simp only [dCartan, if_pos h]

/-- Edge entry of `dCartan`. -/
private lemma dCartan_offdiag {n : ℕ} {i j : Fin n} (hne : i.val ≠ j.val)
    (h : (i.val + 1 = j.val ∧ j.val ≤ n - 2) ∨ (j.val + 1 = i.val ∧ i.val ≤ n - 2) ∨
         (i.val = n - 3 ∧ j.val = n - 1) ∨ (j.val = n - 3 ∧ i.val = n - 1)) :
    dCartan n i j = -1 := by simp only [dCartan, if_neg hne, if_pos h]

/-- Non-edge, off-diagonal entry of `dCartan`. -/
private lemma dCartan_far {n : ℕ} {i j : Fin n} (hne : i.val ≠ j.val)
    (h : ¬ ((i.val + 1 = j.val ∧ j.val ≤ n - 2) ∨ (j.val + 1 = i.val ∧ i.val ≤ n - 2) ∨
         (i.val = n - 3 ∧ j.val = n - 1) ∨ (j.val = n - 3 ∧ i.val = n - 1))) :
    dCartan n i j = 0 := by simp only [dCartan, if_neg hne, if_neg h]

/-- The `DynkinType.D` Cartan matrix is exactly the bare `dCartan`. -/
private lemma cartan_D_eq_dCartan (n : ℕ) (hn : 4 ≤ n) :
    cartan (DynkinType.D n hn) = dCartan n := by
  ext i j
  simp only [cartan, dCartan, DynkinType.adj, Matrix.sub_apply, two_nsmul,
    Matrix.add_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- Base case `det(D₄) = 4`. -/
private lemma det_dCartan_four : (dCartan 4).det = 4 := by
  have hC : dCartan 4 = !![2,-1,0,0; -1,2,-1,-1; 0,-1,2,0; 0,-1,0,2] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  rw [hC]; cartan_det

/-- Base case `det(D₅) = 4`. -/
private lemma det_dCartan_five : (dCartan 5).det = 4 := by
  have hC : dCartan 5 = !![2,-1,0,0,0; -1,2,-1,0,0; 0,-1,2,-1,-1; 0,0,-1,2,0; 0,0,-1,0,2] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  rw [hC]; cartan_det

/-- Deleting the first row and column of `dCartan (m+5)` returns `dCartan (m+4)`:
vertex `0` is a leaf, and peeling it shifts the fork position consistently. -/
private lemma dCartan_submatrix_succ (m : ℕ) :
    (dCartan (m + 5)).submatrix Fin.succ Fin.succ = dCartan (m + 4) := by
  ext i j
  simp only [dCartan, Matrix.submatrix_apply, Fin.val_succ]
  split_ifs <;> omega

/-- The second cofactor of the row-`0` expansion of `dCartan (m+6)`: its column `0`
has a single nonzero entry `-1`, and peeling it leaves `dCartan (m+4)`. -/
private lemma det_dCartan_minor_one (m : ℕ) :
    ((dCartan (m + 6)).submatrix Fin.succ (Fin.succ (0 : Fin (m + 5))).succAbove).det
      = -(dCartan (m + 4)).det := by
  have hz : ∀ i : Fin (m + 4),
      ((dCartan (m + 6)).submatrix Fin.succ (Fin.succ (0 : Fin (m + 5))).succAbove)
        (Fin.succ i) 0 = 0 := by
    intro i
    rw [Matrix.submatrix_apply, Fin.succ_succAbove_zero]
    exact dCartan_far (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (by simp only [Fin.val_succ, Fin.val_zero]; omega)
  have e0 : ((dCartan (m + 6)).submatrix Fin.succ (Fin.succ (0 : Fin (m + 5))).succAbove)
      0 0 = -1 := by
    rw [Matrix.submatrix_apply, Fin.succ_succAbove_zero]
    exact dCartan_offdiag (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (Or.inr (Or.inl ⟨by simp only [Fin.val_succ, Fin.val_zero],
        by simp only [Fin.val_succ, Fin.val_zero]; omega⟩))
  have hsub : ((dCartan (m + 6)).submatrix Fin.succ
      (Fin.succ (0 : Fin (m + 5))).succAbove).submatrix Fin.succ Fin.succ = dCartan (m + 4) := by
    ext i j
    simp only [Matrix.submatrix_apply, Fin.succ_succAbove_succ, Fin.zero_succAbove, dCartan,
      Fin.val_succ]
    split_ifs <;> omega
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, e0,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, hsub]
  ring

/-- The `Dₙ` continuant recursion. -/
private lemma det_dCartan_rec (m : ℕ) :
    (dCartan (m + 6)).det = 2 * (dCartan (m + 5)).det - (dCartan (m + 4)).det := by
  have hz : ∀ j : Fin (m + 4), dCartan (m + 6) 0 (Fin.succ (Fin.succ j)) = 0 := fun j =>
    dCartan_far (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (by simp only [Fin.val_succ, Fin.val_zero]; omega)
  have e0 : dCartan (m + 6) 0 0 = 2 := dCartan_diag rfl
  have e1 : dCartan (m + 6) 0 (Fin.succ 0) = -1 :=
    dCartan_offdiag (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (Or.inl ⟨by simp only [Fin.val_succ, Fin.val_zero],
        by simp only [Fin.val_succ, Fin.val_zero]; omega⟩)
  have hs0 : (dCartan (m + 6)).submatrix Fin.succ (0 : Fin (m + 6)).succAbove
      = dCartan (m + 5) := by
    rw [Fin.succAbove_zero]; exact dCartan_submatrix_succ (m + 1)
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, e0, e1, hs0,
    det_dCartan_minor_one, Fin.val_zero, Fin.val_succ, zero_add, pow_zero, one_mul]
  ring

/-- The determinant of the bare `dCartan (m+4)` is the constant `4`. -/
private lemma det_dCartan : ∀ m : ℕ, (dCartan (m + 4)).det = 4
  | 0 => det_dCartan_four
  | 1 => det_dCartan_five
  | (m + 2) => by
      have h1 : (dCartan (m + 5)).det = 4 := det_dCartan (m + 1)
      have h2 : (dCartan (m + 4)).det = 4 := det_dCartan m
      have hrec : (dCartan (m + 2 + 4)).det
          = 2 * (dCartan (m + 5)).det - (dCartan (m + 4)).det := det_dCartan_rec m
      rw [hrec, h1, h2]; ring

/-- **(a)** `det A = 4` for `Dₙ`. -/
theorem det_cartan_D (n : ℕ) (hn : 4 ≤ n) :
    (cartan (DynkinType.D n hn)).det = 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [cartan_D_eq_dCartan (m + 4) hn, det_dCartan m]

/-- **(a)** `Aₙ` is a Dynkin diagram (its Cartan form is positive definite).
Sylvester's criterion reads the positivity off the leading principal minors,
whose values are the `det_cartan_A (= n+1)` computation; the underlying
positive-definiteness is packaged in `isDynkinDiagram_of_type`. -/
theorem isDynkinDiagram_A (n : ℕ) (hn : 1 ≤ n) :
    IsDynkinDiagram (DynkinType.A n hn).rank (DynkinType.A n hn).adj :=
  isDynkinDiagram_of_type (.A n hn)

/-- **(a)** `Dₙ` is a Dynkin diagram. Sylvester's criterion reads the positivity
off the leading principal minors (`det_cartan_D (= 4)` being the top minor); the
positive-definiteness is supplied by `isDynkinDiagram_of_type`. -/
theorem isDynkinDiagram_D (n : ℕ) (hn : 4 ≤ n) :
    IsDynkinDiagram (DynkinType.D n hn).rank (DynkinType.D n hn).adj :=
  isDynkinDiagram_of_type (.D n hn)

/-! ## Part (b): determinants of `E₆, E₇, E₈`, and they are Dynkin diagrams -/

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
