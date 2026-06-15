import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4

/-!
# Problem 6.1.5, Step 3: orbit-dimension bound ⟹ Tits form positive definite

This file is part of the orbit-counting redirect for the Chapter 6 infinite-type
direction (directive #4777). It closes **step 3** of Etingof Problem 6.1.5:

> From `dim W(m) ≤ dim G(m)` for every dimension vector `m`, conclude that the
> Tits form `q(m) = Σ mᵢ² − Σ bᵢⱼ mᵢ mⱼ` is positive definite — i.e. the
> graph is a Dynkin diagram (Definition 6.1.4).

## The matrix quadratic form is `2·q`

`IsDynkinDiagram` (Definition 6.1.4) packages positive-definiteness as

`∀ x : Fin n → ℤ, x ≠ 0 → 0 < xᵀ (2·I − adj) x`,

a quadratic form over **ℤ**. A direct expansion (`titsBilinear_eq` below) gives

`xᵀ (2·I − adj) x = 2 · (Σ xᵢ²) − Σᵢ Σⱼ adjᵢⱼ xᵢ xⱼ`,

which is exactly `2 · q(x)` for the undirected adjacency `adj` (recall
`Σᵢⱼ adjᵢⱼ xᵢxⱼ = 2 Σ_{i<j} adjᵢⱼ xᵢxⱼ` since `adj` is symmetric with no loops).
So positive-definiteness of this matrix form is literally positivity of the Tits
form, and because the definition only quantifies over **integer** vectors, no
real-density argument is needed: steps 1–3 of the book argument suffice.

## What the orbit chain supplies

The output of S1+S2 (`dim W(m) ≤ dim G(m) − 1` for nonzero `m`, the strict bound
coming from the trivial action of the global scalars `k*`) is, in matrix terms,
positivity of `xᵀ (2·I − adj) x` on every nonzero vector with **nonnegative**
entries. The work here is the elementary step 3: extend that positivity from the
nonnegative cone to all nonzero integer vectors via the `|·|` trick, using only
`adjᵢⱼ ≥ 0`.

`titsForm_posDef_of_cone` is the load-bearing lemma; `isDynkinDiagram_of_cone`
packages it together with the graph-shape clauses into `IsDynkinDiagram`, ready
for the final wiring in S4.
-/

namespace Etingof

open Matrix Finset

variable {n : ℕ}

/-- Expand any integer matrix quadratic form `vᵀ M v` as the double sum
`Σᵢ Σⱼ Mᵢⱼ vᵢ vⱼ`. -/
theorem dotProduct_mulVec_eq_sum (M : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) :
    dotProduct v (M.mulVec v) = ∑ i, ∑ j, M i j * v i * v j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `(2·I)ᵢⱼ = 2` on the diagonal and `0` off it. -/
private theorem two_smul_one_apply (i j : Fin n) :
    (2 • (1 : Matrix (Fin n) (Fin n) ℤ)) i j = if i = j then (2 : ℤ) else 0 := by
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply_eq]
  · simp [Matrix.one_apply_ne h, h]

/-- The Tits bilinear form expanded: `xᵀ (2·I − adj) x = 2·(Σ xᵢ²) − Σᵢ Σⱼ adjᵢⱼ xᵢ xⱼ`.
This identifies the matrix form of Definition 6.1.4 with twice the Tits form, and
exposes the `dim G = Σ xᵢ²` / `dim W = ½ Σᵢⱼ adjᵢⱼ xᵢxⱼ` quantities for S4. -/
theorem titsBilinear_eq (adj : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x)
      = 2 * (∑ i, x i * x i) - ∑ i, ∑ j, adj i j * x i * x j := by
  rw [dotProduct_mulVec_eq_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- per row `i`: `Σⱼ (2·I − adj)ᵢⱼ xᵢ xⱼ = 2·xᵢ² − Σⱼ adjᵢⱼ xᵢ xⱼ`
  have hsplit : ∀ j, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j * x i * x j
      = (if i = j then (2 : ℤ) * (x i * x i) else 0) - adj i j * x i * x j := by
    intro j
    rw [Matrix.sub_apply, two_smul_one_apply, sub_mul, sub_mul]
    by_cases h : i = j
    · subst h; simp; ring
    · simp [h]
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq Finset.univ i (fun _ => (2 : ℤ) * (x i * x i))]
  simp

/-- **Step 3 of Problem 6.1.5 (core).** From positivity of the Tits matrix form
`xᵀ (2·I − adj) x` on every nonzero *nonnegative* integer vector (the output of the
orbit-dimension bound `dim W ≤ dim G − 1`), the form is positive on *every* nonzero
integer vector. Only `adjᵢⱼ ≥ 0` is used: the `|·|`-trick replaces each `x` by
`|x|`, which can only decrease the form (`adjᵢⱼ (|xᵢ||xⱼ| − xᵢxⱼ) ≥ 0`). -/
theorem titsForm_posDef_of_cone (adj : Matrix (Fin n) (Fin n) ℤ)
    (hnonneg : ∀ i j, 0 ≤ adj i j)
    (hcone : ∀ m : Fin n → ℤ, (∀ i, 0 ≤ m i) → m ≠ 0 →
        0 < dotProduct m ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec m)) :
    ∀ x : Fin n → ℤ, x ≠ 0 →
        0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) := by
  intro x hx
  set M := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) with hMdef
  -- replace `x` by its componentwise absolute value
  set ax : Fin n → ℤ := fun i => |x i| with haxdef
  have hax_nonneg : ∀ i, 0 ≤ ax i := fun i => abs_nonneg _
  have hax_ne : ax ≠ 0 := by
    intro h
    apply hx
    funext i
    have hi : |x i| = 0 := by have := congrFun h i; simpa [haxdef] using this
    simpa using abs_eq_zero.mp hi
  have hpos : 0 < dotProduct ax (M.mulVec ax) := hcone ax hax_nonneg hax_ne
  -- the form can only decrease when each entry is replaced by its absolute value
  have hterm : ∀ i j, M i j * ax i * ax j ≤ M i j * x i * x j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have he : M i i * ax i * ax i = M i i * x i * x i := by
        rw [mul_assoc, mul_assoc]
        congr 1
        simp only [haxdef, abs_mul_abs_self]
      exact le_of_eq he
    · have hM : M i j = - adj i j := by
        rw [hMdef, Matrix.sub_apply, two_smul_one_apply, if_neg hij, zero_sub]
      rw [hM]
      have hxx : x i * x j ≤ |x i| * |x j| := by
        calc x i * x j ≤ |x i * x j| := le_abs_self _
          _ = |x i| * |x j| := abs_mul _ _
      have hmul := mul_le_mul_of_nonneg_left hxx (hnonneg i j)
      have e1 : -adj i j * ax i * ax j = -(adj i j * (|x i| * |x j|)) := by
        simp [haxdef]; ring
      have e2 : -adj i j * x i * x j = -(adj i j * (x i * x j)) := by ring
      rw [e1, e2]
      linarith [hmul]
  have hle : dotProduct ax (M.mulVec ax) ≤ dotProduct x (M.mulVec x) := by
    rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.sum_le_sum fun j _ => hterm i j
  linarith [hpos, hle]

/-- **Step 3 of Problem 6.1.5 (packaged).** Given the graph-shape clauses and the
orbit-dimension bound (positivity of the Tits matrix form on the nonzero
nonnegative cone), the graph is a Dynkin diagram. This is the hook consumed by the
final assembly in S4. -/
theorem isDynkinDiagram_of_cone (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hloop : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (hcone : ∀ m : Fin n → ℤ, (∀ i, 0 ≤ m i) → m ≠ 0 →
        0 < dotProduct m ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec m)) :
    Etingof.IsDynkinDiagram n adj := by
  have hnonneg : ∀ i j, 0 ≤ adj i j := by
    intro i j
    rcases h01 i j with h | h <;> omega
  exact ⟨hsymm, hloop, h01, hconn, titsForm_posDef_of_cone adj hnonneg hcone⟩

end Etingof
