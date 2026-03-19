import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4

/-!
# Theorem: Classification of Dynkin Diagrams

Γ is a Dynkin diagram if and only if it is one of the following graphs:
- Aₙ (n ≥ 1): a path with n vertices
- Dₙ (n ≥ 4): a path on vertices 0,...,n-2 with an extra edge from vertex n-3 to vertex n-1
- E₆, E₇, E₈: the three exceptional Dynkin diagrams (path with branch at vertex 2)

## Mathlib correspondence

Mathlib has `CoxeterMatrix` with Coxeter-Dynkin data for classical types, but the
classification theorem for positive-definite graphs is not present. The graph theory
and quadratic form infrastructure exists but the classification itself is absent.

## Formalization note

We define `DynkinType` as an inductive type enumerating the five families, together
with their adjacency matrices. The classification theorem states that `IsDynkinDiagram`
(positive-definite Cartan form) is equivalent to being graph-isomorphic to one of these
standard types.
-/

/-- The five families of Dynkin diagrams: A_n (n ≥ 1), D_n (n ≥ 4), E₆, E₇, E₈. -/
inductive Etingof.DynkinType where
  | A (n : ℕ) (hn : 1 ≤ n)
  | D (n : ℕ) (hn : 4 ≤ n)
  | E6
  | E7
  | E8

/-- The number of vertices (rank) of a Dynkin diagram. -/
def Etingof.DynkinType.rank : Etingof.DynkinType → ℕ
  | .A n _ => n
  | .D n _ => n
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8

/-- The adjacency matrix of a Dynkin diagram of the given type.

- **A_n**: path graph 0—1—2—⋯—(n-1)
- **D_n**: path 0—1—⋯—(n-2) with branch edge (n-3)—(n-1)
- **E₆**: path 0—1—2—3—4 with branch edge 2—5
- **E₇**: path 0—1—2—3—4—5 with branch edge 2—6
- **E₈**: path 0—1—2—3—4—5—6 with branch edge 2—7 -/
def Etingof.DynkinType.adj : (t : Etingof.DynkinType) → Matrix (Fin t.rank) (Fin t.rank) ℤ
  | .A _n _ => fun i j =>
      if (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) then 1 else 0
  | .D n _ => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ n - 2) ∨
          (j.val + 1 = i.val ∧ i.val ≤ n - 2)) ∨
         ((i.val = n - 3 ∧ j.val = n - 1) ∨
          (j.val = n - 3 ∧ i.val = n - 1))
      then 1 else 0
  | .E6 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 4) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 4)) ∨
         ((i.val = 2 ∧ j.val = 5) ∨ (j.val = 2 ∧ i.val = 5))
      then 1 else 0
  | .E7 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 5) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 5)) ∨
         ((i.val = 2 ∧ j.val = 6) ∨ (j.val = 2 ∧ i.val = 6))
      then 1 else 0
  | .E8 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 6) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 6)) ∨
         ((i.val = 2 ∧ j.val = 7) ∨ (j.val = 2 ∧ i.val = 7))
      then 1 else 0

namespace Etingof

open Matrix Finset

/-! ## Graph isomorphism preserves IsDynkinDiagram -/

/-- If `adj'` is the image of `adj` under a graph isomorphism `σ`, and `adj` is a
Dynkin diagram, then so is `adj'`. -/
private lemma isDynkinDiagram_of_graph_iso {n m : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    {adj' : Matrix (Fin m) (Fin m) ℤ} (σ : Fin n ≃ Fin m)
    (hiso : ∀ i j, adj' (σ i) (σ j) = adj i j)
    (hD : IsDynkinDiagram n adj) : IsDynkinDiagram m adj' := by
  obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
  -- Helper: rewrite adj' in terms of adj via σ.symm
  have rw_adj' : ∀ i j : Fin m, adj' i j = adj (σ.symm i) (σ.symm j) := by
    intro i j
    conv_lhs => rw [show i = σ (σ.symm i) from (σ.apply_symm_apply i).symm,
      show j = σ (σ.symm j) from (σ.apply_symm_apply j).symm]
    exact hiso _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
    · -- head
      cases path with
      | nil => exact absurd hhead (by simp)
      | cons a _ => simp only [List.map, List.head?]; rw [List.head?] at hhead; exact congr_arg _ (Option.some.inj hhead ▸ σ.apply_symm_apply i)
    · -- last
      sorry
    · -- edges
      sorry
  · -- Positive definiteness
    intro x hx
    have hx' : x ∘ σ ≠ 0 := by
      intro h; apply hx; ext i
      have := congr_fun h (σ.symm i); simp [Function.comp] at this; exact this
    specialize hpos (x ∘ σ) hx'
    -- Show the quadratic form values agree
    sorry

/-! ## A_n is a Dynkin diagram

For the path graph A_n, the Tits form q(x) = x^T(2I-adj)x satisfies the sum-of-squares
identity q(x) = x₀² + Σᵢ(xᵢ-xᵢ₊₁)² + x_{n-1}², from which positive definiteness follows.
-/

/-- A_n (path graph) is a Dynkin diagram. -/
private lemma An_isDynkin (n : ℕ) (hn : 1 ≤ n) :
    IsDynkinDiagram n (DynkinType.adj (.A n hn)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Symmetry
    exact Matrix.IsSymm.ext (fun i j => by
      simp only [DynkinType.adj]; congr 1; exact propext or_comm)
  · -- Zero diagonal
    intro i; simp only [DynkinType.adj]; split_ifs with h
    · exact absurd h (by push_neg; constructor <;> omega)
    · rfl
  · -- 0-1 entries
    intro i j; simp only [DynkinType.adj]; split_ifs <;> simp
  · -- Connectivity
    sorry
  · -- Positive definiteness
    sorry

/-- D_n (path with branch) is a Dynkin diagram. -/
private lemma Dn_isDynkin (n : ℕ) (hn : 4 ≤ n) :
    IsDynkinDiagram n (DynkinType.adj (.D n hn)) := by
  sorry

/-- Explicit tree-paths for E₆: vertex `i` to vertex `j` through the unique tree path. -/
private def E6_treePath : Fin 6 → Fin 6 → List (Fin 6) := fun i j =>
  match i, j with
  | 0, 0 => [0] | 0, 1 => [0, 1] | 0, 2 => [0, 1, 2]
  | 0, 3 => [0, 1, 2, 3] | 0, 4 => [0, 1, 2, 3, 4] | 0, 5 => [0, 1, 2, 5]
  | 1, 0 => [1, 0] | 1, 1 => [1] | 1, 2 => [1, 2]
  | 1, 3 => [1, 2, 3] | 1, 4 => [1, 2, 3, 4] | 1, 5 => [1, 2, 5]
  | 2, 0 => [2, 1, 0] | 2, 1 => [2, 1] | 2, 2 => [2]
  | 2, 3 => [2, 3] | 2, 4 => [2, 3, 4] | 2, 5 => [2, 5]
  | 3, 0 => [3, 2, 1, 0] | 3, 1 => [3, 2, 1] | 3, 2 => [3, 2]
  | 3, 3 => [3] | 3, 4 => [3, 4] | 3, 5 => [3, 2, 5]
  | 4, 0 => [4, 3, 2, 1, 0] | 4, 1 => [4, 3, 2, 1] | 4, 2 => [4, 3, 2]
  | 4, 3 => [4, 3] | 4, 4 => [4] | 4, 5 => [4, 3, 2, 5]
  | 5, 0 => [5, 2, 1, 0] | 5, 1 => [5, 2, 1] | 5, 2 => [5, 2]
  | 5, 3 => [5, 2, 3] | 5, 4 => [5, 2, 3, 4] | 5, 5 => [5]

-- No separate path_valid lemma needed; we verify inline below.

/-- E₆ is a Dynkin diagram. -/
private lemma E6_isDynkin : IsDynkinDiagram 6 (DynkinType.adj .E6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Symmetry
    exact Matrix.IsSymm.ext (fun i j => by fin_cases i <;> fin_cases j <;> native_decide)
  · -- Zero diagonal
    intro i; fin_cases i <;> native_decide
  · -- 0-1 entries
    intro i j; fin_cases i <;> fin_cases j <;> native_decide
  · -- Connectivity: provide explicit tree paths and verify
    intro i j
    refine ⟨E6_treePath i j, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> rfl
    · fin_cases i <;> fin_cases j <;> rfl
    · intro k hk
      fin_cases i <;> fin_cases j <;>
        simp only [E6_treePath, List.length_cons, List.length_nil, Nat.reduceAdd] at hk <;>
        rcases k with _ | (_ | (_ | (_ | _))) <;>
        (first | omega | (dsimp only [E6_treePath, List.get]; native_decide))
  · -- Positive definiteness via Cholesky sum-of-squares decomposition.
    -- The LDLᵀ factorization of the Cartan matrix 2I - adj_E6 gives
    -- D = diag(2, 3/2, 4/3, 5/4, 6/5, 1/2), all positive.
    -- Clearing denominators: 60 · xᵀCx = 30(2x₀−x₁)² + 10(3x₁−2x₂)² +
    --   5(4x₂−3x₃−3x₅)² + 3(5x₃−4x₄−3x₅)² + 18(2x₄−x₅)² + 30x₅²
    intro x hx
    -- Abbreviate coordinates
    set a := x 0; set b := x 1; set c := x 2; set d := x 3; set e := x 4; set f := x 5
    -- It suffices to show 60 * q(x) > 0 (since 60 > 0)
    suffices h60 : 0 < 60 * dotProduct x
        ((2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) - DynkinType.adj .E6).mulVec x) by linarith
    -- Step 1: Expand the quadratic form to a polynomial in a,b,c,d,e,f
    have expand : dotProduct x ((2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) -
        DynkinType.adj .E6).mulVec x) =
        2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*c*f := by
      -- First show the Cartan matrix equals a concrete matrix
      set C := 2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) - DynkinType.adj .E6
      have hC : C = !![2,-1,0,0,0,0; -1,2,-1,0,0,0; 0,-1,2,-1,0,-1;
                        0,0,-1,2,-1,0; 0,0,0,-1,2,0; 0,0,-1,0,0,2] := by
        ext i j; fin_cases i <;> fin_cases j <;> native_decide
      rw [hC]
      simp [dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, vecHead]
      ring
    -- Step 2: Rewrite as SOS
    rw [expand]
    have sos : 60 * (2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*c*f) =
        30*(2*a-b)^2 + 10*(3*b-2*c)^2 + 5*(4*c-3*d-3*f)^2 +
        3*(5*d-4*e-3*f)^2 + 18*(2*e-f)^2 + 30*f^2 := by ring
    rw [sos]
    -- Step 3: SOS > 0 when x ≠ 0. Proof by contradiction.
    by_contra h_le
    push_neg at h_le
    have s1 := sq_nonneg (2*a-b)
    have s2 := sq_nonneg (3*b-2*c)
    have s3 := sq_nonneg (4*c-3*d-3*f)
    have s4 := sq_nonneg (5*d-4*e-3*f)
    have s5 := sq_nonneg (2*e-f)
    have s6 := sq_nonneg f
    -- Back-substitute: from f upward, each variable must be 0
    have hf : f = 0 := by
      have : f ^ 2 ≤ 0 := by nlinarith
      have := le_antisymm this (sq_nonneg f)
      exact pow_eq_zero (show f ^ 2 = 0 from this)
    have he : e = 0 := by
      have : (2*e-f) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (2*e-f)))
      omega
    have hd : d = 0 := by
      have : (5*d-4*e-3*f) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (5*d-4*e-3*f)))
      omega
    have hc : c = 0 := by
      have : (4*c-3*d-3*f) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (4*c-3*d-3*f)))
      omega
    have hb : b = 0 := by
      have : (3*b-2*c) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (3*b-2*c)))
      omega
    have ha : a = 0 := by
      have : (2*a-b) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (2*a-b)))
      omega
    exact hx (funext fun i => by fin_cases i <;> assumption)

/-- Explicit tree-paths for E₇: path 0—1—2—3—4—5 with branch 2—6. -/
private def E7_treePath : Fin 7 → Fin 7 → List (Fin 7) := fun i j =>
  match i, j with
  | 0, 0 => [0] | 0, 1 => [0, 1] | 0, 2 => [0, 1, 2]
  | 0, 3 => [0, 1, 2, 3] | 0, 4 => [0, 1, 2, 3, 4] | 0, 5 => [0, 1, 2, 3, 4, 5]
  | 0, 6 => [0, 1, 2, 6]
  | 1, 0 => [1, 0] | 1, 1 => [1] | 1, 2 => [1, 2]
  | 1, 3 => [1, 2, 3] | 1, 4 => [1, 2, 3, 4] | 1, 5 => [1, 2, 3, 4, 5]
  | 1, 6 => [1, 2, 6]
  | 2, 0 => [2, 1, 0] | 2, 1 => [2, 1] | 2, 2 => [2]
  | 2, 3 => [2, 3] | 2, 4 => [2, 3, 4] | 2, 5 => [2, 3, 4, 5]
  | 2, 6 => [2, 6]
  | 3, 0 => [3, 2, 1, 0] | 3, 1 => [3, 2, 1] | 3, 2 => [3, 2]
  | 3, 3 => [3] | 3, 4 => [3, 4] | 3, 5 => [3, 4, 5]
  | 3, 6 => [3, 2, 6]
  | 4, 0 => [4, 3, 2, 1, 0] | 4, 1 => [4, 3, 2, 1] | 4, 2 => [4, 3, 2]
  | 4, 3 => [4, 3] | 4, 4 => [4] | 4, 5 => [4, 5]
  | 4, 6 => [4, 3, 2, 6]
  | 5, 0 => [5, 4, 3, 2, 1, 0] | 5, 1 => [5, 4, 3, 2, 1] | 5, 2 => [5, 4, 3, 2]
  | 5, 3 => [5, 4, 3] | 5, 4 => [5, 4] | 5, 5 => [5]
  | 5, 6 => [5, 4, 3, 2, 6]
  | 6, 0 => [6, 2, 1, 0] | 6, 1 => [6, 2, 1] | 6, 2 => [6, 2]
  | 6, 3 => [6, 2, 3] | 6, 4 => [6, 2, 3, 4] | 6, 5 => [6, 2, 3, 4, 5]
  | 6, 6 => [6]

set_option maxHeartbeats 400000 in
/-- E₇ is a Dynkin diagram. -/
private lemma E7_isDynkin : IsDynkinDiagram 7 (DynkinType.adj .E7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.IsSymm.ext (fun i j => by fin_cases i <;> fin_cases j <;> native_decide)
  · intro i; fin_cases i <;> native_decide
  · intro i j; fin_cases i <;> fin_cases j <;> native_decide
  · -- Connectivity
    intro i j
    refine ⟨E7_treePath i j, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> rfl
    · fin_cases i <;> fin_cases j <;> rfl
    · intro k hk
      fin_cases i <;> fin_cases j <;>
        simp only [E7_treePath, List.length_cons, List.length_nil, Nat.reduceAdd] at hk <;>
        rcases k with _ | (_ | (_ | (_ | (_ | _)))) <;>
        (first | omega | (dsimp only [E7_treePath, List.get]; native_decide))
  · -- Positive definiteness via Cholesky SOS decomposition
    -- 420·q = 210(2a-b)² + 70(3b-2c)² + 35(4c-3d-3g)² + 21(5d-4e-3g)² +
    --         14(6e-5f-3g)² + 10(7f-3g)² + 120g²
    intro x hx
    set a := x 0; set b := x 1; set c := x 2; set d := x 3
    set e := x 4; set f := x 5; set g := x 6
    suffices h420 : 0 < 420 * dotProduct x
        ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) - DynkinType.adj .E7).mulVec x) by linarith
    have expand : dotProduct x ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) -
        DynkinType.adj .E7).mulVec x) =
        2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*c*g := by
      set C := 2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) - DynkinType.adj .E7
      have hC : C = !![2,-1,0,0,0,0,0; -1,2,-1,0,0,0,0; 0,-1,2,-1,0,0,-1;
                        0,0,-1,2,-1,0,0; 0,0,0,-1,2,-1,0; 0,0,0,0,-1,2,0;
                        0,0,-1,0,0,0,2] := by
        ext i j; fin_cases i <;> fin_cases j <;> native_decide
      rw [hC]
      simp [dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]
      ring
    rw [expand]
    have sos : 420 * (2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*c*g) =
        210*(2*a-b)^2 + 70*(3*b-2*c)^2 + 35*(4*c-3*d-3*g)^2 + 21*(5*d-4*e-3*g)^2 +
        14*(6*e-5*f-3*g)^2 + 10*(7*f-3*g)^2 + 120*g^2 := by ring
    rw [sos]
    by_contra h_le
    push_neg at h_le
    have s1 := sq_nonneg (2*a-b)
    have s2 := sq_nonneg (3*b-2*c)
    have s3 := sq_nonneg (4*c-3*d-3*g)
    have s4 := sq_nonneg (5*d-4*e-3*g)
    have s5 := sq_nonneg (6*e-5*f-3*g)
    have s6 := sq_nonneg (7*f-3*g)
    have s7 := sq_nonneg g
    have hg : g = 0 := by
      have : g ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero (le_antisymm this (sq_nonneg g))
    have hf : f = 0 := by
      have : (7*f-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (7*f-3*g)))
      omega
    have he : e = 0 := by
      have : (6*e-5*f-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (6*e-5*f-3*g)))
      omega
    have hd : d = 0 := by
      have : (5*d-4*e-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (5*d-4*e-3*g)))
      omega
    have hc : c = 0 := by
      have : (4*c-3*d-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (4*c-3*d-3*g)))
      omega
    have hb : b = 0 := by
      have : (3*b-2*c) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (3*b-2*c)))
      omega
    have ha : a = 0 := by
      have : (2*a-b) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (2*a-b)))
      omega
    exact hx (funext fun i => by fin_cases i <;> assumption)

/-- Explicit tree-paths for E₈: path 0—1—2—3—4—5—6 with branch 2—7. -/
private def E8_treePath : Fin 8 → Fin 8 → List (Fin 8) := fun i j =>
  match i, j with
  | 0, 0 => [0] | 0, 1 => [0, 1] | 0, 2 => [0, 1, 2]
  | 0, 3 => [0, 1, 2, 3] | 0, 4 => [0, 1, 2, 3, 4] | 0, 5 => [0, 1, 2, 3, 4, 5]
  | 0, 6 => [0, 1, 2, 3, 4, 5, 6] | 0, 7 => [0, 1, 2, 7]
  | 1, 0 => [1, 0] | 1, 1 => [1] | 1, 2 => [1, 2]
  | 1, 3 => [1, 2, 3] | 1, 4 => [1, 2, 3, 4] | 1, 5 => [1, 2, 3, 4, 5]
  | 1, 6 => [1, 2, 3, 4, 5, 6] | 1, 7 => [1, 2, 7]
  | 2, 0 => [2, 1, 0] | 2, 1 => [2, 1] | 2, 2 => [2]
  | 2, 3 => [2, 3] | 2, 4 => [2, 3, 4] | 2, 5 => [2, 3, 4, 5]
  | 2, 6 => [2, 3, 4, 5, 6] | 2, 7 => [2, 7]
  | 3, 0 => [3, 2, 1, 0] | 3, 1 => [3, 2, 1] | 3, 2 => [3, 2]
  | 3, 3 => [3] | 3, 4 => [3, 4] | 3, 5 => [3, 4, 5]
  | 3, 6 => [3, 4, 5, 6] | 3, 7 => [3, 2, 7]
  | 4, 0 => [4, 3, 2, 1, 0] | 4, 1 => [4, 3, 2, 1] | 4, 2 => [4, 3, 2]
  | 4, 3 => [4, 3] | 4, 4 => [4] | 4, 5 => [4, 5]
  | 4, 6 => [4, 5, 6] | 4, 7 => [4, 3, 2, 7]
  | 5, 0 => [5, 4, 3, 2, 1, 0] | 5, 1 => [5, 4, 3, 2, 1] | 5, 2 => [5, 4, 3, 2]
  | 5, 3 => [5, 4, 3] | 5, 4 => [5, 4] | 5, 5 => [5]
  | 5, 6 => [5, 6] | 5, 7 => [5, 4, 3, 2, 7]
  | 6, 0 => [6, 5, 4, 3, 2, 1, 0] | 6, 1 => [6, 5, 4, 3, 2, 1] | 6, 2 => [6, 5, 4, 3, 2]
  | 6, 3 => [6, 5, 4, 3] | 6, 4 => [6, 5, 4] | 6, 5 => [6, 5]
  | 6, 6 => [6] | 6, 7 => [6, 5, 4, 3, 2, 7]
  | 7, 0 => [7, 2, 1, 0] | 7, 1 => [7, 2, 1] | 7, 2 => [7, 2]
  | 7, 3 => [7, 2, 3] | 7, 4 => [7, 2, 3, 4] | 7, 5 => [7, 2, 3, 4, 5]
  | 7, 6 => [7, 2, 3, 4, 5, 6] | 7, 7 => [7]

set_option maxHeartbeats 400000 in
/-- E₈ is a Dynkin diagram. -/
private lemma E8_isDynkin : IsDynkinDiagram 8 (DynkinType.adj .E8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.IsSymm.ext (fun i j => by fin_cases i <;> fin_cases j <;> native_decide)
  · intro i; fin_cases i <;> native_decide
  · intro i j; fin_cases i <;> fin_cases j <;> native_decide
  · -- Connectivity
    intro i j
    refine ⟨E8_treePath i j, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> rfl
    · fin_cases i <;> fin_cases j <;> rfl
    · intro k hk
      fin_cases i <;> fin_cases j <;>
        simp only [E8_treePath, List.length_cons, List.length_nil, Nat.reduceAdd] at hk <;>
        rcases k with _ | (_ | (_ | (_ | (_ | (_ | _))))) <;>
        (first | omega | (dsimp only [E8_treePath, List.get]; native_decide))
  · -- Positive definiteness via Cholesky SOS decomposition
    -- 840·q = 420(2a-b)² + 140(3b-2c)² + 70(4c-3d-3h)² + 42(5d-4e-3h)² +
    --         28(6e-5f-3h)² + 20(7f-6g-3h)² + 15(8g-3h)² + 105h²
    intro x hx
    set a := x 0; set b := x 1; set c := x 2; set d := x 3
    set e := x 4; set f := x 5; set g := x 6; set h := x 7
    suffices h840 : 0 < 840 * dotProduct x
        ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) - DynkinType.adj .E8).mulVec x) by linarith
    have expand : dotProduct x ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) -
        DynkinType.adj .E8).mulVec x) =
        2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 + 2*h^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*f*g - 2*c*h := by
      set C := 2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) - DynkinType.adj .E8
      have hC : C = !![2,-1,0,0,0,0,0,0; -1,2,-1,0,0,0,0,0; 0,-1,2,-1,0,0,0,-1;
                        0,0,-1,2,-1,0,0,0; 0,0,0,-1,2,-1,0,0; 0,0,0,0,-1,2,-1,0;
                        0,0,0,0,0,-1,2,0; 0,0,-1,0,0,0,0,2] := by
        ext i j; fin_cases i <;> fin_cases j <;> native_decide
      rw [hC]
      simp [dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]
      ring
    rw [expand]
    have sos : 840 * (2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 + 2*h^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*f*g - 2*c*h) =
        420*(2*a-b)^2 + 140*(3*b-2*c)^2 + 70*(4*c-3*d-3*h)^2 + 42*(5*d-4*e-3*h)^2 +
        28*(6*e-5*f-3*h)^2 + 20*(7*f-6*g-3*h)^2 + 15*(8*g-3*h)^2 + 105*h^2 := by ring
    rw [sos]
    by_contra h_le
    push_neg at h_le
    have s1 := sq_nonneg (2*a-b)
    have s2 := sq_nonneg (3*b-2*c)
    have s3 := sq_nonneg (4*c-3*d-3*h)
    have s4 := sq_nonneg (5*d-4*e-3*h)
    have s5 := sq_nonneg (6*e-5*f-3*h)
    have s6 := sq_nonneg (7*f-6*g-3*h)
    have s7 := sq_nonneg (8*g-3*h)
    have s8 := sq_nonneg h
    have hh : h = 0 := by
      have : h ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero (le_antisymm this (sq_nonneg h))
    have hg : g = 0 := by
      have : (8*g-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (8*g-3*h)))
      omega
    have hf : f = 0 := by
      have : (7*f-6*g-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (7*f-6*g-3*h)))
      omega
    have he : e = 0 := by
      have : (6*e-5*f-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (6*e-5*f-3*h)))
      omega
    have hd : d = 0 := by
      have : (5*d-4*e-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (5*d-4*e-3*h)))
      omega
    have hc : c = 0 := by
      have : (4*c-3*d-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (4*c-3*d-3*h)))
      omega
    have hb : b = 0 := by
      have : (3*b-2*c) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (3*b-2*c)))
      omega
    have ha : a = 0 := by
      have : (2*a-b) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (2*a-b)))
      omega
    exact hx (funext fun i => by fin_cases i <;> assumption)

/-- Each standard Dynkin type gives a Dynkin diagram. -/
private lemma isDynkinDiagram_of_type (t : DynkinType) :
    IsDynkinDiagram t.rank t.adj := by
  cases t with
  | A n hn => exact An_isDynkin n hn
  | D n hn => exact Dn_isDynkin n hn
  | E6 => exact E6_isDynkin
  | E7 => exact E7_isDynkin
  | E8 => exact E8_isDynkin

/-- Classification of Dynkin diagrams: a connected graph with positive-definite Cartan form
is a Dynkin diagram if and only if it is isomorphic (as a graph) to one of the standard
types A_n, D_n, E₆, E₇, or E₈.
(Etingof Theorem, Section 6.1) -/
theorem Theorem_Dynkin_classification (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) :
    IsDynkinDiagram n adj ↔
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  constructor
  · -- Forward direction: any Dynkin diagram is isomorphic to a standard type
    sorry
  · -- Backward direction: isomorphism to a standard type → IsDynkinDiagram
    rintro ⟨t, σ, hiso⟩
    exact isDynkinDiagram_of_graph_iso σ hiso (isDynkinDiagram_of_type t)

end Etingof
