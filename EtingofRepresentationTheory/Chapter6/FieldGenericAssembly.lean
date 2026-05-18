import EtingofRepresentationTheory.Chapter6.FieldGenericTpqr
import EtingofRepresentationTheory.Chapter6.FieldGenericD5Tilde

/-!
# Per-(F, Q) outer assembly: `not_posdef_infinite_type_per_kQ`

This file assembles the per-(field, orientation) versions of the leaf
helpers from `Chapter6/FieldGeneric*.lean` into the outer-tree case
analysis that matches `not_posdef_infinite_type`
(`Chapter6/InfiniteTypeConstructions.lean:10661`).

Per-(F, Q) means the conclusion is

  `¬ Set.Finite { d | ∃ V : QuiverRepresentation F (Fin n) over Q,
                          V.IsIndecomposable ∧ dim V = d }`

for an algebraically closed `F` and an arbitrary orientation `Q`. This
is strictly stronger than the universal `¬ IsFiniteTypeQuiver n adj`,
which only asserts that *some* (F, Q) witnesses infinitely many
indecomposables — the per-(F, Q) form is the one Chapter 2 needs to
close `not_posdef_not_HasFiniteRepresentationType`.

## Case analysis (mirrors `not_posdef_infinite_type`)

* `∃ v, vertexDegree adj v ≥ 4` → `degree_ge_4_infinite_type_per_kQ`
  (`Chapter6/FieldGenericStar.lean:649`)
* the graph contains a cycle → `graph_with_list_cycle_infinite_type_per_kQ`
  (`Chapter6/FieldGenericCycle.lean:440`)
* acyclic with a degree-3 branch point →
  `acyclic_branch_not_posdef_infinite_type_per_kQ` (this file)
* acyclic with all degrees ≤ 2 → contradiction via the universal
  `acyclic_deg_le_2_posdef` (positive-definiteness of path graphs is
  field-independent, so the universal lemma suffices).

The branch case fans out to:

* adjacent branches → `adjacent_branches_infinite_type_per_kQ`
  (`Chapter6/FieldGenericD5Tilde.lean:1043`)
* single branch → `single_branch_not_posdef_infinite_type_per_kQ`
  (`Chapter6/FieldGenericTpqr.lean:1408`)
* ≥ 2 non-adjacent branches →
  `non_adjacent_branches_infinite_type_per_kQ` (this file, sorry-bodied;
  tracked by #2919).
-/

open Matrix

namespace Etingof

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `non_adjacent_branches_infinite_type`
(`Chapter6/InfiniteTypeConstructions.lean:9682`).

A connected acyclic simple graph with all degrees ≤ 3 and two
non-adjacent degree-3 vertices `v₀` and `w` has infinite representation
type for every algebraically closed `F` and every orientation `Q`.

The proof (universal version) embeds either D̃ₖ (when both branch points
have two leaf neighbours), Ẽ₇ (when arms extend appropriately), or
T(1, 2, 5) (when one arm is long) via
`subgraph_infinite_type_transfer_per_kQ`. Body is `sorry`; mirror tracked
by #2919. -/
theorem non_adjacent_branches_infinite_type_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (h_deg : ∀ v, vertexDegree adj v < 4)
    (v₀ w : Fin n) (hv₀ : vertexDegree adj v₀ = 3) (hw : vertexDegree adj w = 3)
    (hne : w ≠ v₀) (h_no_adj_branch : ∀ u, adj v₀ u = 1 → vertexDegree adj u < 3)
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧
          ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- TODO (#2919): mirror `non_adjacent_branches_infinite_type` at
  -- `Chapter6/InfiniteTypeConstructions.lean:9682-10608` line-for-line,
  -- swapping each leaf dispatch for its per-(F, Q) variant
  -- (`adjacent_branches_infinite_type_per_kQ`, `d5tilde_not_finite_type_per_kQ`,
  -- `etilde7_not_finite_type_per_kQ`, `t125_not_finite_type_per_kQ`).
  let _ := hOrient
  sorry

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `acyclic_branch_not_posdef_infinite_type`
(`Chapter6/InfiniteTypeConstructions.lean:10609`).

A connected acyclic simple graph with all degrees ≤ 3, a degree-3
branch point, and non-positive-definite Cartan form has infinite
representation type for every algebraically closed `F` and every
orientation `Q`.

Mirrors the universal version line-for-line, dispatching by branch-
point geometry:
  * an adjacent pair of branch points → D̃₅ embedding
  * a unique branch point → T(p, q, r) classification
  * ≥ 2 non-adjacent branch points → D̃ₖ / Ẽ₇ / T(1, 2, 5). -/
theorem acyclic_branch_not_posdef_infinite_type_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (h_deg : ∀ v, vertexDegree adj v < 4)
    (h_has_branch : ∃ v, vertexDegree adj v = 3)
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x))
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧
          ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  obtain ⟨v₀, hv₀⟩ := h_has_branch
  by_cases h_adj_branch : ∃ u, adj v₀ u = 1 ∧ vertexDegree adj u = 3
  · -- Case 1: Adjacent branch points → D̃₅ embedding
    obtain ⟨w, hw_adj, hw_deg⟩ := h_adj_branch
    exact adjacent_branches_infinite_type_per_kQ adj hsymm hdiag h01 h_acyclic
      v₀ w hv₀ hw_deg hw_adj F Q hOrient
  · push_neg at h_adj_branch
    -- All neighbors of v₀ have degree < 3
    have h_no_adj : ∀ u, adj v₀ u = 1 → vertexDegree adj u < 3 := by
      intro u hu
      have := h_adj_branch u hu
      have := h_deg u
      omega
    by_cases h_unique : ∀ w, vertexDegree adj w = 3 → w = v₀
    · -- Case 2: Single branch point → T(p, q, r) analysis
      exact single_branch_not_posdef_infinite_type_per_kQ adj hn hsymm hdiag h01
        hconn h_acyclic h_deg v₀ hv₀ h_unique h_not_posdef F Q hOrient
    · -- Case 3: ≥ 2 non-adjacent branch points
      push_neg at h_unique
      obtain ⟨w, hw_deg, hw_ne⟩ := h_unique
      exact non_adjacent_branches_infinite_type_per_kQ adj hn hsymm hdiag h01
        hconn h_acyclic h_deg v₀ w hv₀ hw_deg hw_ne h_no_adj F Q hOrient

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `not_posdef_infinite_type`
(`Chapter6/InfiniteTypeConstructions.lean:10661`).

A connected simple graph whose Cartan form `2I - adj` is not positive
definite has infinite representation type for every algebraically
closed field `F` and every orientation `Q`. Specifically: the set of
dimension vectors of (`F`, `Q`)-indecomposable representations is
infinite.

This is the outer assembly Chapter 2 dispatches to in order to close
`not_posdef_not_HasFiniteRepresentationType` (i.e., to derive
`¬ HasFiniteRepresentationType` from non-positive-definiteness). -/
theorem not_posdef_infinite_type_per_kQ {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x))
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧
          ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- Case 1: ∃ vertex with degree ≥ 4
  by_cases h_deg4 : ∃ v, 4 ≤ vertexDegree adj v
  · obtain ⟨v, hv⟩ := h_deg4
    exact degree_ge_4_infinite_type_per_kQ adj hsymm hdiag h01 v hv F Q hOrient
  · push_neg at h_deg4
    -- All degrees ≤ 3. Define acyclicity predicate
    set HasCycle := ∃ (cycle : List (Fin n)) (_ : 3 ≤ cycle.length),
        cycle.Nodup ∧
        (∀ k, (h : k + 1 < cycle.length) →
          adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) ∧
        adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
          (cycle.get ⟨0, by omega⟩) = 1 with HasCycle_def
    -- Case 2: graph contains a cycle
    by_cases h_cycle : HasCycle
    · obtain ⟨cycle, hlen, hnodup, hedges, hclose⟩ := h_cycle
      have hclose' : adj (cycle.get ⟨cycle.length - 1, by omega⟩)
          (cycle.get ⟨0, by omega⟩) = 1 := by
        rwa [List.getLast_eq_getElem] at hclose
      exact graph_with_list_cycle_infinite_type_per_kQ adj hsymm hdiag h01
        cycle hlen hnodup hedges hclose' F Q hOrient
    · -- No cycle: graph is acyclic (a tree, since it's connected)
      have h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
          (∀ k, (h : k + 1 < cycle.length) →
            adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
          adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
            (cycle.get ⟨0, by omega⟩) ≠ 1 := by
        intro cycle hclen hnodup hedges hclose
        exact h_cycle ⟨cycle, hclen, hnodup, hedges, hclose⟩
      -- Case 3: tree with a branch point
      by_cases h_has_branch : ∃ v, vertexDegree adj v = 3
      · exact acyclic_branch_not_posdef_infinite_type_per_kQ adj hn hsymm hdiag h01
          hconn h_acyclic h_deg4 h_has_branch h_not_posdef F Q hOrient
      · -- Case 4: all degrees ≤ 2 → path → positive definite → contradicts h_not_posdef
        push_neg at h_has_branch
        have h_deg_lt_3 : ∀ v, vertexDegree adj v < 3 := by
          intro v
          have h3 := h_deg4 v
          have hne3 := h_has_branch v
          omega
        exact absurd (acyclic_deg_le_2_posdef adj hn hsymm hdiag h01 hconn
          h_acyclic h_deg_lt_3) h_not_posdef

end Etingof
