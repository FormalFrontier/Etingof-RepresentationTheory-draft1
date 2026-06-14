import EtingofRepresentationTheory.Chapter6.FieldGenericTpqr
import EtingofRepresentationTheory.Chapter6.FieldGenericD5Tilde
import EtingofRepresentationTheory.Chapter6.FieldGenericNonAdjacentBranches

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
  `non_adjacent_branches_infinite_type_per_kQ` (this file; the
  remaining leaf-case body is in `FieldGenericNonAdjacentBranches.lean`,
  tracked by #2939).
-/

open Matrix

namespace Etingof

set_option maxHeartbeats 6400000 in
-- reason: mirrors the budget on the universal
-- `non_adjacent_branches_infinite_type`
-- (`InfiniteTypeConstructions.lean:9678`); the all-deg-2 case verifies
-- the 49-pair `etilde6Adj`/host adjacency table via `fin_cases` +
-- `linarith` and pushes past the default budget.
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `non_adjacent_branches_infinite_type`
(`Chapter6/InfiniteTypeConstructions.lean:9682`).

A connected acyclic simple graph with all degrees ≤ 3 and two
non-adjacent degree-3 vertices `v₀` and `w` has infinite representation
type for every algebraically closed `F` and every orientation `Q`.

The proof mirrors the universal version. After dispatching to
`adjacent_branches_infinite_type_per_kQ` when any pair of branch points
turns out to be adjacent, we extract `v₀`'s three neighbours and case
split: if any neighbour is a leaf we delegate to
`non_adjacent_branches_leaf_case_per_kQ`; otherwise all three have
degree 2 and we embed `Ẽ₆ = T(2, 2, 2)` via
`subgraph_infinite_type_transfer_per_kQ` and
`etilde6_not_finite_type_per_kQ`. -/
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
  -- Case 1: If some pair of branch points is adjacent somewhere, use that directly
  by_cases h_adj_exists : ∃ x y, adj x y = 1 ∧ vertexDegree adj x = 3 ∧ vertexDegree adj y = 3
  · obtain ⟨x, y, hxy, hx, hy⟩ := h_adj_exists
    exact adjacent_branches_infinite_type_per_kQ adj hsymm hdiag h01 h_acyclic x y hx hy
      hxy F Q hOrient
  · -- Case 2: All branch points are pairwise non-adjacent
    push_neg at h_adj_exists
    have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
    have ne_of_adj : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
      rw [hab, hdiag] at h; exact one_ne_zero h.symm
    -- Extract v₀'s 3 neighbors
    set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1) with hS₀_def
    have hS₀_card : S₀.card = 3 := hv₀
    have hS₀_ne : S₀.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hS₀_card
    obtain ⟨u₃, hu₃_mem⟩ := hS₀_ne
    have hu₃_adj : adj v₀ u₃ = 1 := (Finset.mem_filter.mp hu₃_mem).2
    have hS₀_erase : (S₀.erase u₃).card = 2 := by
      rw [Finset.card_erase_of_mem hu₃_mem, hS₀_card]
    obtain ⟨u₁, u₂, hu₁₂, hS₀_eq⟩ := Finset.card_eq_two.mp hS₀_erase
    have hu₁_mem : u₁ ∈ S₀.erase u₃ := hS₀_eq ▸ Finset.mem_insert_self u₁ _
    have hu₂_mem : u₂ ∈ S₀.erase u₃ := hS₀_eq ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self u₂))
    have hu₁_adj : adj v₀ u₁ = 1 :=
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₁_mem)).2
    have hu₂_adj : adj v₀ u₂ = 1 :=
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₂_mem)).2
    have hu₁_ne_u₃ : u₁ ≠ u₃ := Finset.ne_of_mem_erase hu₁_mem
    have hu₂_ne_u₃ : u₂ ≠ u₃ := Finset.ne_of_mem_erase hu₂_mem
    have hu₁_deg : vertexDegree adj u₁ < 3 := h_no_adj_branch u₁ hu₁_adj
    have hu₂_deg : vertexDegree adj u₂ < 3 := h_no_adj_branch u₂ hu₂_adj
    have hu₃_deg : vertexDegree adj u₃ < 3 := h_no_adj_branch u₃ hu₃_adj
    have hu₁_ne_v₀ : u₁ ≠ v₀ := (ne_of_adj v₀ u₁ hu₁_adj).symm
    have hu₂_ne_v₀ : u₂ ≠ v₀ := (ne_of_adj v₀ u₂ hu₂_adj).symm
    have hu₃_ne_v₀ : u₃ ≠ v₀ := (ne_of_adj v₀ u₃ hu₃_adj).symm
    have hu₁_v₀ : adj u₁ v₀ = 1 := (adj_comm u₁ v₀).trans hu₁_adj
    have hu₂_v₀ : adj u₂ v₀ = 1 := (adj_comm u₂ v₀).trans hu₂_adj
    have hu₃_v₀ : adj u₃ v₀ = 1 := (adj_comm u₃ v₀).trans hu₃_adj
    have hu₁_deg_ge : 1 ≤ vertexDegree adj u₁ :=
      Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₁_v₀⟩⟩
    have hu₂_deg_ge : 1 ≤ vertexDegree adj u₂ :=
      Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₂_v₀⟩⟩
    have hu₃_deg_ge : 1 ≤ vertexDegree adj u₃ :=
      Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₃_v₀⟩⟩
    -- v₀ and w are not adjacent (no adjacent degree-3 pair exists)
    have h_v₀w_nonadj : adj v₀ w ≠ 1 := by
      intro hadj
      have := h_adj_exists v₀ w hadj
      simp [hv₀, hw] at this
    -- Neighbours of `w` have degree `< 3`, derived from the negated existential
    -- (the per-(F, Q) leaf-case helper hypothesises this symmetrically to
    -- `h_no_adj_branch`; see `FieldGenericNonAdjacentBranches.lean:76-81`).
    have h_no_adj_branch_w : ∀ u, adj w u = 1 → vertexDegree adj u < 3 := by
      intro u hu
      have := h_adj_exists w u hu hw
      have := h_deg u
      omega
    -- Leaf-case dispatch via Sub-A1 helper (`non_adjacent_branches_leaf_case_per_kQ`).
    by_cases hu₁_leaf : vertexDegree adj u₁ = 1
    · exact non_adjacent_branches_leaf_case_per_kQ adj hn hsymm hdiag h01 hconn h_acyclic
        h_deg v₀ w hv₀ hw hne h_no_adj_branch h_no_adj_branch_w h_v₀w_nonadj
        u₁ hu₁_adj hu₁_leaf F Q hOrient
    · by_cases hu₂_leaf : vertexDegree adj u₂ = 1
      · exact non_adjacent_branches_leaf_case_per_kQ adj hn hsymm hdiag h01 hconn h_acyclic
          h_deg v₀ w hv₀ hw hne h_no_adj_branch h_no_adj_branch_w h_v₀w_nonadj
          u₂ hu₂_adj hu₂_leaf F Q hOrient
      · by_cases hu₃_leaf : vertexDegree adj u₃ = 1
        · exact non_adjacent_branches_leaf_case_per_kQ adj hn hsymm hdiag h01 hconn h_acyclic
            h_deg v₀ w hv₀ hw hne h_no_adj_branch h_no_adj_branch_w h_v₀w_nonadj
            u₃ hu₃_adj hu₃_leaf F Q hOrient
        · -- All 3 neighbors have degree = 2. Embed Ẽ₆ = T(2, 2, 2).
          have hu₁_deg2 : vertexDegree adj u₁ = 2 := by omega
          have hu₂_deg2 : vertexDegree adj u₂ = 2 := by omega
          have hu₃_deg2 : vertexDegree adj u₃ = 2 := by omega
          -- u₁'s other neighbor
          set Su₁ := Finset.univ.filter (fun j => adj u₁ j = 1)
          have hSu₁_card : Su₁.card = 2 := hu₁_deg2
          have hv₀_in_Su₁ : v₀ ∈ Su₁ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₁_v₀⟩
          obtain ⟨u₁', hu₁'_eq⟩ := Finset.card_eq_one.mp (by
            rw [Finset.card_erase_of_mem hv₀_in_Su₁, hSu₁_card])
          have hu₁'_mem : u₁' ∈ Su₁.erase v₀ := hu₁'_eq ▸ Finset.mem_singleton_self u₁'
          have hu₁'_adj : adj u₁ u₁' = 1 :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₁'_mem)).2
          have hu₁'_ne_v₀ : u₁' ≠ v₀ := Finset.ne_of_mem_erase hu₁'_mem
          -- u₂'s other neighbor
          set Su₂ := Finset.univ.filter (fun j => adj u₂ j = 1)
          have hSu₂_card : Su₂.card = 2 := hu₂_deg2
          have hv₀_in_Su₂ : v₀ ∈ Su₂ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₂_v₀⟩
          obtain ⟨u₂', hu₂'_eq⟩ := Finset.card_eq_one.mp (by
            rw [Finset.card_erase_of_mem hv₀_in_Su₂, hSu₂_card])
          have hu₂'_mem : u₂' ∈ Su₂.erase v₀ := hu₂'_eq ▸ Finset.mem_singleton_self u₂'
          have hu₂'_adj : adj u₂ u₂' = 1 :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₂'_mem)).2
          have hu₂'_ne_v₀ : u₂' ≠ v₀ := Finset.ne_of_mem_erase hu₂'_mem
          -- u₃'s other neighbor
          set Su₃ := Finset.univ.filter (fun j => adj u₃ j = 1)
          have hSu₃_card : Su₃.card = 2 := hu₃_deg2
          have hv₀_in_Su₃ : v₀ ∈ Su₃ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₃_v₀⟩
          obtain ⟨u₃', hu₃'_eq⟩ := Finset.card_eq_one.mp (by
            rw [Finset.card_erase_of_mem hv₀_in_Su₃, hSu₃_card])
          have hu₃'_mem : u₃' ∈ Su₃.erase v₀ := hu₃'_eq ▸ Finset.mem_singleton_self u₃'
          have hu₃'_adj : adj u₃ u₃' = 1 :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₃'_mem)).2
          have hu₃'_ne_v₀ : u₃' ≠ v₀ := Finset.ne_of_mem_erase hu₃'_mem
          -- Reverse adjacencies for u_i'
          have hu₁'_u₁ : adj u₁' u₁ = 1 := (adj_comm u₁' u₁).trans hu₁'_adj
          have hu₂'_u₂ : adj u₂' u₂ = 1 := (adj_comm u₂' u₂).trans hu₂'_adj
          have hu₃'_u₃ : adj u₃' u₃ = 1 := (adj_comm u₃' u₃).trans hu₃'_adj
          -- u_i' ≠ u_i (from adjacency)
          have hu₁'_ne_u₁ : u₁' ≠ u₁ := (ne_of_adj u₁ u₁' hu₁'_adj).symm
          have hu₂'_ne_u₂ : u₂' ≠ u₂ := (ne_of_adj u₂ u₂' hu₂'_adj).symm
          have hu₃'_ne_u₃ : u₃' ≠ u₃ := (ne_of_adj u₃ u₃' hu₃'_adj).symm
          -- Non-edges via acyclic_no_triangle
          have hu₁u₂ : adj u₁ u₂ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ u₂
              hu₁₂ hu₁_ne_v₀ hu₂_ne_v₀ hu₁_adj hu₂_adj
          have hu₁u₃ : adj u₁ u₃ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ u₃
              hu₁_ne_u₃ hu₁_ne_v₀ hu₃_ne_v₀ hu₁_adj hu₃_adj
          have hu₂u₃ : adj u₂ u₃ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₂ u₃
              hu₂_ne_u₃ hu₂_ne_v₀ hu₃_ne_v₀ hu₂_adj hu₃_adj
          have hv₀_u₁' : adj v₀ u₁' = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic u₁ v₀ u₁'
              hu₁'_ne_v₀.symm (ne_of_adj v₀ u₁ hu₁_adj) hu₁'_ne_u₁ hu₁_v₀ hu₁'_adj
          have hv₀_u₂' : adj v₀ u₂' = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic u₂ v₀ u₂'
              hu₂'_ne_v₀.symm (ne_of_adj v₀ u₂ hu₂_adj) hu₂'_ne_u₂ hu₂_v₀ hu₂'_adj
          have hv₀_u₃' : adj v₀ u₃' = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic u₃ v₀ u₃'
              hu₃'_ne_v₀.symm (ne_of_adj v₀ u₃ hu₃_adj) hu₃'_ne_u₃ hu₃_v₀ hu₃'_adj
          -- Distinctness: u_i' ≠ u_j
          have hu₁'_ne_u₂ : u₁' ≠ u₂ := by intro h; rw [h] at hv₀_u₁'; linarith
          have hu₁'_ne_u₃ : u₁' ≠ u₃ := by intro h; rw [h] at hv₀_u₁'; linarith
          have hu₂'_ne_u₁ : u₂' ≠ u₁ := by intro h; rw [h] at hv₀_u₂'; linarith
          have hu₂'_ne_u₃ : u₂' ≠ u₃ := by intro h; rw [h] at hv₀_u₂'; linarith
          have hu₃'_ne_u₁ : u₃' ≠ u₁ := by intro h; rw [h] at hv₀_u₃'; linarith
          have hu₃'_ne_u₂ : u₃' ≠ u₂ := by intro h; rw [h] at hv₀_u₃'; linarith
          -- Cross-arm non-adjacency via 4-vertex paths
          have path_nodup4 : ∀ (a b c d : Fin n),
              a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → [a, b, c, d].Nodup := by
            intro a b c d hab hac had hbc hbd hcd
            simp only [List.nodup_cons, List.mem_cons,
              List.not_mem_nil, not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
            exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
          have path_edges4 : ∀ (a b c d : Fin n),
              adj a b = 1 → adj b c = 1 → adj c d = 1 →
              ∀ k, (hk : k + 1 < [a, b, c, d].length) →
                adj ([a, b, c, d].get ⟨k, by omega⟩) ([a, b, c, d].get ⟨k + 1, hk⟩) = 1 := by
            intro a b c d h₁ h₂ h₃ k hk
            have : k + 1 < 4 := by simpa using hk
            have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
            rcases this with rfl | rfl | rfl <;> assumption
          have hu₁'_u₂_nonadj : adj u₁' u₂ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₂, v₀, u₁, u₁'] (by simp)
              (path_nodup4 u₂ v₀ u₁ u₁' hu₂_ne_v₀ hu₁₂.symm hu₁'_ne_u₂.symm
                hu₁_ne_v₀.symm hu₁'_ne_v₀.symm hu₁'_ne_u₁.symm)
              (path_edges4 u₂ v₀ u₁ u₁' (adj_comm u₂ v₀ |>.trans hu₂_adj)
                hu₁_adj hu₁'_adj)
          have hu₁'_u₃_nonadj : adj u₁' u₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃, v₀, u₁, u₁'] (by simp)
              (path_nodup4 u₃ v₀ u₁ u₁' hu₃_ne_v₀ hu₁_ne_u₃.symm hu₁'_ne_u₃.symm
                hu₁_ne_v₀.symm hu₁'_ne_v₀.symm hu₁'_ne_u₁.symm)
              (path_edges4 u₃ v₀ u₁ u₁' (adj_comm u₃ v₀ |>.trans hu₃_adj)
                hu₁_adj hu₁'_adj)
          have hu₂'_u₁_nonadj : adj u₂' u₁ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₁, v₀, u₂, u₂'] (by simp)
              (path_nodup4 u₁ v₀ u₂ u₂' hu₁_ne_v₀ hu₁₂ hu₂'_ne_u₁.symm
                hu₂_ne_v₀.symm hu₂'_ne_v₀.symm hu₂'_ne_u₂.symm)
              (path_edges4 u₁ v₀ u₂ u₂' (adj_comm u₁ v₀ |>.trans hu₁_adj)
                hu₂_adj hu₂'_adj)
          have hu₂'_u₃_nonadj : adj u₂' u₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃, v₀, u₂, u₂'] (by simp)
              (path_nodup4 u₃ v₀ u₂ u₂' hu₃_ne_v₀ hu₂_ne_u₃.symm hu₂'_ne_u₃.symm
                hu₂_ne_v₀.symm hu₂'_ne_v₀.symm hu₂'_ne_u₂.symm)
              (path_edges4 u₃ v₀ u₂ u₂' (adj_comm u₃ v₀ |>.trans hu₃_adj)
                hu₂_adj hu₂'_adj)
          have hu₃'_u₁_nonadj : adj u₃' u₁ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₁, v₀, u₃, u₃'] (by simp)
              (path_nodup4 u₁ v₀ u₃ u₃' hu₁_ne_v₀ hu₁_ne_u₃ hu₃'_ne_u₁.symm
                hu₃_ne_v₀.symm hu₃'_ne_v₀.symm hu₃'_ne_u₃.symm)
              (path_edges4 u₁ v₀ u₃ u₃' (adj_comm u₁ v₀ |>.trans hu₁_adj)
                hu₃_adj hu₃'_adj)
          have hu₃'_u₂_nonadj : adj u₃' u₂ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₂, v₀, u₃, u₃'] (by simp)
              (path_nodup4 u₂ v₀ u₃ u₃' hu₂_ne_v₀ hu₂_ne_u₃ hu₃'_ne_u₂.symm
                hu₃_ne_v₀.symm hu₃'_ne_v₀.symm hu₃'_ne_u₃.symm)
              (path_edges4 u₂ v₀ u₃ u₃' (adj_comm u₂ v₀ |>.trans hu₂_adj)
                hu₃_adj hu₃'_adj)
          -- 5-vertex paths for extension-vertex non-adjacencies
          have path_nodup5 : ∀ (a b c d e : Fin n),
              a ≠ b → a ≠ c → a ≠ d → a ≠ e →
              b ≠ c → b ≠ d → b ≠ e →
              c ≠ d → c ≠ e → d ≠ e → [a, b, c, d, e].Nodup := by
            intro a b c d e hab hac had hae hbc hbd hbe hcd hce hde
            simp only [List.nodup_cons, List.mem_cons,
              List.not_mem_nil, not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
            exact ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩
          have path_edges5 : ∀ (a b c d e : Fin n),
              adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
              ∀ k, (hk : k + 1 < [a, b, c, d, e].length) →
                adj ([a, b, c, d, e].get ⟨k, by omega⟩)
                    ([a, b, c, d, e].get ⟨k + 1, hk⟩) = 1 := by
            intro a b c d e h₁ h₂ h₃ h₄ k hk
            have : k + 1 < 5 := by simpa using hk
            have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
            rcases this with rfl | rfl | rfl | rfl <;> assumption
          have hu₁'_ne_u₂' : u₁' ≠ u₂' := by
            intro h; rw [h] at hu₁'_u₂_nonadj
            linarith [adj_comm u₂' u₂, hu₂'_u₂]
          have hu₁'_ne_u₃' : u₁' ≠ u₃' := by
            intro h; rw [h] at hu₁'_u₃_nonadj
            linarith [adj_comm u₃' u₃, hu₃'_u₃]
          have hu₂'_ne_u₃' : u₂' ≠ u₃' := by
            intro h; rw [h] at hu₂'_u₃_nonadj
            linarith [adj_comm u₃' u₃, hu₃'_u₃]
          have hu₁'_u₂'_nonadj : adj u₁' u₂' = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₂', u₂, v₀, u₁, u₁'] (by simp)
              (path_nodup5 u₂' u₂ v₀ u₁ u₁'
                hu₂'_ne_u₂ hu₂'_ne_v₀ hu₂'_ne_u₁ hu₁'_ne_u₂'.symm
                hu₂_ne_v₀ hu₁₂.symm hu₁'_ne_u₂.symm
                hu₁_ne_v₀.symm hu₁'_ne_v₀.symm hu₁'_ne_u₁.symm)
              (path_edges5 u₂' u₂ v₀ u₁ u₁' hu₂'_u₂
                (adj_comm u₂ v₀ |>.trans hu₂_adj) hu₁_adj hu₁'_adj)
          have hu₁'_u₃'_nonadj : adj u₁' u₃' = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃', u₃, v₀, u₁, u₁'] (by simp)
              (path_nodup5 u₃' u₃ v₀ u₁ u₁'
                hu₃'_ne_u₃ hu₃'_ne_v₀ hu₃'_ne_u₁ hu₁'_ne_u₃'.symm
                hu₃_ne_v₀ hu₁_ne_u₃.symm hu₁'_ne_u₃.symm
                hu₁_ne_v₀.symm hu₁'_ne_v₀.symm hu₁'_ne_u₁.symm)
              (path_edges5 u₃' u₃ v₀ u₁ u₁' hu₃'_u₃
                (adj_comm u₃ v₀ |>.trans hu₃_adj) hu₁_adj hu₁'_adj)
          have hu₂'_u₃'_nonadj : adj u₂' u₃' = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃', u₃, v₀, u₂, u₂'] (by simp)
              (path_nodup5 u₃' u₃ v₀ u₂ u₂'
                hu₃'_ne_u₃ hu₃'_ne_v₀ hu₃'_ne_u₂ hu₂'_ne_u₃'.symm
                hu₃_ne_v₀ hu₂_ne_u₃.symm hu₂'_ne_u₃.symm
                hu₂_ne_v₀.symm hu₂'_ne_v₀.symm hu₂'_ne_u₂.symm)
              (path_edges5 u₃' u₃ v₀ u₂ u₂' hu₃'_u₃
                (adj_comm u₃ v₀ |>.trans hu₃_adj) hu₂_adj hu₂'_adj)
          have hu₁_u₃'_nonadj : adj u₁ u₃' = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃', u₃, v₀, u₁] (by simp)
              (path_nodup4 u₃' u₃ v₀ u₁
                hu₃'_ne_u₃ hu₃'_ne_v₀ hu₃'_ne_u₁
                hu₃_ne_v₀ hu₁_ne_u₃.symm hu₁_ne_v₀.symm)
              (path_edges4 u₃' u₃ v₀ u₁ hu₃'_u₃
                (adj_comm u₃ v₀ |>.trans hu₃_adj) hu₁_adj)
          have hu₂_u₃'_nonadj : adj u₂ u₃' = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃', u₃, v₀, u₂] (by simp)
              (path_nodup4 u₃' u₃ v₀ u₂
                hu₃'_ne_u₃ hu₃'_ne_v₀ hu₃'_ne_u₂
                hu₃_ne_v₀ hu₂_ne_u₃.symm hu₂_ne_v₀.symm)
              (path_edges4 u₃' u₃ v₀ u₂ hu₃'_u₃
                (adj_comm u₃ v₀ |>.trans hu₃_adj) hu₂_adj)
          -- Embedding φ : Fin 7 → Fin n
          let φ_fun : Fin 7 → Fin n := fun i =>
            match i with
            | ⟨0, _⟩ => v₀  | ⟨1, _⟩ => u₁  | ⟨2, _⟩ => u₁'
            | ⟨3, _⟩ => u₂  | ⟨4, _⟩ => u₂' | ⟨5, _⟩ => u₃ | ⟨6, _⟩ => u₃'
          have φ_inj : Function.Injective φ_fun := by
            intro i j hij; simp only [φ_fun] at hij
            fin_cases i <;> fin_cases j <;>
              first | rfl | (exact absurd hij ‹_›) | (exact absurd hij.symm ‹_›)
          let φ : Fin 7 ↪ Fin n := ⟨φ_fun, φ_inj⟩
          have hembed : ∀ i j, etilde6Adj i j = adj (φ i) (φ j) := by
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp only [etilde6Adj, φ, φ_fun] <;> norm_num <;>
              linarith [hdiag v₀, hdiag u₁, hdiag u₁', hdiag u₂, hdiag u₂',
                        hdiag u₃, hdiag u₃',
                        adj_comm v₀ u₁, adj_comm v₀ u₂, adj_comm v₀ u₃,
                        adj_comm u₁ u₁', adj_comm u₂ u₂', adj_comm u₃ u₃',
                        adj_comm u₁ u₂, adj_comm u₁ u₃, adj_comm u₂ u₃,
                        adj_comm v₀ u₁', adj_comm v₀ u₂', adj_comm v₀ u₃',
                        adj_comm u₁' u₂, adj_comm u₁' u₃, adj_comm u₂' u₁,
                        adj_comm u₂' u₃, adj_comm u₃' u₁, adj_comm u₃' u₂,
                        adj_comm u₁' u₂', adj_comm u₁' u₃', adj_comm u₂' u₃',
                        adj_comm u₁ u₃', adj_comm u₂ u₃']
          exact subgraph_infinite_type_transfer_per_kQ φ F Q
            (etilde6_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
              (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

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
