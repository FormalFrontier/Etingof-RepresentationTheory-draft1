import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericD5Tilde
import EtingofRepresentationTheory.Chapter6.FieldGenericETilde6
import EtingofRepresentationTheory.Chapter6.FieldGenericETilde7
import EtingofRepresentationTheory.Chapter6.FieldGenericT125

/-!
# Orientation-Generic Non-Adjacent Branches Leaf-Case (sub-A1 of #2919 / #2877)

Per-(F, Q) leaf-neighbour helper for the non-adjacent branches case of the
infinite-type dispatch. Mirrors the inline `leaf_case` at
`Chapter6/InfiniteTypeConstructions.lean:9770-10316` inside
`non_adjacent_branches_infinite_type` — but with a different embedding
strategy.

## Why a different strategy

The universal `leaf_case` embeds `D̃_{k+5}` where `k = chain.length - 2`
varies with the host graph's chain length and dispatches to
`dTilde_not_finite_type` (parameterised over `n`). The per-(F, Q)
forbidden-subgraph library on `main` has no `dTilde_not_finite_type_per_kQ`
for general `n` — only the fixed-`n` leaves
`d5tilde_not_finite_type_per_kQ` (`FieldGenericD5Tilde.lean:999`),
`etilde6_not_finite_type_per_kQ` (`FieldGenericETilde6.lean:319`),
`etilde7_not_finite_type_per_kQ` (`FieldGenericETilde7.lean:301`), and
`t125_not_finite_type_per_kQ` (`FieldGenericT125.lean:39`), plus the
shared embedding helper `embed_t125_in_tree_per_kQ`
(`FieldGenericT125.lean:71`).

The per-(F, Q) port must therefore case-split on chain length and arm
extensions and embed one of the available fixed-shape forbidden
subgraphs (`Ẽ₆`, `Ẽ₇`, `T(1, 2, 5)`).

## API stub

This file introduces `non_adjacent_branches_leaf_case_per_kQ` as an
**API stub** with a `sorry` body so that the outer assembly
`non_adjacent_branches_infinite_type_per_kQ` (issue #2923) can dispatch
to it by name. The actual proof — chain extraction, side / arm
extraction, distinctness lattice, and the case-split on
`(chain.length, side.deg, arm₁.deg, arm₂.deg)` with the corresponding
embeddings — is tracked by a follow-up issue.

Mirrors the API-stub precedent set by `t125_not_finite_type_per_kQ`
(`FieldGenericT125.lean:39`, introduced by issue #2875 with body
deferred to #2793).
-/

open scoped Matrix

namespace Etingof

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) leaf-neighbour helper for the non-adjacent
branches case: given two degree-3 branch vertices `v₀, w` of a connected
acyclic simple graph (all degrees `< 4`), with `v₀, w` non-adjacent, all
of `v₀`'s neighbours of degree `< 3`, all of `w`'s neighbours of
degree `< 3`, and one specified neighbour `leaf` of `v₀` having degree
`1`, the dimension-vector set of indecomposable representations is
infinite for every algebraically closed `F` and every orientation `Q`
of `adj`.

Mirrors the inline `leaf_case` at
`Chapter6/InfiniteTypeConstructions.lean:9770` inside
`non_adjacent_branches_infinite_type`, but with the embedding strategy
adapted to the per-(F, Q) forbidden-subgraph library on `main`
(no `dTilde_not_finite_type_per_kQ` for general `n`). See the file
docstring for the strategy.

The two hypotheses `h_no_adj_branch` (on `v₀`'s neighbours) and
`h_no_adj_branch_w` (on `w`'s neighbours) are both implied by the
"no two adjacent degree-3 vertices anywhere" assumption that holds in
the outer assembly `non_adjacent_branches_infinite_type_per_kQ`
(issue #2923) — the caller derives them from the negated existential
`h_adj_exists` before invoking this helper.

**API stub** (issue #2922): the body is `sorry` pending the proof
tracked by issue #2932 and its sub-issues. The signature exists so
that the outer assembly `non_adjacent_branches_infinite_type_per_kQ`
(issue #2923) can dispatch to it by name. -/
theorem non_adjacent_branches_leaf_case_per_kQ {n : ℕ}
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
    (v₀ w : Fin n) (hv₀ : vertexDegree adj v₀ = 3)
    (hw : vertexDegree adj w = 3) (hne : w ≠ v₀)
    (h_no_adj_branch : ∀ u, adj v₀ u = 1 → vertexDegree adj u < 3)
    (h_no_adj_branch_w : ∀ u, adj w u = 1 → vertexDegree adj u < 3)
    (h_v₀w_nonadj : adj v₀ w ≠ 1)
    (leaf : Fin n) (h_leaf_adj : adj v₀ leaf = 1)
    (h_leaf_deg : vertexDegree adj leaf = 1)
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- Phase 1: setup. Port of `InfiniteTypeConstructions.lean:9707-10120`
  -- adapted to the per-(F, Q) signature (h_v₀w_nonadj is a direct
  -- hypothesis here; S₀/Sw and the universal helpers are inlined).
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have ne_of_adj : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  -- Extract v₀'s 3 neighbours into S₀
  set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1) with hS₀_def
  have hS₀_card : S₀.card = 3 := hv₀
  -- Get a Nodup path from v₀ to w (via hconn + walk trimming).
  -- chain = [v₀, c₁, ..., c_{d-1}, w] with length ≥ 3 (since non-adjacent)
  obtain ⟨chain, hchain_head, hchain_last, hchain_nodup, hchain_len, hchain_edges⟩ :
    ∃ chain : List (Fin n), chain.head? = some v₀ ∧ chain.getLast? = some w ∧
      chain.Nodup ∧ 3 ≤ chain.length ∧
      ∀ t, (ht : t + 1 < chain.length) →
        adj (chain.get ⟨t, by omega⟩) (chain.get ⟨t + 1, ht⟩) = 1 := by
    obtain ⟨walk, hwh, hwl, hwe⟩ := hconn v₀ w
    obtain ⟨spath, hsh, hsl, hsd, hslen, hse⟩ :=
      walk_to_nodup_path adj walk hwh hwl hne.symm hwe
    refine ⟨spath, hsh, hsl, hsd, ?_, hse⟩
    by_contra hlt; push_neg at hlt
    have hlen2 : spath.length = 2 := by omega
    have h01' := hse 0 (by omega)
    have hfirst : spath.get ⟨0, by omega⟩ = v₀ := by
      cases spath with
      | nil => simp at hlen2
      | cons a _ => simpa using hsh
    have hsecond : spath.get ⟨1, by omega⟩ = w := by
      cases spath with
      | nil => simp at hlen2
      | cons a t =>
        cases t with
        | nil => simp at hlen2
        | cons b u =>
          cases u with
          | nil => simpa using hsl
          | cons _ _ => simp [List.length] at hlen2
    rw [hfirst, hsecond] at h01'
    exact h_v₀w_nonadj h01'
  -- chain[0] = v₀, chain[last] = w
  have hchain_ne : chain ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hchain_first : chain.get ⟨0, by omega⟩ = v₀ := by
    cases chain with
    | nil => exact absurd rfl hchain_ne
    | cons a t => simpa using hchain_head
  have hchain_last' : chain.getLast hchain_ne = w := by
    rw [List.getLast?_eq_some_getLast hchain_ne] at hchain_last
    exact Option.some_injective _ hchain_last
  -- chain[1] is adjacent to v₀ and distinct from it
  have hc1_adj : adj v₀ (chain.get ⟨1, by omega⟩) = 1 := by
    rw [← hchain_first]; exact hchain_edges 0 (by omega)
  -- leaf ≠ chain[1] (leaf has degree 1, but chain[1] connects to chain[2] and v₀)
  have hleaf_ne_c1 : leaf ≠ chain.get ⟨1, by omega⟩ := by
    intro heq
    have hc1c2_adj : adj (chain.get ⟨1, by omega⟩) (chain.get ⟨2, by omega⟩) = 1 :=
      hchain_edges 1 (by omega)
    have hc2_ne_v₀ : chain.get ⟨2, by omega⟩ ≠ v₀ := by
      rw [← hchain_first]; intro h
      exact absurd ((hchain_nodup.get_inj_iff).mp h) (by simp)
    have : 2 ≤ vertexDegree adj leaf := by
      rw [heq]; unfold vertexDegree
      have hv₀_in : v₀ ∈ Finset.univ.filter (fun j => adj (chain.get ⟨1, by omega⟩) j = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm _ _).trans hc1_adj⟩
      have hc2_in : chain.get ⟨2, by omega⟩ ∈
          Finset.univ.filter (fun j => adj (chain.get ⟨1, by omega⟩) j = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1c2_adj⟩
      have hsub : {v₀, chain.get ⟨2, by omega⟩} ⊆
          Finset.univ.filter (fun j => adj (chain.get ⟨1, by omega⟩) j = 1) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hc2_ne_v₀.symm] at this
      exact this
    omega
  -- v₀ has exactly 3 neighbours. leaf and chain[1] are two of them.
  -- The third is the "side arm" start.
  have hleaf_in_S₀ : leaf ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_leaf_adj⟩
  have hc1_in_S₀ : chain.get ⟨1, by omega⟩ ∈ S₀ :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1_adj⟩
  have hS₀_remove2 : ((S₀.erase leaf).erase (chain.get ⟨1, by omega⟩)).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hleaf_ne_c1.symm, hc1_in_S₀⟩)]
    rw [Finset.card_erase_of_mem hleaf_in_S₀, hS₀_card]
  obtain ⟨side_arm, hside_eq⟩ := Finset.card_eq_one.mp hS₀_remove2
  have hside_mem : side_arm ∈ (S₀.erase leaf).erase (chain.get ⟨1, by omega⟩) :=
    hside_eq ▸ Finset.mem_singleton_self _
  have hside_adj : adj v₀ side_arm = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hside_mem))).2
  have hside_ne_leaf : side_arm ≠ leaf :=
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hside_mem)
  have hside_ne_c1 : side_arm ≠ chain.get ⟨1, by omega⟩ :=
    Finset.ne_of_mem_erase hside_mem
  -- Extract w's two non-chain neighbours (arm₁, arm₂)
  have hw_get : w = chain.get ⟨chain.length - 1, by omega⟩ := by
    rw [← hchain_last']; simp [List.getLast_eq_getElem]
  have hclast_idx : chain.get ⟨chain.length - 2, by omega⟩ ≠ w := by
    rw [hw_get]; intro h
    exact absurd ((hchain_nodup.get_inj_iff).mp h) (by simp; omega)
  have hw_chain_adj : adj w (chain.get ⟨chain.length - 2, by omega⟩) = 1 := by
    rw [adj_comm, hw_get]
    have := hchain_edges (chain.length - 2) (by omega)
    have h_nat : chain.length - 2 + 1 = chain.length - 1 := by omega
    rw [show chain.get ⟨chain.length - 2 + 1, _⟩ =
          chain.get ⟨chain.length - 1, by omega⟩ from by congr 1; exact Fin.ext h_nat] at this
    exact this
  set Sw := Finset.univ.filter (fun j => adj w j = 1) with hSw_def
  have hSw_card : Sw.card = 3 := hw
  have hpre_in_Sw : chain.get ⟨chain.length - 2, by omega⟩ ∈ Sw :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_chain_adj⟩
  have hSw_erase : (Sw.erase (chain.get ⟨chain.length - 2, by omega⟩)).card = 2 := by
    rw [Finset.card_erase_of_mem hpre_in_Sw, hSw_card]
  obtain ⟨arm₁, arm₂, harm₁₂, hSw_eq⟩ := Finset.card_eq_two.mp hSw_erase
  have harm₁_mem : arm₁ ∈ Sw.erase (chain.get ⟨chain.length - 2, by omega⟩) :=
    hSw_eq ▸ Finset.mem_insert_self arm₁ _
  have harm₂_mem : arm₂ ∈ Sw.erase (chain.get ⟨chain.length - 2, by omega⟩) :=
    hSw_eq ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self arm₂))
  have harm₁_adj : adj w arm₁ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase harm₁_mem)).2
  have harm₂_adj : adj w arm₂ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase harm₂_mem)).2
  have harm₁_ne_pre : arm₁ ≠ chain.get ⟨chain.length - 2, by omega⟩ :=
    Finset.ne_of_mem_erase harm₁_mem
  have harm₂_ne_pre : arm₂ ≠ chain.get ⟨chain.length - 2, by omega⟩ :=
    Finset.ne_of_mem_erase harm₂_mem
  -- Convenience adjacency facts
  have leaf_adj_v₀ : adj leaf v₀ = 1 := (adj_comm leaf v₀).trans h_leaf_adj
  have side_adj_v₀ : adj side_arm v₀ = 1 := (adj_comm side_arm v₀).trans hside_adj
  have arm₁_adj_w : adj arm₁ w = 1 := (adj_comm arm₁ w).trans harm₁_adj
  have arm₂_adj_w : adj arm₂ w = 1 := (adj_comm arm₂ w).trans harm₂_adj
  have leaf_ne_v₀ : leaf ≠ v₀ := (ne_of_adj v₀ leaf h_leaf_adj).symm
  have side_ne_v₀ : side_arm ≠ v₀ := (ne_of_adj v₀ side_arm hside_adj).symm
  have arm₁_ne_w : arm₁ ≠ w := (ne_of_adj w arm₁ harm₁_adj).symm
  have arm₂_ne_w : arm₂ ≠ w := (ne_of_adj w arm₂ harm₂_adj).symm
  -- chain[last] = w
  have hchain_get_last : chain.get ⟨chain.length - 1, by omega⟩ = w := by
    conv_rhs => rw [← hchain_last']
    simp [List.getLast_eq_getElem]
  -- leaf's only neighbour is v₀
  have leaf_only : ∀ x, adj leaf x = 1 → x = v₀ := by
    intro x hx
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_leaf_deg
    have h1 : v₀ = a := Finset.mem_singleton.mp (ha ▸ Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, leaf_adj_v₀⟩)
    exact (Finset.mem_singleton.mp (ha ▸ Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hx⟩)).trans h1.symm
  -- Distinctness: leaf ∉ chain
  have leaf_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
      leaf ≠ chain.get ⟨idx, hidx⟩ := by
    intro idx hidx heq
    by_cases h0 : idx = 0
    · subst h0; rw [hchain_first] at heq; exact leaf_ne_v₀ heq
    · by_cases h1 : idx = 1
      · subst h1; exact hleaf_ne_c1 heq
      · have hedge : adj (chain.get ⟨idx - 1, by omega⟩)
            (chain.get ⟨idx, hidx⟩) = 1 := by
          have h_nat : idx - 1 + 1 = idx := by omega
          have h := hchain_edges (idx - 1) (by omega)
          rwa [show chain.get ⟨idx - 1 + 1, by omega⟩ =
            chain.get ⟨idx, hidx⟩ from by congr 1; exact Fin.ext h_nat] at h
        rw [← heq] at hedge
        have := leaf_only _ ((adj_comm _ _).trans hedge)
        rw [← hchain_first] at this
        exact absurd ((hchain_nodup.get_inj_iff).mp this) (by simp; omega)
  -- Distinctness: side_arm ∉ chain (uses acyclicity for idx ≥ 2)
  have side_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
      side_arm ≠ chain.get ⟨idx, hidx⟩ := by
    intro idx hidx heq
    by_cases h0 : idx = 0
    · subst h0; rw [hchain_first] at heq; exact side_ne_v₀ heq
    · by_cases h1 : idx = 1
      · subst h1; exact hside_ne_c1 heq
      · exfalso
        have h_back : adj (chain.get ⟨idx, hidx⟩) (chain.get ⟨0, by omega⟩) = 1 := by
          rw [← heq, hchain_first]; exact side_adj_v₀
        have h_nonadj := acyclic_path_nonadj adj hsymm h01 h_acyclic
          (chain.take (idx + 1))
          (by rw [List.length_take_of_le (by omega)]; omega)
          (hchain_nodup.sublist (List.take_sublist _ _))
          (fun t ht => by
            rw [List.length_take_of_le (by omega)] at ht
            have ht1 : t + 1 < chain.length := by omega
            have hgt : (chain.take (idx + 1)).get ⟨t, by
                rw [List.length_take_of_le (by omega)]; omega⟩ =
                chain.get ⟨t, by omega⟩ := by
              simp only [List.get_eq_getElem, List.getElem_take]
            have hgt1 : (chain.take (idx + 1)).get ⟨t + 1, by
                rw [List.length_take_of_le (by omega)]; exact ht⟩ =
                chain.get ⟨t + 1, ht1⟩ := by
              simp only [List.get_eq_getElem, List.getElem_take]
            rw [hgt, hgt1]; exact hchain_edges t ht1)
        have hlast : (chain.take (idx + 1)).getLast
            (List.ne_nil_of_length_pos (by
              rw [List.length_take_of_le (by omega)]; omega)) =
            chain.get ⟨idx, hidx⟩ := by
          simp only [List.getLast_eq_getElem, List.get_eq_getElem,
            List.length_take_of_le (by omega : idx + 1 ≤ chain.length),
            show idx + 1 - 1 = idx from by omega, List.getElem_take]
        have hfirst : (chain.take (idx + 1)).get ⟨0, by
            rw [List.length_take_of_le (by omega)]; omega⟩ =
            chain.get ⟨0, by omega⟩ := by
          simp only [List.get_eq_getElem, List.getElem_take]
        rw [hlast, hfirst] at h_nonadj
        linarith
  -- Distinctness: arm₁ ∉ chain
  have arm₁_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
      arm₁ ≠ chain.get ⟨idx, hidx⟩ := by
    intro idx hidx heq
    by_cases hlast : idx = chain.length - 1
    · subst hlast; rw [hchain_get_last] at heq; exact arm₁_ne_w heq
    · by_cases hpre : idx = chain.length - 2
      · subst hpre; exact harm₁_ne_pre heq
      · exfalso
        have h_back : adj (chain.get ⟨chain.length - 1, by omega⟩)
            (chain.get ⟨idx, hidx⟩) = 1 := by
          rw [hchain_get_last, ← heq]; exact harm₁_adj
        have h_nonadj := acyclic_path_nonadj adj hsymm h01 h_acyclic
          (chain.drop idx)
          (by rw [List.length_drop]; omega)
          (hchain_nodup.sublist (List.drop_sublist _ _))
          (fun t ht => by
            rw [List.length_drop] at ht
            have ht1 : idx + t + 1 < chain.length := by omega
            have hgt : (chain.drop idx).get ⟨t, by rw [List.length_drop]; omega⟩ =
                chain.get ⟨idx + t, by omega⟩ := by
              simp only [List.get_eq_getElem, List.getElem_drop]
            have hgt1 : (chain.drop idx).get ⟨t + 1, by rw [List.length_drop]; exact ht⟩ =
                chain.get ⟨idx + t + 1, ht1⟩ := by
              simp only [List.get_eq_getElem, List.getElem_drop]
              rfl
            rw [hgt, hgt1]; exact hchain_edges (idx + t) (by omega))
        have hlast' : (chain.drop idx).getLast
            (List.ne_nil_of_length_pos (by rw [List.length_drop]; omega)) =
            chain.get ⟨chain.length - 1, by omega⟩ := by
          rw [List.getLast_drop, List.getLast_eq_getElem, List.get_eq_getElem]
        have hfirst : (chain.drop idx).get ⟨0, by rw [List.length_drop]; omega⟩ =
            chain.get ⟨idx, hidx⟩ := by
          simp only [List.get_eq_getElem, List.getElem_drop, Nat.add_zero]
        rw [hlast', hfirst] at h_nonadj
        linarith
  -- Distinctness: arm₂ ∉ chain
  have arm₂_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
      arm₂ ≠ chain.get ⟨idx, hidx⟩ := by
    intro idx hidx heq
    by_cases hlast : idx = chain.length - 1
    · subst hlast; rw [hchain_get_last] at heq; exact arm₂_ne_w heq
    · by_cases hpre : idx = chain.length - 2
      · subst hpre; exact harm₂_ne_pre heq
      · exfalso
        have h_back : adj (chain.get ⟨chain.length - 1, by omega⟩)
            (chain.get ⟨idx, hidx⟩) = 1 := by
          rw [hchain_get_last, ← heq]; exact harm₂_adj
        have h_nonadj := acyclic_path_nonadj adj hsymm h01 h_acyclic
          (chain.drop idx)
          (by rw [List.length_drop]; omega)
          (hchain_nodup.sublist (List.drop_sublist _ _))
          (fun t ht => by
            rw [List.length_drop] at ht
            have ht1 : idx + t + 1 < chain.length := by omega
            have hgt : (chain.drop idx).get ⟨t, by rw [List.length_drop]; omega⟩ =
                chain.get ⟨idx + t, by omega⟩ := by
              simp only [List.get_eq_getElem, List.getElem_drop]
            have hgt1 : (chain.drop idx).get ⟨t + 1, by rw [List.length_drop]; exact ht⟩ =
                chain.get ⟨idx + t + 1, ht1⟩ := by
              simp only [List.get_eq_getElem, List.getElem_drop]
              rfl
            rw [hgt, hgt1]; exact hchain_edges (idx + t) (by omega))
        have hlast' : (chain.drop idx).getLast
            (List.ne_nil_of_length_pos (by rw [List.length_drop]; omega)) =
            chain.get ⟨chain.length - 1, by omega⟩ := by
          rw [List.getLast_drop, List.getLast_eq_getElem, List.get_eq_getElem]
        have hfirst : (chain.drop idx).get ⟨0, by rw [List.length_drop]; omega⟩ =
            chain.get ⟨idx, hidx⟩ := by
          simp only [List.get_eq_getElem, List.getElem_drop, Nat.add_zero]
        rw [hlast', hfirst] at h_nonadj
        linarith
  -- Cross-region distinctness: leaf ≠ arm₁, leaf ≠ arm₂
  have hleaf_ne_arm₁ : leaf ≠ arm₁ := by
    intro heq; have := leaf_only w (heq ▸ arm₁_adj_w); exact hne this
  have hleaf_ne_arm₂ : leaf ≠ arm₂ := by
    intro heq; have := leaf_only w (heq ▸ arm₂_adj_w); exact hne this
  -- side_arm ≠ arm₁, side_arm ≠ arm₂ (cycle via chain contradicts acyclicity)
  have side_arm_ne_arm : ∀ (arm : Fin n), adj w arm = 1 →
      (∀ (idx : ℕ) (hidx : idx < chain.length), arm ≠ chain.get ⟨idx, hidx⟩) →
      side_arm ≠ arm := by
    intro arm harm_adj harm_ne_chain heq
    -- chain ++ [side_arm] is a cycle: last→first edge is side_arm→v₀
    apply h_acyclic (chain ++ [side_arm])
      (by simp [List.length]; omega)
    · -- Nodup
      rw [List.nodup_append]
      refine ⟨hchain_nodup, List.nodup_singleton _, ?_⟩
      intro x hx1 y hy
      simp only [List.mem_singleton] at hy
      subst hy
      obtain ⟨⟨i, hi⟩, heq'⟩ := List.mem_iff_get.mp hx1
      exact heq' ▸ (side_ne_chain i hi).symm
    · -- Consecutive edges
      intro t ht
      simp only [List.length_append, List.length_singleton] at ht
      by_cases ht' : t + 1 < chain.length
      · have hge1 : (chain ++ [side_arm]).get ⟨t, by omega⟩ = chain.get ⟨t, by omega⟩ := by
          simp only [List.get_eq_getElem]; exact List.getElem_append_left (by omega)
        have hge2 : (chain ++ [side_arm]).get ⟨t + 1, by omega⟩ = chain.get ⟨t + 1, ht'⟩ := by
          simp only [List.get_eq_getElem]; exact List.getElem_append_left ht'
        rw [hge1, hge2]; exact hchain_edges t ht'
      · have htv : t = chain.length - 1 := by omega
        subst htv
        have hge1 : (chain ++ [side_arm]).get ⟨chain.length - 1, by omega⟩ =
            chain.get ⟨chain.length - 1, by omega⟩ := by
          simp only [List.get_eq_getElem]; exact List.getElem_append_left (by omega)
        have hge2 : (chain ++ [side_arm]).get ⟨chain.length - 1 + 1, by omega⟩ = side_arm := by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_right (by omega)]
          simp [show chain.length - 1 + 1 - chain.length = 0 from by omega]
        rw [hge1, hge2, hchain_get_last, heq]; exact harm_adj
    · -- Back-edge: adj side_arm v₀ = 1, contradiction
      have hlast' : (chain ++ [side_arm]).getLast
          (List.ne_nil_of_length_pos (by simp)) = side_arm := by
        rw [List.getLast_append_of_ne_nil (by simp) (by simp)]
        simp
      have hfirst : (chain ++ [side_arm]).get ⟨0, by simp⟩ =
          chain.get ⟨0, by omega⟩ := by
        simp only [List.get_eq_getElem]
        exact List.getElem_append_left (by omega)
      rw [hlast', hfirst, hchain_first]; exact side_adj_v₀
  have hside_ne_arm₁ : side_arm ≠ arm₁ := side_arm_ne_arm arm₁ harm₁_adj arm₁_ne_chain
  have hside_ne_arm₂ : side_arm ≠ arm₂ := side_arm_ne_arm arm₂ harm₂_adj arm₂_ne_chain
  -- Phase 2: case-split on
  -- `(chain.length, vertexDegree adj side_arm, vertexDegree adj arm₁,
  -- vertexDegree adj arm₂)` and dispatch to one of the per-(F, Q)
  -- embedders. Cases (from the parent issue #2951):
  --
  -- * Case A — `6 ≤ chain.length ∧ vertexDegree adj side_arm = 2`:
  --   embed T(1, 2, 5) centred at `v₀` and dispatch to
  --   `embed_t125_in_tree_per_kQ`. **Implemented here.**
  -- * Case B — `6 ≤ chain.length ∧
  --   (vertexDegree adj arm₁ = 2 ∨ vertexDegree adj arm₂ = 2)`:
  --   embed T(1, 2, 5) centred at `w` (symmetric to A). **Sub-issue.**
  -- * Case C — `4 ≤ chain.length < 6 ∧ vertexDegree adj side_arm = 2`:
  --   embed Ẽ₇ = T(1, 3, 3) centred at `v₀` and dispatch to
  --   `embed_etilde7_in_tree_per_kQ`. **Sub-issue.**
  -- * Case D — `4 ≤ chain.length < 6 ∧ vertexDegree adj arm₁ = 2 ∧
  --   vertexDegree adj arm₂ = 2`: embed Ẽ₆ = T(2, 2, 2) centred at `w`
  --   and dispatch to `embed_etilde6_in_tree_per_kQ`. **Sub-issue.**
  -- * Case E — `chain.length = 3`: dispatch to a D̃₅-style embedding via
  --   `d5tilde_not_finite_type_per_kQ`. **Sub-issue.**
  by_cases hA : 6 ≤ chain.length ∧ vertexDegree adj side_arm = 2
  · -- ===== Case A: T(1, 2, 5) centred at v₀ =====
    obtain ⟨hlen6, hside_deg2⟩ := hA
    -- Extract `x`: side_arm's unique non-v₀ neighbour
    set Sside := Finset.univ.filter (fun j => adj side_arm j = 1) with hSside_def
    have hSside_card : Sside.card = 2 := hside_deg2
    have hv₀_in_Sside : v₀ ∈ Sside :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (adj_comm side_arm v₀).trans hside_adj⟩
    have hSside_erase : (Sside.erase v₀).card = 1 := by
      rw [Finset.card_erase_of_mem hv₀_in_Sside, hSside_card]
    obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hSside_erase
    have hx_mem : x ∈ Sside.erase v₀ :=
      hx_eq ▸ Finset.mem_singleton_self _
    have hx_adj : adj side_arm x = 1 :=
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase hx_mem)).2
    have hx_ne_v₀ : x ≠ v₀ := Finset.ne_of_mem_erase hx_mem
    -- Adjacency facts on chain[1..5] from `hchain_edges`
    have hc12 : adj (chain.get ⟨1, by omega⟩) (chain.get ⟨2, by omega⟩) = 1 :=
      hchain_edges 1 (by omega)
    have hc23 : adj (chain.get ⟨2, by omega⟩) (chain.get ⟨3, by omega⟩) = 1 :=
      hchain_edges 2 (by omega)
    have hc34 : adj (chain.get ⟨3, by omega⟩) (chain.get ⟨4, by omega⟩) = 1 :=
      hchain_edges 3 (by omega)
    have hc45 : adj (chain.get ⟨4, by omega⟩) (chain.get ⟨5, by omega⟩) = 1 :=
      hchain_edges 4 (by omega)
    -- Distinctness facts on chain[i] vs v₀ / chain[j] (from `hchain_nodup`)
    have hc2_ne_v₀ : chain.get ⟨2, by omega⟩ ≠ v₀ := by
      rw [← hchain_first]; intro h
      exact absurd (hchain_nodup.get_inj_iff.mp h) (by simp)
    have hc3_ne_c1 : chain.get ⟨3, by omega⟩ ≠ chain.get ⟨1, by omega⟩ := by
      intro h; exact absurd (hchain_nodup.get_inj_iff.mp h) (by simp)
    have hc4_ne_c2 : chain.get ⟨4, by omega⟩ ≠ chain.get ⟨2, by omega⟩ := by
      intro h; exact absurd (hchain_nodup.get_inj_iff.mp h) (by simp)
    have hc5_ne_c3 : chain.get ⟨5, by omega⟩ ≠ chain.get ⟨3, by omega⟩ := by
      intro h; exact absurd (hchain_nodup.get_inj_iff.mp h) (by simp)
    -- Dispatch to `embed_t125_in_tree_per_kQ`.
    -- Vertex map: 0→v₀, 1→leaf (length-1 arm), 2→side_arm, 3→x
    -- (length-2 arm), 4→chain[1], 5→chain[2], 6→chain[3], 7→chain[4],
    -- 8→chain[5] (length-5 arm).
    exact embed_t125_in_tree_per_kQ adj hsymm hdiag h01 h_acyclic
      v₀ leaf side_arm x
      (chain.get ⟨1, by omega⟩) (chain.get ⟨2, by omega⟩)
      (chain.get ⟨3, by omega⟩) (chain.get ⟨4, by omega⟩)
      (chain.get ⟨5, by omega⟩)
      h_leaf_adj hside_adj hx_adj
      hc1_adj hc12 hc23 hc34 hc45
      hside_ne_leaf.symm hleaf_ne_c1 hside_ne_c1
      hx_ne_v₀ hc2_ne_v₀ hc3_ne_c1 hc4_ne_c2 hc5_ne_c3
      F Q hOrient
  · -- ===== Cases B, C, D, E — sub-issues =====
    -- TODO (sub-issues of #2951): implement the remaining cases.
    -- See the case enumeration above. Phase 1 setup and the Case A
    -- exclusion `¬(6 ≤ chain.length ∧ vertexDegree adj side_arm = 2)`
    -- are in scope.
    let _ := hn; let _ := h_deg; let _ := h_no_adj_branch
    let _ := h_no_adj_branch_w; let _ := hOrient
    let _ := hleaf_ne_arm₁; let _ := hleaf_ne_arm₂
    let _ := hside_ne_arm₁; let _ := hside_ne_arm₂
    let _ := leaf_ne_chain; let _ := arm₂_ne_chain
    sorry

end Etingof
