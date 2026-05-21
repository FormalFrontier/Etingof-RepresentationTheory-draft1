import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericETilde6
import EtingofRepresentationTheory.Chapter6.FieldGenericETilde7
import EtingofRepresentationTheory.Chapter6.FieldGenericT125

/-!
# Orientation-Generic T(p,q,r) Single-Branch Construction (sub D2.single of #2877)

Per-(F, Q) wrapper around `single_branch_not_posdef_infinite_type`
(`InfiniteTypeConstructions.lean:8401`): a connected acyclic simple
graph with a unique degree-3 vertex (a T(p, q, r) tree) and non-positive-
definite Cartan form has infinite representation type for every
algebraically closed `F` and every orientation `Q`. The proof case-splits
on whether all three arms have length ≥ 2:

* All three arms ≥ 2 → embed Ẽ₆ = T(2, 2, 2) and dispatch to
  `etilde6_not_finite_type_per_kQ` via `subgraph_infinite_type_transfer_per_kQ`.
* Some arm is a leaf → delegate to `single_branch_leaf_case_per_kQ`,
  which case-splits on whether each of `v₀`'s non-leaf neighbours `a₂`,
  `a₃` has degree 2: if both extend, dispatch to
  `single_branch_leaf_case_both_extend_per_kQ` (still an API stub,
  tracked by the #2905 sub-chain #2907 / #2908 / #2909 / #2910); if
  either `a₂` or `a₃` is itself a leaf, the graph is a D-type tree and
  the Cartan form is positive definite by `tree_two_leaf_posdef`,
  contradicting `h_not_posdef`.

The remaining API stub in this file is
`single_branch_leaf_case_both_extend_per_kQ` (line 1240) — the body is
`sorry`, tracked by the #2905 sub-chain.

Audit-pattern recipe (per
`progress/reviews/2026-05-18-degree4-per-kQ-placement.md`): the per-(F, Q)
wrapper carries `[IsAlgClosed F]` because the dispatch leaves
(`etilde6_not_finite_type_per_kQ`, `etilde7_not_finite_type_per_kQ`,
`t125_not_finite_type_per_kQ`) all carry it. Sibling wrappers landed under
the same recipe:

* `degree_ge_4_infinite_type_per_kQ` (`FieldGenericStar.lean:649`, PR #2891)
* `graph_with_list_cycle_infinite_type_per_kQ`
  (`FieldGenericCycle.lean:440`, PR #2897)
* `adjacent_branches_infinite_type_per_kQ`
  (`FieldGenericD5Tilde.lean:1043`, PR #2900)
* `non_adjacent_branches_infinite_type_per_kQ`
  (`FieldGenericAssembly.lean:75`, PR #2943)
-/

open scoped Matrix

namespace Etingof

set_option maxHeartbeats 6400000 in
-- reason: T(1,2,2) posdef proof unfolds the QF over 6 vertices via a
-- single `simp only` with ~30 distinctness facts plus extensive
-- `acyclic_path_nonadj` and `Finset.sum_insert` reasoning, pushing
-- elaboration past the default budget; mirrors the same setting on
-- `single_branch_leaf_case` (`InfiniteTypeConstructions.lean:6896`).
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of the `(b₂ degree 1, b₃ degree 1)` sub-case of
the "both arms extend" branch of `single_branch_leaf_case`
(`InfiniteTypeConstructions.lean:7964-8352`): given the T(1, 2, 2) = D₅
configuration where both `b₂` and `b₃` are leaves, the Cartan form is
positive definite — contradicting `h_not_posdef`. The proof does not
depend on `F` or `Q` substantively; those are carried through for API
consistency with the sibling sub-case helpers. -/
theorem single_branch_leaf_both_extend_t122_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
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
    (v₀ leaf a₂ a₃ b₂ b₃ : Fin n)
    (h_leaf_adj : adj v₀ leaf = 1)
    (ha₂_adj : adj v₀ a₂ = 1) (ha₃_adj : adj v₀ a₃ = 1)
    (hb₂_adj : adj a₂ b₂ = 1) (hb₃_adj : adj a₃ b₃ = 1)
    (h_leaf_deg : vertexDegree adj leaf = 1)
    (hb₂_deg1 : vertexDegree adj b₂ = 1)
    (hb₃_deg1 : vertexDegree adj b₃ = 1)
    (ha₂₃ : a₂ ≠ a₃)
    (ha₂_ne_leaf : a₂ ≠ leaf) (ha₃_ne_leaf : a₃ ≠ leaf)
    (hb₂_ne_v₀ : b₂ ≠ v₀) (hb₃_ne_v₀ : b₃ ≠ v₀)
    (hS₀_eq : (Finset.univ.filter (adj v₀ · = 1)).erase leaf = {a₂, a₃})
    (hb₂_eq : (Finset.univ.filter (adj a₂ · = 1)).erase v₀ = {b₂})
    (hb₃_eq : (Finset.univ.filter (adj a₃ · = 1)).erase v₀ = {b₃})
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x))
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  let _ := F; let _ := Q; let _ := hOrient
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have ne_of_adj' : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  have hleaf_ne_v₀ : leaf ≠ v₀ := (ne_of_adj' v₀ leaf h_leaf_adj).symm
  have ha₂_ne_v₀ : a₂ ≠ v₀ := (ne_of_adj' v₀ a₂ ha₂_adj).symm
  have ha₃_ne_v₀ : a₃ ≠ v₀ := (ne_of_adj' v₀ a₃ ha₃_adj).symm
  -- T(1,2,2) positive definiteness proof — port of
  -- `InfiniteTypeConstructions.lean:7964-8352`.
  exfalso; apply h_not_posdef
  -- Step 2: Unique neighbor lists for each vertex
  have hv₀_nbrs : ∀ j, adj v₀ j = 1 →
      j = leaf ∨ j = a₂ ∨ j = a₃ := by
    intro j hj
    by_cases hjl : j = leaf
    · exact Or.inl hjl
    · have : j ∈ (Finset.univ.filter (adj v₀ · = 1)).erase leaf :=
        Finset.mem_erase.mpr
          ⟨hjl, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      rw [hS₀_eq] at this
      rcases Finset.mem_insert.mp this with rfl | hm
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Finset.mem_singleton.mp hm))
  have hleaf_nbrs : ∀ j, adj leaf j = 1 → j = v₀ := by
    intro j hj; by_contra hne
    have : 2 ≤ vertexDegree adj leaf := by
      have h1 : v₀ ∈ Finset.univ.filter (adj leaf · = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ v₀,
          (adj_comm leaf v₀).trans h_leaf_adj⟩
      have h2 : j ∈ Finset.univ.filter (adj leaf · = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      calc 2 = ({v₀, j} : Finset _).card :=
            (Finset.card_pair (Ne.symm hne)).symm
        _ ≤ _ := Finset.card_le_card fun x hx => by
          simp only [Finset.mem_insert,
            Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
    omega
  have ha₂_nbrs : ∀ j, adj a₂ j = 1 → j = v₀ ∨ j = b₂ := by
    intro j hj
    by_cases hjv : j = v₀
    · exact Or.inl hjv
    · right
      have hmem : j ∈ (Finset.univ.filter
          (adj a₂ · = 1)).erase v₀ :=
        Finset.mem_erase.mpr
          ⟨hjv, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hj⟩⟩
      rw [hb₂_eq] at hmem
      exact Finset.mem_singleton.mp hmem
  have hb₂_nbrs : ∀ j, adj b₂ j = 1 → j = a₂ := by
    intro j hj; by_contra hne
    have : 2 ≤ vertexDegree adj b₂ := by
      have h1 : a₂ ∈ Finset.univ.filter (adj b₂ · = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ a₂,
          (adj_comm b₂ a₂).trans hb₂_adj⟩
      have h2 : j ∈ Finset.univ.filter (adj b₂ · = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      calc 2 = ({a₂, j} : Finset _).card :=
            (Finset.card_pair (Ne.symm hne)).symm
        _ ≤ _ := Finset.card_le_card fun x hx => by
          simp only [Finset.mem_insert,
            Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
    omega
  have ha₃_nbrs : ∀ j, adj a₃ j = 1 → j = v₀ ∨ j = b₃ := by
    intro j hj
    by_cases hjv : j = v₀
    · exact Or.inl hjv
    · right
      have hmem : j ∈ (Finset.univ.filter
          (adj a₃ · = 1)).erase v₀ :=
        Finset.mem_erase.mpr
          ⟨hjv, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hj⟩⟩
      rw [hb₃_eq] at hmem
      exact Finset.mem_singleton.mp hmem
  have hb₃_nbrs : ∀ j, adj b₃ j = 1 → j = a₃ := by
    intro j hj; by_contra hne
    have : 2 ≤ vertexDegree adj b₃ := by
      have h1 : a₃ ∈ Finset.univ.filter (adj b₃ · = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ a₃,
          (adj_comm b₃ a₃).trans hb₃_adj⟩
      have h2 : j ∈ Finset.univ.filter (adj b₃ · = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      calc 2 = ({a₃, j} : Finset _).card :=
            (Finset.card_pair (Ne.symm hne)).symm
        _ ≤ _ := Finset.card_le_card fun x hx => by
          simp only [Finset.mem_insert,
            Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
    omega
  -- Step 3: Named set is closed under adjacency
  have h_closed : ∀ i j,
      (i = v₀ ∨ i = leaf ∨ i = a₂ ∨ i = b₂ ∨
        i = a₃ ∨ i = b₃) →
      adj i j = 1 →
      (j = v₀ ∨ j = leaf ∨ j = a₂ ∨ j = b₂ ∨
        j = a₃ ∨ j = b₃) := by
    intro i j hi hadj
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · rcases hv₀_nbrs j hadj with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (hleaf_nbrs j hadj)
    · rcases ha₂_nbrs j hadj with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl (hb₂_nbrs j hadj)))
    · rcases ha₃_nbrs j hadj with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact .inr (.inr (.inr (.inr (.inl
        (hb₃_nbrs j hadj)))))
  -- Step 4: Every vertex is named
  have h_all_named : ∀ i : Fin n,
      i = v₀ ∨ i = leaf ∨ i = a₂ ∨ i = b₂ ∨
        i = a₃ ∨ i = b₃ := by
    intro i
    obtain ⟨path, hhead, hlast, hedges⟩ := hconn v₀ i
    have hne : path ≠ [] := by
      intro h; rw [h] at hhead; simp at hhead
    have hpos : 0 < path.length := by
      cases path with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    have h_elts : ∀ (k : ℕ) (hk : k < path.length),
        path.get ⟨k, hk⟩ = v₀ ∨
        path.get ⟨k, hk⟩ = leaf ∨
        path.get ⟨k, hk⟩ = a₂ ∨
        path.get ⟨k, hk⟩ = b₂ ∨
        path.get ⟨k, hk⟩ = a₃ ∨
        path.get ⟨k, hk⟩ = b₃ := by
      intro k
      induction k with
      | zero =>
        intro hk; left
        cases path with
        | nil => simp at hk
        | cons a _ => exact Option.some.inj hhead
      | succ k ih =>
        intro hk
        exact h_closed _ _
          (ih (by omega)) (hedges k (by omega))
    have hlast_val : path.getLast hne = i := by
      rw [List.getLast?_eq_some_getLast hne] at hlast
      exact Option.some.inj hlast
    have := h_elts (path.length - 1) (by omega)
    rwa [show path.get ⟨path.length - 1, by omega⟩ =
        path.getLast hne from by
      rw [List.getLast_eq_getElem]; rfl,
      hlast_val] at this
  -- Step 5: Additional distinctness facts
  have ha₂_ne_b₂ := ne_of_adj' a₂ b₂ hb₂_adj
  have ha₃_ne_b₃ := ne_of_adj' a₃ b₃ hb₃_adj
  have hb₂_ne_leaf : b₂ ≠ leaf := by
    intro heq
    have : adj leaf a₂ = 1 :=
      heq ▸ (adj_comm b₂ a₂).trans hb₂_adj
    exact ha₂_ne_v₀ (hleaf_nbrs a₂ this)
  have hb₃_ne_leaf : b₃ ≠ leaf := by
    intro heq
    have : adj leaf a₃ = 1 :=
      heq ▸ (adj_comm b₃ a₃).trans hb₃_adj
    exact ha₃_ne_v₀ (hleaf_nbrs a₃ this)
  have ha₃a₂_zero : adj a₃ a₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic
      [a₂, v₀, a₃]
      (by simp)
      (by simp only [List.nodup_cons, List.mem_cons,
            List.not_mem_nil, not_or,
            not_false_eq_true, List.nodup_nil,
            and_self, and_true]
          exact ⟨⟨ha₂_ne_v₀, ha₂₃⟩, Ne.symm ha₃_ne_v₀⟩)
      (by intro k hk
          have hk3 : k + 1 < 3 := by
            simpa using hk
          have : k = 0 ∨ k = 1 := by omega
          rcases this with rfl | rfl
          · exact (adj_comm a₂ v₀).trans ha₂_adj
          · exact ha₃_adj)
  have hb₂_ne_a₃ : b₂ ≠ a₃ := by
    intro heq
    have : adj a₃ a₂ = 1 :=
      heq ▸ (adj_comm b₂ a₂).trans hb₂_adj
    linarith [ha₃a₂_zero]
  have ha₂_ne_b₃ : a₂ ≠ b₃ := by
    intro heq
    have : adj a₃ a₂ = 1 := heq ▸ hb₃_adj
    linarith [ha₃a₂_zero]
  have hb₂_ne_b₃ : b₂ ≠ b₃ := by
    intro heq
    have h1 : a₂ ∈ Finset.univ.filter
        (adj b₂ · = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ a₂,
        (adj_comm b₂ a₂).trans hb₂_adj⟩
    have h2 : a₃ ∈ Finset.univ.filter
        (adj b₂ · = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ a₃,
        heq ▸ (adj_comm b₃ a₃).trans hb₃_adj⟩
    have : 2 ≤ vertexDegree adj b₂ :=
      calc 2 = ({a₂, a₃} : Finset _).card :=
            (Finset.card_pair ha₂₃).symm
        _ ≤ _ := Finset.card_le_card fun x hx => by
          simp only [Finset.mem_insert,
            Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
    omega
  -- Step 6: Finset.univ equals the 6 named vertices
  have huniv : (Finset.univ : Finset (Fin n)) =
      {v₀, leaf, a₂, b₂, a₃, b₃} := by
    ext i
    simp only [Finset.mem_univ, true_iff,
      Finset.mem_insert, Finset.mem_singleton]
    rcases h_all_named i with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp
  have h_sum : ∀ f : Fin n → ℤ,
      ∑ i, f i = f v₀ + f leaf + f a₂ +
        f b₂ + f a₃ + f b₃ := by
    intro f
    change Finset.sum Finset.univ f = _
    rw [huniv]
    rw [Finset.sum_insert (show v₀ ∉
        ({leaf, a₂, b₂, a₃, b₃} : Finset _) from by
      simp only [Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hleaf_ne_v₀,
        Ne.symm ha₂_ne_v₀, Ne.symm hb₂_ne_v₀,
        Ne.symm ha₃_ne_v₀, Ne.symm hb₃_ne_v₀⟩)]
    rw [Finset.sum_insert (show leaf ∉
        ({a₂, b₂, a₃, b₃} : Finset _) from by
      simp only [Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha₂_ne_leaf,
        Ne.symm hb₂_ne_leaf,
        Ne.symm ha₃_ne_leaf,
        Ne.symm hb₃_ne_leaf⟩)]
    rw [Finset.sum_insert (show a₂ ∉
        ({b₂, a₃, b₃} : Finset _) from by
      simp only [Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨ha₂_ne_b₂, ha₂₃, ha₂_ne_b₃⟩)]
    rw [Finset.sum_insert (show b₂ ∉
        ({a₃, b₃} : Finset _) from by
      simp only [Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨hb₂_ne_a₃, hb₂_ne_b₃⟩)]
    rw [Finset.sum_pair ha₃_ne_b₃]
    ring
  -- Step 7: adj row equations
  have hv₀_adj_eq : ∀ j,
      adj v₀ j =
        if j = leaf ∨ j = a₂ ∨ j = a₃
        then 1 else 0 := by
    intro j; split_ifs with h
    · rcases h with rfl | rfl | rfl
      · exact h_leaf_adj
      · exact ha₂_adj
      · exact ha₃_adj
    · push_neg at h; obtain ⟨h1, h2, h3⟩ := h
      rcases h01 v₀ j with h | h
      · exact h
      · exfalso
        rcases hv₀_nbrs j h with rfl | rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
        · exact h3 rfl
  have hleaf_adj_eq : ∀ j,
      adj leaf j = if j = v₀ then 1 else 0 := by
    intro j; split_ifs with h
    · rw [h]
      exact (hsymm.apply v₀ leaf).trans h_leaf_adj
    · rcases h01 leaf j with h' | h'
      · exact h'
      · exact absurd (hleaf_nbrs j h') h
  have ha₂_adj_eq : ∀ j,
      adj a₂ j =
        if j = v₀ ∨ j = b₂ then 1 else 0 := by
    intro j; split_ifs with h
    · rcases h with hj | hj
      · rw [hj]; exact (hsymm.apply v₀ a₂).trans ha₂_adj
      · rw [hj]; exact hb₂_adj
    · push_neg at h; obtain ⟨h1, h2⟩ := h
      rcases h01 a₂ j with h' | h'
      · exact h'
      · exfalso
        rcases ha₂_nbrs j h' with rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
  have hb₂_adj_eq : ∀ j,
      adj b₂ j = if j = a₂ then 1 else 0 := by
    intro j; split_ifs with h
    · rw [h]
      exact (hsymm.apply a₂ b₂).trans hb₂_adj
    · rcases h01 b₂ j with h' | h'
      · exact h'
      · exact absurd (hb₂_nbrs j h') h
  have ha₃_adj_eq : ∀ j,
      adj a₃ j =
        if j = v₀ ∨ j = b₃ then 1 else 0 := by
    intro j; split_ifs with h
    · rcases h with hj | hj
      · rw [hj]; exact (hsymm.apply v₀ a₃).trans ha₃_adj
      · rw [hj]; exact hb₃_adj
    · push_neg at h; obtain ⟨h1, h2⟩ := h
      rcases h01 a₃ j with h' | h'
      · exact h'
      · exfalso
        rcases ha₃_nbrs j h' with rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
  have hb₃_adj_eq : ∀ j,
      adj b₃ j = if j = a₃ then 1 else 0 := by
    intro j; split_ifs with h
    · rw [h]
      exact (hsymm.apply a₃ b₃).trans hb₃_adj
    · rcases h01 b₃ j with h' | h'
      · exact h'
      · exact absurd (hb₃_nbrs j h') h
  -- Step 8: Expand QF as polynomial
  intro x hx
  set V := x v₀; set L := x leaf; set A₂ := x a₂
  set B₂ := x b₂; set A₃ := x a₃; set B₃ := x b₃
  have h_qf : dotProduct x
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) =
      2 * V ^ 2 + 2 * L ^ 2 + 2 * A₂ ^ 2 +
      2 * B₂ ^ 2 + 2 * A₃ ^ 2 + 2 * B₃ ^ 2 -
      2 * V * L - 2 * V * A₂ - 2 * A₂ * B₂ -
      2 * V * A₃ - 2 * A₃ * B₃ := by
    simp only [dotProduct, Matrix.mulVec, h_sum,
      Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, hdiag,
      hv₀_adj_eq, hleaf_adj_eq, ha₂_adj_eq,
      hb₂_adj_eq, ha₃_adj_eq, hb₃_adj_eq,
      eq_self_iff_true, ite_true, ite_false,
      hleaf_ne_v₀, Ne.symm hleaf_ne_v₀,
      ha₂_ne_v₀, Ne.symm ha₂_ne_v₀,
      ha₃_ne_v₀, Ne.symm ha₃_ne_v₀,
      hb₂_ne_v₀, Ne.symm hb₂_ne_v₀,
      hb₃_ne_v₀, Ne.symm hb₃_ne_v₀,
      ha₂_ne_leaf, Ne.symm ha₂_ne_leaf,
      ha₃_ne_leaf, Ne.symm ha₃_ne_leaf,
      hb₂_ne_leaf, Ne.symm hb₂_ne_leaf,
      hb₃_ne_leaf, Ne.symm hb₃_ne_leaf,
      ha₂₃, Ne.symm ha₂₃,
      ha₂_ne_b₂, Ne.symm ha₂_ne_b₂,
      ha₂_ne_b₃, Ne.symm ha₂_ne_b₃,
      hb₂_ne_a₃, Ne.symm hb₂_ne_a₃,
      hb₂_ne_b₃, Ne.symm hb₂_ne_b₃,
      ha₃_ne_b₃, Ne.symm ha₃_ne_b₃,
      ite_mul, one_mul, zero_mul,
      true_or, or_true, false_or, or_false,
      mul_one, mul_zero, sub_zero, zero_sub]
    ring
  -- Step 9: SoS positivity from LDL^T decomposition
  rw [h_qf]
  suffices h60 :
      0 < 30 * (2 * V - L - A₂ - A₃) ^ 2 +
      10 * (3 * L - A₂ - A₃) ^ 2 +
      5 * (4 * A₂ - 3 * B₂ - 2 * A₃) ^ 2 +
      3 * (5 * B₂ - 2 * A₃) ^ 2 +
      3 * (4 * A₃ - 5 * B₃) ^ 2 +
      45 * B₃ ^ 2 by nlinarith
  by_contra h_le; push_neg at h_le
  have h_all_zero :
      2 * V - L - A₂ - A₃ = 0 ∧
      3 * L - A₂ - A₃ = 0 ∧
      4 * A₂ - 3 * B₂ - 2 * A₃ = 0 ∧
      5 * B₂ - 2 * A₃ = 0 ∧
      4 * A₃ - 5 * B₃ = 0 ∧ B₃ = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg (2 * V - L - A₂ - A₃),
      sq_nonneg (3 * L - A₂ - A₃),
      sq_nonneg (4 * A₂ - 3 * B₂ - 2 * A₃),
      sq_nonneg (5 * B₂ - 2 * A₃),
      sq_nonneg (4 * A₃ - 5 * B₃),
      sq_nonneg B₃]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h_all_zero
  have hB₃ : B₃ = 0 := h6
  have hA₃ : A₃ = 0 := by nlinarith
  have hB₂ : B₂ = 0 := by nlinarith
  have hA₂ : A₂ = 0 := by nlinarith
  have hL : L = 0 := by nlinarith
  have hV : V = 0 := by nlinarith
  apply hx; ext i
  rcases h_all_named i with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    [exact hV; exact hL; exact hA₂;
     exact hB₂; exact hA₃; exact hB₃]

set_option maxHeartbeats 6400000 in
-- reason: T(1, q, 2) case-split mirrors `InfiniteTypeConstructions.lean:7325-7639`
-- (~315 lines of port plus an inlined T(1, 2, 5) embedding); the
-- 81-case `fin_cases` adjacency proof through the `Fin 9 ↪ Fin n` embedding
-- and the bundle of `acyclic_path_nonadj`/`Finset.sum_insert` reasoning push
-- elaboration past the default budget. Same setting as on the sub-D helper
-- and on `single_branch_leaf_case` in the original source.
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of the `(b₂ degree 2, b₃ degree 1)` sub-case of the
"both arms extend" branch of `single_branch_leaf_case`
(`InfiniteTypeConstructions.lean:7325-7639`): the T(1, q, 2) configuration
with q ≥ 3 (i.e. `b₂` extends to a longer arm and `b₃` is a leaf).
Case-splits on whether `c₂`, `d₂`, `e₂` extend:

* `c₂` is a leaf (arm2 length = 3) → T(1, 3, 2) = E₇ is positive definite,
  contradicting `h_not_posdef` via `e7_tree_posdef`.
* `d₂` is a leaf (arm2 length = 4) → T(1, 4, 2) = E₈ is positive definite,
  contradicting `h_not_posdef` via `e8_posdef`.
* `d₂` extends (arm2 length ≥ 5) → the 9 vertices
  `{v₀, leaf, a₃, b₃, a₂, b₂, c₂, d₂, e₂}` form a T(1, 2, 5) = Ẽ₈ subgraph;
  dispatch to `t125_not_finite_type_per_kQ` via
  `subgraph_infinite_type_transfer_per_kQ`. -/
theorem single_branch_leaf_both_extend_b3leaf_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
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
    (v₀ : Fin n) (hv₀ : vertexDegree adj v₀ = 3)
    (h_unique : ∀ w, vertexDegree adj w = 3 → w = v₀)
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x))
    (leaf a₂ a₃ b₂ b₃ : Fin n)
    (h_leaf_adj : adj v₀ leaf = 1)
    (ha₂_adj : adj v₀ a₂ = 1) (ha₃_adj : adj v₀ a₃ = 1)
    (hb₂_adj : adj a₂ b₂ = 1) (hb₃_adj : adj a₃ b₃ = 1)
    (h_leaf_deg : vertexDegree adj leaf = 1)
    (h_a2_ext : vertexDegree adj a₂ = 2) (h_a3_ext : vertexDegree adj a₃ = 2)
    (h_b2_ext : vertexDegree adj b₂ = 2)
    (hb₃_deg1 : vertexDegree adj b₃ = 1)
    (ha₂₃ : a₂ ≠ a₃)
    (ha₂_ne_leaf : a₂ ≠ leaf) (ha₃_ne_leaf : a₃ ≠ leaf)
    (hb₂_ne_v₀ : b₂ ≠ v₀) (hb₃_ne_v₀ : b₃ ≠ v₀)
    (hS₀_eq : (Finset.univ.filter (adj v₀ · = 1)).erase leaf = {a₂, a₃})
    (hb₂_eq : (Finset.univ.filter (adj a₂ · = 1)).erase v₀ = {b₂})
    (hb₃_eq : (Finset.univ.filter (adj a₃ · = 1)).erase v₀ = {b₃})
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have ne_of_adj' : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  have h_deg_le2 : ∀ v, v ≠ v₀ → vertexDegree adj v ≤ 2 := by
    intro v hv; have h3 := h_deg v
    by_contra h; push_neg at h; exact hv (h_unique v (by omega))
  have hleaf_ne_v₀ : leaf ≠ v₀ := (ne_of_adj' v₀ leaf h_leaf_adj).symm
  have ha₂_ne_v₀ : a₂ ≠ v₀ := (ne_of_adj' v₀ a₂ ha₂_adj).symm
  have ha₃_ne_v₀ : a₃ ≠ v₀ := (ne_of_adj' v₀ a₃ ha₃_adj).symm
  have ha₂_ne_b₂ : a₂ ≠ b₂ := ne_of_adj' a₂ b₂ hb₂_adj
  have ha₃_ne_b₃ : a₃ ≠ b₃ := ne_of_adj' a₃ b₃ hb₃_adj
  set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1) with hS₀_def
  -- Extract c₂: the neighbour of b₂ other than a₂
  have extract_other := fun (v u : Fin n) (hvu : adj v u = 1)
      (hdeg2 : vertexDegree adj v = 2) =>
    let Sv := Finset.univ.filter (fun j => adj v j = 1)
    have hcard : Sv.card = 2 := hdeg2
    have hu_mem : u ∈ Sv :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu⟩
    Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem hu_mem, hcard])
  obtain ⟨c₂, hc₂_eq⟩ := extract_other b₂ a₂
    ((adj_comm b₂ a₂).trans hb₂_adj) h_b2_ext
  have hc₂_mem : c₂ ∈ (Finset.univ.filter (adj b₂ · = 1)).erase a₂ :=
    hc₂_eq ▸ Finset.mem_singleton_self c₂
  have hc₂_adj : adj b₂ c₂ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc₂_mem)).2
  have hc₂_ne_a₂ : c₂ ≠ a₂ := Finset.ne_of_mem_erase hc₂_mem
  have hb₂_ne_c₂ : b₂ ≠ c₂ := ne_of_adj' b₂ c₂ hc₂_adj
  by_cases h_c2_ext : vertexDegree adj c₂ = 2
  · -- c₂ extends (arm2 length ≥ 4): extract d₂
    obtain ⟨d₂, hd₂_eq⟩ := extract_other c₂ b₂
      ((adj_comm c₂ b₂).trans hc₂_adj) h_c2_ext
    have hd₂_mem : d₂ ∈ (Finset.univ.filter (adj c₂ · = 1)).erase b₂ :=
      hd₂_eq ▸ Finset.mem_singleton_self d₂
    have hd₂_adj : adj c₂ d₂ = 1 :=
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase hd₂_mem)).2
    have hd₂_ne_b₂ : d₂ ≠ b₂ := Finset.ne_of_mem_erase hd₂_mem
    have hc₂_ne_d₂ : c₂ ≠ d₂ := ne_of_adj' c₂ d₂ hd₂_adj
    by_cases h_d2_ext : vertexDegree adj d₂ = 2
    · -- d₂ extends (arm2 length ≥ 5): extract e₂, embed T(1, 2, 5) via the
      -- shared helper `embed_t125_in_tree_per_kQ` with renaming
      -- (v₀, u₁, p₁, p₂, q₁, q₂, q₃, q₄, q₅) ↦
      -- (v₀, leaf, a₃, b₃, a₂, b₂, c₂, d₂, e₂).
      obtain ⟨e₂, he₂_eq⟩ := extract_other d₂ c₂
        ((adj_comm d₂ c₂).trans hd₂_adj) h_d2_ext
      have he₂_mem : e₂ ∈ (Finset.univ.filter (adj d₂ · = 1)).erase c₂ :=
        he₂_eq ▸ Finset.mem_singleton_self e₂
      have he₂_adj : adj d₂ e₂ = 1 :=
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase he₂_mem)).2
      have he₂_ne_c₂ : e₂ ≠ c₂ := Finset.ne_of_mem_erase he₂_mem
      exact embed_t125_in_tree_per_kQ adj hsymm hdiag h01 h_acyclic
        v₀ leaf a₃ b₃ a₂ b₂ c₂ d₂ e₂
        h_leaf_adj ha₃_adj hb₃_adj ha₂_adj hb₂_adj hc₂_adj hd₂_adj he₂_adj
        ha₃_ne_leaf.symm ha₂_ne_leaf.symm ha₂₃.symm hb₃_ne_v₀ hb₂_ne_v₀
        hc₂_ne_a₂ hd₂_ne_b₂ he₂_ne_c₂
        F Q hOrient
    · -- d₂ is a leaf (arm2 length = 4): T(1, 4, 2) = E₈ posdef contradiction.
      -- The 8 named vertices {v₀, leaf, a₂, b₂, c₂, d₂, a₃, b₃} form an E₈ tree
      -- whose Cartan form is positive definite — contradicting `h_not_posdef`.
      exfalso
      apply h_not_posdef
      have hd₂_ne_v₀ : d₂ ≠ v₀ := by
        intro h
        have ha₂_ne_b₂' : a₂ ≠ b₂ := ne_of_adj' a₂ b₂ hb₂_adj
        have hb₂_ne_c₂' : b₂ ≠ c₂ := ne_of_adj' b₂ c₂ hc₂_adj
        have hv₀_ne_b₂ : v₀ ≠ b₂ := hb₂_ne_v₀.symm
        have hv₀_ne_c₂ : v₀ ≠ c₂ := by
          intro heq; rw [h, heq] at hd₂_adj; linarith [hdiag c₂]
        have ha₂_ne_c₂ : a₂ ≠ c₂ := hc₂_ne_a₂.symm
        have h_nonadj : adj c₂ v₀ = 0 := acyclic_path_nonadj adj hsymm h01 h_acyclic
          [v₀, a₂, b₂, c₂] (by simp)
          (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
              not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
              exact ⟨⟨ha₂_ne_v₀.symm, hv₀_ne_b₂, hv₀_ne_c₂⟩, ⟨ha₂_ne_b₂', ha₂_ne_c₂⟩, hb₂_ne_c₂'⟩)
          (by intro k hk
              have : k + 1 < 4 := by simpa using hk
              have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
              rcases this with rfl | rfl | rfl
              · exact ha₂_adj
              · exact hb₂_adj
              · exact hc₂_adj)
        have hcv : adj c₂ v₀ = 1 := by rw [← h]; exact hd₂_adj
        linarith [hcv, h_nonadj]
      have hd₂_deg_ge1 : 1 ≤ vertexDegree adj d₂ :=
        Finset.card_pos.mpr ⟨c₂, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (adj_comm d₂ c₂).trans hd₂_adj⟩⟩
      have hd₂_deg1 : vertexDegree adj d₂ = 1 := by
        have hle := h_deg_le2 d₂ hd₂_ne_v₀; omega
      -- "only" facts for each named vertex (8 vertices)
      have hv₀_only : ∀ w, adj v₀ w = 1 → w = leaf ∨ w = a₂ ∨ w = a₃ := by
        intro w hw
        have hw_mem : w ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        by_cases hwl : w = leaf
        · left; exact hwl
        have hw_mem' : w ∈ S₀.erase leaf := Finset.mem_erase.mpr ⟨hwl, hw_mem⟩
        rw [hS₀_eq] at hw_mem'
        rcases Finset.mem_insert.mp hw_mem' with h | h
        · right; left; exact h
        · right; right; exact Finset.mem_singleton.mp h
      have hleaf_only : ∀ w, adj leaf w = 1 → w = v₀ := by
        intro w hw; by_contra hne
        have h2 : 2 ≤ vertexDegree adj leaf := by
          change 2 ≤ (Finset.univ.filter (fun j => adj leaf j = 1)).card
          have hv₀_in : v₀ ∈ Finset.univ.filter (fun j => adj leaf j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm leaf v₀).trans h_leaf_adj⟩
          have hw_in : w ∈ Finset.univ.filter (fun j => adj leaf j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
          calc 2 = ({v₀, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
            _ ≤ _ := Finset.card_le_card (fun x hx => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption)
        omega
      have ha₂_only : ∀ w, adj a₂ w = 1 → w = v₀ ∨ w = b₂ := by
        intro w hw
        have hw_mem : w ∈ Finset.univ.filter (fun j => adj a₂ j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        by_cases hwv : w = v₀
        · left; exact hwv
        right
        have hw' : w ∈ (Finset.univ.filter (fun j => adj a₂ j = 1)).erase v₀ :=
          Finset.mem_erase.mpr ⟨hwv, hw_mem⟩
        rw [hb₂_eq] at hw'; exact Finset.mem_singleton.mp hw'
      have hb₂_only : ∀ w, adj b₂ w = 1 → w = a₂ ∨ w = c₂ := by
        intro w hw
        have hw_mem : w ∈ Finset.univ.filter (fun j => adj b₂ j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        by_cases hwa : w = a₂
        · left; exact hwa
        right
        have hw' : w ∈ (Finset.univ.filter (fun j => adj b₂ j = 1)).erase a₂ :=
          Finset.mem_erase.mpr ⟨hwa, hw_mem⟩
        rw [hc₂_eq] at hw'; exact Finset.mem_singleton.mp hw'
      have hc₂_only : ∀ w, adj c₂ w = 1 → w = b₂ ∨ w = d₂ := by
        intro w hw
        have hw_mem : w ∈ Finset.univ.filter (fun j => adj c₂ j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        by_cases hwb : w = b₂
        · left; exact hwb
        right
        have hw' : w ∈ (Finset.univ.filter (fun j => adj c₂ j = 1)).erase b₂ :=
          Finset.mem_erase.mpr ⟨hwb, hw_mem⟩
        rw [hd₂_eq] at hw'; exact Finset.mem_singleton.mp hw'
      have hd₂_only : ∀ w, adj d₂ w = 1 → w = c₂ := by
        intro w hw; by_contra hne
        have h2 : 2 ≤ vertexDegree adj d₂ := by
          change 2 ≤ (Finset.univ.filter (fun j => adj d₂ j = 1)).card
          have hc₂_in : c₂ ∈ Finset.univ.filter (fun j => adj d₂ j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm d₂ c₂).trans hd₂_adj⟩
          have hw_in : w ∈ Finset.univ.filter (fun j => adj d₂ j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
          calc 2 = ({c₂, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
            _ ≤ _ := Finset.card_le_card (fun x hx => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption)
        omega
      have ha₃_only : ∀ w, adj a₃ w = 1 → w = v₀ ∨ w = b₃ := by
        intro w hw
        have hw_mem : w ∈ Finset.univ.filter (fun j => adj a₃ j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        by_cases hwv : w = v₀
        · left; exact hwv
        right
        have hw' : w ∈ (Finset.univ.filter (fun j => adj a₃ j = 1)).erase v₀ :=
          Finset.mem_erase.mpr ⟨hwv, hw_mem⟩
        rw [hb₃_eq] at hw'; exact Finset.mem_singleton.mp hw'
      have hb₃_only : ∀ w, adj b₃ w = 1 → w = a₃ := by
        intro w hw; by_contra hne
        have h2 : 2 ≤ vertexDegree adj b₃ := by
          change 2 ≤ (Finset.univ.filter (fun j => adj b₃ j = 1)).card
          have ha₃_in : a₃ ∈ Finset.univ.filter (fun j => adj b₃ j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm b₃ a₃).trans hb₃_adj⟩
          have hw_in : w ∈ Finset.univ.filter (fun j => adj b₃ j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
          calc 2 = ({a₃, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
            _ ≤ _ := Finset.card_le_card (fun x hx => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption)
        omega
      have h_all_named : ∀ w : Fin n,
          w = v₀ ∨ w = leaf ∨ w = a₂ ∨ w = b₂ ∨ w = c₂ ∨ w = d₂ ∨
          w = a₃ ∨ w = b₃ := by
        apply connected_closed_set_is_all adj hconn
          (fun w => w = v₀ ∨ w = leaf ∨ w = a₂ ∨ w = b₂ ∨ w = c₂ ∨ w = d₂ ∨
            w = a₃ ∨ w = b₃) v₀ (Or.inl rfl)
        intro v w hv hvw
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rcases hv₀_only w hvw with rfl | rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        · rcases hleaf_only w hvw with rfl
          exact Or.inl rfl
        · rcases ha₂_only w hvw with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · rcases hb₂_only w hvw with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rcases hc₂_only w hvw with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        · rcases hd₂_only w hvw with rfl
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rcases ha₃_only w hvw with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
        · rcases hb₃_only w hvw with rfl
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have hd_e8 : E8Distinct v₀ leaf a₂ b₂ c₂ d₂ a₃ b₃ := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact ne_of_adj' v₀ leaf h_leaf_adj
        · exact ne_of_adj' v₀ a₂ ha₂_adj
        · intro h; subst h
          rcases hb₂_only leaf h_leaf_adj with rfl | rfl
          · linarith [h_leaf_deg, h_a2_ext]
          · linarith [h_leaf_deg, h_c2_ext]
        · intro h; subst h
          rcases hc₂_only a₂ ha₂_adj with rfl | rfl
          · linarith [hdiag a₂, hb₂_adj]
          · linarith [h_a2_ext, hd₂_deg1]
        · intro h; subst h; exact absurd rfl hd₂_ne_v₀
        · exact ne_of_adj' v₀ a₃ ha₃_adj
        · intro heq; linarith [hv₀, heq ▸ hb₃_deg1]
        · exact ha₂_ne_leaf.symm
        · intro h; linarith [h_leaf_deg, h ▸ h_b2_ext]
        · intro h; linarith [h_leaf_deg, h ▸ h_c2_ext]
        · intro h; subst h
          have hca : c₂ = v₀ := hleaf_only c₂ ((adj_comm leaf c₂).trans hd₂_adj)
          subst hca; linarith [hv₀, h_c2_ext]
        · exact ha₃_ne_leaf.symm
        · intro h; subst h
          have haa : a₃ = v₀ := hleaf_only a₃ ((adj_comm leaf a₃).trans hb₃_adj)
          subst haa; linarith [hv₀, h_a3_ext]
        · exact ne_of_adj' a₂ b₂ hb₂_adj
        · intro h; subst h
          rcases ha₂_only d₂ hd₂_adj with rfl | rfl
          · linarith [hv₀, hd₂_deg1]
          · linarith [h_b2_ext, hd₂_deg1]
        · intro h; linarith [h_a2_ext, h ▸ hd₂_deg1]
        · exact ha₂₃
        · intro h; linarith [h_a2_ext, h ▸ hb₃_deg1]
        · exact ne_of_adj' b₂ c₂ hc₂_adj
        · intro h; linarith [h_b2_ext, h ▸ hd₂_deg1]
        · intro h
          rw [h] at hb₂_only
          rcases hb₂_only v₀ ((adj_comm a₃ v₀).trans ha₃_adj) with rfl | rfl
          · linarith [hv₀, h_a2_ext]
          · linarith [hv₀, h_c2_ext]
        · intro h; linarith [h_b2_ext, h ▸ hb₃_deg1]
        · exact ne_of_adj' c₂ d₂ hd₂_adj
        · intro h
          rw [h] at hc₂_only
          rcases hc₂_only v₀ ((adj_comm a₃ v₀).trans ha₃_adj) with rfl | rfl
          · linarith [hv₀, h_b2_ext]
          · linarith [hv₀, hd₂_deg1]
        · intro h; linarith [h_c2_ext, h ▸ hb₃_deg1]
        · intro h; linarith [hd₂_deg1, h ▸ h_a3_ext]
        · intro h; subst h
          have ha₃_eq_c₂ := hd₂_only a₃ ((adj_comm d₂ a₃).trans hb₃_adj)
          rcases hc₂_only v₀ (ha₃_eq_c₂ ▸ (adj_comm a₃ v₀).trans ha₃_adj) with rfl | rfl
          · linarith [hv₀, h_b2_ext]
          · linarith [hv₀, hd₂_deg1]
        · exact ne_of_adj' a₃ b₃ hb₃_adj
      intro x hx
      exact e8_posdef adj hsymm hdiag h01 v₀ leaf a₂ b₂ c₂ d₂ a₃ b₃ hd_e8
        h_leaf_adj ha₂_adj hb₂_adj hc₂_adj hd₂_adj ha₃_adj hb₃_adj
        hv₀_only hleaf_only ha₂_only hb₂_only hc₂_only hd₂_only
        ha₃_only hb₃_only h_all_named x hx
  · -- c₂ is a leaf (arm2 length = 3): e7_tree_posdef contradiction.
    -- The 7 named vertices {v₀, leaf, a₂, b₂, c₂, a₃, b₃} form T(1, 3, 2) = E₇,
    -- whose Cartan form is positive definite — contradicting `h_not_posdef`.
    exfalso
    apply h_not_posdef
    have hc₂_ne_v₀ : c₂ ≠ v₀ := by
      intro heq
      have hb₂v₀ : adj v₀ b₂ = 1 := by
        rw [adj_comm]; rw [heq] at hc₂_adj; exact hc₂_adj
      have hv₀_nbrs := deg3_three_neighbors h_leaf_adj ha₂_adj
        ha₃_adj ha₂_ne_leaf.symm ha₃_ne_leaf.symm ha₂₃ hv₀
      rcases hv₀_nbrs b₂ hb₂v₀ with h_eq | h_eq | h_eq
      · rw [h_eq] at h_b2_ext; omega
      · rw [h_eq] at hb₂_adj; have := hdiag a₂; omega
      · rw [h_eq] at hb₂_adj
        have ha₃_nbrs := deg2_two_neighbors
          ((adj_comm a₃ v₀).trans ha₃_adj)
          hb₃_adj hb₃_ne_v₀.symm h_a3_ext
        rcases ha₃_nbrs a₂
          ((adj_comm a₃ a₂).trans hb₂_adj) with h' | h'
        · exact ha₂_ne_v₀ h'
        · rw [h'] at h_a2_ext; omega
    have hc₂_deg_ge1 : 1 ≤ vertexDegree adj c₂ :=
      Finset.card_pos.mpr ⟨b₂, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (adj_comm c₂ b₂).trans hc₂_adj⟩⟩
    have hc₂_deg1 : vertexDegree adj c₂ = 1 := by
      have hle := h_deg_le2 c₂ hc₂_ne_v₀; omega
    exact e7_tree_posdef adj hsymm hdiag h01 hconn h_acyclic
      v₀ leaf a₂ b₂ c₂ a₃ b₃
      h_leaf_adj ha₂_adj ha₃_adj hb₂_adj hc₂_adj hb₃_adj
      hv₀ h_leaf_deg h_a2_ext h_a3_ext h_b2_ext
      hc₂_deg1 hb₃_deg1

set_option maxHeartbeats 6400000 in
-- reason: T(1, 2, r) case-split mirrors `InfiniteTypeConstructions.lean:7640-7963`
-- (~324 lines of port); the structure is the symmetric image of
-- `single_branch_leaf_both_extend_b3leaf_per_kQ` under swapping the `a₂`
-- and `a₃` arms.  Same heartbeat budget as on the sub-B sibling.
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of the `(b₂ degree 1, b₃ degree 2)` sub-case of the
"both arms extend" branch of `single_branch_leaf_case`
(`InfiniteTypeConstructions.lean:7640-7963`): the T(1, 2, r) configuration
with r ≥ 3 (i.e. `b₂` is a leaf and `b₃` extends to a longer arm).
Case-splits on whether `c₃`, `d₃`, `e₃` extend:

* `c₃` is a leaf (arm3 length = 3) → T(1, 3, 2) = E₇ is positive definite,
  contradicting `h_not_posdef` via `e7_tree_posdef`.
* `d₃` is a leaf (arm3 length = 4) → T(1, 4, 2) = E₈ is positive definite,
  contradicting `h_not_posdef` via `e8_posdef`.
* `d₃` extends (arm3 length ≥ 5) → the 9 vertices
  `{v₀, leaf, a₂, b₂, a₃, b₃, c₃, d₃, e₃}` form a T(1, 2, 5) = Ẽ₈ subgraph;
  dispatch to `t125_not_finite_type_per_kQ` via
  `subgraph_infinite_type_transfer_per_kQ`. -/
theorem single_branch_leaf_both_extend_b2leaf_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
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
    (v₀ : Fin n) (hv₀ : vertexDegree adj v₀ = 3)
    (h_unique : ∀ w, vertexDegree adj w = 3 → w = v₀)
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x))
    (leaf a₂ a₃ b₂ b₃ : Fin n)
    (h_leaf_adj : adj v₀ leaf = 1)
    (ha₂_adj : adj v₀ a₂ = 1) (ha₃_adj : adj v₀ a₃ = 1)
    (hb₂_adj : adj a₂ b₂ = 1) (hb₃_adj : adj a₃ b₃ = 1)
    (h_leaf_deg : vertexDegree adj leaf = 1)
    (h_a2_ext : vertexDegree adj a₂ = 2) (h_a3_ext : vertexDegree adj a₃ = 2)
    (hb₂_deg1 : vertexDegree adj b₂ = 1)
    (h_b3_ext : vertexDegree adj b₃ = 2)
    (ha₂₃ : a₂ ≠ a₃)
    (ha₂_ne_leaf : a₂ ≠ leaf) (ha₃_ne_leaf : a₃ ≠ leaf)
    (hb₂_ne_v₀ : b₂ ≠ v₀) (hb₃_ne_v₀ : b₃ ≠ v₀)
    (hS₀_eq : (Finset.univ.filter (adj v₀ · = 1)).erase leaf = {a₂, a₃})
    (hb₂_eq : (Finset.univ.filter (adj a₂ · = 1)).erase v₀ = {b₂})
    (hb₃_eq : (Finset.univ.filter (adj a₃ · = 1)).erase v₀ = {b₃})
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have ne_of_adj' : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  have h_deg_le2 : ∀ v, v ≠ v₀ → vertexDegree adj v ≤ 2 := by
    intro v hv; have h3 := h_deg v
    by_contra h; push_neg at h; exact hv (h_unique v (by omega))
  have hleaf_ne_v₀ : leaf ≠ v₀ := (ne_of_adj' v₀ leaf h_leaf_adj).symm
  have ha₂_ne_v₀ : a₂ ≠ v₀ := (ne_of_adj' v₀ a₂ ha₂_adj).symm
  have ha₃_ne_v₀ : a₃ ≠ v₀ := (ne_of_adj' v₀ a₃ ha₃_adj).symm
  have ha₂_ne_b₂ : a₂ ≠ b₂ := ne_of_adj' a₂ b₂ hb₂_adj
  have ha₃_ne_b₃ : a₃ ≠ b₃ := ne_of_adj' a₃ b₃ hb₃_adj
  set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1) with hS₀_def
  -- Extract c₃: the neighbour of b₃ other than a₃
  have extract_other := fun (v u : Fin n) (hvu : adj v u = 1)
      (hdeg2 : vertexDegree adj v = 2) =>
    let Sv := Finset.univ.filter (fun j => adj v j = 1)
    have hcard : Sv.card = 2 := hdeg2
    have hu_mem : u ∈ Sv :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu⟩
    Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem hu_mem, hcard])
  obtain ⟨c₃, hc₃_eq⟩ := extract_other b₃ a₃
    ((adj_comm b₃ a₃).trans hb₃_adj) h_b3_ext
  have hc₃_mem : c₃ ∈ (Finset.univ.filter (adj b₃ · = 1)).erase a₃ :=
    hc₃_eq ▸ Finset.mem_singleton_self c₃
  have hc₃_adj : adj b₃ c₃ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc₃_mem)).2
  have hc₃_ne_a₃ : c₃ ≠ a₃ := Finset.ne_of_mem_erase hc₃_mem
  have hb₃_ne_c₃ : b₃ ≠ c₃ := ne_of_adj' b₃ c₃ hc₃_adj
  by_cases h_c3_ext : vertexDegree adj c₃ = 2
  · -- c₃ extends (arm3 length ≥ 4): extract d₃
    obtain ⟨d₃, hd₃_eq⟩ := extract_other c₃ b₃
      ((adj_comm c₃ b₃).trans hc₃_adj) h_c3_ext
    have hd₃_mem : d₃ ∈ (Finset.univ.filter (adj c₃ · = 1)).erase b₃ :=
      hd₃_eq ▸ Finset.mem_singleton_self d₃
    have hd₃_adj : adj c₃ d₃ = 1 :=
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase hd₃_mem)).2
    have hd₃_ne_b₃ : d₃ ≠ b₃ := Finset.ne_of_mem_erase hd₃_mem
    have hc₃_ne_d₃ : c₃ ≠ d₃ := ne_of_adj' c₃ d₃ hd₃_adj
    by_cases h_d3_ext : vertexDegree adj d₃ = 2
    · -- d₃ extends (arm3 length ≥ 5): extract e₃, embed T(1, 2, 5) via the
      -- shared helper `embed_t125_in_tree_per_kQ` with renaming
      -- (v₀, u₁, p₁, p₂, q₁, q₂, q₃, q₄, q₅) ↦
      -- (v₀, leaf, a₂, b₂, a₃, b₃, c₃, d₃, e₃).
      obtain ⟨e₃, he₃_eq⟩ := extract_other d₃ c₃
        ((adj_comm d₃ c₃).trans hd₃_adj) h_d3_ext
      have he₃_mem : e₃ ∈ (Finset.univ.filter (adj d₃ · = 1)).erase c₃ :=
        he₃_eq ▸ Finset.mem_singleton_self e₃
      have he₃_adj : adj d₃ e₃ = 1 :=
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase he₃_mem)).2
      have he₃_ne_c₃ : e₃ ≠ c₃ := Finset.ne_of_mem_erase he₃_mem
      exact embed_t125_in_tree_per_kQ adj hsymm hdiag h01 h_acyclic
        v₀ leaf a₂ b₂ a₃ b₃ c₃ d₃ e₃
        h_leaf_adj ha₂_adj hb₂_adj ha₃_adj hb₃_adj hc₃_adj hd₃_adj he₃_adj
        ha₂_ne_leaf.symm ha₃_ne_leaf.symm ha₂₃ hb₂_ne_v₀ hb₃_ne_v₀
        hc₃_ne_a₃ hd₃_ne_b₃ he₃_ne_c₃
        F Q hOrient
    · -- d₃ is a leaf (arm3 length = 4): T(1, 2, 4) = E₈ posdef contradiction.
      -- The 8 named vertices {v₀, leaf, a₃, b₃, c₃, d₃, a₂, b₂} form an E₈ tree
      -- whose Cartan form is positive definite — contradicting `h_not_posdef`.
      exfalso
      apply h_not_posdef
      have hd₃_ne_v₀ : d₃ ≠ v₀ := by
        intro h
        have ha₃_ne_b₃' : a₃ ≠ b₃ := ne_of_adj' a₃ b₃ hb₃_adj
        have hb₃_ne_c₃' : b₃ ≠ c₃ := ne_of_adj' b₃ c₃ hc₃_adj
        have hv₀_ne_b₃ : v₀ ≠ b₃ := hb₃_ne_v₀.symm
        have hv₀_ne_c₃ : v₀ ≠ c₃ := by
          intro heq; rw [h, heq] at hd₃_adj; linarith [hdiag c₃]
        have ha₃_ne_c₃ : a₃ ≠ c₃ := hc₃_ne_a₃.symm
        have h_nonadj : adj c₃ v₀ = 0 := acyclic_path_nonadj adj hsymm h01 h_acyclic
          [v₀, a₃, b₃, c₃] (by simp)
          (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
              not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
              exact ⟨⟨ha₃_ne_v₀.symm, hv₀_ne_b₃, hv₀_ne_c₃⟩, ⟨ha₃_ne_b₃', ha₃_ne_c₃⟩, hb₃_ne_c₃'⟩)
          (by intro k hk
              have : k + 1 < 4 := by simpa using hk
              have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
              rcases this with rfl | rfl | rfl
              · exact ha₃_adj
              · exact hb₃_adj
              · exact hc₃_adj)
        have hcv : adj c₃ v₀ = 1 := by rw [← h]; exact hd₃_adj
        linarith [hcv, h_nonadj]
      have hd₃_deg_ge1 : 1 ≤ vertexDegree adj d₃ :=
        Finset.card_pos.mpr ⟨c₃, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (adj_comm d₃ c₃).trans hd₃_adj⟩⟩
      have hd₃_deg1 : vertexDegree adj d₃ = 1 := by
        have hle := h_deg_le2 d₃ hd₃_ne_v₀; omega
      -- "only" facts for each named vertex (8 vertices)
      have hv₀_only : ∀ w, adj v₀ w = 1 → w = leaf ∨ w = a₃ ∨ w = a₂ := by
        intro w hw
        have hw_mem : w ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        by_cases hwl : w = leaf
        · left; exact hwl
        have hw_mem' : w ∈ S₀.erase leaf := Finset.mem_erase.mpr ⟨hwl, hw_mem⟩
        rw [hS₀_eq] at hw_mem'
        rcases Finset.mem_insert.mp hw_mem' with h | h
        · right; right; exact h
        · right; left; exact Finset.mem_singleton.mp h
      have hleaf_only : ∀ w, adj leaf w = 1 → w = v₀ := by
        intro w hw; by_contra hne
        have h2 : 2 ≤ vertexDegree adj leaf := by
          change 2 ≤ (Finset.univ.filter (fun j => adj leaf j = 1)).card
          have hv₀_in : v₀ ∈ Finset.univ.filter (fun j => adj leaf j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm leaf v₀).trans h_leaf_adj⟩
          have hw_in : w ∈ Finset.univ.filter (fun j => adj leaf j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
          calc 2 = ({v₀, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
            _ ≤ _ := Finset.card_le_card (fun x hx => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption)
        omega
      have ha₃_only : ∀ w, adj a₃ w = 1 → w = v₀ ∨ w = b₃ := by
        intro w hw
        have hw_mem : w ∈ Finset.univ.filter (fun j => adj a₃ j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        by_cases hwv : w = v₀
        · left; exact hwv
        right
        have hw' : w ∈ (Finset.univ.filter (fun j => adj a₃ j = 1)).erase v₀ :=
          Finset.mem_erase.mpr ⟨hwv, hw_mem⟩
        rw [hb₃_eq] at hw'; exact Finset.mem_singleton.mp hw'
      have hb₃_only : ∀ w, adj b₃ w = 1 → w = a₃ ∨ w = c₃ := by
        intro w hw
        have hw_mem : w ∈ Finset.univ.filter (fun j => adj b₃ j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        by_cases hwa : w = a₃
        · left; exact hwa
        right
        have hw' : w ∈ (Finset.univ.filter (fun j => adj b₃ j = 1)).erase a₃ :=
          Finset.mem_erase.mpr ⟨hwa, hw_mem⟩
        rw [hc₃_eq] at hw'; exact Finset.mem_singleton.mp hw'
      have hc₃_only : ∀ w, adj c₃ w = 1 → w = b₃ ∨ w = d₃ := by
        intro w hw
        have hw_mem : w ∈ Finset.univ.filter (fun j => adj c₃ j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        by_cases hwb : w = b₃
        · left; exact hwb
        right
        have hw' : w ∈ (Finset.univ.filter (fun j => adj c₃ j = 1)).erase b₃ :=
          Finset.mem_erase.mpr ⟨hwb, hw_mem⟩
        rw [hd₃_eq] at hw'; exact Finset.mem_singleton.mp hw'
      have hd₃_only : ∀ w, adj d₃ w = 1 → w = c₃ := by
        intro w hw; by_contra hne
        have h2 : 2 ≤ vertexDegree adj d₃ := by
          change 2 ≤ (Finset.univ.filter (fun j => adj d₃ j = 1)).card
          have hc₃_in : c₃ ∈ Finset.univ.filter (fun j => adj d₃ j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm d₃ c₃).trans hd₃_adj⟩
          have hw_in : w ∈ Finset.univ.filter (fun j => adj d₃ j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
          calc 2 = ({c₃, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
            _ ≤ _ := Finset.card_le_card (fun x hx => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption)
        omega
      have ha₂_only : ∀ w, adj a₂ w = 1 → w = v₀ ∨ w = b₂ := by
        intro w hw
        have hw_mem : w ∈ Finset.univ.filter (fun j => adj a₂ j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        by_cases hwv : w = v₀
        · left; exact hwv
        right
        have hw' : w ∈ (Finset.univ.filter (fun j => adj a₂ j = 1)).erase v₀ :=
          Finset.mem_erase.mpr ⟨hwv, hw_mem⟩
        rw [hb₂_eq] at hw'; exact Finset.mem_singleton.mp hw'
      have hb₂_only : ∀ w, adj b₂ w = 1 → w = a₂ := by
        intro w hw; by_contra hne
        have h2 : 2 ≤ vertexDegree adj b₂ := by
          change 2 ≤ (Finset.univ.filter (fun j => adj b₂ j = 1)).card
          have ha₂_in : a₂ ∈ Finset.univ.filter (fun j => adj b₂ j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm b₂ a₂).trans hb₂_adj⟩
          have hw_in : w ∈ Finset.univ.filter (fun j => adj b₂ j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
          calc 2 = ({a₂, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
            _ ≤ _ := Finset.card_le_card (fun x hx => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption)
        omega
      have h_all_named : ∀ w : Fin n,
          w = v₀ ∨ w = leaf ∨ w = a₃ ∨ w = b₃ ∨ w = c₃ ∨ w = d₃ ∨
          w = a₂ ∨ w = b₂ := by
        apply connected_closed_set_is_all adj hconn
          (fun w => w = v₀ ∨ w = leaf ∨ w = a₃ ∨ w = b₃ ∨ w = c₃ ∨ w = d₃ ∨
            w = a₂ ∨ w = b₂) v₀ (Or.inl rfl)
        intro v w hv hvw
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rcases hv₀_only w hvw with rfl | rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        · rcases hleaf_only w hvw with rfl
          exact Or.inl rfl
        · rcases ha₃_only w hvw with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · rcases hb₃_only w hvw with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rcases hc₃_only w hvw with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        · rcases hd₃_only w hvw with rfl
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rcases ha₂_only w hvw with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
        · rcases hb₂_only w hvw with rfl
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have hd_e8 : E8Distinct v₀ leaf a₃ b₃ c₃ d₃ a₂ b₂ := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact ne_of_adj' v₀ leaf h_leaf_adj
        · exact ne_of_adj' v₀ a₃ ha₃_adj
        · intro h; linarith [hv₀, h.symm ▸ h_b3_ext]
        · intro h; linarith [hv₀, h.symm ▸ h_c3_ext]
        · intro h; linarith [hv₀, h.symm ▸ hd₃_deg1]
        · exact ne_of_adj' v₀ a₂ ha₂_adj
        · intro heq; linarith [hv₀, heq ▸ hb₂_deg1]
        · exact ha₃_ne_leaf.symm
        · intro h; linarith [h_leaf_deg, h ▸ h_b3_ext]
        · intro h; linarith [h_leaf_deg, h ▸ h_c3_ext]
        · intro h; subst h
          have hca : c₃ = v₀ := hleaf_only c₃ ((adj_comm leaf c₃).trans hd₃_adj)
          subst hca; linarith [hv₀, h_c3_ext]
        · exact ha₂_ne_leaf.symm
        · intro h; subst h
          have haa : a₂ = v₀ := hleaf_only a₂ ((adj_comm leaf a₂).trans hb₂_adj)
          subst haa; linarith [hv₀, h_a2_ext]
        · exact ne_of_adj' a₃ b₃ hb₃_adj
        · intro h; subst h
          rcases ha₃_only d₃ hd₃_adj with rfl | rfl
          · linarith [hv₀, hd₃_deg1]
          · linarith [h_b3_ext, hd₃_deg1]
        · intro h; linarith [h_a3_ext, h ▸ hd₃_deg1]
        · exact ha₂₃.symm
        · intro h; linarith [h_a3_ext, h ▸ hb₂_deg1]
        · exact ne_of_adj' b₃ c₃ hc₃_adj
        · intro h; linarith [h_b3_ext, h ▸ hd₃_deg1]
        · intro h
          rw [h] at hb₃_only
          rcases hb₃_only v₀ ((adj_comm a₂ v₀).trans ha₂_adj) with rfl | rfl
          · linarith [hv₀, h_a3_ext]
          · linarith [hv₀, h_c3_ext]
        · intro h; linarith [h_b3_ext, h ▸ hb₂_deg1]
        · exact ne_of_adj' c₃ d₃ hd₃_adj
        · intro h
          rw [h] at hc₃_only
          rcases hc₃_only v₀ ((adj_comm a₂ v₀).trans ha₂_adj) with rfl | rfl
          · linarith [hv₀, h_b3_ext]
          · linarith [hv₀, hd₃_deg1]
        · intro h; linarith [h_c3_ext, h ▸ hb₂_deg1]
        · intro h; linarith [hd₃_deg1, h ▸ h_a2_ext]
        · intro h; subst h
          have ha₂_eq_c₃ := hd₃_only a₂ ((adj_comm d₃ a₂).trans hb₂_adj)
          rcases hc₃_only v₀ (ha₂_eq_c₃ ▸ (adj_comm a₂ v₀).trans ha₂_adj) with rfl | rfl
          · linarith [hv₀, h_b3_ext]
          · linarith [hv₀, hd₃_deg1]
        · exact ne_of_adj' a₂ b₂ hb₂_adj
      intro x hx
      exact e8_posdef adj hsymm hdiag h01 v₀ leaf a₃ b₃ c₃ d₃ a₂ b₂ hd_e8
        h_leaf_adj ha₃_adj hb₃_adj hc₃_adj hd₃_adj ha₂_adj hb₂_adj
        hv₀_only hleaf_only ha₃_only hb₃_only hc₃_only hd₃_only
        ha₂_only hb₂_only h_all_named x hx
  · -- c₃ is a leaf (arm3 length = 3): e7_tree_posdef contradiction.
    -- The 7 named vertices {v₀, leaf, a₃, b₃, c₃, a₂, b₂} form T(1, 3, 2) = E₇,
    -- whose Cartan form is positive definite — contradicting `h_not_posdef`.
    exfalso
    apply h_not_posdef
    have hc₃_ne_v₀ : c₃ ≠ v₀ := by
      intro heq
      have hb₃v₀ : adj v₀ b₃ = 1 := by
        rw [adj_comm]; rw [heq] at hc₃_adj; exact hc₃_adj
      have hv₀_nbrs := deg3_three_neighbors h_leaf_adj ha₂_adj
        ha₃_adj ha₂_ne_leaf.symm ha₃_ne_leaf.symm ha₂₃ hv₀
      rcases hv₀_nbrs b₃ hb₃v₀ with h_eq | h_eq | h_eq
      · rw [h_eq] at h_b3_ext; omega
      · rw [h_eq] at hb₃_adj
        have ha₂_nbrs := deg2_two_neighbors
          ((adj_comm a₂ v₀).trans ha₂_adj)
          hb₂_adj hb₂_ne_v₀.symm h_a2_ext
        rcases ha₂_nbrs a₃
          ((adj_comm a₂ a₃).trans hb₃_adj) with h' | h'
        · exact ha₃_ne_v₀ h'
        · rw [h'] at h_a3_ext; omega
      · rw [h_eq] at hb₃_adj; have := hdiag a₃; omega
    have hc₃_deg_ge1 : 1 ≤ vertexDegree adj c₃ :=
      Finset.card_pos.mpr ⟨b₃, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (adj_comm c₃ b₃).trans hc₃_adj⟩⟩
    have hc₃_deg1 : vertexDegree adj c₃ = 1 := by
      have hle := h_deg_le2 c₃ hc₃_ne_v₀; omega
    exact e7_tree_posdef adj hsymm hdiag h01 hconn h_acyclic
      v₀ leaf a₃ b₃ c₃ a₂ b₂
      h_leaf_adj ha₃_adj ha₂_adj hb₃_adj hc₃_adj hb₂_adj
      hv₀ h_leaf_deg h_a3_ext h_a2_ext h_b3_ext
      hc₃_deg1 hb₂_deg1

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of the "both arms extend" branch of
`single_branch_leaf_case` (`InfiniteTypeConstructions.lean:6981-8352`):
given the T(1, q, r) configuration where both of `v₀`'s non-leaf
neighbours have degree 2.

API stub: the body is `sorry`, tracked by a follow-up sub-issue. The real
proof mirrors the `_kQ`-free original — further case-splits on whether
`b₂`, `b₃` and deeper vertices extend, dispatching to
`etilde7_not_finite_type_per_kQ` (q, r ≥ 3 → Ẽ₇),
`t125_not_finite_type_per_kQ` (r = 2, q ≥ 3 → T(1, q, 2), or q = 2,
r ≥ 3 → T(1, 2, r)), or contradicting `h_not_posdef` for the
T(1, 2, 2) = D₅ shape (with the asymmetric ADE configurations
T(1, 3, 2)/T(1, 4, 2)/T(1, 2, 3)/T(1, 2, 4) folded into the
T(1, q, 2)/T(1, 2, r) sub-cases above).

The "one or both arms are leaves" branches are handled inline in
`single_branch_leaf_case_per_kQ` via `tree_two_leaf_posdef` and do not flow
through this helper. -/
theorem single_branch_leaf_case_both_extend_per_kQ {n : ℕ}
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
    (v₀ : Fin n) (hv₀ : vertexDegree adj v₀ = 3)
    (h_unique : ∀ w, vertexDegree adj w = 3 → w = v₀)
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x))
    (leaf : Fin n) (h_leaf_adj : adj v₀ leaf = 1)
    (h_leaf_deg : vertexDegree adj leaf = 1)
    (a₂ a₃ : Fin n)
    (ha₂_adj : adj v₀ a₂ = 1) (ha₃_adj : adj v₀ a₃ = 1)
    (ha₂₃ : a₂ ≠ a₃)
    (ha₂_ne_leaf : a₂ ≠ leaf) (ha₃_ne_leaf : a₃ ≠ leaf)
    (ha₂_deg : vertexDegree adj a₂ = 2) (ha₃_deg : vertexDegree adj a₃ = 2)
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- TODO (parent assembly issue #2905): replace this `sorry` with the
  -- per-(F, Q) "both arms extend" body mirroring `single_branch_leaf_case`
  -- (`InfiniteTypeConstructions.lean:6981-8352`, ~1370 lines). Further case-
  -- splits on whether `b₂`, `b₃` and deeper vertices extend, dispatching to:
  --   * both arms ≥ 3 → embed Ẽ₇ and call `etilde7_not_finite_type_per_kQ`
  --     (sub-issue #2907).
  --   * `b₃` leaf, q ≥ 3 (T(1, q, 2)) → embed T(1, 2, 5) and call
  --     `t125_not_finite_type_per_kQ` (sub-issue #2908).
  --   * `b₂` leaf, r ≥ 3 (T(1, 2, r)) — symmetric to the previous case;
  --     call `t125_not_finite_type_per_kQ` (sub-issue #2909).
  --   * ADE shape T(1, 2, 2) = D₅ → contradict `h_not_posdef` via the
  --     `d5_posdef`-style posdef facts in `InfiniteTypeConstructions.lean`
  --     (sub-issue #2910; landed via PR #2912 — only T(1, 2, 2)). The
  --     other ADE configurations T(1, 3, 2)/T(1, 4, 2)/T(1, 2, 3)/T(1, 2, 4)
  --     are q,r ∈ {3, 4} sub-rows of #2908/#2909 above, not separately
  --     tracked.
  -- The real body will need `set_option maxHeartbeats 6400000 in` (mirroring
  -- the `_kQ`-free original at `InfiniteTypeConstructions.lean:6896`); the
  -- stub elaborates fine without it.
  let _ := hn; let _ := hsymm; let _ := hdiag; let _ := h01; let _ := hconn
  let _ := h_acyclic; let _ := h_deg; let _ := hv₀; let _ := h_unique
  let _ := h_not_posdef; let _ := h_leaf_adj; let _ := h_leaf_deg
  let _ := ha₂_adj; let _ := ha₃_adj; let _ := ha₂₃
  let _ := ha₂_ne_leaf; let _ := ha₃_ne_leaf; let _ := ha₂_deg; let _ := ha₃_deg
  let _ := hOrient
  sorry

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `single_branch_leaf_case`
(`InfiniteTypeConstructions.lean:6901`): a connected acyclic simple graph
with a unique degree-3 vertex `v₀`, all degrees ≤ 3, non-positive-definite
Cartan form, and at least one leaf neighbour of `v₀` has infinite
representation type for every algebraically closed `F` and every
orientation `Q`.

Top-level case-split on whether each of `v₀`'s other two neighbours
(`a₂`, `a₃`) has degree 2:

* Both `a₂` and `a₃` extend (q, r ≥ 2) → delegate to
  `single_branch_leaf_case_both_extend_per_kQ`.
* `a₃` is a leaf (q ≥ 2, r = 1) → T(1, q, 1) is a D-type tree, whose Cartan
  form is positive definite by `tree_two_leaf_posdef`, contradicting
  `h_not_posdef`.
* `a₂` is a leaf — symmetric to the previous case. -/
theorem single_branch_leaf_case_per_kQ {n : ℕ}
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
    (v₀ : Fin n) (hv₀ : vertexDegree adj v₀ = 3)
    (h_unique : ∀ w, vertexDegree adj w = 3 → w = v₀)
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x))
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
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have ne_of_adj' : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  have h_deg_le2 : ∀ v, v ≠ v₀ → vertexDegree adj v ≤ 2 := by
    intro v hv; have h3 := h_deg v
    by_contra h; push_neg at h; exact hv (h_unique v (by omega))
  -- Extract a₂, a₃: the other two neighbours of v₀ (besides leaf)
  set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1) with hS₀_def
  have h_leaf_mem : leaf ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_leaf_adj⟩
  obtain ⟨a₂, a₃, ha₂₃, hS₀_eq⟩ := Finset.card_eq_two.mp (by
    rw [Finset.card_erase_of_mem h_leaf_mem, (show S₀.card = 3 from hv₀)])
  have ha₂_mem : a₂ ∈ S₀.erase leaf := hS₀_eq ▸ Finset.mem_insert_self a₂ _
  have ha₃_mem : a₃ ∈ S₀.erase leaf := hS₀_eq ▸ Finset.mem_insert.mpr
    (Or.inr (Finset.mem_singleton_self a₃))
  have ha₂_adj : adj v₀ a₂ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase ha₂_mem)).2
  have ha₃_adj : adj v₀ a₃ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase ha₃_mem)).2
  have ha₂_ne_leaf : a₂ ≠ leaf := Finset.ne_of_mem_erase ha₂_mem
  have ha₃_ne_leaf : a₃ ≠ leaf := Finset.ne_of_mem_erase ha₃_mem
  have hleaf_ne_v₀ : leaf ≠ v₀ := (ne_of_adj' v₀ leaf h_leaf_adj).symm
  have ha₂_ne_v₀ : a₂ ≠ v₀ := (ne_of_adj' v₀ a₂ ha₂_adj).symm
  have ha₃_ne_v₀ : a₃ ≠ v₀ := (ne_of_adj' v₀ a₃ ha₃_adj).symm
  -- Case split: both a₂ and a₃ have degree 2?
  by_cases h_a2_ext : vertexDegree adj a₂ = 2
  · by_cases h_a3_ext : vertexDegree adj a₃ = 2
    · -- Both arms extend (degree = 2 each) → delegate to the both-extend helper
      exact single_branch_leaf_case_both_extend_per_kQ adj hn hsymm hdiag h01 hconn
        h_acyclic h_deg v₀ hv₀ h_unique h_not_posdef leaf h_leaf_adj h_leaf_deg
        a₂ a₃ ha₂_adj ha₃_adj ha₂₃ ha₂_ne_leaf ha₃_ne_leaf h_a2_ext h_a3_ext
        F Q hOrient
    · -- a₃ has degree 1 (leaf): T(1, ≥2, 1) = D-type → posdef → contradiction
      have ha₃_deg1 : vertexDegree adj a₃ = 1 := by
        have hle := h_deg_le2 a₃ ha₃_ne_v₀
        have hge : 1 ≤ vertexDegree adj a₃ :=
          Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (adj_comm a₃ v₀).trans ha₃_adj⟩⟩
        omega
      exfalso
      apply h_not_posdef
      intro x hx
      exact tree_two_leaf_posdef adj hsymm hdiag h01 hconn h_acyclic h_deg v₀ leaf a₃
        h_leaf_adj h_leaf_deg ha₃_adj ha₃_deg1
        ha₃_ne_leaf.symm hleaf_ne_v₀ ha₃_ne_v₀ h_deg_le2 x hx
  · -- a₂ has degree 1 (leaf): T(1, ≥1, 1) — symmetric to the a₃ leaf case
    have ha₂_deg1 : vertexDegree adj a₂ = 1 := by
      have hle := h_deg_le2 a₂ ha₂_ne_v₀
      have hge : 1 ≤ vertexDegree adj a₂ :=
        Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (adj_comm a₂ v₀).trans ha₂_adj⟩⟩
      omega
    exfalso
    apply h_not_posdef
    intro x hx
    exact tree_two_leaf_posdef adj hsymm hdiag h01 hconn h_acyclic h_deg v₀ leaf a₂
      h_leaf_adj h_leaf_deg ha₂_adj ha₂_deg1
      ha₂_ne_leaf.symm hleaf_ne_v₀ ha₂_ne_v₀ h_deg_le2 x hx

set_option maxHeartbeats 3200000 in
-- reason: ~30 distinctness facts plus the 49-case `fin_cases` adjacency
-- proof through the `Fin 7 ↪ Fin n` embedding push elaboration past the
-- default budget; mirrors the same setting on
-- `single_branch_not_posdef_infinite_type`
-- (`InfiniteTypeConstructions.lean:8392`).
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `single_branch_not_posdef_infinite_type`
(`InfiniteTypeConstructions.lean:8401`): a connected acyclic simple graph
with a unique degree-3 vertex (a T(p, q, r) tree) and non-positive-
definite Cartan form has infinite representation type for every
algebraically closed `F` and every orientation `Q`. Case-splits on whether
all three arms have length ≥ 2: if so, embed Ẽ₆ = T(2, 2, 2); otherwise
delegate to `single_branch_leaf_case_per_kQ`. -/
theorem single_branch_not_posdef_infinite_type_per_kQ {n : ℕ}
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
    (v₀ : Fin n) (hv₀ : vertexDegree adj v₀ = 3)
    (h_unique : ∀ w, vertexDegree adj w = 3 → w = v₀)
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x))
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have ne_of_adj : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  -- Non-v₀ vertices have degree ≤ 2
  have h_deg_le2 : ∀ v, v ≠ v₀ → vertexDegree adj v ≤ 2 := by
    intro v hv
    have h3 := h_deg v
    by_contra h
    push_neg at h
    have : vertexDegree adj v = 3 := by omega
    exact hv (h_unique v this)
  -- Extract 3 neighbors of v₀
  set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1) with hS₀_def
  have hS₀_card : S₀.card = 3 := hv₀
  have hS₀_nonempty : S₀.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hS₀_card
  obtain ⟨a₁, ha₁_mem⟩ := hS₀_nonempty
  have ha₁_adj : adj v₀ a₁ = 1 := (Finset.mem_filter.mp ha₁_mem).2
  have hS₀_erase1 : (S₀.erase a₁).card = 2 := by
    rw [Finset.card_erase_of_mem ha₁_mem, hS₀_card]
  obtain ⟨a₂, a₃, ha₂₃, hS₀_eq2⟩ := Finset.card_eq_two.mp hS₀_erase1
  have ha₂_mem : a₂ ∈ S₀.erase a₁ := hS₀_eq2 ▸ Finset.mem_insert_self a₂ _
  have ha₃_mem : a₃ ∈ S₀.erase a₁ := hS₀_eq2 ▸ Finset.mem_insert.mpr
    (Or.inr (Finset.mem_singleton_self a₃))
  have ha₂_adj : adj v₀ a₂ = 1 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase ha₂_mem)).2
  have ha₃_adj : adj v₀ a₃ = 1 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase ha₃_mem)).2
  have ha₁₂ : a₁ ≠ a₂ := (Finset.ne_of_mem_erase ha₂_mem).symm
  have ha₁₃ : a₁ ≠ a₃ := (Finset.ne_of_mem_erase ha₃_mem).symm
  have ha₁_ne_v₀ : a₁ ≠ v₀ := (ne_of_adj v₀ a₁ ha₁_adj).symm
  have ha₂_ne_v₀ : a₂ ≠ v₀ := (ne_of_adj v₀ a₂ ha₂_adj).symm
  have ha₃_ne_v₀ : a₃ ≠ v₀ := (ne_of_adj v₀ a₃ ha₃_adj).symm
  -- Case split on whether each arm extends (degree ≥ 2 at the neighbor)
  by_cases h_a1_ext : 2 ≤ vertexDegree adj a₁
  · by_cases h_a2_ext : 2 ≤ vertexDegree adj a₂
    · by_cases h_a3_ext : 2 ≤ vertexDegree adj a₃
      · -- All 3 arms have length ≥ 2 → embed Ẽ₆ = T(2,2,2)
        have ha₁_deg : vertexDegree adj a₁ = 2 := by
          have := h_deg_le2 a₁ ha₁_ne_v₀; omega
        set Sa₁ := Finset.univ.filter (fun j => adj a₁ j = 1) with hSa₁_def
        have hSa₁_card : Sa₁.card = 2 := ha₁_deg
        have hv₀_in_Sa₁ : v₀ ∈ Sa₁ :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm a₁ v₀).trans ha₁_adj⟩
        have hSa₁_erase : (Sa₁.erase v₀).card = 1 := by
          rw [Finset.card_erase_of_mem hv₀_in_Sa₁, hSa₁_card]
        obtain ⟨b₁, hb₁_eq⟩ := Finset.card_eq_one.mp hSa₁_erase
        have hb₁_mem : b₁ ∈ Sa₁.erase v₀ := hb₁_eq ▸ Finset.mem_singleton_self b₁
        have hb₁_adj : adj a₁ b₁ = 1 :=
          (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb₁_mem)).2
        have hb₁_ne_v₀ : b₁ ≠ v₀ := Finset.ne_of_mem_erase hb₁_mem
        have ha₂_deg : vertexDegree adj a₂ = 2 := by
          have := h_deg_le2 a₂ ha₂_ne_v₀; omega
        set Sa₂ := Finset.univ.filter (fun j => adj a₂ j = 1) with hSa₂_def
        have hSa₂_card : Sa₂.card = 2 := ha₂_deg
        have hv₀_in_Sa₂ : v₀ ∈ Sa₂ :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm a₂ v₀).trans ha₂_adj⟩
        have hSa₂_erase : (Sa₂.erase v₀).card = 1 := by
          rw [Finset.card_erase_of_mem hv₀_in_Sa₂, hSa₂_card]
        obtain ⟨b₂, hb₂_eq⟩ := Finset.card_eq_one.mp hSa₂_erase
        have hb₂_mem : b₂ ∈ Sa₂.erase v₀ := hb₂_eq ▸ Finset.mem_singleton_self b₂
        have hb₂_adj : adj a₂ b₂ = 1 :=
          (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb₂_mem)).2
        have hb₂_ne_v₀ : b₂ ≠ v₀ := Finset.ne_of_mem_erase hb₂_mem
        have ha₃_deg : vertexDegree adj a₃ = 2 := by
          have := h_deg_le2 a₃ ha₃_ne_v₀; omega
        set Sa₃ := Finset.univ.filter (fun j => adj a₃ j = 1) with hSa₃_def
        have hSa₃_card : Sa₃.card = 2 := ha₃_deg
        have hv₀_in_Sa₃ : v₀ ∈ Sa₃ :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm a₃ v₀).trans ha₃_adj⟩
        have hSa₃_erase : (Sa₃.erase v₀).card = 1 := by
          rw [Finset.card_erase_of_mem hv₀_in_Sa₃, hSa₃_card]
        obtain ⟨b₃, hb₃_eq⟩ := Finset.card_eq_one.mp hSa₃_erase
        have hb₃_mem : b₃ ∈ Sa₃.erase v₀ := hb₃_eq ▸ Finset.mem_singleton_self b₃
        have hb₃_adj : adj a₃ b₃ = 1 :=
          (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb₃_mem)).2
        have hb₃_ne_v₀ : b₃ ≠ v₀ := Finset.ne_of_mem_erase hb₃_mem
        have ha₁a₂ : adj a₁ a₂ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic v₀ a₁ a₂
            ha₁₂ ha₁_ne_v₀ ha₂_ne_v₀ ha₁_adj ha₂_adj
        have ha₁a₃ : adj a₁ a₃ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic v₀ a₁ a₃
            ha₁₃ ha₁_ne_v₀ ha₃_ne_v₀ ha₁_adj ha₃_adj
        have ha₂a₃ : adj a₂ a₃ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic v₀ a₂ a₃
            ha₂₃ ha₂_ne_v₀ ha₃_ne_v₀ ha₂_adj ha₃_adj
        have hv₀b₁ : adj v₀ b₁ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic a₁ v₀ b₁
            hb₁_ne_v₀.symm ha₁_ne_v₀.symm (ne_of_adj a₁ b₁ hb₁_adj).symm
            ((adj_comm a₁ v₀).trans ha₁_adj) hb₁_adj
        have hv₀b₂ : adj v₀ b₂ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic a₂ v₀ b₂
            hb₂_ne_v₀.symm ha₂_ne_v₀.symm (ne_of_adj a₂ b₂ hb₂_adj).symm
            ((adj_comm a₂ v₀).trans ha₂_adj) hb₂_adj
        have hv₀b₃ : adj v₀ b₃ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic a₃ v₀ b₃
            hb₃_ne_v₀.symm ha₃_ne_v₀.symm (ne_of_adj a₃ b₃ hb₃_adj).symm
            ((adj_comm a₃ v₀).trans ha₃_adj) hb₃_adj
        have ha₁_ne_b₂ : a₁ ≠ b₂ := by intro h; rw [h] at ha₁_adj; linarith
        have ha₁_ne_b₃ : a₁ ≠ b₃ := by intro h; rw [h] at ha₁_adj; linarith
        have ha₂_ne_b₁ : a₂ ≠ b₁ := by intro h; rw [h] at ha₂_adj; linarith
        have ha₂_ne_b₃ : a₂ ≠ b₃ := by intro h; rw [h] at ha₂_adj; linarith
        have ha₃_ne_b₁ : a₃ ≠ b₁ := by intro h; rw [h] at ha₃_adj; linarith
        have ha₃_ne_b₂ : a₃ ≠ b₂ := by intro h; rw [h] at ha₃_adj; linarith
        have ha₁_ne_b₁ : a₁ ≠ b₁ := ne_of_adj a₁ b₁ hb₁_adj
        have ha₂_ne_b₂ : a₂ ≠ b₂ := ne_of_adj a₂ b₂ hb₂_adj
        have ha₃_ne_b₃ : a₃ ≠ b₃ := ne_of_adj a₃ b₃ hb₃_adj
        have nodup4 : ∀ (a b c d : Fin n),
            a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → [a, b, c, d].Nodup := by
          intro a b c d hab hac had hbc hbd hcd
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
            not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
          exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
        have edges4 : ∀ (a b c d : Fin n),
            adj a b = 1 → adj b c = 1 → adj c d = 1 →
            ∀ k, (hk : k + 1 < [a, b, c, d].length) →
              adj ([a, b, c, d].get ⟨k, by omega⟩) ([a, b, c, d].get ⟨k + 1, hk⟩) = 1 := by
          intro a b c d h₁ h₂ h₃ k hk
          have : k + 1 < 4 := by simpa using hk
          have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
          rcases this with rfl | rfl | rfl <;> assumption
        have hb₁_ne_b₂ : b₁ ≠ b₂ := by
          intro h; rw [← h] at hb₂_adj
          exact h_acyclic [b₁, a₁, v₀, a₂] (by simp)
            (nodup4 b₁ a₁ v₀ a₂ ha₁_ne_b₁.symm hb₁_ne_v₀ ha₂_ne_b₁.symm
              ha₁_ne_v₀ ha₁₂ ha₂_ne_v₀.symm)
            (edges4 b₁ a₁ v₀ a₂ ((adj_comm b₁ a₁).trans hb₁_adj)
              ((adj_comm a₁ v₀).trans ha₁_adj) ha₂_adj) hb₂_adj
        have hb₁_ne_b₃ : b₁ ≠ b₃ := by
          intro h; rw [← h] at hb₃_adj
          exact h_acyclic [b₁, a₁, v₀, a₃] (by simp)
            (nodup4 b₁ a₁ v₀ a₃ ha₁_ne_b₁.symm hb₁_ne_v₀ ha₃_ne_b₁.symm
              ha₁_ne_v₀ ha₁₃ ha₃_ne_v₀.symm)
            (edges4 b₁ a₁ v₀ a₃ ((adj_comm b₁ a₁).trans hb₁_adj)
              ((adj_comm a₁ v₀).trans ha₁_adj) ha₃_adj) hb₃_adj
        have hb₂_ne_b₃ : b₂ ≠ b₃ := by
          intro h; rw [← h] at hb₃_adj
          exact h_acyclic [b₂, a₂, v₀, a₃] (by simp)
            (nodup4 b₂ a₂ v₀ a₃ ha₂_ne_b₂.symm hb₂_ne_v₀ ha₃_ne_b₂.symm
              ha₂_ne_v₀ ha₂₃ ha₃_ne_v₀.symm)
            (edges4 b₂ a₂ v₀ a₃ ((adj_comm b₂ a₂).trans hb₂_adj)
              ((adj_comm a₂ v₀).trans ha₂_adj) ha₃_adj) hb₃_adj
        have ha₁b₂ : adj a₁ b₂ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₂, a₂, v₀, a₁] (by simp)
            (nodup4 b₂ a₂ v₀ a₁ (ne_of_adj a₂ b₂ hb₂_adj).symm hb₂_ne_v₀
              ha₁_ne_b₂.symm ha₂_ne_v₀ ha₁₂.symm ha₁_ne_v₀.symm)
            (edges4 b₂ a₂ v₀ a₁ ((adj_comm b₂ a₂).trans hb₂_adj)
              ((adj_comm a₂ v₀).trans ha₂_adj) ha₁_adj)
        have ha₁b₃ : adj a₁ b₃ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₃, a₃, v₀, a₁] (by simp)
            (nodup4 b₃ a₃ v₀ a₁ (ne_of_adj a₃ b₃ hb₃_adj).symm hb₃_ne_v₀
              ha₁_ne_b₃.symm ha₃_ne_v₀ ha₁₃.symm ha₁_ne_v₀.symm)
            (edges4 b₃ a₃ v₀ a₁ ((adj_comm b₃ a₃).trans hb₃_adj)
              ((adj_comm a₃ v₀).trans ha₃_adj) ha₁_adj)
        have ha₂b₁ : adj a₂ b₁ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₁, a₁, v₀, a₂] (by simp)
            (nodup4 b₁ a₁ v₀ a₂ (ne_of_adj a₁ b₁ hb₁_adj).symm hb₁_ne_v₀
              ha₂_ne_b₁.symm ha₁_ne_v₀ ha₁₂ ha₂_ne_v₀.symm)
            (edges4 b₁ a₁ v₀ a₂ ((adj_comm b₁ a₁).trans hb₁_adj)
              ((adj_comm a₁ v₀).trans ha₁_adj) ha₂_adj)
        have ha₂b₃ : adj a₂ b₃ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₃, a₃, v₀, a₂] (by simp)
            (nodup4 b₃ a₃ v₀ a₂ (ne_of_adj a₃ b₃ hb₃_adj).symm hb₃_ne_v₀
              ha₂_ne_b₃.symm ha₃_ne_v₀ ha₂₃.symm ha₂_ne_v₀.symm)
            (edges4 b₃ a₃ v₀ a₂ ((adj_comm b₃ a₃).trans hb₃_adj)
              ((adj_comm a₃ v₀).trans ha₃_adj) ha₂_adj)
        have ha₃b₁ : adj a₃ b₁ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₁, a₁, v₀, a₃] (by simp)
            (nodup4 b₁ a₁ v₀ a₃ (ne_of_adj a₁ b₁ hb₁_adj).symm hb₁_ne_v₀
              ha₃_ne_b₁.symm ha₁_ne_v₀ ha₁₃ ha₃_ne_v₀.symm)
            (edges4 b₁ a₁ v₀ a₃ ((adj_comm b₁ a₁).trans hb₁_adj)
              ((adj_comm a₁ v₀).trans ha₁_adj) ha₃_adj)
        have ha₃b₂ : adj a₃ b₂ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₂, a₂, v₀, a₃] (by simp)
            (nodup4 b₂ a₂ v₀ a₃ (ne_of_adj a₂ b₂ hb₂_adj).symm hb₂_ne_v₀
              ha₃_ne_b₂.symm ha₂_ne_v₀ ha₂₃ ha₃_ne_v₀.symm)
            (edges4 b₂ a₂ v₀ a₃ ((adj_comm b₂ a₂).trans hb₂_adj)
              ((adj_comm a₂ v₀).trans ha₂_adj) ha₃_adj)
        have path_nodup5 : ∀ (a b c d e : Fin n),
            a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
            [a, b, c, d, e].Nodup := by
          intro a b c d e hab hac had hae hbc hbd hbe hcd hce hde
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
            not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
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
        have hb₁b₂ : adj b₁ b₂ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₂, a₂, v₀, a₁, b₁] (by simp)
            (path_nodup5 b₂ a₂ v₀ a₁ b₁
              (ne_of_adj a₂ b₂ hb₂_adj).symm hb₂_ne_v₀ ha₁_ne_b₂.symm hb₁_ne_b₂.symm
              ha₂_ne_v₀ ha₁₂.symm ha₂_ne_b₁ ha₁_ne_v₀.symm hb₁_ne_v₀.symm ha₁_ne_b₁)
            (path_edges5 b₂ a₂ v₀ a₁ b₁
              ((adj_comm b₂ a₂).trans hb₂_adj) ((adj_comm a₂ v₀).trans ha₂_adj)
              ha₁_adj hb₁_adj)
        have hb₁b₃ : adj b₁ b₃ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₃, a₃, v₀, a₁, b₁] (by simp)
            (path_nodup5 b₃ a₃ v₀ a₁ b₁
              (ne_of_adj a₃ b₃ hb₃_adj).symm hb₃_ne_v₀ ha₁_ne_b₃.symm hb₁_ne_b₃.symm
              ha₃_ne_v₀ ha₁₃.symm ha₃_ne_b₁ ha₁_ne_v₀.symm hb₁_ne_v₀.symm ha₁_ne_b₁)
            (path_edges5 b₃ a₃ v₀ a₁ b₁
              ((adj_comm b₃ a₃).trans hb₃_adj) ((adj_comm a₃ v₀).trans ha₃_adj)
              ha₁_adj hb₁_adj)
        have hb₂b₃ : adj b₂ b₃ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₃, a₃, v₀, a₂, b₂] (by simp)
            (path_nodup5 b₃ a₃ v₀ a₂ b₂
              (ne_of_adj a₃ b₃ hb₃_adj).symm hb₃_ne_v₀ ha₂_ne_b₃.symm hb₂_ne_b₃.symm
              ha₃_ne_v₀ ha₂₃.symm ha₃_ne_b₂ ha₂_ne_v₀.symm hb₂_ne_v₀.symm ha₂_ne_b₂)
            (path_edges5 b₃ a₃ v₀ a₂ b₂
              ((adj_comm b₃ a₃).trans hb₃_adj) ((adj_comm a₃ v₀).trans ha₃_adj)
              ha₂_adj hb₂_adj)
        -- Construct the embedding φ : Fin 7 ↪ Fin n for Ẽ₆ = T(2,2,2)
        let φ_fun : Fin 7 → Fin n := fun i =>
          match i with
          | ⟨0, _⟩ => v₀ | ⟨1, _⟩ => a₁ | ⟨2, _⟩ => b₁
          | ⟨3, _⟩ => a₂ | ⟨4, _⟩ => b₂ | ⟨5, _⟩ => a₃ | ⟨6, _⟩ => b₃
        have φ_inj : Function.Injective φ_fun := by
          intro i j hij; simp only [φ_fun] at hij
          fin_cases i <;> fin_cases j <;>
            first | rfl | (exact absurd hij ‹_›) | (exact absurd hij.symm ‹_›)
        let φ : Fin 7 ↪ Fin n := ⟨φ_fun, φ_inj⟩
        have hembed : ∀ i j, etilde6Adj i j = adj (φ i) (φ j) := by
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp only [etilde6Adj, φ, φ_fun] <;> norm_num <;>
            linarith [hdiag v₀, hdiag a₁, hdiag a₂, hdiag a₃, hdiag b₁, hdiag b₂, hdiag b₃,
                      ha₁_adj, ha₂_adj, ha₃_adj, hb₁_adj, hb₂_adj, hb₃_adj,
                      adj_comm v₀ a₁, adj_comm v₀ a₂, adj_comm v₀ a₃,
                      adj_comm v₀ b₁, adj_comm v₀ b₂, adj_comm v₀ b₃,
                      adj_comm a₁ a₂, adj_comm a₁ a₃, adj_comm a₂ a₃,
                      adj_comm a₁ b₁, adj_comm a₁ b₂, adj_comm a₁ b₃,
                      adj_comm a₂ b₁, adj_comm a₂ b₂, adj_comm a₂ b₃,
                      adj_comm a₃ b₁, adj_comm a₃ b₂, adj_comm a₃ b₃,
                      adj_comm b₁ b₂, adj_comm b₁ b₃, adj_comm b₂ b₃,
                      ha₁a₂, ha₁a₃, ha₂a₃,
                      hv₀b₁, hv₀b₂, hv₀b₃,
                      ha₁b₂, ha₁b₃, ha₂b₁, ha₂b₃, ha₃b₁, ha₃b₂,
                      hb₁b₂, hb₁b₃, hb₂b₃]
        exact subgraph_infinite_type_transfer_per_kQ φ F Q
          (etilde6_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
            (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))
      · -- a₃ is leaf → delegate to leaf case
        have ha₃_deg1 : vertexDegree adj a₃ = 1 := by
          have := h_deg_le2 a₃ ha₃_ne_v₀
          have : 1 ≤ vertexDegree adj a₃ :=
            Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (adj_comm a₃ v₀).trans ha₃_adj⟩⟩
          omega
        exact single_branch_leaf_case_per_kQ adj hn hsymm hdiag h01 hconn h_acyclic h_deg v₀ hv₀
          h_unique h_not_posdef a₃ ha₃_adj ha₃_deg1 F Q hOrient
    · -- a₂ is leaf → delegate to leaf case
      have ha₂_deg1 : vertexDegree adj a₂ = 1 := by
        have := h_deg_le2 a₂ ha₂_ne_v₀
        have : 1 ≤ vertexDegree adj a₂ :=
          Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (adj_comm a₂ v₀).trans ha₂_adj⟩⟩
        omega
      exact single_branch_leaf_case_per_kQ adj hn hsymm hdiag h01 hconn h_acyclic h_deg v₀ hv₀
        h_unique h_not_posdef a₂ ha₂_adj ha₂_deg1 F Q hOrient
  · -- a₁ is leaf → delegate to leaf case
    have ha₁_deg1 : vertexDegree adj a₁ = 1 := by
      have := h_deg_le2 a₁ ha₁_ne_v₀
      have : 1 ≤ vertexDegree adj a₁ :=
        Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (adj_comm a₁ v₀).trans ha₁_adj⟩⟩
      omega
    exact single_branch_leaf_case_per_kQ adj hn hsymm hdiag h01 hconn h_acyclic h_deg v₀ hv₀
      h_unique h_not_posdef a₁ ha₁_adj ha₁_deg1 F Q hOrient

end Etingof
