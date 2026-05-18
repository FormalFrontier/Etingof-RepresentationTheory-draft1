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
  which internally dispatches to Ẽ₇ / T(1, 2, 5) depending on the
  T(1, q, r) shape.

`single_branch_leaf_case_per_kQ` is introduced here as an API stub with a
`sorry` body, tracked by a follow-up issue. Mirrors the API-stub
precedent set by `t125_not_finite_type_per_kQ` (`FieldGenericT125.lean`).

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
    · -- d₂ extends (arm2 length ≥ 5): extract e₂, embed T(1, 2, 5)
      obtain ⟨e₂, he₂_eq⟩ := extract_other d₂ c₂
        ((adj_comm d₂ c₂).trans hd₂_adj) h_d2_ext
      have he₂_mem : e₂ ∈ (Finset.univ.filter (adj d₂ · = 1)).erase c₂ :=
        he₂_eq ▸ Finset.mem_singleton_self e₂
      have _he₂_adj : adj d₂ e₂ = 1 :=
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase he₂_mem)).2
      have _he₂_ne_c₂ : e₂ ≠ c₂ := Finset.ne_of_mem_erase he₂_mem
      let _ := h_a3_ext  -- silenced until d₂-extends body is implemented
      sorry  -- T(1, 2, 5) embedding for d₂-extends arm
    · -- d₂ is a leaf (arm2 length = 4): e8_posdef contradiction
      sorry  -- E₈ posdef contradiction for T(1, 4, 2)
  · -- c₂ is a leaf (arm2 length = 3): e7_tree_posdef contradiction
    sorry  -- E₇ posdef contradiction for T(1, 3, 2)

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of the "both arms extend" branch of
`single_branch_leaf_case` (`InfiniteTypeConstructions.lean:6981-8352`):
given the T(1, q, r) configuration where both of `v₀`'s non-leaf

API stub: the body is `sorry`, tracked by a follow-up sub-issue. The real
proof mirrors the `_kQ`-free original — further case-splits on whether
`b₂`, `b₃` and deeper vertices extend, dispatching to
`etilde7_not_finite_type_per_kQ` (q, r ≥ 3 → Ẽ₇),
`t125_not_finite_type_per_kQ` (q = 2, r ≥ 5 → T(1, 2, 5)), or contradicting
`h_not_posdef` for the ADE shapes T(1, 2, 2), T(1, 2, 3), T(1, 2, 4).

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
  -- TODO (follow-up issue): replace this `sorry` with the per-(F, Q) "both arms
  -- extend" body mirroring `single_branch_leaf_case`
  -- (`InfiniteTypeConstructions.lean:6981-8352`, ~1370 lines). Further case-
  -- splits on whether `b₂`, `b₃` and deeper vertices extend, dispatching to:
  --   * both arms ≥ 3 → embed Ẽ₇ and call `etilde7_not_finite_type_per_kQ`
  --   * one arm length 2, other ≥ 5 → embed T(1, 2, 5) and call
  --     `t125_not_finite_type_per_kQ`
  --   * ADE shapes T(1, 2, 2/3/4) → contradict `h_not_posdef` via the
  --     `e7_tree_posdef` / `e8_posdef`-style posdef facts in
  --     `InfiniteTypeConstructions.lean`.
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
