import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType

/-!
# Field-Generic T(1, 2, 5) Representation — API stub

API stub file introduced by issue #2875 (deliverable 1) so that the
per-(F, Q) assembly `not_posdef_infinite_type_per_kQ` in
`FieldGenericInfiniteType.lean` can dispatch by name to the T(1, 2, 5)
forbidden-subgraph case.

The actual `_F` / `_kQ` constructions and the body of
`t125_not_finite_type_per_kQ` are tracked by issue #2793. This file only
introduces the theorem signature with a `sorry` body so that the
assembly remains decoupled from the proof-level chain.

See `FieldGenericInfiniteType.lean` for the naming conventions
(`_F` / `_gen`, `_kQ`, `_per_kQ`).
-/

namespace Etingof

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) version of `t125_not_finite_type`: for any
algebraically closed field `F` and any orientation `Q` of `t125Adj`, the
set of dimension vectors of indecomposable representations of `Q` over
`F` is infinite.

API stub introduced by issue #2875 (deliverable 1): the body is `sorry`
pending the proof tracked by issue #2793. This stub exists so that the
per-(F, Q) assembly `not_posdef_infinite_type_per_kQ` can dispatch by
name to the T(1, 2, 5) forbidden-subgraph case via
`subgraph_infinite_type_transfer_per_kQ`. -/
theorem t125_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q t125Adj) :
    ¬ Set.Finite
      {d : Fin 9 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 9) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- TODO (#2793): replace this `sorry` with the proof that the
  -- orientation-generic family `t125Rep_kQ F Q hOrient (m + 1)` is
  -- indecomposable and produces infinitely many distinct dimension
  -- vectors (mirror `etilde6_not_finite_type_per_kQ`).
  let _ := hOrient
  sorry

set_option maxHeartbeats 3200000 in
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) port of `embed_t125_in_tree`
(`InfiniteTypeConstructions.lean:4918-5279`): given 9 vertices forming
T(1, 2, 5) inside an acyclic simple graph, embed and dispatch to
`t125_not_finite_type_per_kQ` via `subgraph_infinite_type_transfer_per_kQ`.

Vertex roles: `v₀` (center), `u₁` (arm of length 1), `p₁`-`p₂` (arm of
length 2), `q₁`-`q₂`-`q₃`-`q₄`-`q₅` (arm of length 5).
Embedding map: 0→v₀, 1→u₁, 2→p₁, 3→p₂, 4→q₁, 5→q₂, 6→q₃, 7→q₄, 8→q₅.

Shared helper used by both
`single_branch_leaf_both_extend_b3leaf_per_kQ` (sub-B, d₂-extends case,
issue #2913) and `single_branch_leaf_both_extend_b2leaf_per_kQ`
(sub-C, d₃-extends case, issue #2915). -/
theorem embed_t125_in_tree_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (v₀ u₁ p₁ p₂ q₁ q₂ q₃ q₄ q₅ : Fin n)
    (hu₁ : adj v₀ u₁ = 1) (hp₁ : adj v₀ p₁ = 1) (hp₂ : adj p₁ p₂ = 1)
    (hq₁ : adj v₀ q₁ = 1) (hq₂ : adj q₁ q₂ = 1)
    (hq₃ : adj q₂ q₃ = 1) (hq₄ : adj q₃ q₄ = 1) (hq₅ : adj q₄ q₅ = 1)
    (hu₁_ne_p₁ : u₁ ≠ p₁) (hu₁_ne_q₁ : u₁ ≠ q₁) (hp₁_ne_q₁ : p₁ ≠ q₁)
    (hp₂_ne_v₀ : p₂ ≠ v₀) (hq₂_ne_v₀ : q₂ ≠ v₀)
    (hq₃_ne_q₁ : q₃ ≠ q₁) (hq₄_ne_q₂ : q₄ ≠ q₂) (hq₅_ne_q₃ : q₅ ≠ q₃)
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
  -- Same-arm distinctness (from adjacency)
  have hv₀_ne_u₁ := ne_of_adj' v₀ u₁ hu₁
  have hv₀_ne_p₁ := ne_of_adj' v₀ p₁ hp₁
  have hp₁_ne_p₂ := ne_of_adj' p₁ p₂ hp₂
  have hv₀_ne_q₁ := ne_of_adj' v₀ q₁ hq₁
  have hq₁_ne_q₂ := ne_of_adj' q₁ q₂ hq₂
  have hq₂_ne_q₃ := ne_of_adj' q₂ q₃ hq₃
  have hq₃_ne_q₄ := ne_of_adj' q₃ q₄ hq₄
  have hq₄_ne_q₅ := ne_of_adj' q₄ q₅ hq₅
  -- Reversed edges
  have hp₁_v₀ : adj p₁ v₀ = 1 := (adj_comm p₁ v₀).trans hp₁
  have hp₂_p₁ : adj p₂ p₁ = 1 := (adj_comm p₂ p₁).trans hp₂
  have hq₁_v₀ : adj q₁ v₀ = 1 := (adj_comm q₁ v₀).trans hq₁
  have hq₂_q₁ : adj q₂ q₁ = 1 := (adj_comm q₂ q₁).trans hq₂
  have hq₃_q₂ : adj q₃ q₂ = 1 := (adj_comm q₃ q₂).trans hq₃
  have hq₄_q₃ : adj q₄ q₃ = 1 := (adj_comm q₄ q₃).trans hq₄
  have hq₅_q₄ : adj q₅ q₄ = 1 := (adj_comm q₅ q₄).trans hq₅
  -- Distance-2 non-edges (acyclic_no_triangle)
  have hu₁p₁ : adj u₁ p₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ p₁
      hu₁_ne_p₁ hv₀_ne_u₁.symm hv₀_ne_p₁.symm hu₁ hp₁
  have hu₁q₁ : adj u₁ q₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ q₁
      hu₁_ne_q₁ hv₀_ne_u₁.symm hv₀_ne_q₁.symm hu₁ hq₁
  have hp₁q₁ : adj p₁ q₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ p₁ q₁
      hp₁_ne_q₁ hv₀_ne_p₁.symm hv₀_ne_q₁.symm hp₁ hq₁
  have hv₀p₂ : adj v₀ p₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p₁ v₀ p₂
      hp₂_ne_v₀.symm hv₀_ne_p₁ hp₁_ne_p₂.symm hp₁_v₀ hp₂
  have hv₀q₂ : adj v₀ q₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₁ v₀ q₂
      hq₂_ne_v₀.symm hv₀_ne_q₁ hq₁_ne_q₂.symm hq₁_v₀ hq₂
  have hq₁q₃ : adj q₁ q₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₂ q₁ q₃
      hq₃_ne_q₁.symm hq₁_ne_q₂ hq₂_ne_q₃.symm hq₂_q₁ hq₃
  have hq₂q₄ : adj q₂ q₄ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₃ q₂ q₄
      hq₄_ne_q₂.symm hq₂_ne_q₃ hq₃_ne_q₄.symm hq₃_q₂ hq₄
  have hq₃q₅ : adj q₃ q₅ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₄ q₃ q₅
      hq₅_ne_q₃.symm hq₃_ne_q₄ hq₄_ne_q₅.symm hq₄_q₃ hq₅
  -- Cross-arm ne (level 1)
  have hu₁_ne_p₂ : u₁ ≠ p₂ := by intro h; rw [h] at hu₁; linarith [hv₀p₂]
  have hu₁_ne_q₂ : u₁ ≠ q₂ := by intro h; rw [h] at hu₁; linarith [hv₀q₂]
  have hp₁_ne_q₂ : p₁ ≠ q₂ := by intro h; rw [h] at hp₁; linarith [hv₀q₂]
  have hp₂_ne_q₁ : p₂ ≠ q₁ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₁, hp₁q₁]
  have hv₀_ne_q₃ : v₀ ≠ q₃ := by intro h; rw [← h] at hq₃; linarith [adj_comm q₂ v₀, hv₀q₂]
  have hq₁_ne_q₄ : q₁ ≠ q₄ := by intro h; rw [← h] at hq₄; linarith [adj_comm q₃ q₁, hq₁q₃]
  have hq₂_ne_q₅ : q₂ ≠ q₅ := by intro h; rw [← h] at hq₅; linarith [adj_comm q₄ q₂, hq₂q₄]
  -- Path nodup helpers
  have path_nodup4 : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → [a, b, c, d].Nodup := by
    intro a b c d hab hac had hbc hbd hcd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
  have path_nodup5 : ∀ (a b c d e : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e →
      b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
      [a, b, c, d, e].Nodup := by
    intro a b c d e hab hac had hae hbc hbd hbe hcd hce hde
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩
  have path_nodup6 : ∀ (a b c d e f : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ f →
      b ≠ c → b ≠ d → b ≠ e → b ≠ f →
      c ≠ d → c ≠ e → c ≠ f → d ≠ e → d ≠ f → e ≠ f →
      [a, b, c, d, e, f].Nodup := by
    intro a b c d e f hab hac had hae haf hbc hbd hbe hbf
      hcd hce hcf hde hdf hef
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩,
      ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef⟩
  have path_nodup7 : ∀ (a b c d e f g : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ f → a ≠ g →
      b ≠ c → b ≠ d → b ≠ e → b ≠ f → b ≠ g →
      c ≠ d → c ≠ e → c ≠ f → c ≠ g →
      d ≠ e → d ≠ f → d ≠ g → e ≠ f → e ≠ g → f ≠ g →
      [a, b, c, d, e, f, g].Nodup := by
    intro a b c d e f g hab hac had hae haf hag hbc hbd hbe hbf hbg
      hcd hce hcf hcg hde hdf hdg hef heg hfg
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae, haf, hag⟩, ⟨hbc, hbd, hbe, hbf, hbg⟩,
      ⟨hcd, hce, hcf, hcg⟩, ⟨hde, hdf, hdg⟩, ⟨hef, heg⟩, hfg⟩
  have path_nodup8 : ∀ (a b c d e f g h : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ f → a ≠ g → a ≠ h →
      b ≠ c → b ≠ d → b ≠ e → b ≠ f → b ≠ g → b ≠ h →
      c ≠ d → c ≠ e → c ≠ f → c ≠ g → c ≠ h →
      d ≠ e → d ≠ f → d ≠ g → d ≠ h →
      e ≠ f → e ≠ g → e ≠ h → f ≠ g → f ≠ h → g ≠ h →
      [a, b, c, d, e, f, g, h].Nodup := by
    intro a b c d e f g h₀ hab hac had hae haf hag hah hbc hbd hbe hbf hbg hbh
      hcd hce hcf hcg hch hde hdf hdg hdh hef heg heh hfg hfh hgh
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae, haf, hag, hah⟩,
      ⟨hbc, hbd, hbe, hbf, hbg, hbh⟩,
      ⟨hcd, hce, hcf, hcg, hch⟩, ⟨hde, hdf, hdg, hdh⟩,
      ⟨hef, heg, heh⟩, ⟨hfg, hfh⟩, hgh⟩
  -- Path edges helpers
  have path_edges4 : ∀ (a b c d : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d].length) →
        adj ([a, b, c, d].get ⟨k, by omega⟩)
          ([a, b, c, d].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d h₁ h₂ h₃ k hk
    have : k + 1 < 4 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> assumption
  have path_edges5 : ∀ (a b c d e : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e].length) →
        adj ([a, b, c, d, e].get ⟨k, by omega⟩)
          ([a, b, c, d, e].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e h₁ h₂ h₃ h₄ k hk
    have : k + 1 < 5 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> assumption
  have path_edges6 : ∀ (a b c d e f : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 →
      adj d e = 1 → adj e f = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e, f].length) →
        adj ([a, b, c, d, e, f].get ⟨k, by omega⟩)
          ([a, b, c, d, e, f].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e f h₁ h₂ h₃ h₄ h₅ k hk
    have : k + 1 < 6 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> assumption
  have path_edges7 : ∀ (a b c d e f g : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
      adj e f = 1 → adj f g = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e, f, g].length) →
        adj ([a, b, c, d, e, f, g].get ⟨k, by omega⟩)
          ([a, b, c, d, e, f, g].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e f g h₁ h₂ h₃ h₄ h₅ h₆ k hk
    have : k + 1 < 7 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have path_edges8 : ∀ (a b c d e f g h : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
      adj e f = 1 → adj f g = 1 → adj g h = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e, f, g, h].length) →
        adj ([a, b, c, d, e, f, g, h].get ⟨k, by omega⟩)
          ([a, b, c, d, e, f, g, h].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e f g h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ k hk
    have : k + 1 < 8 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  -- Distance-3 non-edges (4-vertex paths)
  have hu₁p₂ : adj u₁ p₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [p₂, p₁, v₀, u₁] (by simp)
      (path_nodup4 _ _ _ _ hp₁_ne_p₂.symm hp₂_ne_v₀ hu₁_ne_p₂.symm
        hv₀_ne_p₁.symm hu₁_ne_p₁.symm hv₀_ne_u₁)
      (path_edges4 _ _ _ _ hp₂_p₁ hp₁_v₀ hu₁)
  have hu₁q₂ : adj u₁ q₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₂, q₁, v₀, u₁] (by simp)
      (path_nodup4 _ _ _ _ hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm
        hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges4 _ _ _ _ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₂ : adj p₁ q₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₂, q₁, v₀, p₁] (by simp)
      (path_nodup4 _ _ _ _ hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges4 _ _ _ _ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂_ne_q₁ : p₂ ≠ q₁ := by
    intro h; rw [h] at hv₀p₂; linarith [hq₁]
  have hp₂q₁ : adj p₂ q₁ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₁, v₀, p₁, p₂] (by simp)
      (path_nodup4 _ _ _ _ hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm
        hv₀_ne_p₁ hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges4 _ _ _ _ hq₁_v₀ hp₁ hp₂)
  have hq₁_ne_q₃ : q₁ ≠ q₃ := hq₃_ne_q₁.symm
  have hv₀q₃ : adj v₀ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀] (by simp)
      (path_nodup4 _ _ _ _ hq₂_ne_q₃.symm hq₃_ne_q₁ hv₀_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hv₀_ne_q₁.symm)
      (path_edges4 _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀)
  have hq₂_ne_q₄ : q₂ ≠ q₄ := hq₄_ne_q₂.symm
  have hq₁q₄ : adj q₁ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁] (by simp)
      (path_nodup4 _ _ _ _ hq₃_ne_q₄.symm hq₄_ne_q₂ hq₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₃_ne_q₁ hq₁_ne_q₂.symm)
      (path_edges4 _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁)
  have hq₃_ne_q₅ : q₃ ≠ q₅ := hq₅_ne_q₃.symm
  have hq₂q₅ : adj q₂ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂] (by simp)
      (path_nodup4 _ _ _ _ hq₄_ne_q₅.symm hq₅_ne_q₃ hq₂_ne_q₅.symm
        hq₃_ne_q₄.symm hq₄_ne_q₂ hq₂_ne_q₃.symm)
      (path_edges4 _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂)
  -- Cross-arm ne (level 2)
  have hu₁_ne_q₃ : u₁ ≠ q₃ := by intro h; rw [h] at hu₁; linarith [hv₀q₃]
  have hp₁_ne_q₃ : p₁ ≠ q₃ := by intro h; rw [h] at hp₁; linarith [hv₀q₃]
  have hp₂_ne_q₂ : p₂ ≠ q₂ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₂, hp₁q₂]
  have hv₀_ne_q₄ : v₀ ≠ q₄ := by intro h; rw [← h] at hq₄; linarith [adj_comm q₃ v₀, hv₀q₃]
  have hq₁_ne_q₅ : q₁ ≠ q₅ := by intro h; rw [← h] at hq₅; linarith [adj_comm q₄ q₁, hq₁q₄]
  -- Distance-4 non-edges (5-vertex paths)
  have hu₁q₃ : adj u₁ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀, u₁] (by simp)
      (path_nodup5 _ _ _ _ _ hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hu₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges5 _ _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₃ : adj p₁ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀, p₁] (by simp)
      (path_nodup5 _ _ _ _ _ hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges5 _ _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂q₂ : adj p₂ q₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup5 _ _ _ _ _ hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges5 _ _ _ _ _ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  have hv₀q₄ : adj v₀ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀] (by simp)
      (path_nodup5 _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hq₁_ne_q₂.symm hq₂_ne_v₀ hv₀_ne_q₁.symm)
      (path_edges5 _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀)
  have hq₁q₅ : adj q₁ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁] (by simp)
      (path_nodup5 _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hq₂_ne_q₃.symm hq₁_ne_q₃.symm hq₁_ne_q₂.symm)
      (path_edges5 _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁)
  -- Cross-arm ne (level 3)
  have hu₁_ne_q₄ : u₁ ≠ q₄ := by intro h; rw [h] at hu₁; linarith [hv₀q₄]
  have hp₁_ne_q₄ : p₁ ≠ q₄ := by intro h; rw [h] at hp₁; linarith [hv₀q₄]
  have hp₂_ne_q₃ : p₂ ≠ q₃ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₃, hp₁q₃]
  have hv₀_ne_q₅ : v₀ ≠ q₅ := by intro h; rw [← h] at hq₅; linarith [adj_comm q₄ v₀, hv₀q₄]
  -- Distance-5 non-edges (6-vertex paths)
  have hu₁q₄ : adj u₁ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀, u₁] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hu₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hu₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges6 _ _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₄ : adj p₁ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀, p₁] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges6 _ _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂q₃ : adj p₂ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm hp₂_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges6 _ _ _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  have hv₀q₅ : adj v₀ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hq₁_ne_q₂.symm hq₂_ne_v₀ hv₀_ne_q₁.symm)
      (path_edges6 _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀)
  -- Cross-arm ne (level 4)
  have hu₁_ne_q₅ : u₁ ≠ q₅ := by intro h; rw [h] at hu₁; linarith [hv₀q₅]
  have hp₁_ne_q₅ : p₁ ≠ q₅ := by intro h; rw [h] at hp₁; linarith [hv₀q₅]
  have hp₂_ne_q₄ : p₂ ≠ q₄ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₄, hp₁q₄]
  -- Distance-6 non-edges (7-vertex paths)
  have hu₁q₅ : adj u₁ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀, u₁] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm hu₁_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hu₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hu₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges7 _ _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₅ : adj p₁ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀, p₁] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm hp₁_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges7 _ _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂q₄ : adj p₂ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm hp₂_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm hp₂_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges7 _ _ _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  -- Cross-arm ne (level 5)
  have hp₂_ne_q₅ : p₂ ≠ q₅ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₅, hp₁q₅]
  -- Distance-7 non-edge (8-vertex path)
  have hp₂q₅ : adj p₂ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup8 _ _ _ _ _ _ _ _
        hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm hp₁_ne_q₅.symm hp₂_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm hp₂_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm hp₂_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges8 _ _ _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  -- Construct the embedding φ : Fin 9 ↪ Fin n for T(1,2,5)
  -- Map: 0→v₀, 1→u₁, 2→p₁, 3→p₂, 4→q₁, 5→q₂, 6→q₃, 7→q₄, 8→q₅
  let φ_fun : Fin 9 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => v₀  | ⟨1, _⟩ => u₁  | ⟨2, _⟩ => p₁
    | ⟨3, _⟩ => p₂  | ⟨4, _⟩ => q₁  | ⟨5, _⟩ => q₂
    | ⟨6, _⟩ => q₃  | ⟨7, _⟩ => q₄  | ⟨8, _⟩ => q₅
  have φ_inj : Function.Injective φ_fun := by
    intro i j hij; simp only [φ_fun] at hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exact absurd hij ‹_›)
      | (exact absurd hij.symm ‹_›)
  let φ : Fin 9 ↪ Fin n := ⟨φ_fun, φ_inj⟩
  have hembed : ∀ i j, t125Adj i j = adj (φ i) (φ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [t125Adj, φ, φ_fun] <;> norm_num <;>
      linarith [hdiag v₀, hdiag u₁, hdiag p₁, hdiag p₂,
        hdiag q₁, hdiag q₂, hdiag q₃, hdiag q₄, hdiag q₅,
        hu₁, hp₁, hp₂, hq₁, hq₂, hq₃, hq₄, hq₅,
        adj_comm v₀ u₁, adj_comm v₀ p₁, adj_comm v₀ p₂,
        adj_comm v₀ q₁, adj_comm v₀ q₂, adj_comm v₀ q₃,
        adj_comm v₀ q₄, adj_comm v₀ q₅,
        adj_comm u₁ p₁, adj_comm u₁ p₂,
        adj_comm u₁ q₁, adj_comm u₁ q₂, adj_comm u₁ q₃,
        adj_comm u₁ q₄, adj_comm u₁ q₅,
        adj_comm p₁ p₂, adj_comm p₁ q₁, adj_comm p₁ q₂,
        adj_comm p₁ q₃, adj_comm p₁ q₄, adj_comm p₁ q₅,
        adj_comm p₂ q₁, adj_comm p₂ q₂, adj_comm p₂ q₃,
        adj_comm p₂ q₄, adj_comm p₂ q₅,
        adj_comm q₁ q₂, adj_comm q₁ q₃, adj_comm q₁ q₄, adj_comm q₁ q₅,
        adj_comm q₂ q₃, adj_comm q₂ q₄, adj_comm q₂ q₅,
        adj_comm q₃ q₄, adj_comm q₃ q₅,
        adj_comm q₄ q₅,
        hu₁p₁, hu₁q₁, hp₁q₁, hv₀p₂, hv₀q₂, hq₁q₃, hq₂q₄, hq₃q₅,
        hu₁p₂, hu₁q₂, hp₁q₂, hp₂q₁, hv₀q₃, hq₁q₄, hq₂q₅,
        hu₁q₃, hp₁q₃, hp₂q₂, hv₀q₄, hq₁q₅,
        hu₁q₄, hp₁q₄, hp₂q₃, hv₀q₅,
        hu₁q₅, hp₁q₅, hp₂q₄,
        hp₂q₅]
  exact subgraph_infinite_type_transfer_per_kQ φ F Q
    (t125_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

end Etingof
