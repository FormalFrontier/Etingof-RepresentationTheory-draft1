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
of `v₀`'s neighbours of degree `< 3`, and one specified neighbour `leaf`
of `v₀` having degree 1, the dimension-vector set of indecomposable
representations is infinite for every algebraically closed `F` and every
orientation `Q` of `adj`.

Mirrors the inline `leaf_case` at
`Chapter6/InfiniteTypeConstructions.lean:9770` inside
`non_adjacent_branches_infinite_type`, but with the embedding strategy
adapted to the per-(F, Q) forbidden-subgraph library on `main`
(no `dTilde_not_finite_type_per_kQ` for general `n`). See the file
docstring for the strategy.

**API stub** (issue #2922): the body is `sorry` pending the proof
tracked by a follow-up issue. The signature exists so that the outer
assembly `non_adjacent_branches_infinite_type_per_kQ` (issue #2923)
can dispatch to it by name. -/
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
  -- TODO (follow-up to #2922): replace this `sorry` with the case-split
  -- proof. Sketch:
  -- 1. Mirror lines 9779-10120 of `InfiniteTypeConstructions.lean`
  --    (universal `leaf_case`) to extract `chain : List (Fin n)` from
  --    `hconn` (the `v₀ → w` Nodup path with length ≥ 3), then extract
  --    `v₀`'s third neighbour `side_arm` (not `leaf`, not `chain[1]`)
  --    and `w`'s two non-chain neighbours `arm₁, arm₂`. Establish the
  --    full distinctness lattice (`leaf_ne_chain`, `side_ne_chain`,
  --    `arm₁_ne_chain`, `arm₂_ne_chain`, cross-region neqs via
  --    `acyclic_path_nonadj` and `leaf_only`).
  -- 2. Case-split on `(chain.length, side.deg, arm₁.deg, arm₂.deg)`
  --    and embed one of the available per-(F, Q) forbidden subgraphs:
  --    * `T(1, 2, 5)` (via `embed_t125_in_tree_per_kQ` /
  --      `t125_not_finite_type_per_kQ`) — primary tool when a long
  --      arm is available.
  --    * `Ẽ₇ = T(1, 3, 3)` (via a new `embed_etilde7_in_tree_per_kQ`
  --      helper to be ported from the universal proof, then
  --      `etilde7_not_finite_type_per_kQ`).
  --    * `Ẽ₆ = T(2, 2, 2)` (via a new `embed_etilde6_in_tree_per_kQ`
  --      helper, then `etilde6_not_finite_type_per_kQ`) — when three
  --      arms of length 2 are available from `w` (the chain extends
  --      one arm; both `arm₁` and `arm₂` extend the other two).
  --    Each case feeds `subgraph_infinite_type_transfer_per_kQ` with
  --    `restrictOrientationViaEmb_isOrientationOf` on `hOrient`.
  --
  -- Reference: `single_branch_leaf_case_per_kQ`
  -- (`Chapter6/FieldGenericTpqr.lean:1306`) for the case-split pattern
  -- on arm degrees; `adjacent_branches_infinite_type_per_kQ`
  -- (`Chapter6/FieldGenericD5Tilde.lean:1043`) for the embed-dispatch
  -- pattern.
  let _ := hn; let _ := hsymm; let _ := hdiag; let _ := h01; let _ := hconn
  let _ := h_acyclic; let _ := h_deg; let _ := hv₀; let _ := hw; let _ := hne
  let _ := h_no_adj_branch; let _ := h_v₀w_nonadj; let _ := h_leaf_adj
  let _ := h_leaf_deg; let _ := hOrient
  sorry

end Etingof
