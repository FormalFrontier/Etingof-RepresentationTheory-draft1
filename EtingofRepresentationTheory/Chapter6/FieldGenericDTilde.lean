import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericStar
import EtingofRepresentationTheory.Chapter6.FieldGenericD5Tilde

/-!
# Field-Generic parametric D̃_{k+5} representation (per-(F, Q))

This module ports the universal (ℂ, canonical-orientation) D̃_{k+5}
infinite-type construction
(`dTildeRep` / `dTilde_not_finite_type`,
`InfiniteTypeConstructions.lean:2288-3191`) to the **per-(field,
orientation)** setting needed by the field-generic forbidden-subgraph
library. It is the parametric (Option A) analogue of the fixed-shape
helpers `FieldGenericD{6,7,8}Tilde.lean`, parametric in `k : ℕ` over the
vertex type `Fin (k + 6)`.

The underlying adjacency / quiver / orientation data is **reused** from
`InfiniteTypeConstructions.lean`:
* `dTildeAdj k` (`:2007`) — the D̃_{k+5} adjacency matrix,
* `dTildeQuiver k` (`:2034`) — the canonical orientation quiver,
* `dTildeOrientation_isOrientationOf k` (`:2050`),
* `dTildeDim k m` (`:2203`) — the dimension vector.

What this file adds is the **direction-aware** representation
`dTildeRep_kQ` valid for an *arbitrary* orientation `Q` of `dTildeAdj k`
over an *arbitrary* field `F`, mirroring `d8tildeRep_kQ`
(`FieldGenericD8Tilde.lean:205`) but parametric in the chain length.

## Deliverables in this file (sub-issue 1 of #2978)

* `dTildeRepMap_kQ` — the per-(F, Q) direction-aware map function.
* `dTildeRep_kQ` — the representation (noncomputable def, no sorry).
* `dTildeRep_kQ_dimVec` — its dimension vector is `dTildeDim k m`.
* `dTildeRep_kQ_isIndecomposable` — **deferred sorry body**, mirroring
  the `d{5,7,8}tildeRep_kQ_isIndecomposable` precedent. Tracked by a
  follow-up sub-issue.
* `dTilde_not_finite_type_per_kQ` — the per-(F, Q) infinite-type
  theorem (carries the indecomposability sorry transitively).

The remaining embedding helper `embed_dtilde_in_tree_per_kQ` (taking a
host chain of arbitrary length) and the dispatch wiring in
`FieldGenericNonAdjacentBranches.lean` are tracked by separate
follow-up sub-issues.

See `FieldGenericInfiniteType.lean` for the `_F` / `_kQ` / `_per_kQ`
naming conventions.
-/

open scoped Matrix
open Finset

namespace Etingof

/-! ## Section 1: Dimension cast (F-generic)

`dTildeCast_F` is the field-generic analogue of `dTildeCast`
(`InfiniteTypeConstructions.lean:2235`). It reindexes a linear map
`(Fin p → F) →ₗ (Fin q → F)` through dimension equalities so the result
lands on the `dTildeDim`-indexed function spaces. -/

/-- Reindex a linear map between `Fin`-indexed `F`-function spaces through
dimension equalities. F-generic analogue of `dTildeCast`. -/
private noncomputable def dTildeCast_F {F : Type} [Field F] {p q p' q' : ℕ}
    (hp : p' = p) (hq : q' = q)
    (G : (Fin p → F) →ₗ[F] (Fin q → F)) :
    (Fin p' → F) →ₗ[F] (Fin q' → F) :=
  (LinearEquiv.funCongrLeft F F (finCongr hq)).toLinearMap ∘ₗ
    G ∘ₗ (LinearEquiv.funCongrLeft F F (finCongr hp.symm)).toLinearMap

/-! ## Section 2: Direction-aware match-based representation map

For an arbitrary orientation `Q` of `dTildeAdj k`, each of the
`(k + 5)` edges may point in either direction. The map function below
provides the canonical forward map and a reverse map per edge, mirroring
the universal `dTildeRepMap` (`InfiniteTypeConstructions.lean:2250`) on
the canonical direction and `d8tildeRepMap_kQ`
(`FieldGenericD8Tilde.lean:161`) on the per-edge direction split:

* `{0, 2}`, `{1, 2}`: `starEmbed1_F / starEmbed2_F` (toward the left
  branch point `2`) and `starFirst_F / starSecond_F` (reverses).
* `{2, 3}`: `d5tildeGamma_F` (canonical `2 → 3`) and `d5tildeGammaInv_F`
  (reverse `3 → 2`).
* interior path edges `{i, i+1}` for `3 ≤ i`, `i + 1 ≤ k + 3`:
  `LinearMap.id` in both directions (equal-dimension blocks).
* `{k+4, k+3}`, `{k+5, k+3}`: `starEmbed1_F / starEmbed2_F` (toward the
  right branch point `k + 3`) and `starFirst_F / starSecond_F`
  (reverses).

Outside these directed edges the map is `0` (ruled out by `hOrient`). -/

/-- Direction-aware match-based map for the orientation-generic
parametric D̃_{k+5} representation over a field `F`. -/
private noncomputable def dTildeRepMap_kQ (F : Type) [Field F] (k m : ℕ)
    (a b : Fin (k + 6)) :
    (Fin (dTildeDim k m a) → F) →ₗ[F] (Fin (dTildeDim k m b) → F) :=
  -- Edge {0, 2}
  if h : a.val = 0 ∧ b.val = 2 then
    dTildeCast_F
      (show dTildeDim k m a = m + 1 by simp [dTildeDim]; omega)
      (show dTildeDim k m b = 2 * (m + 1) by simp [dTildeDim]; omega)
      (starEmbed1_F F m)
  else if h : a.val = 2 ∧ b.val = 0 then
    dTildeCast_F
      (show dTildeDim k m a = 2 * (m + 1) by simp [dTildeDim]; omega)
      (show dTildeDim k m b = m + 1 by simp [dTildeDim]; omega)
      (starFirst_F F m)
  -- Edge {1, 2}
  else if h : a.val = 1 ∧ b.val = 2 then
    dTildeCast_F
      (show dTildeDim k m a = m + 1 by simp [dTildeDim]; omega)
      (show dTildeDim k m b = 2 * (m + 1) by simp [dTildeDim]; omega)
      (starEmbed2_F F m)
  else if h : a.val = 2 ∧ b.val = 1 then
    dTildeCast_F
      (show dTildeDim k m a = 2 * (m + 1) by simp [dTildeDim]; omega)
      (show dTildeDim k m b = m + 1 by simp [dTildeDim]; omega)
      (starSecond_F F m)
  -- Edge {2, 3}
  else if h : a.val = 2 ∧ b.val = 3 then
    dTildeCast_F
      (show dTildeDim k m a = 2 * (m + 1) by simp [dTildeDim]; omega)
      (show dTildeDim k m b = 2 * (m + 1) by simp [dTildeDim]; omega)
      (d5tildeGamma_F F m)
  else if h : a.val = 3 ∧ b.val = 2 then
    dTildeCast_F
      (show dTildeDim k m a = 2 * (m + 1) by simp [dTildeDim]; omega)
      (show dTildeDim k m b = 2 * (m + 1) by simp [dTildeDim]; omega)
      (d5tildeGammaInv_F F m)
  -- Interior path edge, forward: 3 ≤ a, a + 1 = b, b ≤ k + 3
  else if h : 3 ≤ a.val ∧ a.val + 1 = b.val ∧ b.val ≤ k + 3 then
    dTildeCast_F
      (show dTildeDim k m a = 2 * (m + 1) by simp [dTildeDim]; omega)
      (show dTildeDim k m b = 2 * (m + 1) by simp [dTildeDim]; omega)
      (LinearMap.id : (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (2 * (m + 1)) → F))
  -- Interior path edge, backward: 3 ≤ b, b + 1 = a, a ≤ k + 3
  else if h : 3 ≤ b.val ∧ b.val + 1 = a.val ∧ a.val ≤ k + 3 then
    dTildeCast_F
      (show dTildeDim k m a = 2 * (m + 1) by simp [dTildeDim]; omega)
      (show dTildeDim k m b = 2 * (m + 1) by simp [dTildeDim]; omega)
      (LinearMap.id : (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (2 * (m + 1)) → F))
  -- Edge {k+4, k+3}
  else if h : a.val = k + 4 ∧ b.val = k + 3 then
    dTildeCast_F
      (show dTildeDim k m a = m + 1 by simp [dTildeDim]; omega)
      (show dTildeDim k m b = 2 * (m + 1) by simp [dTildeDim]; omega)
      (starEmbed1_F F m)
  else if h : a.val = k + 3 ∧ b.val = k + 4 then
    dTildeCast_F
      (show dTildeDim k m a = 2 * (m + 1) by simp [dTildeDim]; omega)
      (show dTildeDim k m b = m + 1 by simp [dTildeDim]; omega)
      (starFirst_F F m)
  -- Edge {k+5, k+3}
  else if h : a.val = k + 5 ∧ b.val = k + 3 then
    dTildeCast_F
      (show dTildeDim k m a = m + 1 by simp [dTildeDim]; omega)
      (show dTildeDim k m b = 2 * (m + 1) by simp [dTildeDim]; omega)
      (starEmbed2_F F m)
  else if h : a.val = k + 3 ∧ b.val = k + 5 then
    dTildeCast_F
      (show dTildeDim k m a = 2 * (m + 1) by simp [dTildeDim]; omega)
      (show dTildeDim k m b = m + 1 by simp [dTildeDim]; omega)
      (starSecond_F F m)
  else
    0

/-! ## Section 3: The orientation-generic parametric representation -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic parametric D̃_{k+5} representation over an
arbitrary field `F` with arbitrary orientation `Q` of `dTildeAdj k`.
Dimension vector follows `dTildeDim k m`: interior vertices `2, …, k+3`
have dim `2(m+1)`; the four leaf vertices `0, 1, k+4, k+5` have dim
`m+1`.

The map on an arrow `e : Q.Hom a b` depends only on the underlying
unordered edge `{a, b}` and the direction `a → b` (see
`dTildeRepMap_kQ`). The orientation hypothesis `hOrient` is not used by
the construction itself; it is recorded so that downstream lemmas (the
deferred indecomposability proof) can pattern-match on which arrows
exist. Mirrors `d8tildeRep_kQ` (`FieldGenericD8Tilde.lean:205`). -/
noncomputable def dTildeRep_kQ
    (F : Type) [Field F] (k : ℕ)
    (Q : @Quiver.{0, 0} (Fin (k + 6)))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin (k + 6)) Q a b)]
    (_hOrient : @Etingof.IsOrientationOf (k + 6) Q (dTildeAdj k))
    (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin (k + 6)) _ Q := by
  letI := Q
  exact {
    obj := fun v => Fin (dTildeDim k m v) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => dTildeRepMap_kQ F k m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The orientation-generic parametric D̃_{k+5} rep has the expected
dimension vector `dTildeDim k m` at each vertex. -/
theorem dTildeRep_kQ_dimVec
    (F : Type) [Field F] (k : ℕ)
    (Q : @Quiver.{0, 0} (Fin (k + 6)))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin (k + 6)) Q a b)]
    (hOrient : @Etingof.IsOrientationOf (k + 6) Q (dTildeAdj k))
    (m : ℕ) (v : Fin (k + 6)) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin (k + 6)) _ Q
      (dTildeRep_kQ F k Q hOrient m) v ≃ₗ[F] (Fin (dTildeDim k m v) → F)) :=
  ⟨LinearEquiv.refl F _⟩

/-! ## Section 4: Indecomposability (deferred sorry)

The body of the indecomposability proof is deferred to a follow-up
sub-issue, mirroring the precedent of
`d5tildeRep_kQ_isIndecomposable` (`FieldGenericD5Tilde.lean`, #2834),
`d7tildeRep_kQ_isIndecomposable` (`FieldGenericD7Tilde.lean`, #2967),
and `d8tildeRep_kQ_isIndecomposable` (`FieldGenericD8Tilde.lean`). The
per-(F, Q) infinite-type theorem below transitively depends on this
sorry.
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic indecomposability of `dTildeRep_kQ`.

The proof body is deferred to a follow-up sub-issue (the parametric
analogue of `d8tildeRep_kQ_isIndecomposable`, which is itself
sorry-deferred). Closing this sorry requires F-generic versions of the
leaf-subspace equalities used by the ℂ-specific universal proof
`dTildeRep_isIndecomposable` (`InfiniteTypeConstructions.lean:3114`),
parameterised across each of the `(k + 5)` possible arrow directions;
the d5tilde/d7tilde/d8tilde precedents show this is a multi-hundred-line
construction. The consumer `dTilde_not_finite_type_per_kQ` carries this
sorry transitively. -/
theorem dTildeRep_kQ_isIndecomposable
    (F : Type) [Field F] [IsAlgClosed F] (k : ℕ)
    (Q : @Quiver.{0, 0} (Fin (k + 6)))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin (k + 6)) Q a b)]
    (hOrient : @Etingof.IsOrientationOf (k + 6) Q (dTildeAdj k))
    (m : ℕ) :
    (dTildeRep_kQ F k Q hOrient m).IsIndecomposable := by
  refine ⟨?_, ?_⟩
  · -- Nontriviality: vertex `0` is a leaf with dimension `m + 1 ≥ 1`, and the
    -- function space `Fin (m + 1) → F` over the field `F` is nontrivial.
    refine ⟨⟨0, by omega⟩, ?_⟩
    have hdim : dTildeDim k m (⟨0, by omega⟩ : Fin (k + 6)) = m + 1 := by
      simp [dTildeDim]
    haveI : Nonempty (Fin (dTildeDim k m (⟨0, by omega⟩ : Fin (k + 6)))) :=
      ⟨⟨0, by rw [hdim]; omega⟩⟩
    obtain ⟨e⟩ := dTildeRep_kQ_dimVec F k Q hOrient m ⟨0, by omega⟩
    exact e.toEquiv.nontrivial
  · -- Decomposition core (deferred to a follow-up sub-issue of #2978).
    --
    -- This is the genuinely hard, k-parametric, orientation-generic part:
    -- given invariant complementary subspaces `W₁ v, W₂ v` at every vertex,
    -- show `W₁ v = ⊥` for all `v` or `W₂ v = ⊥` for all `v`.
    --
    -- The structural template is the ℂ-specific universal proof
    -- `dTildeRep_isIndecomposable` (`InfiniteTypeConstructions.lean:3114`),
    -- which transports through a `DTildeVertex`-indexed representation and
    -- ultimately rests on `dTildeRep'_isIndecomposable` (line 2431). The
    -- per-(F, Q) version must instead case-split on the direction of each of
    -- the `(k + 5)` edges (`fin_cases` over the edge lattice does not
    -- generalise in `k`), establish F-generic leaf-subspace equalities at the
    -- four leaves `0, 1, k+4, k+5`, and propagate constancy along the interior
    -- chain `2, …, k+3` (whose maps are `LinearMap.id`) by induction on the
    -- chain length. None of the fixed-shape precedents
    -- (`d{5,7,8}tildeRep_kQ_isIndecomposable`) are yet closed, so no reusable
    -- F-generic leaf equalities exist to build on. See the follow-up sub-issue.
    intro W₁ W₂ _hW₁ _hW₂ _hCompl
    sorry

/-! ## Section 5: Per-(F, Q) infinite-type theorem -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) parametric D̃_{k+5} infinite-type theorem:
for any algebraically closed field `F` and any orientation `Q` of
`dTildeAdj k`, the set of dimension vectors of indecomposable
representations is infinite. Mirrors the proof shape of
`d8tilde_not_finite_type_per_kQ` (`FieldGenericD8Tilde.lean:281`) and
the universal `dTilde_not_finite_type`
(`InfiniteTypeConstructions.lean:3176`).

Injectivity comes from vertex `0`, where `dTildeDim k m 0 = m + 1`.

This theorem carries no direct `sorry`, but transitively depends on
`dTildeRep_kQ_isIndecomposable`, whose proof body is deferred — see its
docstring. -/
theorem dTilde_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F] (k : ℕ)
    (Q : @Quiver.{0, 0} (Fin (k + 6)))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin (k + 6)) Q a b)]
    (hOrient : @Etingof.IsOrientationOf (k + 6) Q (dTildeAdj k)) :
    ¬ Set.Finite
      {d : Fin (k + 6) → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin (k + 6)) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ, dTildeDim k m ∈
      {d : Fin (k + 6) → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin (k + 6)) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨dTildeRep_kQ F k Q hOrient m,
      dTildeRep_kQ_isIndecomposable F k Q hOrient m,
      dTildeRep_kQ_dimVec F k Q hOrient m⟩
  have hinj : Function.Injective (dTildeDim k : ℕ → Fin (k + 6) → ℕ) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨0, by omega⟩
    have hnot : ¬(2 ≤ (⟨0, by omega⟩ : Fin (k + 6)).val ∧
      (⟨0, by omega⟩ : Fin (k + 6)).val ≤ k + 3) := by simp
    simp only [dTildeDim, hnot, ite_false] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section 6: Embedding D̃_{k+5} into a host tree (per-(F, Q) helper)

Chain-length-general analogue of `embed_d8tilde_in_tree_per_kQ`
(`FieldGenericD8Tilde.lean`). Given a host acyclic adjacency matrix with
two degree-3 branch points `v₀`, `w` connected by an internal `Nodup`
chain `chain` of length `≥ 3` (`chain.get 0 = v₀`,
`chain.get (length-1) = w`), each branch point carrying two extra leaves
(`leaf, side_arm` at `v₀`; `arm₁, arm₂` at `w`), this embeds D̃_{k+5}
with `k = chain.length - 2` and dispatches via
`subgraph_infinite_type_transfer_per_kQ` and
`dTilde_not_finite_type_per_kQ`.

Unlike the fixed-shape `embed_d{6,7,8}tilde_in_tree_per_kQ` helpers
(which enumerate the full pair lattice with `fin_cases`), the non-edges
are obtained uniformly from `tree_embed_adj_eq` plus
`dTilde_nodup_path_between`, so the proof is genuinely parametric in the
chain length. The vertex map matches `dTildeAdj k`:
`0 → leaf, 1 → side_arm, 2 → v₀ = chain[0], …, k+3 → w = chain[k+1],
k+4 → arm₁, k+5 → arm₂`, with spine vertices `2, …, k+3` covering the
chain. -/
set_option maxHeartbeats 1600000 in
-- The injectivity case-split and the per-edge `simp only` dispatch run a
-- sizeable case analysis over the `k`-parametric vertex lattice,
-- exceeding the default 200k heartbeat limit.
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) embedding of D̃_{k+5} into a host acyclic adjacency
matrix along an internal chain of arbitrary length. -/
theorem embed_dtilde_in_tree_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (v₀ w : Fin n)
    (chain : List (Fin n))
    (hchain_len : 3 ≤ chain.length)
    (hchain_nodup : chain.Nodup)
    (hchain_first : chain.get ⟨0, by omega⟩ = v₀)
    (hchain_get_last : chain.get ⟨chain.length - 1, by omega⟩ = w)
    (hchain_edges : ∀ t, (ht : t + 1 < chain.length) →
      adj (chain.get ⟨t, by omega⟩) (chain.get ⟨t + 1, ht⟩) = 1)
    (leaf side_arm arm₁ arm₂ : Fin n)
    (leaf_adj_v₀ : adj leaf v₀ = 1) (side_adj_v₀ : adj side_arm v₀ = 1)
    (arm₁_adj_w : adj arm₁ w = 1) (arm₂_adj_w : adj arm₂ w = 1)
    (leaf_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
      leaf ≠ chain.get ⟨idx, hidx⟩)
    (side_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
      side_arm ≠ chain.get ⟨idx, hidx⟩)
    (arm₁_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
      arm₁ ≠ chain.get ⟨idx, hidx⟩)
    (arm₂_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
      arm₂ ≠ chain.get ⟨idx, hidx⟩)
    (hleaf_ne_arm₁ : leaf ≠ arm₁) (hleaf_ne_arm₂ : leaf ≠ arm₂)
    (hside_ne_arm₁ : side_arm ≠ arm₁) (hside_ne_arm₂ : side_arm ≠ arm₂)
    (harm₁₂ : arm₁ ≠ arm₂) (hside_ne_leaf : side_arm ≠ leaf)
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  set k := chain.length - 2 with hk_def
  have hk_add : k + 2 = chain.length := by omega
  -- Define the embedding φ : Fin (k+6) → Fin n
  let φ_fun : Fin (k + 6) → Fin n := fun ⟨i, _⟩ =>
    if i = 0 then leaf
    else if i = 1 then side_arm
    else if h : i ≤ k + 3 then chain.get ⟨i - 2, by omega⟩
    else if i = k + 4 then arm₁
    else arm₂
  -- Prove φ_fun is injective
  have φ_inj : Function.Injective φ_fun := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    simp only [Fin.mk.injEq]
    -- Unfold φ_fun let binding
    dsimp only [φ_fun] at heq
    -- Case analysis on regions
    by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;>
    by_cases ha1 : a = 1 <;> by_cases hb1 : b = 1 <;>
    by_cases haS : a ≤ k + 3 <;> by_cases hbS : b ≤ k + 3 <;>
    by_cases ha4 : a = k + 4 <;> by_cases hb4 : b = k + 4
    all_goals (simp only [ha0, hb0, ha1, hb1, haS, hbS, ha4, hb4,
      ite_true, ite_false, dite_true, dite_false, eq_self_iff_true,
      show (1:ℕ) = 0 ↔ False from by decide,
      show (1:ℕ) = 1 ↔ True from by decide,
      show (0:ℕ) = 0 ↔ True from by decide,
      show (k + 4 : ℕ) ≠ 0 from by omega,
      show (k + 4 : ℕ) ≠ 1 from by omega,
      show ¬((k + 4 : ℕ) ≤ k + 3) from by omega,
      show (k + 5 : ℕ) ≠ 0 from by omega,
      show (k + 5 : ℕ) ≠ 1 from by omega,
      show ¬((k + 5 : ℕ) ≤ k + 3) from by omega,
      show (k + 5 : ℕ) ≠ k + 4 from by omega,
      show (k + 3 : ℕ) ≠ 0 from by omega,
      show (k + 3 : ℕ) ≠ 1 from by omega,
      show (k + 3 : ℕ) ≤ k + 3 from by omega] at heq ⊢ <;> try omega)
    -- Remaining cross-region collision cases (try all orientations)
    all_goals first
      | exact absurd heq (leaf_ne_chain _ _)
      | exact absurd heq.symm (leaf_ne_chain _ _)
      | exact absurd heq (side_ne_chain _ _)
      | exact absurd heq.symm (side_ne_chain _ _)
      | exact absurd heq (arm₁_ne_chain _ _)
      | exact absurd heq.symm (arm₁_ne_chain _ _)
      | exact absurd heq (arm₂_ne_chain _ _)
      | exact absurd heq.symm (arm₂_ne_chain _ _)
      | exact absurd heq hleaf_ne_arm₁
      | exact absurd heq.symm hleaf_ne_arm₁
      | exact absurd heq hleaf_ne_arm₂
      | exact absurd heq.symm hleaf_ne_arm₂
      | exact absurd heq hside_ne_arm₁
      | exact absurd heq.symm hside_ne_arm₁
      | exact absurd heq hside_ne_arm₂
      | exact absurd heq.symm hside_ne_arm₂
      | exact absurd heq harm₁₂
      | exact absurd heq.symm harm₁₂
      | exact absurd heq hside_ne_leaf
      | exact absurd heq.symm hside_ne_leaf
      | (have := (hchain_nodup.get_inj_iff).mp heq; simp at this; omega)
  let φ : Fin (k + 6) ↪ Fin n := ⟨φ_fun, φ_inj⟩
  -- Edge preservation: D̃ edges map to host edges
  have hedges : ∀ i j : Fin (k + 6), dTildeAdj k i j = 1 →
      adj (φ i) (φ j) = 1 := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    rcases (dTildeAdj_eq_one_iff k ⟨a, ha⟩ ⟨b, hb⟩).mp hab with hp | hp <;>
      simp only [dTildeEdgePred] at hp <;>
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h12, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    -- Forward edges
    · -- 0→2: leaf → v₀
      show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
      dsimp only [φ_fun]
      simp only [h1, h2, ite_true, show (2:ℕ) ≠ 0 from by omega,
        show (2:ℕ) ≠ 1 from by omega, ite_false, show (2:ℕ) ≤ k + 3 from by omega,
        dite_true]
      rw [show chain.get ⟨2 - 2, _⟩ = chain.get ⟨0, by omega⟩ from by congr 1,
          hchain_first]
      exact leaf_adj_v₀
    · -- 1→2: side_arm → v₀
      show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
      dsimp only [φ_fun]
      simp only [h1, h2, show (1:ℕ) ≠ 0 from by omega, ite_true, ite_false,
        show (2:ℕ) ≠ 0 from by omega, show (2:ℕ) ≠ 1 from by omega,
        show (2:ℕ) ≤ k + 3 from by omega, dite_true]
      rw [show chain.get ⟨2 - 2, _⟩ = chain.get ⟨0, by omega⟩ from by congr 1,
          hchain_first]
      exact side_adj_v₀
    · -- Spine edge a→b (a+1=b, 2≤a, b≤k+3)
      show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
      dsimp only [φ_fun]
      have ha0 : a ≠ 0 := by omega
      have ha1 : a ≠ 1 := by omega
      have haS : a ≤ k + 3 := by omega
      have hb0 : b ≠ 0 := by omega
      have hb1 : b ≠ 1 := by omega
      simp only [ha0, ha1, haS, hb0, hb1, h2, ite_true, ite_false, dite_true]
      have hb_idx : b - 2 = a - 2 + 1 := by omega
      rw [show chain.get ⟨b - 2, _⟩ = chain.get ⟨a - 2 + 1, by omega⟩ from by
            congr 1; exact Fin.ext hb_idx]
      exact hchain_edges (a - 2) (by omega)
    · -- (k+4)→(k+3): arm₁ → w (h1: a=k+4, h2: b=k+3)
      show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
      dsimp only [φ_fun]
      simp only [h1, show (k + 4 : ℕ) ≠ 0 from by omega,
        show (k + 4 : ℕ) ≠ 1 from by omega,
        show ¬(k + 4 ≤ k + 3) from by omega, ite_true, ite_false,
        h2, show (k + 3 : ℕ) ≠ 0 from by omega,
        show (k + 3 : ℕ) ≠ 1 from by omega,
        show (k + 3 : ℕ) ≤ k + 3 from by omega, dite_true]
      have hb_eq : k + 3 - 2 = chain.length - 1 := by omega
      rw [show chain.get ⟨k + 3 - 2, _⟩ = chain.get ⟨chain.length - 1, by omega⟩ from by
            congr 1; exact Fin.ext hb_eq,
          hchain_get_last]
      exact arm₁_adj_w
    · -- (k+5)→(k+3): arm₂ → w (h1: a=k+5, h2: b=k+3)
      show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
      dsimp only [φ_fun]
      simp only [h1, show (k + 5 : ℕ) ≠ 0 from by omega,
        show (k + 5 : ℕ) ≠ 1 from by omega,
        show ¬(k + 5 ≤ k + 3) from by omega,
        show (k + 5 : ℕ) ≠ k + 4 from by omega, ite_true, ite_false,
        h2, show (k + 3 : ℕ) ≠ 0 from by omega,
        show (k + 3 : ℕ) ≠ 1 from by omega,
        show (k + 3 : ℕ) ≤ k + 3 from by omega, dite_true]
      have hb_eq : k + 3 - 2 = chain.length - 1 := by omega
      rw [show chain.get ⟨k + 3 - 2, _⟩ = chain.get ⟨chain.length - 1, by omega⟩ from by
            congr 1; exact Fin.ext hb_eq,
          hchain_get_last]
      exact arm₂_adj_w
    -- Backward edges (symmetric)
    · -- 2→0: v₀ → leaf (h1: b=0, h2: a=2)
      show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
      dsimp only [φ_fun]
      simp only [h2, h1, ite_true, ite_false,
        show (2:ℕ) ≠ 0 from by omega, show (2:ℕ) ≠ 1 from by omega,
        show (2:ℕ) ≤ k + 3 from by omega, dite_true]
      rw [show chain.get ⟨2 - 2, _⟩ = chain.get ⟨0, by omega⟩ from by congr 1,
          hchain_first]
      exact (adj_comm v₀ leaf).trans leaf_adj_v₀
    · -- 2→1: v₀ → side_arm (h1: b=1, h2: a=2)
      show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
      dsimp only [φ_fun]
      simp only [h2, h1, ite_true, ite_false,
        show (2:ℕ) ≠ 0 from by omega, show (2:ℕ) ≠ 1 from by omega,
        show (2:ℕ) ≤ k + 3 from by omega, dite_true,
        show (1:ℕ) ≠ 0 from by omega]
      rw [show chain.get ⟨2 - 2, _⟩ = chain.get ⟨0, by omega⟩ from by congr 1,
          hchain_first]
      exact (adj_comm v₀ side_arm).trans side_adj_v₀
    · -- Spine backward (h1: 2≤b, h12: b+1=a, h2: a≤k+3)
      show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
      dsimp only [φ_fun]
      have hb0 : b ≠ 0 := by omega
      have hb1 : b ≠ 1 := by omega
      have hbS : b ≤ k + 3 := by omega
      have ha0 : a ≠ 0 := by omega
      have ha1 : a ≠ 1 := by omega
      simp only [ha0, ha1, show a ≤ k + 3 from by omega, hb0, hb1, hbS,
        ite_true, ite_false, dite_true]
      rw [adj_comm]
      have ha_idx : a - 2 = b - 2 + 1 := by omega
      rw [show chain.get ⟨a - 2, _⟩ = chain.get ⟨b - 2 + 1, by omega⟩ from by
            congr 1; exact Fin.ext ha_idx]
      exact hchain_edges (b - 2) (by omega)
    · -- (k+3)→(k+4): w → arm₁ (h1: b=k+4, h2: a=k+3)
      show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
      dsimp only [φ_fun]
      simp only [h2, show (k + 3 : ℕ) ≠ 0 from by omega,
        show (k + 3 : ℕ) ≠ 1 from by omega,
        show (k + 3 : ℕ) ≤ k + 3 from by omega, dite_true,
        h1, show (k + 4 : ℕ) ≠ 0 from by omega, show (k + 4 : ℕ) ≠ 1 from by omega,
        show ¬(k + 4 ≤ k + 3) from by omega, ite_true, ite_false]
      have ha2 : k + 3 - 2 = chain.length - 1 := by omega
      rw [show chain.get ⟨k + 3 - 2, _⟩ = chain.get ⟨chain.length - 1, by omega⟩ from by
            congr 1; exact Fin.ext ha2,
          hchain_get_last]
      exact (adj_comm w arm₁).trans arm₁_adj_w
    · -- (k+3)→(k+5): w → arm₂ (h1: b=k+5, h2: a=k+3)
      show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
      dsimp only [φ_fun]
      simp only [h2, show (k + 3 : ℕ) ≠ 0 from by omega,
        show (k + 3 : ℕ) ≠ 1 from by omega,
        show (k + 3 : ℕ) ≤ k + 3 from by omega, dite_true,
        h1, show (k + 5 : ℕ) ≠ 0 from by omega, show (k + 5 : ℕ) ≠ 1 from by omega,
        show ¬(k + 5 ≤ k + 3) from by omega,
        show (k + 5 : ℕ) ≠ k + 4 from by omega, ite_true, ite_false]
      have ha2 : k + 3 - 2 = chain.length - 1 := by omega
      rw [show chain.get ⟨k + 3 - 2, _⟩ = chain.get ⟨chain.length - 1, by omega⟩ from by
            congr 1; exact Fin.ext ha2,
          hchain_get_last]
      exact (adj_comm w arm₂).trans arm₂_adj_w
  -- Apply tree_embed_adj_eq for full adjacency equality.
  have hembed : ∀ i j, dTildeAdj k i j = adj (φ i) (φ j) :=
    tree_embed_adj_eq adj (dTildeAdj k) hsymm h01 hdiag h_acyclic
      (dTildeAdj_01 k) φ hedges
      (fun i j hij hnadj => dTilde_nodup_path_between k i j hij hnadj)
  -- Transfer infinite type from D̃_{k+5} to the host graph (per-(F, Q)).
  exact subgraph_infinite_type_transfer_per_kQ φ F Q
    (dTilde_not_finite_type_per_kQ F k (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

end Etingof
