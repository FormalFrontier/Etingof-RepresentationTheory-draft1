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

end Etingof
