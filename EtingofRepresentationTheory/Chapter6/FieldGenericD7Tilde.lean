import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericStar
import EtingofRepresentationTheory.Chapter6.FieldGenericD5Tilde

/-!
# Orientation-Generic D̃₇ Construction (#2964)

F-generic, orientation-generic version of the D̃₇ extended-Dynkin
representation. This file provides `d7tildeRep_kQ`, its dimension-vector
lemma, an indecomposability stub, and the per-(F, Q) infinite-type
theorem `d7tilde_not_finite_type_per_kQ`.

D̃₇ is the affine D₇ Dynkin diagram with 8 vertices, two non-adjacent
degree-3 branch points each with two leaves, connected by a length-3
internal chain:

```
0       6
 \     /
  2-3-4-5
 /     \
1       7
```

Vertex labelling: `0, 1` are leaves of left branch `2`; `2-3-4-5` is the
internal path; `6, 7` are leaves of right branch `5`.

The canonical orientation (`d7tildeQuiver`) is the universal sink-
orientation pattern from `dTildeQuiver` (`InfiniteTypeConstructions.lean:
2049`): both leaf pairs point inward, the internal chain runs
left-to-right. For an arbitrary orientation `Q` of `d7tildeAdj`, each
of the seven edges may point either way, so the construction provides a
forward and reverse map per edge.

Indecomposability mirrors the deferred-`sorry` precedent of
`d5tildeRep_kQ_isIndecomposable` (`FieldGenericD5Tilde.lean:980`) — the
proof body is deferred to a follow-up issue; the per-(F, Q) infinite-
type theorem `d7tilde_not_finite_type_per_kQ` transitively depends on
it. The consumer of this helper is the residual all-leaves sub-case of
the non-adjacent-branches assembly (`#2960` and successors).

See `Chapter6/FieldGenericInfiniteType.lean` for the meaning of the
`_F` / `_kQ` / `_per_kQ` suffixes.
-/

open scoped Matrix

namespace Etingof

/-! ## Section 1: D̃₇ adjacency matrix -/

/-- Adjacency matrix for the extended Dynkin diagram D̃₇ on 8 vertices.
Edges: `0-2`, `1-2`, `2-3`, `3-4`, `4-5`, `5-6`, `5-7`.
Vertices `2` and `5` have degree 3; the rest have degree 1. -/
def d7tildeAdj : Matrix (Fin 8) (Fin 8) ℤ := fun i j =>
  match i.val, j.val with
  -- left leaves to left branch (vertex 2)
  | 0, 2 | 2, 0 | 1, 2 | 2, 1
  -- internal chain 2-3-4-5
  | 2, 3 | 3, 2 | 3, 4 | 4, 3 | 4, 5 | 5, 4
  -- right leaves to right branch (vertex 5)
  | 5, 6 | 6, 5 | 5, 7 | 7, 5 => 1
  | _, _ => 0

theorem d7tildeAdj_symm : d7tildeAdj.IsSymm := by
  ext i j
  simp only [d7tildeAdj, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem d7tildeAdj_diag (i : Fin 8) : d7tildeAdj i i = 0 := by
  fin_cases i <;> simp [d7tildeAdj]

theorem d7tildeAdj_01 (i j : Fin 8) : d7tildeAdj i j = 0 ∨ d7tildeAdj i j = 1 := by
  fin_cases i <;> fin_cases j <;> simp [d7tildeAdj]

/-! ## Section 2: D̃₇ canonical quiver and orientation property -/

/-- Canonical orientation for D̃₇: leaves point inward and the internal
chain runs left-to-right. Arrows:
`0→2, 1→2, 2→3, 3→4, 4→5, 6→5, 7→5`. -/
def d7tildeQuiver : Quiver (Fin 8) where
  Hom i j := PLift (
    (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 2) ∨
    (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 4) ∨
    (i.val = 4 ∧ j.val = 5) ∨
    (i.val = 6 ∧ j.val = 5) ∨ (i.val = 7 ∧ j.val = 5))

instance d7tildeQuiver_subsingleton (a b : Fin 8) :
    Subsingleton (@Quiver.Hom (Fin 8) d7tildeQuiver a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

private theorem d7tilde_arrow_implies_edge (i j : Fin 8)
    (hp : (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 2) ∨
      (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 4) ∨
      (i.val = 4 ∧ j.val = 5) ∨
      (i.val = 6 ∧ j.val = 5) ∨ (i.val = 7 ∧ j.val = 5)) :
    d7tildeAdj i j = 1 := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [d7tildeAdj, h1, h2]

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem d7tildeOrientation_isOrientationOf :
    @Etingof.IsOrientationOf 8 d7tildeQuiver d7tildeAdj := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · -- Non-edges have no arrows
    constructor; intro ⟨hp⟩
    exact hij (d7tilde_arrow_implies_edge i j hp)
  · -- Each edge has an arrow in one direction
    fin_cases i <;> fin_cases j <;> simp [d7tildeAdj] at hij <;>
      first
      | (left; exact ⟨⟨by decide⟩⟩)
      | (right; exact ⟨⟨by decide⟩⟩)
  · -- No two-way arrows (antisymmetry)
    obtain ⟨hp⟩ := hi; obtain ⟨hq⟩ := hj
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      (rcases hq with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ |
        ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
         omega)

/-! ## Section 3: D̃₇ dimension vector

Vertices `0, 1, 6, 7` are leaves with dimension `m + 1`; the path
vertices `2, 3, 4, 5` have dimension `2 * (m + 1)`. -/

/-- Dimension of vertex `v` in the D̃₇ representation with parameter `m`. -/
def d7tildeDim (m : ℕ) (v : Fin 8) : ℕ :=
  if 2 ≤ v.val ∧ v.val ≤ 5 then 2 * (m + 1) else m + 1

/-! ## Section 4: D̃₇ direction-aware match-based representation map

For an arbitrary orientation `Q` of `d7tildeAdj`, each of the seven
edges may point in either direction. The map function below provides
the canonical forward map and a reverse map per edge:

* `0-2`, `1-2`: `starEmbed1_F / starEmbed2_F` (canonical) and
  `starFirst_F / starSecond_F` (reverses).
* `2-3`: `d5tildeGamma_F` (canonical) and `d5tildeGammaInv_F` (reverse).
* `3-4`, `4-5`: `LinearMap.id` in both directions (internal-chain
  edges between equal-dimension blocks).
* `5-6`, `5-7`: `starEmbed1_F / starEmbed2_F` (canonical) and
  `starFirst_F / starSecond_F` (reverses).

Outside these 14 directed edges the map is `0` (ruled out by `hOrient`).
-/

/-- Direction-aware match-based map function for the orientation-generic
D̃₇ representation. -/
private noncomputable def d7tildeRepMap_kQ (F : Type) [Field F] (m : ℕ) (a b : Fin 8) :
    (Fin (d7tildeDim m a) → F) →ₗ[F] (Fin (d7tildeDim m b) → F) :=
  match a, b with
  -- Edge {0, 2}: canonical 0→2, reverse 2→0
  | ⟨0, _⟩, ⟨2, _⟩ => starEmbed1_F F m
  | ⟨2, _⟩, ⟨0, _⟩ => starFirst_F F m
  -- Edge {1, 2}: canonical 1→2, reverse 2→1
  | ⟨1, _⟩, ⟨2, _⟩ => starEmbed2_F F m
  | ⟨2, _⟩, ⟨1, _⟩ => starSecond_F F m
  -- Edge {2, 3}: canonical 2→3, reverse 3→2
  | ⟨2, _⟩, ⟨3, _⟩ => d5tildeGamma_F F m
  | ⟨3, _⟩, ⟨2, _⟩ => d5tildeGammaInv_F F m
  -- Edge {3, 4}: canonical 3→4, reverse 4→3 (both identities)
  | ⟨3, _⟩, ⟨4, _⟩ => LinearMap.id
  | ⟨4, _⟩, ⟨3, _⟩ => LinearMap.id
  -- Edge {4, 5}: canonical 4→5, reverse 5→4 (both identities)
  | ⟨4, _⟩, ⟨5, _⟩ => LinearMap.id
  | ⟨5, _⟩, ⟨4, _⟩ => LinearMap.id
  -- Edge {5, 6}: canonical 6→5, reverse 5→6
  | ⟨6, _⟩, ⟨5, _⟩ => starEmbed1_F F m
  | ⟨5, _⟩, ⟨6, _⟩ => starFirst_F F m
  -- Edge {5, 7}: canonical 7→5, reverse 5→7
  | ⟨7, _⟩, ⟨5, _⟩ => starEmbed2_F F m
  | ⟨5, _⟩, ⟨7, _⟩ => starSecond_F F m
  -- Non-edges (ruled out by `hOrient`); placeholder.
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic D̃₇ representation over an arbitrary field `F`
with arbitrary orientation `Q` of `d7tildeAdj`. Dimension vector follows
`d7tildeDim`: path vertices `2, 3, 4, 5` have dim `2(m+1)`; leaf
vertices `0, 1, 6, 7` have dim `m+1`.

The map on an arrow `e : Q.Hom a b` depends only on the underlying
unordered edge `{a, b}` and the direction `a → b`. Each of the seven
edges of `d7tildeAdj` contributes one canonical map and one reverse map
(see `d7tildeRepMap_kQ` for the dispatch). The orientation hypothesis
`hOrient` is not used by the construction itself; it is recorded so
that downstream lemmas (the deferred indecomposability proof) can
pattern-match on which arrows exist. -/
noncomputable def d7tildeRep_kQ
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (_hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin 8) _ Q := by
  letI := Q
  exact {
    obj := fun v => Fin (d7tildeDim m v) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => d7tildeRepMap_kQ F m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The orientation-generic D̃₇ rep has the expected dimension vector
`d7tildeDim m` at each vertex. -/
theorem d7tildeRep_kQ_dimVec
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ) (v : Fin 8) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin 8) _ Q
      (d7tildeRep_kQ F Q hOrient m) v ≃ₗ[F] (Fin (d7tildeDim m v) → F)) :=
  ⟨LinearEquiv.refl F _⟩

/-! ## Section 5: Indecomposability (deferred sorry)

The body of the indecomposability proof is deferred to follow-up
issue #2967, mirroring the precedent of
`d5tildeRep_kQ_isIndecomposable` (`FieldGenericD5Tilde.lean:980`,
tracked by #2834). The per-(F, Q) infinite-type theorem below
transitively depends on this sorry.
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic indecomposability of `d7tildeRep_kQ`.

The proof body is deferred to a follow-up issue (the D̃₇ analogue of
`d5tildeRep_kQ_isIndecomposable`, `FieldGenericD5Tilde.lean:980`,
which is itself sorry-deferred). Closing this sorry requires
F-generic versions of the leaf-subspace equalities used by the
ℂ-specific universal proof, parameterised across each of the seven
possible arrow directions; the d5tilde precedent shows this is a
multi-hundred-line construction. The consumer
`d7tilde_not_finite_type_per_kQ` carries this sorry transitively. -/
theorem d7tildeRep_kQ_isIndecomposable
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ) :
    (d7tildeRep_kQ F Q hOrient m).IsIndecomposable := by
  sorry

/-! ## Section 6: Per-(F, Q) infinite-type theorem -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) D̃₇ infinite-type theorem: for any
algebraically closed field `F` and any orientation `Q` of `d7tildeAdj`,
the set of dimension vectors of indecomposable representations is
infinite. Mirrors the proof shape of `d5tilde_not_finite_type_per_kQ`
(`FieldGenericD5Tilde.lean:999`) and `dTilde_not_finite_type`
(`InfiniteTypeConstructions.lean:3191`).

Injectivity comes from vertex `0`, where `d7tildeDim m 0 = m + 1`.

This theorem carries no direct `sorry`, but transitively depends on
`d7tildeRep_kQ_isIndecomposable`, whose proof body is deferred — see
its docstring. -/
theorem d7tilde_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj) :
    ¬ Set.Finite
      {d : Fin 8 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 8) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ, d7tildeDim m ∈
      {d : Fin 8 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 8) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨d7tildeRep_kQ F Q hOrient m,
      d7tildeRep_kQ_isIndecomposable F Q hOrient m,
      d7tildeRep_kQ_dimVec F Q hOrient m⟩
  have hinj : Function.Injective (d7tildeDim : ℕ → Fin 8 → ℕ) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨0, by omega⟩
    have hnot : ¬(2 ≤ (⟨0, by omega⟩ : Fin 8).val ∧
      (⟨0, by omega⟩ : Fin 8).val ≤ 5) := by simp
    simp only [d7tildeDim, hnot, ite_false] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

end Etingof
