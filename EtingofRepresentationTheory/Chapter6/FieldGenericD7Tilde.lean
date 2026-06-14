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

/-! ## Section 5a: Identity-chain collapse

D̃₇ differs from D̃₅ only by the internal identity chain `3 — 4 — 5`:
the edges `3-4` and `4-5` carry `LinearMap.id` in either direction
(see `d7tildeRepMap_kQ`). Consequently any complementary invariant
submodule pair `(W₁, W₂)` has `W₁⟨3⟩ = W₁⟨4⟩ = W₁⟨5⟩`. After this
collapse, the central picture at the merged `3 = 4 = 5` space is
exactly the d5tilde vertex-`3` picture (leaves `0,1` push in via
`γ ∘ embed`, leaves `6,7` push in via embeds), with leaf relabel
`4 ↦ 6, 5 ↦ 7`; this is what lets the d5tilde core/γ-containment
helpers be reused for D̃₇ (issue #4531). -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The internal identity chain `3 — 4 — 5` forces the invariant
subspaces to agree at vertices `3, 4, 5`: for any complementary
invariant submodule pair `(W₁, W₂)` of `d7tildeRep_kQ F Q hOrient m`,
`W₁⟨3⟩ = W₁⟨4⟩` and `W₁⟨4⟩ = W₁⟨5⟩`.

The two chain edges map by `LinearMap.id` in whichever direction `Q`
orients them, so invariance gives one containment between the two
endpoints; `compl_le_forces_eq` upgrades it to equality. -/
theorem d7tilde_chain_collapse
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ)
    (W₁ W₂ : ∀ v, Submodule F ((d7tildeRep_kQ F Q hOrient m).obj v))
    (hW₁_inv : ∀ {a b : Fin 8} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₁ a, (d7tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₁ b)
    (hW₂_inv : ∀ {a b : Fin 8} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₂ a, (d7tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₂ b)
    (hcompl : ∀ v, IsCompl (W₁ v) (W₂ v)) :
    W₁ ⟨3, by omega⟩ = W₁ ⟨4, by omega⟩ ∧
    W₁ ⟨4, by omega⟩ = W₁ ⟨5, by omega⟩ := by
  letI := Q
  have hOrient_edge := hOrient.2.1
  have h34 : d7tildeAdj ⟨3, by omega⟩ ⟨4, by omega⟩ = 1 := by simp [d7tildeAdj]
  have h45 : d7tildeAdj ⟨4, by omega⟩ ⟨5, by omega⟩ = 1 := by simp [d7tildeAdj]
  refine ⟨?_, ?_⟩
  · -- W₁⟨3⟩ = W₁⟨4⟩
    rcases hOrient_edge ⟨3, by omega⟩ ⟨4, by omega⟩ h34 with hQ | hQ
    · -- arrow 3 → 4 (canonical): W₁⟨3⟩ ≤ W₁⟨4⟩, W₂⟨3⟩ ≤ W₂⟨4⟩
      obtain ⟨e⟩ := hQ
      have hle1 : W₁ ⟨3, by omega⟩ ≤ W₁ ⟨4, by omega⟩ := by
        intro x hx
        have h := hW₁_inv e x hx
        simpa only [d7tildeRep_kQ, d7tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
      have hle2 : W₂ ⟨3, by omega⟩ ≤ W₂ ⟨4, by omega⟩ := by
        intro x hx
        have h := hW₂_inv e x hx
        simpa only [d7tildeRep_kQ, d7tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
      exact (compl_le_forces_eq (V := Fin (2 * (m + 1)) → F)
        (W₁ ⟨3, by omega⟩) (W₂ ⟨3, by omega⟩)
        (W₁ ⟨4, by omega⟩) (W₂ ⟨4, by omega⟩)
        (hcompl ⟨3, by omega⟩) (hcompl ⟨4, by omega⟩) hle1 hle2).1
    · -- arrow 4 → 3 (reverse): W₁⟨4⟩ ≤ W₁⟨3⟩, W₂⟨4⟩ ≤ W₂⟨3⟩
      obtain ⟨e⟩ := hQ
      have hle1 : W₁ ⟨4, by omega⟩ ≤ W₁ ⟨3, by omega⟩ := by
        intro x hx
        have h := hW₁_inv e x hx
        simpa only [d7tildeRep_kQ, d7tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
      have hle2 : W₂ ⟨4, by omega⟩ ≤ W₂ ⟨3, by omega⟩ := by
        intro x hx
        have h := hW₂_inv e x hx
        simpa only [d7tildeRep_kQ, d7tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
      exact ((compl_le_forces_eq (V := Fin (2 * (m + 1)) → F)
        (W₁ ⟨4, by omega⟩) (W₂ ⟨4, by omega⟩)
        (W₁ ⟨3, by omega⟩) (W₂ ⟨3, by omega⟩)
        (hcompl ⟨4, by omega⟩) (hcompl ⟨3, by omega⟩) hle1 hle2).1).symm
  · -- W₁⟨4⟩ = W₁⟨5⟩
    rcases hOrient_edge ⟨4, by omega⟩ ⟨5, by omega⟩ h45 with hQ | hQ
    · -- arrow 4 → 5 (canonical)
      obtain ⟨e⟩ := hQ
      have hle1 : W₁ ⟨4, by omega⟩ ≤ W₁ ⟨5, by omega⟩ := by
        intro x hx
        have h := hW₁_inv e x hx
        simpa only [d7tildeRep_kQ, d7tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
      have hle2 : W₂ ⟨4, by omega⟩ ≤ W₂ ⟨5, by omega⟩ := by
        intro x hx
        have h := hW₂_inv e x hx
        simpa only [d7tildeRep_kQ, d7tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
      exact (compl_le_forces_eq (V := Fin (2 * (m + 1)) → F)
        (W₁ ⟨4, by omega⟩) (W₂ ⟨4, by omega⟩)
        (W₁ ⟨5, by omega⟩) (W₂ ⟨5, by omega⟩)
        (hcompl ⟨4, by omega⟩) (hcompl ⟨5, by omega⟩) hle1 hle2).1
    · -- arrow 5 → 4 (reverse)
      obtain ⟨e⟩ := hQ
      have hle1 : W₁ ⟨5, by omega⟩ ≤ W₁ ⟨4, by omega⟩ := by
        intro x hx
        have h := hW₁_inv e x hx
        simpa only [d7tildeRep_kQ, d7tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
      have hle2 : W₂ ⟨5, by omega⟩ ≤ W₂ ⟨4, by omega⟩ := by
        intro x hx
        have h := hW₂_inv e x hx
        simpa only [d7tildeRep_kQ, d7tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
      exact ((compl_le_forces_eq (V := Fin (2 * (m + 1)) → F)
        (W₁ ⟨5, by omega⟩) (W₂ ⟨5, by omega⟩)
        (W₁ ⟨4, by omega⟩) (W₂ ⟨4, by omega⟩)
        (hcompl ⟨5, by omega⟩) (hcompl ⟨4, by omega⟩) hle1 hle2).1).symm

/-! ## Section 4b: Core decomposition helpers

D̃₇ analogues of the d5tilde `core_F` / `core3_F` / `gamma_containment_F`
helpers. The left branch `2` (leaves `0,1`) is identical to d5tilde's
branch `2`, so `d7tilde_core_F` is a verbatim port. The right branch is
vertex `5` (leaves `6,7`) instead of d5tilde's vertex `3` (leaves
`4,5`), so `d7tilde_core5_F` is the index-shifted port of
`d5tilde_core3_F` (`3 ↦ 5, 4 ↦ 6, 5 ↦ 7`). The γ-containment helper
threads through the two extra identity edges `3-4-5` via the collapse
equality `Wmain⟨3⟩ = Wmain⟨5⟩`. -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Core decomposition at v=2 (left branch, leaves `0,1`): if
`starEmbed1_F x + starEmbed2_F z ∈ Wmain ⟨2⟩`, then `x ∈ Wmain ⟨0⟩` and
`z ∈ Wmain ⟨1⟩`. Verbatim port of `d5tilde_core_F`. -/
theorem d7tilde_core_F
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d7tildeRep_kQ F Q hOrient m).obj v))
    (hMain_02 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hMain_12 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨1, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hOther_02 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨0, by omega⟩ →
        starEmbed1_F F m x ∈ Wother ⟨2, by omega⟩)
    (hOther_12 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨1, by omega⟩ →
        starEmbed2_F F m x ∈ Wother ⟨2, by omega⟩)
    (hc : ∀ v, IsCompl (Wmain v) (Wother v))
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ Wmain ⟨2, by omega⟩) :
    x ∈ Wmain ⟨0, by omega⟩ ∧ z ∈ Wmain ⟨1, by omega⟩ := by
  have htop0 := (hc ⟨0, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := x)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop0
  have htop1 := (hc ⟨1, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := z)
  obtain ⟨c, hcm, d, hd, hcd⟩ := Submodule.mem_sup.mp htop1
  have ha2 := hMain_02 a ha
  have hcm2 := hMain_12 c hcm
  have hb2 := hOther_02 b hb
  have hd2 := hOther_12 d hd
  have hsum : starEmbed1_F F m x + starEmbed2_F F m z =
      (starEmbed1_F F m a + starEmbed2_F F m c) +
        (starEmbed1_F F m b + starEmbed2_F F m d) := by
    rw [← hab, ← hcd]; simp [map_add]; abel
  rw [hsum] at hmem
  have hadd : starEmbed1_F F m a + starEmbed2_F F m c ∈ Wmain ⟨2, by omega⟩ :=
    (Wmain ⟨2, by omega⟩).add_mem ha2 hcm2
  have hw'_in_W : starEmbed1_F F m b + starEmbed2_F F m d ∈
      Wmain ⟨2, by omega⟩ := by
    have hsmul := (Wmain ⟨2, by omega⟩).smul_mem (-1 : F) hadd
    have hadd2 := (Wmain ⟨2, by omega⟩).add_mem hmem hsmul
    have key : starEmbed1_F F m a + starEmbed2_F F m c +
        (starEmbed1_F F m b + starEmbed2_F F m d) +
        (-1 : F) • (starEmbed1_F F m a + starEmbed2_F F m c) =
        starEmbed1_F F m b + starEmbed2_F F m d := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rwa [key] at hadd2
  have hzero : starEmbed1_F F m b + starEmbed2_F F m d = 0 := by
    have hcross := Submodule.mem_inf.mpr ⟨hw'_in_W,
      (Wother ⟨2, by omega⟩).add_mem hb2 hd2⟩
    rwa [(hc ⟨2, by omega⟩).inf_eq_bot, Submodule.mem_bot] at hcross
  obtain ⟨hb0, hd0⟩ := embed_sum_zero_F F m b d hzero
  exact ⟨hab ▸ by rw [hb0, add_zero]; exact ha,
         hcd ▸ by rw [hd0, add_zero]; exact hcm⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Core decomposition at v=5 (right branch, leaves `6,7`): if
`starEmbed1_F x + starEmbed2_F z ∈ Wmain ⟨5⟩`, then `x ∈ Wmain ⟨6⟩` and
`z ∈ Wmain ⟨7⟩`. Index-shifted port of `d5tilde_core3_F`
(`3 ↦ 5, 4 ↦ 6, 5 ↦ 7`). -/
theorem d7tilde_core5_F
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d7tildeRep_kQ F Q hOrient m).obj v))
    (hMain_65 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨6, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨5, by omega⟩)
    (hMain_75 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨7, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨5, by omega⟩)
    (hOther_65 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨6, by omega⟩ →
        starEmbed1_F F m x ∈ Wother ⟨5, by omega⟩)
    (hOther_75 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨7, by omega⟩ →
        starEmbed2_F F m x ∈ Wother ⟨5, by omega⟩)
    (hc : ∀ v, IsCompl (Wmain v) (Wother v))
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ Wmain ⟨5, by omega⟩) :
    x ∈ Wmain ⟨6, by omega⟩ ∧ z ∈ Wmain ⟨7, by omega⟩ := by
  have htop6 := (hc ⟨6, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := x)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop6
  have htop7 := (hc ⟨7, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := z)
  obtain ⟨c, hcm, d, hd, hcd⟩ := Submodule.mem_sup.mp htop7
  have ha5 := hMain_65 a ha
  have hcm5 := hMain_75 c hcm
  have hb5 := hOther_65 b hb
  have hd5 := hOther_75 d hd
  have hsum : starEmbed1_F F m x + starEmbed2_F F m z =
      (starEmbed1_F F m a + starEmbed2_F F m c) +
        (starEmbed1_F F m b + starEmbed2_F F m d) := by
    rw [← hab, ← hcd]; simp [map_add]; abel
  rw [hsum] at hmem
  have hadd : starEmbed1_F F m a + starEmbed2_F F m c ∈ Wmain ⟨5, by omega⟩ :=
    (Wmain ⟨5, by omega⟩).add_mem ha5 hcm5
  have hw'_in_W : starEmbed1_F F m b + starEmbed2_F F m d ∈
      Wmain ⟨5, by omega⟩ := by
    have hsmul := (Wmain ⟨5, by omega⟩).smul_mem (-1 : F) hadd
    have hadd2 := (Wmain ⟨5, by omega⟩).add_mem hmem hsmul
    have key : starEmbed1_F F m a + starEmbed2_F F m c +
        (starEmbed1_F F m b + starEmbed2_F F m d) +
        (-1 : F) • (starEmbed1_F F m a + starEmbed2_F F m c) =
        starEmbed1_F F m b + starEmbed2_F F m d := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rwa [key] at hadd2
  have hzero : starEmbed1_F F m b + starEmbed2_F F m d = 0 := by
    have hcross := Submodule.mem_inf.mpr ⟨hw'_in_W,
      (Wother ⟨5, by omega⟩).add_mem hb5 hd5⟩
    rwa [(hc ⟨5, by omega⟩).inf_eq_bot, Submodule.mem_bot] at hcross
  obtain ⟨hb0, hd0⟩ := embed_sum_zero_F F m b d hzero
  exact ⟨hab ▸ by rw [hb0, add_zero]; exact ha,
         hcd ▸ by rw [hd0, add_zero]; exact hcm⟩

/-! ### Reversed-edge projection siblings

For sub-cases of `d7tildeRep_kQ_leaf_equalities` where a leaf edge points
*out of* its branch vertex, the rep map is the reversed-direction pull
(`starFirst_F` for the "1-side" leaf, `starSecond_F` for the "2-side"
leaf). These siblings extract a single leaf component directly from a
`starEmbed1_F x + starEmbed2_F z` membership using the left-inverse
identities. Vertex-relabel ports of `d5tilde_core_F_proj1/2` and
`d5tilde_core3_F_proj1/2`: vertex 2 (leaves 0, 1) reuses the v=2 sibling
and vertex 5 (leaves 6, 7) is the index-shifted v=5 sibling
(`3↦5, 4↦6, 5↦7`). -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Projection sibling for the `e02 = 2→0` reversed orientation: the
reversed 0-2 pull `starFirst_F` sends `W ⟨2⟩` into `W ⟨0⟩`, so any sum
`starEmbed1_F x + starEmbed2_F z` in `W ⟨2⟩` has first component
`x ∈ W ⟨0⟩`. Port of `d5tilde_core_F_proj1`. -/
theorem d7tilde_core_F_proj1
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d7tildeRep_kQ F Q hOrient m).obj v))
    (hW_20 : ∀ (w : Fin (2 * (m + 1)) → F), w ∈ W ⟨2, by omega⟩ →
        starFirst_F F m w ∈ W ⟨0, by omega⟩)
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ W ⟨2, by omega⟩) :
    x ∈ W ⟨0, by omega⟩ := by
  have h := hW_20 _ hmem
  rw [map_add, starFirst_F_starEmbed1_F, starFirst_F_starEmbed2_F, add_zero] at h
  exact h

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Projection sibling for the `e12 = 2→1` reversed orientation: the
reversed 1-2 pull `starSecond_F` sends `W ⟨2⟩` into `W ⟨1⟩`, so any sum
`starEmbed1_F x + starEmbed2_F z` in `W ⟨2⟩` has second component
`z ∈ W ⟨1⟩`. Port of `d5tilde_core_F_proj2`. -/
theorem d7tilde_core_F_proj2
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d7tildeRep_kQ F Q hOrient m).obj v))
    (hW_21 : ∀ (w : Fin (2 * (m + 1)) → F), w ∈ W ⟨2, by omega⟩ →
        starSecond_F F m w ∈ W ⟨1, by omega⟩)
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ W ⟨2, by omega⟩) :
    z ∈ W ⟨1, by omega⟩ := by
  have h := hW_21 _ hmem
  rw [map_add, starSecond_F_starEmbed1_F, starSecond_F_starEmbed2_F, zero_add] at h
  exact h

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Projection sibling for the `e65 = 5→6` reversed orientation: the
reversed 6-5 pull `starFirst_F` sends `W ⟨5⟩` into `W ⟨6⟩`, so any sum
`starEmbed1_F x + starEmbed2_F z` in `W ⟨5⟩` has first component
`x ∈ W ⟨6⟩`. Index-shifted port of `d5tilde_core3_F_proj1`. -/
theorem d7tilde_core5_F_proj1
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d7tildeRep_kQ F Q hOrient m).obj v))
    (hW_56 : ∀ (w : Fin (2 * (m + 1)) → F), w ∈ W ⟨5, by omega⟩ →
        starFirst_F F m w ∈ W ⟨6, by omega⟩)
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ W ⟨5, by omega⟩) :
    x ∈ W ⟨6, by omega⟩ := by
  have h := hW_56 _ hmem
  rw [map_add, starFirst_F_starEmbed1_F, starFirst_F_starEmbed2_F, add_zero] at h
  exact h

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Projection sibling for the `e75 = 5→7` reversed orientation: the
reversed 7-5 pull `starSecond_F` sends `W ⟨5⟩` into `W ⟨7⟩`, so any sum
`starEmbed1_F x + starEmbed2_F z` in `W ⟨5⟩` has second component
`z ∈ W ⟨7⟩`. Index-shifted port of `d5tilde_core3_F_proj2`. -/
theorem d7tilde_core5_F_proj2
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d7tildeRep_kQ F Q hOrient m).obj v))
    (hW_57 : ∀ (w : Fin (2 * (m + 1)) → F), w ∈ W ⟨5, by omega⟩ →
        starSecond_F F m w ∈ W ⟨7, by omega⟩)
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ W ⟨5, by omega⟩) :
    z ∈ W ⟨7, by omega⟩ := by
  have h := hW_57 _ hmem
  rw [map_add, starSecond_F_starEmbed1_F, starSecond_F_starEmbed2_F, zero_add] at h
  exact h

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- γ-coupled leaf containments for D̃₇. Given canonical embed pushes on
both `Wmain` and `Wother`, the `2→3` γ-push on `Wmain`, and the
chain-collapse equality `Wmain⟨3⟩ = Wmain⟨5⟩`, derive four containments
linking source leaves `{0,1}` to target leaves `{6,7}` via
γ-then-collapse-then-core5. Port of `d5tilde_gamma_containment_F` with
the extra identity-edge collapse threaded in. -/
theorem d7tilde_gamma_containment_F
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d7tildeRep_kQ F Q hOrient m).obj v))
    (hMain_02 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hMain_12 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨1, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hMain_23 : ∀ (x : Fin (2 * (m + 1)) → F), x ∈ Wmain ⟨2, by omega⟩ →
        d5tildeGamma_F F m x ∈ Wmain ⟨3, by omega⟩)
    (hcol_main : Wmain ⟨3, by omega⟩ = Wmain ⟨5, by omega⟩)
    (hMain_65 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨6, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨5, by omega⟩)
    (hMain_75 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨7, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨5, by omega⟩)
    (hOther_65 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨6, by omega⟩ →
        starEmbed1_F F m x ∈ Wother ⟨5, by omega⟩)
    (hOther_75 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨7, by omega⟩ →
        starEmbed2_F F m x ∈ Wother ⟨5, by omega⟩)
    (hc : ∀ v, IsCompl (Wmain v) (Wother v)) :
    (∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
      x ∈ Wmain ⟨6, by omega⟩) ∧
    (∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
      x ∈ Wmain ⟨7, by omega⟩) ∧
    (∀ (y : Fin (m + 1) → F), y ∈ Wmain ⟨1, by omega⟩ →
      y ∈ Wmain ⟨6, by omega⟩) ∧
    (∀ (y : Fin (m + 1) → F), y ∈ Wmain ⟨1, by omega⟩ →
      nilpotentShiftLinGen F m y ∈ Wmain ⟨7, by omega⟩) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have he1 := hMain_02 x hx
    have hgamma := hMain_23 (starEmbed1_F F m x) he1
    rw [gamma_from_embed1_F] at hgamma
    have hgamma5 := hcol_main ▸ hgamma
    exact (d7tilde_core5_F F Q hOrient m Wmain Wother hMain_65 hMain_75
      hOther_65 hOther_75 hc x x hgamma5).1
  · have he1 := hMain_02 x hx
    have hgamma := hMain_23 (starEmbed1_F F m x) he1
    rw [gamma_from_embed1_F] at hgamma
    have hgamma5 := hcol_main ▸ hgamma
    exact (d7tilde_core5_F F Q hOrient m Wmain Wother hMain_65 hMain_75
      hOther_65 hOther_75 hc x x hgamma5).2
  · have he2 := hMain_12 y hy
    have hgamma := hMain_23 (starEmbed2_F F m y) he2
    rw [gamma_from_embed2_F] at hgamma
    have hgamma5 := hcol_main ▸ hgamma
    exact (d7tilde_core5_F F Q hOrient m Wmain Wother hMain_65 hMain_75
      hOther_65 hOther_75 hc y (nilpotentShiftLinGen F m y) hgamma5).1
  · have he2 := hMain_12 y hy
    have hgamma := hMain_23 (starEmbed2_F F m y) he2
    rw [gamma_from_embed2_F] at hgamma
    have hgamma5 := hcol_main ▸ hgamma
    exact (d7tilde_core5_F F Q hOrient m Wmain Wother hMain_65 hMain_75
      hOther_65 hOther_75 hc y (nilpotentShiftLinGen F m y) hgamma5).2

/-! ## Section 4c: Leaf equalities (#4531: canonical branch)

The leaf-equality theorem derives `W₁⟨0⟩ = W₁⟨1⟩ = W₁⟨6⟩ = W₁⟨7⟩` for any
complementary invariant pair. The internal identity chain `3-4-5` is
handled orientation-independently by `d7tilde_chain_collapse`, so the
case analysis only branches on the five leaf/γ edges (`0-2, 1-2, 2-3,
6-5, 7-5`) — the same 32-branch tree as d5tilde/d6tilde. The
all-canonical branch is proven inline by mirroring
`d5tildeRep_kQ_leaf_equalities` (and `d6tildeRep_kQ_leaf_equalities`);
the remaining 31 non-canonical branches are tracked by #4533 (sub-B). -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- For any orientation `Q` of `d7tildeAdj` and any complementary invariant
submodule pair `(W₁, W₂)` of `d7tildeRep_kQ F Q hOrient m`, the leaf
vertices `0, 1, 6, 7` carry equal `W₁`-subspaces.

**Proof body partially deferred** (#4533, sub-B). Two branches are proven
inline: the all-canonical branch (`0→2, 1→2, 2→3, 6→5, 7→5`, with the
identity chain `3-4-5` collapsed) and **combo D** (`0→2, 1→2, 2→3`
canonical, both v=5 leaf edges reversed `5→6, 5→7`), the latter via the
reversed-edge projection siblings `d7tilde_core5_F_proj1/2`. This matches
the proven state of the d5tilde / d6tilde precedents. The five remaining
coarse branches are `sorry`: the two **mixed-direction v=5** cases (one
leaf edge canonical, the other reversed — combo C / C′) are blocked on
nilpotent-shift (N) invariance infrastructure, and the three outer
reversed branches (`e02`, `e12`, `e23`) nest those same mixed v=5
sub-configurations. -/
theorem d7tildeRep_kQ_leaf_equalities
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q d7tildeAdj)
    (m : ℕ)
    (W₁ W₂ : ∀ v, Submodule F ((d7tildeRep_kQ F Q hOrient m).obj v))
    (hW₁_inv : ∀ {a b : Fin 8} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₁ a, (d7tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₁ b)
    (hW₂_inv : ∀ {a b : Fin 8} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₂ a, (d7tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₂ b)
    (hcompl : ∀ v, IsCompl (W₁ v) (W₂ v)) :
    W₁ ⟨0, by omega⟩ = W₁ ⟨1, by omega⟩ ∧
    W₁ ⟨6, by omega⟩ = W₁ ⟨7, by omega⟩ ∧
    W₁ ⟨0, by omega⟩ = W₁ ⟨6, by omega⟩ := by
  letI := Q
  -- Internal identity chain 3-4-5 collapses orientation-independently.
  obtain ⟨hcolA, hcolB⟩ :=
    d7tilde_chain_collapse F Q hOrient m W₁ W₂ hW₁_inv hW₂_inv hcompl
  have hcol₁ : W₁ ⟨3, by omega⟩ = W₁ ⟨5, by omega⟩ := hcolA.trans hcolB
  obtain ⟨hcolA', hcolB'⟩ :=
    d7tilde_chain_collapse F Q hOrient m W₂ W₁ hW₂_inv hW₁_inv
      (fun v => (hcompl v).symm)
  have hcol₂ : W₂ ⟨3, by omega⟩ = W₂ ⟨5, by omega⟩ := hcolA'.trans hcolB'
  have hOrient_edge := hOrient.2.1
  have h02 : d7tildeAdj ⟨0, by omega⟩ ⟨2, by omega⟩ = 1 := by simp [d7tildeAdj]
  have h12 : d7tildeAdj ⟨1, by omega⟩ ⟨2, by omega⟩ = 1 := by simp [d7tildeAdj]
  have h23 : d7tildeAdj ⟨2, by omega⟩ ⟨3, by omega⟩ = 1 := by simp [d7tildeAdj]
  have h65 : d7tildeAdj ⟨6, by omega⟩ ⟨5, by omega⟩ = 1 := by simp [d7tildeAdj]
  have h75 : d7tildeAdj ⟨7, by omega⟩ ⟨5, by omega⟩ = 1 := by simp [d7tildeAdj]
  rcases hOrient_edge ⟨0, by omega⟩ ⟨2, by omega⟩ h02 with hQ02 | hQ02
  · obtain ⟨a02⟩ := hQ02
    rcases hOrient_edge ⟨1, by omega⟩ ⟨2, by omega⟩ h12 with hQ12 | hQ12
    · obtain ⟨a12⟩ := hQ12
      rcases hOrient_edge ⟨2, by omega⟩ ⟨3, by omega⟩ h23 with hQ23 | hQ23
      · obtain ⟨a23⟩ := hQ23
        rcases hOrient_edge ⟨6, by omega⟩ ⟨5, by omega⟩ h65 with hQ65 | hQ65
        · obtain ⟨a65⟩ := hQ65
          rcases hOrient_edge ⟨7, by omega⟩ ⟨5, by omega⟩ h75 with hQ75 | hQ75
          · obtain ⟨a75⟩ := hQ75
            -- ALL CANONICAL (leaf/γ edges): 0→2, 1→2, 2→3, 6→5, 7→5.
            have hW₁_02 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨0, by omega⟩) :
                starEmbed1_F F m x ∈ W₁ ⟨2, by omega⟩ := by
              have h := hW₁_inv a02 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₁_12 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨1, by omega⟩) :
                starEmbed2_F F m x ∈ W₁ ⟨2, by omega⟩ := by
              have h := hW₁_inv a12 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₁_23 (x : Fin (2 * (m + 1)) → F) (hx : x ∈ W₁ ⟨2, by omega⟩) :
                d5tildeGamma_F F m x ∈ W₁ ⟨3, by omega⟩ := by
              have h := hW₁_inv a23 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₁_65 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨6, by omega⟩) :
                starEmbed1_F F m x ∈ W₁ ⟨5, by omega⟩ := by
              have h := hW₁_inv a65 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₁_75 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨7, by omega⟩) :
                starEmbed2_F F m x ∈ W₁ ⟨5, by omega⟩ := by
              have h := hW₁_inv a75 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₂_02 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨0, by omega⟩) :
                starEmbed1_F F m x ∈ W₂ ⟨2, by omega⟩ := by
              have h := hW₂_inv a02 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₂_12 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨1, by omega⟩) :
                starEmbed2_F F m x ∈ W₂ ⟨2, by omega⟩ := by
              have h := hW₂_inv a12 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₂_23 (x : Fin (2 * (m + 1)) → F) (hx : x ∈ W₂ ⟨2, by omega⟩) :
                d5tildeGamma_F F m x ∈ W₂ ⟨3, by omega⟩ := by
              have h := hW₂_inv a23 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₂_65 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨6, by omega⟩) :
                starEmbed1_F F m x ∈ W₂ ⟨5, by omega⟩ := by
              have h := hW₂_inv a65 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₂_75 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨7, by omega⟩) :
                starEmbed2_F F m x ∈ W₂ ⟨5, by omega⟩ := by
              have h := hW₂_inv a75 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            obtain ⟨h06, h07, h16, _hN17⟩ :=
              d7tilde_gamma_containment_F F Q hOrient m W₁ W₂
                hW₁_02 hW₁_12 hW₁_23 hcol₁ hW₁_65 hW₁_75 hW₂_65 hW₂_75 hcompl
            obtain ⟨h06', h07', h16', _hN17'⟩ :=
              d7tilde_gamma_containment_F F Q hOrient m W₂ W₁
                hW₂_02 hW₂_12 hW₂_23 hcol₂ hW₂_65 hW₂_75 hW₁_65 hW₁_75
                (fun v => (hcompl v).symm)
            have heq06 : W₁ ⟨0, by omega⟩ = W₁ ⟨6, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨0, by omega⟩) (W₂ ⟨0, by omega⟩)
                (W₁ ⟨6, by omega⟩) (W₂ ⟨6, by omega⟩)
                (hcompl ⟨0, by omega⟩) (hcompl ⟨6, by omega⟩) h06 h06').1
            have heq07 : W₁ ⟨0, by omega⟩ = W₁ ⟨7, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨0, by omega⟩) (W₂ ⟨0, by omega⟩)
                (W₁ ⟨7, by omega⟩) (W₂ ⟨7, by omega⟩)
                (hcompl ⟨0, by omega⟩) (hcompl ⟨7, by omega⟩) h07 h07').1
            have heq16 : W₁ ⟨1, by omega⟩ = W₁ ⟨6, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨1, by omega⟩) (W₂ ⟨1, by omega⟩)
                (W₁ ⟨6, by omega⟩) (W₂ ⟨6, by omega⟩)
                (hcompl ⟨1, by omega⟩) (hcompl ⟨6, by omega⟩) h16 h16').1
            have heq01 : W₁ ⟨0, by omega⟩ = W₁ ⟨1, by omega⟩ := heq06.trans heq16.symm
            have heq67 : W₁ ⟨6, by omega⟩ = W₁ ⟨7, by omega⟩ := heq06.symm.trans heq07
            exact ⟨heq01, heq67, heq06⟩
          · -- e75 reversed (5→7): MIXED v=5 (6-5 canonical, 7-5 reversed).
            -- Blocked on nilpotent-shift (N) invariance infrastructure — the
            -- canonical 6-push only yields an (I - N)-twisted relation through
            -- γ; same obstruction as d5tilde combo C. Tracked by #4533.
            sorry
        · obtain ⟨a56⟩ := hQ65
          rcases hOrient_edge ⟨7, by omega⟩ ⟨5, by omega⟩ h75 with hQ75 | hQ75
          · -- e65 reversed (5→6), e75 canonical (7→5): MIXED v=5.
            -- Blocked on nilpotent-shift (N) invariance infrastructure — the
            -- canonical 7-push only yields an (I - N)-twisted relation through
            -- γ; same obstruction as d5tilde combo C. Tracked by #4533.
            obtain ⟨a75⟩ := hQ75
            sorry
          · -- e65 reversed (5→6), e75 reversed (5→7): COMBO D.
            -- Tractable: the reversed pulls starFirst_F / starSecond_F extract
            -- the leaf-6/7 components directly via the proj siblings, with no
            -- mixed-direction obstruction. Mirrors d5tilde / d6tilde combo D.
            obtain ⟨a57⟩ := hQ75
            -- Canonical v=2 + central γ pushes (same as the all-canonical branch).
            have hW₁_02 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨0, by omega⟩) :
                starEmbed1_F F m x ∈ W₁ ⟨2, by omega⟩ := by
              have h := hW₁_inv a02 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₁_12 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨1, by omega⟩) :
                starEmbed2_F F m x ∈ W₁ ⟨2, by omega⟩ := by
              have h := hW₁_inv a12 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₁_23 (x : Fin (2 * (m + 1)) → F) (hx : x ∈ W₁ ⟨2, by omega⟩) :
                d5tildeGamma_F F m x ∈ W₁ ⟨3, by omega⟩ := by
              have h := hW₁_inv a23 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₂_02 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨0, by omega⟩) :
                starEmbed1_F F m x ∈ W₂ ⟨2, by omega⟩ := by
              have h := hW₂_inv a02 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₂_12 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨1, by omega⟩) :
                starEmbed2_F F m x ∈ W₂ ⟨2, by omega⟩ := by
              have h := hW₂_inv a12 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₂_23 (x : Fin (2 * (m + 1)) → F) (hx : x ∈ W₂ ⟨2, by omega⟩) :
                d5tildeGamma_F F m x ∈ W₂ ⟨3, by omega⟩ := by
              have h := hW₂_inv a23 x hx
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            -- Reversed v=5 leaf pulls (5→6 = starFirst, 5→7 = starSecond).
            have hW₁_56 (w : Fin (2 * (m + 1)) → F) (hw : w ∈ W₁ ⟨5, by omega⟩) :
                starFirst_F F m w ∈ W₁ ⟨6, by omega⟩ := by
              have h := hW₁_inv a56 w hw
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₁_57 (w : Fin (2 * (m + 1)) → F) (hw : w ∈ W₁ ⟨5, by omega⟩) :
                starSecond_F F m w ∈ W₁ ⟨7, by omega⟩ := by
              have h := hW₁_inv a57 w hw
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₂_56 (w : Fin (2 * (m + 1)) → F) (hw : w ∈ W₂ ⟨5, by omega⟩) :
                starFirst_F F m w ∈ W₂ ⟨6, by omega⟩ := by
              have h := hW₂_inv a56 w hw
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            have hW₂_57 (w : Fin (2 * (m + 1)) → F) (hw : w ∈ W₂ ⟨5, by omega⟩) :
                starSecond_F F m w ∈ W₂ ⟨7, by omega⟩ := by
              have h := hW₂_inv a57 w hw
              simp only [d7tildeRep_kQ, d7tildeRepMap_kQ] at h; exact h
            -- Leaf containments for W₁: route 0/1 → 2 →(γ) 3, collapse to 5,
            -- then pull to leaves 6/7.
            have h06 : W₁ ⟨0, by omega⟩ ≤ W₁ ⟨6, by omega⟩ := by
              intro x hx
              have hg := hW₁_23 _ (hW₁_02 x hx)
              rw [gamma_from_embed1_F] at hg
              exact d7tilde_core5_F_proj1 F Q hOrient m W₁ hW₁_56 x x (hcol₁ ▸ hg)
            have h07 : W₁ ⟨0, by omega⟩ ≤ W₁ ⟨7, by omega⟩ := by
              intro x hx
              have hg := hW₁_23 _ (hW₁_02 x hx)
              rw [gamma_from_embed1_F] at hg
              exact d7tilde_core5_F_proj2 F Q hOrient m W₁ hW₁_57 x x (hcol₁ ▸ hg)
            have h16 : W₁ ⟨1, by omega⟩ ≤ W₁ ⟨6, by omega⟩ := by
              intro y hy
              have hg := hW₁_23 _ (hW₁_12 y hy)
              rw [gamma_from_embed2_F] at hg
              exact d7tilde_core5_F_proj1 F Q hOrient m W₁ hW₁_56 y
                (nilpotentShiftLinGen F m y) (hcol₁ ▸ hg)
            -- Same containments for W₂.
            have h06' : W₂ ⟨0, by omega⟩ ≤ W₂ ⟨6, by omega⟩ := by
              intro x hx
              have hg := hW₂_23 _ (hW₂_02 x hx)
              rw [gamma_from_embed1_F] at hg
              exact d7tilde_core5_F_proj1 F Q hOrient m W₂ hW₂_56 x x (hcol₂ ▸ hg)
            have h07' : W₂ ⟨0, by omega⟩ ≤ W₂ ⟨7, by omega⟩ := by
              intro x hx
              have hg := hW₂_23 _ (hW₂_02 x hx)
              rw [gamma_from_embed1_F] at hg
              exact d7tilde_core5_F_proj2 F Q hOrient m W₂ hW₂_57 x x (hcol₂ ▸ hg)
            have h16' : W₂ ⟨1, by omega⟩ ≤ W₂ ⟨6, by omega⟩ := by
              intro y hy
              have hg := hW₂_23 _ (hW₂_12 y hy)
              rw [gamma_from_embed2_F] at hg
              exact d7tilde_core5_F_proj1 F Q hOrient m W₂ hW₂_56 y
                (nilpotentShiftLinGen F m y) (hcol₂ ▸ hg)
            -- Complementarity upgrades each containment to an equality.
            have heq06 : W₁ ⟨0, by omega⟩ = W₁ ⟨6, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨0, by omega⟩) (W₂ ⟨0, by omega⟩)
                (W₁ ⟨6, by omega⟩) (W₂ ⟨6, by omega⟩)
                (hcompl ⟨0, by omega⟩) (hcompl ⟨6, by omega⟩) h06 h06').1
            have heq07 : W₁ ⟨0, by omega⟩ = W₁ ⟨7, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨0, by omega⟩) (W₂ ⟨0, by omega⟩)
                (W₁ ⟨7, by omega⟩) (W₂ ⟨7, by omega⟩)
                (hcompl ⟨0, by omega⟩) (hcompl ⟨7, by omega⟩) h07 h07').1
            have heq16 : W₁ ⟨1, by omega⟩ = W₁ ⟨6, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨1, by omega⟩) (W₂ ⟨1, by omega⟩)
                (W₁ ⟨6, by omega⟩) (W₂ ⟨6, by omega⟩)
                (hcompl ⟨1, by omega⟩) (hcompl ⟨6, by omega⟩) h16 h16').1
            have heq01 : W₁ ⟨0, by omega⟩ = W₁ ⟨1, by omega⟩ := heq06.trans heq16.symm
            have heq67 : W₁ ⟨6, by omega⟩ = W₁ ⟨7, by omega⟩ := heq06.symm.trans heq07
            exact ⟨heq01, heq67, heq06⟩
      · -- e23 reversed (3→2): tracked by #4533 sub-B
        sorry
    · -- e12 reversed (2→1): tracked by #4533 sub-B
      sorry
  · -- e02 reversed (2→0): tracked by #4533 sub-B
    sorry

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

/-! ## Section 7: Embedding D̃₇ into a host tree (per-(F, Q) helper)

Mirrors `embed_etilde7_in_tree_per_kQ` (`FieldGenericETilde7.lean:356`)
for the D̃₇ shape: two non-adjacent degree-3 branch points (`p`, `s`)
each with two leaves (`a, b` for `p`; `u, v` for `s`), connected by an
internal length-3 chain `p – q – r – s`. Given the seven edges, the
`p – s` non-edge, and seven distinctness hypotheses, this helper
derives the remaining 21-pair adjacency lattice and dispatches via
`subgraph_infinite_type_transfer_per_kQ` and
`d7tilde_not_finite_type_per_kQ`. -/

set_option maxHeartbeats 800000 in
-- The 21-pair adjacency lattice (8 triangle + 1 input + 12 path-based
-- non-edges) drives a sizeable `linarith` over the 64 `fin_cases` of
-- `hembed`, exceeding the default 200k heartbeat limit.
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) embedding of D̃₇ into a host acyclic adjacency matrix.

Vertex map (matching `d7tildeAdj`):
`0 → a, 1 → b, 2 → p, 3 → q, 4 → r, 5 → s, 6 → u, 7 → v`. The seven
D̃₇ edges are: `a-p, b-p, p-q, q-r, r-s, s-u, s-v`; vertices `p` and
`s` are the two non-adjacent degree-3 branch points. -/
theorem embed_d7tilde_in_tree_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (a b p q r s u v : Fin n)
    (hap : adj p a = 1) (hbp : adj p b = 1) (hpq : adj p q = 1)
    (hqr : adj q r = 1) (hrs : adj r s = 1)
    (hsu : adj s u = 1) (hsv : adj s v = 1)
    (hps : adj p s = 0)
    (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (huv : u ≠ v) (hru : r ≠ u) (hrv : r ≠ v)
    (hps_ne : p ≠ s)
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have ne_of_adj' : ∀ x y, adj x y = 1 → x ≠ y := fun x y h hxy => by
    rw [hxy, hdiag] at h; exact one_ne_zero h.symm
  -- Edge-derived distinctness (Phase 1) — directions matching the edge labels.
  have hap_ne : a ≠ p := (ne_of_adj' p a hap).symm
  have hbp_ne : b ≠ p := (ne_of_adj' p b hbp).symm
  have hpq_ne : p ≠ q := ne_of_adj' p q hpq
  have hqr_ne : q ≠ r := ne_of_adj' q r hqr
  have hrs_ne : r ≠ s := ne_of_adj' r s hrs
  have hsu_ne : s ≠ u := ne_of_adj' s u hsu
  have hsv_ne : s ≠ v := ne_of_adj' s v hsv
  -- Reversed edges.
  have hap' : adj a p = 1 := (adj_comm a p).trans hap
  have hbp' : adj b p = 1 := (adj_comm b p).trans hbp
  have hpq' : adj q p = 1 := (adj_comm q p).trans hpq
  have hqr' : adj r q = 1 := (adj_comm r q).trans hqr
  have hrs' : adj s r = 1 := (adj_comm s r).trans hrs
  have hsu' : adj u s = 1 := (adj_comm u s).trans hsu
  have hsv' : adj v s = 1 := (adj_comm v s).trans hsv
  have hps' : adj s p = 0 := (adj_comm s p).trans hps
  -- Path Nodup helpers.
  have path_nodup4 : ∀ (x₁ x₂ x₃ x₄ : Fin n),
      x₁ ≠ x₂ → x₁ ≠ x₃ → x₁ ≠ x₄ → x₂ ≠ x₃ → x₂ ≠ x₄ → x₃ ≠ x₄ →
      [x₁, x₂, x₃, x₄].Nodup := by
    intro x₁ x₂ x₃ x₄ h12 h13 h14 h23 h24 h34
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩
  have path_nodup5 : ∀ (x₁ x₂ x₃ x₄ x₅ : Fin n),
      x₁ ≠ x₂ → x₁ ≠ x₃ → x₁ ≠ x₄ → x₁ ≠ x₅ →
      x₂ ≠ x₃ → x₂ ≠ x₄ → x₂ ≠ x₅ →
      x₃ ≠ x₄ → x₃ ≠ x₅ → x₄ ≠ x₅ →
      [x₁, x₂, x₃, x₄, x₅].Nodup := by
    intro x₁ x₂ x₃ x₄ x₅ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45⟩
  have path_nodup6 : ∀ (x₁ x₂ x₃ x₄ x₅ x₆ : Fin n),
      x₁ ≠ x₂ → x₁ ≠ x₃ → x₁ ≠ x₄ → x₁ ≠ x₅ → x₁ ≠ x₆ →
      x₂ ≠ x₃ → x₂ ≠ x₄ → x₂ ≠ x₅ → x₂ ≠ x₆ →
      x₃ ≠ x₄ → x₃ ≠ x₅ → x₃ ≠ x₆ →
      x₄ ≠ x₅ → x₄ ≠ x₆ → x₅ ≠ x₆ →
      [x₁, x₂, x₃, x₄, x₅, x₆].Nodup := by
    intro x₁ x₂ x₃ x₄ x₅ x₆ h12 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨h12, h13, h14, h15, h16⟩, ⟨h23, h24, h25, h26⟩,
      ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56⟩
  have path_edges4 : ∀ (x₁ x₂ x₃ x₄ : Fin n),
      adj x₁ x₂ = 1 → adj x₂ x₃ = 1 → adj x₃ x₄ = 1 →
      ∀ k, (hk : k + 1 < [x₁, x₂, x₃, x₄].length) →
        adj ([x₁, x₂, x₃, x₄].get ⟨k, by omega⟩)
          ([x₁, x₂, x₃, x₄].get ⟨k + 1, hk⟩) = 1 := by
    intro x₁ x₂ x₃ x₄ e12 e23 e34 k hk
    have : k + 1 < 4 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> assumption
  have path_edges5 : ∀ (x₁ x₂ x₃ x₄ x₅ : Fin n),
      adj x₁ x₂ = 1 → adj x₂ x₃ = 1 → adj x₃ x₄ = 1 → adj x₄ x₅ = 1 →
      ∀ k, (hk : k + 1 < [x₁, x₂, x₃, x₄, x₅].length) →
        adj ([x₁, x₂, x₃, x₄, x₅].get ⟨k, by omega⟩)
          ([x₁, x₂, x₃, x₄, x₅].get ⟨k + 1, hk⟩) = 1 := by
    intro x₁ x₂ x₃ x₄ x₅ e12 e23 e34 e45 k hk
    have : k + 1 < 5 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> assumption
  have path_edges6 : ∀ (x₁ x₂ x₃ x₄ x₅ x₆ : Fin n),
      adj x₁ x₂ = 1 → adj x₂ x₃ = 1 → adj x₃ x₄ = 1 →
      adj x₄ x₅ = 1 → adj x₅ x₆ = 1 →
      ∀ k, (hk : k + 1 < [x₁, x₂, x₃, x₄, x₅, x₆].length) →
        adj ([x₁, x₂, x₃, x₄, x₅, x₆].get ⟨k, by omega⟩)
          ([x₁, x₂, x₃, x₄, x₅, x₆].get ⟨k + 1, hk⟩) = 1 := by
    intro x₁ x₂ x₃ x₄ x₅ x₆ e12 e23 e34 e45 e56 k hk
    have : k + 1 < 6 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> assumption
  -- Triangle non-edges via `acyclic_no_triangle` (8 distance-2 non-edges).
  have hab0 : adj a b = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p a b hab hap_ne hbp_ne hap hbp
  have haq0 : adj a q = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p a q haq hap_ne hpq_ne.symm hap hpq
  have hbq0 : adj b q = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p b q hbq hbp_ne hpq_ne.symm hbp hpq
  have huv0 : adj u v = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic s u v huv hsu_ne.symm hsv_ne.symm hsu hsv
  have hru0 : adj r u = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic s r u hru hrs_ne hsu_ne.symm hrs' hsu
  have hrv0 : adj r v = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic s r v hrv hrs_ne hsv_ne.symm hrs' hsv
  -- Apex q: p-r (need p ≠ r derived from hrs + hps).
  have hpr_ne : p ≠ r := by
    intro h; rw [← h] at hrs; exact absurd hrs (hps ▸ zero_ne_one)
  have hpr0 : adj p r = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q p r hpr_ne hpq_ne hqr_ne.symm hpq' hqr
  -- Apex r: q-s (need q ≠ s derived from hpq + hps).
  have hqs_ne : q ≠ s := by
    intro h; rw [h] at hpq; exact absurd hpq (hps ▸ zero_ne_one)
  have hqs0 : adj q s = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic r q s hqs_ne hqr_ne hrs_ne.symm hqr' hrs
  -- Cross-side distinctness derived from distance-2 non-edges.
  have har_ne : a ≠ r := by intro h; rw [h] at hap; linarith [hpr0]
  have has_ne : a ≠ s := by intro h; rw [h] at hap; linarith [hps]
  have hbr_ne : b ≠ r := by intro h; rw [h] at hbp; linarith [hpr0]
  have hbs_ne : b ≠ s := by intro h; rw [h] at hbp; linarith [hps]
  have hpu_ne : p ≠ u := by intro h; rw [h] at hps; linarith [hsu']
  have hpv_ne : p ≠ v := by intro h; rw [h] at hps; linarith [hsv']
  have hqu_ne : q ≠ u := by intro h; rw [h] at hqs0; linarith [hsu']
  have hqv_ne : q ≠ v := by intro h; rw [h] at hqs0; linarith [hsv']
  -- Distance-3 non-edges (4-vertex paths).
  have har0 : adj a r = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [a, p, q, r] (by simp)
      (path_nodup4 _ _ _ _ hap_ne haq har_ne hpq_ne hpr_ne hqr_ne)
      (path_edges4 _ _ _ _ hap' hpq hqr)
    simpa using h
  have hbr0 : adj b r = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [b, p, q, r] (by simp)
      (path_nodup4 _ _ _ _ hbp_ne hbq hbr_ne hpq_ne hpr_ne hqr_ne)
      (path_edges4 _ _ _ _ hbp' hpq hqr)
    simpa using h
  have hqu0 : adj q u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [q, r, s, u] (by simp)
      (path_nodup4 _ _ _ _ hqr_ne hqs_ne hqu_ne hrs_ne hru hsu_ne)
      (path_edges4 _ _ _ _ hqr hrs hsu)
    simpa using h
  have hqv0 : adj q v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [q, r, s, v] (by simp)
      (path_nodup4 _ _ _ _ hqr_ne hqs_ne hqv_ne hrs_ne hrv hsv_ne)
      (path_edges4 _ _ _ _ hqr hrs hsv)
    simpa using h
  -- Distance-4 non-edges (5-vertex paths).
  have has0 : adj a s = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [a, p, q, r, s] (by simp)
      (path_nodup5 _ _ _ _ _ hap_ne haq har_ne has_ne
        hpq_ne hpr_ne hps_ne hqr_ne hqs_ne hrs_ne)
      (path_edges5 _ _ _ _ _ hap' hpq hqr hrs)
    simpa using h
  have hbs0 : adj b s = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [b, p, q, r, s] (by simp)
      (path_nodup5 _ _ _ _ _ hbp_ne hbq hbr_ne hbs_ne
        hpq_ne hpr_ne hps_ne hqr_ne hqs_ne hrs_ne)
      (path_edges5 _ _ _ _ _ hbp' hpq hqr hrs)
    simpa using h
  have hpu0 : adj p u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [p, q, r, s, u] (by simp)
      (path_nodup5 _ _ _ _ _ hpq_ne hpr_ne hps_ne hpu_ne
        hqr_ne hqs_ne hqu_ne hrs_ne hru hsu_ne)
      (path_edges5 _ _ _ _ _ hpq hqr hrs hsu)
    simpa using h
  have hpv0 : adj p v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [p, q, r, s, v] (by simp)
      (path_nodup5 _ _ _ _ _ hpq_ne hpr_ne hps_ne hpv_ne
        hqr_ne hqs_ne hqv_ne hrs_ne hrv hsv_ne)
      (path_edges5 _ _ _ _ _ hpq hqr hrs hsv)
    simpa using h
  -- Cross-leaf distinctness (level 3, from distance-4 non-edges).
  have hau_ne : a ≠ u := by intro h; rw [h] at hap; linarith [hpu0]
  have hav_ne : a ≠ v := by intro h; rw [h] at hap; linarith [hpv0]
  have hbu_ne : b ≠ u := by intro h; rw [h] at hbp; linarith [hpu0]
  have hbv_ne : b ≠ v := by intro h; rw [h] at hbp; linarith [hpv0]
  -- Distance-5 non-edges (6-vertex paths).
  have hau0 : adj a u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [a, p, q, r, s, u] (by simp)
      (path_nodup6 _ _ _ _ _ _ hap_ne haq har_ne has_ne hau_ne
        hpq_ne hpr_ne hps_ne hpu_ne hqr_ne hqs_ne hqu_ne hrs_ne hru hsu_ne)
      (path_edges6 _ _ _ _ _ _ hap' hpq hqr hrs hsu)
    simpa using h
  have hav0 : adj a v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [a, p, q, r, s, v] (by simp)
      (path_nodup6 _ _ _ _ _ _ hap_ne haq har_ne has_ne hav_ne
        hpq_ne hpr_ne hps_ne hpv_ne hqr_ne hqs_ne hqv_ne hrs_ne hrv hsv_ne)
      (path_edges6 _ _ _ _ _ _ hap' hpq hqr hrs hsv)
    simpa using h
  have hbu0 : adj b u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [b, p, q, r, s, u] (by simp)
      (path_nodup6 _ _ _ _ _ _ hbp_ne hbq hbr_ne hbs_ne hbu_ne
        hpq_ne hpr_ne hps_ne hpu_ne hqr_ne hqs_ne hqu_ne hrs_ne hru hsu_ne)
      (path_edges6 _ _ _ _ _ _ hbp' hpq hqr hrs hsu)
    simpa using h
  have hbv0 : adj b v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [b, p, q, r, s, v] (by simp)
      (path_nodup6 _ _ _ _ _ _ hbp_ne hbq hbr_ne hbs_ne hbv_ne
        hpq_ne hpr_ne hps_ne hpv_ne hqr_ne hqs_ne hqv_ne hrs_ne hrv hsv_ne)
      (path_edges6 _ _ _ _ _ _ hbp' hpq hqr hrs hsv)
    simpa using h
  -- Construct φ : Fin 8 ↪ Fin n.
  let φ_fun : Fin 8 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => a  | ⟨1, _⟩ => b  | ⟨2, _⟩ => p  | ⟨3, _⟩ => q
    | ⟨4, _⟩ => r  | ⟨5, _⟩ => s  | ⟨6, _⟩ => u  | ⟨7, _⟩ => v
  have φ_inj : Function.Injective φ_fun := by
    intro i j hij; simp only [φ_fun] at hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exact absurd hij ‹_›)
      | (exact absurd hij.symm ‹_›)
  let φ : Fin 8 ↪ Fin n := ⟨φ_fun, φ_inj⟩
  have hembed : ∀ i j, d7tildeAdj i j = adj (φ i) (φ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [d7tildeAdj, φ, φ_fun] <;> norm_num <;>
      linarith [hdiag a, hdiag b, hdiag p, hdiag q, hdiag r, hdiag s, hdiag u, hdiag v,
        hap, hbp, hpq, hqr, hrs, hsu, hsv,
        hap', hbp', hpq', hqr', hrs', hsu', hsv',
        hps, hps',
        hab0, haq0, hbq0, huv0, hru0, hrv0, hpr0, hqs0,
        adj_comm a b, adj_comm a q, adj_comm b q, adj_comm u v,
        adj_comm r u, adj_comm r v, adj_comm p r, adj_comm q s,
        har0, hbr0, hqu0, hqv0,
        adj_comm a r, adj_comm b r, adj_comm q u, adj_comm q v,
        has0, hbs0, hpu0, hpv0,
        adj_comm a s, adj_comm b s, adj_comm p u, adj_comm p v,
        hau0, hav0, hbu0, hbv0,
        adj_comm a u, adj_comm a v, adj_comm b u, adj_comm b v]
  exact subgraph_infinite_type_transfer_per_kQ φ F Q
    (d7tilde_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

end Etingof
