import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericStar
import EtingofRepresentationTheory.Chapter6.FieldGenericD5Tilde

/-!
# Orientation-Generic D̃₈ Construction (#2977)

F-generic, orientation-generic version of the D̃₈ extended-Dynkin
representation. This file provides `d8tildeRep_kQ`, its dimension-vector
lemma, an indecomposability stub, and the per-(F, Q) infinite-type
theorem `d8tilde_not_finite_type_per_kQ`.

D̃₈ is the affine D₈ Dynkin diagram with 9 vertices, two non-adjacent
degree-3 branch points each with two leaves, connected by a length-4
internal chain:

```
0           7
 \         /
  2-3-4-5-6
 /         \
1           8
```

Vertex labelling: `0, 1` are leaves of left branch `2`; `2-3-4-5-6` is
the internal path; `7, 8` are leaves of right branch `6`.

The canonical orientation (`d8tildeQuiver`) is the universal sink-
orientation pattern from `dTildeQuiver` (`InfiniteTypeConstructions.lean:
2049`): both leaf pairs point inward, the internal chain runs
left-to-right. For an arbitrary orientation `Q` of `d8tildeAdj`, each of
the eight edges may point either way, so the construction provides a
forward and reverse map per edge.

This is the `chain.length = 5` analogue of `FieldGenericD7Tilde.lean`
(`chain.length = 4`) and `FieldGenericD6Tilde.lean` (`chain.length = 3`):
one extra internal chain vertex carrying an identity edge.

The central edge `2-3` carries the corrected eigenvalue-site tube
`d5tildeGammaTube_F` (#4597 / `progress/dtilde-tube-redesign-design.md`),
replacing the refuted rank-deficient bridge `d5tildeGamma_F`. With this
correction `d8tildeRep_kQ_isIndecomposable` becomes true for every
orientation; its proof body is deferred to a sub-C follow-up that
generalises the D̃₅ assembly to the length-4 chain. The per-(F, Q)
infinite-type theorem `d8tilde_not_finite_type_per_kQ` transitively
depends on that sorry. The consumer of this helper is the
`chain.length = 5` residual sub-case of the non-adjacent-branches
assembly (`FieldGenericNonAdjacentBranches.lean`).

See `Chapter6/FieldGenericInfiniteType.lean` for the meaning of the
`_F` / `_kQ` / `_per_kQ` suffixes.
-/

open scoped Matrix

namespace Etingof

/-! ## Section 1: D̃₈ adjacency matrix -/

/-- Adjacency matrix for the extended Dynkin diagram D̃₈ on 9 vertices.
Edges: `0-2`, `1-2`, `2-3`, `3-4`, `4-5`, `5-6`, `6-7`, `6-8`.
Vertices `2` and `6` have degree 3; the rest have degree 1. -/
def d8tildeAdj : Matrix (Fin 9) (Fin 9) ℤ := fun i j =>
  match i.val, j.val with
  -- left leaves to left branch (vertex 2)
  | 0, 2 | 2, 0 | 1, 2 | 2, 1
  -- internal chain 2-3-4-5-6
  | 2, 3 | 3, 2 | 3, 4 | 4, 3 | 4, 5 | 5, 4 | 5, 6 | 6, 5
  -- right leaves to right branch (vertex 6)
  | 6, 7 | 7, 6 | 6, 8 | 8, 6 => 1
  | _, _ => 0

theorem d8tildeAdj_symm : d8tildeAdj.IsSymm := by
  ext i j
  simp only [d8tildeAdj, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem d8tildeAdj_diag (i : Fin 9) : d8tildeAdj i i = 0 := by
  fin_cases i <;> simp [d8tildeAdj]

theorem d8tildeAdj_01 (i j : Fin 9) : d8tildeAdj i j = 0 ∨ d8tildeAdj i j = 1 := by
  fin_cases i <;> fin_cases j <;> simp [d8tildeAdj]

/-! ## Section 2: D̃₈ canonical quiver and orientation property -/

/-- Canonical orientation for D̃₈: leaves point inward and the internal
chain runs left-to-right. Arrows:
`0→2, 1→2, 2→3, 3→4, 4→5, 5→6, 7→6, 8→6`. -/
def d8tildeQuiver : Quiver (Fin 9) where
  Hom i j := PLift (
    (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 2) ∨
    (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 4) ∨
    (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 6) ∨
    (i.val = 7 ∧ j.val = 6) ∨ (i.val = 8 ∧ j.val = 6))

instance d8tildeQuiver_subsingleton (a b : Fin 9) :
    Subsingleton (@Quiver.Hom (Fin 9) d8tildeQuiver a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

private theorem d8tilde_arrow_implies_edge (i j : Fin 9)
    (hp : (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 2) ∨
      (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 4) ∨
      (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 6) ∨
      (i.val = 7 ∧ j.val = 6) ∨ (i.val = 8 ∧ j.val = 6)) :
    d8tildeAdj i j = 1 := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [d8tildeAdj, h1, h2]

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem d8tildeOrientation_isOrientationOf :
    @Etingof.IsOrientationOf 9 d8tildeQuiver d8tildeAdj := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · -- Non-edges have no arrows
    constructor; intro ⟨hp⟩
    exact hij (d8tilde_arrow_implies_edge i j hp)
  · -- Each edge has an arrow in one direction
    fin_cases i <;> fin_cases j <;> simp [d8tildeAdj] at hij <;>
      first
      | (left; exact ⟨⟨by decide⟩⟩)
      | (right; exact ⟨⟨by decide⟩⟩)
  · -- No two-way arrows (antisymmetry)
    obtain ⟨hp⟩ := hi; obtain ⟨hq⟩ := hj
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      (rcases hq with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ |
        ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
         omega)

/-! ## Section 3: D̃₈ dimension vector

Vertices `0, 1, 7, 8` are leaves with dimension `m + 1`; the path
vertices `2, 3, 4, 5, 6` have dimension `2 * (m + 1)`. -/

/-- Dimension of vertex `v` in the D̃₈ representation with parameter `m`. -/
def d8tildeDim (m : ℕ) (v : Fin 9) : ℕ :=
  if 2 ≤ v.val ∧ v.val ≤ 6 then 2 * (m + 1) else m + 1

/-! ## Section 4: D̃₈ direction-aware match-based representation map

For an arbitrary orientation `Q` of `d8tildeAdj`, each of the eight
edges may point in either direction. The map function below provides
the canonical forward map and a reverse map per edge:

* `0-2`, `1-2`: `starEmbed1_F / starEmbed2_F` (canonical) and
  `starFirst_F / starSecond_F` (reverses).
* `2-3`: the corrected eigenvalue-site tube `d5tildeGammaTube_F F lam`
  (canonical) and its closed-form inverse `d5tildeGammaTubeInv_F F lam`
  (reverse). This replaces the refuted rank-deficient bridge
  `d5tildeGamma_F` / `d5tildeGammaInv_F` (#4597 /
  `progress/dtilde-tube-redesign-design.md`); `lam` is the generic
  eigenvalue `d5tildeTubeLam F`, shared with the D̃₅ central edge.
* `3-4`, `4-5`, `5-6`: `LinearMap.id` in both directions (internal-chain
  edges between equal-dimension blocks).
* `6-7`, `6-8`: `starEmbed1_F / starEmbed2_F` (canonical) and
  `starFirst_F / starSecond_F` (reverses).

Outside these 16 directed edges the map is `0` (ruled out by `hOrient`).
-/

/-- Direction-aware match-based map function for the orientation-generic
D̃₈ representation. -/
private noncomputable def d8tildeRepMap_kQ (F : Type) [Field F] (lam : F) (m : ℕ)
    (a b : Fin 9) :
    (Fin (d8tildeDim m a) → F) →ₗ[F] (Fin (d8tildeDim m b) → F) :=
  match a, b with
  -- Edge {0, 2}: canonical 0→2, reverse 2→0
  | ⟨0, _⟩, ⟨2, _⟩ => starEmbed1_F F m
  | ⟨2, _⟩, ⟨0, _⟩ => starFirst_F F m
  -- Edge {1, 2}: canonical 1→2, reverse 2→1
  | ⟨1, _⟩, ⟨2, _⟩ => starEmbed2_F F m
  | ⟨2, _⟩, ⟨1, _⟩ => starSecond_F F m
  -- Edge {2, 3}: canonical 2→3, reverse 3→2 (corrected eigenvalue-site tube)
  | ⟨2, _⟩, ⟨3, _⟩ => d5tildeGammaTube_F F lam m
  | ⟨3, _⟩, ⟨2, _⟩ => d5tildeGammaTubeInv_F F lam m
  -- Edge {3, 4}: canonical 3→4, reverse 4→3 (both identities)
  | ⟨3, _⟩, ⟨4, _⟩ => LinearMap.id
  | ⟨4, _⟩, ⟨3, _⟩ => LinearMap.id
  -- Edge {4, 5}: canonical 4→5, reverse 5→4 (both identities)
  | ⟨4, _⟩, ⟨5, _⟩ => LinearMap.id
  | ⟨5, _⟩, ⟨4, _⟩ => LinearMap.id
  -- Edge {5, 6}: canonical 5→6, reverse 6→5 (both identities)
  | ⟨5, _⟩, ⟨6, _⟩ => LinearMap.id
  | ⟨6, _⟩, ⟨5, _⟩ => LinearMap.id
  -- Edge {6, 7}: canonical 7→6, reverse 6→7
  | ⟨7, _⟩, ⟨6, _⟩ => starEmbed1_F F m
  | ⟨6, _⟩, ⟨7, _⟩ => starFirst_F F m
  -- Edge {6, 8}: canonical 8→6, reverse 6→8
  | ⟨8, _⟩, ⟨6, _⟩ => starEmbed2_F F m
  | ⟨6, _⟩, ⟨8, _⟩ => starSecond_F F m
  -- Non-edges (ruled out by `hOrient`); placeholder.
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic D̃₈ representation over an arbitrary field `F`
with arbitrary orientation `Q` of `d8tildeAdj`. Dimension vector follows
`d8tildeDim`: path vertices `2, 3, 4, 5, 6` have dim `2(m+1)`; leaf
vertices `0, 1, 7, 8` have dim `m+1`.

The map on an arrow `e : Q.Hom a b` depends only on the underlying
unordered edge `{a, b}` and the direction `a → b`. Each of the eight
edges of `d8tildeAdj` contributes one canonical map and one reverse map
(see `d8tildeRepMap_kQ` for the dispatch). The orientation hypothesis
`hOrient` is not used by the construction itself; it is recorded so
that downstream lemmas (the deferred indecomposability proof) can
pattern-match on which arrows exist. -/
noncomputable def d8tildeRep_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (_hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj)
    (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin 9) _ Q := by
  letI := Q
  exact {
    obj := fun v => Fin (d8tildeDim m v) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => d8tildeRepMap_kQ F (d5tildeTubeLam F) m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The orientation-generic D̃₈ rep has the expected dimension vector
`d8tildeDim m` at each vertex. -/
theorem d8tildeRep_kQ_dimVec
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj)
    (m : ℕ) (v : Fin 9) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin 9) _ Q
      (d8tildeRep_kQ F Q hOrient m) v ≃ₗ[F] (Fin (d8tildeDim m v) → F)) :=
  ⟨LinearEquiv.refl F _⟩

/-! ## Section 5a: Foundational center-decomposition lemmas

The D̃₈ indecomposability proof (Section 5) decomposes any complementary
invariant submodule pair through the two degree-3 branch points: vertex
`2` (leaves `0, 1`) and vertex `6` (leaves `7, 8`). Both centers carry
the same star structure as the D̃₅ center (`starEmbed1_F` for the first
leaf, `starEmbed2_F` for the second, `starFirst_F / starSecond_F` for the
reverse pulls), so the core-decomposition lemmas port verbatim from
`d5tilde_core_F` / `d5tilde_core_F_proj{1,2}` (`FieldGenericD5Tilde.lean`)
with the vertex labels relabelled. These are the shape-specific
foundation reused by every orientation branch of the assembly; the
γ-coupled containment along the internal chain `2-3-4-5-6` is genuinely
new D̃₈ work and is tracked by the follow-up sub-issue. -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Core decomposition at the first branch point `v = 2` for any
complementary invariant submodule pair `(Wmain, Wother)`: if
`starEmbed1_F x + starEmbed2_F z ∈ Wmain ⟨2⟩`, then `x ∈ Wmain ⟨0⟩` and
`z ∈ Wmain ⟨1⟩`. Uses canonical `0→2` and `1→2` pushes on both `Wmain`
and `Wother`. Verbatim analogue of `d5tilde_core_F`. -/
theorem d8tilde_core_F
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d8tildeRep_kQ F Q hOrient m).obj v))
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
/-- Core decomposition at the second branch point `v = 6` for any
complementary invariant submodule pair `(Wmain, Wother)`: if
`starEmbed1_F x + starEmbed2_F z ∈ Wmain ⟨6⟩`, then `x ∈ Wmain ⟨7⟩` and
`z ∈ Wmain ⟨8⟩`. Uses canonical `7→6` and `8→6` pushes on both `Wmain`
and `Wother`. Relabelled analogue of `d5tilde_core3_F`. -/
theorem d8tilde_core6_F
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d8tildeRep_kQ F Q hOrient m).obj v))
    (hMain_76 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨7, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨6, by omega⟩)
    (hMain_86 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨8, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨6, by omega⟩)
    (hOther_76 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨7, by omega⟩ →
        starEmbed1_F F m x ∈ Wother ⟨6, by omega⟩)
    (hOther_86 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨8, by omega⟩ →
        starEmbed2_F F m x ∈ Wother ⟨6, by omega⟩)
    (hc : ∀ v, IsCompl (Wmain v) (Wother v))
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ Wmain ⟨6, by omega⟩) :
    x ∈ Wmain ⟨7, by omega⟩ ∧ z ∈ Wmain ⟨8, by omega⟩ := by
  have htop7 := (hc ⟨7, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := x)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop7
  have htop8 := (hc ⟨8, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := z)
  obtain ⟨c, hcm, d, hd, hcd⟩ := Submodule.mem_sup.mp htop8
  have ha6 := hMain_76 a ha
  have hcm6 := hMain_86 c hcm
  have hb6 := hOther_76 b hb
  have hd6 := hOther_86 d hd
  have hsum : starEmbed1_F F m x + starEmbed2_F F m z =
      (starEmbed1_F F m a + starEmbed2_F F m c) +
        (starEmbed1_F F m b + starEmbed2_F F m d) := by
    rw [← hab, ← hcd]; simp [map_add]; abel
  rw [hsum] at hmem
  have hadd : starEmbed1_F F m a + starEmbed2_F F m c ∈ Wmain ⟨6, by omega⟩ :=
    (Wmain ⟨6, by omega⟩).add_mem ha6 hcm6
  have hw'_in_W : starEmbed1_F F m b + starEmbed2_F F m d ∈
      Wmain ⟨6, by omega⟩ := by
    have hsmul := (Wmain ⟨6, by omega⟩).smul_mem (-1 : F) hadd
    have hadd2 := (Wmain ⟨6, by omega⟩).add_mem hmem hsmul
    have key : starEmbed1_F F m a + starEmbed2_F F m c +
        (starEmbed1_F F m b + starEmbed2_F F m d) +
        (-1 : F) • (starEmbed1_F F m a + starEmbed2_F F m c) =
        starEmbed1_F F m b + starEmbed2_F F m d := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rwa [key] at hadd2
  have hzero : starEmbed1_F F m b + starEmbed2_F F m d = 0 := by
    have hcross := Submodule.mem_inf.mpr ⟨hw'_in_W,
      (Wother ⟨6, by omega⟩).add_mem hb6 hd6⟩
    rwa [(hc ⟨6, by omega⟩).inf_eq_bot, Submodule.mem_bot] at hcross
  obtain ⟨hb0, hd0⟩ := embed_sum_zero_F F m b d hzero
  exact ⟨hab ▸ by rw [hb0, add_zero]; exact ha,
         hcd ▸ by rw [hd0, add_zero]; exact hcm⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Projection-based sibling for the first half of `d8tilde_core_F` at
the reversed `2→0` orientation: if the reversed `0-2` pull `starFirst_F`
sends `W ⟨2⟩` into `W ⟨0⟩`, then any `starEmbed1_F x + starEmbed2_F z` in
`W ⟨2⟩` has first component `x ∈ W ⟨0⟩`. Analogue of
`d5tilde_core_F_proj1`. -/
theorem d8tilde_core_F_proj1
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d8tildeRep_kQ F Q hOrient m).obj v))
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
/-- Projection-based sibling for the second half of `d8tilde_core_F` at
the reversed `2→1` orientation: if the reversed `1-2` pull `starSecond_F`
sends `W ⟨2⟩` into `W ⟨1⟩`, then any `starEmbed1_F x + starEmbed2_F z` in
`W ⟨2⟩` has second component `z ∈ W ⟨1⟩`. Analogue of
`d5tilde_core_F_proj2`. -/
theorem d8tilde_core_F_proj2
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d8tildeRep_kQ F Q hOrient m).obj v))
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
/-- Projection-based sibling for the first half of `d8tilde_core6_F` at
the reversed `6→7` orientation: if the reversed `7-6` pull `starFirst_F`
sends `W ⟨6⟩` into `W ⟨7⟩`, then any `starEmbed1_F x + starEmbed2_F z` in
`W ⟨6⟩` has first component `x ∈ W ⟨7⟩`. Analogue of
`d5tilde_core3_F_proj1`. -/
theorem d8tilde_core6_F_proj1
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d8tildeRep_kQ F Q hOrient m).obj v))
    (hW_67 : ∀ (w : Fin (2 * (m + 1)) → F), w ∈ W ⟨6, by omega⟩ →
        starFirst_F F m w ∈ W ⟨7, by omega⟩)
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ W ⟨6, by omega⟩) :
    x ∈ W ⟨7, by omega⟩ := by
  have h := hW_67 _ hmem
  rw [map_add, starFirst_F_starEmbed1_F, starFirst_F_starEmbed2_F, add_zero] at h
  exact h

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Projection-based sibling for the second half of `d8tilde_core6_F` at
the reversed `6→8` orientation: if the reversed `8-6` pull `starSecond_F`
sends `W ⟨6⟩` into `W ⟨8⟩`, then any `starEmbed1_F x + starEmbed2_F z` in
`W ⟨6⟩` has second component `z ∈ W ⟨8⟩`. Analogue of
`d5tilde_core3_F_proj2`. -/
theorem d8tilde_core6_F_proj2
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d8tildeRep_kQ F Q hOrient m).obj v))
    (hW_68 : ∀ (w : Fin (2 * (m + 1)) → F), w ∈ W ⟨6, by omega⟩ →
        starSecond_F F m w ∈ W ⟨8, by omega⟩)
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ W ⟨6, by omega⟩) :
    z ∈ W ⟨8, by omega⟩ := by
  have h := hW_68 _ hmem
  rw [map_add, starSecond_F_starEmbed1_F, starSecond_F_starEmbed2_F, zero_add] at h
  exact h

/-! ## Section 5b: Internal-chain collapse and γ-coupled containment
(#4546 deliverable 1)

D̃₈ couples its two degree-3 branch points (vertices `2` and `6`) across
the internal length-4 chain `2 – 3 – 4 – 5 – 6`. The edge `2-3` carries
the γ-coupling `d5tildeGamma_F`; the three edges `3-4`, `4-5`, `5-6`
carry `LinearMap.id` in both orientations. For any complementary
invariant pair, each identity edge forces equality of the two vertex
subspaces (the D̃₆ single-edge `d6tildeRep_kQ_chain_collapse` argument,
applied three times), so the whole interior collapses:
`W ⟨3⟩ = W ⟨4⟩ = W ⟨5⟩ = W ⟨6⟩`. This lets γ-data pushed in at vertex `3`
transport to the right center `6`, where `d8tilde_core6_F` decomposes it
onto the leaves `7, 8`. This is the genuinely D̃₈-specific propagation
that does not port directly from D̃₅ (single γ edge) or D̃₆ (single
identity edge). -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Internal-chain collapse for D̃₈: the three identity edges `3-4`,
`4-5`, `5-6` force any complementary invariant pair to carry equal
subspaces across the whole interior, so `W₁ ⟨3⟩ = W₁ ⟨6⟩` and
`W₂ ⟨3⟩ = W₂ ⟨6⟩`. Generalises `d6tildeRep_kQ_chain_collapse` (single
edge `3-4`) to the three-edge chain. -/
theorem d8tildeRep_kQ_chain_collapse
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj)
    (m : ℕ)
    (W₁ W₂ : ∀ v, Submodule F ((d8tildeRep_kQ F Q hOrient m).obj v))
    (hW₁_inv : ∀ {a b : Fin 9} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₁ a, (d8tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₁ b)
    (hW₂_inv : ∀ {a b : Fin 9} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₂ a, (d8tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₂ b)
    (hcompl : ∀ v, IsCompl (W₁ v) (W₂ v)) :
    W₁ ⟨3, by omega⟩ = W₁ ⟨6, by omega⟩ ∧
    W₂ ⟨3, by omega⟩ = W₂ ⟨6, by omega⟩ := by
  letI := Q
  have hOrient_edge := hOrient.2.1
  -- One identity edge `{i, j}` (with `j = i+1`) collapses both subspaces.
  -- Each block mirrors `d6tildeRep_kQ_chain_collapse`'s single-edge proof.
  have hstep34 : W₁ ⟨3, by omega⟩ = W₁ ⟨4, by omega⟩ ∧
      W₂ ⟨3, by omega⟩ = W₂ ⟨4, by omega⟩ := by
    have hadj : d8tildeAdj ⟨3, by omega⟩ ⟨4, by omega⟩ = 1 := by simp [d8tildeAdj]
    rcases hOrient_edge ⟨3, by omega⟩ ⟨4, by omega⟩ hadj with hQ | hQ
    · obtain ⟨a⟩ := hQ
      have hle1 : W₁ ⟨3, by omega⟩ ≤ W₁ ⟨4, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₁_inv a x hx
      have hle2 : W₂ ⟨3, by omega⟩ ≤ W₂ ⟨4, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₂_inv a x hx
      exact compl_le_forces_eq (V := Fin (2 * (m + 1)) → F) _ _ _ _
        (hcompl ⟨3, by omega⟩) (hcompl ⟨4, by omega⟩) hle1 hle2
    · obtain ⟨a⟩ := hQ
      have hle1 : W₁ ⟨4, by omega⟩ ≤ W₁ ⟨3, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₁_inv a x hx
      have hle2 : W₂ ⟨4, by omega⟩ ≤ W₂ ⟨3, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₂_inv a x hx
      have h := compl_le_forces_eq (V := Fin (2 * (m + 1)) → F) _ _ _ _
        (hcompl ⟨4, by omega⟩) (hcompl ⟨3, by omega⟩) hle1 hle2
      exact ⟨h.1.symm, h.2.symm⟩
  have hstep45 : W₁ ⟨4, by omega⟩ = W₁ ⟨5, by omega⟩ ∧
      W₂ ⟨4, by omega⟩ = W₂ ⟨5, by omega⟩ := by
    have hadj : d8tildeAdj ⟨4, by omega⟩ ⟨5, by omega⟩ = 1 := by simp [d8tildeAdj]
    rcases hOrient_edge ⟨4, by omega⟩ ⟨5, by omega⟩ hadj with hQ | hQ
    · obtain ⟨a⟩ := hQ
      have hle1 : W₁ ⟨4, by omega⟩ ≤ W₁ ⟨5, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₁_inv a x hx
      have hle2 : W₂ ⟨4, by omega⟩ ≤ W₂ ⟨5, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₂_inv a x hx
      exact compl_le_forces_eq (V := Fin (2 * (m + 1)) → F) _ _ _ _
        (hcompl ⟨4, by omega⟩) (hcompl ⟨5, by omega⟩) hle1 hle2
    · obtain ⟨a⟩ := hQ
      have hle1 : W₁ ⟨5, by omega⟩ ≤ W₁ ⟨4, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₁_inv a x hx
      have hle2 : W₂ ⟨5, by omega⟩ ≤ W₂ ⟨4, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₂_inv a x hx
      have h := compl_le_forces_eq (V := Fin (2 * (m + 1)) → F) _ _ _ _
        (hcompl ⟨5, by omega⟩) (hcompl ⟨4, by omega⟩) hle1 hle2
      exact ⟨h.1.symm, h.2.symm⟩
  have hstep56 : W₁ ⟨5, by omega⟩ = W₁ ⟨6, by omega⟩ ∧
      W₂ ⟨5, by omega⟩ = W₂ ⟨6, by omega⟩ := by
    have hadj : d8tildeAdj ⟨5, by omega⟩ ⟨6, by omega⟩ = 1 := by simp [d8tildeAdj]
    rcases hOrient_edge ⟨5, by omega⟩ ⟨6, by omega⟩ hadj with hQ | hQ
    · obtain ⟨a⟩ := hQ
      have hle1 : W₁ ⟨5, by omega⟩ ≤ W₁ ⟨6, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₁_inv a x hx
      have hle2 : W₂ ⟨5, by omega⟩ ≤ W₂ ⟨6, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₂_inv a x hx
      exact compl_le_forces_eq (V := Fin (2 * (m + 1)) → F) _ _ _ _
        (hcompl ⟨5, by omega⟩) (hcompl ⟨6, by omega⟩) hle1 hle2
    · obtain ⟨a⟩ := hQ
      have hle1 : W₁ ⟨6, by omega⟩ ≤ W₁ ⟨5, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₁_inv a x hx
      have hle2 : W₂ ⟨6, by omega⟩ ≤ W₂ ⟨5, by omega⟩ := fun x hx => by
        simpa only [d8tildeRep_kQ, d8tildeRepMap_kQ, LinearMap.id_coe, id_eq]
          using hW₂_inv a x hx
      have h := compl_le_forces_eq (V := Fin (2 * (m + 1)) → F) _ _ _ _
        (hcompl ⟨6, by omega⟩) (hcompl ⟨5, by omega⟩) hle1 hle2
      exact ⟨h.1.symm, h.2.symm⟩
  exact ⟨hstep34.1.trans (hstep45.1.trans hstep56.1),
         hstep34.2.trans (hstep45.2.trans hstep56.2)⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- γ-coupled containment for D̃₈: leaf data on the left center (vertices
`0, 1` feeding vertex `2`) propagates along the γ edge `2 → 3`, transports
across the collapsed interior `⟨3⟩ = ⟨6⟩` (supplied by
`d8tildeRep_kQ_chain_collapse`), and decomposes at the right center `6`
onto its leaves `7, 8` via `d8tilde_core6_F`. The fourth conjunct carries
the nilpotent twist `nilpotentShiftLinGen F m y` from
`gamma_from_embed2_F` (`γ(0, y) = (y, N y)`). D̃₈ analogue of
`d6tilde_gamma_containment_F`, with the single collapse edge replaced by
the three-edge chain endpoint.

**Legacy bridge.** This lemma is hypothesised against the refuted
rank-deficient bridge `d5tildeGamma_F` (`hMain_23`), whereas the corrected
rep (`d8tildeRepMap_kQ`) now carries the eigenvalue-site tube
`d5tildeGammaTube_F` on the `{2, 3}` edge. It therefore no longer matches
the rep's central map and is not used by the corrected indecomposability
assembly. The sub-C follow-up must re-derive a `d5tildeGammaTube_F`-based
containment (with the Jordan twist `Λ = λ·id + J` replacing `N`); this
statement is retained only as the worked legacy template. -/
theorem d8tilde_gamma_containment_F
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d8tildeRep_kQ F Q hOrient m).obj v))
    (hMain_02 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hMain_12 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨1, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hMain_23 : ∀ (x : Fin (2 * (m + 1)) → F), x ∈ Wmain ⟨2, by omega⟩ →
        d5tildeGamma_F F m x ∈ Wmain ⟨3, by omega⟩)
    (hcol_main : Wmain ⟨3, by omega⟩ = Wmain ⟨6, by omega⟩)
    (hMain_76 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨7, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨6, by omega⟩)
    (hMain_86 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨8, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨6, by omega⟩)
    (hOther_76 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨7, by omega⟩ →
        starEmbed1_F F m x ∈ Wother ⟨6, by omega⟩)
    (hOther_86 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨8, by omega⟩ →
        starEmbed2_F F m x ∈ Wother ⟨6, by omega⟩)
    (hc : ∀ v, IsCompl (Wmain v) (Wother v)) :
    (∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
      x ∈ Wmain ⟨7, by omega⟩) ∧
    (∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
      x ∈ Wmain ⟨8, by omega⟩) ∧
    (∀ (y : Fin (m + 1) → F), y ∈ Wmain ⟨1, by omega⟩ →
      y ∈ Wmain ⟨7, by omega⟩) ∧
    (∀ (y : Fin (m + 1) → F), y ∈ Wmain ⟨1, by omega⟩ →
      nilpotentShiftLinGen F m y ∈ Wmain ⟨8, by omega⟩) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have he1 := hMain_02 x hx
    have hgamma := hMain_23 (starEmbed1_F F m x) he1
    rw [gamma_from_embed1_F] at hgamma
    have hgamma6 := hcol_main ▸ hgamma
    exact (d8tilde_core6_F F Q hOrient m Wmain Wother hMain_76 hMain_86
      hOther_76 hOther_86 hc x x hgamma6).1
  · have he1 := hMain_02 x hx
    have hgamma := hMain_23 (starEmbed1_F F m x) he1
    rw [gamma_from_embed1_F] at hgamma
    have hgamma6 := hcol_main ▸ hgamma
    exact (d8tilde_core6_F F Q hOrient m Wmain Wother hMain_76 hMain_86
      hOther_76 hOther_86 hc x x hgamma6).2
  · have he2 := hMain_12 y hy
    have hgamma := hMain_23 (starEmbed2_F F m y) he2
    rw [gamma_from_embed2_F] at hgamma
    have hgamma6 := hcol_main ▸ hgamma
    exact (d8tilde_core6_F F Q hOrient m Wmain Wother hMain_76 hMain_86
      hOther_76 hOther_86 hc y (nilpotentShiftLinGen F m y) hgamma6).1
  · have he2 := hMain_12 y hy
    have hgamma := hMain_23 (starEmbed2_F F m y) he2
    rw [gamma_from_embed2_F] at hgamma
    have hgamma6 := hcol_main ▸ hgamma
    exact (d8tilde_core6_F F Q hOrient m Wmain Wother hMain_76 hMain_86
      hOther_76 hOther_86 hc y (nilpotentShiftLinGen F m y) hgamma6).2

/-! ## Section 5: Indecomposability (deferred sorry)

With the corrected eigenvalue-site construction (Section 4, edge `{2, 3}`
now `d5tildeGammaTube_F`), the statement below is **true for every
orientation** — the rank-deficient under-coupling that made the old
`[[I, I], [I, N]]` bridge decomposable in the mixed / reversed-leaf
orientations (#4566 / #4597) is gone. The proof body is deferred to a
follow-up sub-C issue, which must generalise the worked D̃₅ assembly
`d5tildeRep_kQ_isIndecomposable` (`FieldGenericD5Tilde.lean`, the
pattern-setter under #4647 / #4663) from one central γ-edge to the
length-4 internal chain via `d8tildeRep_kQ_chain_collapse`. The per-(F, Q)
infinite-type theorem below transitively depends on this sorry.
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic indecomposability of `d8tildeRep_kQ` (corrected
eigenvalue-site tube).

True for every orientation on the corrected rep. The proof body is
deferred to a sub-C follow-up issue: generalise the worked D̃₅ assembly
`d5tildeRep_kQ_isIndecomposable` (`FieldGenericD5Tilde.lean`, #4663) to
the length-4 internal chain. The route is leaf collapse at the two
centers (`d8tilde_core_F` / `d8tilde_core6_F`) → interior collapse
`⟨3⟩ = ⟨6⟩` (`d8tildeRep_kQ_chain_collapse`) → a single
`(λ·id + J)`-invariant splitting at the eigenvalue site killed by
`eigenvalue_jordan_invariant_compl_trivial_gen`. The consumer
`d8tilde_not_finite_type_per_kQ` carries this sorry transitively. -/
theorem d8tildeRep_kQ_isIndecomposable
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj)
    (m : ℕ) :
    (d8tildeRep_kQ F Q hOrient m).IsIndecomposable := by
  sorry

/-! ## Section 6: Per-(F, Q) infinite-type theorem -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) D̃₈ infinite-type theorem: for any
algebraically closed field `F` and any orientation `Q` of `d8tildeAdj`,
the set of dimension vectors of indecomposable representations is
infinite. Mirrors the proof shape of `d7tilde_not_finite_type_per_kQ`
(`FieldGenericD7Tilde.lean:272`) and `dTilde_not_finite_type`
(`InfiniteTypeConstructions.lean:3191`).

Injectivity comes from vertex `0`, where `d8tildeDim m 0 = m + 1`.

This theorem carries no direct `sorry`, but transitively depends on
`d8tildeRep_kQ_isIndecomposable`, whose proof body is deferred — see
its docstring. -/
theorem d8tilde_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 9))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 9) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 9 Q d8tildeAdj) :
    ¬ Set.Finite
      {d : Fin 9 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 9) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ, d8tildeDim m ∈
      {d : Fin 9 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 9) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨d8tildeRep_kQ F Q hOrient m,
      d8tildeRep_kQ_isIndecomposable F Q hOrient m,
      d8tildeRep_kQ_dimVec F Q hOrient m⟩
  have hinj : Function.Injective (d8tildeDim : ℕ → Fin 9 → ℕ) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨0, by omega⟩
    have hnot : ¬(2 ≤ (⟨0, by omega⟩ : Fin 9).val ∧
      (⟨0, by omega⟩ : Fin 9).val ≤ 6) := by simp
    simp only [d8tildeDim, hnot, ite_false] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section 7: Embedding D̃₈ into a host tree (per-(F, Q) helper)

Mirrors `embed_d7tilde_in_tree_per_kQ` (`FieldGenericD7Tilde.lean:323`)
for the D̃₈ shape: two non-adjacent degree-3 branch points (`p`, `t`)
each with two leaves (`a, b` for `p`; `u, v` for `t`), connected by an
internal length-4 chain `p – q – r – s – t`. Given the eight edges, the
`p – t` non-edge, and the distinctness hypotheses, this helper derives
the remaining 27-pair adjacency lattice and dispatches via
`subgraph_infinite_type_transfer_per_kQ` and
`d8tilde_not_finite_type_per_kQ`.

Because the branch points are now at distance 4 (vs. distance 3 in D̃₇),
the three interior path-distinctness facts `p ≠ r`, `q ≠ s`, `r ≠ t` are
*not* derivable from the branch non-edge alone (a graph with `p = r`,
etc., satisfies all the edge and `p – t` non-edge hypotheses), so they
are taken as additional inputs. The caller supplies them from the host
chain's `Nodup`. -/

set_option maxHeartbeats 1600000 in
-- The 27-pair adjacency lattice drives a sizeable `linarith` over the 81
-- `fin_cases` of `hembed`, exceeding the default 200k heartbeat limit.
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) embedding of D̃₈ into a host acyclic adjacency matrix.

Vertex map (matching `d8tildeAdj`):
`0 → a, 1 → b, 2 → p, 3 → q, 4 → r, 5 → s, 6 → t, 7 → u, 8 → v`. The
eight D̃₈ edges are: `a-p, b-p, p-q, q-r, r-s, s-t, t-u, t-v`; vertices
`p` and `t` are the two non-adjacent degree-3 branch points. -/
theorem embed_d8tilde_in_tree_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (a b p q r s t u v : Fin n)
    (hap : adj p a = 1) (hbp : adj p b = 1) (hpq : adj p q = 1)
    (hqr : adj q r = 1) (hrs : adj r s = 1) (hst : adj s t = 1)
    (htu : adj t u = 1) (htv : adj t v = 1)
    (hpt : adj p t = 0)
    (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (huv : u ≠ v) (hsu : s ≠ u) (hsv : s ≠ v)
    (hpt_ne : p ≠ t) (hpr_ne : p ≠ r) (hqs_ne : q ≠ s) (hrt_ne : r ≠ t)
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
  -- Edge-derived distinctness — directions matching the edge labels.
  have hap_ne : a ≠ p := (ne_of_adj' p a hap).symm
  have hbp_ne : b ≠ p := (ne_of_adj' p b hbp).symm
  have hpq_ne : p ≠ q := ne_of_adj' p q hpq
  have hqr_ne : q ≠ r := ne_of_adj' q r hqr
  have hrs_ne : r ≠ s := ne_of_adj' r s hrs
  have hst_ne : s ≠ t := ne_of_adj' s t hst
  have htu_ne : t ≠ u := ne_of_adj' t u htu
  have htv_ne : t ≠ v := ne_of_adj' t v htv
  -- Reversed edges.
  have hap' : adj a p = 1 := (adj_comm a p).trans hap
  have hbp' : adj b p = 1 := (adj_comm b p).trans hbp
  have hpq' : adj q p = 1 := (adj_comm q p).trans hpq
  have hqr' : adj r q = 1 := (adj_comm r q).trans hqr
  have hrs' : adj s r = 1 := (adj_comm s r).trans hrs
  have hst' : adj t s = 1 := (adj_comm t s).trans hst
  have htu' : adj u t = 1 := (adj_comm u t).trans htu
  have htv' : adj v t = 1 := (adj_comm v t).trans htv
  have hpt' : adj t p = 0 := (adj_comm t p).trans hpt
  -- Remaining interior path-distinctness derivable from the branch non-edge.
  have hps_ne : p ≠ s := by
    intro h; rw [h, hst] at hpt; exact one_ne_zero hpt
  have hqt_ne : q ≠ t := by
    intro h; rw [← h, hpq] at hpt; exact one_ne_zero hpt
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
  have path_nodup7 : ∀ (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : Fin n),
      x₁ ≠ x₂ → x₁ ≠ x₃ → x₁ ≠ x₄ → x₁ ≠ x₅ → x₁ ≠ x₆ → x₁ ≠ x₇ →
      x₂ ≠ x₃ → x₂ ≠ x₄ → x₂ ≠ x₅ → x₂ ≠ x₆ → x₂ ≠ x₇ →
      x₃ ≠ x₄ → x₃ ≠ x₅ → x₃ ≠ x₆ → x₃ ≠ x₇ →
      x₄ ≠ x₅ → x₄ ≠ x₆ → x₄ ≠ x₇ →
      x₅ ≠ x₆ → x₅ ≠ x₇ → x₆ ≠ x₇ →
      [x₁, x₂, x₃, x₄, x₅, x₆, x₇].Nodup := by
    intro x₁ x₂ x₃ x₄ x₅ x₆ x₇
      h12 h13 h14 h15 h16 h17 h23 h24 h25 h26 h27 h34 h35 h36 h37
      h45 h46 h47 h56 h57 h67
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨h12, h13, h14, h15, h16, h17⟩, ⟨h23, h24, h25, h26, h27⟩,
      ⟨h34, h35, h36, h37⟩, ⟨h45, h46, h47⟩, ⟨h56, h57⟩, h67⟩
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
  have path_edges7 : ∀ (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : Fin n),
      adj x₁ x₂ = 1 → adj x₂ x₃ = 1 → adj x₃ x₄ = 1 →
      adj x₄ x₅ = 1 → adj x₅ x₆ = 1 → adj x₆ x₇ = 1 →
      ∀ k, (hk : k + 1 < [x₁, x₂, x₃, x₄, x₅, x₆, x₇].length) →
        adj ([x₁, x₂, x₃, x₄, x₅, x₆, x₇].get ⟨k, by omega⟩)
          ([x₁, x₂, x₃, x₄, x₅, x₆, x₇].get ⟨k + 1, hk⟩) = 1 := by
    intro x₁ x₂ x₃ x₄ x₅ x₆ x₇ e12 e23 e34 e45 e56 e67 k hk
    have : k + 1 < 7 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  -- Triangle non-edges via `acyclic_no_triangle` (9 distance-2 non-edges).
  have hab0 : adj a b = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p a b hab hap_ne hbp_ne hap hbp
  have haq0 : adj a q = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p a q haq hap_ne hpq_ne.symm hap hpq
  have hbq0 : adj b q = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p b q hbq hbp_ne hpq_ne.symm hbp hpq
  have huv0 : adj u v = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic t u v huv htu_ne.symm htv_ne.symm htu htv
  have hsu0 : adj s u = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic t s u hsu hst_ne htu_ne.symm hst' htu
  have hsv0 : adj s v = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic t s v hsv hst_ne htv_ne.symm hst' htv
  have hpr0 : adj p r = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q p r hpr_ne hpq_ne hqr_ne.symm hpq' hqr
  have hqs0 : adj q s = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic r q s hqs_ne hqr_ne hrs_ne.symm hqr' hrs
  have hrt0 : adj r t = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic s r t hrt_ne hrs_ne hst_ne.symm hrs' hst
  -- Cross-side distinctness derived from distance-2 non-edges.
  have har_ne : a ≠ r := by intro h; rw [h] at hap; linarith [hpr0]
  have hbr_ne : b ≠ r := by intro h; rw [h] at hbp; linarith [hpr0]
  have hru_ne : r ≠ u := by intro h; rw [h] at hrt0; rw [adj_comm] at hrt0; linarith [htu]
  have hrv_ne : r ≠ v := by intro h; rw [h] at hrt0; rw [adj_comm] at hrt0; linarith [htv]
  have hpu_ne : p ≠ u := by intro h; rw [h] at hpt'; linarith [htu]
  have hpv_ne : p ≠ v := by intro h; rw [h] at hpt'; linarith [htv]
  -- Distance-3 non-edges (4-vertex paths).
  have hps0 : adj p s = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [p, q, r, s] (by simp)
      (path_nodup4 _ _ _ _ hpq_ne hpr_ne hps_ne hqr_ne hqs_ne hrs_ne)
      (path_edges4 _ _ _ _ hpq hqr hrs)
    simpa using h
  have hqt0 : adj q t = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [q, r, s, t] (by simp)
      (path_nodup4 _ _ _ _ hqr_ne hqs_ne hqt_ne hrs_ne hrt_ne hst_ne)
      (path_edges4 _ _ _ _ hqr hrs hst)
    simpa using h
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
  have hru0 : adj r u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [r, s, t, u] (by simp)
      (path_nodup4 _ _ _ _ hrs_ne hrt_ne hru_ne hst_ne hsu htu_ne)
      (path_edges4 _ _ _ _ hrs hst htu)
    simpa using h
  have hrv0 : adj r v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [r, s, t, v] (by simp)
      (path_nodup4 _ _ _ _ hrs_ne hrt_ne hrv_ne hst_ne hsv htv_ne)
      (path_edges4 _ _ _ _ hrs hst htv)
    simpa using h
  -- Cross-side distinctness derived from distance-3 non-edges.
  have has_ne : a ≠ s := by intro h; rw [h] at hap; linarith [hps0]
  have hbs_ne : b ≠ s := by intro h; rw [h] at hbp; linarith [hps0]
  have hqu_ne : q ≠ u := by intro h; rw [h] at hqt0; rw [adj_comm] at hqt0; linarith [htu]
  have hqv_ne : q ≠ v := by intro h; rw [h] at hqt0; rw [adj_comm] at hqt0; linarith [htv]
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
  have hqu0 : adj q u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [q, r, s, t, u] (by simp)
      (path_nodup5 _ _ _ _ _ hqr_ne hqs_ne hqt_ne hqu_ne
        hrs_ne hrt_ne hru_ne hst_ne hsu htu_ne)
      (path_edges5 _ _ _ _ _ hqr hrs hst htu)
    simpa using h
  have hqv0 : adj q v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [q, r, s, t, v] (by simp)
      (path_nodup5 _ _ _ _ _ hqr_ne hqs_ne hqt_ne hqv_ne
        hrs_ne hrt_ne hrv_ne hst_ne hsv htv_ne)
      (path_edges5 _ _ _ _ _ hqr hrs hst htv)
    simpa using h
  -- Cross-side distinctness derived from distance-4 non-edges / branch non-edge.
  have hat_ne : a ≠ t := by intro h; rw [h] at hap; linarith [hpt]
  have hbt_ne : b ≠ t := by intro h; rw [h] at hbp; linarith [hpt]
  -- Distance-5 non-edges (6-vertex paths).
  have hat0 : adj a t = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [a, p, q, r, s, t] (by simp)
      (path_nodup6 _ _ _ _ _ _ hap_ne haq har_ne has_ne hat_ne
        hpq_ne hpr_ne hps_ne hpt_ne hqr_ne hqs_ne hqt_ne hrs_ne hrt_ne hst_ne)
      (path_edges6 _ _ _ _ _ _ hap' hpq hqr hrs hst)
    simpa using h
  have hbt0 : adj b t = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [b, p, q, r, s, t] (by simp)
      (path_nodup6 _ _ _ _ _ _ hbp_ne hbq hbr_ne hbs_ne hbt_ne
        hpq_ne hpr_ne hps_ne hpt_ne hqr_ne hqs_ne hqt_ne hrs_ne hrt_ne hst_ne)
      (path_edges6 _ _ _ _ _ _ hbp' hpq hqr hrs hst)
    simpa using h
  have hpu0 : adj p u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [p, q, r, s, t, u] (by simp)
      (path_nodup6 _ _ _ _ _ _ hpq_ne hpr_ne hps_ne hpt_ne hpu_ne
        hqr_ne hqs_ne hqt_ne hqu_ne hrs_ne hrt_ne hru_ne hst_ne hsu htu_ne)
      (path_edges6 _ _ _ _ _ _ hpq hqr hrs hst htu)
    simpa using h
  have hpv0 : adj p v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [p, q, r, s, t, v] (by simp)
      (path_nodup6 _ _ _ _ _ _ hpq_ne hpr_ne hps_ne hpt_ne hpv_ne
        hqr_ne hqs_ne hqt_ne hqv_ne hrs_ne hrt_ne hrv_ne hst_ne hsv htv_ne)
      (path_edges6 _ _ _ _ _ _ hpq hqr hrs hst htv)
    simpa using h
  -- Cross-leaf distinctness (from distance-5 non-edges).
  have hau_ne : a ≠ u := by intro h; rw [h] at hap; linarith [hpu0]
  have hav_ne : a ≠ v := by intro h; rw [h] at hap; linarith [hpv0]
  have hbu_ne : b ≠ u := by intro h; rw [h] at hbp; linarith [hpu0]
  have hbv_ne : b ≠ v := by intro h; rw [h] at hbp; linarith [hpv0]
  -- Distance-6 non-edges (7-vertex paths).
  have hau0 : adj a u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [a, p, q, r, s, t, u] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hap_ne haq har_ne has_ne hat_ne hau_ne
        hpq_ne hpr_ne hps_ne hpt_ne hpu_ne hqr_ne hqs_ne hqt_ne hqu_ne
        hrs_ne hrt_ne hru_ne hst_ne hsu htu_ne)
      (path_edges7 _ _ _ _ _ _ _ hap' hpq hqr hrs hst htu)
    simpa using h
  have hav0 : adj a v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [a, p, q, r, s, t, v] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hap_ne haq har_ne has_ne hat_ne hav_ne
        hpq_ne hpr_ne hps_ne hpt_ne hpv_ne hqr_ne hqs_ne hqt_ne hqv_ne
        hrs_ne hrt_ne hrv_ne hst_ne hsv htv_ne)
      (path_edges7 _ _ _ _ _ _ _ hap' hpq hqr hrs hst htv)
    simpa using h
  have hbu0 : adj b u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [b, p, q, r, s, t, u] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hbp_ne hbq hbr_ne hbs_ne hbt_ne hbu_ne
        hpq_ne hpr_ne hps_ne hpt_ne hpu_ne hqr_ne hqs_ne hqt_ne hqu_ne
        hrs_ne hrt_ne hru_ne hst_ne hsu htu_ne)
      (path_edges7 _ _ _ _ _ _ _ hbp' hpq hqr hrs hst htu)
    simpa using h
  have hbv0 : adj b v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [b, p, q, r, s, t, v] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hbp_ne hbq hbr_ne hbs_ne hbt_ne hbv_ne
        hpq_ne hpr_ne hps_ne hpt_ne hpv_ne hqr_ne hqs_ne hqt_ne hqv_ne
        hrs_ne hrt_ne hrv_ne hst_ne hsv htv_ne)
      (path_edges7 _ _ _ _ _ _ _ hbp' hpq hqr hrs hst htv)
    simpa using h
  -- Construct φ : Fin 9 ↪ Fin n.
  let φ_fun : Fin 9 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => a  | ⟨1, _⟩ => b  | ⟨2, _⟩ => p  | ⟨3, _⟩ => q
    | ⟨4, _⟩ => r  | ⟨5, _⟩ => s  | ⟨6, _⟩ => t  | ⟨7, _⟩ => u
    | ⟨8, _⟩ => v
  have φ_inj : Function.Injective φ_fun := by
    intro i j hij; simp only [φ_fun] at hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exact absurd hij ‹_›)
      | (exact absurd hij.symm ‹_›)
  let φ : Fin 9 ↪ Fin n := ⟨φ_fun, φ_inj⟩
  have hembed : ∀ i j, d8tildeAdj i j = adj (φ i) (φ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [d8tildeAdj, φ, φ_fun] <;> norm_num <;>
      linarith [hdiag a, hdiag b, hdiag p, hdiag q, hdiag r, hdiag s, hdiag t,
        hdiag u, hdiag v,
        hap, hbp, hpq, hqr, hrs, hst, htu, htv,
        hap', hbp', hpq', hqr', hrs', hst', htu', htv',
        hpt, hpt',
        hab0, haq0, hbq0, huv0, hsu0, hsv0, hpr0, hqs0, hrt0,
        adj_comm a b, adj_comm a q, adj_comm b q, adj_comm u v,
        adj_comm s u, adj_comm s v, adj_comm p r, adj_comm q s, adj_comm r t,
        hps0, hqt0, har0, hbr0, hru0, hrv0,
        adj_comm p s, adj_comm q t, adj_comm a r, adj_comm b r,
        adj_comm r u, adj_comm r v,
        has0, hbs0, hqu0, hqv0,
        adj_comm a s, adj_comm b s, adj_comm q u, adj_comm q v,
        hat0, hbt0, hpu0, hpv0,
        adj_comm a t, adj_comm b t, adj_comm p u, adj_comm p v,
        hau0, hav0, hbu0, hbv0,
        adj_comm a u, adj_comm a v, adj_comm b u, adj_comm b v]
  exact subgraph_infinite_type_transfer_per_kQ φ F Q
    (d8tilde_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

end Etingof
