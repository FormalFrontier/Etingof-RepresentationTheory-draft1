import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericStar
import EtingofRepresentationTheory.Chapter6.FieldGenericD5Tilde

/-!
# Orientation-Generic D̃₆ Construction (#2974)

F-generic, orientation-generic version of the D̃₆ extended-Dynkin
representation. This file provides `d6tildeRep_kQ`, its dimension-vector
lemma, an indecomposability stub, and the per-(F, Q) infinite-type
theorem `d6tilde_not_finite_type_per_kQ`.

D̃₆ is the affine D₆ Dynkin diagram with 7 vertices, two non-adjacent
degree-3 branch points each with two leaves, connected by a length-2
internal chain:

```
0       5
 \     /
  2-3-4
 /     \
1       6
```

Vertex labelling: `0, 1` are leaves of left branch `2`; `2-3-4` is the
internal path; `5, 6` are leaves of right branch `4`. The two degree-3
branch points `2` and `4` are at distance 2 (one internal vertex `3`).

The canonical orientation (`d6tildeQuiver`) is the universal sink-
orientation pattern from `dTildeQuiver` (`InfiniteTypeConstructions.lean:
2049`): both leaf pairs point inward, the internal chain runs
left-to-right. For an arbitrary orientation `Q` of `d6tildeAdj`, each
of the six edges may point either way, so the construction provides a
forward and reverse map per edge.

Indecomposability mirrors the deferred-`sorry` precedent of
`d7tildeRep_kQ_isIndecomposable` (`FieldGenericD7Tilde.lean:247`) and
`d5tildeRep_kQ_isIndecomposable` (`FieldGenericD5Tilde.lean:980`) — the
proof body is deferred to a follow-up issue; the per-(F, Q) infinite-
type theorem `d6tilde_not_finite_type_per_kQ` transitively depends on
it. The consumer of this helper is the `chain.length = 3` all-leaves
sub-case of the non-adjacent-branches assembly (`#2955` / `#2974`).

See `Chapter6/FieldGenericInfiniteType.lean` for the meaning of the
`_F` / `_kQ` / `_per_kQ` suffixes.
-/

open scoped Matrix

namespace Etingof

/-! ## Section 1: D̃₆ adjacency matrix -/

/-- Adjacency matrix for the extended Dynkin diagram D̃₆ on 7 vertices.
Edges: `0-2`, `1-2`, `2-3`, `3-4`, `4-5`, `4-6`.
Vertices `2` and `4` have degree 3; the rest have degree 1. -/
def d6tildeAdj : Matrix (Fin 7) (Fin 7) ℤ := fun i j =>
  match i.val, j.val with
  -- left leaves to left branch (vertex 2)
  | 0, 2 | 2, 0 | 1, 2 | 2, 1
  -- internal chain 2-3-4
  | 2, 3 | 3, 2 | 3, 4 | 4, 3
  -- right leaves to right branch (vertex 4)
  | 4, 5 | 5, 4 | 4, 6 | 6, 4 => 1
  | _, _ => 0

theorem d6tildeAdj_symm : d6tildeAdj.IsSymm := by
  ext i j
  simp only [d6tildeAdj, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem d6tildeAdj_diag (i : Fin 7) : d6tildeAdj i i = 0 := by
  fin_cases i <;> simp [d6tildeAdj]

theorem d6tildeAdj_01 (i j : Fin 7) : d6tildeAdj i j = 0 ∨ d6tildeAdj i j = 1 := by
  fin_cases i <;> fin_cases j <;> simp [d6tildeAdj]

/-! ## Section 2: D̃₆ canonical quiver and orientation property -/

/-- Canonical orientation for D̃₆: leaves point inward and the internal
chain runs left-to-right. Arrows:
`0→2, 1→2, 2→3, 3→4, 5→4, 6→4`. -/
def d6tildeQuiver : Quiver (Fin 7) where
  Hom i j := PLift (
    (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 2) ∨
    (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 4) ∨
    (i.val = 5 ∧ j.val = 4) ∨ (i.val = 6 ∧ j.val = 4))

instance d6tildeQuiver_subsingleton (a b : Fin 7) :
    Subsingleton (@Quiver.Hom (Fin 7) d6tildeQuiver a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

private theorem d6tilde_arrow_implies_edge (i j : Fin 7)
    (hp : (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 2) ∨
      (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 4) ∨
      (i.val = 5 ∧ j.val = 4) ∨ (i.val = 6 ∧ j.val = 4)) :
    d6tildeAdj i j = 1 := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [d6tildeAdj, h1, h2]

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem d6tildeOrientation_isOrientationOf :
    @Etingof.IsOrientationOf 7 d6tildeQuiver d6tildeAdj := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · -- Non-edges have no arrows
    constructor; intro ⟨hp⟩
    exact hij (d6tilde_arrow_implies_edge i j hp)
  · -- Each edge has an arrow in one direction
    fin_cases i <;> fin_cases j <;> simp [d6tildeAdj] at hij <;>
      first
      | (left; exact ⟨⟨by decide⟩⟩)
      | (right; exact ⟨⟨by decide⟩⟩)
  · -- No two-way arrows (antisymmetry)
    obtain ⟨hp⟩ := hi; obtain ⟨hq⟩ := hj
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      (rcases hq with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ |
        ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
         omega)

/-! ## Section 3: D̃₆ dimension vector

Vertices `0, 1, 5, 6` are leaves with dimension `m + 1`; the path
vertices `2, 3, 4` have dimension `2 * (m + 1)`. -/

/-- Dimension of vertex `v` in the D̃₆ representation with parameter `m`. -/
def d6tildeDim (m : ℕ) (v : Fin 7) : ℕ :=
  if 2 ≤ v.val ∧ v.val ≤ 4 then 2 * (m + 1) else m + 1

/-! ## Section 4: D̃₆ direction-aware match-based representation map

For an arbitrary orientation `Q` of `d6tildeAdj`, each of the six edges
may point in either direction. The map function below provides the
canonical forward map and a reverse map per edge:

* `0-2`, `1-2`: `starEmbed1_F / starEmbed2_F` (canonical) and
  `starFirst_F / starSecond_F` (reverses).
* `2-3`: `d5tildeGamma_F` (canonical) and `d5tildeGammaInv_F` (reverse).
* `3-4`: `LinearMap.id` in both directions (internal-chain edge between
  equal-dimension blocks).
* `4-5`, `4-6`: `starEmbed1_F / starEmbed2_F` (canonical) and
  `starFirst_F / starSecond_F` (reverses).

Outside these 12 directed edges the map is `0` (ruled out by `hOrient`).
-/

/-- Direction-aware match-based map function for the orientation-generic
D̃₆ representation. -/
private noncomputable def d6tildeRepMap_kQ (F : Type) [Field F] (m : ℕ) (a b : Fin 7) :
    (Fin (d6tildeDim m a) → F) →ₗ[F] (Fin (d6tildeDim m b) → F) :=
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
  -- Edge {4, 5}: canonical 5→4, reverse 4→5
  | ⟨5, _⟩, ⟨4, _⟩ => starEmbed1_F F m
  | ⟨4, _⟩, ⟨5, _⟩ => starFirst_F F m
  -- Edge {4, 6}: canonical 6→4, reverse 4→6
  | ⟨6, _⟩, ⟨4, _⟩ => starEmbed2_F F m
  | ⟨4, _⟩, ⟨6, _⟩ => starSecond_F F m
  -- Non-edges (ruled out by `hOrient`); placeholder.
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic D̃₆ representation over an arbitrary field `F`
with arbitrary orientation `Q` of `d6tildeAdj`. Dimension vector follows
`d6tildeDim`: path vertices `2, 3, 4` have dim `2(m+1)`; leaf vertices
`0, 1, 5, 6` have dim `m+1`.

The map on an arrow `e : Q.Hom a b` depends only on the underlying
unordered edge `{a, b}` and the direction `a → b`. Each of the six
edges of `d6tildeAdj` contributes one canonical map and one reverse map
(see `d6tildeRepMap_kQ` for the dispatch). The orientation hypothesis
`hOrient` is not used by the construction itself; it is recorded so
that downstream lemmas (the deferred indecomposability proof) can
pattern-match on which arrows exist. -/
noncomputable def d6tildeRep_kQ
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (_hOrient : @Etingof.IsOrientationOf 7 Q d6tildeAdj)
    (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin 7) _ Q := by
  letI := Q
  exact {
    obj := fun v => Fin (d6tildeDim m v) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => d6tildeRepMap_kQ F m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The orientation-generic D̃₆ rep has the expected dimension vector
`d6tildeDim m` at each vertex. -/
theorem d6tildeRep_kQ_dimVec
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 7 Q d6tildeAdj)
    (m : ℕ) (v : Fin 7) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin 7) _ Q
      (d6tildeRep_kQ F Q hOrient m) v ≃ₗ[F] (Fin (d6tildeDim m v) → F)) :=
  ⟨LinearEquiv.refl F _⟩

/-! ## Section 4b: Identity-chain collapse (#4527 sub-A infrastructure)

D̃₆ is D̃₅ with one extra internal vertex: leaves `0,1` → branch `2` →
(γ via `d5tildeGamma_F`) → `3` → (`id`) → `4` ← leaves `5,6`. The single
internal edge `3-4` uses `LinearMap.id` in both directions (see
`d6tildeRepMap_kQ`). So for any complementary invariant submodule pair
`(W₁, W₂)`, invariance through that identity arrow forces
`W₁⟨3⟩ = W₁⟨4⟩` and `W₂⟨3⟩ = W₂⟨4⟩`, regardless of how `Q` orients the
edge. After this collapse, the picture at the merged `3 = 4` space is
exactly the d5tilde vertex-3 picture, with the right leaves relabelled
`4 ↦ 5, 5 ↦ 6`. This mirrors deliverable 1 of the D̃₇ sub-A issue. -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Identity-chain collapse for D̃₆: the internal edge `3-4` is an
identity iso in either orientation, so any complementary invariant pair
`(W₁, W₂)` has `W₁⟨3⟩ = W₁⟨4⟩` and `W₂⟨3⟩ = W₂⟨4⟩`. -/
theorem d6tildeRep_kQ_chain_collapse
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 7 Q d6tildeAdj)
    (m : ℕ)
    (W₁ W₂ : ∀ v, Submodule F ((d6tildeRep_kQ F Q hOrient m).obj v))
    (hW₁_inv : ∀ {a b : Fin 7} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₁ a, (d6tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₁ b)
    (hW₂_inv : ∀ {a b : Fin 7} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₂ a, (d6tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₂ b)
    (hcompl : ∀ v, IsCompl (W₁ v) (W₂ v)) :
    W₁ ⟨3, by omega⟩ = W₁ ⟨4, by omega⟩ ∧
    W₂ ⟨3, by omega⟩ = W₂ ⟨4, by omega⟩ := by
  letI := Q
  have hOrient_edge := hOrient.2.1
  have h34 : d6tildeAdj ⟨3, by omega⟩ ⟨4, by omega⟩ = 1 := by simp [d6tildeAdj]
  rcases hOrient_edge ⟨3, by omega⟩ ⟨4, by omega⟩ h34 with hQ34 | hQ34
  · -- Edge oriented `3 → 4` (canonical): map = `id`, so `W₁⟨3⟩ ≤ W₁⟨4⟩`.
    obtain ⟨a34⟩ := hQ34
    have hW₁_le : W₁ ⟨3, by omega⟩ ≤ W₁ ⟨4, by omega⟩ := by
      intro x hx
      have h := hW₁_inv a34 x hx
      simpa only [d6tildeRep_kQ, d6tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
    have hW₂_le : W₂ ⟨3, by omega⟩ ≤ W₂ ⟨4, by omega⟩ := by
      intro x hx
      have h := hW₂_inv a34 x hx
      simpa only [d6tildeRep_kQ, d6tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
    exact compl_le_forces_eq (V := Fin (2 * (m + 1)) → F)
      (W₁ ⟨3, by omega⟩) (W₂ ⟨3, by omega⟩)
      (W₁ ⟨4, by omega⟩) (W₂ ⟨4, by omega⟩)
      (hcompl ⟨3, by omega⟩) (hcompl ⟨4, by omega⟩) hW₁_le hW₂_le
  · -- Edge oriented `4 → 3` (reversed): map = `id`, so `W₁⟨4⟩ ≤ W₁⟨3⟩`.
    obtain ⟨a43⟩ := hQ34
    have hW₁_le : W₁ ⟨4, by omega⟩ ≤ W₁ ⟨3, by omega⟩ := by
      intro x hx
      have h := hW₁_inv a43 x hx
      simpa only [d6tildeRep_kQ, d6tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
    have hW₂_le : W₂ ⟨4, by omega⟩ ≤ W₂ ⟨3, by omega⟩ := by
      intro x hx
      have h := hW₂_inv a43 x hx
      simpa only [d6tildeRep_kQ, d6tildeRepMap_kQ, LinearMap.id_coe, id_eq] using h
    have h := compl_le_forces_eq (V := Fin (2 * (m + 1)) → F)
      (W₁ ⟨4, by omega⟩) (W₂ ⟨4, by omega⟩)
      (W₁ ⟨3, by omega⟩) (W₂ ⟨3, by omega⟩)
      (hcompl ⟨4, by omega⟩) (hcompl ⟨3, by omega⟩) hW₁_le hW₂_le
    exact ⟨h.1.symm, h.2.symm⟩

/-! ## Section 4c: Core decomposition helpers (#4527 sub-A infrastructure)

D̃₆ analogues of the d5tilde `core_F` / `core3_F` / `gamma_containment_F`
helpers. The left branch `2` (leaves `0,1`) is identical to d5tilde's
branch `2`, so `d6tilde_core_F` is a verbatim port. The right branch is
vertex `4` (leaves `5,6`) instead of d5tilde's vertex `3` (leaves
`4,5`), so `d6tilde_core4_F` is the index-shifted port of
`d5tilde_core3_F`. The γ-containment helper threads through the extra
identity edge `3-4` via the collapse equality `Wmain⟨3⟩ = Wmain⟨4⟩`. -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Core decomposition at v=2 (left branch, leaves `0,1`): if
`starEmbed1_F x + starEmbed2_F z ∈ Wmain ⟨2⟩`, then `x ∈ Wmain ⟨0⟩` and
`z ∈ Wmain ⟨1⟩`. Verbatim port of `d5tilde_core_F`. -/
theorem d6tilde_core_F
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 7 Q d6tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d6tildeRep_kQ F Q hOrient m).obj v))
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
/-- Core decomposition at v=4 (right branch, leaves `5,6`): if
`starEmbed1_F x + starEmbed2_F z ∈ Wmain ⟨4⟩`, then `x ∈ Wmain ⟨5⟩` and
`z ∈ Wmain ⟨6⟩`. Index-shifted port of `d5tilde_core3_F`
(`3 ↦ 4, 4 ↦ 5, 5 ↦ 6`). -/
theorem d6tilde_core4_F
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 7 Q d6tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d6tildeRep_kQ F Q hOrient m).obj v))
    (hMain_54 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨5, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨4, by omega⟩)
    (hMain_64 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨6, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨4, by omega⟩)
    (hOther_54 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨5, by omega⟩ →
        starEmbed1_F F m x ∈ Wother ⟨4, by omega⟩)
    (hOther_64 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨6, by omega⟩ →
        starEmbed2_F F m x ∈ Wother ⟨4, by omega⟩)
    (hc : ∀ v, IsCompl (Wmain v) (Wother v))
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ Wmain ⟨4, by omega⟩) :
    x ∈ Wmain ⟨5, by omega⟩ ∧ z ∈ Wmain ⟨6, by omega⟩ := by
  have htop5 := (hc ⟨5, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := x)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop5
  have htop6 := (hc ⟨6, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := z)
  obtain ⟨c, hcm, d, hd, hcd⟩ := Submodule.mem_sup.mp htop6
  have ha4 := hMain_54 a ha
  have hcm4 := hMain_64 c hcm
  have hb4 := hOther_54 b hb
  have hd4 := hOther_64 d hd
  have hsum : starEmbed1_F F m x + starEmbed2_F F m z =
      (starEmbed1_F F m a + starEmbed2_F F m c) +
        (starEmbed1_F F m b + starEmbed2_F F m d) := by
    rw [← hab, ← hcd]; simp [map_add]; abel
  rw [hsum] at hmem
  have hadd : starEmbed1_F F m a + starEmbed2_F F m c ∈ Wmain ⟨4, by omega⟩ :=
    (Wmain ⟨4, by omega⟩).add_mem ha4 hcm4
  have hw'_in_W : starEmbed1_F F m b + starEmbed2_F F m d ∈
      Wmain ⟨4, by omega⟩ := by
    have hsmul := (Wmain ⟨4, by omega⟩).smul_mem (-1 : F) hadd
    have hadd2 := (Wmain ⟨4, by omega⟩).add_mem hmem hsmul
    have key : starEmbed1_F F m a + starEmbed2_F F m c +
        (starEmbed1_F F m b + starEmbed2_F F m d) +
        (-1 : F) • (starEmbed1_F F m a + starEmbed2_F F m c) =
        starEmbed1_F F m b + starEmbed2_F F m d := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rwa [key] at hadd2
  have hzero : starEmbed1_F F m b + starEmbed2_F F m d = 0 := by
    have hcross := Submodule.mem_inf.mpr ⟨hw'_in_W,
      (Wother ⟨4, by omega⟩).add_mem hb4 hd4⟩
    rwa [(hc ⟨4, by omega⟩).inf_eq_bot, Submodule.mem_bot] at hcross
  obtain ⟨hb0, hd0⟩ := embed_sum_zero_F F m b d hzero
  exact ⟨hab ▸ by rw [hb0, add_zero]; exact ha,
         hcd ▸ by rw [hd0, add_zero]; exact hcm⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- γ-coupled leaf containments for D̃₆. Given canonical embed pushes on
both `Wmain` and `Wother`, the `2→3` γ-push on `Wmain`, and the
chain-collapse equality `Wmain⟨3⟩ = Wmain⟨4⟩`, derive four containments
linking source leaves `{0,1}` to target leaves `{5,6}` via
γ-then-collapse-then-core4. Port of `d5tilde_gamma_containment_F` with
the extra identity-edge collapse threaded in. -/
theorem d6tilde_gamma_containment_F
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 7 Q d6tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d6tildeRep_kQ F Q hOrient m).obj v))
    (hMain_02 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hMain_12 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨1, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hMain_23 : ∀ (x : Fin (2 * (m + 1)) → F), x ∈ Wmain ⟨2, by omega⟩ →
        d5tildeGamma_F F m x ∈ Wmain ⟨3, by omega⟩)
    (hcol_main : Wmain ⟨3, by omega⟩ = Wmain ⟨4, by omega⟩)
    (hMain_54 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨5, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨4, by omega⟩)
    (hMain_64 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨6, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨4, by omega⟩)
    (hOther_54 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨5, by omega⟩ →
        starEmbed1_F F m x ∈ Wother ⟨4, by omega⟩)
    (hOther_64 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨6, by omega⟩ →
        starEmbed2_F F m x ∈ Wother ⟨4, by omega⟩)
    (hc : ∀ v, IsCompl (Wmain v) (Wother v)) :
    (∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
      x ∈ Wmain ⟨5, by omega⟩) ∧
    (∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
      x ∈ Wmain ⟨6, by omega⟩) ∧
    (∀ (y : Fin (m + 1) → F), y ∈ Wmain ⟨1, by omega⟩ →
      y ∈ Wmain ⟨5, by omega⟩) ∧
    (∀ (y : Fin (m + 1) → F), y ∈ Wmain ⟨1, by omega⟩ →
      nilpotentShiftLinGen F m y ∈ Wmain ⟨6, by omega⟩) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have he1 := hMain_02 x hx
    have hgamma := hMain_23 (starEmbed1_F F m x) he1
    rw [gamma_from_embed1_F] at hgamma
    have hgamma4 := hcol_main ▸ hgamma
    exact (d6tilde_core4_F F Q hOrient m Wmain Wother hMain_54 hMain_64
      hOther_54 hOther_64 hc x x hgamma4).1
  · have he1 := hMain_02 x hx
    have hgamma := hMain_23 (starEmbed1_F F m x) he1
    rw [gamma_from_embed1_F] at hgamma
    have hgamma4 := hcol_main ▸ hgamma
    exact (d6tilde_core4_F F Q hOrient m Wmain Wother hMain_54 hMain_64
      hOther_54 hOther_64 hc x x hgamma4).2
  · have he2 := hMain_12 y hy
    have hgamma := hMain_23 (starEmbed2_F F m y) he2
    rw [gamma_from_embed2_F] at hgamma
    have hgamma4 := hcol_main ▸ hgamma
    exact (d6tilde_core4_F F Q hOrient m Wmain Wother hMain_54 hMain_64
      hOther_54 hOther_64 hc y (nilpotentShiftLinGen F m y) hgamma4).1
  · have he2 := hMain_12 y hy
    have hgamma := hMain_23 (starEmbed2_F F m y) he2
    rw [gamma_from_embed2_F] at hgamma
    have hgamma4 := hcol_main ▸ hgamma
    exact (d6tilde_core4_F F Q hOrient m Wmain Wother hMain_54 hMain_64
      hOther_54 hOther_64 hc y (nilpotentShiftLinGen F m y) hgamma4).2

/-! ## Section 4d: Leaf equalities (#4527 sub-A: canonical branch)

The leaf-equality theorem derives `W₁⟨0⟩ = W₁⟨1⟩ = W₁⟨5⟩ = W₁⟨6⟩` for any
complementary invariant pair. The internal edge `3-4` is handled
orientation-independently by `d6tildeRep_kQ_chain_collapse`, so the case
analysis only branches on the five leaf/γ edges (`0-2, 1-2, 2-3, 5-4,
6-4`) — the same 32-branch tree as d5tilde. The all-canonical branch is
proven inline by mirroring `d5tildeRep_kQ_leaf_equalities`; the remaining
31 non-canonical branches are tracked by #4527 sub-B. -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- For any orientation `Q` of `d6tildeAdj` and any complementary invariant
submodule pair `(W₁, W₂)` of `d6tildeRep_kQ F Q hOrient m`, the leaf
vertices `0, 1, 5, 6` carry equal `W₁`-subspaces.

**Proof body partially deferred** (#4527 sub-B). The all-canonical
orientation branch (`0→2, 1→2, 2→3, 5→4, 6→4`, with `3-4` collapsed) is
proven inline; the remaining 31 leaf/γ orientation branches are `sorry`. -/
theorem d6tildeRep_kQ_leaf_equalities
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 7 Q d6tildeAdj)
    (m : ℕ)
    (W₁ W₂ : ∀ v, Submodule F ((d6tildeRep_kQ F Q hOrient m).obj v))
    (hW₁_inv : ∀ {a b : Fin 7} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₁ a, (d6tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₁ b)
    (hW₂_inv : ∀ {a b : Fin 7} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₂ a, (d6tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₂ b)
    (hcompl : ∀ v, IsCompl (W₁ v) (W₂ v)) :
    W₁ ⟨0, by omega⟩ = W₁ ⟨1, by omega⟩ ∧
    W₁ ⟨0, by omega⟩ = W₁ ⟨5, by omega⟩ ∧
    W₁ ⟨0, by omega⟩ = W₁ ⟨6, by omega⟩ := by
  letI := Q
  -- Internal edge 3-4 collapses orientation-independently.
  obtain ⟨hcol₁, hcol₂⟩ :=
    d6tildeRep_kQ_chain_collapse F Q hOrient m W₁ W₂ hW₁_inv hW₂_inv hcompl
  have hOrient_edge := hOrient.2.1
  have h02 : d6tildeAdj ⟨0, by omega⟩ ⟨2, by omega⟩ = 1 := by simp [d6tildeAdj]
  have h12 : d6tildeAdj ⟨1, by omega⟩ ⟨2, by omega⟩ = 1 := by simp [d6tildeAdj]
  have h23 : d6tildeAdj ⟨2, by omega⟩ ⟨3, by omega⟩ = 1 := by simp [d6tildeAdj]
  have h54 : d6tildeAdj ⟨5, by omega⟩ ⟨4, by omega⟩ = 1 := by simp [d6tildeAdj]
  have h64 : d6tildeAdj ⟨6, by omega⟩ ⟨4, by omega⟩ = 1 := by simp [d6tildeAdj]
  rcases hOrient_edge ⟨0, by omega⟩ ⟨2, by omega⟩ h02 with hQ02 | hQ02
  · obtain ⟨a02⟩ := hQ02
    rcases hOrient_edge ⟨1, by omega⟩ ⟨2, by omega⟩ h12 with hQ12 | hQ12
    · obtain ⟨a12⟩ := hQ12
      rcases hOrient_edge ⟨2, by omega⟩ ⟨3, by omega⟩ h23 with hQ23 | hQ23
      · obtain ⟨a23⟩ := hQ23
        rcases hOrient_edge ⟨5, by omega⟩ ⟨4, by omega⟩ h54 with hQ54 | hQ54
        · obtain ⟨a54⟩ := hQ54
          rcases hOrient_edge ⟨6, by omega⟩ ⟨4, by omega⟩ h64 with hQ64 | hQ64
          · obtain ⟨a64⟩ := hQ64
            -- ALL CANONICAL (leaf/γ edges): 0→2, 1→2, 2→3, 5→4, 6→4.
            have hW₁_02 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨0, by omega⟩) :
                starEmbed1_F F m x ∈ W₁ ⟨2, by omega⟩ := by
              have h := hW₁_inv a02 x hx
              simp only [d6tildeRep_kQ, d6tildeRepMap_kQ] at h; exact h
            have hW₁_12 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨1, by omega⟩) :
                starEmbed2_F F m x ∈ W₁ ⟨2, by omega⟩ := by
              have h := hW₁_inv a12 x hx
              simp only [d6tildeRep_kQ, d6tildeRepMap_kQ] at h; exact h
            have hW₁_23 (x : Fin (2 * (m + 1)) → F) (hx : x ∈ W₁ ⟨2, by omega⟩) :
                d5tildeGamma_F F m x ∈ W₁ ⟨3, by omega⟩ := by
              have h := hW₁_inv a23 x hx
              simp only [d6tildeRep_kQ, d6tildeRepMap_kQ] at h; exact h
            have hW₁_54 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨5, by omega⟩) :
                starEmbed1_F F m x ∈ W₁ ⟨4, by omega⟩ := by
              have h := hW₁_inv a54 x hx
              simp only [d6tildeRep_kQ, d6tildeRepMap_kQ] at h; exact h
            have hW₁_64 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨6, by omega⟩) :
                starEmbed2_F F m x ∈ W₁ ⟨4, by omega⟩ := by
              have h := hW₁_inv a64 x hx
              simp only [d6tildeRep_kQ, d6tildeRepMap_kQ] at h; exact h
            have hW₂_02 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨0, by omega⟩) :
                starEmbed1_F F m x ∈ W₂ ⟨2, by omega⟩ := by
              have h := hW₂_inv a02 x hx
              simp only [d6tildeRep_kQ, d6tildeRepMap_kQ] at h; exact h
            have hW₂_12 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨1, by omega⟩) :
                starEmbed2_F F m x ∈ W₂ ⟨2, by omega⟩ := by
              have h := hW₂_inv a12 x hx
              simp only [d6tildeRep_kQ, d6tildeRepMap_kQ] at h; exact h
            have hW₂_23 (x : Fin (2 * (m + 1)) → F) (hx : x ∈ W₂ ⟨2, by omega⟩) :
                d5tildeGamma_F F m x ∈ W₂ ⟨3, by omega⟩ := by
              have h := hW₂_inv a23 x hx
              simp only [d6tildeRep_kQ, d6tildeRepMap_kQ] at h; exact h
            have hW₂_54 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨5, by omega⟩) :
                starEmbed1_F F m x ∈ W₂ ⟨4, by omega⟩ := by
              have h := hW₂_inv a54 x hx
              simp only [d6tildeRep_kQ, d6tildeRepMap_kQ] at h; exact h
            have hW₂_64 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨6, by omega⟩) :
                starEmbed2_F F m x ∈ W₂ ⟨4, by omega⟩ := by
              have h := hW₂_inv a64 x hx
              simp only [d6tildeRep_kQ, d6tildeRepMap_kQ] at h; exact h
            obtain ⟨h05, h06, h15, _hN16⟩ :=
              d6tilde_gamma_containment_F F Q hOrient m W₁ W₂
                hW₁_02 hW₁_12 hW₁_23 hcol₁ hW₁_54 hW₁_64 hW₂_54 hW₂_64 hcompl
            obtain ⟨h05', h06', h15', _hN16'⟩ :=
              d6tilde_gamma_containment_F F Q hOrient m W₂ W₁
                hW₂_02 hW₂_12 hW₂_23 hcol₂ hW₂_54 hW₂_64 hW₁_54 hW₁_64
                (fun v => (hcompl v).symm)
            have heq05 : W₁ ⟨0, by omega⟩ = W₁ ⟨5, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨0, by omega⟩) (W₂ ⟨0, by omega⟩)
                (W₁ ⟨5, by omega⟩) (W₂ ⟨5, by omega⟩)
                (hcompl ⟨0, by omega⟩) (hcompl ⟨5, by omega⟩) h05 h05').1
            have heq06 : W₁ ⟨0, by omega⟩ = W₁ ⟨6, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨0, by omega⟩) (W₂ ⟨0, by omega⟩)
                (W₁ ⟨6, by omega⟩) (W₂ ⟨6, by omega⟩)
                (hcompl ⟨0, by omega⟩) (hcompl ⟨6, by omega⟩) h06 h06').1
            have heq15 : W₁ ⟨1, by omega⟩ = W₁ ⟨5, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨1, by omega⟩) (W₂ ⟨1, by omega⟩)
                (W₁ ⟨5, by omega⟩) (W₂ ⟨5, by omega⟩)
                (hcompl ⟨1, by omega⟩) (hcompl ⟨5, by omega⟩) h15 h15').1
            have heq01 : W₁ ⟨0, by omega⟩ = W₁ ⟨1, by omega⟩ := heq05.trans heq15.symm
            exact ⟨heq01, heq05, heq06⟩
          · -- e64 reversed (4→6): tracked by #4527 sub-B
            sorry
        · -- e54 reversed (4→5): tracked by #4527 sub-B
          sorry
      · -- e23 reversed (3→2): tracked by #4527 sub-B
        sorry
    · -- e12 reversed (2→1): tracked by #4527 sub-B
      sorry
  · -- e02 reversed (2→0): tracked by #4527 sub-B
    sorry

/-! ## Section 5: Indecomposability (deferred sorry)

The body of the indecomposability proof is deferred to a follow-up
issue, mirroring the precedent of `d7tildeRep_kQ_isIndecomposable`
(`FieldGenericD7Tilde.lean:247`, tracked by #2967) and
`d5tildeRep_kQ_isIndecomposable` (`FieldGenericD5Tilde.lean:980`,
tracked by #2834). The per-(F, Q) infinite-type theorem below
transitively depends on this sorry.
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic indecomposability of `d6tildeRep_kQ`.

The proof body is deferred to a follow-up issue (the D̃₆ analogue of
`d7tildeRep_kQ_isIndecomposable`, `FieldGenericD7Tilde.lean:247`, which
is itself sorry-deferred). Closing this sorry requires F-generic
versions of the leaf-subspace equalities used by the ℂ-specific
universal proof, parameterised across each of the six possible arrow
directions; the d5tilde / d7tilde precedents show this is a
multi-hundred-line construction. The consumer
`d6tilde_not_finite_type_per_kQ` carries this sorry transitively. -/
theorem d6tildeRep_kQ_isIndecomposable
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 7 Q d6tildeAdj)
    (m : ℕ) :
    (d6tildeRep_kQ F Q hOrient m).IsIndecomposable := by
  sorry

/-! ## Section 6: Per-(F, Q) infinite-type theorem -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) D̃₆ infinite-type theorem: for any
algebraically closed field `F` and any orientation `Q` of `d6tildeAdj`,
the set of dimension vectors of indecomposable representations is
infinite. Mirrors the proof shape of `d7tilde_not_finite_type_per_kQ`
(`FieldGenericD7Tilde.lean:272`) and `d5tilde_not_finite_type_per_kQ`
(`FieldGenericD5Tilde.lean:999`).

Injectivity comes from vertex `0`, where `d6tildeDim m 0 = m + 1`.

This theorem carries no direct `sorry`, but transitively depends on
`d6tildeRep_kQ_isIndecomposable`, whose proof body is deferred — see
its docstring. -/
theorem d6tilde_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 7 Q d6tildeAdj) :
    ¬ Set.Finite
      {d : Fin 7 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 7) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ, d6tildeDim m ∈
      {d : Fin 7 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 7) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨d6tildeRep_kQ F Q hOrient m,
      d6tildeRep_kQ_isIndecomposable F Q hOrient m,
      d6tildeRep_kQ_dimVec F Q hOrient m⟩
  have hinj : Function.Injective (d6tildeDim : ℕ → Fin 7 → ℕ) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨0, by omega⟩
    have hnot : ¬(2 ≤ (⟨0, by omega⟩ : Fin 7).val ∧
      (⟨0, by omega⟩ : Fin 7).val ≤ 4) := by simp
    simp only [d6tildeDim, hnot, ite_false] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section 7: Embedding D̃₆ into a host tree (per-(F, Q) helper)

Mirrors `embed_d7tilde_in_tree_per_kQ` (`FieldGenericD7Tilde.lean:323`)
for the D̃₆ shape: two non-adjacent degree-3 branch points (`p`, `s`)
each with two leaves (`a, b` for `p`; `u, v` for `s`), connected by an
internal length-2 chain `p – q – s`. Given the six edges, the `p – s`
non-edge, and the distinctness hypotheses, this helper derives the
remaining 15 non-edges of the 21-pair adjacency lattice and dispatches
via `subgraph_infinite_type_transfer_per_kQ` and
`d6tilde_not_finite_type_per_kQ`. -/

set_option maxHeartbeats 800000 in
-- The 21-pair adjacency lattice drives a sizeable `linarith` over the 49
-- `fin_cases` of `hembed`, exceeding the default 200k heartbeat limit.
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) embedding of D̃₆ into a host acyclic adjacency matrix.

Vertex map (matching `d6tildeAdj`):
`0 → a, 1 → b, 2 → p, 3 → q, 4 → s, 5 → u, 6 → v`. The six D̃₆ edges
are: `a-p, b-p, p-q, q-s, s-u, s-v`; vertices `p` and `s` are the two
non-adjacent degree-3 branch points connected by the single internal
vertex `q`. -/
theorem embed_d6tilde_in_tree_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (a b p q s u v : Fin n)
    (hap : adj p a = 1) (hbp : adj p b = 1) (hpq : adj p q = 1)
    (hqs : adj q s = 1) (hsu : adj s u = 1) (hsv : adj s v = 1)
    (hps : adj p s = 0)
    (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (huv : u ≠ v) (hqu : q ≠ u) (hqv : q ≠ v)
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
  have hqs_ne : q ≠ s := ne_of_adj' q s hqs
  have hsu_ne : s ≠ u := ne_of_adj' s u hsu
  have hsv_ne : s ≠ v := ne_of_adj' s v hsv
  -- Reversed edges.
  have hap' : adj a p = 1 := (adj_comm a p).trans hap
  have hbp' : adj b p = 1 := (adj_comm b p).trans hbp
  have hpq' : adj q p = 1 := (adj_comm q p).trans hpq
  have hqs' : adj s q = 1 := (adj_comm s q).trans hqs
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
  -- Triangle non-edges via `acyclic_no_triangle` (6 distance-2 non-edges).
  have hab0 : adj a b = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p a b hab hap_ne hbp_ne hap hbp
  have haq0 : adj a q = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p a q haq hap_ne hpq_ne.symm hap hpq
  have hbq0 : adj b q = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p b q hbq hbp_ne hpq_ne.symm hbp hpq
  have huv0 : adj u v = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic s u v huv hsu_ne.symm hsv_ne.symm hsu hsv
  have hqu0 : adj q u = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic s q u hqu hqs_ne hsu_ne.symm hqs' hsu
  have hqv0 : adj q v = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic s q v hqv hqs_ne hsv_ne.symm hqs' hsv
  -- Apex q: p-s (the two branch points, distance 2 via q).
  have hps0 : adj p s = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q p s hps_ne hpq_ne hqs_ne.symm hpq' hqs
  -- Cross-side distinctness derived from distance-2 non-edges.
  have has_ne : a ≠ s := by intro h; rw [h] at hap; linarith [hps]
  have hbs_ne : b ≠ s := by intro h; rw [h] at hbp; linarith [hps]
  have hpu_ne : p ≠ u := by intro h; rw [h] at hps; linarith [hsu']
  have hpv_ne : p ≠ v := by intro h; rw [h] at hps; linarith [hsv']
  -- Distance-3 non-edges (4-vertex paths).
  have has0 : adj a s = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [a, p, q, s] (by simp)
      (path_nodup4 _ _ _ _ hap_ne haq has_ne hpq_ne hps_ne hqs_ne)
      (path_edges4 _ _ _ _ hap' hpq hqs)
    simpa using h
  have hbs0 : adj b s = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [b, p, q, s] (by simp)
      (path_nodup4 _ _ _ _ hbp_ne hbq hbs_ne hpq_ne hps_ne hqs_ne)
      (path_edges4 _ _ _ _ hbp' hpq hqs)
    simpa using h
  have hpu0 : adj p u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [p, q, s, u] (by simp)
      (path_nodup4 _ _ _ _ hpq_ne hps_ne hpu_ne hqs_ne hqu hsu_ne)
      (path_edges4 _ _ _ _ hpq hqs hsu)
    simpa using h
  have hpv0 : adj p v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [p, q, s, v] (by simp)
      (path_nodup4 _ _ _ _ hpq_ne hps_ne hpv_ne hqs_ne hqv hsv_ne)
      (path_edges4 _ _ _ _ hpq hqs hsv)
    simpa using h
  -- Cross-leaf distinctness (from distance-3 non-edges).
  have hau_ne : a ≠ u := by intro h; rw [h] at hap; linarith [hpu0]
  have hav_ne : a ≠ v := by intro h; rw [h] at hap; linarith [hpv0]
  have hbu_ne : b ≠ u := by intro h; rw [h] at hbp; linarith [hpu0]
  have hbv_ne : b ≠ v := by intro h; rw [h] at hbp; linarith [hpv0]
  -- Distance-4 non-edges (5-vertex paths).
  have hau0 : adj a u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [a, p, q, s, u] (by simp)
      (path_nodup5 _ _ _ _ _ hap_ne haq has_ne hau_ne
        hpq_ne hps_ne hpu_ne hqs_ne hqu hsu_ne)
      (path_edges5 _ _ _ _ _ hap' hpq hqs hsu)
    simpa using h
  have hav0 : adj a v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [a, p, q, s, v] (by simp)
      (path_nodup5 _ _ _ _ _ hap_ne haq has_ne hav_ne
        hpq_ne hps_ne hpv_ne hqs_ne hqv hsv_ne)
      (path_edges5 _ _ _ _ _ hap' hpq hqs hsv)
    simpa using h
  have hbu0 : adj b u = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [b, p, q, s, u] (by simp)
      (path_nodup5 _ _ _ _ _ hbp_ne hbq hbs_ne hbu_ne
        hpq_ne hps_ne hpu_ne hqs_ne hqu hsu_ne)
      (path_edges5 _ _ _ _ _ hbp' hpq hqs hsu)
    simpa using h
  have hbv0 : adj b v = 0 := by
    rw [adj_comm]
    have h := acyclic_path_nonadj adj hsymm h01 h_acyclic [b, p, q, s, v] (by simp)
      (path_nodup5 _ _ _ _ _ hbp_ne hbq hbs_ne hbv_ne
        hpq_ne hps_ne hpv_ne hqs_ne hqv hsv_ne)
      (path_edges5 _ _ _ _ _ hbp' hpq hqs hsv)
    simpa using h
  -- Construct φ : Fin 7 ↪ Fin n.
  let φ_fun : Fin 7 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => a  | ⟨1, _⟩ => b  | ⟨2, _⟩ => p  | ⟨3, _⟩ => q
    | ⟨4, _⟩ => s  | ⟨5, _⟩ => u  | ⟨6, _⟩ => v
  have φ_inj : Function.Injective φ_fun := by
    intro i j hij; simp only [φ_fun] at hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exact absurd hij ‹_›)
      | (exact absurd hij.symm ‹_›)
  let φ : Fin 7 ↪ Fin n := ⟨φ_fun, φ_inj⟩
  have hembed : ∀ i j, d6tildeAdj i j = adj (φ i) (φ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [d6tildeAdj, φ, φ_fun] <;> norm_num <;>
      linarith [hdiag a, hdiag b, hdiag p, hdiag q, hdiag s, hdiag u, hdiag v,
        hap, hbp, hpq, hqs, hsu, hsv,
        hap', hbp', hpq', hqs', hsu', hsv',
        hps, hps',
        hab0, haq0, hbq0, huv0, hqu0, hqv0, hps0,
        adj_comm a b, adj_comm a q, adj_comm b q, adj_comm u v,
        adj_comm q u, adj_comm q v, adj_comm p s,
        has0, hbs0, hpu0, hpv0,
        adj_comm a s, adj_comm b s, adj_comm p u, adj_comm p v,
        hau0, hav0, hbu0, hbv0,
        adj_comm a u, adj_comm a v, adj_comm b u, adj_comm b v]
  exact subgraph_infinite_type_transfer_per_kQ φ F Q
    (d6tilde_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

end Etingof
