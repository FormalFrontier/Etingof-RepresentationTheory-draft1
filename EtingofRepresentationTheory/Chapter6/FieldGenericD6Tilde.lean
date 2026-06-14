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
