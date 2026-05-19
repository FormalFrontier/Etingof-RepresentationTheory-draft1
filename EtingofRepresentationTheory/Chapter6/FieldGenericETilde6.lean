import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericStar

/-!
# Orientation-Generic Ẽ₆ Construction (Sub A of #2791)

F-generic, orientation-generic version of the Ẽ₆ representation
`etilde6v2Rep` from `InfiniteTypeConstructions.lean`. This file provides
the construction `etilde6Rep_kQ` and its dimension-vector lemma; the
indecomposability proof and the final per-(F, Q) infinite-type theorem
are deferred to Sub B (issue #2807), which inherits the wave-54
framework-wall question flagged on the ℂ-specific source
`etilde6v2Rep_isIndecomposable` (`InfiniteTypeConstructions.lean:3331`).

The orientation-generic rep needs direction-aware maps for each of the
six edges of `etilde6Adj`. For the canonical mixed orientation
`etilde6v2Quiver` (2→1→0, 0→3←4, 6→5→0) the maps are the F-generic
analogues of `embed2to3_AB`, `embed2to3_CA`, `etilde6v2Gamma`,
`starEmbed1`, `starEmbedNilp`. For the reversed direction of each edge
the rep needs an appropriately-typed map in the other direction; the
choices below are left inverses (for embeddings) or a right section
(for `etilde6Gamma_F`, which is not injective). Sub B may revisit the
section choice if it turns out indecomposability requires a different
one.

See the "Naming conventions" section of
`Chapter6/FieldGenericInfiniteType.lean` for the meaning of the
`_F` / `_kQ` / `_per_kQ` suffixes used throughout this file.
-/

open scoped Matrix

namespace Etingof

/-! ## Section 0: Shared prefix-block primitives

Two-parameter families that subsume the prefix-block embed / projection
pairs used in both Ẽ₆ and Ẽ₇. The Ẽ₆ rep uses `prefixBlockEmbed_F 2 3`
(zero-extension `F^{2(m+1)} → F^{3(m+1)}`) and `prefixBlockProj_F 2 3 _`;
the Ẽ₇ rep additionally uses the `3 → 4` instances.
-/

/-- F-generic zero-extension `F^{a(m+1)} → F^{b(m+1)}` along the first
`a` blocks: `x ↦ (x, 0, …, 0)`. When `a > b` the output is zero
everywhere (no values fit), but the typical use case has `a ≤ b`. -/
noncomputable def prefixBlockEmbed_F (F : Type) [Field F]
    (a b m : ℕ) :
    (Fin (a * (m + 1)) → F) →ₗ[F] (Fin (b * (m + 1)) → F) where
  toFun x i := if h : i.val < a * (m + 1) then x ⟨i.val, h⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- F-generic first-`a`-blocks projection `F^{b(m+1)} → F^{a(m+1)}`:
`w ↦ (w₀, …, w_{a(m+1)-1})`. Requires `a ≤ b` so the domain index
remains in range. -/
noncomputable def prefixBlockProj_F (F : Type) [Field F]
    (a b m : ℕ) (hab : a ≤ b) :
    (Fin (b * (m + 1)) → F) →ₗ[F] (Fin (a * (m + 1)) → F) where
  toFun w i :=
    w ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.mul_le_mul_right _ hab)⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-! ## Section 1: F-generic forward maps for Ẽ₆

F-generic versions of the ℂ-specific maps used in `etilde6v2RepMap`
(`InfiniteTypeConstructions.lean:3282-3294`). The bodies are
copy-paste of the ℂ versions with `ℂ` replaced by `F`.
-/

/-- F-generic embedding from a 2-block space into blocks (C, _, A) of a
3-block space: `(a, b) ↦ (b, 0, a)` (first component to block C, second
to block A). Mirror of `embed2to3_CA`
(`InfiniteTypeConstructions.lean:1944`). -/
noncomputable def embed2to3_CA_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (3 * (m + 1)) → F) where
  toFun x i :=
    if h : i.val < m + 1 then
      x ⟨i.val + (m + 1), by omega⟩
    else if h2 : 2 * (m + 1) ≤ i.val then
      (if h3 : i.val - 2 * (m + 1) < m + 1 then x ⟨i.val - 2 * (m + 1), by omega⟩ else 0)
    else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- F-generic coupling map `Γ : F^{3(m+1)} → F^{2(m+1)}` for the Ẽ₆ mixed
orientation: `Γ(a, b, c) = (a + b, a + Nc)`, where `a, b, c` are blocks of
size `m+1` and `N` is the nilpotent shift. Mirror of `etilde6v2Gamma`
(`InfiniteTypeConstructions.lean:3266`). -/
noncomputable def etilde6Gamma_F (F : Type) [Field F] (m : ℕ) :
    (Fin (3 * (m + 1)) → F) →ₗ[F] (Fin (2 * (m + 1)) → F) where
  toFun w i :=
    if h : i.val < m + 1 then
      w ⟨i.val, by omega⟩ + w ⟨m + 1 + i.val, by omega⟩
    else
      w ⟨i.val - (m + 1), by omega⟩ +
        (if h2 : (i.val - (m + 1)) + 1 < m + 1 then
          w ⟨2 * (m + 1) + (i.val - (m + 1)) + 1, by omega⟩ else 0)
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-! ## Section 2: F-generic reverse maps for Ẽ₆

For an arbitrary orientation `Q` of `etilde6Adj`, each edge may point the
opposite way from `etilde6v2Quiver`. The reverse maps below are linear
maps in the opposite direction:

- The reverse of `prefixBlockEmbed_F 2 3` is `prefixBlockProj_F 2 3 _`
  (defined in Section 0), sending `(a, b, c) ↦ (a, b)`.
- `embed2to3_CA_reverse_F`: left inverse of `embed2to3_CA_F`, sending
  `(a, b, c) ↦ (c, a)` (block C to first half, block A to second half).
- `etilde6GammaInv_F`: right section of `etilde6Gamma_F`. The map
  `etilde6Gamma_F` is not injective (3(m+1)-dim domain into 2(m+1)-dim
  codomain), so it has no left inverse — we provide a right section
  `(u, v) ↦ (v, u - v, 0)`, which satisfies
  `etilde6Gamma_F ∘ etilde6GammaInv_F = id`.
- `etilde6LeafProj_F`: first-half projection `(a, b) ↦ a`. Left inverse
  of both `starEmbed1_F` (since `starEmbed1_F x = (x, 0)`) and
  `starEmbedNilp_F` (since `starEmbedNilp_F x = (x, Nx)`). Used for the
  three reversed-leaf-edge cases.
-/

/-- Reverse map for the `embed2to3_CA_F` edge: `(a', b', c') ↦ (c', a')`,
sending block C to the first half and block A to the second half. Left
inverse of `embed2to3_CA_F`. -/
noncomputable def embed2to3_CA_reverse_F (F : Type) [Field F] (m : ℕ) :
    (Fin (3 * (m + 1)) → F) →ₗ[F] (Fin (2 * (m + 1)) → F) where
  toFun w i :=
    if h : i.val < m + 1 then
      w ⟨2 * (m + 1) + i.val, by omega⟩
    else
      w ⟨i.val - (m + 1), by omega⟩
  map_add' _ _ := by ext; simp only [Pi.add_apply]; split_ifs <;> rfl
  map_smul' _ _ := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> rfl

/-- A right section of `etilde6Gamma_F`: `(u, v) ↦ (v, u - v, 0)`. The
choice is motivated by `etilde6Gamma_F (v, u-v, 0) = (v + (u-v), v + N(0))
= (u, v)` (for the first half of the output) and `= a[m] = v[m]` at the
last position (since `N(0) = 0`). -/
noncomputable def etilde6GammaInv_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (3 * (m + 1)) → F) where
  toFun w i :=
    if h : i.val < m + 1 then
      w ⟨m + 1 + i.val, by omega⟩
    else if h2 : i.val < 2 * (m + 1) then
      w ⟨i.val - (m + 1), by omega⟩ - w ⟨m + 1 + (i.val - (m + 1)), by omega⟩
    else
      0
  map_add' _ _ := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' _ _ := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- First-half projection `(a, b) ↦ a` for `F^{2(m+1)} → F^{m+1}`. Used as
the reverse map for the three leaf-edge cases of Ẽ₆ ({1,2}, {3,4}, {5,6}).
A left inverse of `starEmbed1_F` (`(x, 0) ↦ x`) and of `starEmbedNilp_F`
(`(x, Nx) ↦ x`). -/
noncomputable def etilde6LeafProj_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) where
  toFun w i := w ⟨i.val, by omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-! ## Section 3: Orientation-generic Ẽ₆ representation

The map function is a match on `(a.val, b.val)` mirroring `etilde6v2RepMap`
(`InfiniteTypeConstructions.lean:3282`) for the canonical six (a, b)
pairs, plus the six reversed pairs using the maps from Section 2. Outside
those 12 edge pairs, the map is `0` (these arrows do not exist in any
orientation of `etilde6Adj`).
-/

/-- Direction-aware match-based map function for the orientation-generic
Ẽ₆ representation. Returns the same linear maps as
`etilde6v2RepMap` for the canonical orientation, plus the reverse maps
from Section 2 when the arrow is in the reversed direction. -/
private noncomputable def etilde6RepMap_kQ (F : Type) [Field F] (m : ℕ) (a b : Fin 7) :
    (Fin (etilde6Dim m a) → F) →ₗ[F] (Fin (etilde6Dim m b) → F) :=
  match a, b with
  -- Edge {1, 2}
  | ⟨2, _⟩, ⟨1, _⟩ => starEmbed1_F F m
  | ⟨1, _⟩, ⟨2, _⟩ => etilde6LeafProj_F F m
  -- Edge {0, 1}
  | ⟨1, _⟩, ⟨0, _⟩ => prefixBlockEmbed_F F 2 3 m
  | ⟨0, _⟩, ⟨1, _⟩ => prefixBlockProj_F F 2 3 m (by omega)
  -- Edge {0, 3}
  | ⟨0, _⟩, ⟨3, _⟩ => etilde6Gamma_F F m
  | ⟨3, _⟩, ⟨0, _⟩ => etilde6GammaInv_F F m
  -- Edge {3, 4}
  | ⟨4, _⟩, ⟨3, _⟩ => starEmbed1_F F m
  | ⟨3, _⟩, ⟨4, _⟩ => etilde6LeafProj_F F m
  -- Edge {0, 5}
  | ⟨5, _⟩, ⟨0, _⟩ => embed2to3_CA_F F m
  | ⟨0, _⟩, ⟨5, _⟩ => embed2to3_CA_reverse_F F m
  -- Edge {5, 6}
  | ⟨6, _⟩, ⟨5, _⟩ => starEmbedNilp_F F m
  | ⟨5, _⟩, ⟨6, _⟩ => etilde6LeafProj_F F m
  -- Non-edge or impossible (ruled out by `hOrient`); placeholder
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic Ẽ₆ (= T_{2,2,2}) representation over an arbitrary
field `F` with arbitrary orientation `Q` of `etilde6Adj`. Dimension vector
follows `etilde6Dim`: vertex 0 has dim `3(m+1)`, vertices 1/3/5 have dim
`2(m+1)`, vertices 2/4/6 have dim `m+1`.

The map on an arrow `e : Q.Hom a b` depends only on the underlying
unordered edge `{a, b}` and the direction `a → b`. Each of the six edges
of `etilde6Adj` contributes one canonical map (matching `etilde6v2RepMap`)
and one reverse map (defined in Section 2). The orientation hypothesis
`hOrient` is not used by the construction itself; it is recorded so that
downstream lemmas (notably the indecomposability proof planned for
Sub B #2807) can pattern-match on which arrows exist. -/
noncomputable def etilde6Rep_kQ
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (_hOrient : @Etingof.IsOrientationOf 7 Q etilde6Adj)
    (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin 7) _ Q := by
  letI := Q
  exact {
    obj := fun v => Fin (etilde6Dim m v) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => etilde6RepMap_kQ F m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The orientation-generic Ẽ₆ rep has the expected dimension vector
`etilde6Dim m` at each vertex. -/
theorem etilde6Rep_kQ_dimVec
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 7 Q etilde6Adj)
    (m : ℕ) (v : Fin 7) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin 7) _ Q
      (etilde6Rep_kQ F Q hOrient m) v ≃ₗ[F] (Fin (etilde6Dim m v) → F)) :=
  ⟨LinearEquiv.refl F _⟩

/-! ## Section 4: Indecomposability (path b: inherits the wave-54 framework wall)

The ℂ-specific source `etilde6v2Rep_isIndecomposable`
(`InfiniteTypeConstructions.lean:3331`) is `sorry`'d due to the wave-54
framework wall: the single-nilpotent-twist construction is decomposable for
every `m ≥ 1` because the N-twist only covers the `⟨e₀, …, e_{m-1}⟩`
sub-block of its target, leaving the `e_m` direction free to peel off as a
1-dim summand at the center. See
`progress/indecomposability-framework-investigation.md` (Section 1) for the
explicit counter-example (verified at `etilde6v2Rep 1`).

Per #2807, we follow path (b): mirror the ℂ-specific stub at the
orientation-generic level, carrying the same `sorry` with a docstring
tying it to the framework wall. The final per-(F, Q) theorem
`etilde6_not_finite_type_per_kQ` below depends transitively on this
sorry, exactly as the ℂ-specific `etilde6_not_finite_type` depends on
`etilde6v2Rep_isIndecomposable`.
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic indecomposability of `etilde6Rep_kQ`.

**Framework wall (wave 54)**: this theorem inherits the same wall that
blocks the ℂ-specific source `etilde6v2Rep_isIndecomposable`
(`InfiniteTypeConstructions.lean:3331`): the single-nilpotent-twist
construction is provably decomposable for every `m ≥ 1` (the N-twist only
covers the `⟨e₀, …, e_{m-1}⟩` sub-block of its target, leaving `e_m`
free). See `progress/indecomposability-framework-investigation.md`
(Section 1) for the explicit counter-example and Section 5 Option B for a
sketched stronger construction. The `1 ≤ m` hypothesis is required even
in the planned proof — for `m = 0`, `nilpotentShiftLin 0 = 0`, the
nilpotent twist disappears and the representation is provably
decomposable (see the comment at
`InfiniteTypeConstructions.lean:3322-3328`).

The current proof is a `sorry`; the consumer `etilde6_not_finite_type_per_kQ`
inherits this dependency. This is path (b) of #2807 — a follow-up
issue will revisit when the framework question is resolved. -/
theorem etilde6Rep_kQ_isIndecomposable
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 7 Q etilde6Adj)
    (m : ℕ) (hm : 1 ≤ m) :
    (etilde6Rep_kQ F Q hOrient m).IsIndecomposable := by
  let _ := hm  -- retain `hm` in the signature for the future proof
  sorry

/-! ## Section 5: Per-(F, Q) infinite-type theorem -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) version of `etilde6_not_finite_type`: for any
algebraically closed field `F` and any orientation `Q` of `etilde6Adj`,
the set of dimension vectors of indecomposable representations is
infinite.

Mirrors the proof of `etilde6_not_finite_type`
(`InfiniteTypeConstructions.lean:3354`): we range over `m + 1` (not `m`)
because `etilde6Rep_kQ_isIndecomposable` requires `1 ≤ m` (the `m = 0`
case is provably decomposable). Injectivity comes from vertex `0`, where
`etilde6Dim m 0 = 3 * (m + 1)`.

This theorem carries no direct `sorry`, but transitively depends on
`etilde6Rep_kQ_isIndecomposable`, which inherits the wave-54 framework
wall — see its docstring. -/
theorem etilde6_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 7))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 7) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 7 Q etilde6Adj) :
    ¬ Set.Finite
      {d : Fin 7 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 7) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ, (fun v : Fin 7 => etilde6Dim (m + 1) v) ∈
      {d : Fin 7 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 7) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨etilde6Rep_kQ F Q hOrient (m + 1),
      etilde6Rep_kQ_isIndecomposable F Q hOrient (m + 1) (Nat.succ_le_succ m.zero_le),
      etilde6Rep_kQ_dimVec F Q hOrient (m + 1)⟩
  have hinj : Function.Injective (fun m : ℕ => fun v : Fin 7 => etilde6Dim (m + 1) v) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨0, by omega⟩
    simp only [etilde6Dim] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

set_option maxHeartbeats 3200000 in
-- reason: matches the `set_option maxHeartbeats` budget on
-- `embed_t125_in_tree_per_kQ` (`FieldGenericT125.lean:55`), which the
-- forthcoming proof body of this helper mirrors line-for-line — the
-- ~20 distinctness facts and the 49-case `fin_cases` adjacency check
-- through the `Fin 7 ↪ Fin n` embedding need the larger budget.
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) Ẽ₆ = T(2, 2, 2) embedding helper: given
seven vertices forming a `T(2, 2, 2)` shape inside an acyclic simple
graph, embed and dispatch to `etilde6_not_finite_type_per_kQ` via
`subgraph_infinite_type_transfer_per_kQ`.

Mirrors the pattern of `embed_t125_in_tree_per_kQ`
(`FieldGenericT125.lean:71`). Vertex roles match `etilde6Adj`: `v₀`
(center, vertex `0`) with three length-2 arms `(c₁, d₁)` (vertices
`1`-`2`), `(c₂, d₂)` (vertices `3`-`4`), `(c₃, d₃)` (vertices `5`-`6`).
Embedding map: `0→v₀, 1→c₁, 2→d₁, 3→c₂, 4→d₂, 5→c₃, 6→d₃`.

Shared helper introduced for the non-adjacent-branches leaf case
(issue #2932). Body filled in #2937 following the
`embed_t125_in_tree_per_kQ` pattern: build the distinctness lattice
via `acyclic_no_triangle` (six triangle non-edges) and
`acyclic_path_nonadj` (six distance-3 and three distance-4 non-edges),
define a `Fin 7 ↪ Fin n` embedding, verify
`etilde6Adj i j = adj (φ i) (φ j)` by case analysis, then dispatch
via `subgraph_infinite_type_transfer_per_kQ`. -/
theorem embed_etilde6_in_tree_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (v₀ c₁ d₁ c₂ d₂ c₃ d₃ : Fin n)
    (hc₁ : adj v₀ c₁ = 1) (hd₁ : adj c₁ d₁ = 1)
    (hc₂ : adj v₀ c₂ = 1) (hd₂ : adj c₂ d₂ = 1)
    (hc₃ : adj v₀ c₃ = 1) (hd₃ : adj c₃ d₃ = 1)
    (hc₁_ne_c₂ : c₁ ≠ c₂) (hc₁_ne_c₃ : c₁ ≠ c₃) (hc₂_ne_c₃ : c₂ ≠ c₃)
    (hd₁_ne_v₀ : d₁ ≠ v₀) (hd₂_ne_v₀ : d₂ ≠ v₀) (hd₃_ne_v₀ : d₃ ≠ v₀)
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
  have hv₀_ne_c₁ := ne_of_adj' v₀ c₁ hc₁
  have hv₀_ne_c₂ := ne_of_adj' v₀ c₂ hc₂
  have hv₀_ne_c₃ := ne_of_adj' v₀ c₃ hc₃
  have hc₁_ne_d₁ := ne_of_adj' c₁ d₁ hd₁
  have hc₂_ne_d₂ := ne_of_adj' c₂ d₂ hd₂
  have hc₃_ne_d₃ := ne_of_adj' c₃ d₃ hd₃
  -- Reversed edges
  have hc₁_v₀ : adj c₁ v₀ = 1 := (adj_comm c₁ v₀).trans hc₁
  have hc₂_v₀ : adj c₂ v₀ = 1 := (adj_comm c₂ v₀).trans hc₂
  have hc₃_v₀ : adj c₃ v₀ = 1 := (adj_comm c₃ v₀).trans hc₃
  have hd₁_c₁ : adj d₁ c₁ = 1 := (adj_comm d₁ c₁).trans hd₁
  have hd₂_c₂ : adj d₂ c₂ = 1 := (adj_comm d₂ c₂).trans hd₂
  have hd₃_c₃ : adj d₃ c₃ = 1 := (adj_comm d₃ c₃).trans hd₃
  -- Triangle non-edges (acyclic_no_triangle): v₀-dᵢ via apex cᵢ
  have hv₀d₁ : adj v₀ d₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic c₁ v₀ d₁
      hd₁_ne_v₀.symm hv₀_ne_c₁ hc₁_ne_d₁.symm hc₁_v₀ hd₁
  have hv₀d₂ : adj v₀ d₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic c₂ v₀ d₂
      hd₂_ne_v₀.symm hv₀_ne_c₂ hc₂_ne_d₂.symm hc₂_v₀ hd₂
  have hv₀d₃ : adj v₀ d₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic c₃ v₀ d₃
      hd₃_ne_v₀.symm hv₀_ne_c₃ hc₃_ne_d₃.symm hc₃_v₀ hd₃
  -- Triangle non-edges: cᵢ-cⱼ via apex v₀
  have hc₁c₂ : adj c₁ c₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ c₁ c₂
      hc₁_ne_c₂ hv₀_ne_c₁.symm hv₀_ne_c₂.symm hc₁ hc₂
  have hc₁c₃ : adj c₁ c₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ c₁ c₃
      hc₁_ne_c₃ hv₀_ne_c₁.symm hv₀_ne_c₃.symm hc₁ hc₃
  have hc₂c₃ : adj c₂ c₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ c₂ c₃
      hc₂_ne_c₃ hv₀_ne_c₂.symm hv₀_ne_c₃.symm hc₂ hc₃
  -- Cross-arm ne (level 1): cᵢ ≠ dⱼ for i ≠ j (from triangle non-edges)
  have hc₁_ne_d₂ : c₁ ≠ d₂ := by intro h; rw [h] at hc₁; linarith [hv₀d₂]
  have hc₁_ne_d₃ : c₁ ≠ d₃ := by intro h; rw [h] at hc₁; linarith [hv₀d₃]
  have hc₂_ne_d₁ : c₂ ≠ d₁ := by intro h; rw [h] at hc₂; linarith [hv₀d₁]
  have hc₂_ne_d₃ : c₂ ≠ d₃ := by intro h; rw [h] at hc₂; linarith [hv₀d₃]
  have hc₃_ne_d₁ : c₃ ≠ d₁ := by intro h; rw [h] at hc₃; linarith [hv₀d₁]
  have hc₃_ne_d₂ : c₃ ≠ d₂ := by intro h; rw [h] at hc₃; linarith [hv₀d₂]
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
  -- Distance-3 non-edges (4-vertex paths): cᵢ-dⱼ for i ≠ j
  have hc₁d₂ : adj c₁ d₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₂, c₂, v₀, c₁] (by simp)
      (path_nodup4 _ _ _ _ hc₂_ne_d₂.symm hd₂_ne_v₀ hc₁_ne_d₂.symm
        hv₀_ne_c₂.symm hc₁_ne_c₂.symm hv₀_ne_c₁)
      (path_edges4 _ _ _ _ hd₂_c₂ hc₂_v₀ hc₁)
  have hc₁d₃ : adj c₁ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, c₁] (by simp)
      (path_nodup4 _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hc₁_ne_d₃.symm
        hv₀_ne_c₃.symm hc₁_ne_c₃.symm hv₀_ne_c₁)
      (path_edges4 _ _ _ _ hd₃_c₃ hc₃_v₀ hc₁)
  have hc₂d₁ : adj c₂ d₁ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₁, c₁, v₀, c₂] (by simp)
      (path_nodup4 _ _ _ _ hc₁_ne_d₁.symm hd₁_ne_v₀ hc₂_ne_d₁.symm
        hv₀_ne_c₁.symm hc₁_ne_c₂ hv₀_ne_c₂)
      (path_edges4 _ _ _ _ hd₁_c₁ hc₁_v₀ hc₂)
  have hc₂d₃ : adj c₂ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, c₂] (by simp)
      (path_nodup4 _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hv₀_ne_c₂)
      (path_edges4 _ _ _ _ hd₃_c₃ hc₃_v₀ hc₂)
  have hc₃d₁ : adj c₃ d₁ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₁, c₁, v₀, c₃] (by simp)
      (path_nodup4 _ _ _ _ hc₁_ne_d₁.symm hd₁_ne_v₀ hc₃_ne_d₁.symm
        hv₀_ne_c₁.symm hc₁_ne_c₃ hv₀_ne_c₃)
      (path_edges4 _ _ _ _ hd₁_c₁ hc₁_v₀ hc₃)
  have hc₃d₂ : adj c₃ d₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₂, c₂, v₀, c₃] (by simp)
      (path_nodup4 _ _ _ _ hc₂_ne_d₂.symm hd₂_ne_v₀ hc₃_ne_d₂.symm
        hv₀_ne_c₂.symm hc₂_ne_c₃ hv₀_ne_c₃)
      (path_edges4 _ _ _ _ hd₂_c₂ hc₂_v₀ hc₃)
  -- Cross-arm ne (level 2): dᵢ ≠ dⱼ for i ≠ j (from distance-3 non-edges)
  have hd₁_ne_d₂ : d₁ ≠ d₂ := by intro h; rw [h] at hd₁; linarith [hc₁d₂]
  have hd₁_ne_d₃ : d₁ ≠ d₃ := by intro h; rw [h] at hd₁; linarith [hc₁d₃]
  have hd₂_ne_d₃ : d₂ ≠ d₃ := by intro h; rw [h] at hd₂; linarith [hc₂d₃]
  -- Distance-4 non-edges (5-vertex paths): dᵢ-dⱼ for i ≠ j
  have hd₁d₂ : adj d₁ d₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₂, c₂, v₀, c₁, d₁] (by simp)
      (path_nodup5 _ _ _ _ _ hc₂_ne_d₂.symm hd₂_ne_v₀ hc₁_ne_d₂.symm hd₁_ne_d₂.symm
        hv₀_ne_c₂.symm hc₁_ne_c₂.symm hc₂_ne_d₁ hv₀_ne_c₁ hd₁_ne_v₀.symm hc₁_ne_d₁)
      (path_edges5 _ _ _ _ _ hd₂_c₂ hc₂_v₀ hc₁ hd₁)
  have hd₁d₃ : adj d₁ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, c₁, d₁] (by simp)
      (path_nodup5 _ _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hc₁_ne_d₃.symm hd₁_ne_d₃.symm
        hv₀_ne_c₃.symm hc₁_ne_c₃.symm hc₃_ne_d₁ hv₀_ne_c₁ hd₁_ne_v₀.symm hc₁_ne_d₁)
      (path_edges5 _ _ _ _ _ hd₃_c₃ hc₃_v₀ hc₁ hd₁)
  have hd₂d₃ : adj d₂ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, c₂, d₂] (by simp)
      (path_nodup5 _ _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm hd₂_ne_d₃.symm
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂ hv₀_ne_c₂ hd₂_ne_v₀.symm hc₂_ne_d₂)
      (path_edges5 _ _ _ _ _ hd₃_c₃ hc₃_v₀ hc₂ hd₂)
  -- Construct the embedding φ : Fin 7 ↪ Fin n for T(2, 2, 2)
  -- Map: 0→v₀, 1→c₁, 2→d₁, 3→c₂, 4→d₂, 5→c₃, 6→d₃
  let φ_fun : Fin 7 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => v₀  | ⟨1, _⟩ => c₁  | ⟨2, _⟩ => d₁
    | ⟨3, _⟩ => c₂  | ⟨4, _⟩ => d₂  | ⟨5, _⟩ => c₃
    | ⟨6, _⟩ => d₃
  have φ_inj : Function.Injective φ_fun := by
    intro i j hij; simp only [φ_fun] at hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exact absurd hij ‹_›)
      | (exact absurd hij.symm ‹_›)
  let φ : Fin 7 ↪ Fin n := ⟨φ_fun, φ_inj⟩
  have hembed : ∀ i j, etilde6Adj i j = adj (φ i) (φ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [etilde6Adj, φ, φ_fun] <;> norm_num <;>
      linarith [hdiag v₀, hdiag c₁, hdiag d₁,
        hdiag c₂, hdiag d₂, hdiag c₃, hdiag d₃,
        hc₁, hd₁, hc₂, hd₂, hc₃, hd₃,
        adj_comm v₀ c₁, adj_comm v₀ d₁, adj_comm v₀ c₂, adj_comm v₀ d₂,
        adj_comm v₀ c₃, adj_comm v₀ d₃,
        adj_comm c₁ d₁, adj_comm c₁ c₂, adj_comm c₁ d₂,
        adj_comm c₁ c₃, adj_comm c₁ d₃,
        adj_comm d₁ c₂, adj_comm d₁ d₂, adj_comm d₁ c₃, adj_comm d₁ d₃,
        adj_comm c₂ d₂, adj_comm c₂ c₃, adj_comm c₂ d₃,
        adj_comm d₂ c₃, adj_comm d₂ d₃,
        adj_comm c₃ d₃,
        hv₀d₁, hv₀d₂, hv₀d₃, hc₁c₂, hc₁c₃, hc₂c₃,
        hc₁d₂, hc₁d₃, hc₂d₁, hc₂d₃, hc₃d₁, hc₃d₂,
        hd₁d₂, hd₁d₃, hd₂d₃]
  exact subgraph_infinite_type_transfer_per_kQ φ F Q
    (etilde6_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

end Etingof
