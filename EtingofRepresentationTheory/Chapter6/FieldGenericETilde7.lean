import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericStar
import EtingofRepresentationTheory.Chapter6.FieldGenericETilde6

/-!
# Orientation-Generic Ẽ₇ Construction (#2792)

F-generic, orientation-generic version of the Ẽ₇ representation
`etilde7Rep` from `InfiniteTypeConstructions.lean`. This file provides
`etilde7Rep_kQ`, its dimension-vector lemma, an indecomposability
stub that inherits the wave-54 framework wall, and the per-(F, Q)
infinite-type theorem.

Ẽ₇ is the affine `E₇` Dynkin diagram T_{1,3,3}: 8 vertices forming
three arms meeting at the center (vertex 0).

- Arm 1 (length 1): `0 — 1`
- Arm 2 (length 3): `0 — 2 — 3 — 4`
- Arm 3 (length 3): `0 — 5 — 6 — 7`

The canonical orientation (`etilde7Quiver`) directs all arrows toward
the center: `1 → 0`, `4 → 3 → 2 → 0`, `7 → 6 → 5 → 0`. For an
arbitrary orientation `Q` of `etilde7Adj`, each of the seven edges
may point either way, so the construction provides a forward and
reverse map per edge.

Indecomposability inherits the same wave-54 framework wall as the
ℂ-specific source `etilde7Rep_isIndecomposable`
(`InfiniteTypeConstructions.lean:3588`); the stub here carries the
same `sorry` with a docstring tying it to the wall.

See the "Naming conventions" section of
`Chapter6/FieldGenericInfiniteType.lean` for the meaning of the
`_F` / `_kQ` / `_per_kQ` suffixes used throughout this file.
-/

open scoped Matrix

namespace Etingof

/-! ## Section 1: F-generic forward maps for Ẽ₇

F-generic versions of the ℂ-specific maps used in `etilde7RepMap`
(`InfiniteTypeConstructions.lean:3559`). The bodies are copy-paste of
the ℂ versions with `ℂ` replaced by `F`. The maps reused from existing
files are `starEmbed1_F` (from `FieldGenericInfiniteType.lean`) and
`prefixBlockEmbed_F 2 3` (from `FieldGenericETilde6.lean`, used for
edges {2,3} and {5,6} where the arrow goes leaf → arm-internal vertex).
The `3 → 4` prefix-block embedding for edges {0,2} and (via the dual)
{0,5} comes from the same `prefixBlockEmbed_F` family.
-/

/-- F-generic embedding from a 3-block space into blocks (A, _, C, D) of a
4-block space: `(x, y, z) ↦ (x, 0, y, z)`. Mirror of `embed3to4_ACD`
(`InfiniteTypeConstructions.lean:3516`). -/
noncomputable def embed3to4_ACD_F (F : Type) [Field F] (m : ℕ) :
    (Fin (3 * (m + 1)) → F) →ₗ[F] (Fin (4 * (m + 1)) → F) where
  toFun x i :=
    if h : i.val < m + 1 then
      x ⟨i.val, by omega⟩
    else if h2 : m + 1 ≤ i.val ∧ i.val < 2 * (m + 1) then
      0
    else if h3 : i.val < 4 * (m + 1) then
      x ⟨i.val - (m + 1), by omega⟩
    else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- F-generic Ẽ₇ arm-1 embedding `F^{2(m+1)} → F^{4(m+1)}`:
`(p, q) ↦ (p + q, p, q, Nq)`. Couples all four blocks of the center
with the arm-1 leaf, introducing a nilpotent twist in block D. Mirror
of `etilde7Arm1Embed` (`InfiniteTypeConstructions.lean:3535`). -/
noncomputable def etilde7Arm1Embed_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (4 * (m + 1)) → F) where
  toFun w i :=
    if h : i.val < m + 1 then
      w ⟨i.val, by omega⟩ + w ⟨m + 1 + i.val, by omega⟩
    else if h2 : i.val < 2 * (m + 1) then
      w ⟨i.val - (m + 1), by omega⟩
    else if h3 : i.val < 3 * (m + 1) then
      w ⟨m + 1 + (i.val - 2 * (m + 1)), by omega⟩
    else
      let j := i.val - 3 * (m + 1)
      if h4 : j + 1 < m + 1 then w ⟨m + 1 + j + 1, by omega⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-! ## Section 2: F-generic reverse maps for Ẽ₇

For an arbitrary orientation `Q` of `etilde7Adj`, each edge may point
the opposite way from `etilde7Quiver`. The reverse maps below are
linear maps in the opposite direction:

- The reverse of `prefixBlockEmbed_F 3 4` is `prefixBlockProj_F 3 4 _`
  (from `FieldGenericETilde6.lean`), sending `(a, b, c, d) ↦ (a, b, c)`.
- `embed3to4_ACD_reverse_F`: left inverse of `embed3to4_ACD_F`,
  sending `(a, b, c, d) ↦ (a, c, d)` (blocks A, C, D extracted).
- `etilde7Arm1Embed_reverse_F`: a right section of `etilde7Arm1Embed_F`,
  sending `(a, b, c, d) ↦ (b, c)`. The map `etilde7Arm1Embed_F` is not
  injective for `m ≥ 1` (4(m+1)-dim codomain, 2(m+1)-dim domain — it
  *is* injective, but the projection `(b, c)` is a left inverse on its
  image rather than a right inverse on the codomain). The choice
  matches the analogous shape used in `etilde6GammaInv_F`
  (`FieldGenericETilde6.lean:133`).

The leaf-edge reverses (for edges `{3, 4}` and `{6, 7}`) reuse
`etilde6LeafProj_F` from `FieldGenericETilde6.lean`; the arm-internal
reverses (for edges `{2, 3}` and `{5, 6}`) use
`prefixBlockProj_F 2 3 _` from the same file.
-/

/-- Reverse map for the `embed3to4_ACD_F` edge: `(a, b, c, d) ↦ (a, c, d)`,
sending block A to the first third, then blocks C, D to the last two
thirds. Left inverse of `embed3to4_ACD_F`. -/
noncomputable def embed3to4_ACD_reverse_F (F : Type) [Field F] (m : ℕ) :
    (Fin (4 * (m + 1)) → F) →ₗ[F] (Fin (3 * (m + 1)) → F) where
  toFun w i :=
    if h : i.val < m + 1 then
      w ⟨i.val, by omega⟩
    else
      w ⟨i.val + (m + 1), by omega⟩
  map_add' _ _ := by ext; simp only [Pi.add_apply]; split_ifs <;> rfl
  map_smul' _ _ := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> rfl

/-- A right section of `etilde7Arm1Embed_F`: `(a, b, c, d) ↦ (b, c)`.
The choice extracts blocks B and C, which are exactly the `p` and `q`
components of the canonical input. Satisfies
`etilde7Arm1Embed_F ∘ etilde7Arm1Embed_reverse_F ≠ id` (the section
is only a right inverse on the image of `etilde7Arm1Embed_F`). -/
noncomputable def etilde7Arm1Embed_reverse_F (F : Type) [Field F] (m : ℕ) :
    (Fin (4 * (m + 1)) → F) →ₗ[F] (Fin (2 * (m + 1)) → F) where
  toFun w i :=
    if h : i.val < m + 1 then
      w ⟨m + 1 + i.val, by omega⟩
    else
      w ⟨2 * (m + 1) + (i.val - (m + 1)), by omega⟩
  map_add' _ _ := by ext; simp only [Pi.add_apply]; split_ifs <;> rfl
  map_smul' _ _ := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> rfl

/-! ## Section 3: Orientation-generic Ẽ₇ representation

The map function is a match on `(a.val, b.val)` mirroring `etilde7RepMap`
(`InfiniteTypeConstructions.lean:3559`) for the canonical seven (a, b)
pairs, plus the seven reversed pairs using the maps from Section 2.
Outside those 14 edge pairs, the map is `0` (these arrows do not exist
in any orientation of `etilde7Adj`).
-/

/-- Direction-aware match-based map function for the orientation-generic
Ẽ₇ representation. Returns the same linear maps as `etilde7RepMap` for
the canonical orientation, plus the reverse maps from Section 2 when the
arrow is in the reversed direction. -/
private noncomputable def etilde7RepMap_kQ (F : Type) [Field F] (m : ℕ) (a b : Fin 8) :
    (Fin (etilde7Dim m a) → F) →ₗ[F] (Fin (etilde7Dim m b) → F) :=
  match a, b with
  -- Arm 1: edge {0, 1}
  | ⟨1, _⟩, ⟨0, _⟩ => etilde7Arm1Embed_F F m
  | ⟨0, _⟩, ⟨1, _⟩ => etilde7Arm1Embed_reverse_F F m
  -- Arm 2: edge {3, 4}
  | ⟨4, _⟩, ⟨3, _⟩ => starEmbed1_F F m
  | ⟨3, _⟩, ⟨4, _⟩ => etilde6LeafProj_F F m
  -- Arm 2: edge {2, 3}
  | ⟨3, _⟩, ⟨2, _⟩ => prefixBlockEmbed_F F 2 3 m
  | ⟨2, _⟩, ⟨3, _⟩ => prefixBlockProj_F F 2 3 m (by omega)
  -- Arm 2: edge {0, 2}
  | ⟨2, _⟩, ⟨0, _⟩ => prefixBlockEmbed_F F 3 4 m
  | ⟨0, _⟩, ⟨2, _⟩ => prefixBlockProj_F F 3 4 m (by omega)
  -- Arm 3: edge {6, 7}
  | ⟨7, _⟩, ⟨6, _⟩ => starEmbed1_F F m
  | ⟨6, _⟩, ⟨7, _⟩ => etilde6LeafProj_F F m
  -- Arm 3: edge {5, 6}
  | ⟨6, _⟩, ⟨5, _⟩ => prefixBlockEmbed_F F 2 3 m
  | ⟨5, _⟩, ⟨6, _⟩ => prefixBlockProj_F F 2 3 m (by omega)
  -- Arm 3: edge {0, 5}
  | ⟨5, _⟩, ⟨0, _⟩ => embed3to4_ACD_F F m
  | ⟨0, _⟩, ⟨5, _⟩ => embed3to4_ACD_reverse_F F m
  -- Non-edge or impossible (ruled out by `hOrient`); placeholder
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic Ẽ₇ (= T_{1,3,3}) representation over an arbitrary
field `F` with arbitrary orientation `Q` of `etilde7Adj`. Dimension vector
follows `etilde7Dim`: vertex 0 has dim `4(m+1)`, vertices 2/5 have dim
`3(m+1)`, vertices 1/3/6 have dim `2(m+1)`, vertices 4/7 have dim `m+1`.

The map on an arrow `e : Q.Hom a b` depends only on the underlying
unordered edge `{a, b}` and the direction `a → b`. Each of the seven
edges of `etilde7Adj` contributes one canonical map (matching
`etilde7RepMap`) and one reverse map (defined in Section 2). The
orientation hypothesis `hOrient` is not used by the construction
itself; it is recorded so that downstream lemmas (the
indecomposability proof for the inherited framework wall) can
pattern-match on which arrows exist. -/
noncomputable def etilde7Rep_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (_hOrient : @Etingof.IsOrientationOf 8 Q etilde7Adj)
    (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin 8) _ Q := by
  letI := Q
  exact {
    obj := fun v => Fin (etilde7Dim m v) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => etilde7RepMap_kQ F m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The orientation-generic Ẽ₇ rep has the expected dimension vector
`etilde7Dim m` at each vertex. -/
theorem etilde7Rep_kQ_dimVec
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q etilde7Adj)
    (m : ℕ) (v : Fin 8) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin 8) _ Q
      (etilde7Rep_kQ F Q hOrient m) v ≃ₗ[F] (Fin (etilde7Dim m v) → F)) :=
  ⟨LinearEquiv.refl F _⟩

/-! ## Section 4: Indecomposability (inherits the wave-54 framework wall)

The ℂ-specific source `etilde7Rep_isIndecomposable`
(`InfiniteTypeConstructions.lean:3588`) is `sorry`'d due to the wave-54
framework wall: the single-nilpotent-twist construction is provably
decomposable for every `m ≥ 1` because the N-twist on arm 1 only covers
the `⟨e₀, …, e_{m-1}⟩` sub-block of its target at the center, leaving
the `e_m` direction free to peel off as a 1-dim summand. See
`progress/indecomposability-framework-investigation.md` (Section 1)
for the explicit counter-example (verified at `etilde7Rep 1`).

Following the same pattern as Ẽ₆ Sub B (#2807), we mirror the
ℂ-specific stub at the orientation-generic level, carrying the same
`sorry` with a docstring tying it to the framework wall. The final
per-(F, Q) theorem `etilde7_not_finite_type_per_kQ` below depends
transitively on this sorry, exactly as the ℂ-specific
`etilde7_not_finite_type` depends on `etilde7Rep_isIndecomposable`.
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic indecomposability of `etilde7Rep_kQ`.

**Framework wall (wave 54)**: this theorem inherits the same wall that
blocks the ℂ-specific source `etilde7Rep_isIndecomposable`
(`InfiniteTypeConstructions.lean:3588`): the single-nilpotent-twist
construction is provably decomposable for every `m ≥ 1` (the N-twist on
arm 1 only covers the `⟨e₀, …, e_{m-1}⟩` sub-block of block D at the
center, leaving `e_m` free). See
`progress/indecomposability-framework-investigation.md` (Section 1) for
the explicit counter-example (`etilde7Rep 1`). A stronger construction
sketched in Section 5 Option B would close the wall.

The `1 ≤ m` hypothesis is required even in the planned proof — for
`m = 0`, `nilpotentShiftLin 0 = 0`, the nilpotent twist disappears and
the representation is provably decomposable.

The current proof is a `sorry`; the consumer
`etilde7_not_finite_type_per_kQ` inherits this dependency. A follow-up
issue will revisit when the framework question is resolved. -/
theorem etilde7Rep_kQ_isIndecomposable
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q etilde7Adj)
    (m : ℕ) (hm : 1 ≤ m) :
    (etilde7Rep_kQ F Q hOrient m).IsIndecomposable := by
  let _ := hm  -- retain `hm` in the signature for the future proof
  sorry

/-! ## Section 5: Per-(F, Q) infinite-type theorem -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) version of `etilde7_not_finite_type`: for any
algebraically closed field `F` and any orientation `Q` of `etilde7Adj`,
the set of dimension vectors of indecomposable representations is
infinite.

Mirrors the proof of `etilde7_not_finite_type`
(`InfiniteTypeConstructions.lean:3608`): we range over `m + 1` (not `m`)
because `etilde7Rep_kQ_isIndecomposable` requires `1 ≤ m` (the `m = 0`
case is provably decomposable). Injectivity comes from vertex `4`, where
`etilde7Dim m 4 = m + 1`.

This theorem carries no direct `sorry`, but transitively depends on
`etilde7Rep_kQ_isIndecomposable`, which inherits the wave-54 framework
wall — see its docstring. -/
theorem etilde7_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 8))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 8) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 8 Q etilde7Adj) :
    ¬ Set.Finite
      {d : Fin 8 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 8) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ, (fun v : Fin 8 => etilde7Dim (m + 1) v) ∈
      {d : Fin 8 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 8) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨etilde7Rep_kQ F Q hOrient (m + 1),
      etilde7Rep_kQ_isIndecomposable F Q hOrient (m + 1) (Nat.succ_le_succ m.zero_le),
      etilde7Rep_kQ_dimVec F Q hOrient (m + 1)⟩
  have hinj : Function.Injective (fun m : ℕ => fun v : Fin 8 => etilde7Dim (m + 1) v) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨4, by omega⟩
    simp only [etilde7Dim] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

set_option maxHeartbeats 3200000 in
-- reason: matches the `set_option maxHeartbeats` budget on
-- `embed_t125_in_tree_per_kQ` (`FieldGenericT125.lean:55`), which the
-- proof body mirrors — the ~30 distinctness facts and the 64-case
-- `fin_cases` adjacency check through the `Fin 8 ↪ Fin n` embedding
-- need the larger budget.
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) Ẽ₇ = T(1, 3, 3) embedding helper: given
eight vertices forming a `T(1, 3, 3)` shape inside an acyclic simple
graph, embed and dispatch to `etilde7_not_finite_type_per_kQ` via
`subgraph_infinite_type_transfer_per_kQ`.

Mirrors the pattern of `embed_t125_in_tree_per_kQ`
(`FieldGenericT125.lean:71`). Vertex roles match `etilde7Adj`: `v₀`
(center, vertex `0`); `u₁` (length-1 arm, vertex `1`); `(c₂, d₂, e₂)`
(length-3 arm, vertices `2`-`3`-`4`); `(c₃, d₃, e₃)` (length-3 arm,
vertices `5`-`6`-`7`). Embedding map:
`0→v₀, 1→u₁, 2→c₂, 3→d₂, 4→e₂, 5→c₃, 6→d₃, 7→e₃`.

Shared helper introduced for the non-adjacent-branches leaf case
(issue #2932). Body filled in #2938 following the
`embed_t125_in_tree_per_kQ` pattern: build the distinctness lattice
via `acyclic_no_triangle` (seven triangle non-edges) and
`acyclic_path_nonadj` (six distance-3, five distance-4, two
distance-5, and one distance-6 non-edges), define a
`Fin 8 ↪ Fin n` embedding, verify `etilde7Adj i j = adj (φ i) (φ j)`
by 64-case split, then dispatch via
`subgraph_infinite_type_transfer_per_kQ`. -/
theorem embed_etilde7_in_tree_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (v₀ u₁ c₂ d₂ e₂ c₃ d₃ e₃ : Fin n)
    (hu₁ : adj v₀ u₁ = 1)
    (hc₂ : adj v₀ c₂ = 1) (hd₂ : adj c₂ d₂ = 1) (he₂ : adj d₂ e₂ = 1)
    (hc₃ : adj v₀ c₃ = 1) (hd₃ : adj c₃ d₃ = 1) (he₃ : adj d₃ e₃ = 1)
    (hu₁_ne_c₂ : u₁ ≠ c₂) (hu₁_ne_c₃ : u₁ ≠ c₃) (hc₂_ne_c₃ : c₂ ≠ c₃)
    (hd₂_ne_v₀ : d₂ ≠ v₀) (hd₃_ne_v₀ : d₃ ≠ v₀)
    (he₂_ne_c₂ : e₂ ≠ c₂) (he₃_ne_c₃ : e₃ ≠ c₃)
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
  have hv₀_ne_c₂ := ne_of_adj' v₀ c₂ hc₂
  have hv₀_ne_c₃ := ne_of_adj' v₀ c₃ hc₃
  have hc₂_ne_d₂ := ne_of_adj' c₂ d₂ hd₂
  have hc₃_ne_d₃ := ne_of_adj' c₃ d₃ hd₃
  have hd₂_ne_e₂ := ne_of_adj' d₂ e₂ he₂
  have hd₃_ne_e₃ := ne_of_adj' d₃ e₃ he₃
  -- Reversed edges
  have hu₁_v₀ : adj u₁ v₀ = 1 := (adj_comm u₁ v₀).trans hu₁
  have hc₂_v₀ : adj c₂ v₀ = 1 := (adj_comm c₂ v₀).trans hc₂
  have hc₃_v₀ : adj c₃ v₀ = 1 := (adj_comm c₃ v₀).trans hc₃
  have hd₂_c₂ : adj d₂ c₂ = 1 := (adj_comm d₂ c₂).trans hd₂
  have hd₃_c₃ : adj d₃ c₃ = 1 := (adj_comm d₃ c₃).trans hd₃
  have he₂_d₂ : adj e₂ d₂ = 1 := (adj_comm e₂ d₂).trans he₂
  have he₃_d₃ : adj e₃ d₃ = 1 := (adj_comm e₃ d₃).trans he₃
  -- Triangle non-edges (acyclic_no_triangle)
  -- u₁-cᵢ via apex v₀; cᵢ-cⱼ via apex v₀
  have hu₁c₂ : adj u₁ c₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ c₂
      hu₁_ne_c₂ hv₀_ne_u₁.symm hv₀_ne_c₂.symm hu₁ hc₂
  have hu₁c₃ : adj u₁ c₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ c₃
      hu₁_ne_c₃ hv₀_ne_u₁.symm hv₀_ne_c₃.symm hu₁ hc₃
  have hc₂c₃ : adj c₂ c₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ c₂ c₃
      hc₂_ne_c₃ hv₀_ne_c₂.symm hv₀_ne_c₃.symm hc₂ hc₃
  -- v₀-dᵢ via apex cᵢ
  have hv₀d₂ : adj v₀ d₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic c₂ v₀ d₂
      hd₂_ne_v₀.symm hv₀_ne_c₂ hc₂_ne_d₂.symm hc₂_v₀ hd₂
  have hv₀d₃ : adj v₀ d₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic c₃ v₀ d₃
      hd₃_ne_v₀.symm hv₀_ne_c₃ hc₃_ne_d₃.symm hc₃_v₀ hd₃
  -- cᵢ-eᵢ via apex dᵢ
  have hc₂e₂ : adj c₂ e₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic d₂ c₂ e₂
      he₂_ne_c₂.symm hc₂_ne_d₂ hd₂_ne_e₂.symm hd₂_c₂ he₂
  have hc₃e₃ : adj c₃ e₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic d₃ c₃ e₃
      he₃_ne_c₃.symm hc₃_ne_d₃ hd₃_ne_e₃.symm hd₃_c₃ he₃
  -- Cross-arm ne (level 1): from triangle non-edges
  have hu₁_ne_d₂ : u₁ ≠ d₂ := by intro h; rw [h] at hu₁; linarith [hv₀d₂]
  have hu₁_ne_d₃ : u₁ ≠ d₃ := by intro h; rw [h] at hu₁; linarith [hv₀d₃]
  have hc₂_ne_d₃ : c₂ ≠ d₃ := by intro h; rw [h] at hc₂; linarith [hv₀d₃]
  have hc₃_ne_d₂ : c₃ ≠ d₂ := by intro h; rw [h] at hc₃; linarith [hv₀d₂]
  have hv₀_ne_e₂ : v₀ ≠ e₂ := by
    intro h; rw [← h] at he₂; linarith [adj_comm d₂ v₀, hv₀d₂]
  have hv₀_ne_e₃ : v₀ ≠ e₃ := by
    intro h; rw [← h] at he₃; linarith [adj_comm d₃ v₀, hv₀d₃]
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
  -- Distance-3 non-edges (4-vertex paths)
  have hu₁d₂ : adj u₁ d₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₂, c₂, v₀, u₁] (by simp)
      (path_nodup4 _ _ _ _ hc₂_ne_d₂.symm hd₂_ne_v₀ hu₁_ne_d₂.symm
        hv₀_ne_c₂.symm hu₁_ne_c₂.symm hv₀_ne_u₁)
      (path_edges4 _ _ _ _ hd₂_c₂ hc₂_v₀ hu₁)
  have hu₁d₃ : adj u₁ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, u₁] (by simp)
      (path_nodup4 _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hu₁_ne_d₃.symm
        hv₀_ne_c₃.symm hu₁_ne_c₃.symm hv₀_ne_u₁)
      (path_edges4 _ _ _ _ hd₃_c₃ hc₃_v₀ hu₁)
  have hd₂c₃ : adj d₂ c₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [c₃, v₀, c₂, d₂] (by simp)
      (path_nodup4 _ _ _ _ hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂
        hv₀_ne_c₂ hd₂_ne_v₀.symm hc₂_ne_d₂)
      (path_edges4 _ _ _ _ hc₃_v₀ hc₂ hd₂)
  have hc₂d₃ : adj c₂ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, c₂] (by simp)
      (path_nodup4 _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hv₀_ne_c₂)
      (path_edges4 _ _ _ _ hd₃_c₃ hc₃_v₀ hc₂)
  have hv₀e₂ : adj v₀ e₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₂, d₂, c₂, v₀] (by simp)
      (path_nodup4 _ _ _ _ hd₂_ne_e₂.symm he₂_ne_c₂ hv₀_ne_e₂.symm
        hc₂_ne_d₂.symm hd₂_ne_v₀ hv₀_ne_c₂.symm)
      (path_edges4 _ _ _ _ he₂_d₂ hd₂_c₂ hc₂_v₀)
  have hv₀e₃ : adj v₀ e₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₃, d₃, c₃, v₀] (by simp)
      (path_nodup4 _ _ _ _ hd₃_ne_e₃.symm he₃_ne_c₃ hv₀_ne_e₃.symm
        hc₃_ne_d₃.symm hd₃_ne_v₀ hv₀_ne_c₃.symm)
      (path_edges4 _ _ _ _ he₃_d₃ hd₃_c₃ hc₃_v₀)
  -- Cross-arm ne (level 2): from distance-3 non-edges
  have hu₁_ne_e₂ : u₁ ≠ e₂ := by intro h; rw [h] at hu₁; linarith [hv₀e₂]
  have hu₁_ne_e₃ : u₁ ≠ e₃ := by intro h; rw [h] at hu₁; linarith [hv₀e₃]
  have hc₂_ne_e₃ : c₂ ≠ e₃ := by intro h; rw [h] at hc₂; linarith [hv₀e₃]
  have hc₃_ne_e₂ : c₃ ≠ e₂ := by intro h; rw [h] at hc₃; linarith [hv₀e₂]
  have hd₂_ne_d₃ : d₂ ≠ d₃ := by intro h; rw [h] at hd₂; linarith [hc₂d₃]
  -- Distance-4 non-edges (5-vertex paths)
  have hu₁e₂ : adj u₁ e₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₂, d₂, c₂, v₀, u₁] (by simp)
      (path_nodup5 _ _ _ _ _ hd₂_ne_e₂.symm he₂_ne_c₂ hv₀_ne_e₂.symm hu₁_ne_e₂.symm
        hc₂_ne_d₂.symm hd₂_ne_v₀ hu₁_ne_d₂.symm hv₀_ne_c₂.symm hu₁_ne_c₂.symm hv₀_ne_u₁)
      (path_edges5 _ _ _ _ _ he₂_d₂ hd₂_c₂ hc₂_v₀ hu₁)
  have hu₁e₃ : adj u₁ e₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₃, d₃, c₃, v₀, u₁] (by simp)
      (path_nodup5 _ _ _ _ _ hd₃_ne_e₃.symm he₃_ne_c₃ hv₀_ne_e₃.symm hu₁_ne_e₃.symm
        hc₃_ne_d₃.symm hd₃_ne_v₀ hu₁_ne_d₃.symm hv₀_ne_c₃.symm hu₁_ne_c₃.symm hv₀_ne_u₁)
      (path_edges5 _ _ _ _ _ he₃_d₃ hd₃_c₃ hc₃_v₀ hu₁)
  have hd₂d₃ : adj d₂ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, c₂, d₂] (by simp)
      (path_nodup5 _ _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm hd₂_ne_d₃.symm
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂ hv₀_ne_c₂ hd₂_ne_v₀.symm hc₂_ne_d₂)
      (path_edges5 _ _ _ _ _ hd₃_c₃ hc₃_v₀ hc₂ hd₂)
  have hc₂e₃ : adj c₂ e₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₃, d₃, c₃, v₀, c₂] (by simp)
      (path_nodup5 _ _ _ _ _ hd₃_ne_e₃.symm he₃_ne_c₃ hv₀_ne_e₃.symm hc₂_ne_e₃.symm
        hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm hv₀_ne_c₃.symm hc₂_ne_c₃.symm hv₀_ne_c₂)
      (path_edges5 _ _ _ _ _ he₃_d₃ hd₃_c₃ hc₃_v₀ hc₂)
  have he₂c₃ : adj e₂ c₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [c₃, v₀, c₂, d₂, e₂] (by simp)
      (path_nodup5 _ _ _ _ _ hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂ hc₃_ne_e₂
        hv₀_ne_c₂ hd₂_ne_v₀.symm hv₀_ne_e₂ hc₂_ne_d₂ he₂_ne_c₂.symm hd₂_ne_e₂)
      (path_edges5 _ _ _ _ _ hc₃_v₀ hc₂ hd₂ he₂)
  -- Cross-arm ne (level 3): from distance-4 non-edges
  have hd₂_ne_e₃ : d₂ ≠ e₃ := by intro h; rw [h] at hd₂; linarith [hc₂e₃]
  have hd₃_ne_e₂ : d₃ ≠ e₂ := by
    intro h; rw [← h] at he₂; linarith [adj_comm d₂ d₃, hd₂d₃]
  -- Distance-5 non-edges (6-vertex paths)
  have hd₂e₃ : adj d₂ e₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₃, d₃, c₃, v₀, c₂, d₂] (by simp)
      (path_nodup6 _ _ _ _ _ _ hd₃_ne_e₃.symm he₃_ne_c₃ hv₀_ne_e₃.symm hc₂_ne_e₃.symm hd₂_ne_e₃.symm
        hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm hd₂_ne_d₃.symm
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂ hv₀_ne_c₂ hd₂_ne_v₀.symm hc₂_ne_d₂)
      (path_edges6 _ _ _ _ _ _ he₃_d₃ hd₃_c₃ hc₃_v₀ hc₂ hd₂)
  have he₂d₃ : adj e₂ d₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [d₃, c₃, v₀, c₂, d₂, e₂] (by simp)
      (path_nodup6 _ _ _ _ _ _ hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm hd₂_ne_d₃.symm hd₃_ne_e₂
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂ hc₃_ne_e₂
        hv₀_ne_c₂ hd₂_ne_v₀.symm hv₀_ne_e₂ hc₂_ne_d₂ he₂_ne_c₂.symm hd₂_ne_e₂)
      (path_edges6 _ _ _ _ _ _ hd₃_c₃ hc₃_v₀ hc₂ hd₂ he₂)
  -- Cross-arm ne (level 4): from distance-5 non-edge
  have he₂_ne_e₃ : e₂ ≠ e₃ := by intro h; rw [h] at he₂; linarith [hd₂e₃]
  -- Distance-6 non-edge (7-vertex path)
  have he₂e₃ : adj e₂ e₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [e₃, d₃, c₃, v₀, c₂, d₂, e₂] (by simp)
      (path_nodup7 _ _ _ _ _ _ _
        hd₃_ne_e₃.symm he₃_ne_c₃ hv₀_ne_e₃.symm hc₂_ne_e₃.symm hd₂_ne_e₃.symm he₂_ne_e₃.symm
        hc₃_ne_d₃.symm hd₃_ne_v₀ hc₂_ne_d₃.symm hd₂_ne_d₃.symm hd₃_ne_e₂
        hv₀_ne_c₃.symm hc₂_ne_c₃.symm hc₃_ne_d₂ hc₃_ne_e₂
        hv₀_ne_c₂ hd₂_ne_v₀.symm hv₀_ne_e₂ hc₂_ne_d₂ he₂_ne_c₂.symm hd₂_ne_e₂)
      (path_edges7 _ _ _ _ _ _ _ he₃_d₃ hd₃_c₃ hc₃_v₀ hc₂ hd₂ he₂)
  -- Construct the embedding φ : Fin 8 ↪ Fin n for T(1, 3, 3)
  -- Map: 0→v₀, 1→u₁, 2→c₂, 3→d₂, 4→e₂, 5→c₃, 6→d₃, 7→e₃
  let φ_fun : Fin 8 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => v₀  | ⟨1, _⟩ => u₁  | ⟨2, _⟩ => c₂
    | ⟨3, _⟩ => d₂  | ⟨4, _⟩ => e₂  | ⟨5, _⟩ => c₃
    | ⟨6, _⟩ => d₃  | ⟨7, _⟩ => e₃
  have φ_inj : Function.Injective φ_fun := by
    intro i j hij; simp only [φ_fun] at hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exact absurd hij ‹_›)
      | (exact absurd hij.symm ‹_›)
  let φ : Fin 8 ↪ Fin n := ⟨φ_fun, φ_inj⟩
  have hembed : ∀ i j, etilde7Adj i j = adj (φ i) (φ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [etilde7Adj, φ, φ_fun] <;> norm_num <;>
      linarith [hdiag v₀, hdiag u₁, hdiag c₂, hdiag d₂, hdiag e₂,
        hdiag c₃, hdiag d₃, hdiag e₃,
        hu₁, hc₂, hd₂, he₂, hc₃, hd₃, he₃,
        adj_comm v₀ u₁, adj_comm v₀ c₂, adj_comm v₀ d₂, adj_comm v₀ e₂,
        adj_comm v₀ c₃, adj_comm v₀ d₃, adj_comm v₀ e₃,
        adj_comm u₁ c₂, adj_comm u₁ d₂, adj_comm u₁ e₂,
        adj_comm u₁ c₃, adj_comm u₁ d₃, adj_comm u₁ e₃,
        adj_comm c₂ d₂, adj_comm c₂ e₂, adj_comm c₂ c₃,
        adj_comm c₂ d₃, adj_comm c₂ e₃,
        adj_comm d₂ e₂, adj_comm d₂ c₃, adj_comm d₂ d₃, adj_comm d₂ e₃,
        adj_comm e₂ c₃, adj_comm e₂ d₃, adj_comm e₂ e₃,
        adj_comm c₃ d₃, adj_comm c₃ e₃,
        adj_comm d₃ e₃,
        hu₁c₂, hu₁c₃, hc₂c₃, hv₀d₂, hv₀d₃, hc₂e₂, hc₃e₃,
        hu₁d₂, hu₁d₃, hd₂c₃, hc₂d₃, hv₀e₂, hv₀e₃,
        hu₁e₂, hu₁e₃, hd₂d₃, hc₂e₃, he₂c₃,
        hd₂e₃, he₂d₃,
        he₂e₃]
  exact subgraph_infinite_type_transfer_per_kQ φ F Q
    (etilde7_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

end Etingof
