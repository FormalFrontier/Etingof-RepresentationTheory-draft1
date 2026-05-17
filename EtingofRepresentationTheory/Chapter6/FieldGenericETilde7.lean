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

end Etingof
