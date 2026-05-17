import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType

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
-/

open scoped Matrix

namespace Etingof

/-! ## Section 1: F-generic forward maps for Ẽ₆

F-generic versions of the ℂ-specific maps used in `etilde6v2RepMap`
(`InfiniteTypeConstructions.lean:3282-3294`). The bodies are
copy-paste of the ℂ versions with `ℂ` replaced by `F`.
-/

/-- F-generic embedding from a 2-block space into the first two blocks of a
3-block space: `(a, b) ↦ (a, b, 0)`. Mirror of `embed2to3_AB`
(`InfiniteTypeConstructions.lean:1518`). -/
noncomputable def embed2to3_AB_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (3 * (m + 1)) → F) where
  toFun x i := if h : i.val < 2 * (m + 1) then x ⟨i.val, h⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

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

- `embed2to3_AB_reverse_F`: left inverse of `embed2to3_AB_F`, sending
  `(a, b, c) ↦ (a, b)` (first two blocks).
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

/-- Reverse map for the `embed2to3_AB_F` edge: `(a, b, c) ↦ (a, b)`,
which is the first-two-blocks projection. Left inverse of
`embed2to3_AB_F`. -/
noncomputable def embed2to3_AB_reverse_F (F : Type) [Field F] (m : ℕ) :
    (Fin (3 * (m + 1)) → F) →ₗ[F] (Fin (2 * (m + 1)) → F) where
  toFun w i := w ⟨i.val, by omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

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
  | ⟨1, _⟩, ⟨0, _⟩ => embed2to3_AB_F F m
  | ⟨0, _⟩, ⟨1, _⟩ => embed2to3_AB_reverse_F F m
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

end Etingof
