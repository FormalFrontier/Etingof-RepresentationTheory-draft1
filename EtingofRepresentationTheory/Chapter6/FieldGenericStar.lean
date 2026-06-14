import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericCycle

/-!
# Field-Generic Star (K_{1,4} / D̃₄) Representation

Extracted from `FieldGenericInfiniteType.lean` (originally §4 of that file)
during the file split tracked by #2825. This module provides the F-generic
K_{1,4} representation `starRepGen` with the canonical all-sink orientation
`starQuiver`, its dimension vector, indecomposability, and the resulting
infinite-type theorem `star_not_finite_type_F`.

The per-(field, orientation) star variants (`starRep_kQ` / projections)
from PR #2802 live in the lower half of this module (Sections labelled
"Direction-aware leaf maps" and "Orientation-generic K_{1,4} representation").
They were re-homed here from the shared header by #2846 — the original
PR #2802 added them to `FieldGenericInfiniteType.lean`, which broke
post-split main since the references to `starEmbed*_F` could not be
resolved (a cyclic import would be required).

The `_per_kQ` indecomposability proof from #2801 and the final
`star_not_finite_type_per_kQ` theorem will land in this module too.

See `FieldGenericInfiniteType.lean` for the naming conventions
(`_F` / `_gen`, `_kQ`, `_per_kQ`) and the shared nilpotent shift /
nilpotent complement primitives used here.
-/

open scoped Matrix
open Finset

namespace Etingof

/-- First-component embedding (F-generic): `x ↦ (x, 0)`. -/
noncomputable def starEmbed1_F (F : Type) [Field F] (m : ℕ) :
    (Fin (m + 1) → F) →ₗ[F] (Fin (2 * (m + 1)) → F) where
  toFun x i := if h : i.val < m + 1 then x ⟨i.val, h⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Second-component embedding (F-generic): `x ↦ (0, x)`. -/
noncomputable def starEmbed2_F (F : Type) [Field F] (m : ℕ) :
    (Fin (m + 1) → F) →ₗ[F] (Fin (2 * (m + 1)) → F) where
  toFun x i := if h : m + 1 ≤ i.val then x ⟨i.val - (m + 1), by omega⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Diagonal embedding (F-generic): `x ↦ (x, x)`. -/
noncomputable def starEmbedDiag_F (F : Type) [Field F] (m : ℕ) :
    (Fin (m + 1) → F) →ₗ[F] (Fin (2 * (m + 1)) → F) :=
  starEmbed1_F F m + starEmbed2_F F m

/-- Nilpotent-twisted embedding (F-generic): `x ↦ (x, Nx)`. -/
noncomputable def starEmbedNilp_F (F : Type) [Field F] (m : ℕ) :
    (Fin (m + 1) → F) →ₗ[F] (Fin (2 * (m + 1)) → F) :=
  starEmbed1_F F m + (starEmbed2_F F m).comp (nilpotentShiftLinGen F m)

/-- First-half projection (F-generic): `(a, b) ↦ a`. -/
noncomputable def starFirst_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) where
  toFun w i := w ⟨i.val, by omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Second-half projection (F-generic): `(a, b) ↦ b`. -/
noncomputable def starSecond_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) where
  toFun w i := w ⟨m + 1 + i.val, by omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-! ## Embedding sum lemmas

F-generic lemmas about the two leaf-embeds at the center vertex. Used by
`starRepGen_isIndecomposable` (this file) and by the D̃₅ cascade in
`FieldGenericD5Tilde.lean`. -/

/-- The two leaf-embeds are disjoint at the center:
`starEmbed1_F x + starEmbed2_F y = 0 → x = 0 ∧ y = 0`. -/
theorem embed_sum_zero_F (F : Type) [Field F] (m : ℕ) (x y : Fin (m + 1) → F)
    (h : starEmbed1_F F m x + starEmbed2_F F m y = 0) :
    x = 0 ∧ y = 0 := by
  have heval : ∀ j : Fin (2 * (m + 1)),
      starEmbed1_F F m x j + starEmbed2_F F m y j = 0 :=
    fun j => by have := congr_fun h j; simpa using this
  constructor <;> ext ⟨i, hi⟩ <;> simp only [Pi.zero_apply]
  · have := heval ⟨i, by omega⟩
    simp only [starEmbed1_F, starEmbed2_F, LinearMap.coe_mk, AddHom.coe_mk] at this
    split_ifs at this with h1
    · omega
    · simpa using this
  · have := heval ⟨m + 1 + i, by omega⟩
    simp only [starEmbed1_F, starEmbed2_F, LinearMap.coe_mk, AddHom.coe_mk] at this
    split_ifs at this with h1 h2
    · omega
    · omega
    · simp only [zero_add] at this
      have key : (⟨m + 1 + i - (m + 1), by omega⟩ : Fin (m + 1)) = ⟨i, hi⟩ := by
        simp only [Fin.mk.injEq]; omega
      rwa [key] at this
    · omega

/-- Every `F^{2(m+1)}` vector decomposes as the sum of its two half-block
embeddings via the half-block projections. -/
theorem center_decomp_F (F : Type) [Field F] (m : ℕ) (w : Fin (2 * (m + 1)) → F) :
    w = starEmbed1_F F m (starFirst_F F m w) +
        starEmbed2_F F m (starSecond_F F m w) := by
  ext ⟨j, hj⟩
  simp only [Pi.add_apply, starEmbed1_F, starEmbed2_F, starFirst_F, starSecond_F,
    LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hjlt : j < m + 1
  · simp only [dif_pos hjlt, show ¬(m + 1 ≤ j) from by omega, dite_false, add_zero]
  · simp only [dif_neg hjlt, show m + 1 ≤ j from by omega, dite_true, zero_add]
    congr 1; ext; simp; omega

/-- Match-based map for the F-generic star representation. -/
private noncomputable def starRepMapGen (F : Type) [Field F] (m : ℕ) (a b : Fin 5) :
    (Fin (if a.val = 0 then 2 * (m + 1) else m + 1) → F) →ₗ[F]
    (Fin (if b.val = 0 then 2 * (m + 1) else m + 1) → F) :=
  match a, b with
  | ⟨1, _⟩, ⟨0, _⟩ => starEmbed1_F F m
  | ⟨2, _⟩, ⟨0, _⟩ => starEmbed2_F F m
  | ⟨3, _⟩, ⟨0, _⟩ => starEmbedDiag_F F m
  | ⟨4, _⟩, ⟨0, _⟩ => starEmbedNilp_F F m
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The F-generic star representation with dim vector `(2(m+1), m+1, m+1, m+1, m+1)`. -/
noncomputable def starRepGen (F : Type) [Field F] (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin 5) _ starQuiver := by
  letI := starQuiver
  exact {
    obj := fun v => Fin (if v.val = 0 then 2 * (m + 1) else m + 1) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => starRepMapGen F m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem starRepGen_dimVec (F : Type) [Field F] (m : ℕ) (v : Fin 5) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin 5) _
      starQuiver (starRepGen F m) v ≃ₗ[F]
      (Fin (if v.val = 0 then 2 * (m + 1) else m + 1) → F)) :=
  ⟨LinearEquiv.refl F _⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
-- Bumped from default: the proof body is ~200 lines with many nested have-blocks
-- that exercise typeclass synthesis repeatedly under the `attribute [-instance]`
-- pragma. Matches the bump on the ℂ-specific source `starRep_isIndecomposable`.
set_option maxHeartbeats 1600000 in
theorem starRepGen_isIndecomposable (F : Type) [Field F] (m : ℕ) :
    @Etingof.QuiverRepresentation.IsIndecomposable F _ (Fin 5)
      starQuiver (starRepGen F m) := by
  letI := starQuiver
  constructor
  · -- Nontrivial at leaf 1 (dim m+1 ≥ 1)
    refine ⟨⟨1, by omega⟩, ?_⟩
    change Nontrivial (Fin (if (1 : Fin 5).val = 0 then _ else m + 1) → F)
    simp only [show (1 : Fin 5).val = 1 from rfl, one_ne_zero, ↓reduceIte]
    infer_instance
  · intro W₁ W₂ hW₁_inv hW₂_inv hcompl
    -- Core decomposition: if embed1(x) + embed2(z) ∈ W(center) and both W, W'
    -- have subrepresentation invariance, then x ∈ W(leaf1) and z ∈ W(leaf2).
    have core (W W' : ∀ v, Submodule F ((starRepGen F m).obj v))
        (hW : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W a, (starRepGen F m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starRepGen F m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x z : Fin (m + 1) → F)
        (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ W ⟨0, by omega⟩) :
        x ∈ W ⟨1, by omega⟩ ∧ z ∈ W ⟨2, by omega⟩ := by
      have htop1 := (hc ⟨1, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := x)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop1
      have htop2 := (hc ⟨2, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := z)
      obtain ⟨c, hc2, d, hd, hcd⟩ := Submodule.mem_sup.mp htop2
      have ha0 : starEmbed1_F F m a ∈ W ⟨0, by omega⟩ :=
        hW (show @Quiver.Hom _ starQuiver ⟨1, by omega⟩ ⟨0, by omega⟩ from ⟨⟨by decide, rfl⟩⟩) a ha
      have hc0 : starEmbed2_F F m c ∈ W ⟨0, by omega⟩ :=
        hW (show @Quiver.Hom _ starQuiver ⟨2, by omega⟩ ⟨0, by omega⟩ from ⟨⟨by decide, rfl⟩⟩) c hc2
      have hb0 : starEmbed1_F F m b ∈ W' ⟨0, by omega⟩ :=
        hW' (show @Quiver.Hom _ starQuiver ⟨1, by omega⟩ ⟨0, by omega⟩ from ⟨⟨by decide, rfl⟩⟩) b hb
      have hd0 : starEmbed2_F F m d ∈ W' ⟨0, by omega⟩ :=
        hW' (show @Quiver.Hom _ starQuiver ⟨2, by omega⟩ ⟨0, by omega⟩
          from ⟨⟨by decide, rfl⟩⟩) d hd
      have hsum : starEmbed1_F F m x + starEmbed2_F F m z =
          (starEmbed1_F F m a + starEmbed2_F F m c) +
            (starEmbed1_F F m b + starEmbed2_F F m d) := by
        rw [← hab, ← hcd]; simp [map_add]; abel
      rw [hsum] at hmem
      have hadd : starEmbed1_F F m a + starEmbed2_F F m c ∈ W ⟨0, by omega⟩ :=
        (W ⟨0, by omega⟩).add_mem ha0 hc0
      have hw'_in_W : starEmbed1_F F m b + starEmbed2_F F m d ∈ W ⟨0, by omega⟩ := by
        have hsmul := (W ⟨0, by omega⟩).smul_mem (-1 : F) hadd
        have hadd2 := (W ⟨0, by omega⟩).add_mem hmem hsmul
        have key : starEmbed1_F F m a + starEmbed2_F F m c +
            (starEmbed1_F F m b + starEmbed2_F F m d) +
            (-1 : F) • (starEmbed1_F F m a + starEmbed2_F F m c) =
            starEmbed1_F F m b + starEmbed2_F F m d := by
          ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        rwa [key] at hadd2
      have hzero : starEmbed1_F F m b + starEmbed2_F F m d = 0 := by
        have := Submodule.mem_inf.mpr ⟨hw'_in_W,
          (W' ⟨0, by omega⟩).add_mem hb0 hd0⟩
        rwa [(hc ⟨0, by omega⟩).inf_eq_bot, Submodule.mem_bot] at this
      obtain ⟨hb0', hd0'⟩ := embed_sum_zero_F F m b d hzero
      exact ⟨hab ▸ by rw [hb0', add_zero]; exact ha,
             hcd ▸ by rw [hd0', add_zero]; exact hc2⟩
    -- Leaf 3 (diagonal embedding): x ∈ W(3) → x ∈ W(1) ∧ x ∈ W(2)
    have leaf3_sub (W W' : ∀ v, Submodule F ((starRepGen F m).obj v))
        (hW : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W a, (starRepGen F m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starRepGen F m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x : Fin (m + 1) → F) (hx : x ∈ W ⟨3, by omega⟩) :
        x ∈ W ⟨1, by omega⟩ ∧ x ∈ W ⟨2, by omega⟩ := by
      have hmem := hW (show @Quiver.Hom _ starQuiver ⟨3, by omega⟩ ⟨0, by omega⟩
        from ⟨⟨by decide, rfl⟩⟩) x hx
      change starEmbedDiag_F F m x ∈ W ⟨0, by omega⟩ at hmem
      rw [starEmbedDiag_F, LinearMap.add_apply] at hmem
      exact core W W' hW hW' hc x x hmem
    -- Leaf 4 (nilpotent embedding): x ∈ W(4) → x ∈ W(1) ∧ Nx ∈ W(2)
    have leaf4_sub (W W' : ∀ v, Submodule F ((starRepGen F m).obj v))
        (hW : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W a, (starRepGen F m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starRepGen F m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x : Fin (m + 1) → F) (hx : x ∈ W ⟨4, by omega⟩) :
        x ∈ W ⟨1, by omega⟩ ∧ nilpotentShiftLinGen F m x ∈ W ⟨2, by omega⟩ := by
      have hmem := hW (show @Quiver.Hom _ starQuiver ⟨4, by omega⟩ ⟨0, by omega⟩
        from ⟨⟨by decide, rfl⟩⟩) x hx
      change starEmbedNilp_F F m x ∈ W ⟨0, by omega⟩ at hmem
      rw [starEmbedNilp_F, LinearMap.add_apply, LinearMap.comp_apply] at hmem
      exact core W W' hW hW' hc x (nilpotentShiftLinGen F m x) hmem
    -- If A ≤ B, A' ≤ B', IsCompl A A', IsCompl B B', then A = B
    have compl_eq_of_le (A B A' B' : Submodule F (Fin (m + 1) → F))
        (hAB : A ≤ B) (hA'B' : A' ≤ B')
        (hcA : IsCompl A A') (hcB : IsCompl B B') : A = B := by
      apply le_antisymm hAB; intro x hx
      have hx_top := hcA.sup_eq_top ▸ Submodule.mem_top (x := x)
      obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hx_top
      have ha'_B : a' ∈ B := by
        have h := B.sub_mem hx (hAB ha); rwa [show a + a' - a = a' from by abel] at h
      have : a' ∈ B ⊓ B' := Submodule.mem_inf.mpr ⟨ha'_B, hA'B' ha'⟩
      rw [hcB.inf_eq_bot, Submodule.mem_bot] at this; rwa [this, add_zero]
    -- W₁(3) = W₁(1), W₁(3) = W₁(2), W₁(4) = W₁(1)
    have heq31 : W₁ ⟨3, by omega⟩ = W₁ ⟨1, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf3_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).1)
      (fun x hx => (leaf3_sub W₂ W₁ hW₂_inv hW₁_inv
        (fun v => (hcompl v).symm) x hx).1)
      (hcompl ⟨3, by omega⟩) (hcompl ⟨1, by omega⟩)
    have heq32 : W₁ ⟨3, by omega⟩ = W₁ ⟨2, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf3_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).2)
      (fun x hx => (leaf3_sub W₂ W₁ hW₂_inv hW₁_inv
        (fun v => (hcompl v).symm) x hx).2)
      (hcompl ⟨3, by omega⟩) (hcompl ⟨2, by omega⟩)
    have heq41 : W₁ ⟨4, by omega⟩ = W₁ ⟨1, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf4_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).1)
      (fun x hx => (leaf4_sub W₂ W₁ hW₂_inv hW₁_inv
        (fun v => (hcompl v).symm) x hx).1)
      (hcompl ⟨4, by omega⟩) (hcompl ⟨1, by omega⟩)
    have h12 : W₁ ⟨1, by omega⟩ = W₁ ⟨2, by omega⟩ := heq31.symm.trans heq32
    have hN₁ : ∀ (x : Fin (m + 1) → F),
        x ∈ W₁ ⟨1, by omega⟩ → nilpotentShiftLinGen F m x ∈ W₁ ⟨1, by omega⟩ := by
      intro x hx
      have hx4 : x ∈ W₁ ⟨4, by omega⟩ := by rw [heq41]; exact hx
      have h2 := (leaf4_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx4).2
      exact h12 ▸ h2
    have heq31' : W₂ ⟨3, by omega⟩ = W₂ ⟨1, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf3_sub W₂ W₁ hW₂_inv hW₁_inv (fun v => (hcompl v).symm) x hx).1)
      (fun x hx => (leaf3_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).1)
      ((hcompl ⟨3, by omega⟩).symm) ((hcompl ⟨1, by omega⟩).symm)
    have heq32' : W₂ ⟨3, by omega⟩ = W₂ ⟨2, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf3_sub W₂ W₁ hW₂_inv hW₁_inv (fun v => (hcompl v).symm) x hx).2)
      (fun x hx => (leaf3_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).2)
      ((hcompl ⟨3, by omega⟩).symm) ((hcompl ⟨2, by omega⟩).symm)
    have heq41' : W₂ ⟨4, by omega⟩ = W₂ ⟨1, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf4_sub W₂ W₁ hW₂_inv hW₁_inv (fun v => (hcompl v).symm) x hx).1)
      (fun x hx => (leaf4_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).1)
      ((hcompl ⟨4, by omega⟩).symm) ((hcompl ⟨1, by omega⟩).symm)
    have h12' : W₂ ⟨1, by omega⟩ = W₂ ⟨2, by omega⟩ := heq31'.symm.trans heq32'
    have hN₂ : ∀ (x : Fin (m + 1) → F),
        x ∈ W₂ ⟨1, by omega⟩ → nilpotentShiftLinGen F m x ∈ W₂ ⟨1, by omega⟩ := by
      intro x hx
      have hx4 : x ∈ W₂ ⟨4, by omega⟩ := by rw [heq41']; exact hx
      have h2 := (leaf4_sub W₂ W₁ hW₂_inv hW₁_inv (fun v => (hcompl v).symm)
        x hx4).2
      exact h12' ▸ h2
    have hresult := nilpotent_invariant_compl_trivial_gen
      (nilpotentShiftLinGen F m) (nilpotentShiftLinGen_nilpotent F m)
      (nilpotentShiftLinGen_ker_finrank F m)
      (W₁ ⟨1, by omega⟩) (W₂ ⟨1, by omega⟩) hN₁ hN₂ (hcompl ⟨1, by omega⟩)
    suffices propagate : ∀ (W W' : ∀ v, Submodule F ((starRepGen F m).obj v)),
        (∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starRepGen F m).mapLinear e x ∈ W' b) →
        (∀ v, IsCompl (W v) (W' v)) →
        W ⟨1, by omega⟩ = W ⟨2, by omega⟩ →
        W ⟨3, by omega⟩ = W ⟨1, by omega⟩ →
        W ⟨4, by omega⟩ = W ⟨1, by omega⟩ →
        W ⟨1, by omega⟩ = ⊥ → ∀ v, W v = ⊥ by
      rcases hresult with h | h
      · left; exact propagate W₁ W₂ hW₂_inv hcompl (heq31.symm.trans heq32) heq31 heq41 h
      · right; exact propagate W₂ W₁ hW₁_inv (fun v => (hcompl v).symm)
          (heq31'.symm.trans heq32') heq31' heq41' h
    intro W W' hW'_inv hc h12 h31 h41 hbot v
    fin_cases v
    · change W ⟨0, by omega⟩ = ⊥
      have hW'1_top : W' ⟨1, by omega⟩ = ⊤ := by
        have := (hc ⟨1, by omega⟩).sup_eq_top; rwa [hbot, bot_sup_eq] at this
      have hW'2_top : W' ⟨2, by omega⟩ = ⊤ := by
        have := (hc ⟨2, by omega⟩).sup_eq_top; rwa [← h12, hbot, bot_sup_eq] at this
      have h_emb1 : ∀ (x : Fin (m + 1) → F), starEmbed1_F F m x ∈ W' ⟨0, by omega⟩ :=
        fun x => hW'_inv (show @Quiver.Hom _ starQuiver ⟨1, by omega⟩ ⟨0, by omega⟩
          from ⟨⟨by decide, rfl⟩⟩) x (hW'1_top ▸ Submodule.mem_top)
      have h_emb2 : ∀ (x : Fin (m + 1) → F), starEmbed2_F F m x ∈ W' ⟨0, by omega⟩ :=
        fun x => hW'_inv (show @Quiver.Hom _ starQuiver ⟨2, by omega⟩ ⟨0, by omega⟩
          from ⟨⟨by decide, rfl⟩⟩) x (hW'2_top ▸ Submodule.mem_top)
      rw [eq_bot_iff]; intro (w : Fin (2 * (m + 1)) → F) hw
      have hw' : w ∈ W' ⟨0, by omega⟩ :=
        center_decomp_F F m w ▸ (W' ⟨0, by omega⟩).add_mem (h_emb1 _) (h_emb2 _)
      have := Submodule.mem_inf.mpr ⟨hw, hw'⟩
      rwa [(hc ⟨0, by omega⟩).inf_eq_bot, Submodule.mem_bot] at this
    · exact hbot
    · change W ⟨2, by omega⟩ = ⊥; rw [← h12]; exact hbot
    · change W ⟨3, by omega⟩ = ⊥; rw [h31]; exact hbot
    · change W ⟨4, by omega⟩ = ⊥; rw [h41]; exact hbot

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- F-generic: the star graph K_{1,4} (D̃₄) has infinite representation type
over any field F when oriented as the canonical all-sink `starQuiver`. -/
theorem star_not_finite_type_F (F : Type) [Field F] :
    ¬ Set.Finite
      {d : Fin 5 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0, 0, 0, 0} F (Fin 5) _ starQuiver,
          @Etingof.QuiverRepresentation.IsIndecomposable F _ (Fin 5) starQuiver V ∧
          ∀ v, Nonempty
            (@Etingof.QuiverRepresentation.obj F (Fin 5) _ starQuiver V v ≃ₗ[F]
              (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ,
      (fun v : Fin 5 => if v.val = 0 then 2 * (m + 1) else m + 1) ∈
      {d : Fin 5 → ℕ | ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 5) _ starQuiver,
        @Etingof.QuiverRepresentation.IsIndecomposable F _ (Fin 5) starQuiver V ∧
        ∀ v, Nonempty
          (@Etingof.QuiverRepresentation.obj F (Fin 5) _ starQuiver V v ≃ₗ[F]
            (Fin (d v) → F))} := by
    intro m
    exact ⟨starRepGen F m, starRepGen_isIndecomposable F m, starRepGen_dimVec F m⟩
  have hinj : Function.Injective
      (fun m : ℕ => fun v : Fin 5 => if v.val = 0 then 2 * (m + 1) else m + 1) := by
    intro m₁ m₂ h
    have h1 := congr_fun h ⟨1, by omega⟩
    simp only [one_ne_zero, ↓reduceIte] at h1
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section: Direction-aware leaf maps for orientation-generic K_{1,4}

For an arbitrary orientation `Q` of `starAdj`, each leaf edge `{0, i}` is
oriented one of two ways. The canonical direction `i → 0` uses the
embeddings `starEmbed_i_F`. The reversed direction `0 → i` needs a
projection `V_0 → V_i` that is a left inverse of the corresponding
embedding. Below we define four such projections with pairwise distinct
kernels — each kernel equals the image of one of the other three
embeddings.

Moved here from `FieldGenericInfiniteType.lean` (originally PR #2802,
Sections 7–8) per #2846: the original placement in the shared header
referenced `starEmbed*_F` which now live in `FieldGenericStar.lean`,
breaking the build (a cyclic import would be needed to reach them from
the shared header). The two half-block projections `starFirst_F` and
`starSecond_F` that these projections build on are defined earlier in
this file alongside the embeddings, since the indecomposability proof
also uses them. -/

/-- Projection 1 (F-generic): `(a, b) ↦ a − b`. Left inverse of
`starEmbed1_F`. Kernel = image of `starEmbedDiag_F`. -/
noncomputable def starProj1_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) :=
  starFirst_F F m - starSecond_F F m

/-- Projection 2 (F-generic): `(a, b) ↦ b − N(a)` where `N` is the
nilpotent shift. Left inverse of `starEmbed2_F`. Kernel = image of
`starEmbedNilp_F`. -/
noncomputable def starProj2_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) :=
  starSecond_F F m - (nilpotentShiftLinGen F m).comp (starFirst_F F m)

/-- Projection 3 (F-generic): `(a, b) ↦ b`. Left inverse of
`starEmbedDiag_F`. Kernel = image of `starEmbed1_F`. -/
noncomputable def starProj3_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) :=
  starSecond_F F m

/-- Projection 4 (F-generic): `(a, b) ↦ a`. Left inverse of
`starEmbedNilp_F`. Kernel = image of `starEmbed2_F`. -/
noncomputable def starProj4_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) :=
  starFirst_F F m

/-! ### Left-inverse identities

Each `starProj_i_F` is a left inverse of `starEmbed_i_F`. These identities
are the key linear-algebra facts the downstream indecomposability proof
needs. -/

theorem starFirst_F_starEmbed1_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    starFirst_F F m (starEmbed1_F F m x) = x := by
  ext i
  simp only [starFirst_F, starEmbed1_F, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.isLt]

theorem starFirst_F_starEmbed2_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    starFirst_F F m (starEmbed2_F F m x) = 0 := by
  ext i
  simp only [starFirst_F, starEmbed2_F, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg (by omega)]
  rfl

theorem starSecond_F_starEmbed1_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    starSecond_F F m (starEmbed1_F F m x) = 0 := by
  ext i
  simp only [starSecond_F, starEmbed1_F, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg (by omega)]
  rfl

theorem starSecond_F_starEmbed2_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    starSecond_F F m (starEmbed2_F F m x) = x := by
  ext i
  simp only [starSecond_F, starEmbed2_F, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos (by omega)]
  congr 1
  apply Fin.ext
  simp

theorem starProj1_F_starEmbed1_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    starProj1_F F m (starEmbed1_F F m x) = x := by
  simp [starProj1_F, LinearMap.sub_apply,
    starFirst_F_starEmbed1_F, starSecond_F_starEmbed1_F]

theorem starProj2_F_starEmbed2_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    starProj2_F F m (starEmbed2_F F m x) = x := by
  simp [starProj2_F, LinearMap.sub_apply, LinearMap.comp_apply,
    starFirst_F_starEmbed2_F, starSecond_F_starEmbed2_F, map_zero]

theorem starProj3_F_starEmbedDiag_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    starProj3_F F m (starEmbedDiag_F F m x) = x := by
  simp [starProj3_F, starEmbedDiag_F, LinearMap.add_apply,
    starSecond_F_starEmbed1_F, starSecond_F_starEmbed2_F]

theorem starProj4_F_starEmbedNilp_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    starProj4_F F m (starEmbedNilp_F F m x) = x := by
  simp [starProj4_F, starEmbedNilp_F, LinearMap.add_apply, LinearMap.comp_apply,
    starFirst_F_starEmbed1_F, starFirst_F_starEmbed2_F]

/-! ### Reversed-leaf projection surjectivity

Each `starProj_i_F` is surjective: the corresponding embedding `starEmbed_i_F`
is a right inverse (`starProj_i_F (starEmbed_i_F x) = x`), so surjectivity
follows from `Function.RightInverse.surjective`. These are exactly the
`Function.Surjective p` hypotheses that `reversed_leaf_subspace_eq` needs at
each leaf oriented `0 → i` in the orientation-generic indecomposability
proof. -/

theorem starProj1_F_surjective (F : Type) [Field F] (m : ℕ) :
    Function.Surjective (starProj1_F F m) :=
  Function.RightInverse.surjective (starProj1_F_starEmbed1_F F m)

theorem starProj2_F_surjective (F : Type) [Field F] (m : ℕ) :
    Function.Surjective (starProj2_F F m) :=
  Function.RightInverse.surjective (starProj2_F_starEmbed2_F F m)

theorem starProj3_F_surjective (F : Type) [Field F] (m : ℕ) :
    Function.Surjective (starProj3_F F m) :=
  Function.RightInverse.surjective (starProj3_F_starEmbedDiag_F F m)

theorem starProj4_F_surjective (F : Type) [Field F] (m : ℕ) :
    Function.Surjective (starProj4_F F m) :=
  Function.RightInverse.surjective (starProj4_F_starEmbedNilp_F F m)

/-! ### Directness transfer

A pure submodule-lattice companion to `compl_le_forces_eq`. Where
`compl_le_forces_eq` collapses `A ≤ B` between two complementary *pairs*
via a finrank count, this one starts from the *lower* pair already
spanning the whole space and needs no dimension argument. It is the key
step that lets the orientation-generic K_{1,4} proof pin a leaf subspace
from the center: a surjective reversed-leaf projection sends a center
complement pair `(W₁ 0, W₂ 0)` to a pair that spans the leaf (`⊔ = ⊤`),
and the leaf's own complement pair bounds it from above, so the two must
coincide. -/

/-- If `A₁ ⊔ A₂ = ⊤`, `A₁ ≤ B₁`, `A₂ ≤ B₂` and `B₁, B₂` are
complementary, then `A₁ = B₁` and `A₂ = B₂`. The two lower spaces, already
spanning the whole space, must fill their complementary upper bounds
exactly. No finite-dimensionality required. -/
theorem sup_top_le_isCompl_forces_eq
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (A₁ A₂ B₁ B₂ : Submodule F V)
    (htop : A₁ ⊔ A₂ = ⊤) (h1 : A₁ ≤ B₁) (h2 : A₂ ≤ B₂)
    (hB : IsCompl B₁ B₂) :
    A₁ = B₁ ∧ A₂ = B₂ := by
  have hB1 : B₁ ≤ A₁ := by
    intro b hb
    have hb_top : b ∈ A₁ ⊔ A₂ := htop ▸ Submodule.mem_top
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp hb_top
    have ha₂B1 : a₂ ∈ B₁ := by
      have hsub : a₂ = (a₁ + a₂) - a₁ := by abel
      rw [hsub]; exact B₁.sub_mem hb (h1 ha₁)
    have : a₂ ∈ B₁ ⊓ B₂ := Submodule.mem_inf.mpr ⟨ha₂B1, h2 ha₂⟩
    rw [hB.inf_eq_bot, Submodule.mem_bot] at this
    rw [this, add_zero]; exact ha₁
  have hB2 : B₂ ≤ A₂ := by
    intro b hb
    have hb_top : b ∈ A₁ ⊔ A₂ := htop ▸ Submodule.mem_top
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp hb_top
    have ha₁B2 : a₁ ∈ B₂ := by
      have hsub : a₁ = (a₁ + a₂) - a₂ := by abel
      rw [hsub]; exact B₂.sub_mem hb (h2 ha₂)
    have : a₁ ∈ B₁ ⊓ B₂ := Submodule.mem_inf.mpr ⟨h1 ha₁, ha₁B2⟩
    rw [hB.inf_eq_bot, Submodule.mem_bot] at this
    rw [this, zero_add]; exact ha₂
  exact ⟨le_antisymm h1 hB1, le_antisymm h2 hB2⟩

/-- **Reversed-leaf subspace reduction (abstract form).** When a leaf edge
is oriented *into* the leaf (`0 → i`, the reversed direction), its map is a
surjective projection `p : V₀ → Vᵢ`. Subrepresentation invariance then
gives `map p (W 0) ≤ W i` for both halves of a complementary pair, and
because `p` is surjective the two images already span `Vᵢ`. By
`sup_top_le_isCompl_forces_eq` the leaf subspaces are therefore *exactly*
the projected center subspaces: `W i = map p (W 0)`. This is the crux
reduction for every reversed leaf in the orientation-generic D̃/star
indecomposability proofs — the entire leaf datum is determined by the
center. -/
theorem reversed_leaf_subspace_eq
    {F : Type*} [Field F] {V₀ Vᵢ : Type*}
    [AddCommGroup V₀] [Module F V₀] [AddCommGroup Vᵢ] [Module F Vᵢ]
    (p : V₀ →ₗ[F] Vᵢ) (hp : Function.Surjective p)
    (U₁ U₂ : Submodule F V₀) (Wi₁ Wi₂ : Submodule F Vᵢ)
    (hU : IsCompl U₁ U₂) (hWi : IsCompl Wi₁ Wi₂)
    (h1 : U₁.map p ≤ Wi₁) (h2 : U₂.map p ≤ Wi₂) :
    Wi₁ = U₁.map p ∧ Wi₂ = U₂.map p := by
  have htop : U₁.map p ⊔ U₂.map p = ⊤ := by
    rw [← Submodule.map_sup, hU.sup_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr hp]
  obtain ⟨e1, e2⟩ := sup_top_le_isCompl_forces_eq _ _ _ _ htop h1 h2 hWi
  exact ⟨e1.symm, e2.symm⟩

/-- General directness primitive: if the lower pair `(A₁, A₂)` already
sups above the upper pair `(B₁, B₂)`, each `Aₖ ≤ Bₖ`, and the upper pair
meets trivially, then the pairs coincide. Generalises
`sup_top_le_isCompl_forces_eq` by replacing the ambient `⊤` with the
common sup `A₁ ⊔ A₂`; used for the forward-leaf reduction, where the
relevant ambient is `range e` rather than the whole space. -/
theorem submodule_pair_eq_of_sup_le_of_inf_bot
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (A₁ A₂ B₁ B₂ : Submodule F V)
    (h1 : A₁ ≤ B₁) (h2 : A₂ ≤ B₂)
    (hsup : B₁ ⊔ B₂ ≤ A₁ ⊔ A₂) (hinf : B₁ ⊓ B₂ = ⊥) :
    A₁ = B₁ ∧ A₂ = B₂ := by
  have hB1 : B₁ ≤ A₁ := by
    intro b hb
    have hb_top : b ∈ A₁ ⊔ A₂ := hsup (Submodule.mem_sup_left hb)
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp hb_top
    have ha₂B1 : a₂ ∈ B₁ := by
      have hsub : a₂ = (a₁ + a₂) - a₁ := by abel
      rw [hsub]; exact B₁.sub_mem hb (h1 ha₁)
    have : a₂ ∈ B₁ ⊓ B₂ := Submodule.mem_inf.mpr ⟨ha₂B1, h2 ha₂⟩
    rw [hinf, Submodule.mem_bot] at this
    rw [this, add_zero]; exact ha₁
  have hB2 : B₂ ≤ A₂ := by
    intro b hb
    have hb_top : b ∈ A₁ ⊔ A₂ := hsup (Submodule.mem_sup_right hb)
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp hb_top
    have ha₁B2 : a₁ ∈ B₂ := by
      have hsub : a₁ = (a₁ + a₂) - a₂ := by abel
      rw [hsub]; exact B₂.sub_mem hb (h2 ha₂)
    have : a₁ ∈ B₁ ⊓ B₂ := Submodule.mem_inf.mpr ⟨h1 ha₁, ha₁B2⟩
    rw [hinf, Submodule.mem_bot] at this
    rw [this, zero_add]; exact ha₂
  exact ⟨le_antisymm h1 hB1, le_antisymm h2 hB2⟩

/-- **Forward-leaf subspace reduction (abstract form).** A leaf edge
oriented *out of* the leaf (`i → 0`, the canonical direction) has an
injective embedding `e : Vᵢ → V₀` as its map. Invariance gives
`map e (W i) ≤ W 0` for both halves of a complementary pair, and since the
two leaf images sup to `range e`, each is pinned to `W 0 ⊓ range e`. Dual
to `reversed_leaf_subspace_eq`: together they reduce every leaf datum of
the orientation-generic D̃/star representations to the center subspace. -/
theorem forward_leaf_subspace_eq
    {F : Type*} [Field F] {V₀ Vᵢ : Type*}
    [AddCommGroup V₀] [Module F V₀] [AddCommGroup Vᵢ] [Module F Vᵢ]
    (e : Vᵢ →ₗ[F] V₀)
    (Wi₁ Wi₂ : Submodule F Vᵢ) (U₁ U₂ : Submodule F V₀)
    (hWi : IsCompl Wi₁ Wi₂) (hU : IsCompl U₁ U₂)
    (h1 : Wi₁.map e ≤ U₁) (h2 : Wi₂.map e ≤ U₂) :
    Wi₁.map e = U₁ ⊓ LinearMap.range e ∧
      Wi₂.map e = U₂ ⊓ LinearMap.range e := by
  have hrange : Wi₁.map e ⊔ Wi₂.map e = LinearMap.range e := by
    rw [← Submodule.map_sup, hWi.sup_eq_top, Submodule.map_top]
  have hmr : ∀ W : Submodule F Vᵢ, W.map e ≤ LinearMap.range e :=
    fun W => le_trans (Submodule.map_mono le_top) (Submodule.map_top e).le
  have h1' : Wi₁.map e ≤ U₁ ⊓ LinearMap.range e := le_inf h1 (hmr _)
  have h2' : Wi₂.map e ≤ U₂ ⊓ LinearMap.range e := le_inf h2 (hmr _)
  refine submodule_pair_eq_of_sup_le_of_inf_bot _ _ _ _ h1' h2' ?_ ?_
  · rw [hrange]; exact sup_le inf_le_right inf_le_right
  · have hle : (U₁ ⊓ LinearMap.range e) ⊓ (U₂ ⊓ LinearMap.range e) ≤ U₁ ⊓ U₂ :=
      le_inf (le_trans inf_le_left inf_le_left) (le_trans inf_le_right inf_le_left)
    rw [hU.inf_eq_bot] at hle
    exact le_bot_iff.mp hle

/-! ## Section: Orientation-generic K_{1,4} representation

`starRep_kQ` matches `starRepGen` at the canonical orientation and uses the
projections `starProj_i_F` at reversed leaf edges. The same object map and
dimension vector `(2(m+1), m+1, m+1, m+1, m+1)` regardless of `Q`. -/

/-- Match-based map for the orientation-generic K_{1,4} representation. -/
private noncomputable def starRepMap_kQ (F : Type) [Field F] (m : ℕ) (a b : Fin 5) :
    (Fin (if a.val = 0 then 2 * (m + 1) else m + 1) → F) →ₗ[F]
    (Fin (if b.val = 0 then 2 * (m + 1) else m + 1) → F) :=
  match a, b with
  | ⟨1, _⟩, ⟨0, _⟩ => starEmbed1_F F m
  | ⟨2, _⟩, ⟨0, _⟩ => starEmbed2_F F m
  | ⟨3, _⟩, ⟨0, _⟩ => starEmbedDiag_F F m
  | ⟨4, _⟩, ⟨0, _⟩ => starEmbedNilp_F F m
  | ⟨0, _⟩, ⟨1, _⟩ => starProj1_F F m
  | ⟨0, _⟩, ⟨2, _⟩ => starProj2_F F m
  | ⟨0, _⟩, ⟨3, _⟩ => starProj3_F F m
  | ⟨0, _⟩, ⟨4, _⟩ => starProj4_F F m
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic K_{1,4} (D̃₄) representation over `F` with arbitrary
orientation `Q`. Dimension vector `(2(m+1), m+1, m+1, m+1, m+1)`. -/
noncomputable def starRep_kQ
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 5))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 5) Q a b)]
    (_hOrient : @Etingof.IsOrientationOf 5 Q starAdj)
    (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin 5) _ Q := by
  letI := Q
  exact {
    obj := fun v => Fin (if v.val = 0 then 2 * (m + 1) else m + 1) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => starRepMap_kQ F m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem starRep_kQ_dimVec
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 5))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 5) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 5 Q starAdj)
    (m : ℕ) (v : Fin 5) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin 5) _ Q
      (starRep_kQ F Q hOrient m) v ≃ₗ[F]
      (Fin (if v.val = 0 then 2 * (m + 1) else m + 1) → F)) :=
  ⟨LinearEquiv.refl F _⟩

/-! ## Section: Reduction of `starRep_kQ` to `starRepGen` at the canonical orientation

At the canonical all-sink orientation `starQuiver` the orientation-generic
representation `starRep_kQ` coincides with the canonical F-generic representation
`starRepGen`. The two have the same object family, instances, and dimension
vector; their arrow maps agree on every arrow of `starQuiver` — all of the form
leaf `i → 0`, where `starRepMap_kQ` and `starRepMapGen` select the same
embedding. The reversed-edge arms of `starRepMap_kQ` (`0 → i`, using the
projections `starProj_i_F`) are never reached because `starQuiver` has no such
arrow. This lets the canonical-orientation indecomposability of `starRep_kQ`
reuse `starRepGen_isIndecomposable` instead of reproving the ~210-line argument
(review #2816 Q3, issue #2823). -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The orientation-generic K_{1,4} representation at the canonical orientation
`starQuiver` equals the canonical F-generic representation `starRepGen`. -/
theorem starRep_kQ_canonical_eq_starRepGen
    (F : Type) [Field F] (m : ℕ)
    (hOrient : @Etingof.IsOrientationOf 5 starQuiver starAdj) :
    starRep_kQ F starQuiver hOrient m = starRepGen F m := by
  letI : Quiver (Fin 5) := starQuiver
  -- The two arrow maps agree on every arrow of `starQuiver`: such an arrow `a → b`
  -- forces `a.val ≠ 0` and `b.val = 0`, i.e. a leaf `i → 0`, where both `starRepMap_kQ`
  -- and `starRepMapGen` select the same embedding. On every other index pair an arrow
  -- cannot exist (`b.val = 0` is contradicted), so the reversed-edge arms are unreached.
  have hmap : ∀ (a b : Fin 5), @Quiver.Hom (Fin 5) starQuiver a b →
      starRepMap_kQ F m a b = starRepMapGen F m a b := by
    intro a b e
    obtain ⟨ha, hb⟩ := e.down
    fin_cases a <;> fin_cases b <;>
      first
        | rfl
        | exact absurd hb (by decide)
  unfold starRep_kQ starRepGen
  congr 1
  funext a b e
  exact hmap a b e

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Canonical-orientation indecomposability of `starRep_kQ`, obtained from
`starRepGen_isIndecomposable` via `starRep_kQ_canonical_eq_starRepGen`. This is
the canonical-orientation half of the `star_not_finite_type_per_kQ` deliverable
(issue #2801); the general orientation `Q` is handled separately. -/
theorem starRep_kQ_canonical_isIndecomposable
    (F : Type) [Field F] (m : ℕ)
    (hOrient : @Etingof.IsOrientationOf 5 starQuiver starAdj) :
    @Etingof.QuiverRepresentation.IsIndecomposable F _ (Fin 5) starQuiver
      (starRep_kQ F starQuiver hOrient m) := by
  rw [starRep_kQ_canonical_eq_starRepGen]
  exact starRepGen_isIndecomposable F m

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- **Orientation-generic indecomposability of `starRep_kQ`** (issue #2801,
center-crux sub #4523). For any field `F`, any orientation `Q` of `starAdj`,
and any `m`, the K_{1,4} (D̃₄) representation `starRep_kQ F Q hOrient m` is
indecomposable.

**WARNING (issue #4566): this statement is FALSE and its `sorry` cannot be
filled.** For the orientation that reverses the diagonal leaf 3, the
representation is decomposable for every `m ≥ 1`; see the machine-checked
refutation `starRep_kQ_reversedLeaf3_decomposable` (end of this file). The
construction needs the homogeneous-tube redesign of issue #4566 before any
orientation-generic indecomposability can hold. The canonical all-sink
orientation is genuinely indecomposable
(`starRep_kQ_canonical_isIndecomposable`), and the downstream
`star_not_finite_type_per_kQ` remains true on other grounds (D̃₄ is affine).

The nontriviality half is proven here (leaf 1 has dimension `m + 1 ≥ 1`). The
no-nontrivial-decomposition half is the orientation-generic D̃₄ center crux,
deferred to the body `sorry`:

* Each leaf edge `{0, i}` is oriented `i → 0` (forward, map `starEmbed_i_F`)
  or `0 → i` (reversed, map `starProj_i_F`). The landed per-leaf reductions
  `forward_leaf_subspace_eq` / `reversed_leaf_subspace_eq` (the latter using
  the `starProj_i_F_surjective` facts in this file) pin every leaf subspace
  to the center subspace `U₁ := W₁ 0 ⊆ V₀`.
* The genuinely hard part — forcing `U₁ ∈ {⊥, ⊤}` from the four images in
  general position plus the nilpotent twist `N` at leaf 4 (reusing
  `nilpotent_invariant_compl_trivial_gen`), then propagating to every
  vertex — is the D̃₄ instance of the project-wide tree-indecomposability
  wall (the analogous D̃₅/D̃₆/D̃₇/Ẽ₆/Ẽ₇ bodies are likewise sorry-deferred).

The canonical all-forward orientation is fully proven and reachable via
`starRep_kQ_canonical_isIndecomposable`; this theorem subsumes it for the
general `Q`. -/
theorem starRep_kQ_isIndecomposable
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 5))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 5) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 5 Q starAdj)
    (m : ℕ) :
    (starRep_kQ F Q hOrient m).IsIndecomposable := by
  constructor
  · -- Nontrivial at leaf 1 (dimension `m + 1 ≥ 1`).
    refine ⟨⟨1, by omega⟩, ?_⟩
    change Nontrivial (Fin (if (1 : Fin 5).val = 0 then 2 * (m + 1) else m + 1) → F)
    simp only [show (1 : Fin 5).val = 1 from rfl, one_ne_zero, ↓reduceIte]
    infer_instance
  · -- Orientation-generic D̃₄ center crux + propagation. Tracked sub-issue of
    -- #2801; see the docstring above for the reduction roadmap.
    let _ := hOrient
    sorry

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) version of `star_not_finite_type`: for any
algebraically closed field `F` and any orientation `Q` of `starAdj`, the
set of dimension vectors of indecomposable representations of `Q` over
`F` is infinite.

This theorem carries no direct `sorry`, but transitively depends on
`starRep_kQ_isIndecomposable`, whose center-crux body is deferred (see its
docstring). The dimension vectors of the family `starRep_kQ F Q hOrient m`
(value `2(m+1)` at the center, `m+1` at every leaf) are pairwise distinct, so
the indecomposable dimension-vector set is infinite. Mirrors the proof of
`star_not_finite_type_F`. -/
theorem star_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 5))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 5) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 5 Q starAdj) :
    ¬ Set.Finite
      {d : Fin 5 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 5) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ,
      (fun v : Fin 5 => if v.val = 0 then 2 * (m + 1) else m + 1) ∈
      {d : Fin 5 → ℕ | ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 5) _ Q,
        V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨starRep_kQ F Q hOrient m, starRep_kQ_isIndecomposable F Q hOrient m,
      starRep_kQ_dimVec F Q hOrient m⟩
  have hinj : Function.Injective
      (fun m : ℕ => fun v : Fin 5 => if v.val = 0 then 2 * (m + 1) else m + 1) := by
    intro m₁ m₂ h
    have h1 := congr_fun h ⟨1, by omega⟩
    simp only [one_ne_zero, ↓reduceIte] at h1
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section: Per-(F, Q) subgraph dispatch wrapper for K_{1,4}

Mirrors `star_subgraph_not_finite_type` (`InfiniteTypeConstructions.lean:1133`):
given a center vertex and four pairwise non-adjacent leaves, conclude that
the per-(F, Q) representation set of indecomposable dimension vectors is
infinite. Inherits the `sorry` chain of `star_not_finite_type_per_kQ`
(tracked by #2789 / #2801).

Placed here (rather than in `FieldGenericInfiniteType.lean` next to
`subgraph_infinite_type_transfer_per_kQ`) because it depends on
`star_not_finite_type_per_kQ`, which lives in this file; the import graph
runs `FieldGenericInfiniteType → FieldGenericStar`, not the reverse.
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `star_subgraph_not_finite_type`: a graph
containing a `K_{1,4}` subgraph (a center vertex with four pairwise
non-adjacent leaves) has infinite representation type for every
algebraically closed `F` and every orientation `Q`. -/
theorem star_subgraph_not_finite_type_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hadj_symm : adj.IsSymm)
    (hadj_diag : ∀ v, adj v v = 0)
    (center : Fin n) (leaves : Fin 4 ↪ Fin n)
    (hleaves_ne : ∀ i, leaves i ≠ center)
    (hadj_edge : ∀ i, adj center (leaves i) = 1)
    (hadj_indep : ∀ i j, adj (leaves i) (leaves j) = 0)
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- Construct embedding φ : Fin 5 ↪ Fin n mapping 0 ↦ center, k+1 ↦ leaves k.
  have h_leaf (i : Fin 5) (h : i.val ≠ 0) : i.val - 1 < 4 := by omega
  let φ_fun : Fin 5 → Fin n := fun i =>
    if h : i.val = 0 then center
    else leaves ⟨i.val - 1, h_leaf i h⟩
  have hφ_inj : Function.Injective φ_fun := by
    intro a b hab
    simp only [φ_fun] at hab
    by_cases ha0 : a.val = 0 <;> by_cases hb0 : b.val = 0
    · exact Fin.ext (by omega)
    · exfalso; rw [dif_pos ha0, dif_neg hb0] at hab; exact hleaves_ne _ hab.symm
    · exfalso; rw [dif_neg ha0, dif_pos hb0] at hab; exact hleaves_ne _ hab
    · rw [dif_neg ha0, dif_neg hb0] at hab
      have h := congr_arg Fin.val (leaves.injective hab)
      simp at h
      exact Fin.ext (by omega)
  let φ : Fin 5 ↪ Fin n := ⟨φ_fun, hφ_inj⟩
  -- Verify adjacency embedding condition: starAdj i j = adj (φ i) (φ j).
  have hembed : ∀ i j, starAdj i j = adj (φ i) (φ j) := by
    intro i j
    change (if (i.val = 0 ∧ j.val ≠ 0) ∨ (i.val ≠ 0 ∧ j.val = 0) then (1 : ℤ) else 0) =
      adj (φ_fun i) (φ_fun j)
    by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
    · -- center-center
      rw [if_neg (by rintro (⟨-, h⟩ | ⟨h, -⟩) <;> contradiction)]
      simp only [φ_fun, dif_pos hi0, dif_pos hj0]
      exact (hadj_diag center).symm
    · -- center-leaf
      rw [if_pos (Or.inl ⟨hi0, hj0⟩)]
      simp only [φ_fun, dif_pos hi0, dif_neg hj0]
      exact (hadj_edge ⟨j.val - 1, h_leaf j hj0⟩).symm
    · -- leaf-center
      rw [if_pos (Or.inr ⟨hi0, hj0⟩)]
      simp only [φ_fun, dif_neg hi0, dif_pos hj0]
      exact ((hadj_symm.apply center (leaves ⟨i.val - 1, h_leaf i hi0⟩)).trans
        (hadj_edge ⟨i.val - 1, h_leaf i hi0⟩)).symm
    · -- leaf-leaf
      rw [if_neg (by rintro (⟨h, -⟩ | ⟨-, h⟩) <;> contradiction)]
      simp only [φ_fun, dif_neg hi0, dif_neg hj0]
      exact (hadj_indep ⟨i.val - 1, h_leaf i hi0⟩ ⟨j.val - 1, h_leaf j hj0⟩).symm
  exact subgraph_infinite_type_transfer_per_kQ φ F Q
    (star_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `degree_ge_4_infinite_type`: a graph with a
vertex of degree ≥ 4 has infinite representation type for every
algebraically closed `F` and every orientation `Q`.

Either four neighbors are pairwise non-adjacent (dispatch to
`star_subgraph_not_finite_type_per_kQ`) or two neighbors are adjacent,
giving a triangle (dispatch to `triangle_infinite_type_per_kQ`). Mirrors
`degree_ge_4_infinite_type` (`InfiniteTypeConstructions.lean:4064`). -/
theorem degree_ge_4_infinite_type_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (v : Fin n) (hv : 4 ≤ vertexDegree adj v)
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- Get 4 distinct neighbors of v
  set S := Finset.univ.filter (fun w => adj v w = 1) with hS_def
  have hS_card : 4 ≤ S.card := hv
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS_card
  have hT_fin : Fintype T := inferInstance
  have hT_card : Fintype.card T = 4 := by rwa [Fintype.card_coe]
  let e := (Fintype.equivFinOfCardEq hT_card).symm
  let neighbors : Fin 4 → Fin n := fun i => (e i).val
  have h_adj : ∀ i, adj v (neighbors i) = 1 := by
    intro i; exact (Finset.mem_filter.mp (hTS (e i).prop)).2
  have h_ne : ∀ i, neighbors i ≠ v := by
    intro i hc; have := h_adj i; rw [← hc, hdiag] at this; exact one_ne_zero this.symm
  have h_inj : Function.Injective neighbors := by
    intro a b hab; exact (e.injective (Subtype.val_injective hab))
  -- Case split: are any two neighbors adjacent?
  by_cases h_indep : ∀ i j, adj (neighbors i) (neighbors j) = 0
  · -- All pairwise non-adjacent: dispatch to star_subgraph_not_finite_type_per_kQ
    exact star_subgraph_not_finite_type_per_kQ adj hsymm hdiag v
      ⟨neighbors, h_inj⟩ h_ne h_adj h_indep F Q hOrient
  · -- Two neighbors are adjacent: triangle v - neighbors i - neighbors j
    push_neg at h_indep
    obtain ⟨i, j, h_adj_ij⟩ := h_indep
    have h_nonzero : adj (neighbors i) (neighbors j) ≠ 0 := by
      intro hc; exact h_adj_ij hc
    have h_one : adj (neighbors i) (neighbors j) = 1 := by
      rcases h01 (neighbors i) (neighbors j) with h | h
      · exact absurd h h_nonzero
      · exact h
    have hij : neighbors i ≠ neighbors j := by
      intro hc; rw [hc, hdiag] at h_one; exact one_ne_zero h_one.symm
    exact triangle_infinite_type_per_kQ adj hsymm hdiag h01 v (neighbors i) (neighbors j)
      (h_ne i).symm hij (h_ne j).symm
      (h_adj i) h_one (h_adj j) F Q hOrient

/-! ## Shared nilpotent-inverse infrastructure `(I - N)⁻¹`

The cumulative right-tail sum map `cumTailSumLin` is the explicit inverse
`M = (I - N)⁻¹` of `(I - nilpotentShiftLinGen)`, where `N` is nilpotent so
the geometric series `M = I + N + N² + ⋯ + Nᵐ` terminates. The key fact is
the telescoping inversion identity `cumTailSumLin (v - N v) = v`
(`cumTailSumLin_oneSubNilp`).

Relocated here from `FieldGenericD5Tilde.lean` (#4554) so the whole D̃-family
(`d5`/`d6`/`d7`/`d8`) can reuse it: the reversed γ-edge maps and the
mixed-direction leaf arguments all need `(I - N)⁻¹` to strip the `(I - N)`
twist that the γ-coupling introduces. The nilpotent shift itself
(`nilpotentShiftLinGen` / `nilpotentShiftMatrixGen`) already lives in
`FieldGenericInfiniteType.lean`. -/

/-- Cumulative right-tail sum matrix: upper triangular with `1`s on and
above the diagonal. `cumTailSumMatrix[i][j] = 1` iff `i ≤ j`. -/
noncomputable def cumTailSumMatrix (F : Type) [Field F] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  fun i j => if i.val ≤ j.val then 1 else 0

/-- The cumulative right-tail sum linear map
`w ↦ (i ↦ Σ_{j=i}^{m} w_j)`, equivalently `(I - N)⁻¹` for the nilpotent
shift `N`. Defined as `Matrix.mulVecLin (cumTailSumMatrix F m)`. -/
noncomputable def cumTailSumLin (F : Type) [Field F] (m : ℕ) :
    (Fin (m + 1) → F) →ₗ[F] (Fin (m + 1) → F) :=
  Matrix.mulVecLin (cumTailSumMatrix F m)

/-- Closed-form right-tail sum:
`cumTailSumLin F m v i = ∑_{j : Fin (m+1), i.val ≤ j.val} v j`. -/
theorem cumTailSumLin_apply (F : Type) [Field F] (m : ℕ)
    (v : Fin (m + 1) → F) (i : Fin (m + 1)) :
    cumTailSumLin F m v i =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (m + 1) => i.val ≤ j.val), v j := by
  simp only [cumTailSumLin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    cumTailSumMatrix, Finset.sum_filter, ite_mul, one_mul, zero_mul]

/-- Boundary case for `cumTailSumLin`: at index `m`, the right-tail sum
collapses to a single term `v ⟨m, _⟩`. -/
theorem cumTailSumLin_apply_last (F : Type) [Field F] (m : ℕ) (v : Fin (m + 1) → F) :
    cumTailSumLin F m v ⟨m, lt_add_one m⟩ = v ⟨m, lt_add_one m⟩ := by
  rw [cumTailSumLin_apply]
  apply Finset.sum_eq_single (⟨m, lt_add_one m⟩ : Fin (m + 1))
  · intro j hj hjne
    exfalso
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have : j.val = m := le_antisymm (by have := j.isLt; omega) hj
    exact hjne (Fin.ext this)
  · intro habs
    exfalso; apply habs; simp

/-- Recursive step for `cumTailSumLin`: splits off the index-`i` term,
yielding `M v ⟨i, _⟩ = v ⟨i, _⟩ + M v ⟨i + 1, _⟩` whenever `i + 1` is in
range. -/
theorem cumTailSumLin_apply_succ (F : Type) [Field F] (m : ℕ)
    (v : Fin (m + 1) → F) (i : ℕ) (hi : i + 1 < m + 1) :
    cumTailSumLin F m v ⟨i, by omega⟩ =
      v ⟨i, by omega⟩ + cumTailSumLin F m v ⟨i + 1, hi⟩ := by
  rw [cumTailSumLin_apply, cumTailSumLin_apply]
  have hmem : (⟨i, by omega⟩ : Fin (m + 1)) ∈
      Finset.univ.filter (fun j : Fin (m + 1) => i ≤ j.val) := by simp
  rw [← Finset.sum_erase_add _ _ hmem, add_comm]
  congr 1
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · rintro ⟨hne, hij⟩
    have hne' : j.val ≠ i := fun h => hne (Fin.ext h)
    omega
  · intro hij
    refine ⟨?_, by omega⟩
    intro h
    have hjv : j.val = i := by
      have := congr_arg Fin.val h
      simpa using this
    omega

/-- `cumTailSumLin` inverts `I - nilpotentShiftLinGen`: telescoping sum
`M (v - N v) = v`. This is the key algebraic identity that makes the
closed-form γ⁻¹ maps true two-sided inverses on the leaf-embedding
patterns, and the tool used to strip the `(I - N)` twist in the
mixed-direction leaf arguments across the D̃-family.

Proof: reverse induction on `i.val`. Base case `i.val = m` uses
`cumTailSumLin_apply_last`; the inductive step uses
`cumTailSumLin_apply_succ` to split off the index-`i` term, the closed
form for `nilpotentShiftLinGen`, and the induction hypothesis at
`i + 1`. -/
theorem cumTailSumLin_oneSubNilp (F : Type) [Field F] (m : ℕ)
    (v : Fin (m + 1) → F) :
    cumTailSumLin F m (v - nilpotentShiftLinGen F m v) = v := by
  -- Closed form for `nilpotentShiftLinGen F m v`.
  have hN : ∀ j : Fin (m + 1), nilpotentShiftLinGen F m v j =
      if h : j.val + 1 < m + 1 then v ⟨j.val + 1, h⟩ else 0 := by
    intro j
    simp only [nilpotentShiftLinGen, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      nilpotentShiftMatrixGen]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨j.val + 1, h⟩]
      · simp
      · intro b _ hb; simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
        intro hbi; exact hb (Fin.ext (by omega))
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · apply Finset.sum_eq_zero; intro c _
      simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
      intro hji; exact h (by have := c.isLt; omega)
  ext ⟨i, hi⟩
  -- Reverse induction on `m - i` (equivalently, induct on `k = m - i` going
  -- from `0` (i.e. `i = m`) up to `m` (i.e. `i = 0`)).
  suffices key : ∀ k : ℕ, ∀ i' (hi' : i' < m + 1), i' + k = m →
      cumTailSumLin F m (v - nilpotentShiftLinGen F m v) ⟨i', hi'⟩ = v ⟨i', hi'⟩ from
    key (m - i) i hi (by omega)
  intro k
  induction k with
  | zero =>
    intro i' hi' heq
    have hi_eq_m : i' = m := by omega
    subst hi_eq_m
    have hidx : (⟨i', hi'⟩ : Fin (i' + 1)) = ⟨i', lt_add_one i'⟩ := rfl
    rw [hidx, cumTailSumLin_apply_last, Pi.sub_apply, hN]
    simp only [show ¬(i' + 1 < i' + 1) by omega, dite_false, sub_zero]
  | succ n ih =>
    intro i' hi' heq
    have hi1 : i' + 1 < m + 1 := by omega
    rw [cumTailSumLin_apply_succ _ _ _ _ hi1]
    rw [ih (i' + 1) hi1 (by omega)]
    rw [Pi.sub_apply, hN]
    simp only [dif_pos hi1]
    ring

/-- The other-sided inverse identity: `(I - N) ∘ M = I`, i.e.
`cumTailSumLin v - N (cumTailSumLin v) = v`. Together with
`cumTailSumLin_oneSubNilp` (`M ∘ (I - N) = I`) this exhibits
`cumTailSumLin = M` as the genuine **two-sided** inverse of
`I - nilpotentShiftLinGen`, which is what packaging `d5tildeGamma_F` as a
`LinearEquiv` requires (the `γ ∘ γ⁻¹ = id` direction needs `(I - N) M = I`,
not just `M (I - N) = I`).

Unlike `cumTailSumLin_oneSubNilp` this needs no reverse induction: at index
`i < m` the recursion `M v ⟨i⟩ = v ⟨i⟩ + M v ⟨i+1⟩` (`cumTailSumLin_apply_succ`)
cancels the shifted term `N (M v) ⟨i⟩ = M v ⟨i+1⟩` directly, and at index `m`
the shift vanishes while `M v ⟨m⟩ = v ⟨m⟩` (`cumTailSumLin_apply_last`). -/
theorem oneSubNilp_cumTailSumLin (F : Type) [Field F] (m : ℕ)
    (v : Fin (m + 1) → F) :
    cumTailSumLin F m v - nilpotentShiftLinGen F m (cumTailSumLin F m v) = v := by
  -- Closed form for `nilpotentShiftLinGen` applied to `cumTailSumLin F m v`.
  have hN : ∀ j : Fin (m + 1),
      nilpotentShiftLinGen F m (cumTailSumLin F m v) j =
      if h : j.val + 1 < m + 1 then cumTailSumLin F m v ⟨j.val + 1, h⟩ else 0 := by
    intro j
    simp only [nilpotentShiftLinGen, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      nilpotentShiftMatrixGen]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨j.val + 1, h⟩]
      · simp
      · intro b _ hb; simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
        intro hbi; exact hb (Fin.ext (by omega))
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · apply Finset.sum_eq_zero; intro c _
      simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
      intro hji; exact h (by have := c.isLt; omega)
  ext ⟨i, hi⟩
  rw [Pi.sub_apply, hN]
  by_cases h : i + 1 < m + 1
  · simp only [dif_pos h]
    rw [cumTailSumLin_apply_succ _ _ _ _ h]
    ring
  · have hi_eq_m : i = m := by omega
    subst hi_eq_m
    simp only [show ¬(i + 1 < i + 1) by omega, dite_false, sub_zero]
    have hidx : (⟨i, hi⟩ : Fin (i + 1)) = ⟨i, lt_add_one i⟩ := rfl
    rw [hidx, cumTailSumLin_apply_last]

/-! ## Eigenvalue-site geometric series `(Λ - I)⁻¹`

The D̃-family tube redesign (`progress/dtilde-tube-redesign-design.md`)
replaces the rank-deficient nilpotent central site `N` with the full-rank
eigenvalue site `Λ = lam·id + N` (`jordanShiftLinGen`, `FieldGenericTube`).
The reversed-central orientation of the corrected tube needs the closed-form
inverse of `Λ - I = (lam-1)·id + N`, the eigenvalue analogue of
`cumTailSumLin = (I - N)⁻¹`.

For `lam ≠ 1` the inverse is the geometric series
`Σ_{k=0}^m (-1)^k (lam-1)^{-(k+1)} N^k`, whose matrix is upper triangular
with entry `(-(lam-1)⁻¹)^{j-i} · (lam-1)⁻¹` at `(i, j)` for `i ≤ j` — the
`cumTailSumMatrix` pattern with each `1` replaced by the weighted power.
Shared here (next to `cumTailSumLin`) so the whole D̃ family reuses it. -/

/-- Eigenvalue-site tail-sum matrix: upper triangular, entry
`(-(lam-1)⁻¹)^{j-i} · (lam-1)⁻¹` for `i ≤ j`, else `0`. Represents
`(Λ - I)⁻¹ = ((lam-1)·id + N)⁻¹` for `lam ≠ 1`. -/
noncomputable def eigTailSumMatrix (F : Type) [Field F] (lam : F) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  fun i j => if i.val ≤ j.val then (-(lam - 1)⁻¹) ^ (j.val - i.val) * (lam - 1)⁻¹ else 0

/-- Eigenvalue-site geometric-series linear map `(Λ - I)⁻¹`, `Λ = lam·id + N`.
The eigenvalue analogue of `cumTailSumLin`. -/
noncomputable def eigTailSumLin (F : Type) [Field F] (lam : F) (m : ℕ) :
    (Fin (m + 1) → F) →ₗ[F] (Fin (m + 1) → F) :=
  Matrix.mulVecLin (eigTailSumMatrix F lam m)

/-- Closed form of `eigTailSumLin`:
`eigTailSumLin F lam m v i = ∑_{j ≥ i} (-(lam-1)⁻¹)^{j-i} (lam-1)⁻¹ v j`. -/
theorem eigTailSumLin_apply (F : Type) [Field F] (lam : F) (m : ℕ)
    (v : Fin (m + 1) → F) (i : Fin (m + 1)) :
    eigTailSumLin F lam m v i =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (m + 1) => i.val ≤ j.val),
        (-(lam - 1)⁻¹) ^ (j.val - i.val) * (lam - 1)⁻¹ * v j := by
  simp only [eigTailSumLin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    eigTailSumMatrix, Finset.sum_filter, ite_mul, zero_mul]

/-- Boundary case for `eigTailSumLin`: at index `m` the tail collapses to the
single diagonal term `(lam-1)⁻¹ · v ⟨m⟩`. -/
theorem eigTailSumLin_apply_last (F : Type) [Field F] (lam : F) (m : ℕ)
    (v : Fin (m + 1) → F) :
    eigTailSumLin F lam m v ⟨m, lt_add_one m⟩ = (lam - 1)⁻¹ * v ⟨m, lt_add_one m⟩ := by
  rw [eigTailSumLin_apply]
  rw [show (Finset.univ.filter (fun j : Fin (m + 1) => m ≤ j.val))
        = {(⟨m, lt_add_one m⟩ : Fin (m + 1))} from ?_]
  · rw [Finset.sum_singleton]
    simp
  · ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have hjm : j.val = m := le_antisymm (by have := j.isLt; omega) h
      exact Fin.ext hjm
    · rintro rfl
      exact le_refl m

/-- Recursive step for `eigTailSumLin`: splits off the index-`i` diagonal term,
`S v ⟨i⟩ = (lam-1)⁻¹ v ⟨i⟩ + (-(lam-1)⁻¹) S v ⟨i+1⟩`. -/
theorem eigTailSumLin_apply_succ (F : Type) [Field F] (lam : F) (m : ℕ)
    (v : Fin (m + 1) → F) (i : ℕ) (hi : i + 1 < m + 1) :
    eigTailSumLin F lam m v ⟨i, by omega⟩ =
      (lam - 1)⁻¹ * v ⟨i, by omega⟩ +
        (-(lam - 1)⁻¹) * eigTailSumLin F lam m v ⟨i + 1, hi⟩ := by
  rw [eigTailSumLin_apply, eigTailSumLin_apply]
  have hsplit : Finset.univ.filter (fun j : Fin (m + 1) => i ≤ j.val)
      = insert (⟨i, by omega⟩ : Fin (m + 1))
          (Finset.univ.filter (fun j : Fin (m + 1) => i + 1 ≤ j.val)) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hij
      rcases Nat.lt_or_ge i j.val with h | h
      · right; omega
      · left; exact Fin.ext (le_antisymm h hij)
    · rintro (rfl | h)
      · exact le_refl i
      · omega
  rw [hsplit, Finset.sum_insert (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega)]
  congr 1
  · have h0 : ((⟨i, by omega⟩ : Fin (m + 1)) : ℕ) - i = 0 := by simp
    rw [h0, pow_zero, one_mul]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hji : (j : ℕ) - i = ((j : ℕ) - (i + 1)) + 1 := by omega
    rw [hji, pow_succ]
    ring

/-- `(Λ - I) ∘ eigTailSumLin = id`, i.e. `(lam-1)·(S v) + N (S v) = v`
(`lam ≠ 1`). Together with `eigTailSumLin_eigSub` this exhibits
`eigTailSumLin` as the genuine two-sided inverse of `Λ - I`. No reverse
induction needed: at index `i < m` the recursion cancels the shifted term,
at index `m` the shift vanishes and the diagonal `(lam-1)·(lam-1)⁻¹ = 1`. -/
theorem eigSub_eigTailSumLin (F : Type) [Field F] (lam : F) (m : ℕ)
    (hlam : lam ≠ 1) (v : Fin (m + 1) → F) :
    (lam - 1) • eigTailSumLin F lam m v
        + nilpotentShiftLinGen F m (eigTailSumLin F lam m v) = v := by
  have hc : (lam - 1) ≠ 0 := sub_ne_zero.mpr hlam
  have hN : ∀ j : Fin (m + 1),
      nilpotentShiftLinGen F m (eigTailSumLin F lam m v) j =
      if h : j.val + 1 < m + 1 then eigTailSumLin F lam m v ⟨j.val + 1, h⟩ else 0 := by
    intro j
    simp only [nilpotentShiftLinGen, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      nilpotentShiftMatrixGen]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨j.val + 1, h⟩]
      · simp
      · intro b _ hb; simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
        intro hbi; exact hb (Fin.ext (by omega))
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · apply Finset.sum_eq_zero; intro c _
      simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
      intro hji; exact h (by have := c.isLt; omega)
  ext ⟨i, hi⟩
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hN]
  by_cases h : i + 1 < m + 1
  · rw [dif_pos h, eigTailSumLin_apply_succ _ _ _ _ _ h]
    field_simp
    ring
  · rw [dif_neg h, add_zero]
    have hi_eq_m : i = m := by omega
    subst hi_eq_m
    rw [show (⟨i, hi⟩ : Fin (i + 1)) = ⟨i, lt_add_one i⟩ from rfl, eigTailSumLin_apply_last,
      ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- `eigTailSumLin ∘ (Λ - I) = id`, i.e.
`S ((lam-1)·v + N v) = v` (`lam ≠ 1`). Reverse induction on `m - i`, mirroring
`cumTailSumLin_oneSubNilp`. -/
theorem eigTailSumLin_eigSub (F : Type) [Field F] (lam : F) (m : ℕ)
    (hlam : lam ≠ 1) (v : Fin (m + 1) → F) :
    eigTailSumLin F lam m ((lam - 1) • v + nilpotentShiftLinGen F m v) = v := by
  have hc : (lam - 1) ≠ 0 := sub_ne_zero.mpr hlam
  have hN : ∀ j : Fin (m + 1), nilpotentShiftLinGen F m v j =
      if h : j.val + 1 < m + 1 then v ⟨j.val + 1, h⟩ else 0 := by
    intro j
    simp only [nilpotentShiftLinGen, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      nilpotentShiftMatrixGen]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨j.val + 1, h⟩]
      · simp
      · intro b _ hb; simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
        intro hbi; exact hb (Fin.ext (by omega))
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · apply Finset.sum_eq_zero; intro c _
      simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
      intro hji; exact h (by have := c.isLt; omega)
  ext ⟨i, hi⟩
  suffices key : ∀ k : ℕ, ∀ i' (hi' : i' < m + 1), i' + k = m →
      eigTailSumLin F lam m ((lam - 1) • v + nilpotentShiftLinGen F m v) ⟨i', hi'⟩
        = v ⟨i', hi'⟩ from
    key (m - i) i hi (by omega)
  intro k
  induction k with
  | zero =>
    intro i' hi' heq
    have hi_eq_m : i' = m := by omega
    subst hi_eq_m
    rw [show (⟨i', hi'⟩ : Fin (i' + 1)) = ⟨i', lt_add_one i'⟩ from rfl,
      eigTailSumLin_apply_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hN]
    simp only [show ¬(i' + 1 < i' + 1) by omega, dite_false, add_zero]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  | succ n ih =>
    intro i' hi' heq
    have hi1 : i' + 1 < m + 1 := by omega
    rw [eigTailSumLin_apply_succ _ _ _ _ _ hi1, ih (i' + 1) hi1 (by omega),
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, hN]
    simp only [dif_pos hi1]
    field_simp
    ring

/-! ## Shared γ-preimage untwisting lemma

The mixed-direction branch-vertex configuration in the D̃-family
indecomposability proofs (one leaf edge at a γ-coupled center canonical,
the other reversed) produces an `(I - N)`-twisted relation rather than a
literal leaf equality. The reusable infrastructure that strips the twist
is **not** a per-leaf `N`-invariance statement — that is circular, because
the only honest route from `y ∈ Wmain ⟨leaf⟩` to `N y ∈ Wmain ⟨leaf⟩`
runs through the leaf-subspace equalities those branches are trying to
establish (the partial fact `gamma_containment` only yields
`y ∈ Wmain ⟨1⟩ → N y ∈ Wmain ⟨5⟩`, and bridging leaf `5` back to leaf `1`
*is* part of the leaf equality). See #4554 for the analysis.

The correct, non-circular tool is a **γ-preimage lemma**: the γ-coupling
`g = d5tildeGamma_F` is a linear isomorphism, and a complementary pair of
invariant submodules is carried by `g` so that each summand maps *onto*
the corresponding summand at the target. Hence the `g`-preimage of a
target-summand element lands in the source summand. Packaging `g` as a
`LinearEquiv` (via its closed-form inverse `d5tildeGammaInv_F`) and feeding
the inverse the leaf-embedding patterns (`gammaInv_*` identities, which use
`cumTailSumLin = M = (I - N)⁻¹` above) recovers the untwisted source-side
coordinates `e₁(a - M (a - b)) + e₂(M (a - b))`.

This lemma is field-generic and stated over an abstract `LinearEquiv`, so
every D̃-family member (`d5`/`d6`/`d7`/`d8`) instantiates it with its own
γ-equiv and center submodules. It needs no finite-dimensionality. -/

/-- γ-preimage untwisting. If a linear isomorphism `g : V ≃ₗ[F] W` carries a
complementary pair of invariant submodules `(A₁, A₂)` of `V` into the
complementary pair `(B₁, B₂)` of `W` (i.e. `g '' A₁ ⊆ B₁` and
`g '' A₂ ⊆ B₂`), then `g` maps `A₁` *onto* `B₁`: the `g`-preimage of any
`w ∈ B₁` lies in `A₁`.

This is the non-circular replacement for per-leaf `N`-invariance in the
mixed-direction D̃-family branches: with `g` the γ-coupling and
`(A₁, A₂)`, `(B₁, B₂)` the complementary invariant submodules at the two
γ-coupled centers, it pulls center-`B` membership back to center `A`, where
the available leaf-edge invariance can extract the leaf coordinates. -/
theorem linearEquiv_invariant_isCompl_symm_mem
    {F : Type*} [Field F] {V W : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (g : V ≃ₗ[F] W)
    (A₁ A₂ : Submodule F V) (B₁ B₂ : Submodule F W)
    (hA : IsCompl A₁ A₂) (hB : IsCompl B₁ B₂)
    (h₁ : ∀ x ∈ A₁, g x ∈ B₁) (h₂ : ∀ x ∈ A₂, g x ∈ B₂)
    (w : W) (hw : w ∈ B₁) :
    g.symm w ∈ A₁ := by
  -- Decompose the preimage in `A₁ ⊕ A₂`.
  have hx : g.symm w ∈ (⊤ : Submodule F V) := Submodule.mem_top
  rw [← hA.sup_eq_top] at hx
  obtain ⟨a₁, ha₁, a₂, ha₂, hsum⟩ := Submodule.mem_sup.mp hx
  -- Apply `g`: `w = g a₁ + g a₂`.
  have hgw : w = g a₁ + g a₂ := by
    have hgg : g (g.symm w) = g (a₁ + a₂) := by rw [hsum]
    rwa [g.apply_symm_apply, map_add] at hgg
  -- `g a₂` lies in both `B₁` (as `w - g a₁`) and `B₂`, hence is `0`.
  have hga₂B₁ : g a₂ ∈ B₁ := by
    have hrw : g a₂ = w - g a₁ := by rw [hgw]; abel
    rw [hrw]; exact B₁.sub_mem hw (h₁ a₁ ha₁)
  have hga₂B₂ : g a₂ ∈ B₂ := h₂ a₂ ha₂
  have hga₂0 : g a₂ = 0 := by
    have hmem : g a₂ ∈ B₁ ⊓ B₂ := Submodule.mem_inf.mpr ⟨hga₂B₁, hga₂B₂⟩
    rwa [hB.inf_eq_bot, Submodule.mem_bot] at hmem
  have ha₂0 : a₂ = 0 := g.injective (by rw [hga₂0, map_zero])
  rw [← hsum, ha₂0, add_zero]
  exact ha₁

/-! ## Section: Decomposability counterexample for the reversed diagonal leaf

`starRep_kQ_isIndecomposable` (above) is **false**: for the orientation `Q`
that reverses the diagonal leaf 3 (`reversedAtVertex starQuiver 3`), the
representation `starRep_kQ F Q hOrient m` is **decomposable** for every `m ≥ 1`.
This section formalises the explicit `m = 1` complementary invariant pair from
issue #4566, machine-checking the refutation.

The mechanism (issue #4566): reversing leaf 3 turns its edge map from the
diagonal embed `starEmbedDiag_F` (range `L₃ = Δ`, the coupling that makes the
canonical D̃₄ rigid) into the projection `starProj3_F = starSecond_F`. The four
leaf images `L₁, L₂, L₄` still split under the center pair `(U₁, U₂)`, but `L₃`
is never forced to split — so an idempotent `A` commuting with the regular
nilpotent is no longer forced to lie in `{0, 1}`, and a nontrivial summand
appears. -/

/-- Two distinct standard coordinate lines are complementary in `Fin 2 → F`. -/
theorem isCompl_coordLines_two (F : Type) [Field F] :
    IsCompl (Submodule.span F {(![1, 0] : Fin 2 → F)})
            (Submodule.span F {(![0, 1] : Fin 2 → F)}) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx hx2
    rw [Submodule.mem_span_singleton] at hx hx2
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hx2
    have hx0 : x 0 = 0 := by rw [← hb]; simp
    have hx1 : x 1 = 0 := by rw [← ha]; simp
    funext i; fin_cases i
    · simpa using hx0
    · simpa using hx1
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = x 0 • (![1, 0] : Fin 2 → F) + x 1 • (![0, 1] : Fin 2 → F) := by
      funext i; fin_cases i <;> simp
    rw [hx]
    exact Submodule.add_mem_sup
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

/-- The two coordinate planes `span{e₀, e₃}` and `span{e₁, e₂}` are
complementary in `Fin 4 → F`. -/
theorem isCompl_coordPlanes_four (F : Type) [Field F] :
    IsCompl (Submodule.span F {(![1, 0, 0, 0] : Fin 4 → F), ![0, 0, 0, 1]})
            (Submodule.span F {(![0, 1, 0, 0] : Fin 4 → F), ![0, 0, 1, 0]}) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx hx2
    rw [Submodule.mem_span_pair] at hx hx2
    obtain ⟨s, t, hst⟩ := hx
    obtain ⟨u, v, huv⟩ := hx2
    have h0 : x 0 = 0 := by rw [← huv]; simp
    have h1 : x 1 = 0 := by rw [← hst]; simp
    have h2 : x 2 = 0 := by rw [← hst]; simp
    have h3 : x 3 = 0 := by rw [← huv]; simp
    funext i; fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (x 0 • (![1, 0, 0, 0] : Fin 4 → F) + x 3 • ![0, 0, 0, 1])
        + (x 1 • (![0, 1, 0, 0] : Fin 4 → F) + x 2 • ![0, 0, 1, 0]) := by
      funext i; fin_cases i <;> simp
    rw [hx]
    refine Submodule.add_mem_sup ?_ ?_
    · exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-! ### Image computations at `m = 1`

The four leaf maps and the reversed-leaf projection evaluated on the explicit
basis vectors of the `m = 1` counterexample. -/

private theorem cex_embed1_e0 (F : Type) [Field F] :
    starEmbed1_F F 1 (![1, 0] : Fin 2 → F) = ![1, 0, 0, 0] := by
  funext i; fin_cases i <;> simp [starEmbed1_F]

private theorem cex_embed1_e1 (F : Type) [Field F] :
    starEmbed1_F F 1 (![0, 1] : Fin 2 → F) = ![0, 1, 0, 0] := by
  funext i; fin_cases i <;> simp [starEmbed1_F]

private theorem cex_embed2_e0 (F : Type) [Field F] :
    starEmbed2_F F 1 (![1, 0] : Fin 2 → F) = ![0, 0, 1, 0] := by
  funext i; fin_cases i <;> simp [starEmbed2_F]

private theorem cex_embed2_e1 (F : Type) [Field F] :
    starEmbed2_F F 1 (![0, 1] : Fin 2 → F) = ![0, 0, 0, 1] := by
  funext i; fin_cases i <;> simp [starEmbed2_F]

private theorem cex_nilp_e0 (F : Type) [Field F] :
    nilpotentShiftLinGen F 1 (![1, 0] : Fin 2 → F) = ![0, 0] := by
  funext i; fin_cases i <;>
    simp [nilpotentShiftLinGen, nilpotentShiftMatrixGen, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem cex_nilp_e1 (F : Type) [Field F] :
    nilpotentShiftLinGen F 1 (![0, 1] : Fin 2 → F) = ![1, 0] := by
  funext i; fin_cases i <;>
    simp [nilpotentShiftLinGen, nilpotentShiftMatrixGen, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem cex_embedNilp_e0 (F : Type) [Field F] :
    starEmbedNilp_F F 1 (![1, 0] : Fin 2 → F) = ![1, 0, 0, 0] := by
  funext i
  simp only [starEmbedNilp_F, LinearMap.add_apply, LinearMap.comp_apply, cex_nilp_e0]
  fin_cases i <;> simp [starEmbed1_F, starEmbed2_F]

private theorem cex_embedNilp_e1 (F : Type) [Field F] :
    starEmbedNilp_F F 1 (![0, 1] : Fin 2 → F) = ![0, 1, 1, 0] := by
  funext i
  simp only [starEmbedNilp_F, LinearMap.add_apply, LinearMap.comp_apply, cex_nilp_e1]
  fin_cases i <;> simp [starEmbed1_F, starEmbed2_F, cex_embed1_e1, cex_embed2_e0]

private theorem cex_proj3_g0 (F : Type) [Field F] :
    starProj3_F F 1 (![1, 0, 0, 0] : Fin 4 → F) = ![0, 0] := by
  funext i; fin_cases i <;> simp [starProj3_F, starSecond_F]

private theorem cex_proj3_g3 (F : Type) [Field F] :
    starProj3_F F 1 (![0, 0, 0, 1] : Fin 4 → F) = ![0, 1] := by
  funext i; fin_cases i <;> simp [starProj3_F, starSecond_F]

private theorem cex_proj3_h1 (F : Type) [Field F] :
    starProj3_F F 1 (![0, 1, 0, 0] : Fin 4 → F) = ![0, 0] := by
  funext i; fin_cases i <;> simp [starProj3_F, starSecond_F]

private theorem cex_proj3_h2 (F : Type) [Field F] :
    starProj3_F F 1 (![0, 0, 1, 0] : Fin 4 → F) = ![1, 0] := by
  funext i; fin_cases i <;> simp [starProj3_F, starSecond_F]

/-! ### The complementary invariant pair and the refutation -/

/-- First summand `W₁` of the `m = 1` decomposition of `starRep_kQ` at the
reversed-leaf-3 orientation (issue #4566). -/
private noncomputable def starCexW1 (F : Type) [Field F] :
    ∀ v : Fin 5, Submodule F (Fin (if v.val = 0 then 2 * (1 + 1) else 1 + 1) → F)
  | ⟨0, _⟩ => Submodule.span F {(![1, 0, 0, 0] : Fin 4 → F), ![0, 0, 0, 1]}
  | ⟨1, _⟩ => Submodule.span F {(![1, 0] : Fin 2 → F)}
  | ⟨2, _⟩ => Submodule.span F {(![0, 1] : Fin 2 → F)}
  | ⟨3, _⟩ => Submodule.span F {(![0, 1] : Fin 2 → F)}
  | ⟨4, _⟩ => Submodule.span F {(![1, 0] : Fin 2 → F)}
  | ⟨n + 5, h⟩ => absurd h (by omega)

/-- Second summand `W₂` of the `m = 1` decomposition (issue #4566). -/
private noncomputable def starCexW2 (F : Type) [Field F] :
    ∀ v : Fin 5, Submodule F (Fin (if v.val = 0 then 2 * (1 + 1) else 1 + 1) → F)
  | ⟨0, _⟩ => Submodule.span F {(![0, 1, 0, 0] : Fin 4 → F), ![0, 0, 1, 0]}
  | ⟨1, _⟩ => Submodule.span F {(![0, 1] : Fin 2 → F)}
  | ⟨2, _⟩ => Submodule.span F {(![1, 0] : Fin 2 → F)}
  | ⟨3, _⟩ => Submodule.span F {(![1, 0] : Fin 2 → F)}
  | ⟨4, _⟩ => Submodule.span F {(![0, 1] : Fin 2 → F)}
  | ⟨n + 5, h⟩ => absurd h (by omega)

/-- The reversed-diagonal-leaf orientation of `starQuiver`. -/
@[reducible] private noncomputable def starRevLeaf3Quiver : Quiver (Fin 5) :=
  @Etingof.reversedAtVertex (Fin 5) _ starQuiver 3

instance starRevLeaf3_subsingleton (a b : Fin 5) :
    Subsingleton (@Quiver.Hom (Fin 5) starRevLeaf3Quiver a b) := by
  show Subsingleton (@Etingof.ReversedAtVertexHom (Fin 5) _ starQuiver 3 a b)
  by_cases ha : a = 3 <;> by_cases hb : b = 3
  · rw [@Etingof.ReversedAtVertexHom_eq_eq (Fin 5) _ starQuiver 3 a b ha hb]; infer_instance
  · rw [@Etingof.ReversedAtVertexHom_eq_ne (Fin 5) _ starQuiver 3 a b ha hb]; infer_instance
  · rw [@Etingof.ReversedAtVertexHom_ne_eq (Fin 5) _ starQuiver 3 a b ha hb]; infer_instance
  · rw [@Etingof.ReversedAtVertexHom_ne_ne (Fin 5) _ starQuiver 3 a b ha hb]; infer_instance

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- **Refutation of `starRep_kQ_isIndecomposable` (issue #4566).** For the
orientation `Q = reversedAtVertex starQuiver 3` (reversing the diagonal leaf),
the K_{1,4} (D̃₄) representation `starRep_kQ F Q hOrient 1` is **decomposable**:
`starCexW1`/`starCexW2` are a nontrivial complementary invariant pair.

This proves `starRep_kQ_isIndecomposable` (above) states a false proposition;
its `sorry` body cannot be filled. The downstream `star_not_finite_type_per_kQ`
remains true (D̃₄ is affine), but its current proof route via this construction
is unsound for reversed orientations and needs the homogeneous-tube redesign
(issue #4566 recommendation 2). -/
theorem starRep_kQ_reversedLeaf3_decomposable (F : Type) [Field F] :
    ¬ @Etingof.QuiverRepresentation.IsIndecomposable F _ (Fin 5) starRevLeaf3Quiver
        (starRep_kQ F starRevLeaf3Quiver
          (Etingof.reversedAtVertex_isOrientationOf starAdj_symm starAdj_diag
            starOrientation_isOrientationOf 3) 1) := by
  rintro ⟨-, hno⟩
  have key := hno (starCexW1 F) (starCexW2 F) ?_ ?_ ?_
  · -- Neither summand is everywhere `⊥`: both are nonzero at leaf 1.
    have hne1 : starCexW1 F 1 ≠ ⊥ := by
      simp only [starCexW1, ne_eq, Submodule.span_singleton_eq_bot]
      intro h; exact one_ne_zero (congr_fun h 0)
    have hne2 : starCexW2 F 1 ≠ ⊥ := by
      simp only [starCexW2, ne_eq, Submodule.span_singleton_eq_bot]
      intro h; exact one_ne_zero (congr_fun h 1)
    rcases key with h | h
    · exact hne1 (h 1)
    · exact hne2 (h 1)
  · -- `W₁`-invariance.
    intro a b e x hx
    show starRepMap_kQ F 1 a b x ∈ starCexW1 F b
    fin_cases a <;> fin_cases b <;>
      first
      | exact absurd e.down (by decide)
      | skip
    · -- arrow 0 → 3 (reversed)
      simp only [starCexW1] at hx ⊢
      show starProj3_F F 1 x ∈ _
      rw [Submodule.mem_span_pair] at hx; obtain ⟨s, t, rfl⟩ := hx
      rw [map_add, map_smul, map_smul, cex_proj3_g0, cex_proj3_g3,
        show (![0, 0] : Fin 2 → F) = 0 from by funext i; fin_cases i <;> rfl,
        smul_zero, zero_add]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · -- arrow 1 → 0
      simp only [starCexW1] at hx ⊢
      rw [Submodule.mem_span_singleton] at hx; obtain ⟨c, rfl⟩ := hx
      show starEmbed1_F F 1 (c • (![1, 0] : Fin 2 → F)) ∈ _
      rw [map_smul, cex_embed1_e0]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · -- arrow 2 → 0
      simp only [starCexW1] at hx ⊢
      rw [Submodule.mem_span_singleton] at hx; obtain ⟨c, rfl⟩ := hx
      show starEmbed2_F F 1 (c • (![0, 1] : Fin 2 → F)) ∈ _
      rw [map_smul, cex_embed2_e1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · -- arrow 4 → 0
      simp only [starCexW1] at hx ⊢
      rw [Submodule.mem_span_singleton] at hx; obtain ⟨c, rfl⟩ := hx
      show starEmbedNilp_F F 1 (c • (![1, 0] : Fin 2 → F)) ∈ _
      rw [map_smul, cex_embedNilp_e0]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · -- `W₂`-invariance.
    intro a b e x hx
    show starRepMap_kQ F 1 a b x ∈ starCexW2 F b
    fin_cases a <;> fin_cases b <;>
      first
      | exact absurd e.down (by decide)
      | skip
    · -- arrow 0 → 3 (reversed)
      simp only [starCexW2] at hx ⊢
      show starProj3_F F 1 x ∈ _
      rw [Submodule.mem_span_pair] at hx; obtain ⟨s, t, rfl⟩ := hx
      rw [map_add, map_smul, map_smul, cex_proj3_h1, cex_proj3_h2,
        show (![0, 0] : Fin 2 → F) = 0 from by funext i; fin_cases i <;> rfl,
        smul_zero, zero_add]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · -- arrow 1 → 0
      simp only [starCexW2] at hx ⊢
      rw [Submodule.mem_span_singleton] at hx; obtain ⟨c, rfl⟩ := hx
      show starEmbed1_F F 1 (c • (![0, 1] : Fin 2 → F)) ∈ _
      rw [map_smul, cex_embed1_e1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · -- arrow 2 → 0
      simp only [starCexW2] at hx ⊢
      rw [Submodule.mem_span_singleton] at hx; obtain ⟨c, rfl⟩ := hx
      show starEmbed2_F F 1 (c • (![1, 0] : Fin 2 → F)) ∈ _
      rw [map_smul, cex_embed2_e0]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · -- arrow 4 → 0
      simp only [starCexW2] at hx ⊢
      rw [Submodule.mem_span_singleton] at hx; obtain ⟨c, rfl⟩ := hx
      show starEmbedNilp_F F 1 (c • (![0, 1] : Fin 2 → F)) ∈ _
      rw [map_smul, cex_embedNilp_e1,
        show (![0, 1, 1, 0] : Fin 4 → F)
          = (![0, 1, 0, 0] : Fin 4 → F) + ![0, 0, 1, 0] from by
        funext i; fin_cases i <;> simp]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _
        (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)))
  · -- Complementarity at every vertex.
    intro v
    fin_cases v
    · exact isCompl_coordPlanes_four F
    · exact isCompl_coordLines_two F
    · exact (isCompl_coordLines_two F).symm
    · exact (isCompl_coordLines_two F).symm
    · exact isCompl_coordLines_two F

end Etingof
