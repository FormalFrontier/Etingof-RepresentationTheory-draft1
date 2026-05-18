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

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) version of `star_not_finite_type`: for any
algebraically closed field `F` and any orientation `Q` of `starAdj`, the
set of dimension vectors of indecomposable representations of `Q` over
`F` is infinite.

API stub introduced by issue #2875 (deliverable 1): the body is `sorry`
pending the indecomposability proof for `starRep_kQ`, which is tracked by
issues #2789 (canonical orientation) and #2801 (Q-extension). This stub
exists so that the per-(F, Q) assembly `not_posdef_infinite_type_per_kQ`
can dispatch by name to the K_{1,4} (D̃₄) forbidden-subgraph case via
`subgraph_infinite_type_transfer_per_kQ`. -/
theorem star_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 5))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 5) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 5 Q starAdj) :
    ¬ Set.Finite
      {d : Fin 5 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 5) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- TODO (#2789, #2801): replace this `sorry` with the proof that the
  -- orientation-generic family `starRep_kQ F Q hOrient (m + 1)` is
  -- indecomposable and produces infinitely many distinct dimension
  -- vectors (mirror `etilde6_not_finite_type_per_kQ`).
  let _ := hOrient
  sorry

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

end Etingof
