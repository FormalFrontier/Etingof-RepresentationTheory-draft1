import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType

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
    -- Key disjointness: embed1(x) + embed2(y) = 0 → x = 0 ∧ y = 0
    have embed_sum_zero : ∀ x y : Fin (m + 1) → F,
        starEmbed1_F F m x + starEmbed2_F F m y = 0 → x = 0 ∧ y = 0 := by
      intro x y h
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
      obtain ⟨hb0', hd0'⟩ := embed_sum_zero b d hzero
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
    -- Center decomposition: every w in 2(m+1)-dim space is embed1(first half) + embed2(second half)
    have center_decomp : ∀ w : Fin (2 * (m + 1)) → F,
        w = starEmbed1_F F m (fun i => w ⟨i.val, by omega⟩) +
            starEmbed2_F F m (fun i => w ⟨m + 1 + i.val, by omega⟩) := by
      intro w; ext ⟨j, hj⟩
      simp only [Pi.add_apply, starEmbed1_F, starEmbed2_F, LinearMap.coe_mk, AddHom.coe_mk]
      by_cases hjlt : j < m + 1
      · simp only [dif_pos hjlt, show ¬(m + 1 ≤ j) from by omega, dite_false, add_zero]
      · simp only [dif_neg hjlt, show m + 1 ≤ j from by omega, dite_true, zero_add]
        congr 1; ext; simp; omega
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
        center_decomp w ▸ (W' ⟨0, by omega⟩).add_mem (h_emb1 _) (h_emb2 _)
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
the shared header). -/

/-- First-half projection `(a, b) ↦ a`. -/
noncomputable def starFirst_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) where
  toFun w i := w ⟨i.val, by omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Second-half projection `(a, b) ↦ b`. -/
noncomputable def starSecond_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) where
  toFun w i := w ⟨m + 1 + i.val, by omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

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

private theorem starFirst_F_starEmbed1_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    starFirst_F F m (starEmbed1_F F m x) = x := by
  ext i
  simp only [starFirst_F, starEmbed1_F, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.isLt]

private theorem starFirst_F_starEmbed2_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    starFirst_F F m (starEmbed2_F F m x) = 0 := by
  ext i
  simp only [starFirst_F, starEmbed2_F, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg (by omega)]
  rfl

private theorem starSecond_F_starEmbed1_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    starSecond_F F m (starEmbed1_F F m x) = 0 := by
  ext i
  simp only [starSecond_F, starEmbed1_F, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg (by omega)]
  rfl

private theorem starSecond_F_starEmbed2_F (F : Type) [Field F] (m : ℕ)
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

end Etingof
