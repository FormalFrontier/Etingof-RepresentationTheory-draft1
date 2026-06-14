import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericCycle
import EtingofRepresentationTheory.Chapter6.FieldGenericStar

/-!
# Homogeneous-tube indecomposability mechanism for tree-shaped affine quivers

This module is the foundational deliverable of the sporadic-tube redesign
(`progress/sporadic-tube-redesign-design.md`, issue #4548). It provides the
reusable **§3 reduction core** that the corrected Ẽ₆/Ẽ₇/T(1,2,5) base cases
(#4557/#4558/#4559) will call, and validates the eigenvalue/Jordan-block
pattern on the cleanest affine tree tube, D̃₄.

## The mechanism

The design replaces the refuted single-nilpotent-twist family with the
**homogeneous-tube** indecomposable: a regular simple `R_λ` carrying a genuine
eigenvalue parameter `λ`, tensored up to the length-`(m+1)` self-extension
built around `λI + J_{m+1}` (a Jordan block at the eigenvalue site).

The project proves indecomposability **only** via the
invariant-submodule-splitting route (workhorse
`nilpotent_invariant_compl_trivial_gen`). The Kronecker template of §3 of the
design doc shows the tube reduces to that workhorse once one observes:

> `λI + J` and `J` have the **same invariant subspaces** — a subspace `U` is
> `(λ • id + N)`-invariant iff it is `N`-invariant, because `λ • id` maps every
> subspace to itself. So the eigenvalue `λ` never needs to be tracked in the
> splitting argument.

`eigenvalue_jordan_invariant_compl_trivial_gen` (relocated upstream to
`FieldGenericStar.lean` by issue #4648, so the orientation-generic `starRep_kQ`
can reach it) packages exactly this "λ drops out" reduction: a complementary
pair invariant under `λ • id + N`, with `N` nilpotent of 1-dimensional kernel,
has one component trivial. This is the portable lemma the per-shape sub-issues
invoke at their eigenvalue site.

## D̃₄ validation

The identity/iso-arrow collapse helper required by the issue is already shared
as `compl_le_forces_eq` (`FieldGenericInfiniteType.lean`); the star proof uses
its one-sided variant `compl_eq_of_le` inline. We reuse that collapse machinery
and build `starTubeRepGen F lam m`: the D̃₄ (4-subspace, `δ = (2;1,1,1,1)`)
homogeneous tube whose fourth arm carries `λ • id + J` at the eigenvalue site
instead of a rank-deficient twist. It is proven indecomposable **for every
`λ`** through the reduction lemma, generalizing the existing `λ = 0`
construction `starRepGen` and de-risking the eigenvalue/`J` pattern before the
rectangular matrices of the real sporadic shapes.

See `FieldGenericStar.lean` for `starEmbed1_F` / `starEmbed2_F` /
`starEmbedDiag_F`, the center decomposition lemmas, and the `λ = 0` source
proof `starRepGen_isIndecomposable` that this module mirrors.
-/

open scoped Matrix
open Finset

namespace Etingof

/-! ## D̃₄ homogeneous tube

The fourth arm of the K_{1,4} star carries the eigenvalue site `λ • id + J`
rather than the rank-deficient nilpotent twist. The other three arms
(`embed1`, `embed2`, `diag`) are unchanged from `starRepGen`, so the collapse
step still forces `W(1) = W(2) = W(3) = W(4)`; the fourth arm then deposits a
`(λ • id + N)`-invariant pair at that common space, where the reduction core
finishes. -/

/-- Match-based map for the D̃₄ homogeneous-tube representation. Arms 1,2,3 are
`embed1`/`embed2`/`diag` exactly as in `starRepGen`; arm 4 carries the
eigenvalue site `λI + J`. -/
private noncomputable def starRepMapTubeGen (F : Type) [Field F] (lam : F) (m : ℕ)
    (a b : Fin 5) :
    (Fin (if a.val = 0 then 2 * (m + 1) else m + 1) → F) →ₗ[F]
    (Fin (if b.val = 0 then 2 * (m + 1) else m + 1) → F) :=
  match a, b with
  | ⟨1, _⟩, ⟨0, _⟩ => starEmbed1_F F m
  | ⟨2, _⟩, ⟨0, _⟩ => starEmbed2_F F m
  | ⟨3, _⟩, ⟨0, _⟩ => starEmbedDiag_F F m
  | ⟨4, _⟩, ⟨0, _⟩ => starEmbedTube_F F lam m
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The D̃₄ homogeneous-tube representation at eigenvalue `lam`, with dim vector
`(2(m+1), m+1, m+1, m+1, m+1) = (m+1)·δ`, `δ = (2;1,1,1,1)`. -/
noncomputable def starTubeRepGen (F : Type) [Field F] (lam : F) (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin 5) _ starQuiver := by
  letI := starQuiver
  exact {
    obj := fun v => Fin (if v.val = 0 then 2 * (m + 1) else m + 1) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => starRepMapTubeGen F lam m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem starTubeRepGen_dimVec (F : Type) [Field F] (lam : F) (m : ℕ) (v : Fin 5) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin 5) _
      starQuiver (starTubeRepGen F lam m) v ≃ₗ[F]
      (Fin (if v.val = 0 then 2 * (m + 1) else m + 1) → F)) :=
  ⟨LinearEquiv.refl F _⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
-- Bumped to match the `λ = 0` source proof `starRepGen_isIndecomposable`:
-- the body is ~190 lines of nested have-blocks that exercise typeclass
-- synthesis under the `attribute [-instance]` pragma.
set_option maxHeartbeats 1600000 in
/-- The D̃₄ homogeneous tube is indecomposable **for every eigenvalue `lam`**.
The proof mirrors `starRepGen_isIndecomposable`: the three iso/identity arms
collapse `W(1) = W(2) = W(3) = W(4)`, and arm 4 deposits a `(λ • id + N)`-
invariant complementary pair at that common space, which
`eigenvalue_jordan_invariant_compl_trivial_gen` kills. The eigenvalue drops
out of the splitting argument. -/
theorem starTubeRepGen_isIndecomposable (F : Type) [Field F] (lam : F) (m : ℕ) :
    @Etingof.QuiverRepresentation.IsIndecomposable F _ (Fin 5)
      starQuiver (starTubeRepGen F lam m) := by
  letI := starQuiver
  constructor
  · -- Nontrivial at leaf 1 (dim m+1 ≥ 1)
    refine ⟨⟨1, by omega⟩, ?_⟩
    change Nontrivial (Fin (if (1 : Fin 5).val = 0 then _ else m + 1) → F)
    simp only [show (1 : Fin 5).val = 1 from rfl, one_ne_zero, ↓reduceIte]
    infer_instance
  · intro W₁ W₂ hW₁_inv hW₂_inv hcompl
    -- Core decomposition: if embed1(x) + embed2(z) ∈ W(center) and both W, W'
    -- are subrepresentation-invariant, then x ∈ W(leaf1) and z ∈ W(leaf2).
    have core (W W' : ∀ v, Submodule F ((starTubeRepGen F lam m).obj v))
        (hW : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W a, (starTubeRepGen F lam m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starTubeRepGen F lam m).mapLinear e x ∈ W' b)
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
    have leaf3_sub (W W' : ∀ v, Submodule F ((starTubeRepGen F lam m).obj v))
        (hW : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W a, (starTubeRepGen F lam m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starTubeRepGen F lam m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x : Fin (m + 1) → F) (hx : x ∈ W ⟨3, by omega⟩) :
        x ∈ W ⟨1, by omega⟩ ∧ x ∈ W ⟨2, by omega⟩ := by
      have hmem := hW (show @Quiver.Hom _ starQuiver ⟨3, by omega⟩ ⟨0, by omega⟩
        from ⟨⟨by decide, rfl⟩⟩) x hx
      change starEmbedDiag_F F m x ∈ W ⟨0, by omega⟩ at hmem
      rw [starEmbedDiag_F, LinearMap.add_apply] at hmem
      exact core W W' hW hW' hc x x hmem
    -- Leaf 4 (eigenvalue site): x ∈ W(4) → x ∈ W(1) ∧ (λI + N)x ∈ W(2)
    have leaf4_sub (W W' : ∀ v, Submodule F ((starTubeRepGen F lam m).obj v))
        (hW : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W a, (starTubeRepGen F lam m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starTubeRepGen F lam m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x : Fin (m + 1) → F) (hx : x ∈ W ⟨4, by omega⟩) :
        x ∈ W ⟨1, by omega⟩ ∧
          (jordanShiftLinGen F lam m) x ∈ W ⟨2, by omega⟩ := by
      have hmem := hW (show @Quiver.Hom _ starQuiver ⟨4, by omega⟩ ⟨0, by omega⟩
        from ⟨⟨by decide, rfl⟩⟩) x hx
      change starEmbedTube_F F lam m x ∈ W ⟨0, by omega⟩ at hmem
      rw [starEmbedTube_F, LinearMap.add_apply, LinearMap.comp_apply] at hmem
      exact core W W' hW hW' hc x
        ((jordanShiftLinGen F lam m) x) hmem
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
        x ∈ W₁ ⟨1, by omega⟩ →
          (jordanShiftLinGen F lam m) x ∈ W₁ ⟨1, by omega⟩ := by
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
        x ∈ W₂ ⟨1, by omega⟩ →
          (jordanShiftLinGen F lam m) x ∈ W₂ ⟨1, by omega⟩ := by
      intro x hx
      have hx4 : x ∈ W₂ ⟨4, by omega⟩ := by rw [heq41']; exact hx
      have h2 := (leaf4_sub W₂ W₁ hW₂_inv hW₁_inv (fun v => (hcompl v).symm)
        x hx4).2
      exact h12' ▸ h2
    -- The eigenvalue site `λI + N` carries the indecomposability: λ drops out.
    have hresult := eigenvalue_jordan_invariant_compl_trivial_gen
      (nilpotentShiftLinGen F m) (nilpotentShiftLinGen_nilpotent F m)
      (nilpotentShiftLinGen_ker_finrank F m) lam
      (W₁ ⟨1, by omega⟩) (W₂ ⟨1, by omega⟩) hN₁ hN₂ (hcompl ⟨1, by omega⟩)
    suffices propagate : ∀ (W W' : ∀ v, Submodule F ((starTubeRepGen F lam m).obj v)),
        (∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starTubeRepGen F lam m).mapLinear e x ∈ W' b) →
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

end Etingof
