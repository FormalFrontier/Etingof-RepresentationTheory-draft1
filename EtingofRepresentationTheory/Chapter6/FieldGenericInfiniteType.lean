import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions

/-!
# Field-Generic Infinite Type Constructions — Shared Header

This file provides the shared primitives used by all field-generic /
orientation-generic infinite-type constructions in Chapter 6. The originals
are ℂ-specific (see `InfiniteTypeConstructions.lean`); the constructions
here work over any field `F` (or any algebraically closed field when
needed).

Per-graph representations and their indecomposability proofs live in
sibling files that import this one:

* `FieldGenericCycle.lean` — `cycleRepGen` / `cycleRep_kQ` for the cycle
  graph (any `k ≥ 3`).
* `FieldGenericStar.lean` — `starRepGen` for K_{1,4} (D̃₄) with the
  canonical all-sink orientation. Per-(F, Q) star variants will land
  here too (see #2801 / #2802).
* `FieldGenericD5Tilde.lean`, `FieldGenericETilde6.lean`,
  `FieldGenericETilde7.lean` — orientation-generic affine Dynkin
  constructions.

The shared content kept in this file is:

* Field-generic nilpotent shift `nilpotentShiftMatrixGen` /
  `nilpotentShiftLinGen` and their key properties (nilpotency,
  one-dimensional kernel).
* The nilpotent-invariant complement lemma
  `nilpotent_invariant_compl_trivial_gen`.
* `compl_le_forces_eq` — the complementary-pair identity used by every
  per-(F, Q) indecomposability proof to collapse an identity-arrow
  inclusion to subspace equality.
* The per-(F, Q) subgraph transfer infrastructure
  `restrictOrientationViaEmb` / `subgraph_infinite_type_transfer_per_kQ`.

The key insight: all the indecomposability proofs use only linear algebra
(nilpotent maps, kernel dimension, complementary subspaces). None of this
requires ℂ specifically.

## Naming conventions

The Chapter 6 "field-generic" / "orientation-generic" wave introduces three
suffix conventions side-by-side with the original ℂ-only names. Four
categories are in use across this file and the sibling per-graph files
(`FieldGenericCycle.lean`, `FieldGenericStar.lean`,
`FieldGenericETilde6.lean`, `FieldGenericETilde7.lean`,
`FieldGenericD5Tilde.lean`):

* `_F` / `_gen` — **field-generic only.** Construction or theorem
  parametrised by an arbitrary field `F` (often algebraically closed),
  but specialised to the canonical orientation of the graph.
  Representative examples: `cycleRepGen`, `cycleRepGen_dimVec`,
  `cycle_not_finite_type_gen`, `starRepGen`, `starEmbed1_F`,
  `starEmbedNilp_F`, `star_not_finite_type_F`.

* `_kQ` — **data, parametrised by both `(F, Q)`.** A representation or
  structure over any field `F` and any orientation `Q` of the underlying
  graph. The `Q` argument selects per-edge directions, so each edge map
  is built from forward/reverse maps depending on `Q`'s choice.
  Representative examples: `cycleRep_kQ`, `etilde6Rep_kQ`,
  `etilde7Rep_kQ`, `etilde6RepMap_kQ`, `etilde7RepMap_kQ`.

* `_per_kQ` — **theorem stating a per-`(F, Q)` conclusion.** Typically
  an infinite-type or indecomposability statement applied to the
  `_kQ` data. Representative examples: `cycle_not_finite_type_per_kQ`,
  `etilde6_not_finite_type_per_kQ`, `subgraph_infinite_type_transfer_per_kQ`.

* (no suffix) — **original ℂ-only construction** living in
  `Chapter6/InfiniteTypeConstructions.lean`. Representative examples:
  `cycleRep`, `etilde6Rep`, `etilde7Rep`, `cycle_not_finite_type`,
  `etilde6_not_finite_type`.

When introducing a new item, pick the suffix matching what is actually
generic: `_F`/`_gen` when only the field is generic, `_kQ` for `(F, Q)`
data, `_per_kQ` for `(F, Q)`-quantified theorems, and no suffix for
ℂ-only code in `InfiniteTypeConstructions.lean`.
-/

open scoped Matrix
open Finset

namespace Etingof

/-! ## Field-generic nilpotent shift -/

/-- The nilpotent shift matrix over an arbitrary commutative ring. -/
noncomputable def nilpotentShiftMatrixGen (R : Type*) [CommSemiring R] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  fun i j => if j.val = i.val + 1 then 1 else 0

/-- The nilpotent shift linear map over an arbitrary commutative ring. -/
noncomputable def nilpotentShiftLinGen (R : Type*) [CommSemiring R] (m : ℕ) :
    (Fin (m + 1) → R) →ₗ[R] (Fin (m + 1) → R) :=
  Matrix.mulVecLin (nilpotentShiftMatrixGen R m)

private theorem mulVecLin_pow_gen {R : Type*} [CommSemiring R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    Matrix.mulVecLin (M ^ k) = (Matrix.mulVecLin M) ^ k := by
  induction k with
  | zero => ext v; simp [Matrix.mulVecLin_one]
  | succ k ih =>
    rw [pow_succ, Matrix.mulVecLin_mul, ih]
    rfl

private theorem nilpotentShiftMatrixGen_pow_entry (R : Type*) [CommSemiring R]
    (m n : ℕ) (a b : Fin (m + 1)) :
    (nilpotentShiftMatrixGen R m ^ n) a b = if b.val = a.val + n then 1 else 0 := by
  induction n generalizing a b with
  | zero =>
    simp only [pow_zero, Nat.add_zero, Matrix.one_apply]
    congr 1; exact propext ⟨fun h => (Fin.val_eq_of_eq h).symm, fun h => Fin.ext h.symm⟩
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    by_cases hb : b.val = a.val + (n + 1)
    · have hbn : a.val + n < m + 1 := by omega
      rw [show (if b.val = a.val + (n + 1) then (1 : R) else 0) = 1 from if_pos hb]
      rw [Finset.sum_eq_single ⟨a.val + n, hbn⟩]
      · rw [ih]; simp only [ite_true, one_mul, nilpotentShiftMatrixGen]
        rw [if_pos (by show b.val = (a.val + n) + 1; omega)]
      · intro c _ hc; rw [ih]; split_ifs with h1
        · exfalso; exact hc (Fin.ext h1)
        · ring
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [show (if b.val = a.val + (n + 1) then (1 : R) else 0) = 0 from if_neg hb]
      apply Finset.sum_eq_zero; intro c _; rw [ih]; split_ifs with h1
      · simp only [one_mul, nilpotentShiftMatrixGen]; rw [if_neg]; intro hbc; exact hb (by omega)
      · ring

theorem nilpotentShiftLinGen_nilpotent (R : Type*) [CommSemiring R] (m : ℕ) :
    IsNilpotent (nilpotentShiftLinGen R m) := by
  use m + 1
  have hmat : nilpotentShiftMatrixGen R m ^ (m + 1) = 0 := by
    ext i j; rw [nilpotentShiftMatrixGen_pow_entry, Matrix.zero_apply, if_neg]
    intro h; exact absurd h (by have := j.isLt; omega)
  change (nilpotentShiftLinGen R m) ^ (m + 1) = 0
  rw [nilpotentShiftLinGen, ← mulVecLin_pow_gen, hmat, Matrix.mulVecLin_zero]

private theorem nilpotentShiftLinGen_apply (F : Type*) [Field F] (m : ℕ)
    (v : Fin (m + 1) → F) (i : Fin (m + 1)) :
    nilpotentShiftLinGen F m v i = if h : i.val + 1 < m + 1 then v ⟨i.val + 1, h⟩ else 0 := by
  simp only [nilpotentShiftLinGen, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    nilpotentShiftMatrixGen]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val + 1, h⟩]
    · simp
    · intro b _ hb; simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
      intro hbi; exact hb (Fin.ext (by omega))
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · apply Finset.sum_eq_zero; intro j _
    simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
    intro hji; exact h (by have := j.isLt; omega)

theorem nilpotentShiftLinGen_ker_finrank (F : Type*) [Field F] (m : ℕ) :
    Module.finrank F (LinearMap.ker (nilpotentShiftLinGen F m)) = 1 := by
  have hker_fwd : ∀ v : Fin (m + 1) → F, nilpotentShiftLinGen F m v = 0 →
      ∀ j : Fin (m + 1), 0 < j.val → v j = 0 := by
    intro v hv j hj
    have h1 : nilpotentShiftLinGen F m v ⟨j.val - 1, by omega⟩ = 0 := by
      simp [hv]
    rw [nilpotentShiftLinGen_apply] at h1
    have h2 : (j.val - 1) + 1 < m + 1 := by omega
    rw [dif_pos h2] at h1
    have h3 : (⟨(j.val - 1) + 1, h2⟩ : Fin (m + 1)) = j := by
      ext; show (j.val - 1) + 1 = j.val; omega
    rwa [h3] at h1
  have hker_bwd : ∀ v : Fin (m + 1) → F,
      (∀ j : Fin (m + 1), 0 < j.val → v j = 0) → nilpotentShiftLinGen F m v = 0 := by
    intro v hv; ext i; simp only [Pi.zero_apply]
    rw [nilpotentShiftLinGen_apply]
    split_ifs with h
    · exact hv ⟨i.val + 1, h⟩ (by simp)
    · rfl
  suffices h : LinearMap.ker (nilpotentShiftLinGen F m) =
      Submodule.span F {Pi.single (0 : Fin (m + 1)) (1 : F)} by
    rw [h, finrank_span_singleton]
    simp [Pi.single_eq_zero_iff]
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    have hvj := hker_fwd v hv
    refine ⟨v 0, funext fun j => ?_⟩
    by_cases hj : j = 0
    · subst hj; simp [Pi.single_apply]
    · have hjz := hvj j (Fin.pos_iff_ne_zero.mpr hj)
      simp [Pi.single_apply, hj, hjz]
  · intro ⟨c, hcv⟩
    apply hker_bwd
    intro j hj
    rw [← hcv]
    simp only [Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    rw [if_neg (show j ≠ (0 : Fin (m + 1)) from by intro h; subst h; simp at hj)]

/-! ## Field-generic nilpotent complement lemma -/

private theorem ker_ne_bot_of_isNilpotent_gen
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [Nontrivial V]
    (N : V →ₗ[F] V) (hN : IsNilpotent N) :
    LinearMap.ker N ≠ ⊥ := by
  obtain ⟨k, hk⟩ := hN
  rw [Submodule.ne_bot_iff]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  classical
  have hNkv : (N ^ k) v = 0 := by rw [hk]; simp
  have hex : ∃ j, (N ^ j) v = 0 := ⟨k, hNkv⟩
  set j := Nat.find hex with hj_def
  have hj_spec : (N ^ j) v = 0 := Nat.find_spec hex
  have hj_min : ∀ i < j, (N ^ i) v ≠ 0 := fun i hi => Nat.find_min hex hi
  by_cases hj_pos : 0 < j
  · refine ⟨(N ^ (j - 1)) v, ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      have hjsucc : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hj_pos
      have : (N ^ j) v = 0 := hj_spec
      rw [← hjsucc] at this
      rwa [pow_succ'] at this
    · exact hj_min (j - 1) (Nat.sub_lt hj_pos Nat.one_pos)
  · exfalso; push_neg at hj_pos; interval_cases j; simp at hj_spec; exact hv hj_spec

/-- Field-generic version: If N is nilpotent with 1-dimensional kernel, then any
complement decomposition into N-invariant subspaces has one component trivial. -/
theorem nilpotent_invariant_compl_trivial_gen
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (N : V →ₗ[F] V) (hN : IsNilpotent N)
    (hker : Module.finrank F (LinearMap.ker N) = 1)
    (W₁ W₂ : Submodule F V)
    (hW₁_inv : ∀ x ∈ W₁, N x ∈ W₁)
    (hW₂_inv : ∀ x ∈ W₂, N x ∈ W₂)
    (hcompl : IsCompl W₁ W₂) :
    W₁ = ⊥ ∨ W₂ = ⊥ := by
  by_contra h
  push_neg at h
  obtain ⟨hW₁_ne, hW₂_ne⟩ := h
  have hmap₁ : Set.MapsTo N W₁ W₁ := fun x hx => hW₁_inv x hx
  have hmap₂ : Set.MapsTo N W₂ W₂ := fun x hx => hW₂_inv x hx
  have hN₁ := Module.End.isNilpotent.restrict hmap₁ hN
  have hN₂ := Module.End.isNilpotent.restrict hmap₂ hN
  have hnt₁ : Nontrivial W₁ := Submodule.nontrivial_iff_ne_bot.mpr hW₁_ne
  have hnt₂ : Nontrivial W₂ := Submodule.nontrivial_iff_ne_bot.mpr hW₂_ne
  have hker₁ := ker_ne_bot_of_isNilpotent_gen (N.restrict hmap₁) hN₁
  have hker₂ := ker_ne_bot_of_isNilpotent_gen (N.restrict hmap₂) hN₂
  rw [Submodule.ne_bot_iff] at hker₁ hker₂
  obtain ⟨⟨w₁, hw₁_mem⟩, hw₁_ker, hw₁_ne⟩ := hker₁
  obtain ⟨⟨w₂, hw₂_mem⟩, hw₂_ker, hw₂_ne⟩ := hker₂
  simp only [LinearMap.mem_ker, Submodule.ne_bot_iff] at hw₁_ker hw₂_ker
  have hw₁_inker : w₁ ∈ LinearMap.ker N := by
    rw [LinearMap.mem_ker]
    have := hw₁_ker
    simp only [LinearMap.restrict_apply, Subtype.ext_iff] at this
    exact this
  have hw₂_inker : w₂ ∈ LinearMap.ker N := by
    rw [LinearMap.mem_ker]
    have := hw₂_ker
    simp only [LinearMap.restrict_apply, Subtype.ext_iff] at this
    exact this
  have hw₁_ne0 : w₁ ≠ 0 := fun h => hw₁_ne (Subtype.ext h)
  have hw₂_ne0 : w₂ ≠ 0 := fun h => hw₂_ne (Subtype.ext h)
  have hw₁_ker_elt : (⟨w₁, hw₁_inker⟩ : ↥(LinearMap.ker N)) ≠ 0 := by
    simp [Subtype.ext_iff]; exact hw₁_ne0
  have hdim1 := (finrank_eq_one_iff_of_nonzero' (⟨w₁, hw₁_inker⟩ : ↥(LinearMap.ker N))
    hw₁_ker_elt).mp hker (⟨w₂, hw₂_inker⟩ : ↥(LinearMap.ker N))
  obtain ⟨c, hc⟩ := hdim1
  have hw₂_eq : w₂ = c • w₁ := by
    have := congr_arg Subtype.val hc
    simpa [Submodule.coe_smul] using this.symm
  have hw₂_in_W₁ : w₂ ∈ W₁ := hw₂_eq ▸ W₁.smul_mem c hw₁_mem
  have hmem : w₂ ∈ W₁ ⊓ W₂ := Submodule.mem_inf.mpr ⟨hw₂_in_W₁, hw₂_mem⟩
  rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
  exact hw₂_ne0 hmem

/-! ## Shared infrastructure for per-(k,Q) constructions

The remaining six per-(field, orientation) sub-issues
(#2787-#2793, decomposed from #2773) all rely on the same complementary-pair
algebra: an identity arrow `e : a → b` in a quiver representation forces
`W₁ a ≤ W₁ b` and `W₂ a ≤ W₂ b` (or the reverse, if Q reverses the arrow).
`compl_le_forces_eq` collapses the asymmetric inclusion to subspace
equality at both ends, so the constancy of `W₁`/`W₂` along an undirected
path is independent of how each individual arrow is oriented.
-/

/-- If `(W₁_a, W₂_a)` and `(W₁_b, W₂_b)` are both complementary pairs in a
finite-dimensional space, and `W₁_a ≤ W₁_b`, `W₂_a ≤ W₂_b`, then both
inclusions are equalities. Used in the per-(field, orientation) refactor of
the forbidden-subgraph constructions: identity arrows force subspace
equality regardless of arrow direction.

The four submodules are passed explicitly: when the carrier `V` arises as
`(cycleRep_kQ …).obj a` (a struct projection that does not always
reduce), implicit-argument inference cannot align them across the two
complementary-pair hypotheses. -/
theorem compl_le_forces_eq
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V]
    (W₁_a W₂_a W₁_b W₂_b : Submodule F V)
    (hcompl_a : IsCompl W₁_a W₂_a) (hcompl_b : IsCompl W₁_b W₂_b)
    (h1 : W₁_a ≤ W₁_b) (h2 : W₂_a ≤ W₂_b) :
    W₁_a = W₁_b ∧ W₂_a = W₂_b := by
  have h_sum_a : Module.finrank F W₁_a + Module.finrank F W₂_a = Module.finrank F V :=
    Submodule.finrank_add_eq_of_isCompl hcompl_a
  have h_sum_b : Module.finrank F W₁_b + Module.finrank F W₂_b = Module.finrank F V :=
    Submodule.finrank_add_eq_of_isCompl hcompl_b
  have h_le₁ : Module.finrank F W₁_a ≤ Module.finrank F W₁_b := Submodule.finrank_mono h1
  have h_le₂ : Module.finrank F W₂_a ≤ Module.finrank F W₂_b := Submodule.finrank_mono h2
  have h_eq₁ : Module.finrank F W₁_a = Module.finrank F W₁_b := by omega
  have h_eq₂ : Module.finrank F W₂_a = Module.finrank F W₂_b := by omega
  exact ⟨Submodule.eq_of_le_of_finrank_eq h1 h_eq₁,
         Submodule.eq_of_le_of_finrank_eq h2 h_eq₂⟩

/-! ## Per-(field, orientation) subgraph transfer

The existing `subgraph_infinite_type_transfer` works at the
`IsFiniteTypeQuiver` level (universal over `k` and orientations). The
per-(field, orientation) refactor needs a version that fixes `F` and `Q`
externally and transfers infinite-type from the restricted subgraph
orientation, `restrictOrientationViaEmb φ Q`, to `Q` itself.

The construction mirrors `subgraph_infinite_type_transfer`: an
indecomposable on the subgraph is extended to one on the full graph by
setting the spaces at vertices outside `Set.range φ` to zero. -/

section SubgraphTransferPerKQ

variable {m n : ℕ}

/-- Restrict a quiver `Q` on `Fin n` to `Fin m` via an embedding
`φ : Fin m ↪ Fin n`. The restricted quiver has
`Hom i j := Q.Hom (φ i) (φ j)`. -/
def restrictOrientationViaEmb (φ : Fin m ↪ Fin n) (Q : Quiver (Fin n)) :
    Quiver (Fin m) where
  Hom i j := Q.Hom (φ i) (φ j)

instance restrictOrientationViaEmb_subsingleton
    (φ : Fin m ↪ Fin n) (Q : Quiver (Fin n))
    [hsub : ∀ a b, Subsingleton (Q.Hom a b)] (i j : Fin m) :
    Subsingleton (@Quiver.Hom (Fin m) (restrictOrientationViaEmb φ Q) i j) :=
  hsub (φ i) (φ j)

/-- The restricted orientation is an orientation of the restricted
adjacency matrix whenever `Q` orients `adj` and the adjacencies embed. -/
theorem restrictOrientationViaEmb_isOrientationOf
    (φ : Fin m ↪ Fin n)
    {adj : Matrix (Fin n) (Fin n) ℤ} {adj_sub : Matrix (Fin m) (Fin m) ℤ}
    (hembed : ∀ i j, adj_sub i j = adj (φ i) (φ j))
    {Q : Quiver (Fin n)}
    (hOrient : Etingof.IsOrientationOf Q adj) :
    Etingof.IsOrientationOf (restrictOrientationViaEmb φ Q) adj_sub := by
  obtain ⟨hno, hedge, huniq⟩ := hOrient
  refine ⟨?_, ?_, ?_⟩
  · intro i j hsub
    rw [hembed] at hsub
    exact hno (φ i) (φ j) hsub
  · intro i j hsub
    rw [hembed] at hsub
    exact hedge (φ i) (φ j) hsub
  · intro i j hij hji
    exact huniq (φ i) (φ j) hij hji

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) subgraph transfer: if the restricted
orientation `restrictOrientationViaEmb φ Q` on the subgraph admits
infinitely many indecomposable dimension vectors over `F`, then `Q`
itself does too.

This is the per-(F, Q) analog of `subgraph_infinite_type_transfer`
(which universally quantifies over `k` and orientations). The proof
extends each subgraph indecomposable by zero on the vertices outside
`Set.range φ`. -/
theorem subgraph_infinite_type_transfer_per_kQ
    (φ : Fin m ↪ Fin n)
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (h_inf : letI Q_sub := restrictOrientationViaEmb φ Q
      ¬ Set.Finite
        {d : Fin m → ℕ |
          ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin m) _ Q_sub,
            V.IsIndecomposable ∧
            ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))}) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧
          ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  letI Q_sub : Quiver (Fin m) := restrictOrientationViaEmb φ Q
  -- Subsingleton for the restricted quiver, derived from Q's subsingleton.
  haveI : ∀ a b, Subsingleton (@Quiver.Hom (Fin m) Q_sub a b) := fun a b =>
    inferInstanceAs (Subsingleton (Q.Hom (φ a) (φ b)))
  intro hfin
  apply h_inf
  classical
  let extDV : (Fin m → ℕ) → (Fin n → ℕ) := fun d v =>
    if h : ∃ i, φ i = v then d h.choose else 0
  have h_choose : ∀ i, (⟨i, rfl⟩ : ∃ j, φ j = φ i).choose = i :=
    fun i => φ.injective (⟨i, rfl⟩ : ∃ j, φ j = φ i).choose_spec
  have extDV_apply : ∀ d i, extDV d (φ i) = d i := by
    intro d i; change (if h : ∃ j, φ j = φ i then d h.choose else 0) = d i
    rw [dif_pos ⟨i, rfl⟩, h_choose]
  have hinj : Function.Injective extDV := by
    intro d₁ d₂ h; ext i
    have := congr_fun h (φ i)
    rwa [extDV_apply, extDV_apply] at this
  have hmem : ∀ d,
      d ∈ {d : Fin m → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin m) _ Q_sub,
          V.IsIndecomposable ∧
          ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} →
      extDV d ∈ {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧
          ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro d ⟨V, hV_ind, hV_dim⟩
    let equiv_at : ∀ i : Fin m, V.obj i ≃ₗ[F] (Fin (d i) → F) := fun i => (hV_dim i).some
    let finCastEquiv (a b : ℕ) (h : a = b) : (Fin a → F) ≃ₗ[F] (Fin b → F) :=
      LinearEquiv.funCongrLeft F F (Fin.castOrderIso h.symm).toEquiv
    -- V'.mapLinear at e : Q.Hom a b. When both a, b are in range φ
    -- (a = φ i, b = φ j), the input e itself witnesses
    -- `Nonempty (restrictOrientationViaEmb φ Q).Hom i j`; the if-branch
    -- uses V's map on an arbitrary representative of that hom space
    -- (by Subsingleton, this equals e).
    let V'mapLinear : ∀ {a b : Fin n},
        @Quiver.Hom (Fin n) Q a b → (Fin (extDV d a) → F) →ₗ[F] (Fin (extDV d b) → F) :=
      fun {a b} _ =>
        if h : ∃ i j, φ i = a ∧ φ j = b ∧
            Nonempty (@Quiver.Hom (Fin m) (restrictOrientationViaEmb φ Q) i j) then
          have hi : φ h.choose = a := h.choose_spec.choose_spec.1
          have hj : φ h.choose_spec.choose = b := h.choose_spec.choose_spec.2.1
          have e_sub := h.choose_spec.choose_spec.2.2.some
          let j := h.choose_spec.choose
          let i := h.choose
          (finCastEquiv _ _ ((extDV_apply d j).symm.trans (congrArg (extDV d) hj))).toLinearMap.comp
            ((equiv_at j).toLinearMap.comp
              ((@Etingof.QuiverRepresentation.mapLinear F (Fin m) _
                (restrictOrientationViaEmb φ Q) V _ _ e_sub).comp
                ((equiv_at i).symm.toLinearMap.comp
                  (finCastEquiv _ _
                    ((extDV_apply d i).symm.trans
                      (congrArg (extDV d) hi))).symm.toLinearMap)))
        else 0
    refine ⟨⟨fun v => Fin (extDV d v) → F, V'mapLinear⟩, ?_, fun v => ⟨LinearEquiv.refl F _⟩⟩
    let e_at (i : Fin m) : V.obj i ≃ₗ[F] (Fin (extDV d (φ i)) → F) :=
      (equiv_at i).trans (finCastEquiv (d i) (extDV d (φ i)) (extDV_apply d i).symm)
    constructor
    · obtain ⟨⟨v₀, hv₀⟩, _⟩ := hV_ind
      exact ⟨φ v₀, (e_at v₀).toEquiv.symm.nontrivial⟩
    · intro W₁ W₂ hW₁_inv hW₂_inv hcompl
      have h_ext_zero : ∀ v, v ∉ Set.range φ → extDV d v = 0 := by
        intro v hv
        simp only [extDV, dif_neg (show ¬∃ i, φ i = v from fun ⟨i, hi⟩ => hv ⟨i, hi⟩)]
      have h_bot_of_not_range : ∀ v, v ∉ Set.range φ →
          ∀ (S : Submodule F (Fin (extDV d v) → F)), S = ⊥ := by
        intro v hv S
        have hze := h_ext_zero v hv
        have : Subsingleton (Fin (extDV d v) → F) := by
          rw [hze]; infer_instance
        rw [eq_bot_iff]; intro x _; rw [Submodule.mem_bot]
        exact Subsingleton.elim _ _
      let U₁ (i : Fin m) : Submodule F (V.obj i) := (W₁ (φ i)).comap (e_at i).toLinearMap
      let U₂ (i : Fin m) : Submodule F (V.obj i) := (W₂ (φ i)).comap (e_at i).toLinearMap
      have hU_compl : ∀ i, IsCompl (U₁ i) (U₂ i) := by
        intro i
        have hc := hcompl (φ i)
        constructor
        · rw [disjoint_iff]; rw [eq_bot_iff]; intro x hx
          rw [Submodule.mem_inf] at hx
          have h1 : (e_at i) x ∈ W₁ (φ i) := hx.1
          have h2 : (e_at i) x ∈ W₂ (φ i) := hx.2
          have : (e_at i) x ∈ W₁ (φ i) ⊓ W₂ (φ i) := Submodule.mem_inf.mpr ⟨h1, h2⟩
          rw [hc.1.eq_bot] at this
          rw [Submodule.mem_bot]
          have h_ez := (Submodule.mem_bot F).mp this
          exact (e_at i).injective (h_ez.trans (map_zero _).symm)
        · rw [codisjoint_iff]; rw [eq_top_iff]; intro x _
          have : (e_at i) x ∈ W₁ (φ i) ⊔ W₂ (φ i) := hc.2.eq_top ▸ Submodule.mem_top
          obtain ⟨y₁, hy₁, y₂, hy₂, hsum⟩ := Submodule.mem_sup.mp this
          rw [Submodule.mem_sup]
          refine ⟨(e_at i).symm y₁, ?_, (e_at i).symm y₂, ?_, ?_⟩
          · change (e_at i) ((e_at i).symm y₁) ∈ W₁ (φ i)
            rw [LinearEquiv.apply_symm_apply]; exact hy₁
          · change (e_at i) ((e_at i).symm y₂) ∈ W₂ (φ i)
            rw [LinearEquiv.apply_symm_apply]; exact hy₂
          · apply (e_at i).injective
            rw [map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
            exact hsum
      -- V'mapLinear on a Q.Hom (φ i) (φ j) edge reduces to V's map conjugated by e_at.
      have V'map_aux : ∀ (i j : Fin m)
          (e_sub_ij : @Quiver.Hom (Fin m) (restrictOrientationViaEmb φ Q) i j)
          (i' j' : Fin m) (hi : i' = i) (hj : j' = j)
          (e' : @Quiver.Hom (Fin m) (restrictOrientationViaEmb φ Q) i' j')
          (x : Fin (extDV d (φ i)) → F),
          (finCastEquiv _ _
            ((extDV_apply d j').symm.trans
              (congrArg (extDV d) (show φ j' = φ j by rw [hj])))).toLinearMap.comp
            ((equiv_at j').toLinearMap.comp
              ((@Etingof.QuiverRepresentation.mapLinear F (Fin m) _
                (restrictOrientationViaEmb φ Q) V _ _ e').comp
                ((equiv_at i').symm.toLinearMap.comp
                  (finCastEquiv _ _ ((extDV_apply d i').symm.trans
                    (congrArg (extDV d) (show φ i' = φ i by rw [hi])))).symm.toLinearMap))) x =
          (e_at j) (V.mapLinear e_sub_ij ((e_at i).symm x)) := by
        intro i j e_sub_ij i' j' hi hj e' x
        subst hi; subst hj
        have : e' = e_sub_ij := Subsingleton.elim _ _
        subst this
        rfl
      have V'map_compat : ∀ (i j : Fin m)
          (e_sub_ij : @Quiver.Hom (Fin m) Q_sub i j)
          (x : Fin (extDV d (φ i)) → F),
          V'mapLinear (show @Quiver.Hom (Fin n) Q (φ i) (φ j) from e_sub_ij) x =
          (e_at j) (V.mapLinear e_sub_ij ((e_at i).symm x)) := by
        intro i j e_sub_ij x
        simp only [V'mapLinear]
        have h_ex : ∃ i' j', φ i' = φ i ∧ φ j' = φ j ∧
            Nonempty (@Quiver.Hom (Fin m) Q_sub i' j') :=
          ⟨i, j, rfl, rfl, ⟨e_sub_ij⟩⟩
        rw [dif_pos h_ex]
        exact V'map_aux i j e_sub_ij
          h_ex.choose h_ex.choose_spec.choose
          (φ.injective h_ex.choose_spec.choose_spec.1)
          (φ.injective h_ex.choose_spec.choose_spec.2.1)
          h_ex.choose_spec.choose_spec.2.2.some x
      have hU₁_inv : ∀ {a b : Fin m}
          (e : @Quiver.Hom (Fin m) (restrictOrientationViaEmb φ Q) a b),
          ∀ x ∈ U₁ a, V.mapLinear e x ∈ U₁ b := by
        intro a b e_ab x hx
        change (e_at b) (V.mapLinear e_ab x) ∈ W₁ (φ b)
        have h_compat := V'map_compat a b e_ab ((e_at a) x)
        rw [LinearEquiv.symm_apply_apply] at h_compat
        rw [← h_compat]
        exact hW₁_inv (show @Quiver.Hom (Fin n) Q (φ a) (φ b) from e_ab) _ hx
      have hU₂_inv : ∀ {a b : Fin m}
          (e : @Quiver.Hom (Fin m) (restrictOrientationViaEmb φ Q) a b),
          ∀ x ∈ U₂ a, V.mapLinear e x ∈ U₂ b := by
        intro a b e_ab x hx
        change (e_at b) (V.mapLinear e_ab x) ∈ W₂ (φ b)
        have h_compat := V'map_compat a b e_ab ((e_at a) x)
        rw [LinearEquiv.symm_apply_apply] at h_compat
        rw [← h_compat]
        exact hW₂_inv (show @Quiver.Hom (Fin n) Q (φ a) (φ b) from e_ab) _ hx
      rcases hV_ind.2 U₁ U₂ hU₁_inv hU₂_inv hU_compl with hU₁_bot | hU₂_bot
      · left; intro v
        by_cases hv : v ∈ Set.range φ
        · obtain ⟨i, rfl⟩ := hv
          rw [eq_bot_iff]; intro y hy
          have hU := hU₁_bot i
          have : (e_at i).symm y ∈ U₁ i := by
            change (e_at i) ((e_at i).symm y) ∈ W₁ (φ i)
            rw [LinearEquiv.apply_symm_apply]; exact hy
          rw [hU, Submodule.mem_bot] at this
          rw [Submodule.mem_bot]
          calc y = (e_at i) ((e_at i).symm y) := (LinearEquiv.apply_symm_apply _ _).symm
            _ = (e_at i) 0 := by rw [this]
            _ = 0 := map_zero _
        · exact h_bot_of_not_range v hv (W₁ v)
      · right; intro v
        by_cases hv : v ∈ Set.range φ
        · obtain ⟨i, rfl⟩ := hv
          rw [eq_bot_iff]; intro y hy
          have hU := hU₂_bot i
          have : (e_at i).symm y ∈ U₂ i := by
            change (e_at i) ((e_at i).symm y) ∈ W₂ (φ i)
            rw [LinearEquiv.apply_symm_apply]; exact hy
          rw [hU, Submodule.mem_bot] at this
          rw [Submodule.mem_bot]
          calc y = (e_at i) ((e_at i).symm y) := (LinearEquiv.apply_symm_apply _ _).symm
            _ = (e_at i) 0 := by rw [this]
            _ = 0 := map_zero _
        · exact h_bot_of_not_range v hv (W₂ v)
  exact (hfin.subset (Set.image_subset_iff.mpr hmem)).of_finite_image hinj.injOn

end SubgraphTransferPerKQ

/-! ## Section 7: Direction-aware leaf maps for orientation-generic K_{1,4}

For an arbitrary orientation `Q` of `starAdj`, each leaf edge `{0, i}` is
oriented one of two ways. The canonical direction `i → 0` uses the
embeddings `starEmbed_i_F`. The reversed direction `0 → i` needs a
projection `V_0 → V_i` that is a left inverse of the corresponding
embedding. Below we define four such projections with pairwise distinct
kernels — each kernel equals the image of one of the other three
embeddings. -/

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

/-! ## Section 8: Orientation-generic K_{1,4} representation

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
