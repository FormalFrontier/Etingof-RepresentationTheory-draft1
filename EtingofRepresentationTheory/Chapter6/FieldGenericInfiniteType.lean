import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions

/-!
# Field-Generic Infinite Type Constructions

This file provides field-generic versions of the infinite type constructions from
`InfiniteTypeConstructions.lean`. The originals are ℂ-specific; these work over
any field F (or any algebraically closed field when needed).

The key insight: all the indecomposability proofs use only linear algebra
(nilpotent maps, kernel dimension, complementary subspaces). None of this
requires ℂ specifically.
-/

open scoped Matrix
open Finset

namespace Etingof

/-! ## Section 1: Field-generic nilpotent shift -/

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

/-! ## Section 2: Field-generic nilpotent complement lemma -/

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

/-! ## Section 3: Field-generic cycle representation -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The cycle representation over an arbitrary field F. At each vertex the space
is Fin (m+1) → F. Non-last arrows map by the identity; the last arrow uses
the nilpotent shift. -/
noncomputable def cycleRepGen (F : Type) [Field F] (k : ℕ) (hk : 3 ≤ k) (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin k) _ (cycleQuiver k hk) := by
  letI := cycleQuiver k hk
  exact { obj := fun _ => Fin (m + 1) → F
          mapLinear := fun {v _} _ =>
            if v.val = k - 1 then nilpotentShiftLinGen F m else LinearMap.id }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem cycleRepGen_isIndecomposable (F : Type) [Field F] (k : ℕ) (hk : 3 ≤ k) (m : ℕ) :
    @Etingof.QuiverRepresentation.IsIndecomposable F _ (Fin k)
      (cycleQuiver k hk) (cycleRepGen F k hk m) := by
  letI := cycleQuiver k hk
  constructor
  · refine ⟨⟨0, by omega⟩, ?_⟩
    change Nontrivial (Fin (m + 1) → F)
    infer_instance
  · intro W₁ W₂ hW₁_inv hW₂_inv hcompl
    have hle_succ : ∀ (W : ∀ v, Submodule F ((cycleRepGen F k hk m).obj v)),
        (∀ {a b : Fin k} (e : @Quiver.Hom _ (cycleQuiver k hk) a b),
          ∀ x ∈ W a, (cycleRepGen F k hk m).mapLinear e x ∈ W b) →
        ∀ (v : Fin k) (hv : v.val + 1 < k), W v ≤ W ⟨v.val + 1, hv⟩ := by
      intro W hW_inv v hv x hx
      have harrow : @Quiver.Hom (Fin k) (cycleQuiver k hk) v
          ⟨v.val + 1, by omega⟩ := ⟨by simp [Nat.mod_eq_of_lt hv]⟩
      have := hW_inv harrow x hx
      simp only [cycleRepGen] at this
      have hne : v.val ≠ k - 1 := by have := v.isLt; omega
      rw [if_neg hne] at this
      exact this
    have hchain_mono : ∀ (W : ∀ v, Submodule F ((cycleRepGen F k hk m).obj v)),
        (∀ {a b : Fin k} (e : @Quiver.Hom _ (cycleQuiver k hk) a b),
          ∀ x ∈ W a, (cycleRepGen F k hk m).mapLinear e x ∈ W b) →
        ∀ (i j : ℕ) (hi : i < k) (hj : j < k), i ≤ j → W ⟨i, hi⟩ ≤ W ⟨j, hj⟩ := by
      intro W hW_inv i j hi hj hij
      induction j with
      | zero => simp at hij; subst hij; exact le_of_eq (by congr 1)
      | succ n ih =>
        rcases Nat.eq_or_lt_of_le hij with rfl | hlt
        · exact le_refl _
        · exact le_trans (ih (by omega) (by omega)) (hle_succ W hW_inv ⟨n, by omega⟩ hj)
    set last : Fin k := ⟨k - 1, by omega⟩
    have hlast_arrow : @Quiver.Hom (Fin k) (cycleQuiver k hk) last
        ⟨0, by omega⟩ := ⟨by
          show (0 : ℕ) = (k - 1 + 1) % k
          rw [show k - 1 + 1 = k from by omega, Nat.mod_self]⟩
    have hshift₁ : ∀ x ∈ W₁ last, nilpotentShiftLinGen F m x ∈ W₁ last := by
      intro x hx
      have h_in_0 := hW₁_inv hlast_arrow x hx
      simp only [cycleRepGen, show last.val = k - 1 from rfl, ite_true] at h_in_0
      exact hchain_mono W₁ hW₁_inv 0 (k - 1) (by omega) (by omega) (by omega) h_in_0
    have hshift₂ : ∀ x ∈ W₂ last, nilpotentShiftLinGen F m x ∈ W₂ last := by
      intro x hx
      have h_in_0 := hW₂_inv hlast_arrow x hx
      simp only [cycleRepGen, show last.val = k - 1 from rfl, ite_true] at h_in_0
      exact hchain_mono W₂ hW₂_inv 0 (k - 1) (by omega) (by omega) (by omega) h_in_0
    have hresult := nilpotent_invariant_compl_trivial_gen
      (nilpotentShiftLinGen F m) (nilpotentShiftLinGen_nilpotent F m)
      (nilpotentShiftLinGen_ker_finrank F m)
      (W₁ last) (W₂ last) hshift₁ hshift₂ (hcompl last)
    rcases hresult with h | h
    · left; intro v
      have : W₁ v ≤ W₁ last :=
        hchain_mono W₁ hW₁_inv v.val (k - 1) v.isLt (by omega) (by omega)
      rwa [h, le_bot_iff] at this
    · right; intro v
      have : W₂ v ≤ W₂ last :=
        hchain_mono W₂ hW₂_inv v.val (k - 1) v.isLt (by omega) (by omega)
      rwa [h, le_bot_iff] at this

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem cycleRepGen_dimVec (F : Type) [Field F] (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (v : Fin k) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin k) _
      (cycleQuiver k hk) (cycleRepGen F k hk m) v ≃ₗ[F] (Fin (m + 1) → F)) :=
  ⟨LinearEquiv.refl F _⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Field-generic: the cycle graph on k ≥ 3 vertices has infinite representation type
over any field F. -/
theorem cycle_not_finite_type_gen (F : Type) [Field F] (k : ℕ) (hk : 3 ≤ k) :
    ¬ ∀ (Q : @Quiver.{0, 0} (Fin k))
      [∀ (a b : Fin k), Subsingleton (@Quiver.Hom (Fin k) Q a b)],
      @Etingof.IsOrientationOf k Q (cycleAdj k hk) →
      Set.Finite
        {d : Fin k → ℕ |
          ∃ (V : @Etingof.QuiverRepresentation.{0, 0, 0, 0} F (Fin k) _ Q),
            V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hft
  letI := cycleQuiver k hk
  have hfin := @hft (cycleQuiver k hk)
    (fun a b => cycleQuiver_subsingleton k hk a b)
    (cycleOrientation_isOrientationOf k hk)
  have hmem : ∀ m : ℕ, (fun (_ : Fin k) => m + 1) ∈
      {d : Fin k → ℕ | ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin k) _ (cycleQuiver k hk),
        V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨cycleRepGen F k hk m, cycleRepGen_isIndecomposable F k hk m,
      cycleRepGen_dimVec F k hk m⟩
  have hinj : Function.Injective (fun m : ℕ => (fun (_ : Fin k) => m + 1)) := by
    intro m₁ m₂ h
    have : m₁ + 1 = m₂ + 1 := congr_fun h ⟨0, by omega⟩
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section 4: Field-generic star (K_{1,4} / D̃₄) representation

The construction mirrors `starRep` from `InfiniteTypeConstructions.lean` over an
arbitrary field `F`, keeping the canonical all-sink orientation `starQuiver`.
Dimension vector: `(2(m+1), m+1, m+1, m+1, m+1)`. The four leaf maps are
`starEmbed1_F`, `starEmbed2_F`, `starEmbedDiag_F`, `starEmbedNilp_F`.
-/

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

/-! ## Section 5: Shared infrastructure for per-(k,Q) constructions

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

/-! ## Section 6: Orientation-generic cycle representation -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic cycle representation. At each vertex the space is
`Fin (m+1) → F`. The "closing edge" (between vertices `0` and `k-1`)
carries the nilpotent shift; all other arrows carry the identity. The
closing edge is detected from the pair `{a.val, b.val}`, not the arrow
direction, so the construction works for any orientation `Q` of the cycle
adjacency matrix `cycleAdj k hk`. -/
noncomputable def cycleRep_kQ
    (F : Type) [Field F] (k : ℕ) (hk : 3 ≤ k)
    (Q : @Quiver.{0, 0} (Fin k))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin k) Q a b)]
    (_ : @Etingof.IsOrientationOf k Q (cycleAdj k hk))
    (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin k) _ Q := by
  letI := Q
  exact { obj := fun _ => Fin (m + 1) → F
          mapLinear := fun {a b} _ =>
            if (a.val = 0 ∧ b.val = k - 1) ∨ (a.val = k - 1 ∧ b.val = 0) then
              nilpotentShiftLinGen F m
            else
              LinearMap.id }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem cycleRep_kQ_isIndecomposable
    (F : Type) [Field F] (k : ℕ) (hk : 3 ≤ k)
    (Q : @Quiver.{0, 0} (Fin k))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin k) Q a b)]
    (hOrient : @Etingof.IsOrientationOf k Q (cycleAdj k hk))
    (m : ℕ) :
    (cycleRep_kQ F k hk Q hOrient m).IsIndecomposable := by
  obtain ⟨_, hOrient_edge, _⟩ := hOrient
  constructor
  · refine ⟨⟨0, by omega⟩, ?_⟩
    change Nontrivial (Fin (m + 1) → F)
    infer_instance
  · intro W₁ W₂ hW₁_inv hW₂_inv hcompl
    -- Step 1: each adjacent pair (i, i+1) with i+1 < k yields W₁ i = W₁ (i+1).
    -- Either the arrow in Q goes i → i+1 (identity map gives W₁ i ≤ W₁ (i+1))
    -- or i+1 → i (gives W₁ (i+1) ≤ W₁ i). Either way `compl_le_forces_eq`
    -- collapses to equality.
    have h_eq_succ : ∀ (i : ℕ) (hi : i + 1 < k),
        W₁ ⟨i, by omega⟩ = W₁ ⟨i + 1, hi⟩ ∧ W₂ ⟨i, by omega⟩ = W₂ ⟨i + 1, hi⟩ := by
      intro i hi
      set a : Fin k := ⟨i, by omega⟩
      set b : Fin k := ⟨i + 1, hi⟩
      have ha_val : a.val = i := rfl
      have hb_val : b.val = i + 1 := rfl
      have h_adj_ab : cycleAdj k hk a b = 1 := by
        simp only [cycleAdj]
        rw [if_pos]
        left
        show b.val = (a.val + 1) % k
        rw [hb_val, ha_val, Nat.mod_eq_of_lt hi]
      have h_not_closing_ab :
          ¬ ((a.val = 0 ∧ b.val = k - 1) ∨ (a.val = k - 1 ∧ b.val = 0)) := by
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
      have h_not_closing_ba :
          ¬ ((b.val = 0 ∧ a.val = k - 1) ∨ (b.val = k - 1 ∧ a.val = 0)) := by
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
      rcases hOrient_edge a b h_adj_ab with hQab | hQba
      · -- arrow a → b in Q; mapLinear e = id
        obtain ⟨e⟩ := hQab
        have h_inv₁ : W₁ a ≤ W₁ b := fun x hx => by
          have h := hW₁_inv e x hx
          simp only [cycleRep_kQ, if_neg h_not_closing_ab, LinearMap.id_coe, id_eq] at h
          exact h
        have h_inv₂ : W₂ a ≤ W₂ b := fun x hx => by
          have h := hW₂_inv e x hx
          simp only [cycleRep_kQ, if_neg h_not_closing_ab, LinearMap.id_coe, id_eq] at h
          exact h
        exact compl_le_forces_eq (V := Fin (m + 1) → F) (W₁ a) (W₂ a) (W₁ b) (W₂ b)
          (hcompl a) (hcompl b) h_inv₁ h_inv₂
      · -- arrow b → a in Q; mapLinear e = id
        obtain ⟨e⟩ := hQba
        have h_inv₁ : W₁ b ≤ W₁ a := fun x hx => by
          have h := hW₁_inv e x hx
          simp only [cycleRep_kQ, if_neg h_not_closing_ba, LinearMap.id_coe, id_eq] at h
          exact h
        have h_inv₂ : W₂ b ≤ W₂ a := fun x hx => by
          have h := hW₂_inv e x hx
          simp only [cycleRep_kQ, if_neg h_not_closing_ba, LinearMap.id_coe, id_eq] at h
          exact h
        have ⟨h1, h2⟩ := compl_le_forces_eq (V := Fin (m + 1) → F)
          (W₁ b) (W₂ b) (W₁ a) (W₂ a)
          (hcompl b) (hcompl a) h_inv₁ h_inv₂
        exact ⟨h1.symm, h2.symm⟩
    -- Step 2: W₁ and W₂ are constant across all vertices.
    have h_const : ∀ (v : Fin k),
        W₁ v = W₁ ⟨0, by omega⟩ ∧ W₂ v = W₂ ⟨0, by omega⟩ := by
      rintro ⟨i, hi⟩
      induction i with
      | zero => exact ⟨rfl, rfl⟩
      | succ n ih =>
        have ihn := ih (by omega)
        have h_step := h_eq_succ n hi
        exact ⟨h_step.1.symm.trans ihn.1, h_step.2.symm.trans ihn.2⟩
    -- Step 3: At the closing edge, the nilpotent shift preserves both W₁ and W₂
    -- at vertex 0 (using constancy from Step 2).
    set z : Fin k := ⟨0, by omega⟩
    set last : Fin k := ⟨k - 1, by omega⟩
    have h_adj_closing : cycleAdj k hk z last = 1 := by
      simp only [cycleAdj]
      rw [if_pos]
      right
      show z.val = (last.val + 1) % k
      simp only [z, last]
      rw [show k - 1 + 1 = k from by omega, Nat.mod_self]
    rcases hOrient_edge z last h_adj_closing with hQzl | hQlz
    · -- arrow z → last; mapLinear e = nilpotentShiftLinGen
      obtain ⟨e⟩ := hQzl
      have h_close_zl :
          (z.val = 0 ∧ last.val = k - 1) ∨ (z.val = k - 1 ∧ last.val = 0) := by
        left; refine ⟨rfl, rfl⟩
      have h_shift₁ : ∀ x ∈ W₁ z, nilpotentShiftLinGen F m x ∈ W₁ z := by
        intro x hx
        have h := hW₁_inv e x hx
        simp only [cycleRep_kQ, if_pos h_close_zl] at h
        rw [(h_const last).1] at h
        exact h
      have h_shift₂ : ∀ x ∈ W₂ z, nilpotentShiftLinGen F m x ∈ W₂ z := by
        intro x hx
        have h := hW₂_inv e x hx
        simp only [cycleRep_kQ, if_pos h_close_zl] at h
        rw [(h_const last).2] at h
        exact h
      have hres := nilpotent_invariant_compl_trivial_gen
        (nilpotentShiftLinGen F m) (nilpotentShiftLinGen_nilpotent F m)
        (nilpotentShiftLinGen_ker_finrank F m)
        (W₁ z) (W₂ z) h_shift₁ h_shift₂ (hcompl z)
      rcases hres with h | h
      · left; intro v; exact (h_const v).1.trans h
      · right; intro v; exact (h_const v).2.trans h
    · -- arrow last → z; mapLinear e = nilpotentShiftLinGen
      obtain ⟨e⟩ := hQlz
      have h_close_lz :
          (last.val = 0 ∧ z.val = k - 1) ∨ (last.val = k - 1 ∧ z.val = 0) := by
        right; refine ⟨rfl, rfl⟩
      have h_shift₁ : ∀ x ∈ W₁ z, nilpotentShiftLinGen F m x ∈ W₁ z := by
        intro x hx
        rw [(h_const last).1.symm] at hx
        have h := hW₁_inv e x hx
        simp only [cycleRep_kQ, if_pos h_close_lz] at h
        exact h
      have h_shift₂ : ∀ x ∈ W₂ z, nilpotentShiftLinGen F m x ∈ W₂ z := by
        intro x hx
        rw [(h_const last).2.symm] at hx
        have h := hW₂_inv e x hx
        simp only [cycleRep_kQ, if_pos h_close_lz] at h
        exact h
      have hres := nilpotent_invariant_compl_trivial_gen
        (nilpotentShiftLinGen F m) (nilpotentShiftLinGen_nilpotent F m)
        (nilpotentShiftLinGen_ker_finrank F m)
        (W₁ z) (W₂ z) h_shift₁ h_shift₂ (hcompl z)
      rcases hres with h | h
      · left; intro v; exact (h_const v).1.trans h
      · right; intro v; exact (h_const v).2.trans h

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem cycleRep_kQ_dimVec
    (F : Type) [Field F] (k : ℕ) (hk : 3 ≤ k)
    (Q : @Quiver.{0, 0} (Fin k))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin k) Q a b)]
    (hOrient : @Etingof.IsOrientationOf k Q (cycleAdj k hk))
    (m : ℕ) (v : Fin k) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin k) _
      Q (cycleRep_kQ F k hk Q hOrient m) v ≃ₗ[F] (Fin (m + 1) → F)) :=
  ⟨LinearEquiv.refl F _⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) version of `cycle_not_finite_type_gen`:
for any field `F`, any size `k ≥ 3`, and any orientation `Q` of the cycle
graph on `k` vertices, the set of dimension vectors of indecomposable
representations is infinite. -/
theorem cycle_not_finite_type_per_kQ
    (F : Type) [Field F] (k : ℕ) (hk : 3 ≤ k)
    (Q : @Quiver.{0, 0} (Fin k))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin k) Q a b)]
    (hOrient : @Etingof.IsOrientationOf k Q (cycleAdj k hk)) :
    ¬ Set.Finite
      {d : Fin k → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin k) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ, (fun (_ : Fin k) => m + 1) ∈
      {d : Fin k → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin k) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨cycleRep_kQ F k hk Q hOrient m,
      cycleRep_kQ_isIndecomposable F k hk Q hOrient m,
      cycleRep_kQ_dimVec F k hk Q hOrient m⟩
  have hinj : Function.Injective (fun m : ℕ => (fun (_ : Fin k) => m + 1)) := by
    intro m₁ m₂ h
    have : m₁ + 1 = m₂ + 1 := congr_fun h ⟨0, by omega⟩
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section 8: Per-(field, orientation) subgraph transfer

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

end Etingof
