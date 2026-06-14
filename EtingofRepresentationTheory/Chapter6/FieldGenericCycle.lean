import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType

/-!
# Field-Generic Cycle Representation

Extracted from `FieldGenericInfiniteType.lean` (originally §3 and §6 of that
file) during the file split tracked by #2825. This module provides the cycle
graph representations:

* `cycleRepGen` / `cycleRepGen_isIndecomposable` / `cycleRepGen_dimVec` /
  `cycle_not_finite_type_gen` — the F-generic version with the canonical
  orientation `cycleQuiver`.
* `cycleRep_kQ` / `cycleRep_kQ_isIndecomposable` / `cycleRep_kQ_dimVec` /
  `cycle_not_finite_type_per_kQ` — the per-(F, Q) version, parametrised by
  an arbitrary orientation `Q` of `cycleAdj k hk`.

See `FieldGenericInfiniteType.lean` for the naming conventions
(`_F` / `_gen`, `_kQ`, `_per_kQ`) and the shared nilpotent shift /
complement primitives (`nilpotentShiftLinGen`,
`nilpotent_invariant_compl_trivial_gen`, `compl_le_forces_eq`) used here.
-/

open scoped Matrix
open Finset

namespace Etingof

/-! ## F-generic cycle representation -/

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

/-! ## Orientation-generic cycle representation -/

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

/-! ## Section: Per-(F, Q) subgraph dispatch wrappers for cycle subgraphs

Mirrors `chordless_cycle_infinite_type` (`InfiniteTypeConstructions.lean:4112`)
and `triangle_infinite_type` (`InfiniteTypeConstructions.lean:3880`): given
an embedding witnessing that `Q` contains a cycle (or a triangle), conclude
that the per-(F, Q) representation set of indecomposable dimension vectors
is infinite. Body-isomorphic to the kQ-free counterparts modulo plumbing
through `(F, Q, hOrient)` via `subgraph_infinite_type_transfer_per_kQ` and
the restricted orientation.

The wrappers are placed here (rather than in `FieldGenericInfiniteType.lean`
next to `subgraph_infinite_type_transfer_per_kQ`) because they depend on
`cycle_not_finite_type_per_kQ`, which lives in this file; the import graph
runs `FieldGenericInfiniteType → FieldGenericCycle`, not the reverse.
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `chordless_cycle_infinite_type`: a graph
containing a chordless cycle of length `k ≥ 3` (witnessed by an embedding
`φ : Fin k ↪ Fin n` exactly preserving the cycle adjacency) has infinite
representation type for every orientation `Q`. -/
theorem chordless_cycle_infinite_type_per_kQ {n k : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (_hsymm : adj.IsSymm)
    (_hdiag : ∀ i, adj i i = 0)
    (hk : 3 ≤ k)
    (φ : Fin k ↪ Fin n)
    (hembed : ∀ i j, cycleAdj k hk i j = adj (φ i) (φ j))
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} :=
  subgraph_infinite_type_transfer_per_kQ φ F Q
    (cycle_not_finite_type_per_kQ F k hk (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `triangle_infinite_type`: a graph containing a
triangle (three pairwise-adjacent distinct vertices) has infinite
representation type for every orientation `Q`. Built as the `k = 3`
specialisation of `chordless_cycle_infinite_type_per_kQ`. -/
theorem triangle_infinite_type_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (_h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h_ab : adj a b = 1) (h_bc : adj b c = 1) (h_ac : adj a c = 1)
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- Construct embedding φ : Fin 3 ↪ Fin n mapping 0 ↦ a, 1 ↦ b, 2 ↦ c.
  let φ_fun : Fin 3 → Fin n := ![a, b, c]
  have hφ_inj : Function.Injective φ_fun := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [φ_fun, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  let φ : Fin 3 ↪ Fin n := ⟨φ_fun, hφ_inj⟩
  have hembed : ∀ i j, cycleAdj 3 (by omega) i j = adj (φ i) (φ j) := by
    intro i j
    have h_ba := (hsymm.apply a b).trans h_ab
    have h_cb := (hsymm.apply b c).trans h_bc
    have h_ca := (hsymm.apply a c).trans h_ac
    fin_cases i <;> fin_cases j <;> simp [cycleAdj, φ, φ_fun, Matrix.cons_val_zero,
      Matrix.cons_val_one, hdiag, h_ab, h_bc, h_ac, h_ba, h_cb, h_ca]
  exact chordless_cycle_infinite_type_per_kQ adj hsymm hdiag (by omega) φ hembed
    F Q hOrient

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `graph_with_list_cycle_infinite_type`: a graph
containing a cycle (given as a list of distinct vertices with edges
between consecutive elements and a closing edge) has infinite
representation type for every orientation `Q`. Proved by strong
induction on cycle length: chordless cycles embed into the abstract
cycle graph via `cycle_not_finite_type_per_kQ` and
`subgraph_infinite_type_transfer_per_kQ`; cycles with chords yield
strictly shorter sub-cycles handled recursively. -/
theorem graph_with_list_cycle_infinite_type_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (cycle : List (Fin n))
    (hlen : 3 ≤ cycle.length)
    (hnodup : cycle.Nodup)
    (hedge : ∀ k, (hk : k + 1 < cycle.length) →
      adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, hk⟩) = 1)
    (hclose : adj (cycle.get ⟨cycle.length - 1, by omega⟩)
                   (cycle.get ⟨0, by omega⟩) = 1)
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- Strong induction on cycle length, quantified over all cycles of that length
  revert cycle hlen hnodup hedge hclose
  have key : ∀ m, (hm : 3 ≤ m) → ∀ (cyc : List (Fin n)), (hlen : cyc.length = m) → cyc.Nodup →
      (∀ k, (hk : k + 1 < cyc.length) →
        adj (cyc.get ⟨k, by omega⟩) (cyc.get ⟨k + 1, hk⟩) = 1) →
      (adj (cyc.get ⟨cyc.length - 1, by omega⟩) (cyc.get ⟨0, by omega⟩) = 1) →
      ¬ Set.Finite
        {d : Fin n → ℕ |
          ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
            V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro hm cyc hcyc_len hcyc_nodup hcyc_edge hcyc_close
      -- Check if cycle has a chord: ∃ i j with i < j, j - i ≥ 2, not closing edge, adjacent
      by_cases h_chord :
        ∃ (i j : Fin cyc.length), i.val < j.val ∧ j.val - i.val ≥ 2 ∧
          ¬(i.val = 0 ∧ j.val = cyc.length - 1) ∧
          adj (cyc.get i) (cyc.get j) = 1
      · -- Chord case: extract shorter sub-cycle and apply IH
        obtain ⟨p, q, hpq, hdist, hnot_close, hadj_chord⟩ := h_chord
        -- Extract natural number indices
        have hi : p.val < cyc.length := p.isLt
        have hj : q.val < cyc.length := q.isLt
        have hij : p.val < q.val := hpq
        have hdist2 : q.val - p.val ≥ 2 := hdist
        -- The sub-cycle is cyc[p], cyc[p+1], ..., cyc[q] with closing edge from chord
        set subcyc := (cyc.drop p.val).take (q.val - p.val + 1) with hsubcyc_def
        have hsublen : subcyc.length = q.val - p.val + 1 := by
          simp [hsubcyc_def, List.length_take, List.length_drop]; omega
        have hsublen3 : 3 ≤ q.val - p.val + 1 := by omega
        have hsublt : q.val - p.val + 1 < m := by
          subst hcyc_len; push_neg at hnot_close
          by_cases hp0 : p.val = 0
          · have := hnot_close hp0; omega
          · omega
        -- Sub-cycle elements match original cycle shifted by p
        have hsubget : ∀ (k : ℕ) (hk : k < subcyc.length),
            subcyc.get ⟨k, hk⟩ = cyc.get ⟨p.val + k, by rw [hsublen] at hk; omega⟩ := by
          intro k hk
          simp only [List.get_eq_getElem, hsubcyc_def, List.getElem_take, List.getElem_drop]
        -- Nodup
        have hsub_nodup : subcyc.Nodup :=
          hcyc_nodup.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
        -- Consecutive edges
        have hsub_edge : ∀ k, (hk : k + 1 < subcyc.length) →
            adj (subcyc.get ⟨k, by omega⟩) (subcyc.get ⟨k + 1, hk⟩) = 1 := by
          intro k hk
          rw [hsubget k (by omega), hsubget (k + 1) (by omega)]
          have hik : p.val + k + 1 < cyc.length := by rw [hsublen] at hk; omega
          have : cyc.get ⟨p.val + (k + 1), by omega⟩ = cyc.get ⟨p.val + k + 1, hik⟩ := by
            congr 1
          rw [this]
          exact hcyc_edge (p.val + k) hik
        -- Closing edge: adj(cyc[q], cyc[p]) = 1 (the chord, via symmetry)
        have hsub_close : adj (subcyc.get ⟨subcyc.length - 1, by omega⟩)
            (subcyc.get ⟨0, by omega⟩) = 1 := by
          rw [hsubget _ (by omega), hsubget 0 (by omega)]
          have h1 : cyc.get ⟨p.val + (subcyc.length - 1), by omega⟩ = cyc.get q := by
            congr 1; ext; simp [hsublen]; omega
          have h2 : cyc.get ⟨p.val + 0, by omega⟩ = cyc.get p := by
            congr 1
          rw [h1, h2, hsymm.apply]; exact hadj_chord
        exact ih (q.val - p.val + 1) hsublt hsublen3 subcyc hsublen hsub_nodup hsub_edge
          hsub_close
      · -- Chordless case: embed into cycle graph
        push_neg at h_chord
        -- The embedding φ : Fin m → Fin n sends i to cyc[i]
        let φ_fun : Fin m → Fin n := fun i => cyc.get ⟨i.val, by omega⟩
        have hφ_inj : Function.Injective φ_fun := by
          intro a b hab
          simp only [φ_fun] at hab
          exact Fin.ext (Fin.mk.inj (hcyc_nodup.injective_get hab))
        let φ : Fin m ↪ Fin n := ⟨φ_fun, hφ_inj⟩
        have hembed : ∀ i j, cycleAdj m hm i j = adj (φ i) (φ j) := by
          intro ⟨i, hi⟩ ⟨j, hj⟩
          simp only [cycleAdj, φ, φ_fun]
          split_ifs with h
          · -- Adjacent in cycle → adj = 1
            rcases h with h_fwd | h_bwd
            · -- j = (i + 1) % m
              by_cases him : i + 1 < m
              · rw [Nat.mod_eq_of_lt him] at h_fwd; subst h_fwd
                exact (hcyc_edge i (by omega)).symm
              · have hi_eq : i = m - 1 := by omega
                rw [hi_eq, show m - 1 + 1 = m from by omega, Nat.mod_self] at h_fwd
                subst hi_eq; subst h_fwd
                have := hcyc_close.symm; convert this using 2; all_goals (ext; simp_all)
            · -- i = (j + 1) % m (symmetric case)
              by_cases hjm : j + 1 < m
              · rw [Nat.mod_eq_of_lt hjm] at h_bwd; subst h_bwd
                rw [hsymm.apply]; exact (hcyc_edge j (by omega)).symm
              · have hj_eq : j = m - 1 := by omega
                rw [hj_eq, show m - 1 + 1 = m from by omega, Nat.mod_self] at h_bwd
                subst hj_eq; subst h_bwd
                rw [hsymm.apply]
                have := hcyc_close.symm; convert this using 2; all_goals (ext; simp_all)
          · -- Not adjacent in cycle → adj = 0
            push_neg at h
            by_cases hij : i = j
            · subst hij; exact (hdiag _).symm
            · -- Distinct non-adjacent: no chord → adj = 0
              -- Convert h from modular to direct form
              have h_not_fwd : j ≠ (i + 1) % m := h.1
              have h_not_bwd : i ≠ (j + 1) % m := h.2
              rcases Nat.lt_or_ge i j with h_lt | h_ge
              · -- i < j
                have hdist : j - i ≥ 2 := by
                  by_contra hd; push_neg at hd
                  have hji : j = i + 1 := by omega
                  subst hji; exact h_not_fwd (Nat.mod_eq_of_lt (by omega)).symm
                have hnotclose : i = 0 → j ≠ cyc.length - 1 := by
                  intro hi0; subst hi0
                  intro hjm; rw [hcyc_len] at hjm; subst hjm
                  exact h_not_bwd (by rw [show m - 1 + 1 = m from by omega, Nat.mod_self])
                have h_not1 := h_chord ⟨i, by omega⟩ ⟨j, by omega⟩ h_lt hdist hnotclose
                rcases h01 (cyc.get ⟨i, by omega⟩) (cyc.get ⟨j, by omega⟩) with h0 | h1
                · exact h0.symm
                · exact absurd h1 h_not1
              · -- j < i
                have h_lt : j < i := by omega
                have hdist : i - j ≥ 2 := by
                  by_contra hd; push_neg at hd
                  have hij2 : i = j + 1 := by omega
                  subst hij2; exact h_not_bwd (Nat.mod_eq_of_lt (by omega)).symm
                have hnotclose : j = 0 → i ≠ cyc.length - 1 := by
                  intro hj0; subst hj0
                  intro him; rw [hcyc_len] at him; subst him
                  exact h_not_fwd (by rw [show m - 1 + 1 = m from by omega, Nat.mod_self])
                have h_not1 := h_chord ⟨j, by omega⟩ ⟨i, by omega⟩ h_lt hdist hnotclose
                rcases h01 (cyc.get ⟨i, by omega⟩) (cyc.get ⟨j, by omega⟩) with h0 | h1
                · exact h0.symm
                · rw [hsymm.apply] at h1; exact absurd h1 h_not1
        exact subgraph_infinite_type_transfer_per_kQ φ F Q
          (cycle_not_finite_type_per_kQ F m hm (restrictOrientationViaEmb φ Q)
            (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))
  intro cycle hlen hnodup hedge hclose
  exact key cycle.length hlen cycle rfl hnodup hedge hclose

end Etingof
