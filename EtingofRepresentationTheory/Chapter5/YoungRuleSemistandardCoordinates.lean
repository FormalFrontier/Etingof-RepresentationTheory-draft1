/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import EtingofRepresentationTheory.Chapter5.YoungRuleTableauBasis

/-!
# Tabloid coordinates for the semistandard vectors in Young's rule

This file records the canonical row-averaged Specht vector attached to a Kostka tableau and
computes its image in the tabloid representation.  The formula exposes the two finite sums
needed for a coefficient-separation argument: row permutations act by right translation of
tabloids, while the standard polytabloid contributes its column-antisymmetrizer expansion.
-/

namespace Etingof

noncomputable section

/-- Right multiplication of tabloids by inverse permutations cancels. -/
@[simp] theorem tabloidRightMul_inv_apply {n : ℕ} {nu : Nat.Partition n}
    (p : Equiv.Perm (Fin n)) (t : Tabloid n nu) :
    tabloidRightMul (la := nu) p⁻¹ (tabloidRightMul (la := nu) p t) = t := by
  induction t using Quotient.inductionOn with
  | _ σ =>
      change toTabloid n nu ((σ * p) * p⁻¹) = toTabloid n nu σ
      congr 1
      group

/-- Right multiplication is injective on tabloids. -/
theorem tabloidRightMul_injective {n : ℕ} {nu : Nat.Partition n}
    (p : Equiv.Perm (Fin n)) :
    Function.Injective (tabloidRightMul (la := nu) p) := by
  intro t u h
  have := congrArg (tabloidRightMul (la := nu) p⁻¹) h
  simpa using this

/-- After tabloid projection, the canonical semistandard vector is the normalized sum of
the right translates of its standard polytabloid by the content row subgroup. -/
theorem tabloidProjectionSpecht_youngRuleRowAverageRange_standardization {n : ℕ}
    {mu nu : Nat.Partition n} (T : KostkaTableau n nu mu) :
    letI := Fintype.ofFinite (↥(RowSubgroup n mu))
    tabloidProjectionSpecht
          ((youngRuleRowAverageRange n mu nu
            (spechtPolytabloid T.standardization)).1) =
        (Nat.card (↥(RowSubgroup n mu)) : ℂ)⁻¹ •
          ∑ p : ↥(RowSubgroup n mu),
            Finsupp.mapDomain (tabloidRightMul (la := nu) p.val⁻¹)
              (polytabloidTab T.standardization) := by
  classical
  unfold tabloidProjectionSpecht youngRuleRowAverageRange youngRuleRowAverage
  change tabloidProjection
      ((Nat.card (↥(RowSubgroup n mu)) : ℂ)⁻¹ •
        (RowSymmetrizer n mu *
          (spechtPolytabloid T.standardization : SymGroupAlgebra n))) = _
  rw [map_smul]
  congr 1
  simp only [RowSymmetrizer, Finset.sum_mul, map_sum, tabloidProjection_of_mul,
    tabloidProjection_spechtPolytabloid]
  apply Finset.sum_congr
  · ext
    simp
  · intro p hp
    rfl

/-- Coordinate form of the projected semistandard vector.  At a tabloid `t`, each row
permutation contributes the coefficient of the original standard polytabloid at the inverse
right translate, equivalently at `t · p`. -/
theorem tabloidProjectionSpecht_youngRuleRowAverageRange_standardization_apply {n : ℕ}
    {mu nu : Nat.Partition n} (T : KostkaTableau n nu mu) (t : Tabloid n nu) :
    letI := Fintype.ofFinite (↥(RowSubgroup n mu))
    tabloidProjectionSpecht
          ((youngRuleRowAverageRange n mu nu
            (spechtPolytabloid T.standardization)).1) t =
        (Nat.card (↥(RowSubgroup n mu)) : ℂ)⁻¹ *
          ∑ p : ↥(RowSubgroup n mu),
            polytabloidTab T.standardization
              (tabloidRightMul (la := nu) p.val t) := by
  classical
  rw [tabloidProjectionSpecht_youngRuleRowAverageRange_standardization T]
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply]
  congr 1
  apply Finset.sum_congr
  · ext
    simp
  · intro p hp
    let a := tabloidRightMul (la := nu) p.val t
    have ha : tabloidRightMul (la := nu) p.val⁻¹ a = t :=
      tabloidRightMul_inv_apply p.val t
    calc
      Finsupp.mapDomain (tabloidRightMul (la := nu) p.val⁻¹)
          (polytabloidTab T.standardization) t =
          Finsupp.mapDomain (tabloidRightMul (la := nu) p.val⁻¹)
            (polytabloidTab T.standardization)
              (tabloidRightMul (la := nu) p.val⁻¹ a) := by rw [ha]
      _ = polytabloidTab T.standardization a :=
        Finsupp.mapDomain_apply
          (tabloidRightMul_injective (nu := nu) p.val⁻¹)
          (polytabloidTab T.standardization) a

/-- A nonzero distinguished-orbit coordinate of one canonical averaged vector forces
tabloid dominance after a content-row permutation.  This is the triangular support statement
needed by a maximal-coordinate linear-independence argument. -/
theorem youngRuleRowAverageRange_standardization_coeff_dominance {n : ℕ}
    {mu nu : Nat.Partition n} (T U : KostkaTableau n nu mu)
    (hne : tabloidProjectionSpecht
      ((youngRuleRowAverageRange n mu nu
        (spechtPolytabloid T.standardization)).1)
          (sytToTabloid n nu U.standardization) ≠ 0) :
    ∃ p : ↥(RowSubgroup n mu),
      tabloidDominates nu (sytPerm n nu T.standardization)
        (sytPerm n nu U.standardization * p.val) := by
  classical
  letI := Fintype.ofFinite (↥(RowSubgroup n mu))
  rw [tabloidProjectionSpecht_youngRuleRowAverageRange_standardization_apply]
    at hne
  have hsum :
      (∑ p : ↥(RowSubgroup n mu),
        polytabloidTab T.standardization
          (tabloidRightMul (la := nu) p.val
            (sytToTabloid n nu U.standardization))) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hne
    exact hne rfl
  obtain ⟨p, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨p, polytabloidTab_coeff_dominance T.standardization
    (sytPerm n nu U.standardization * p.val) ?_⟩
  simpa only [sytToTabloid, tabloidRightMul_toTabloid] using hp.2

/-! ### Block-cutoff cumulative profiles -/

/-- Count labels in the first `a` content blocks whose cells lie in the first
`i` rows of a tabloid represented by `σ`. -/
noncomputable def youngRuleBlockCumulCount {n : ℕ} (mu nu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (a i : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun e =>
    rowOfPos mu.sortedParts e.val < a ∧
      rowOfPos nu.sortedParts (σ e).val < i).card

/-- The intrinsic cumulative profile of a Kostka tableau: cells in the first
`i` shape rows carrying entries in the first `a` content blocks. -/
noncomputable def KostkaTableau.cumulativeProfile {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (a i : ℕ) : ℕ :=
  ((Finset.univ : Finset (Cell n nu)).filter fun c =>
    T.1 c.1.1 c.1.2 < a ∧ c.1.1 < i).card

/-- Right multiplication by a content-row permutation does not change any
block-cutoff cumulative count. -/
theorem youngRuleBlockCumulCount_mul_row {n : ℕ} (mu nu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (p : Equiv.Perm (Fin n))
    (hp : p ∈ RowSubgroup n mu) (a i : ℕ) :
    youngRuleBlockCumulCount mu nu (σ * p) a i =
      youngRuleBlockCumulCount mu nu σ a i := by
  classical
  let source := (Finset.univ : Finset (Fin n)).filter fun e =>
    rowOfPos mu.sortedParts e.val < a ∧
      rowOfPos nu.sortedParts ((σ * p) e).val < i
  let target := (Finset.univ : Finset (Fin n)).filter fun e =>
    rowOfPos mu.sortedParts e.val < a ∧
      rowOfPos nu.sortedParts (σ e).val < i
  change source.card = target.card
  apply Finset.card_bij (fun e _ => p e)
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hp e]
      exact he.2.1
    · simpa only [Equiv.Perm.coe_mul, Function.comp_apply] using he.2.2
  · intro e₁ h₁ e₂ h₂ heq
    exact p.injective heq
  · intro e he
    refine ⟨p⁻¹ e, ?_, p.apply_symm_apply e⟩
    rw [Finset.mem_filter] at he ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hpInv := (RowSubgroup n mu).inv_mem hp
      rw [hpInv e]
      exact he.2.1
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      have hpe : p (p⁻¹ e) = e := p.apply_symm_apply e
      rw [hpe]
      exact he.2.2

/-- The canonical standardization realizes the intrinsic cumulative profile of
the semistandard tableau at every content-block and shape-row cutoff. -/
theorem youngRuleBlockCumulCount_standardization {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (a i : ℕ) :
    youngRuleBlockCumulCount mu nu (sytPerm n nu T.standardization) a i =
      T.cumulativeProfile a i := by
  classical
  let e : Cell n nu ≃ Fin n :=
    Equiv.ofBijective T.standardization.1 T.standardization.2.1
  let source := (Finset.univ : Finset (Fin n)).filter fun x =>
    rowOfPos mu.sortedParts x.val < a ∧
      rowOfPos nu.sortedParts (sytPerm n nu T.standardization x).val < i
  let target := (Finset.univ : Finset (Cell n nu)).filter fun c =>
    T.1 c.1.1 c.1.2 < a ∧ c.1.1 < i
  change source.card = target.card
  apply Finset.card_bij (fun x _ => e.symm x)
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    let c := e.symm x
    have hentry : e c = x := e.apply_symm_apply x
    have hentry' : T.standardization.1 c = x := by
      change e c = x
      exact hentry
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [← KostkaTableau.rowOfPos_standardization T c, hentry']
      exact hx.2.1
    · rw [← rowOfPos_canonical_symm c, ← sytPerm_apply_tableauEntry
        T.standardization c, hentry']
      exact hx.2.2
  · intro x₁ hx₁ x₂ hx₂ heq
    exact e.symm.injective heq
  · intro c hc
    refine ⟨e c, ?_, e.symm_apply_apply c⟩
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · change rowOfPos mu.sortedParts (T.standardization.1 c).val < a
      rw [KostkaTableau.rowOfPos_standardization T c]
      exact hc.2.1
    · change rowOfPos nu.sortedParts
        (sytPerm n nu T.standardization (T.standardization.1 c)).val < i
      rw [sytPerm_apply_tableauEntry T.standardization c,
        rowOfPos_canonical_symm c]
      exact hc.2.2

end

end Etingof
