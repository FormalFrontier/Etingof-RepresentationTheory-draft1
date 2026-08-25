/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import EtingofRepresentationTheory.Chapter5.YoungRuleAveragedIndependence

/-!
# Triangularity of the semistandard vectors in Young's rule

This file turns tabloid dominance into an intrinsic dominance relation on Kostka tableaux.
Only cutoffs between content blocks are used, so the relation is unchanged by the content
row subgroup occurring in the row average.
-/

namespace Etingof

noncomputable section

/-- A block cumulative count is an ordinary tabloid cumulative count when the block
boundary is nonzero. -/
private theorem youngRuleBlockCumulCount_eq_tabloidCumulCount {n : ℕ}
    (mu nu : Nat.Partition n) (sigma : Equiv.Perm (Fin n)) (a i m : ℕ)
    (hm : (mu.sortedParts.take a).sum = m + 1) (hmn : m < n) :
    youngRuleBlockCumulCount mu nu sigma a i =
      tabloidCumulCount nu sigma ⟨m, hmn⟩ i := by
  classical
  unfold youngRuleBlockCumulCount tabloidCumulCount
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val]
  have he : e.val < mu.sortedParts.sum := by
    rw [sortedParts_sum_eq n mu]
    exact e.isLt
  rw [rowOfPos_lt_iff mu.sortedParts e.val a he, hm]
  omega

/-- Tabloid dominance implies dominance at every content-block cutoff. -/
theorem youngRuleBlockCumulCount_le_of_tabloidDominates {n : ℕ}
    (mu nu : Nat.Partition n) {sigma tau : Equiv.Perm (Fin n)}
    (hdom : tabloidDominates nu sigma tau) (a i : ℕ) :
    youngRuleBlockCumulCount mu nu tau a i ≤
      youngRuleBlockCumulCount mu nu sigma a i := by
  classical
  let b := (mu.sortedParts.take a).sum
  have hb_le : b ≤ n := by
    rw [← sortedParts_sum_eq n mu]
    exact (List.take_sublist a mu.sortedParts).sum_le_sum (fun _ _ => Nat.zero_le _)
  cases hb : b with
  | zero =>
      unfold youngRuleBlockCumulCount
      have he : ∀ e : Fin n, ¬ rowOfPos mu.sortedParts e.val < a := by
        intro e hrow
        have hvalid : e.val < mu.sortedParts.sum := by
          rw [sortedParts_sum_eq n mu]
          exact e.isLt
        rw [rowOfPos_lt_iff mu.sortedParts e.val a hvalid] at hrow
        have hzero : (mu.sortedParts.take a).sum = 0 := by
          simpa only [b] using hb
        omega
      simp only [he, false_and, Finset.filter_false, Finset.card_empty, le_refl]
  | succ m =>
      have hm : (mu.sortedParts.take a).sum = m + 1 := by
        simpa only [b] using hb
      have hmn : m < n := by omega
      rw [youngRuleBlockCumulCount_eq_tabloidCumulCount mu nu tau a i m hm hmn,
        youngRuleBlockCumulCount_eq_tabloidCumulCount mu nu sigma a i m hm hmn]
      exact hdom ⟨m, hmn⟩ i

/-- Intrinsic dominance on Kostka tableaux, expressed by their content/shape cumulative
profiles. -/
def KostkaTableau.ProfileDominates {n : ℕ} {nu mu : Nat.Partition n}
    (T U : KostkaTableau n nu mu) : Prop :=
  ∀ a i : ℕ, U.cumulativeProfile a i ≤ T.cumulativeProfile a i

theorem KostkaTableau.profileDominates_refl {n : ℕ} {nu mu : Nat.Partition n}
    (T : KostkaTableau n nu mu) : T.ProfileDominates T :=
  fun _ _ => le_rfl

theorem KostkaTableau.profileDominates_trans {n : ℕ} {nu mu : Nat.Partition n}
    {T U V : KostkaTableau n nu mu} (hTU : T.ProfileDominates U)
    (hUV : U.ProfileDominates V) : T.ProfileDominates V :=
  fun a i => (hUV a i).trans (hTU a i)

/-- The tabloid support statement descends through a content-row permutation to intrinsic
profile dominance. -/
theorem KostkaTableau.profileDominates_of_tabloidDominates_mul_row {n : ℕ}
    {nu mu : Nat.Partition n} (T U : KostkaTableau n nu mu)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RowSubgroup n mu)
    (hdom : tabloidDominates nu (sytPerm n nu T.standardization)
      (sytPerm n nu U.standardization * p)) :
    T.ProfileDominates U := by
  intro a i
  rw [← youngRuleBlockCumulCount_standardization T,
    ← youngRuleBlockCumulCount_standardization U,
    ← youngRuleBlockCumulCount_mul_row mu nu
      (sytPerm n nu U.standardization) p hp]
  exact youngRuleBlockCumulCount_le_of_tabloidDominates mu nu hdom a i

/-- A `Cell` really is a cell of the partition Young diagram. -/
private theorem cell_mem_toYoungDiagram {n : ℕ} {nu : Nat.Partition n}
    (c : Cell n nu) : c.1 ∈ nu.toYoungDiagram := by
  change c.1 ∈ YoungDiagram.ofRowLens nu.sortedParts _
  rw [YoungDiagram.mem_ofRowLens]
  refine ⟨c.2.1, ?_⟩
  have hc := c.2.2
  rwa [List.getD_eq_getElem _ _ c.2.1] at hc

/-- The number of entries below `a` in one specified row. -/
private noncomputable def KostkaTableau.rowProfile {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (a r : ℕ) : ℕ :=
  ((Finset.univ : Finset (Cell n nu)).filter fun c =>
    T.1 c.1.1 c.1.2 < a ∧ c.1.1 = r).card

/-- Successive shape-row cutoffs differ by the profile of the newly added row. -/
private theorem KostkaTableau.cumulativeProfile_succ {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (a r : ℕ) :
    T.cumulativeProfile a (r + 1) =
      T.cumulativeProfile a r + T.rowProfile a r := by
  classical
  let below := (Finset.univ : Finset (Cell n nu)).filter fun c =>
    T.1 c.1.1 c.1.2 < a ∧ c.1.1 < r
  let atRow := (Finset.univ : Finset (Cell n nu)).filter fun c =>
    T.1 c.1.1 c.1.2 < a ∧ c.1.1 = r
  have hunion :
      ((Finset.univ : Finset (Cell n nu)).filter fun c =>
        T.1 c.1.1 c.1.2 < a ∧ c.1.1 < r + 1) = below ∪ atRow := by
    ext c
    simp only [below, atRow, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    omega
  have hdisj : Disjoint below atRow := by
    rw [Finset.disjoint_left]
    intro c hcBelow hcRow
    simp only [below, atRow, Finset.mem_filter, Finset.mem_univ, true_and] at hcBelow hcRow
    omega
  unfold KostkaTableau.cumulativeProfile KostkaTableau.rowProfile
  rw [hunion, Finset.card_union_of_disjoint hdisj]

/-- Equal cumulative profiles give equal counts in each individual row. -/
private theorem KostkaTableau.rowProfile_eq_of_cumulativeProfile_eq {n : ℕ}
    {nu mu : Nat.Partition n} {T U : KostkaTableau n nu mu}
    (h : ∀ a i : ℕ, T.cumulativeProfile a i = U.cumulativeProfile a i)
    (a r : ℕ) : T.rowProfile a r = U.rowProfile a r := by
  have hT := T.cumulativeProfile_succ a r
  have hU := U.cumulativeProfile_succ a r
  rw [h a (r + 1), h a r] at hT
  omega

/-- In a weakly increasing tableau row, equal cumulative profiles forbid a strictly
smaller entry at the same cell. -/
private theorem KostkaTableau.not_entry_lt_of_cumulativeProfile_eq {n : ℕ}
    {nu mu : Nat.Partition n} {T U : KostkaTableau n nu mu}
    (h : ∀ a i : ℕ, T.cumulativeProfile a i = U.cumulativeProfile a i)
    (c : Cell n nu) : ¬ T.1 c.1.1 c.1.2 < U.1 c.1.1 c.1.2 := by
    intro hlt
    let a := U.1 c.1.1 c.1.2
    let left : Finset (Cell n nu) := (Finset.univ.filter fun d =>
      d.1.1 = c.1.1 ∧ d.1.2 ≤ c.1.2)
    have hleft_card : left.card = c.1.2 + 1 := by
      rw [← Finset.card_range (c.1.2 + 1)]
      apply Finset.card_bij (fun d _ => d.1.2)
      · intro d hd
        rw [Finset.mem_range]
        simp only [left, Finset.mem_filter, Finset.mem_univ, true_and] at hd
        omega
      · intro d₁ hd₁ d₂ hd₂ heq
        apply Subtype.ext
        have h₁ := (Finset.mem_filter.mp hd₁).2.1
        have h₂ := (Finset.mem_filter.mp hd₂).2.1
        exact Prod.ext (h₁.trans h₂.symm) heq
      · intro k hk
        rw [Finset.mem_range] at hk
        let d : Cell n nu :=
          ⟨(c.1.1, k), c.2.1, lt_of_lt_of_le hk c.2.2⟩
        refine ⟨d, ?_, rfl⟩
        simp only [left, Finset.mem_filter, Finset.mem_univ, true_and, d]
        omega
    have hleft_subset : left ⊆ (Finset.univ.filter fun d : Cell n nu =>
        T.1 d.1.1 d.1.2 < a ∧ d.1.1 = c.1.1) := by
      intro d hd
      simp only [left, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
      refine ⟨?_, hd.1⟩
      have hweak : T.1 d.1.1 d.1.2 ≤ T.1 c.1.1 c.1.2 := by
        rw [hd.1]
        exact T.1.row_weak_of_le hd.2 (cell_mem_toYoungDiagram c)
      exact hweak.trans_lt hlt
    have hTlower : c.1.2 + 1 ≤ T.rowProfile a c.1.1 := by
      rw [← hleft_card]
      exact Finset.card_le_card hleft_subset
    have hUupper : U.rowProfile a c.1.1 ≤ c.1.2 := by
      let source := (Finset.univ : Finset (Cell n nu)).filter fun d =>
        U.1 d.1.1 d.1.2 < a ∧ d.1.1 = c.1.1
      change source.card ≤ c.1.2
      rw [← Finset.card_range c.1.2]
      apply Finset.card_le_card_of_injOn (fun d : Cell n nu => d.1.2)
      · intro d hd
        rw [Finset.mem_coe, Finset.mem_range]
        simp only [source, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and] at hd
        by_contra hnot
        have hweak : U.1 c.1.1 c.1.2 ≤ U.1 d.1.1 d.1.2 := by
          calc
            U.1 c.1.1 c.1.2 = U.1 d.1.1 c.1.2 := by rw [hd.2]
            _ ≤ U.1 d.1.1 d.1.2 :=
              U.1.row_weak_of_le (Nat.le_of_not_gt hnot) (cell_mem_toYoungDiagram d)
        exact (not_lt_of_ge hweak) hd.1
      · intro d₁ hd₁ d₂ hd₂ heq
        apply Subtype.ext
        have hrow₁ := (Finset.mem_filter.mp hd₁).2.2
        have hrow₂ := (Finset.mem_filter.mp hd₂).2.2
        exact Prod.ext (hrow₁.trans hrow₂.symm) heq
    have hroweq := KostkaTableau.rowProfile_eq_of_cumulativeProfile_eq h a c.1.1
    omega

/-- In a weakly increasing tableau row, its entry-count profile determines every entry. -/
private theorem KostkaTableau.eq_of_cumulativeProfile_eq {n : ℕ}
    {nu mu : Nat.Partition n} {T U : KostkaTableau n nu mu}
    (h : ∀ a i : ℕ, T.cumulativeProfile a i = U.cumulativeProfile a i) : T = U := by
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro r j
  by_cases hc : (r, j) ∈ nu.toYoungDiagram
  · have hc' := hc
    change (r, j) ∈ YoungDiagram.ofRowLens nu.sortedParts _ at hc'
    rw [YoungDiagram.mem_ofRowLens] at hc'
    have hcol := hc'.2
    have hcol' : j < nu.sortedParts.getD r 0 := by
      rw [List.getD_eq_getElem _ _ hc'.1]
      exact hcol
    let c : Cell n nu := ⟨(r, j), hc'.1, hcol'⟩
    change T.1 c.1.1 c.1.2 = U.1 c.1.1 c.1.2
    exact Nat.le_antisymm
      (Nat.le_of_not_gt (KostkaTableau.not_entry_lt_of_cumulativeProfile_eq
        (fun a i => (h a i).symm) c))
      (Nat.le_of_not_gt (KostkaTableau.not_entry_lt_of_cumulativeProfile_eq h c))
  · rw [T.1.zeros hc, U.1.zeros hc]

/-- Intrinsic profile dominance is antisymmetric. -/
theorem KostkaTableau.profileDominates_antisymm {n : ℕ} {nu mu : Nat.Partition n}
    {T U : KostkaTableau n nu mu} (hTU : T.ProfileDominates U)
    (hUT : U.ProfileDominates T) : T = U := by
  apply KostkaTableau.eq_of_cumulativeProfile_eq
  intro a i
  exact Nat.le_antisymm (hUT a i) (hTU a i)

/-- The partial order used for semistandard triangularity is reverse intrinsic profile
dominance. Thus a vector supported at the distinguished coordinate of `T` can only come
from an index weakly above `T`. -/
instance KostkaTableau.profilePartialOrder {n : ℕ} {nu mu : Nat.Partition n} :
    PartialOrder (KostkaTableau n nu mu) where
  le T U := U.ProfileDominates T
  le_refl T := T.profileDominates_refl
  le_trans T U V hTU hUV :=
    KostkaTableau.profileDominates_trans hUV hTU
  le_antisymm T U hTU hUT := profileDominates_antisymm hUT hTU

/-- The distinguished-coordinate matrix of the canonical semistandard vectors is upper
triangular for the cumulative-profile partial order. -/
theorem youngRuleSemistandardVector_upperTriangular {n : ℕ}
    (mu nu : Nat.Partition n) (T U : KostkaTableau n nu mu)
    (hne : youngRuleDistinguishedCoordinate mu nu T
      (youngRuleSemistandardVector n mu nu U) ≠ 0) :
    T ≤ U := by
  change tabloidProjectionSpecht
    ((youngRuleRowAverageRange n mu nu
      (spechtPolytabloid U.standardization)).1)
        (sytToTabloid n nu T.standardization) ≠ 0 at hne
  obtain ⟨p, hp⟩ :=
    youngRuleRowAverageRange_standardization_coeff_dominance U T hne
  exact KostkaTableau.profileDominates_of_tabloidDominates_mul_row U T p.val p.prop hp

/-- Once the diagonal coordinate is known to be nonzero, cumulative-profile
triangularity gives linear independence of the canonical semistandard vectors. -/
theorem youngRuleSemistandardVector_linearIndependent_of_diagonal {n : ℕ}
    (mu nu : Nat.Partition n)
    (hdiag : ∀ T,
      youngRuleDistinguishedCoordinate mu nu T
        (youngRuleSemistandardVector n mu nu T) ≠ 0) :
    LinearIndependent ℂ (youngRuleSemistandardVector n mu nu) :=
  youngRuleSemistandardVector_linearIndependent_of_upperTriangular mu nu
    (youngRuleSemistandardVector_upperTriangular mu nu) hdiag

end

end Etingof
