/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import EtingofRepresentationTheory.Chapter5.YoungRuleSemistandardTriangularity

/-!
# The diagonal coefficient in Young's rule

The distinguished tabloid coordinate of every canonical semistandard vector is nonzero.
More precisely, after expanding the row average, each summand is either zero or one: if a
column-antisymmetrizer term contributes, least-moved-row separation forces its column
permutation to be the identity.  The identity content-row permutation contributes one, so
the whole coefficient is a positive stabilizer count divided by the content-row-subgroup
order.

Together with semistandard triangularity and spanning, this gives the tableau basis and the
unconditional Young-rule/Kostka multiplicity formula.
-/

namespace Etingof

noncomputable section

private theorem positionEntry_eq_content {n : ℕ} {nu mu : Nat.Partition n}
    (T : KostkaTableau n nu mu) (x : Fin n) :
    T.positionEntry x = rowOfPos mu.sortedParts
      ((sytPerm n nu T.standardization)⁻¹ x).val := by
  let c := canonicalFilling n nu x
  change T.1 c.1.1 c.1.2 = _
  rw [← T.rowOfPos_standardization c]
  congr 2

/-- A content-row translate of the distinguished tabloid has coefficient zero or one in
the canonical polytabloid.  The possible extra shape-row stabilizer is retained: it accounts
for the cases where the coefficient is one, rather than being incorrectly discarded. -/
private theorem polytabloidTab_standardization_rightMul_coeff_zero_or_one {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu)
    (p : ↑(RowSubgroup n mu)) :
    polytabloidTab T.standardization
        (tabloidRightMul (la := nu) p.val
          (sytToTabloid n nu T.standardization)) = 0 ∨
      polytabloidTab T.standardization
        (tabloidRightMul (la := nu) p.val
          (sytToTabloid n nu T.standardization)) = 1 := by
  classical
  let σ := sytPerm n nu T.standardization
  let target := tabloidRightMul (la := nu) p.val
    (sytToTabloid n nu T.standardization)
  by_cases hex : ∃ q : ↑(ColumnSubgroup n nu),
      toTabloid n nu (q.val⁻¹ * σ) = target
  · obtain ⟨q, hq⟩ := hex
    have htarget : target = sytToTabloid n nu T.standardization := by
      have htab : toTabloid n nu (q.val⁻¹ * σ) =
          toTabloid n nu (σ * p.val) := by
        simpa only [target, sytToTabloid, tabloidRightMul_toTabloid] using hq
      have hr : q.val⁻¹ * σ * (σ * p.val)⁻¹ ∈ RowSubgroup n nu :=
        (toTabloid_eq_iff _ _).mp htab
      let r := q.val⁻¹ * σ * (σ * p.val)⁻¹
      have hpres : ∀ x, T.positionEntry (q.val (r x)) = T.positionEntry x := by
        intro x
        rw [positionEntry_eq_content T, positionEntry_eq_content T]
        have hpInv := (RowSubgroup n mu).inv_mem p.prop
        have hpContent := hpInv (σ⁻¹ x)
        have hperm : σ⁻¹ * q.val * r = p.val⁻¹ * σ⁻¹ := by
          simp only [r]
          group
        have happ := congrArg (fun g : Equiv.Perm (Fin n) ↦ g x) hperm
        simp only [Equiv.Perm.coe_mul, Function.comp_apply] at happ
        rw [happ]
        exact hpContent
      have hqOne : q.val = 1 :=
        T.column_eq_one_of_col_mul_row_preserves_positionEntry
          q.val r q.prop hr hpres
      rw [hqOne] at hq
      simpa only [σ, sytToTabloid, inv_one, one_mul] using hq.symm
    right
    change polytabloidTab T.standardization target = 1
    rw [htarget, polytabloidTab_coeff_self]
  · left
    change polytabloidTab T.standardization target = 0
    simp only [polytabloidTab]
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro q hqmem
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    have hne : toTabloid n nu (q.val⁻¹ * σ) ≠ target := by
      intro heq
      exact hex ⟨q, heq⟩
    rw [if_neg hne, mul_zero]

/-- The distinguished coordinate of every canonical semistandard vector is nonzero.  Its
unnormalized value is the cardinality of the nonempty set of content-row permutations that
stabilize the distinguished shape tabloid. -/
theorem youngRuleSemistandardVector_diagonal_ne_zero {n : ℕ}
    (mu nu : Nat.Partition n) (T : KostkaTableau n nu mu) :
    youngRuleDistinguishedCoordinate mu nu T
      (youngRuleSemistandardVector n mu nu T) ≠ 0 := by
  classical
  letI := Fintype.ofFinite (↑(RowSubgroup n mu))
  rw [youngRuleDistinguishedCoordinate_apply]
  change tabloidProjectionSpecht
      ((youngRuleRowAverageRange n mu nu
        (spechtPolytabloid T.standardization)).1)
          (sytToTabloid n nu T.standardization) ≠ 0
  rw [tabloidProjectionSpecht_youngRuleRowAverageRange_standardization_apply]
  let coeff : ↑(RowSubgroup n mu) → ℂ := fun p ↦
    polytabloidTab T.standardization
      (tabloidRightMul (la := nu) p.val
        (sytToTabloid n nu T.standardization))
  let stabilizer : Finset (↑(RowSubgroup n mu)) :=
    Finset.univ.filter fun p ↦ coeff p = 1
  have hcoeff : ∀ p, coeff p = if coeff p = 1 then 1 else 0 := by
    intro p
    rcases polytabloidTab_standardization_rightMul_coeff_zero_or_one T p with hp | hp
    · change coeff p = 0 at hp
      rw [hp]
      norm_num
    · change coeff p = 1 at hp
      rw [hp]
      norm_num
  have hone : coeff ⟨1, (RowSubgroup n mu).one_mem⟩ = 1 := by
    have honeAction : tabloidRightMul (la := nu) (1 : Equiv.Perm (Fin n))
        (sytToTabloid n nu T.standardization) =
          sytToTabloid n nu T.standardization := by
      change toTabloid n nu (sytPerm n nu T.standardization * 1) = _
      rw [mul_one]
      rfl
    simp only [coeff]
    rw [honeAction, polytabloidTab_coeff_self]
  have hstabilizer : stabilizer.Nonempty := by
    refine ⟨⟨1, (RowSubgroup n mu).one_mem⟩, ?_⟩
    simp only [stabilizer, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hone
  have hsum : (∑ p : ↑(RowSubgroup n mu), coeff p) =
      (stabilizer.card : ℂ) := by
    calc
      (∑ p : ↑(RowSubgroup n mu), coeff p) =
          ∑ p : ↑(RowSubgroup n mu), if coeff p = 1 then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hcoeff p
      _ = (stabilizer.card : ℂ) := by simp [stabilizer]
  rw [show (∑ p : ↑(RowSubgroup n mu), polytabloidTab T.standardization
      (tabloidRightMul (la := nu) p.val
        (sytToTabloid n nu T.standardization))) =
          (stabilizer.card : ℂ) from hsum]
  apply mul_ne_zero
  · exact inv_ne_zero (Nat.cast_ne_zero.mpr
      (Nat.card_pos (α := ↑(RowSubgroup n mu))).ne')
  · exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hstabilizer)

/-- The canonical semistandard vectors are linearly independent. -/
theorem youngRuleSemistandardVector_linearIndependent {n : ℕ}
    (mu nu : Nat.Partition n) :
    LinearIndependent ℂ (youngRuleSemistandardVector n mu nu) :=
  youngRuleSemistandardVector_linearIndependent_of_diagonal mu nu
    (youngRuleSemistandardVector_diagonal_ne_zero mu nu)

/-- The canonical semistandard vectors form the tableau-indexed basis of row invariants. -/
noncomputable def youngRuleSemistandardBasis {n : ℕ}
    (mu nu : Nat.Partition n) : YoungRuleTableauBasis n mu nu :=
  youngRuleTableauBasisOfLinearIndependent mu nu
    (youngRuleSemistandardVector_linearIndependent mu nu)

/-- **Young's rule.** The multiplicity of the Specht module of shape `nu` in the
permutation module of content `mu` is the Kostka number. -/
theorem youngRuleMultiplicity_eq_kostkaNumber (n : ℕ)
    (mu nu : Nat.Partition n) :
    YoungRuleMultiplicity n mu nu = KostkaNumber n nu mu :=
  youngRuleMultiplicity_eq_kostkaNumber_of_tableauBasis n mu nu
    (youngRuleSemistandardBasis mu nu)

end

end Etingof
