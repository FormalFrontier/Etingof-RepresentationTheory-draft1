/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import EtingofRepresentationTheory.Chapter5.YoungRuleSemistandardCoordinates

/-!
# Linear independence endpoint for Young's rule

This file isolates the linear-algebra endpoint of the semistandard-tableau construction.
A family with nonzero diagonal coordinates and triangular off-diagonal support is linearly
independent.  Applied to the canonical row-averaged polytabloids, this turns any such
coordinate proof into the tableau basis required by Young's rule.

We also record the stabilizer separation behind the nonzero diagonal: a permutation that
simultaneously preserves the content blocks and acts columnwise relative to the canonical
standardization of a semistandard tableau must be the identity.
-/

namespace Etingof

noncomputable section

/-- A finite family with nonzero diagonal coordinates and upper-triangular coordinate
support is linearly independent.  The index order need only be a partial order: a maximal
element of the support of a putative relation isolates its diagonal coefficient. -/
theorem linearIndependent_of_upperTriangular_coordinates
    {R M ι : Type*} [Field R] [AddCommGroup M] [Module R M] [PartialOrder ι]
    (v : ι → M) (coord : ι → M →ₗ[R] R)
    (htri : ∀ i j, coord i (v j) ≠ 0 → i ≤ j)
    (hdiag : ∀ i, coord i (v i) ≠ 0) :
    LinearIndependent R v := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let support := s.filter fun j ↦ g j ≠ 0
  have hiSupport : i ∈ support := Finset.mem_filter.mpr ⟨hi, hgi⟩
  obtain ⟨m, hm⟩ := support.exists_maximal ⟨i, hiSupport⟩
  have hmS : m ∈ s := (Finset.mem_filter.mp hm.1).1
  have hmg : g m ≠ 0 := (Finset.mem_filter.mp hm.1).2
  have hcoord := congrArg (coord m) hsum
  simp only [map_sum, map_smul, map_zero] at hcoord
  have hcollapse :
      ∑ j ∈ s, g j • coord m (v j) = g m • coord m (v m) := by
    apply Finset.sum_eq_single m
    · intro j hjS hjm
      by_cases hgj : g j = 0
      · simp [hgj]
      · have hjSupport : j ∈ support := Finset.mem_filter.mpr ⟨hjS, hgj⟩
        have hnle : ¬m ≤ j := by
          intro hmj
          exact hjm (le_antisymm (hm.2 hjSupport hmj) hmj)
        have hz : coord m (v j) = 0 := not_ne_iff.mp fun hne ↦ hnle (htri m j hne)
        simp [hz]
    · intro hmNot
      exact (hmNot hmS).elim
  rw [hcollapse] at hcoord
  exact (smul_ne_zero hmg (hdiag m)) hcoord

/-- The distinguished top-tabloid coordinate of a row-invariant Specht vector. -/
noncomputable def youngRuleDistinguishedCoordinate {n : ℕ}
    (mu nu : Nat.Partition n) (T : KostkaTableau n nu mu) :
    YoungRuleRowInvariants n mu nu →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (R := ℂ) (M := ℂ)
    (sytToTabloid n nu T.standardization)).comp
      ((tabloidProjectionSpecht (n := n) (la := nu)).comp
        (YoungRuleRowInvariants n mu nu).subtype)

@[simp] theorem youngRuleDistinguishedCoordinate_apply {n : ℕ}
    (mu nu : Nat.Partition n) (T : KostkaTableau n nu mu)
    (v : YoungRuleRowInvariants n mu nu) :
    youngRuleDistinguishedCoordinate mu nu T v =
      tabloidProjectionSpecht v.1 (sytToTabloid n nu T.standardization) :=
  rfl

/-- The generic triangular-coordinate criterion specialized to the canonical averaged
polytabloids indexed by semistandard tableaux. -/
theorem youngRuleSemistandardVector_linearIndependent_of_upperTriangular
    {n : ℕ} (mu nu : Nat.Partition n)
    [PartialOrder (KostkaTableau n nu mu)]
    (htri : ∀ T U,
      youngRuleDistinguishedCoordinate mu nu T
          (youngRuleSemistandardVector n mu nu U) ≠ 0 → T ≤ U)
    (hdiag : ∀ T,
      youngRuleDistinguishedCoordinate mu nu T
          (youngRuleSemistandardVector n mu nu T) ≠ 0) :
    LinearIndependent ℂ (youngRuleSemistandardVector n mu nu) :=
  linearIndependent_of_upperTriangular_coordinates
    (youngRuleSemistandardVector n mu nu)
    (youngRuleDistinguishedCoordinate mu nu) htri hdiag

/-- Linear independence upgrades the already-proved spanning family of semistandard
vectors to the tableau-indexed basis required by Young's rule. -/
noncomputable def youngRuleTableauBasisOfLinearIndependent {n : ℕ}
    (mu nu : Nat.Partition n)
    (hli : LinearIndependent ℂ (youngRuleSemistandardVector n mu nu)) :
    YoungRuleTableauBasis n mu nu :=
  Module.Basis.mk hli (span_range_youngRuleSemistandardVector n mu nu).ge

/-- Once the canonical semistandard vectors are linearly independent, Young's-rule
multiplicity is the Kostka number. -/
theorem youngRuleMultiplicity_eq_kostkaNumber_of_semistandard_linearIndependent
    (n : ℕ) (mu nu : Nat.Partition n)
    (hli : LinearIndependent ℂ (youngRuleSemistandardVector n mu nu)) :
    YoungRuleMultiplicity n mu nu = KostkaNumber n nu mu :=
  youngRuleMultiplicity_eq_kostkaNumber_of_tableauBasis n mu nu
    (youngRuleTableauBasisOfLinearIndependent mu nu hli)

/-- A permutation preserving both the content blocks and the relative columns of the
canonical standardization of a semistandard tableau is the identity. -/
theorem KostkaTableau.eq_one_of_mem_rowSubgroup_of_mem_relColumnSubgroup
    {n : ℕ} {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu)
    (p : Equiv.Perm (Fin n)) (hpRow : p ∈ RowSubgroup n mu)
    (hpCol : p ∈ RelColumnSubgroup n nu T.standardization) :
    p = 1 := by
  let e := Equiv.ofBijective T.standardization.1 T.standardization.2.1
  apply Equiv.ext
  intro k
  let c : Cell n nu := e.symm k
  let d : Cell n nu := e.symm (p k)
  have hcLabel : T.standardization.1 c = k := e.apply_symm_apply k
  have hdLabel : T.standardization.1 d = p k := e.apply_symm_apply (p k)
  have hentry : T.1 d.1.1 d.1.2 = T.1 c.1.1 c.1.2 := by
    rw [← T.rowOfPos_standardization c, ← T.rowOfPos_standardization d,
      hcLabel, hdLabel]
    exact hpRow k
  have hq : sytPerm n nu T.standardization * p *
      (sytPerm n nu T.standardization)⁻¹ ∈ ColumnSubgroup n nu :=
    sytPerm_conj_mem_ColumnSubgroup T.standardization p hpCol
  have hposCol :
      colOfPos nu.sortedParts (sytPerm n nu T.standardization (p k)).val =
        colOfPos nu.sortedParts (sytPerm n nu T.standardization k).val := by
    simpa using hq (sytPerm n nu T.standardization k)
  have hcCell : c = canonicalFilling n nu
      (sytPerm n nu T.standardization k) := by
    change e.symm k = _
    simp only [e, sytPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hdCell : d = canonicalFilling n nu
      (sytPerm n nu T.standardization (p k)) := by
    change e.symm (p k) = _
    simp only [e, sytPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hcol : d.1.2 = c.1.2 := by
    rw [hdCell, hcCell]
    exact hposCol
  have hcMem : c.1 ∈ nu.toYoungDiagram := by
    change c.1 ∈ YoungDiagram.ofRowLens nu.sortedParts _
    rw [YoungDiagram.mem_ofRowLens]
    refine ⟨c.2.1, ?_⟩
    have hc := c.2.2
    rw [List.getD_eq_getElem _ _ c.2.1] at hc
    exact hc
  have hdMem : d.1 ∈ nu.toYoungDiagram := by
    change d.1 ∈ YoungDiagram.ofRowLens nu.sortedParts _
    rw [YoungDiagram.mem_ofRowLens]
    refine ⟨d.2.1, ?_⟩
    have hd := d.2.2
    rw [List.getD_eq_getElem _ _ d.2.1] at hd
    exact hd
  have hrow : d.1.1 = c.1.1 := by
    rcases lt_trichotomy d.1.1 c.1.1 with hlt | heq | hgt
    · have hstrict := T.1.col_strict hlt hcMem
      have heq : T.1 d.1.1 c.1.2 = T.1 c.1.1 c.1.2 := by
        simpa only [hcol] using hentry
      exact (Nat.ne_of_lt hstrict heq).elim
    · exact heq
    · have hstrict := T.1.col_strict hgt hdMem
      have heq : T.1 c.1.1 d.1.2 = T.1 d.1.1 d.1.2 := by
        calc
          T.1 c.1.1 d.1.2 = T.1 c.1.1 c.1.2 := congrArg _ hcol
          _ = T.1 d.1.1 d.1.2 := hentry.symm
      exact (Nat.ne_of_lt hstrict heq).elim
  have hcd : c = d := Subtype.ext (Prod.ext hrow.symm hcol.symm)
  change p k = k
  rw [← hdLabel, ← hcLabel, hcd]

/-- Subgroup form of
`KostkaTableau.eq_one_of_mem_rowSubgroup_of_mem_relColumnSubgroup`. -/
theorem KostkaTableau.rowSubgroup_inf_relColumnSubgroup_eq_bot
    {n : ℕ} {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) :
    RowSubgroup n mu ⊓ RelColumnSubgroup n nu T.standardization = ⊥ := by
  ext p
  constructor
  · intro hp
    rw [Subgroup.mem_inf] at hp
    rw [Subgroup.mem_bot]
    exact T.eq_one_of_mem_rowSubgroup_of_mem_relColumnSubgroup p hp.1 hp.2
  · intro hp
    rw [Subgroup.mem_bot] at hp
    subst p
    exact Subgroup.one_mem _

end

end Etingof
