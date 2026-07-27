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

/-! ### Row/column factor separation -/

/-- Read a Kostka tableau on the canonical position set of its shape. -/
noncomputable def KostkaTableau.positionEntry {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (x : Fin n) : ℕ :=
  T.1 ((canonicalFilling n nu x).1.1) ((canonicalFilling n nu x).1.2)

/-- Reading a standardized position recovers the content block of its label. -/
@[simp] theorem KostkaTableau.positionEntry_sytPerm_standardization {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (x : Fin n) :
    T.positionEntry (sytPerm n nu T.standardization x) =
      rowOfPos mu.sortedParts x.val := by
  let e : Cell n nu ≃ Fin n :=
    Equiv.ofBijective T.standardization.1 T.standardization.2.1
  let c : Cell n nu := e.symm x
  have hcx : T.standardization.1 c = x := e.apply_symm_apply x
  rw [← hcx, sytPerm_apply_tableauEntry T.standardization c,
    KostkaTableau.positionEntry]
  have hcanon := (canonicalFilling n nu).apply_symm_apply c
  rw [hcanon]
  exact (T.rowOfPos_standardization c).symm

private theorem canonicalCell_mem_partitionDiagram {n : ℕ}
    {nu : Nat.Partition n} (x : Fin n) :
    (canonicalFilling n nu x).1 ∈ nu.toYoungDiagram := by
  change (canonicalFilling n nu x).1 ∈
    YoungDiagram.ofRowLens nu.sortedParts _
  rw [YoungDiagram.mem_ofRowLens]
  refine ⟨(canonicalFilling n nu x).2.1, ?_⟩
  have hx := (canonicalFilling n nu x).2.2
  rw [List.getD_eq_getElem _ _ (canonicalFilling n nu x).2.1] at hx
  exact hx

/-- **Least-moved-row separation.** Let `q` permute cells within columns and
`r` permute cells within rows.  If the composite `q ∘ r` preserves every entry
of a semistandard tableau, then `q` is the identity.

Indeed, in the first row moved by `q`, no cell can move upward (all earlier
rows are fixed and `q` is injective).  Column strictness makes every moved cell
strictly increase its entry, while fixed cells keep it.  The row permutation
`r` implies equality of the corresponding row sums, a contradiction. -/
theorem KostkaTableau.column_eq_one_of_col_mul_row_preserves_positionEntry
    {n : ℕ} {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu)
    (q r : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n nu)
    (hr : r ∈ RowSubgroup n nu)
    (hpres : ∀ x : Fin n, T.positionEntry (q (r x)) = T.positionEntry x) :
    q = 1 := by
  classical
  by_contra hqOne
  let moved := (Finset.univ : Finset (Fin n)).filter (fun x => q x ≠ x)
  have hmoved : moved.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hqOne
    apply Equiv.ext
    intro x
    simp only [Equiv.Perm.one_apply]
    by_contra hx
    have hxMem : x ∈ moved :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    have hxEmpty : x ∈ (∅ : Finset (Fin n)) := hempty ▸ hxMem
    simp at hxEmpty
  let movedRows := moved.image (fun x => rowOfPos nu.sortedParts x.val)
  have hmovedRows : movedRows.Nonempty := hmoved.image _
  let a := movedRows.min' hmovedRows
  have haMem : a ∈ movedRows := Finset.min'_mem movedRows hmovedRows
  obtain ⟨x, hxMoved, hxRow⟩ := Finset.mem_image.mp haMem
  have hxNe : q x ≠ x := (Finset.mem_filter.mp hxMoved).2
  have hfixedEarlier : ∀ y : Fin n,
      rowOfPos nu.sortedParts y.val < a → q y = y := by
    intro y hy
    by_contra hyMoved
    have hyMem : y ∈ moved :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyMoved⟩
    have hyRowMem : rowOfPos nu.sortedParts y.val ∈ movedRows :=
      Finset.mem_image.mpr ⟨y, hyMem, rfl⟩
    have hmin := Finset.min'_le movedRows _ hyRowMem
    omega
  have hqRowGe : ∀ y : Fin n, rowOfPos nu.sortedParts y.val = a →
      a ≤ rowOfPos nu.sortedParts (q y).val := by
    intro y hyRow
    by_contra hnot
    have hlt : rowOfPos nu.sortedParts (q y).val < a := Nat.lt_of_not_ge hnot
    have hfix := hfixedEarlier (q y) hlt
    have : q y = y := q.injective hfix
    rw [this] at hlt
    omega
  have hentryLe : ∀ y ∈ (Finset.univ : Finset (Fin n)).filter
      (fun z => rowOfPos nu.sortedParts z.val = a),
      T.positionEntry y ≤ T.positionEntry (q y) := by
    intro y hy
    have hyRow := (Finset.mem_filter.mp hy).2
    by_cases hyFix : q y = y
    · rw [hyFix]
    · apply Nat.le_of_lt
      have hrowLt : rowOfPos nu.sortedParts y.val <
          rowOfPos nu.sortedParts (q y).val := by
        have hge := hqRowGe y hyRow
        have hne : rowOfPos nu.sortedParts (q y).val ≠ a := by
          intro heq
          have hcol := hq y
          have hsum : nu.sortedParts.sum = n := by
            have hsort : (nu.sortedParts : Multiset ℕ) = nu.parts :=
              nu.parts.sort_eq (· ≥ ·)
            have : nu.sortedParts.sum = nu.parts.sum := by
              rw [← Multiset.sum_coe, hsort]
            rw [this, nu.parts_sum]
          have hval := rowOfPos_colOfPos_injective nu.sortedParts
            (q y).val y.val (by rw [hsum]; exact (q y).isLt)
            (by rw [hsum]; exact y.isLt) (heq.trans hyRow.symm) hcol
          exact hyFix (Fin.ext hval)
        omega
      have hcolCell : (canonicalFilling n nu y).1.2 =
          (canonicalFilling n nu (q y)).1.2 := by
        simpa only [canonicalFilling, canonicalFillingFun,
          Equiv.ofBijective_apply] using (hq y).symm
      have hrowCell : (canonicalFilling n nu y).1.1 <
          (canonicalFilling n nu (q y)).1.1 := by
        simpa only [canonicalFilling, canonicalFillingFun,
          Equiv.ofBijective_apply] using hrowLt
      change T.1 (canonicalFilling n nu y).1.1
          (canonicalFilling n nu y).1.2 <
        T.1 (canonicalFilling n nu (q y)).1.1
          (canonicalFilling n nu (q y)).1.2
      rw [hcolCell]
      exact T.1.col_strict hrowCell
        (canonicalCell_mem_partitionDiagram (nu := nu) (q y))
  have hxStrict : T.positionEntry x < T.positionEntry (q x) := by
    have hxInRow : x ∈ (Finset.univ : Finset (Fin n)).filter
        (fun z => rowOfPos nu.sortedParts z.val = a) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hxRow⟩
    have hxLe := hentryLe x hxInRow
    have hxRowGe := hqRowGe x hxRow
    have hxRowNe : rowOfPos nu.sortedParts (q x).val ≠ a := by
      intro heq
      have hsum : nu.sortedParts.sum = n := by
        have hsort : (nu.sortedParts : Multiset ℕ) = nu.parts :=
          nu.parts.sort_eq (· ≥ ·)
        have : nu.sortedParts.sum = nu.parts.sum := by
          rw [← Multiset.sum_coe, hsort]
        rw [this, nu.parts_sum]
      have hval := rowOfPos_colOfPos_injective nu.sortedParts
        (q x).val x.val (by rw [hsum]; exact (q x).isLt)
        (by rw [hsum]; exact x.isLt) (heq.trans hxRow.symm) (hq x)
      exact hxNe (Fin.ext hval)
    have hrowLt : rowOfPos nu.sortedParts x.val <
        rowOfPos nu.sortedParts (q x).val := by omega
    have hcolCell : (canonicalFilling n nu x).1.2 =
        (canonicalFilling n nu (q x)).1.2 := by
      simpa only [canonicalFilling, canonicalFillingFun,
        Equiv.ofBijective_apply] using (hq x).symm
    have hrowCell : (canonicalFilling n nu x).1.1 <
        (canonicalFilling n nu (q x)).1.1 := by
      simpa only [canonicalFilling, canonicalFillingFun,
        Equiv.ofBijective_apply] using hrowLt
    change T.1 (canonicalFilling n nu x).1.1
        (canonicalFilling n nu x).1.2 <
      T.1 (canonicalFilling n nu (q x)).1.1
        (canonicalFilling n nu (q x)).1.2
    rw [hcolCell]
    exact T.1.col_strict hrowCell
      (canonicalCell_mem_partitionDiagram (nu := nu) (q x))
  let rowSet := (Finset.univ : Finset (Fin n)).filter
    (fun z => rowOfPos nu.sortedParts z.val = a)
  have hsumReindex :
      ∑ y ∈ rowSet, T.positionEntry (q (r y)) =
        ∑ y ∈ rowSet, T.positionEntry (q y) := by
    apply Finset.sum_equiv r
    · intro y
      simp only [rowSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hy => (hr y).trans hy, fun hy => (hr y).symm.trans hy⟩
    · intro y hy
      rfl
  have hsumEq : (∑ y ∈ rowSet, T.positionEntry (q y)) =
      ∑ y ∈ rowSet, T.positionEntry y := by
    rw [← hsumReindex]
    apply Finset.sum_congr rfl
    intro y hy
    exact hpres y
  have hxInRow : x ∈ rowSet := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hxRow⟩
  have hsumLt : (∑ y ∈ rowSet, T.positionEntry y) <
      ∑ y ∈ rowSet, T.positionEntry (q y) :=
    Finset.sum_lt_sum
      (fun y hy => hentryLe y hy)
      ⟨x, hxInRow, hxStrict⟩
  omega

/-- If a column term in the standard polytabloid represents the same tabloid as
a translate by the content row subgroup, then that column term is the identity.
This is the quotient-level form of least-moved-row separation used by the
diagonal-coordinate calculation. -/
theorem KostkaTableau.column_eq_one_of_tabloid_inv_mul_standardization_eq_mul_row
    {n : ℕ} {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu)
    (q p : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n nu)
    (hp : p ∈ RowSubgroup n mu)
    (htab : toTabloid n nu (q⁻¹ * sytPerm n nu T.standardization) =
      toTabloid n nu (sytPerm n nu T.standardization * p)) :
    q = 1 := by
  rw [toTabloid_eq_iff] at htab
  let σ := sytPerm n nu T.standardization
  let r := q⁻¹ * σ * p⁻¹ * σ⁻¹
  have hr : r ∈ RowSubgroup n nu := by
    simpa only [r, σ, mul_inv_rev, inv_inv, mul_assoc] using htab
  apply T.column_eq_one_of_col_mul_row_preserves_positionEntry q r hq hr
  intro x
  have hqr : q * r = σ * p⁻¹ * σ⁻¹ := by
    simp only [r]
    group
  have hpInv := (RowSubgroup n mu).inv_mem hp
  calc
    T.positionEntry (q (r x)) =
        T.positionEntry (σ (p⁻¹ (σ⁻¹ x))) := by
      rw [← Equiv.Perm.mul_apply, hqr]
      rfl
    _ = rowOfPos mu.sortedParts (p⁻¹ (σ⁻¹ x)).val := by
      exact T.positionEntry_sytPerm_standardization (p⁻¹ (σ⁻¹ x))
    _ = rowOfPos mu.sortedParts (σ⁻¹ x).val := hpInv (σ⁻¹ x)
    _ = T.positionEntry (σ (σ⁻¹ x)) := by
      exact (T.positionEntry_sytPerm_standardization (σ⁻¹ x)).symm
    _ = T.positionEntry x := by simp

end

end Etingof
