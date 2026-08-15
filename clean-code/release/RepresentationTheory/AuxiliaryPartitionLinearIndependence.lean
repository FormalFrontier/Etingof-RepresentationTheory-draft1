/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryPartitionPermutationAverages














namespace RepresentationTheory.AuxiliaryPartitionLinearIndependence

noncomputable section




/-- A family is linearly independent when its coordinate evaluations are triangular for a partial order and every diagonal evaluation is nonzero. -/
theorem linearIndependent_of_coord_ne_zero_imp_le
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


/-- An auxiliary complex-linear coordinate functional associated with two partitions and an indexing object. -/
noncomputable def auxiliaryCoordinate {n : ℕ}
    (mu nu : Nat.Partition n) (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) :
    RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliarySubmodule n mu nu →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (R := ℂ) (M := ℂ)
    (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject)).comp
      ((RepresentationTheory.Auxiliary.MembershipSubtypes.membershipSubtypeLinearMap (n := n) (la := nu)).comp
        (RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliarySubmodule n mu nu).subtype)

/-- The auxiliary coordinate functional is evaluated by the displayed pair of auxiliary maps. -/
@[simp] theorem auxiliaryCoordinate_apply {n : ℕ}
    (mu nu : Nat.Partition n) (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu)
    (v : RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliarySubmodule n mu nu) :
    auxiliaryCoordinate mu nu T v =
      RepresentationTheory.Auxiliary.MembershipSubtypes.membershipSubtypeLinearMap v.1 (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject) :=
  rfl



/-- Triangular auxiliary coordinates with nonzero diagonal values make the displayed family linearly independent. -/
theorem auxiliary_linearIndependent
    {n : ℕ} (mu nu : Nat.Partition n)
    [PartialOrder (RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu)]
    (htri : ∀ T U,
      auxiliaryCoordinate mu nu T
          (RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliaryFamilyMap n mu nu U) ≠ 0 → T ≤ U)
    (hdiag : ∀ T,
      auxiliaryCoordinate mu nu T
          (RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliaryFamilyMap n mu nu T) ≠ 0) :
    LinearIndependent ℂ (RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliaryFamilyMap n mu nu) :=
  linearIndependent_of_coord_ne_zero_imp_le
    (RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliaryFamilyMap n mu nu)
    (auxiliaryCoordinate mu nu) htri hdiag



/-- Builds the displayed auxiliary structure from linear independence of the associated family. -/
noncomputable def auxiliaryConstructionOfLinearIndependent {n : ℕ}
    (mu nu : Nat.Partition n)
    (hli : LinearIndependent ℂ (RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliaryFamilyMap n mu nu)) :
    RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryStructure n mu nu :=
  Module.Basis.mk hli (RepresentationTheory.AuxiliaryPartitionIndexMaps.span_range_auxiliaryFamilyMap_eq_top n mu nu).ge



/-- Linear independence of the auxiliary family implies equality of the two displayed quantities. -/
theorem auxiliary_eq_of_linearIndependent
    (n : ℕ) (mu nu : Nat.Partition n)
    (hli : LinearIndependent ℂ (RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliaryFamilyMap n mu nu)) :
    RepresentationTheory.AuxiliaryPartitionDecomposition.auxiliaryNatValue n mu nu = RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryPartitionPairNat n nu mu :=
  RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliary_nat_value_eq_of_structure n mu nu
    (auxiliaryConstructionOfLinearIndependent mu nu hli)



/-- A permutation belonging to both displayed auxiliary subgroups is the identity. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliary_perm_eq_one_of_mem_intersection
    {n : ℕ} {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu)
    (p : Equiv.Perm (Fin n)) (hpRow : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)
    (hpCol : p ∈ RepresentationTheory.Permutation.PartitionIndexedAuxiliary.associatedSubgroup n nu T.toAuxiliaryObject) :
    p = 1 := by
  let e := Equiv.ofBijective T.toAuxiliaryObject.1 T.toAuxiliaryObject.2.1
  apply Equiv.ext
  intro k
  let c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu := e.symm k
  let d : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu := e.symm (p k)
  have hcLabel : T.toAuxiliaryObject.1 c = k := e.apply_symm_apply k
  have hdLabel : T.toAuxiliaryObject.1 d = p k := e.apply_symm_apply (p k)
  have hentry : T.1 d.1.1 d.1.2 = T.1 c.1.1 c.1.2 := by
    rw [← T.entry_eq_auxiliary_nat_value c, ← T.entry_eq_auxiliary_nat_value d,
      hcLabel, hdLabel]
    exact hpRow k
  have hq : RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject * p *
      (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject)⁻¹ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n nu :=
    RepresentationTheory.Permutation.PartitionIndexedAuxiliary.mem_auxiliarySet_of_mem_associatedSubgroup T.toAuxiliaryObject p hpCol
  have hposCol :
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject (p k)).val =
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject k).val := by
    simpa using hq (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject k)
  have hcCell : c = RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu
      (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject k) := by
    change e.symm k = _
    simp only [e, RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hdCell : d = RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu
      (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject (p k)) := by
    change e.symm (p k) = _
    simp only [e, RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hcol : d.1.2 = c.1.2 := by
    rw [hdCell, hcCell]
    exact hposCol
  have hcMem : c.1 ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu) := by
    change c.1 ∈ YoungDiagram.ofRowLens (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) _
    rw [YoungDiagram.mem_ofRowLens]
    refine ⟨c.2.1, ?_⟩
    have hc := c.2.2
    rw [List.getD_eq_getElem _ _ c.2.1] at hc
    exact hc
  have hdMem : d.1 ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu) := by
    change d.1 ∈ YoungDiagram.ofRowLens (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) _
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



/-- The infimum of the two displayed auxiliary subgroups is trivial. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliary_inf_eq_bot
    {n : ℕ} {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu ⊓ RepresentationTheory.Permutation.PartitionIndexedAuxiliary.associatedSubgroup n nu T.toAuxiliaryObject = ⊥ := by
  ext p
  constructor
  · intro hp
    rw [Subgroup.mem_inf] at hp
    rw [Subgroup.mem_bot]
    exact T.auxiliary_perm_eq_one_of_mem_intersection p hp.1 hp.2
  · intro hp
    rw [Subgroup.mem_bot] at hp
    subst p
    exact Subgroup.one_mem _




/-- Associates an auxiliary natural-number position value to each finite index. -/
noncomputable def _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliaryPositionEntry {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (x : Fin n) : ℕ :=
  T.1 ((RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x).1.1) ((RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x).1.2)


/-- After the displayed standardizing permutation, the auxiliary position value agrees with the corresponding sorted part. -/
@[simp] theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliaryPositionEntry_standardization {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (x : Fin n) :
    T.auxiliaryPositionEntry (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject x) =
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) x.val := by
  let e : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu ≃ Fin n :=
    Equiv.ofBijective T.toAuxiliaryObject.1 T.toAuxiliaryObject.2.1
  let c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu := e.symm x
  have hcx : T.toAuxiliaryObject.1 c = x := e.apply_symm_apply x
  rw [← hcx, RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliary_map_apply_eq_equiv_symm T.toAuxiliaryObject c,
    RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliaryPositionEntry]
  have hcanon := (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).apply_symm_apply c
  rw [hcanon]
  exact (T.entry_eq_auxiliary_nat_value c).symm

private theorem canonicalCell_mem_partitionDiagram {n : ℕ}
    {nu : Nat.Partition n} (x : Fin n) :
    (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x).1 ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu) := by
  change (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x).1 ∈
    YoungDiagram.ofRowLens (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) _
  rw [YoungDiagram.mem_ofRowLens]
  refine ⟨(RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x).2.1, ?_⟩
  have hx := (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x).2.2
  rw [List.getD_eq_getElem _ _ (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x).2.1] at hx
  exact hx









/-- Under the displayed subgroup conditions, a permutation preserving every auxiliary position value is the identity. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliary_left_perm_eq_one
    {n : ℕ} {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu)
    (q r : Equiv.Perm (Fin n)) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n nu)
    (hr : r ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n nu)
    (hpres : ∀ x : Fin n, T.auxiliaryPositionEntry (q (r x)) = T.auxiliaryPositionEntry x) :
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
  let movedRows := moved.image (fun x => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) x.val)
  have hmovedRows : movedRows.Nonempty := hmoved.image _
  let a := movedRows.min' hmovedRows
  have haMem : a ∈ movedRows := Finset.min'_mem movedRows hmovedRows
  obtain ⟨x, hxMoved, hxRow⟩ := Finset.mem_image.mp haMem
  have hxNe : q x ≠ x := (Finset.mem_filter.mp hxMoved).2
  have hfixedEarlier : ∀ y : Fin n,
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) y.val < a → q y = y := by
    intro y hy
    by_contra hyMoved
    have hyMem : y ∈ moved :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyMoved⟩
    have hyRowMem : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) y.val ∈ movedRows :=
      Finset.mem_image.mpr ⟨y, hyMem, rfl⟩
    have hmin := Finset.min'_le movedRows _ hyRowMem
    omega
  have hqRowGe : ∀ y : Fin n, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) y.val = a →
      a ≤ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) (q y).val := by
    intro y hyRow
    by_contra hnot
    have hlt : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) (q y).val < a := Nat.lt_of_not_ge hnot
    have hfix := hfixedEarlier (q y) hlt
    have : q y = y := q.injective hfix
    rw [this] at hlt
    omega
  have hentryLe : ∀ y ∈ (Finset.univ : Finset (Fin n)).filter
      (fun z => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) z.val = a),
      T.auxiliaryPositionEntry y ≤ T.auxiliaryPositionEntry (q y) := by
    intro y hy
    have hyRow := (Finset.mem_filter.mp hy).2
    by_cases hyFix : q y = y
    · rw [hyFix]
    · apply Nat.le_of_lt
      have hrowLt : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) y.val <
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) (q y).val := by
        have hge := hqRowGe y hyRow
        have hne : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) (q y).val ≠ a := by
          intro heq
          have hcol := hq y
          have hsum : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu).sum = n := by
            have hsort : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) : Multiset ℕ) = nu.parts :=
              nu.parts.sort_eq (· ≥ ·)
            have : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu).sum = nu.parts.sum := by
              rw [← Multiset.sum_coe, hsort]
            rw [this, nu.parts_sum]
          have hval := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu)
            (q y).val y.val (by rw [hsum]; exact (q y).isLt)
            (by rw [hsum]; exact y.isLt) (heq.trans hyRow.symm) hcol
          exact hyFix (Fin.ext hval)
        omega
      have hcolCell : (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu y).1.2 =
          (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu (q y)).1.2 := by
        simpa only [RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex, RepresentationTheory.Combinatorics.PartitionPermutation.partitionIndexOfFin,
          Equiv.ofBijective_apply] using (hq y).symm
      have hrowCell : (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu y).1.1 <
          (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu (q y)).1.1 := by
        simpa only [RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex, RepresentationTheory.Combinatorics.PartitionPermutation.partitionIndexOfFin,
          Equiv.ofBijective_apply] using hrowLt
      change T.1 (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu y).1.1
          (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu y).1.2 <
        T.1 (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu (q y)).1.1
          (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu (q y)).1.2
      rw [hcolCell]
      exact T.1.col_strict hrowCell
        (canonicalCell_mem_partitionDiagram (nu := nu) (q y))
  have hxStrict : T.auxiliaryPositionEntry x < T.auxiliaryPositionEntry (q x) := by
    have hxInRow : x ∈ (Finset.univ : Finset (Fin n)).filter
        (fun z => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) z.val = a) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hxRow⟩
    have hxLe := hentryLe x hxInRow
    have hxRowGe := hqRowGe x hxRow
    have hxRowNe : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) (q x).val ≠ a := by
      intro heq
      have hsum : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu).sum = n := by
        have hsort : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) : Multiset ℕ) = nu.parts :=
          nu.parts.sort_eq (· ≥ ·)
        have : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu).sum = nu.parts.sum := by
          rw [← Multiset.sum_coe, hsort]
        rw [this, nu.parts_sum]
      have hval := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu)
        (q x).val x.val (by rw [hsum]; exact (q x).isLt)
        (by rw [hsum]; exact x.isLt) (heq.trans hxRow.symm) (hq x)
      exact hxNe (Fin.ext hval)
    have hrowLt : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) x.val <
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) (q x).val := by omega
    have hcolCell : (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x).1.2 =
        (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu (q x)).1.2 := by
      simpa only [RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex, RepresentationTheory.Combinatorics.PartitionPermutation.partitionIndexOfFin,
        Equiv.ofBijective_apply] using (hq x).symm
    have hrowCell : (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x).1.1 <
        (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu (q x)).1.1 := by
      simpa only [RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex, RepresentationTheory.Combinatorics.PartitionPermutation.partitionIndexOfFin,
        Equiv.ofBijective_apply] using hrowLt
    change T.1 (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x).1.1
        (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x).1.2 <
      T.1 (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu (q x)).1.1
        (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu (q x)).1.2
    rw [hcolCell]
    exact T.1.col_strict hrowCell
      (canonicalCell_mem_partitionDiagram (nu := nu) (q x))
  let rowSet := (Finset.univ : Finset (Fin n)).filter
    (fun z => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) z.val = a)
  have hsumReindex :
      ∑ y ∈ rowSet, T.auxiliaryPositionEntry (q (r y)) =
        ∑ y ∈ rowSet, T.auxiliaryPositionEntry (q y) := by
    apply Finset.sum_equiv r
    · intro y
      simp only [rowSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hy => (hr y).trans hy, fun hy => (hr y).symm.trans hy⟩
    · intro y hy
      rfl
  have hsumEq : (∑ y ∈ rowSet, T.auxiliaryPositionEntry (q y)) =
      ∑ y ∈ rowSet, T.auxiliaryPositionEntry y := by
    rw [← hsumReindex]
    apply Finset.sum_congr rfl
    intro y hy
    exact hpres y
  have hxInRow : x ∈ rowSet := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hxRow⟩
  have hsumLt : (∑ y ∈ rowSet, T.auxiliaryPositionEntry y) <
      ∑ y ∈ rowSet, T.auxiliaryPositionEntry (q y) :=
    Finset.sum_lt_sum
      (fun y hy => hentryLe y hy)
      ⟨x, hxInRow, hxStrict⟩
  omega





/-- Equality of the displayed auxiliary permutation images forces the left permutation to be the identity. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliary_left_perm_eq_one_of_map_eq
    {n : ℕ} {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu)
    (q p : Equiv.Perm (Fin n)) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n nu)
    (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)
    (htab : RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType n nu (q⁻¹ * RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject) =
      RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType n nu (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject * p)) :
    q = 1 := by
  rw [RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType_eq_iff_mul_inv_mem] at htab
  let σ := RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject
  let r := q⁻¹ * σ * p⁻¹ * σ⁻¹
  have hr : r ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n nu := by
    simpa only [r, σ, mul_inv_rev, inv_inv, mul_assoc] using htab
  apply T.auxiliary_left_perm_eq_one q r hq hr
  intro x
  have hqr : q * r = σ * p⁻¹ * σ⁻¹ := by
    simp only [r]
    group
  have hpInv := (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu).inv_mem hp
  calc
    T.auxiliaryPositionEntry (q (r x)) =
        T.auxiliaryPositionEntry (σ (p⁻¹ (σ⁻¹ x))) := by
      rw [← Equiv.Perm.mul_apply, hqr]
      rfl
    _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (p⁻¹ (σ⁻¹ x)).val := by
      exact T.auxiliaryPositionEntry_standardization (p⁻¹ (σ⁻¹ x))
    _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (σ⁻¹ x).val := hpInv (σ⁻¹ x)
    _ = T.auxiliaryPositionEntry (σ (σ⁻¹ x)) := by
      exact (T.auxiliaryPositionEntry_standardization (σ⁻¹ x)).symm
    _ = T.auxiliaryPositionEntry x := by simp

end

end RepresentationTheory.AuxiliaryPartitionLinearIndependence
