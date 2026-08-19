/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary
import RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics
import RepresentationTheory.Alignment.Attribute




















namespace RepresentationTheory.YoungDiagram.PartitionFormulas
noncomputable section
open scoped BigOperators










/-- The length of a row in a partition's Young diagram is the corresponding sorted part, with default value zero. -/
theorem Partition.toYoungDiagram_rowLen_eq_getD {m : ℕ} (μ : Nat.Partition m) (i : ℕ) :
    (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ).rowLen i = (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ).getD i 0 := by
  have key : ∀ j : ℕ, j < (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ).rowLen i ↔ j < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ).getD i 0 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    change (i, j) ∈ YoungDiagram.ofRowLens (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ) _ ↔ _
    rw [YoungDiagram.mem_ofRowLens]
    by_cases hlen : i < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ).length
    · rw [List.getD_eq_getElem _ _ hlen]
      constructor
      · rintro ⟨_, hj⟩; exact hj
      · intro hj; exact ⟨hlen, hj⟩
    · rw [List.getD_eq_default _ _ (not_lt.mp hlen)]
      constructor
      · rintro ⟨h, -⟩; exact absurd h hlen
      · intro hj; exact absurd hj (Nat.not_lt_zero j)
  have h1 := key ((RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ).rowLen i)
  have h2 := key ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ).getD i 0)
  omega


/-- The sorted-parts list constructed from a family indexed by `Fin N` has length at most `N`. -/
theorem toYoungDiagram_sortedParts_length_le (N : ℕ) (f : Fin N → ℕ) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N f)).length ≤ N := by
  unfold RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple
  rw [Multiset.length_sort]
  calc Multiset.card (Multiset.filter (0 < ·) (Finset.univ.val.map f))
      ≤ Multiset.card (Finset.univ.val.map f) := Multiset.card_le_card (Multiset.filter_le _ _)
    _ = N := by
        rw [Multiset.card_map]
        have : Multiset.card (Finset.univ.val : Multiset (Fin N)) = Finset.univ.card := rfl
        rw [this, Finset.card_univ, Fintype.card_fin]


/-- A row whose index is at least the size of the finite family has length zero. -/
theorem toYoungDiagram_rowLen_eq_zero_of_bound (N : ℕ) (f : Fin N → ℕ) {x : ℕ} (hx : N ≤ x) :
    (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N f)).rowLen x = 0 := by
  rw [Partition.toYoungDiagram_rowLen_eq_getD]
  exact List.getD_eq_default _ _ (le_trans (toYoungDiagram_sortedParts_length_le N f) hx)



private theorem weightToPartition_sortedParts_getD (N : ℕ) (f : Fin N → ℕ) (hf : Antitone f)
    (i : Fin N) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N f)).getD i.val 0 = f i := by
  unfold RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple
  simp only [Fin.univ_val_map]
  have h_sorted : ((List.ofFn f).filter (0 < ·)).SortedGE := by
    rw [List.sortedGE_iff_pairwise]
    exact List.Pairwise.filter _ (List.sortedGE_ofFn_iff.mpr hf).pairwise
  have h_sort_eq : ((↑(List.ofFn f) : Multiset ℕ).filter (0 < ·)).sort (· ≥ ·) =
      (List.ofFn f).filter (0 < ·) := by
    rw [Multiset.filter_coe]
    have h_perm : ((↑((List.ofFn f).filter (0 < ·)) : Multiset ℕ).sort (· ≥ ·)).Perm
        ((List.ofFn f).filter (0 < ·)) :=
      Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)
    have h_sort_sorted : (↑((List.ofFn f).filter (0 < ·)) : Multiset ℕ).sort (· ≥ ·)
        |>.SortedGE := by
      rw [List.sortedGE_iff_pairwise]
      exact Multiset.pairwise_sort _ _
    exact h_perm.eq_of_sortedGE h_sort_sorted h_sorted
  rw [h_sort_eq]
  suffices h_filter_eq : ∀ (m : ℕ) (g : Fin m → ℕ), Antitone g →
      ∀ j : Fin m, ((List.ofFn g).filter (0 < ·)).getD j.val 0 = g j by
    exact h_filter_eq N f hf i
  intro m g hg j
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    rw [List.ofFn_succ]
    by_cases hg0 : 0 < g 0
    · simp only [List.filter_cons, decide_eq_true_eq.mpr hg0, ↓reduceIte]
      cases j using Fin.cases with
      | zero => simp [List.getD]
      | succ j' =>
        simp only [List.getD]
        have hgs : Antitone (g ∘ Fin.succ) :=
          fun a b hab => hg (show Fin.succ a ≤ Fin.succ b from Fin.succ_le_succ_iff.mpr hab)
        exact ih (g ∘ Fin.succ) hgs j'
    · push Not at hg0
      have hg0' : g 0 = 0 := Nat.le_zero.mp hg0
      simp only [List.filter_cons, show decide (0 < g 0) = false from
        decide_eq_false (not_lt.mpr hg0), Bool.false_eq_true, ↓reduceIte]
      have hall : ∀ k : Fin (m + 1), g k = 0 :=
        fun k => Nat.le_zero.mp (hg0' ▸ hg (Fin.zero_le k))
      have h_empty : List.filter (fun x => decide (0 < x))
          (List.ofFn (fun i : Fin m => g i.succ)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx; rw [List.mem_ofFn] at hx; obtain ⟨k, rfl⟩ := hx
        simp [hall k.succ]
      rw [h_empty]; simp [hall j]


/-- At an index in the finite family, the corresponding Young-diagram row has length equal to that part. -/
theorem toYoungDiagram_rowLen_eq_parts (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) (i : Fin N) :
    (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)).rowLen i = lam.parts i := by
  rw [Partition.toYoungDiagram_rowLen_eq_getD]
  exact weightToPartition_sortedParts_getD N lam.parts lam.parts_antitone i



/-- A column length in the Young diagram is the number of indexed parts strictly exceeding the column index. -/
theorem toYoungDiagram_colLen_eq_card_filter (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) (c : ℕ) :
    (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)).colLen c =
      (Finset.univ.filter (fun i : Fin N => c < lam.parts i)).card := by
  rw [← Finset.card_range ((RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)).colLen c),
      ← Finset.card_image_of_injective
        (Finset.univ.filter (fun i : Fin N => c < lam.parts i)) Fin.val_injective]
  congr 1
  ext x
  simp only [Finset.mem_range, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    have hmem : ((x, c) : ℕ × ℕ) ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)) :=
      YoungDiagram.mem_iff_lt_colLen.mpr hx
    have hxN : x < N := by
      by_contra h
      push Not at h
      rw [YoungDiagram.mem_iff_lt_rowLen, toYoungDiagram_rowLen_eq_zero_of_bound N lam.parts h] at hmem
      exact absurd hmem (Nat.not_lt_zero c)
    refine ⟨⟨x, hxN⟩, ?_, rfl⟩
    rw [YoungDiagram.mem_iff_lt_rowLen, toYoungDiagram_rowLen_eq_parts N lam ⟨x, hxN⟩] at hmem
    exact hmem
  · rintro ⟨i, hi, rfl⟩
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen,
        toYoungDiagram_rowLen_eq_parts N lam i]
    exact hi



/-- A hook length is the remaining length in its row plus the number of later rows extending beyond its column. -/
theorem toYoungDiagram_hookLength_eq_row_remainder_add_card (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n)
    (i : Fin N) {c : ℕ} (hc : c < lam.parts i) :
    (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts))) i c =
      lam.parts i - c +
        (Finset.univ.filter (fun r : Fin N => i < r ∧ c < lam.parts r)).card := by
  have hAcard : (Finset.univ.filter (fun r : Fin N => r ≤ i)).card = i.val + 1 := by
    rw [← Finset.card_range (i.val + 1),
        ← Finset.card_image_of_injective _ Fin.val_injective]
    congr 1
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_range, Fin.le_iff_val_le_val]
    constructor
    · rintro ⟨r, hr, rfl⟩; omega
    · intro hx
      have hxi : x ≤ i.val := by omega
      have hxN : x < N := lt_of_le_of_lt hxi i.isLt
      exact ⟨⟨x, hxN⟩, hxi, rfl⟩
  have hdisj : Disjoint (Finset.univ.filter (fun r : Fin N => r ≤ i))
      (Finset.univ.filter (fun r : Fin N => i < r ∧ c < lam.parts r)) := by
    rw [Finset.disjoint_left]
    intro r hrA hrB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrA hrB
    exact absurd hrB.1 (not_lt.mpr hrA)
  have hcol : (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)).colLen c =
      (i.val + 1) + (Finset.univ.filter (fun r : Fin N => i < r ∧ c < lam.parts r)).card := by
    rw [toYoungDiagram_colLen_eq_card_filter N lam c]
    have hunion : (Finset.univ.filter (fun r : Fin N => c < lam.parts r)) =
        (Finset.univ.filter (fun r : Fin N => r ≤ i)) ∪
        (Finset.univ.filter (fun r : Fin N => i < r ∧ c < lam.parts r)) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro hr
        by_cases h : r ≤ i
        · exact Or.inl h
        · exact Or.inr ⟨not_le.mp h, hr⟩
      · rintro (h | ⟨_, h⟩)
        · exact lt_of_lt_of_le hc (lam.parts_antitone h)
        · exact h
    rw [hunion, Finset.card_union_of_disjoint hdisj, hAcard]
  rw [RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellStatistic, toYoungDiagram_rowLen_eq_parts N lam i, hcol]
  omega


/-- The hook-length product of the Young diagram is the iterated product of its hook lengths over the displayed rows and columns. -/
theorem toYoungDiagram_hookLengthProduct_eq_prod (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts))) =
      ∏ i : Fin N, ∏ c ∈ Finset.range (lam.parts i),
        (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts))) i c := by
  have hcell : ∀ p : ℕ × ℕ,
      p ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)).cells → p.1 < N := by
    intro p hp
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hp
    by_contra h
    push Not at h
    rw [toYoungDiagram_rowLen_eq_zero_of_bound N lam.parts h] at hp
    exact absurd hp (Nat.not_lt_zero p.2)
  unfold RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic
  rw [Finset.prod_sigma']
  refine Finset.prod_bij'
    (fun (c : ℕ × ℕ) (hc : c ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)).cells) =>
      (⟨⟨c.1, hcell c hc⟩, c.2⟩ : (_ : Fin N) × ℕ))
    (fun (p : (_ : Fin N) × ℕ) _ => (p.1.val, p.2))
    ?_ ?_ ?_ ?_ ?_
  · intro c hc
    have hlt := hcell c hc
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_range, ← toYoungDiagram_rowLen_eq_parts N lam ⟨c.1, hlt⟩]
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc
    exact hc
  · intro p hp
    rw [Finset.mem_sigma, Finset.mem_range] at hp
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, toYoungDiagram_rowLen_eq_parts N lam p.1]
    exact hp.2
  · intro c hc; rfl
  · intro p hp; rfl
  · intro c hc; rfl

















private theorem descPochhammer_alternant_det_eq_prod_sub
    (N : ℕ) (β : Fin N → ℕ) (hβ : StrictAnti β) :
    (Matrix.of fun i j : Fin N =>
        (descPochhammer ℤ (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j)).eval (β i : ℤ)).det =
      ((∏ i, ∏ j ∈ Finset.Ioi i, (β i - β j) : ℕ) : ℤ) := by
  classical
  set γ : Fin N → ℤ := fun i => (β (Fin.rev i) : ℤ) with hγ


  have hBγ : (Matrix.vandermonde γ).det
      = (Matrix.of fun i j : Fin N => (descPochhammer ℤ (j : ℕ)).eval (γ i)).det :=
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde γ
      (fun i : Fin N => descPochhammer ℤ (i : ℕ))
      (fun i => descPochhammer_natDegree ℤ i)
      (fun i => monic_descPochhammer ℤ i)


  have hsub : (Matrix.of fun i j : Fin N =>
        (descPochhammer ℤ (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j)).eval (β i : ℤ)).submatrix
          Fin.revPerm Fin.revPerm
      = (Matrix.of fun i j : Fin N => (descPochhammer ℤ (j : ℕ)).eval (γ i)) := by
    ext i j
    have hvj : RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N (Fin.rev j) = (j : ℕ) := by
      have hj := j.isLt
      simp only [RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents, Fin.val_rev]
      omega
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.revPerm_apply, hγ, hvj]

  have hdet : (Matrix.of fun i j : Fin N =>
        (descPochhammer ℤ (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j)).eval (β i : ℤ)).det
      = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (γ j - γ i) := by
    rw [← Matrix.det_submatrix_equiv_self Fin.revPerm
          (Matrix.of fun i j : Fin N =>
            (descPochhammer ℤ (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j)).eval (β i : ℤ)),
        hsub, ← hBγ, Matrix.det_vandermonde]
  rw [hdet]

  have hcast : ((∏ i, ∏ j ∈ Finset.Ioi i, (β i - β j) : ℕ) : ℤ)
      = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((β i : ℤ) - (β j : ℤ)) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    exact Nat.cast_sub (hβ (Finset.mem_Ioi.mp hj)).le
  rw [hcast, Finset.prod_sigma', Finset.prod_sigma']

  apply Finset.prod_nbij'
    (fun x : Σ _ : Fin N, Fin N => (⟨Fin.rev x.2, Fin.rev x.1⟩ : Σ _ : Fin N, Fin N))
    (fun x : Σ _ : Fin N, Fin N => (⟨Fin.rev x.2, Fin.rev x.1⟩ : Σ _ : Fin N, Fin N))
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hx ⊢
    exact Fin.rev_lt_rev.mpr hx
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hx ⊢
    exact Fin.rev_lt_rev.mpr hx
  · intro x _; simp only [Fin.rev_rev]
  · intro x _; simp only [Fin.rev_rev]
  · intro x _; simp only [hγ]




/-- The determinant of descending-Pochhammer evaluations agrees with the determinant of the corresponding powers. -/
@[source_ref "Chapter5/Discussion_hook_length_derivation" (role := primary)]
theorem det_descPochhammer_eval_eq_det_pow
    (N : ℕ) (β : Fin N → ℕ) :
    (Matrix.of fun i j : Fin N =>
        (descPochhammer ℤ (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j)).eval (β i : ℤ)).det =
      (Matrix.of fun i j : Fin N =>
        (β i : ℤ) ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j).det := by
  classical
  set γ : Fin N → ℤ := fun i => (β (Fin.rev i) : ℤ) with hγ
  have hdesc : (Matrix.of fun i j : Fin N =>
        (descPochhammer ℤ (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j)).eval (β i : ℤ)).submatrix
          Fin.revPerm Fin.revPerm =
      Matrix.of fun i j : Fin N => (descPochhammer ℤ (j : ℕ)).eval (γ i) := by
    ext i j
    have hvj : RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N (Fin.rev j) = (j : ℕ) := by
      have hj := j.isLt
      simp only [RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents, Fin.val_rev]
      omega
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.revPerm_apply, hγ, hvj]
  have hpow : (Matrix.of fun i j : Fin N =>
        (β i : ℤ) ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j).submatrix Fin.revPerm Fin.revPerm =
      Matrix.vandermonde γ := by
    ext i j
    have hvj : RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N (Fin.rev j) = (j : ℕ) := by
      have hj := j.isLt
      simp only [RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents, Fin.val_rev]
      omega
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.revPerm_apply,
      Matrix.vandermonde, hγ, hvj]
  rw [← Matrix.det_submatrix_equiv_self Fin.revPerm
        (Matrix.of fun i j : Fin N =>
          (descPochhammer ℤ (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j)).eval (β i : ℤ)),
    hdesc, ← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde γ
      (fun i : Fin N => descPochhammer ℤ (i : ℕ))
      (fun i => descPochhammer_natDegree ℤ i)
      (fun i => monic_descPochhammer ℤ i),
    ← hpow, Matrix.det_submatrix_equiv_self]













private lemma coeff_sum_X_pow_eq_multinomial (N n : ℕ) (γ : Fin N → ℕ)
    (hγ : ∑ i, γ i = n) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm γ)
        ((∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n)
      = (Nat.multinomial Finset.univ γ : ℚ) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag, MvPolynomial.coeff_sum, Finset.sum_eq_single γ]
  · rw [show ((Nat.multinomial Finset.univ γ : ℕ) : MvPolynomial (Fin N) ℚ)
          = MvPolynomial.C ((Nat.multinomial Finset.univ γ : ℚ)) from
        (map_natCast MvPolynomial.C _).symm,
      MvPolynomial.coeff_C_mul, RepresentationTheory.SymmetricPolynomials.Alternant.prod_X_pow_eq_monomial, MvPolynomial.coeff_monomial,
      if_pos rfl, mul_one]
  · intro k _ hkne
    rw [show ((Nat.multinomial Finset.univ k : ℕ) : MvPolynomial (Fin N) ℚ)
          = MvPolynomial.C ((Nat.multinomial Finset.univ k : ℚ)) from
        (map_natCast MvPolynomial.C _).symm,
      MvPolynomial.coeff_C_mul, RepresentationTheory.SymmetricPolynomials.Alternant.prod_X_pow_eq_monomial, MvPolynomial.coeff_monomial,
      if_neg (fun h => hkne (Finsupp.equivFunOnFinite.symm.injective h)), mul_zero]
  · intro hmem
    exact absurd (Finset.mem_piAntidiag.mpr ⟨hγ, fun i _ => Finset.mem_univ i⟩) hmem





private lemma multinomial_mul_prod_factorial_eq
    (N n : ℕ) (β e : Fin N → ℕ) (τ : Equiv.Perm (Fin N))
    (hβ : ∑ i, β i = n + ∑ i, e i) :
    (if (∀ i, e (τ i) ≤ β i) then Nat.multinomial Finset.univ (fun i => β i - e (τ i)) else 0)
        * (∏ j, (β j).factorial)
      = n.factorial * ∏ i, (β i).descFactorial (e (τ i)) := by
  by_cases H : ∀ i, e (τ i) ≤ β i
  · rw [if_pos H]
    have hsum : ∑ i, (β i - e (τ i)) = n := by
      have hadd : ∑ i, ((β i - e (τ i)) + e (τ i)) = ∑ i, β i :=
        Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (H i))
      rw [Finset.sum_add_distrib, Equiv.sum_comp τ e] at hadd
      omega
    have hfac : ∏ j, (β j).factorial
        = (∏ i, (β i - e (τ i)).factorial) * ∏ i, (β i).descFactorial (e (τ i)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => (Nat.factorial_mul_descFactorial (H i)).symm)
    rw [hfac, ← mul_assoc, mul_comm (Nat.multinomial _ _) _, Nat.multinomial_spec, hsum]
  · rw [if_neg H, zero_mul]
    obtain ⟨i, hi⟩ := not_forall.mp H
    rw [Finset.prod_eq_zero (Finset.mem_univ i)
      (Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp hi)), mul_zero]











/-- An auxiliary value at the displayed partition is expressed using factorials and a determinant of descending-Pochhammer evaluations. -/
@[source_ref "Chapter5/Discussion_hook_length_derivation" (role := primary)]
theorem auxiliary_partition_value_eq_descPochhammer_determinant_formula
    (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam (RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.partitionChoice n) =
      (n.factorial : ℚ) / (∏ j, ((RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts j).factorial : ℚ)) *
        ((Matrix.of fun i j : Fin N =>
            (descPochhammer ℤ (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j)).eval
              (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts i : ℤ)).det : ℚ) := by
  classical
  rw [show RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam (RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.partitionChoice n)
        = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts))
            ((RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det *
              MvPolynomial.psumPart (Fin N) ℚ (RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.partitionChoice n)) from rfl,
    RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.psumPart_partitionChoice_eq_sum_variables_pow]
  set e := RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N with he_def
  set β := RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts with hβ_def
  have hβsum : ∑ i, β i = n + ∑ i, e i := by
    simp only [hβ_def, he_def, RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents]
    rw [Finset.sum_add_distrib, lam.sum_parts]
  have hβfac_ne : (∏ j, ((β j).factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

  have hD : (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e).det
      = ∑ σ : Equiv.Perm (Fin N),
          Equiv.Perm.sign σ •
            MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) (1 : ℚ) := by
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    rw [show ∏ j, RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e (σ j) j
          = ∏ j, (MvPolynomial.X (σ j) : MvPolynomial (Fin N) ℚ) ^ e j from rfl,
        show ∏ j, (MvPolynomial.X (σ j) : MvPolynomial (Fin N) ℚ) ^ e j
          = ∏ i, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ) ^ (e (σ.symm i))
          from Fintype.prod_equiv σ _ _ (fun _ => by simp)]
    exact RepresentationTheory.SymmetricPolynomials.Alternant.prod_X_pow_eq_monomial _

  have hdet : ((Matrix.of fun i j : Fin N =>
        (descPochhammer ℤ (e j)).eval (β i : ℤ)).det : ℚ)
      = ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ •
          (∏ i, ((β i).descFactorial (e (σ.symm i)) : ℚ)) := by
    rw [Int.cast_det, Matrix.det_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    rw [← Equiv.prod_comp σ (fun k => ((β k).descFactorial (e (σ.symm k)) : ℚ))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [Matrix.map_apply, descPochhammer_eval_eq_descFactorial, Equiv.symm_apply_apply]
  rw [hD, Finset.sum_mul, MvPolynomial.coeff_sum, hdet, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [smul_mul_assoc]
  change MvPolynomial.coeff _ ((Equiv.Perm.sign σ : ℚ) • _) = _
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial_mul', one_mul,
      mul_smul_comm]
  congr 1
  by_cases H : ∀ i, e (σ.symm i) ≤ β i
  · have hle : (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm))
        ≤ Finsupp.equivFunOnFinite.symm β := by
      rw [Finsupp.le_iff' _ _ (Finset.subset_univ _)]
      intro i _
      simpa [Finsupp.equivFunOnFinite] using H i
    have hsum : ∑ i, (β i - e (σ.symm i)) = n := by
      have hadd : ∑ i, ((β i - e (σ.symm i)) + e (σ.symm i)) = ∑ i, β i :=
        Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (H i))
      rw [Finset.sum_add_distrib, Equiv.sum_comp σ.symm e] at hadd
      omega
    rw [if_pos hle,
      show (Finsupp.equivFunOnFinite.symm β - Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm))
          = Finsupp.equivFunOnFinite.symm (fun i => β i - e (σ.symm i)) from by
        ext i; rw [Finsupp.tsub_apply]; simp [Finsupp.equivFunOnFinite],
      coeff_sum_X_pow_eq_multinomial N n _ hsum,
      div_mul_eq_mul_div, eq_div_iff hβfac_ne]
    have hL2 := multinomial_mul_prod_factorial_eq N n β e σ.symm hβsum
    rw [if_pos H] at hL2
    exact_mod_cast hL2
  · have hnle : ¬ (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm))
        ≤ Finsupp.equivFunOnFinite.symm β := by
      rw [Finsupp.le_iff' _ _ (Finset.subset_univ _)]
      push Not
      obtain ⟨i, hi⟩ := not_forall.mp H
      exact ⟨i, Finset.mem_univ i, by
        have := not_le.mp hi; simpa [Finsupp.equivFunOnFinite] using this⟩
    obtain ⟨i, hi⟩ := not_forall.mp H
    have hHσ : (∏ i, ((β i).descFactorial (e (σ.symm i)) : ℚ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp hi)]; exact Nat.cast_zero)
    rw [if_neg hnle, hHσ, mul_zero]



















/-- An auxiliary value at the displayed partition is a factorial times pairwise differences of displayed values, divided by their factorial product. -/
theorem auxiliary_partition_value_eq_pairwise_difference_formula
    (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam (RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.partitionChoice n) =
      (n.factorial : ℚ) *
        ((∏ i, ∏ j ∈ Finset.Ioi i,
            (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts j) : ℕ) : ℚ) /
        ((∏ j, (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts j).factorial : ℕ) : ℚ) := by
  rw [auxiliary_partition_value_eq_descPochhammer_determinant_formula N lam,
    descPochhammer_alternant_det_eq_prod_sub N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts)
      (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase_strictAnti lam)]
  push_cast
  ring






/-- The transported auxiliary subtype's complex finrank is expressed by displayed factorials and a determinant of powers of displayed values. -/
@[source_ref "Chapter5/Discussion_hook_length_derivation" (role := supporting)]
theorem auxiliary_finrank_eq_power_determinant_formula
    (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    (Module.finrank ℂ
        (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)) : ℚ) =
      (n.factorial : ℚ) /
          (∏ j, ((RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts j).factorial : ℚ)) *
        ((Matrix.of fun i j : Fin N =>
          (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts i : ℤ) ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j).det : ℚ) := by
  rw [← RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.auxiliaryValue_eq_finrank,
    auxiliary_partition_value_eq_descPochhammer_determinant_formula,
    det_descPochhammer_eval_eq_det_pow]







/-- The transported auxiliary subtype's complex finrank is given by a factorial and pairwise-difference product formula. -/
@[source_ref "Chapter5/Discussion_hook_length_derivation" (role := primary)]
theorem auxiliary_finrank_eq_pairwise_difference_formula
    (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    (Module.finrank ℂ
        (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)) : ℚ) =
      (n.factorial : ℚ) *
        ((∏ i, ∏ j ∈ Finset.Ioi i,
            (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts j) : ℕ) : ℚ) /
        ((∏ j, (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts j).factorial : ℕ) : ℚ) := by
  rw [← RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.auxiliaryValue_eq_finrank]
  exact auxiliary_partition_value_eq_pairwise_difference_formula N lam


private theorem prod_range_sub_eq_factorial (k : ℕ) :
    ∏ x ∈ Finset.range k, (k - x) = k.factorial := by
  rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect (fun x => x + 1) k]
  refine Finset.prod_congr rfl (fun x hx => ?_)
  rw [Finset.mem_range] at hx
  omega




private theorem hookLengthProduct_cast {a b : ℕ} (h : a = b) (p : Nat.Partition a) :
    (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (h ▸ p))) = (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition p)) := by
  subst h; rfl













private theorem row_hook_gap_prod_eq_factorial (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n)
    (i : Fin N) :
    (∏ c ∈ Finset.range (lam.parts i),
        (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts))) i c) *
      (∏ k ∈ Finset.Ioi i,
        (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts k)) =
      (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts i).factorial := by
  classical
  set β := RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts with hβdef
  have hβanti : StrictAnti β := by rw [hβdef]; exact RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase_strictAnti lam
  have hβinj : Function.Injective β := hβanti.injective
  have hβi : β i = lam.parts i + (N - 1 - (i : ℕ)) := by rw [hβdef]; simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]
  set g : ℕ → ℕ :=
    fun c => c + ((Finset.Ioi i).filter (fun r => lam.parts r ≤ c)).card with hgdef
  have hg_sm : StrictMono g := by
    intro a b hab
    have hcard : ((Finset.Ioi i).filter (fun r => lam.parts r ≤ a)).card ≤
        ((Finset.Ioi i).filter (fun r => lam.parts r ≤ b)).card := by
      apply Finset.card_le_card
      intro r hr
      rw [Finset.mem_filter] at hr ⊢
      exact ⟨hr.1, le_trans hr.2 hab.le⟩
    simp only [hgdef]
    omega
  have hg_inj : Function.Injective g := hg_sm.injective
  set SA := (Finset.Ioi i).image β with hSA
  set SB := (Finset.range (lam.parts i)).image g with hSB
  have hSA_sub : SA ⊆ Finset.range (β i) := by
    intro v hv
    rw [hSA, Finset.mem_image] at hv
    obtain ⟨k, hk, rfl⟩ := hv
    rw [Finset.mem_range]
    exact hβanti (Finset.mem_Ioi.mp hk)
  have hSB_sub : SB ⊆ Finset.range (β i) := by
    intro v hv
    rw [hSB, Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    rw [Finset.mem_range] at hc ⊢
    have hBle : ((Finset.Ioi i).filter (fun r => lam.parts r ≤ c)).card ≤ (Finset.Ioi i).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hIoii : (Finset.Ioi i).card = N - 1 - (i : ℕ) := Fin.card_Ioi i
    rw [hIoii] at hBle
    simp only [hgdef]
    rw [hβi]
    omega
  have hdisj : Disjoint SA SB := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    rw [hSA, Finset.mem_image] at hvA
    rw [hSB, Finset.mem_image] at hvB
    obtain ⟨k, hk, hkv⟩ := hvA
    obtain ⟨c, _, hcv⟩ := hvB
    rw [Finset.mem_Ioi] at hk
    have heq : β k = g c := by rw [hkv, hcv]
    have hβk : β k = lam.parts k + (N - 1 - (k : ℕ)) := by rw [hβdef]; simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]
    have hkN : (k : ℕ) < N := k.isLt
    rcases Nat.lt_or_ge c (lam.parts k) with hkc | hkc
    ·
      have hle : ((Finset.Ioi i).filter (fun r => lam.parts r ≤ c)).card ≤ N - 1 - (k : ℕ) := by
        have hIoik : (Finset.Ioi k).card = N - 1 - (k : ℕ) := Fin.card_Ioi k
        rw [← hIoik]
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_filter, Finset.mem_Ioi] at hs
        obtain ⟨_, hs2⟩ := hs
        rw [Finset.mem_Ioi]
        by_contra hcon
        push Not at hcon
        have hmono := lam.parts_antitone hcon
        omega
      simp only [hgdef] at heq
      omega
    ·
      have hge : (N : ℕ) - (k : ℕ) ≤
          ((Finset.Ioi i).filter (fun r => lam.parts r ≤ c)).card := by
        have hIci : (Finset.Ici k).card = N - (k : ℕ) := Fin.card_Ici k
        rw [← hIci]
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_Ici] at hs
        rw [Finset.mem_filter, Finset.mem_Ioi]
        exact ⟨lt_of_lt_of_le hk hs, le_trans (lam.parts_antitone hs) hkc⟩
      simp only [hgdef] at heq
      omega
  have hcardSA : SA.card = N - 1 - (i : ℕ) := by
    rw [hSA, Finset.card_image_of_injective _ hβinj]
    exact Fin.card_Ioi i
  have hcardSB : SB.card = lam.parts i := by
    rw [hSB, Finset.card_image_of_injective _ hg_inj, Finset.card_range]
  have hunion : SA ∪ SB = Finset.range (β i) := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hSA_sub hSB_sub)
    rw [Finset.card_range, Finset.card_union_of_disjoint hdisj, hcardSA, hcardSB, hβi]
    omega
  have hkey : ∀ c, c < lam.parts i →
      β i - g c = (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts))) i c := by
    intro c hc
    have hcompl : ((Finset.Ioi i).filter (fun r => c < lam.parts r)).card +
        ((Finset.Ioi i).filter (fun r => lam.parts r ≤ c)).card = N - 1 - (i : ℕ) := by
      have hIoii : (Finset.Ioi i).card = N - 1 - (i : ℕ) := Fin.card_Ioi i
      rw [← hIoii, ← Finset.card_filter_add_card_filter_not (s := Finset.Ioi i)
            (p := fun r => c < lam.parts r)]
      congr 1
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro r _
      simp only [not_lt]
    have hA : (Finset.univ.filter (fun r : Fin N => i < r ∧ c < lam.parts r)).card =
        ((Finset.Ioi i).filter (fun r => c < lam.parts r)).card := by
      congr 1
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
    rw [toYoungDiagram_hookLength_eq_row_remainder_add_card N lam i hc, hA]
    simp only [hgdef]
    rw [hβi]
    omega
  have hhook : (∏ c ∈ Finset.range (lam.parts i),
        (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts))) i c)
      = ∏ c ∈ Finset.range (lam.parts i), (β i - g c) := by
    refine Finset.prod_congr rfl (fun c hc => ?_)
    rw [Finset.mem_range] at hc
    rw [← hkey c hc]
  rw [hhook, ← prod_range_sub_eq_factorial (β i), ← hunion, Finset.prod_union hdisj,
      hSA, hSB, Finset.prod_image (fun x _ y _ h => hβinj h),
      Finset.prod_image (fun x _ y _ h => hg_inj h)]
  exact mul_comm _ _









/-- An auxiliary pairwise-difference product times the displayed hook-length product equals the product of the displayed factorials. -/
theorem auxiliary_pairwiseDifference_mul_hookLengthProduct_eq_factorialProduct
    (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    (∏ i, ∏ j ∈ Finset.Ioi i,
        (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts j) : ℕ) *
      (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts))) =
      (∏ j, (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts j).factorial : ℕ) := by
  rw [hookLengthProduct_cast lam.sum_parts, toYoungDiagram_hookLengthProduct_eq_prod,
      ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [mul_comm]
  exact row_hook_gap_prod_eq_factorial N lam i




private lemma frobeniusDetForm_eq_hookFormula_aux {nf V H L : ℕ}
    (hB : V * H = L) (hVpos : 0 < V) (hHpos : 0 < H) (hdvd : H ∣ nf) :
    (nf : ℚ) * (V : ℚ) / (L : ℚ) = ((nf / H : ℕ) : ℚ) := by
  have hV' : (V : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hVpos.ne'
  have hH' : (H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hHpos.ne'
  subst hB
  rw [Nat.cast_div hdvd hH']
  push_cast
  field_simp












/-- An auxiliary value at the displayed partition is the factorial divided by the Young-diagram hook-length product. -/
theorem auxiliary_partition_value_eq_factorial_div_hookLengthProduct
    (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam (RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.partitionChoice n) =
      ((n.factorial /
        (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)))
          : ℕ) : ℚ) := by
  rw [auxiliary_partition_value_eq_pairwise_difference_formula N lam]
  have hVpos : 0 < (∏ i, ∏ j ∈ Finset.Ioi i,
      (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts j) : ℕ) := by
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hlt : RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts j < RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.parts i := by
      simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]
      have h1 : lam.parts j ≤ lam.parts i := lam.parts_antitone hij.le
      have h2 : N - 1 - (j : ℕ) < N - 1 - (i : ℕ) := by
        have hjlt : (j : ℕ) < N := j.isLt
        have hij' : (i : ℕ) < (j : ℕ) := hij
        omega
      omega
    omega
  have hHpos : 0 < (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts))) :=
    RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic_pos _
  have hdvd : (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts))) ∣
      n.factorial :=
    RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.hookLengthProduct_dvd_factorial n (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)
  exact frobeniusDetForm_eq_hookFormula_aux
    (auxiliary_pairwiseDifference_mul_hookLengthProduct_eq_factorialProduct N lam) hVpos hHpos hdvd





/-- An auxiliary value at the displayed partition is the cardinality of the displayed associated type. -/
theorem auxiliary_partition_value_eq_card
    (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam (RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.partitionChoice n) =
      (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n
        (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)) : ℚ) := by
  rw [auxiliary_partition_value_eq_factorial_div_hookLengthProduct,
      RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryCard_eq_factorial_div_hookLengthProduct]




/-- After transporting the partition obtained from a finite family, the auxiliary subtype's complex finrank equals an associated cardinality. -/
theorem auxiliary_finrank_eq_card
    (N : ℕ) {n : ℕ} (lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    (Module.finrank ℂ
        (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)) : ℚ) =
      (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n
        (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)) : ℚ) := by
  rw [← RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.auxiliaryValue_eq_finrank]
  exact auxiliary_partition_value_eq_card N lam











private lemma list_length_le_sum_of_pos (m : List ℕ) (hm : ∀ x ∈ m, 0 < x) :
    m.length ≤ m.sum := by
  induction m with
  | nil => exact Nat.zero_le _
  | cons a t ih =>
    simp only [List.length_cons, List.sum_cons]
    have ha := hm a (by simp)
    have ht := ih (fun x hx => hm x (by simp [hx]))
    omega


private lemma sum_getD_eq_sum (l : List ℕ) (n : ℕ) (hlen : l.length ≤ n) :
    ∑ i : Fin n, l.getD i.val 0 = l.sum := by
  induction n generalizing l with
  | zero =>
    have := List.eq_nil_of_length_eq_zero (by omega : l.length = 0)
    subst this; rfl
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    cases l with
    | nil => simp
    | cons a t =>
      simp only [List.getD_cons_zero, List.sum_cons, Fin.val_zero]
      congr 1
      have hstep : ∀ i : Fin n, (a :: t).getD i.succ.val 0 = t.getD i.val 0 := by
        intro ⟨i, _⟩; simp
      simp_rw [hstep]
      exact ih t (by simpa using hlen)


private lemma getD_antitone_of_pairwise {n : ℕ} (l : List ℕ) (h : l.Pairwise (· ≥ ·)) :
    Antitone (fun i : Fin n => l.getD i.val 0) := by
  intro i j hij
  change l.getD j.val 0 ≤ l.getD i.val 0
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · by_cases hj : j.val < l.length
    · have hi : i.val < l.length := by omega
      rw [List.getD_eq_getElem (hn := hj), List.getD_eq_getElem (hn := hi)]
      exact List.pairwise_iff_get.mp h ⟨i.val, hi⟩ ⟨j.val, hj⟩ hlt
    · rw [List.getD_eq_default (hn := by omega)]
      exact Nat.zero_le _



private lemma ofFn_getD_filter_pos :
    ∀ (m : ℕ) (ll : List ℕ), (∀ x ∈ ll, 0 < x) → ll.length ≤ m →
      (List.ofFn (fun i : Fin m => ll.getD i.val 0)).filter (fun x => decide (0 < x)) = ll := by
  intro m
  induction m with
  | zero => intro ll _ hlen; simp [List.eq_nil_of_length_eq_zero (by omega : ll.length = 0)]
  | succ m ih =>
    intro ll hll hlen
    simp only [List.ofFn_succ, Fin.val_zero, List.filter_cons]
    cases ll with
    | nil =>
      simp only [List.getD_nil, List.ofFn_const, List.filter_replicate,
        show ¬ decide (0 < 0) = true from by simp]
      simp
    | cons a t =>
      simp only [List.getD_cons_zero]
      have ha : 0 < a := hll a (by simp)
      rw [show decide (0 < a) = true from decide_eq_true ha]
      simp only [ite_true]
      congr 1
      change (List.ofFn (fun i : Fin m => t.getD i.val 0)).filter (fun x => decide (0 < x)) = t
      exact ih t (fun x hx => hll x (by simp [hx]))
        (by simp only [List.length_cons] at hlen; omega)





/-- Every partition has an auxiliary preimage whose parts reconstruct it after the displayed dependent transport. -/
theorem auxiliary_exists_preimage_for_partition (n : ℕ) (la : Nat.Partition n) :
    ∃ bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition n n,
      (bp.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple n bp.parts : Nat.Partition n) = la := by
  have hpos : ∀ x ∈ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la), 0 < x := by
    intro x hx
    refine la.parts_pos ?_
    have h := Multiset.sort_eq la.parts (· ≥ ·)
    rw [show la.parts.sort (· ≥ ·) = (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) from rfl] at h
    exact h ▸ Multiset.mem_coe.mpr hx
  have hlen : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length ≤ n := by
    have hsum : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = n := RepresentationTheory.Partition.YoungDiagram.sum_sortedParts n la
    have := list_length_le_sum_of_pos (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) hpos
    omega
  refine ⟨{ parts := fun i : Fin n => (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i.val 0
            parts_antitone := getD_antitone_of_pairwise (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)
              (by rw [show (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) = la.parts.sort (· ≥ ·) from rfl]
                  exact Multiset.pairwise_sort _ _)
            sum_parts := by
              rw [sum_getD_eq_sum (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) n hlen]; exact RepresentationTheory.Partition.YoungDiagram.sum_sortedParts n la }, ?_⟩
  have hrec : ∀ (p q : ℕ) (h : p = q) (P : Nat.Partition p), (h ▸ P).parts = P.parts := by
    intro p q h P; subst h; rfl
  apply Nat.Partition.ext
  rw [hrec _ _ _ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple n (fun i : Fin n => (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i.val 0))]
  change (Finset.univ.val.map (fun i : Fin n => (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD i.val 0)).filter (0 < ·) =
      la.parts
  rw [Fin.univ_val_map, Multiset.filter_coe, ofFn_getD_filter_pos n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) hpos hlen]
  exact Multiset.sort_eq _ _




/-- The complex finrank of the auxiliary subtype associated with a partition equals the cardinality of the corresponding auxiliary type. -/
theorem finrank_auxiliary_subtype_eq_card (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) = Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) := by
  obtain ⟨bp, hbp⟩ := auxiliary_exists_preimage_for_partition n la
  have h := auxiliary_finrank_eq_card n bp
  rw [hbp] at h
  exact_mod_cast h

end
end RepresentationTheory.YoungDiagram.PartitionFormulas
