/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra
import RepresentationTheory.Alignment.Attribute

/-!
# Dominance relations for partitions

Vanishing results for partition-indexed elements of symmetric-group algebras.
-/

namespace RepresentationTheory.SymmetricGroup.PartitionDominance

open PartitionAuxiliaryConstructions PartitionGroupAlgebra



















/-- The dominance relation between partitions of the same natural number. -/
def Partition.Dominates {n : ℕ} (la mu : Nat.Partition n) : Prop :=
  ∀ k : ℕ, ((auxiliaryPartitionNatList mu).take k).sum ≤ ((auxiliaryPartitionNatList la).take k).sum


/-- The strict dominance relation between partitions of the same natural number. -/
def Partition.StrictDominates {n : ℕ} (la mu : Nat.Partition n) : Prop :=
  Partition.Dominates la mu ∧ la ≠ mu






/-- The strict lexicographic order on partitions of the same natural number. -/
@[source_ref "Chapter5/Discussion_lexicographic_ordering" (role := primary)]
def Partition.LexLt {n : ℕ} (la mu : Nat.Partition n) : Prop :=
  toLex (fun i : ℕ => (auxiliaryPartitionNatList la).getD i 0) <
    toLex (fun i : ℕ => (auxiliaryPartitionNatList mu).getD i 0)


/-- The lexicographic non-strict order on partitions of the same natural number. -/
@[source_ref "Chapter5/Discussion_lexicographic_ordering" (role := supporting)]
def Partition.LexLe {n : ℕ} (la mu : Nat.Partition n) : Prop :=
  toLex (fun i : ℕ => (auxiliaryPartitionNatList la).getD i 0) ≤
    toLex (fun i : ℕ => (auxiliaryPartitionNatList mu).getD i 0)



private theorem sum_take_succ_getD (l : List ℕ) (k : ℕ) :
    (l.take (k + 1)).sum = (l.take k).sum + l.getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
      cases k with
      | zero => simp
      | succ k => simp [ih, Nat.add_assoc]


private theorem sum_take_eq_of_getD_eq (l₁ l₂ : List ℕ) (k : ℕ)
    (h : ∀ j < k, l₁.getD j 0 = l₂.getD j 0) :
    (l₁.take k).sum = (l₂.take k).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_take_succ_getD, sum_take_succ_getD,
        ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h k (Nat.lt_succ_self k)]



/-- Dominance of `la` over `mu` implies that `mu` is lexicographically at most `la`. -/
@[source_ref "Chapter5/Discussion_lexicographic_ordering" (role := primary)]
theorem Partition.Dominates.lexLe {n : ℕ} {la mu : Nat.Partition n}
    (h : Partition.Dominates la mu) : Partition.LexLe mu la := by
  rw [Partition.LexLe]
  apply le_of_not_gt
  intro hlt
  obtain ⟨i, hbefore, hi⟩ := hlt
  have hpref : ((auxiliaryPartitionNatList la).take i).sum = ((auxiliaryPartitionNatList mu).take i).sum :=
    sum_take_eq_of_getD_eq (auxiliaryPartitionNatList la) (auxiliaryPartitionNatList mu) i hbefore
  have hi' : (auxiliaryPartitionNatList la).getD i 0 < (auxiliaryPartitionNatList mu).getD i 0 := hi
  have hdom := h (i + 1)
  rw [sum_take_succ_getD, sum_take_succ_getD, hpref] at hdom
  omega




/-- If `mu` is lexicographically smaller than `la`, then `mu` does not dominate `la`. -/
@[source_ref "Chapter5/Discussion_lexicographic_ordering" (role := primary),
  source_ref "Chapter5/Lemma5.13.2" (role := supporting)]
theorem Partition.LexLt.not_dominates {n : ℕ} {la mu : Nat.Partition n}
    (h : Partition.LexLt mu la) : ¬ Partition.Dominates mu la := by
  intro hdom
  exact (not_lt_of_ge (Partition.Dominates.lexLe hdom)) h


/-- There exist two partitions such that one is strictly smaller than the other in lexicographic order. -/
@[source_ref "Chapter5/Discussion_lexicographic_ordering" (role := supporting)]
theorem Partition.exists_lexLt :
    ∃ la mu : Nat.Partition 2, Partition.LexLt mu la := by
  let la : Nat.Partition 2 :=
    { parts := {2}
      parts_pos := by simp
      parts_sum := by simp }
  let mu : Nat.Partition 2 :=
    { parts := {1, 1}
      parts_pos := by simp
      parts_sum := by simp }
  have hla : (auxiliaryPartitionNatList la) = [2] := by
    unfold PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
    rw [show la.parts = (↑[2] : Multiset ℕ) by rfl, Multiset.coe_sort]
    exact List.mergeSort_eq_self (r := (· ≥ ·)) (by simp)
  have hmu : (auxiliaryPartitionNatList mu) = [1, 1] := by
    unfold PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
    rw [show mu.parts = (↑[1, 1] : Multiset ℕ) by rfl, Multiset.coe_sort]
    exact List.mergeSort_eq_self (r := (· ≥ ·)) (by simp)
  refine ⟨la, mu, ?_⟩
  rw [Partition.LexLt]
  refine ⟨0, ?_, ?_⟩
  · intro j hj
    omega
  · simp [hla, hmu]





/-- For a valid row and column, the flattened index given by the preceding row sums has the original row and column coordinates. -/
lemma rowColumnIndex_sum_take_add (parts : List ℕ) (r c : ℕ)
    (hr : r < parts.length) (hc : c < parts[r]) :
    flatIndexRow parts ((parts.take r).sum + c) = r ∧
    flatIndexColumn parts ((parts.take r).sum + c) = c := by
  induction parts generalizing r with
  | nil => simp at hr
  | cons a rest ih =>
    cases r with
    | zero =>
      simp only [List.getElem_cons_zero] at hc
      constructor
      · simp [flatIndexRow]; omega
      · simp [flatIndexColumn]; omega
    | succ r' =>
      simp only [List.length_cons] at hr
      simp only [List.getElem_cons_succ] at hc
      have hr' : r' < rest.length := by omega
      obtain ⟨ih1, ih2⟩ := ih r' hr' hc
      simp only [List.take_succ_cons, List.sum_cons]
      have hge : ¬ ((a + (rest.take r').sum + c) < a) := by omega
      have hsub : a + (rest.take r').sum + c - a = (rest.take r').sum + c := by omega
      constructor
      · simp [flatIndexRow, hge, hsub, ih1]; omega
      · simp [flatIndexColumn, hge, hsub, ih2]


/-- If `c` is less than the entry at index `r`, then the sum of the entries before `r` plus `c` is less than the total sum. -/
lemma List.sum_take_add_lt_sum (parts : List ℕ) (r c : ℕ)
    (hr : r < parts.length) (hc : c < parts[r]) :
    (parts.take r).sum + c < parts.sum := by
  have h1 : (parts.take r).sum + parts[r] ≤ (parts.take (r + 1)).sum := by
    rw [List.take_succ_eq_append_getElem hr, List.sum_append, List.sum_cons, List.sum_nil]
    omega
  have h2 : (parts.take (r + 1)).sum ≤ parts.sum :=
    List.Sublist.sum_le_sum (List.take_sublist (r + 1) parts) (fun _ _ => Nat.zero_le _)
  omega


/-- In a nonincreasing list, a number below the entry at a later index is also below the entry at any earlier index. -/
lemma List.lt_getElem_of_le_index (parts : List ℕ) (hSorted : parts.Pairwise (· ≥ ·))
    (r r' c : ℕ) (hr : r < parts.length) (hr' : r' < parts.length) (hle : r' ≤ r)
    (hc : c < parts[r]) : c < parts[r'] := by
  have : parts[r] ≤ parts[r'] := by
    rcases eq_or_lt_of_le hle with rfl | hlt
    · omega
    · exact List.pairwise_iff_getElem.mp hSorted r' r hr' hr hlt
  omega



private theorem sortedParts_sum {n : ℕ} (la : Nat.Partition n) :
    (auxiliaryPartitionNatList la).sum = n := by
  have h := la.parts_sum
  have hsort : ((auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts := la.parts.sort_eq (· ≥ ·)
  have : (auxiliaryPartitionNatList la).sum = la.parts.sum := by rw [← Multiset.sum_coe, hsort]
  omega

/-- Every entry occurring in the sorted parts of a partition is positive. -/
theorem Partition.zero_lt_of_mem_sortedParts (la : Nat.Partition n) :
    ∀ x ∈ (auxiliaryPartitionNatList la), 0 < x := fun _ hx =>
  la.parts_pos ((Multiset.mem_sort _).mp hx)

/-- The sorted parts of a partition are pairwise nonincreasing. -/
theorem Partition.sortedParts_pairwise_ge (la : Nat.Partition n) :
    (auxiliaryPartitionNatList la).Pairwise (· ≥ ·) := la.parts.pairwise_sort (· ≥ ·)


/-- For an index below the total sum, its row coordinate is less than `k` exactly when the index lies below the sum of the first `k` entries. -/
theorem rowIndex_lt_iff_lt_sum_take (parts : List ℕ) (j k : ℕ) (hj : j < parts.sum) :
    flatIndexRow parts j < k ↔ j < (parts.take k).sum := by
  induction parts generalizing j k with
  | nil => simp at hj
  | cons p ps ih =>
    cases k with
    | zero =>
      simp only [List.take_zero, List.sum_nil, flatIndexRow]
      split_ifs with h <;> omega
    | succ k =>
      simp only [List.take_succ_cons, List.sum_cons, flatIndexRow]
      split_ifs with h
      · omega
      · have hj' : j - p < ps.sum := by simp [List.sum_cons] at hj; omega
        have := ih (j - p) k hj'
        omega


/-- The row coordinate of an index below the total sum is a valid list index. -/
theorem rowIndex_lt_length (parts : List ℕ) (j : ℕ) (hj : j < parts.sum) :
    flatIndexRow parts j < parts.length := by
  induction parts generalizing j with
  | nil => simp at hj
  | cons p ps ih =>
    simp only [flatIndexRow, List.length_cons]
    split_ifs with h
    · omega
    · have := ih (j - p) (by simp [List.sum_cons] at hj; omega); omega


/-- The column coordinate of an index below the total sum is smaller than the entry at its row coordinate. -/
theorem columnIndex_lt_rowLength (parts : List ℕ) (j : ℕ) (hj : j < parts.sum) :
    flatIndexColumn parts j < parts[flatIndexRow parts j]'(rowIndex_lt_length parts j hj) := by
  have h := flatIndexColumn_lt_rowLength parts j hj
  simp [List.getD] at h
  rw [List.getElem?_eq_getElem (rowIndex_lt_length parts j hj)] at h
  simpa using h


private theorem colOfPos_lt_headD (parts : List ℕ) (j : ℕ) (hj : j < parts.sum)
    (hSorted : parts.Pairwise (· ≥ ·)) :
    flatIndexColumn parts j < parts.headD 0 := by
  induction parts generalizing j with
  | nil => simp at hj
  | cons p ps ih =>
    simp only [List.headD, flatIndexColumn]
    split_ifs with h
    · exact h
    · have hj' : j - p < ps.sum := by simp [List.sum_cons] at hj; omega
      have hps_sorted := List.Pairwise.tail hSorted
      calc flatIndexColumn ps (j - p) < ps.headD 0 := ih (j - p) hj' hps_sorted
      _ ≤ p := by
        cases ps with
        | nil => simp [List.headD]
        | cons q qs =>
          simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some]
          exact (List.pairwise_cons.mp hSorted).1 q (by simp)


private def colHeight (parts : List ℕ) (c : ℕ) : ℕ := (parts.filter (· > c)).length

private theorem colHeight_eq_zero_of_ge_headD (parts : List ℕ) (c : ℕ)
    (hSorted : parts.Pairwise (· ≥ ·)) (hc : parts.headD 0 ≤ c) :
    colHeight parts c = 0 := by
  simp only [colHeight]; apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro x hx; simp only [decide_eq_true_eq, not_lt]
  cases parts with
  | nil => simp at hx
  | cons p ps =>
    simp [List.headD] at hc
    rcases List.mem_cons.mp hx with rfl | hm
    · omega
    · exact le_trans (List.rel_of_pairwise_cons hSorted hm) hc

private theorem colHeight_cons_gt {p : ℕ} {ps : List ℕ} {c : ℕ} (h : c < p) :
    colHeight (p :: ps) c = 1 + colHeight ps c := by
  simp [colHeight, List.filter, show p > c from h]; omega


private theorem row_lt_colHeight_of_gt (parts : List ℕ) (r c : ℕ)
    (hSorted : parts.Pairwise (· ≥ ·))
    (hr : r < parts.length) (hgt : parts[r] > c) :
    r < colHeight parts c := by
  induction parts generalizing r with
  | nil => simp at hr
  | cons p ps ih =>
    have hps_sorted : ps.Pairwise (· ≥ ·) := List.Pairwise.tail hSorted
    have hp_gt : p > c := by
      cases r with
      | zero => simpa using hgt
      | succ r' =>
        simp only [List.length_cons] at hr; simp only [List.getElem_cons_succ] at hgt
        exact lt_of_lt_of_le hgt
          (List.rel_of_pairwise_cons hSorted (List.getElem_mem (by omega)))
    simp only [colHeight, List.filter, show decide (p > c) = true from by simp [hp_gt],
      List.length_cons]
    cases r with
    | zero => omega
    | succ r' =>
      simp only [List.length_cons] at hr; simp only [List.getElem_cons_succ] at hgt
      exact Nat.succ_lt_succ (ih r' hps_sorted (by omega) hgt)


private theorem sum_min_colHeight (parts : List ℕ) (k : ℕ)
    (hSorted : parts.Pairwise (· ≥ ·)) :
    ∑ c ∈ Finset.range (parts.headD 0),
      min k (colHeight parts c) = (parts.take k).sum := by
  induction parts generalizing k with
  | nil => simp [colHeight]
  | cons p ps ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.headD, List.take_succ_cons, List.sum_cons]
      have hstep : ∀ c ∈ Finset.range p, min (k + 1) (colHeight (p :: ps) c) =
          1 + min k (colHeight ps c) := by
        intro c hc; rw [Finset.mem_range] at hc; rw [colHeight_cons_gt hc]; omega
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, smul_eq_mul, mul_one]
      have hps_sorted : ps.Pairwise (· ≥ ·) := List.Pairwise.tail hSorted
      rw [← ih k hps_sorted]; congr 1
      have hle : ps.headD 0 ≤ p := by
        cases ps with
        | nil => simp [List.headD]
        | cons q qs =>
          simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some]; exact (List.pairwise_cons.mp hSorted).1 q (by simp)
      rw [← Finset.sum_sdiff (Finset.range_mono hle)]
      suffices h : ∑ c ∈ Finset.range p \ Finset.range (ps.headD 0),
          min k (colHeight ps c) = 0 by omega
      apply Finset.sum_eq_zero
      intro c hc
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hc
      rw [colHeight_eq_zero_of_ge_headD ps c hps_sorted (by omega)]; simp


/-- For `m ≤ n`, exactly `m` elements of `Fin n` have value less than `m`. -/
theorem Fin.card_filter_val_lt (n m : ℕ) (hm : m ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m)).card = m := by
  have hs_eq : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < m) =
      Finset.image (fun j : Fin m => (⟨j.val, by omega⟩ : Fin n)) Finset.univ := by
    ext ⟨i, hi⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Fin.exists_iff]
    constructor
    · intro h; exact ⟨i, by omega, by simp⟩
    · rintro ⟨j, hj, heq⟩; simp at heq; omega
  rw [hs_eq, Finset.card_image_of_injective _ (fun a b h => by ext; simp at h; exact h),
    Finset.card_fin]


private theorem card_first_k_rows (la : Nat.Partition n) (k : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter (fun i =>
      flatIndexRow (auxiliaryPartitionNatList la) i.val < k)).card =
    ((auxiliaryPartitionNatList la).take k).sum := by
  have hconv : (Finset.univ : Finset (Fin n)).filter (fun i =>
      flatIndexRow (auxiliaryPartitionNatList la) i.val < k) =
    (Finset.univ : Finset (Fin n)).filter (fun i =>
      i.val < ((auxiliaryPartitionNatList la).take k).sum) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact rowIndex_lt_iff_lt_sum_take (auxiliaryPartitionNatList la) i.val k (by rw [sortedParts_sum]; exact i.isLt)
  rw [hconv]
  exact Fin.card_filter_val_lt n _ (by
    have h1 : ((auxiliaryPartitionNatList la).take k).sum ≤ (auxiliaryPartitionNatList la).sum :=
      List.Sublist.sum_le_sum (List.take_sublist k (auxiliaryPartitionNatList la)) (fun _ _ => Nat.zero_le _)
    have h2 := sortedParts_sum la
    omega)


private theorem list_eq_of_take_sum_eq {l₁ l₂ : List ℕ}
    (hpos₁ : ∀ x ∈ l₁, 0 < x) (hpos₂ : ∀ x ∈ l₂, 0 < x)
    (h : ∀ k, (l₁.take k).sum = (l₂.take k).sum) : l₁ = l₂ := by
  have hlen : l₁.length = l₂.length := by
    by_contra hne
    wlog hlt : l₁.length < l₂.length with H
    · exact H hpos₂ hpos₁ (fun k => (h k).symm) (by omega) (by omega)
    have hstep := h (l₁.length + 1)
    rw [List.take_of_length_le (by omega : l₁.length ≤ l₁.length + 1)] at hstep
    rw [List.take_succ_eq_append_getElem hlt] at hstep
    simp only [List.sum_append, List.sum_cons, List.sum_nil] at hstep
    have hk := h l₁.length
    rw [List.take_length] at hk
    have := hpos₂ l₂[l₁.length] (List.getElem_mem (by omega))
    omega
  apply List.ext_getElem hlen
  intro i h₁ h₂
  have hk := h (i + 1); have hk' := h i
  rw [List.take_succ_eq_append_getElem h₁, List.sum_append, List.sum_cons, List.sum_nil] at hk
  rw [List.take_succ_eq_append_getElem h₂, List.sum_append, List.sum_cons, List.sum_nil] at hk
  omega


private theorem partition_eq_of_partial_sums (la mu : Nat.Partition n)
    (h : ∀ k, ((auxiliaryPartitionNatList la).take k).sum = ((auxiliaryPartitionNatList mu).take k).sum) :
    la = mu := by
  apply Nat.Partition.ext
  have h1 : ((auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts := la.parts.sort_eq (· ≥ ·)
  have h2 : ((auxiliaryPartitionNatList mu) : Multiset ℕ) = mu.parts := mu.parts.sort_eq (· ≥ ·)
  rw [← h1, ← h2]
  exact congrArg _ (list_eq_of_take_sum_eq (Partition.zero_lt_of_mem_sortedParts la)
    (Partition.zero_lt_of_mem_sortedParts mu) h)



/-- The swap of two positions with equal row coordinates is a member of the associated set. -/
theorem swap_mem_of_row_eq {n : ℕ} {la : Nat.Partition n}
    {i j : Fin n} (hrow : flatIndexRow (auxiliaryPartitionNatList la) i.val = flatIndexRow (auxiliaryPartitionNatList la) j.val) :
    Equiv.swap i j ∈ auxiliaryPartitionPermutationSubgroupB n la := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact hrow.symm
  · subst h2; exact hrow
  · rfl


/-- The swap of two positions with equal column coordinates is a member of the associated set. -/
theorem swap_mem_of_column_eq {n : ℕ} {mu : Nat.Partition n}
    {i j : Fin n} (hcol : flatIndexColumn (auxiliaryPartitionNatList mu) i.val = flatIndexColumn (auxiliaryPartitionNatList mu) j.val) :
    Equiv.swap i j ∈ auxiliaryPartitionPermutationSubgroupA n mu := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact hcol.symm
  · subst h2; exact hcol
  · rfl


private theorem conj_swap_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    σ⁻¹ * Equiv.swap i j * σ = Equiv.swap (σ⁻¹ i) (σ⁻¹ j) := by
  ext k
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  by_cases hki : k = σ.symm i
  · subst hki
    simp [Equiv.swap_apply_left, Equiv.apply_symm_apply]
  · by_cases hkj : k = σ.symm j
    · subst hkj
      simp [Equiv.swap_apply_right, Equiv.apply_symm_apply]
    · have hσki : σ k ≠ i := fun h => hki (by rw [← h]; simp)
      have hσkj : σ k ≠ j := fun h => hkj (by rw [← h]; simp)
      simp [Equiv.swap_apply_of_ne_of_ne hσki hσkj,
            Equiv.swap_apply_of_ne_of_ne hki hkj]



private theorem counting_gives_dominates (n : ℕ) (la mu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n))
    (h_no : ∀ i j : Fin n, i ≠ j →
      flatIndexRow (auxiliaryPartitionNatList la) i.val = flatIndexRow (auxiliaryPartitionNatList la) j.val →
      flatIndexColumn (auxiliaryPartitionNatList mu) (σ⁻¹ i).val ≠ flatIndexColumn (auxiliaryPartitionNatList mu) (σ⁻¹ j).val) :
    Partition.Dominates mu la := by
  intro k
  rw [← sum_min_colHeight (auxiliaryPartitionNatList mu) k
    (Partition.sortedParts_pairwise_ge mu)]
  rw [← card_first_k_rows la k]
  set g := fun (i : Fin n) => flatIndexColumn (auxiliaryPartitionNatList mu) (σ⁻¹ i).val
  set S_k := (Finset.univ : Finset (Fin n)).filter (fun i =>
    flatIndexRow (auxiliaryPartitionNatList la) i.val < k)
  set T := Finset.range ((auxiliaryPartitionNatList mu).headD 0)
  have hmaps : Set.MapsTo g ↑S_k ↑T := fun i hi => by
    rw [Finset.mem_coe, Finset.mem_filter] at hi; rw [Finset.mem_coe, Finset.mem_range]
    exact colOfPos_lt_headD (auxiliaryPartitionNatList mu) _ (by rw [sortedParts_sum]; exact (σ⁻¹ i).isLt)
      (Partition.sortedParts_pairwise_ge mu)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_le_sum; intro c _
  have hfilt_eq : S_k.filter (fun i => g i = c) =
      Finset.univ.filter (fun i : Fin n =>
        flatIndexRow (auxiliaryPartitionNatList la) i.val < k ∧
        flatIndexColumn (auxiliaryPartitionNatList mu) (σ⁻¹ i).val = c) := by
    ext i; simp [S_k, g, Finset.mem_filter]
  rw [hfilt_eq]
  set F := Finset.univ.filter (fun i : Fin n =>
    flatIndexRow (auxiliaryPartitionNatList la) i.val < k ∧
    flatIndexColumn (auxiliaryPartitionNatList mu) (σ⁻¹ i).val = c)
  apply Nat.le_min.mpr; constructor
  · have hmaps1 : Set.MapsTo (fun i : Fin n => flatIndexRow (auxiliaryPartitionNatList la) i.val)
        ↑F ↑(Finset.range k) := by
      intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      exact Finset.mem_range.mpr hi.2.1
    have hinj1 : Set.InjOn (fun i : Fin n => flatIndexRow (auxiliaryPartitionNatList la) i.val) ↑F := by
      intro i hi j hj heq
      rw [Finset.mem_coe, Finset.mem_filter] at hi hj
      by_contra hne; exact h_no i j hne heq (by rw [hi.2.2, hj.2.2])
    have h1 := Finset.card_le_card_of_injOn _ hmaps1 hinj1
    rw [Finset.card_range] at h1; exact h1
  · have hmaps2 : Set.MapsTo (fun i : Fin n => flatIndexRow (auxiliaryPartitionNatList mu) (σ⁻¹ i).val)
        ↑F ↑(Finset.range (colHeight (auxiliaryPartitionNatList mu) c)) := by
      intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      rw [Finset.mem_coe, Finset.mem_range]
      have hv : (σ⁻¹ i).val < (auxiliaryPartitionNatList mu).sum := by rw [sortedParts_sum]; exact (σ⁻¹ i).isLt
      have hrow := rowIndex_lt_length (auxiliaryPartitionNatList mu) _ hv
      have hcol := columnIndex_lt_rowLength (auxiliaryPartitionNatList mu) _ hv
      rw [hi.2.2] at hcol
      exact row_lt_colHeight_of_gt (auxiliaryPartitionNatList mu) _ c
        (Partition.sortedParts_pairwise_ge mu) hrow (by omega)
    have hinj2 : Set.InjOn (fun i : Fin n => flatIndexRow (auxiliaryPartitionNatList mu) (σ⁻¹ i).val) ↑F := by
      intro i hi j hj heq
      rw [Finset.mem_coe, Finset.mem_filter] at hi hj
      have hcol_eq : flatIndexColumn (auxiliaryPartitionNatList mu) (σ⁻¹ i).val =
          flatIndexColumn (auxiliaryPartitionNatList mu) (σ⁻¹ j).val := by rw [hi.2.2, hj.2.2]
      have hval_eq := eq_of_flatIndexRow_eq_and_column_eq (auxiliaryPartitionNatList mu) _ _
        (by rw [sortedParts_sum]; exact (σ⁻¹ i).isLt)
        (by rw [sortedParts_sum]; exact (σ⁻¹ j).isLt) heq hcol_eq
      exact σ.symm.injective (Fin.ext hval_eq)
    have h2 := Finset.card_le_card_of_injOn _ hmaps2 hinj2
    rw [Finset.card_range] at h2; exact h2

/-- An auxiliary theorem involving the strict dominance relation; its formal statement could not be displayed in this packet. -/
theorem strictDominates_aux (n : ℕ) (la mu : Nat.Partition n)
    (hdom : Partition.StrictDominates la mu) (σ : Equiv.Perm (Fin n)) :
    ∃ (t : Equiv.Perm (Fin n)),
      t ∈ auxiliaryPartitionPermutationSubgroupB n la ∧ σ⁻¹ * t * σ ∈ auxiliaryPartitionPermutationSubgroupA n mu ∧
      Equiv.Perm.sign t = -1 := by
  suffices ∃ i j : Fin n, i ≠ j ∧
      flatIndexRow (auxiliaryPartitionNatList la) i.val = flatIndexRow (auxiliaryPartitionNatList la) j.val ∧
      flatIndexColumn (auxiliaryPartitionNatList mu) (σ⁻¹ i).val = flatIndexColumn (auxiliaryPartitionNatList mu) (σ⁻¹ j).val by
    obtain ⟨i, j, hij, hrow, hcol⟩ := this
    exact ⟨Equiv.swap i j, swap_mem_of_row_eq hrow,
      conj_swap_eq σ i j ▸ swap_mem_of_column_eq hcol, Equiv.Perm.sign_swap hij⟩
  by_contra h_no
  push Not at h_no
  exact hdom.2 (partition_eq_of_partial_sums la mu (fun k =>
    le_antisymm ((counting_gives_dominates n la mu σ h_no) k) (hdom.1 k)))


/-- Under strict dominance, inserting the group-algebra basis element of any permutation between the two partition-indexed elements yields zero. -/
theorem sandwich_single_eq_zero_of_strictDominates (n : ℕ) (la mu : Nat.Partition n)
    (hdom : Partition.StrictDominates la mu)
    (σ : Equiv.Perm (Fin n)) :
    auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ *
      auxiliaryPartitionGroupAlgebraElementA n mu = 0 := by
  obtain ⟨t, ht_row, hconj_col, ht_sign⟩ := strictDominates_aux n la mu hdom σ

  let of' := MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))
  set a := auxiliaryPartitionGroupAlgebraElementB n la
  set b := auxiliaryPartitionGroupAlgebraElementA n mu
  set val := a * of' σ * b

  have hconj_sign : (↑(↑(Equiv.Perm.sign (σ⁻¹ * t * σ)) : ℤ) : ℂ) = -1 := by
    simp [Equiv.Perm.sign_mul, ht_sign]

  have hab : a * of' t = a := mul_perm_eq_self_of_mem t ht_row

  have hcol := perm_mul_eq_sign_smul_of_mem (σ⁻¹ * t * σ) hconj_col








  have hval_neg : val = (-1 : ℂ) • val := by
    have step : a * of' σ = a * of' σ * of' (σ⁻¹ * t * σ) := by
      conv_lhs => rw [show a = a * of' t from hab.symm]
      rw [mul_assoc a (of' t) (of' σ), ← map_mul of' t σ,
          show t * σ = σ * (σ⁻¹ * t * σ) from by group,
          map_mul of' σ (σ⁻¹ * t * σ), ← mul_assoc]
    change a * of' σ * b = (-1 : ℂ) • (a * of' σ * b)
    conv_lhs => rw [step, mul_assoc (a * of' σ) (of' (σ⁻¹ * t * σ)) b, hcol]
    rw [mul_smul_comm, hconj_sign]

  rw [neg_one_smul] at hval_neg
  have hadd : val + val = 0 := by nth_rw 1 [hval_neg]; exact neg_add_cancel val
  have h2 : (2 : ℂ) • val = 0 := by rwa [two_smul]
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)



/-- If one partition strictly dominates another, their associated group-algebra elements give zero when placed on either side of any group-algebra element. -/
@[source_ref "Chapter5/Introduction_5.13" (role := supporting),
  source_ref "Chapter5/Lemma5.13.2" (role := primary)]
theorem sandwich_eq_zero_of_strictDominates
    (n : ℕ) (la mu : Nat.Partition n)
    (hdom : Partition.StrictDominates la mu)
    (x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    auxiliaryPartitionGroupAlgebraElementB n la * x * auxiliaryPartitionGroupAlgebraElementA n mu = 0 := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
    have hleft : auxiliaryPartitionGroupAlgebraElementB n la *
        (0 : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) * auxiliaryPartitionGroupAlgebraElementA n mu = 0 := by
      simp
    exact hleft
  | add x y hx hy =>
    let x' : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) := x
    let y' : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) := y
    change auxiliaryPartitionGroupAlgebraElementB n la * (x' + y') * auxiliaryPartitionGroupAlgebraElementA n mu = 0
    rw [mul_add, add_mul, hx, hy, add_zero]
  | single g c =>
    have h : MonoidAlgebra.single g c =
        c • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g := by
      ext h
      simp [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [h, mul_smul_comm, smul_mul_assoc, sandwich_single_eq_zero_of_strictDominates n la mu hdom g, smul_zero]





/-- An auxiliary theorem involving the dominance relation; its formal statement could not be displayed in this packet. -/
@[source_ref "Chapter5/Lemma5.13.2" (role := supporting)]
theorem dominates_aux (n : ℕ) (la mu : Nat.Partition n)
    (h : ¬ Partition.Dominates mu la) (σ : Equiv.Perm (Fin n)) :
    ∃ (t : Equiv.Perm (Fin n)),
      t ∈ auxiliaryPartitionPermutationSubgroupB n la ∧ σ⁻¹ * t * σ ∈ auxiliaryPartitionPermutationSubgroupA n mu ∧
      Equiv.Perm.sign t = -1 := by
  suffices ∃ i j : Fin n, i ≠ j ∧
      flatIndexRow (auxiliaryPartitionNatList la) i.val = flatIndexRow (auxiliaryPartitionNatList la) j.val ∧
      flatIndexColumn (auxiliaryPartitionNatList mu) (σ⁻¹ i).val = flatIndexColumn (auxiliaryPartitionNatList mu) (σ⁻¹ j).val by
    obtain ⟨i, j, hij, hrow, hcol⟩ := this
    exact ⟨Equiv.swap i j, swap_mem_of_row_eq hrow,
      conj_swap_eq σ i j ▸ swap_mem_of_column_eq hcol, Equiv.Perm.sign_swap hij⟩
  by_contra h_no
  push Not at h_no
  exact h (counting_gives_dominates n la mu σ h_no)



/-- If `mu` does not dominate `la`, inserting the group-algebra basis element of any permutation between their associated elements yields zero. -/
@[source_ref "Chapter5/Lemma5.13.2" (role := supporting)]
theorem sandwich_single_eq_zero_of_not_dominates (n : ℕ) (la mu : Nat.Partition n)
    (h : ¬ Partition.Dominates mu la)
    (σ : Equiv.Perm (Fin n)) :
    auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ *
      auxiliaryPartitionGroupAlgebraElementA n mu = 0 := by
  obtain ⟨t, ht_row, hconj_col, ht_sign⟩ := dominates_aux n la mu h σ
  let of' := MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))
  set a := auxiliaryPartitionGroupAlgebraElementB n la
  set b := auxiliaryPartitionGroupAlgebraElementA n mu
  set val := a * of' σ * b
  have hconj_sign : (↑(↑(Equiv.Perm.sign (σ⁻¹ * t * σ)) : ℤ) : ℂ) = -1 := by
    simp [Equiv.Perm.sign_mul, ht_sign]
  have hab : a * of' t = a := mul_perm_eq_self_of_mem t ht_row
  have hcol := perm_mul_eq_sign_smul_of_mem (σ⁻¹ * t * σ) hconj_col
  have hval_neg : val = (-1 : ℂ) • val := by
    have step : a * of' σ = a * of' σ * of' (σ⁻¹ * t * σ) := by
      conv_lhs => rw [show a = a * of' t from hab.symm]
      rw [mul_assoc a (of' t) (of' σ), ← map_mul of' t σ,
          show t * σ = σ * (σ⁻¹ * t * σ) from by group,
          map_mul of' σ (σ⁻¹ * t * σ), ← mul_assoc]
    change a * of' σ * b = (-1 : ℂ) • (a * of' σ * b)
    conv_lhs => rw [step, mul_assoc (a * of' σ) (of' (σ⁻¹ * t * σ)) b, hcol]
    rw [mul_smul_comm, hconj_sign]
  rw [neg_one_smul] at hval_neg
  have hadd : val + val = 0 := by nth_rw 1 [hval_neg]; exact neg_add_cancel val
  have h2 : (2 : ℂ) • val = 0 := by rwa [two_smul]
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)




/-- If `mu` does not dominate `la`, the elements associated with `la` and `mu` give zero when placed on either side of any group-algebra element. -/
@[source_ref "Chapter5/Lemma5.13.2" (role := primary)]
theorem sandwich_eq_zero_of_not_dominates
    (n : ℕ) (la mu : Nat.Partition n)
    (h : ¬ Partition.Dominates mu la)
    (x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    auxiliaryPartitionGroupAlgebraElementB n la * x * auxiliaryPartitionGroupAlgebraElementA n mu = 0 := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
    have hleft : auxiliaryPartitionGroupAlgebraElementB n la *
        (0 : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) * auxiliaryPartitionGroupAlgebraElementA n mu = 0 := by
      simp
    exact hleft
  | add x y hx hy =>
    let x' : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) := x
    let y' : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) := y
    change auxiliaryPartitionGroupAlgebraElementB n la * (x' + y') * auxiliaryPartitionGroupAlgebraElementA n mu = 0
    rw [mul_add, add_mul, hx, hy, add_zero]
  | single g c =>
    have hsg : MonoidAlgebra.single g c =
        c • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g := by
      ext h
      simp [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [hsg, mul_smul_comm, smul_mul_assoc,
      sandwich_single_eq_zero_of_not_dominates n la mu h g, smul_zero]



/-- If `mu` is lexicographically smaller than `la`, the elements associated with `la` and `mu` give zero when placed on either side of any group-algebra element. -/
@[source_ref "Chapter5/Lemma5.13.2" (role := primary)]
theorem sandwich_eq_zero_of_lexLt
    (n : ℕ) (la mu : Nat.Partition n)
    (h : Partition.LexLt mu la)
    (x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    auxiliaryPartitionGroupAlgebraElementB n la * x * auxiliaryPartitionGroupAlgebraElementA n mu = 0 :=
  sandwich_eq_zero_of_not_dominates n la mu (Partition.LexLt.not_dominates h) x




/-- Two partitions that dominate each other are equal. -/
theorem Partition.Dominates.antisymm {n : ℕ} {la mu : Nat.Partition n}
    (h1 : Partition.Dominates la mu) (h2 : Partition.Dominates mu la) : la = mu :=
  partition_eq_of_partial_sums la mu (fun k => le_antisymm (h2 k) (h1 k))

end RepresentationTheory.SymmetricGroup.PartitionDominance
