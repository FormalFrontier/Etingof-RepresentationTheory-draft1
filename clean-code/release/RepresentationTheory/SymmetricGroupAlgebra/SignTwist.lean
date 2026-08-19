/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
import RepresentationTheory.PartitionAuxiliary
import RepresentationTheory.YoungDiagram.PartitionConstructions
import RepresentationTheory.SymmetricGroup.PartitionSubmodules
import RepresentationTheory.Alignment.Attribute

/-!
# Sign twist
-/



namespace RepresentationTheory.SymmetricGroupAlgebra.SignTwist

open scoped Classical



private theorem sum_list_range_map (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp



private theorem rowLens_sum_eq_card (μ : YoungDiagram) : μ.rowLens.sum = μ.card := by
  rw [YoungDiagram.rowLens, sum_list_range_map]
  change _ = μ.cells.card
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.range (μ.colLen 0)) ?_]
  · apply Finset.sum_congr rfl
    intro i _
    exact YoungDiagram.rowLen_eq_card μ
  · intro c hc
    obtain ⟨i, j⟩ := c
    rw [Finset.mem_coe, Finset.mem_range]
    rw [Finset.mem_coe, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen] at hc
    exact lt_of_lt_of_le hc (μ.colLen_anti 0 j (Nat.zero_le _))


private theorem card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  change μ.transpose.cells.card = μ.cells.card
  rw [YoungDiagram.transpose]
  simp [Equiv.finsetCongr_apply]


private theorem card_toYoungDiagram {n : ℕ} (la : Nat.Partition n) :
    (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).card = n := by
  rw [← rowLens_sum_eq_card, RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition,
    YoungDiagram.rowLens_ofRowLens_eq_self (fun x hx => la.parts_pos (by
      rw [Multiset.mem_sort] at hx; exact hx))]
  rw [← Multiset.sum_coe, Multiset.sort_eq]
  exact la.parts_sum



/-- A self-map of the partitions of a natural number. -/
@[source_ref "Chapter5/Problem5.24.1" (role := supporting)]
noncomputable def Partition.selfMap {n : ℕ} (la : Nat.Partition n) : Nat.Partition n where
  parts := ((RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).transpose.rowLens : Multiset ℕ)
  parts_pos := by
    intro i hi
    rw [Multiset.mem_coe] at hi
    exact (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).transpose.pos_of_mem_rowLens i hi
  parts_sum := by


    rw [Multiset.sum_coe, rowLens_sum_eq_card, card_transpose, card_toYoungDiagram]



/-- A monoid homomorphism from finite permutations to the indicated complex algebra. -/
noncomputable def permutationMonoidHom (n : ℕ) :
    Equiv.Perm (Fin n) →* RepresentationTheory.PartitionAuxiliary.natIndexedType n where
  toFun g := ((Equiv.Perm.sign g : ℤ) : ℂ) • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g
  map_one' := by
    simp only [Units.val_one, Int.cast_one, one_smul, map_one]
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, Int.cast_mul, smul_mul_smul_comm]



/-- The complex-algebra endomorphism that twists permutation monomials by their signs. -/
@[source_ref "Chapter5/Problem5.24.1" (role := supporting)]
noncomputable def signTwistAlgHom (n : ℕ) : RepresentationTheory.PartitionAuxiliary.natIndexedType n →ₐ[ℂ] RepresentationTheory.PartitionAuxiliary.natIndexedType n :=
  MonoidAlgebra.lift ℂ (RepresentationTheory.PartitionAuxiliary.natIndexedType n) (Equiv.Perm (Fin n)) (permutationMonoidHom n)


/-- On a permutation monomial, the sign twist multiplies that monomial by the sign of the permutation. -/
@[source_ref "Chapter5/Problem5.24.1" (role := supporting)]
theorem signTwistAlgHom_apply_of (n : ℕ) (g : Equiv.Perm (Fin n)) :
    signTwistAlgHom n (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g)
      = ((Equiv.Perm.sign g : ℤ) : ℂ) • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g := by
  rw [signTwistAlgHom, MonoidAlgebra.lift_of]
  rfl



/-- The sign-twisting algebra endomorphism is bijective. -/
@[source_ref "Chapter5/Problem5.24.1" (role := supporting)]
theorem signTwistAlgHom_bijective (n : ℕ) : Function.Bijective (signTwistAlgHom n) := by
  have hcomp : (signTwistAlgHom n).comp (signTwistAlgHom n) = AlgHom.id ℂ (RepresentationTheory.PartitionAuxiliary.natIndexedType n) := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      have hsq : ((Equiv.Perm.sign g : ℤ) : ℂ) * ((Equiv.Perm.sign g : ℤ) : ℂ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
      change signTwistAlgHom n (signTwistAlgHom n (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g))
          = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g
      rw [signTwistAlgHom_apply_of, map_smul, signTwistAlgHom_apply_of, smul_smul, hsq, one_smul]
    · ext
  have hinv : Function.Involutive (signTwistAlgHom n) := fun a => by
    have := DFunLike.congr_fun hcomp a
    simpa using this
  exact hinv.bijective



/-- The action of a sign-twisted permutation monomial is its original action scaled by the permutation sign. -/
@[source_ref "Chapter5/Problem5.24.1" (role := supporting)]
theorem signTwistAlgHom_apply_of_smul (n : ℕ) {V : Type*} [AddCommGroup V]
    [Module ℂ V] [Module (RepresentationTheory.PartitionAuxiliary.natIndexedType n) V] [IsScalarTower ℂ (RepresentationTheory.PartitionAuxiliary.natIndexedType n) V]
    (g : Equiv.Perm (Fin n)) (v : V) :
    (signTwistAlgHom n (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g)) • v
      = ((Equiv.Perm.sign g : ℤ) : ℂ) • ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) • v) := by
  rw [signTwistAlgHom_apply_of, smul_assoc]



/-- The image under the sign twist of the ideal generated by one element is the ideal generated by its image. -/
@[source_ref "Chapter5/Problem5.24.1" (role := supporting)]
theorem signTwistAlgHom_map_span_singleton (n : ℕ) (a : RepresentationTheory.PartitionAuxiliary.natIndexedType n) :
    Ideal.map (signTwistAlgHom n) (Ideal.span {a})
      = Ideal.span {signTwistAlgHom n a} := by
  rw [Ideal.map_span, Set.image_singleton]



/-- The sign twist sends the indicated partition-indexed element to a sign-weighted sum over all finite permutations. -/
theorem signTwistAlgHom_apply_partitionIndexedElement_eq_signWeightedSum (n : ℕ) (la : Nat.Partition n) :
    haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) := Classical.decPred _
    signTwistAlgHom n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la)
      = ∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la),
          ((Equiv.Perm.sign g.val : ℤ) : ℂ) • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g.val := by
  classical
  rw [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB, map_sum]
  exact Finset.sum_congr rfl (fun g _ => signTwistAlgHom_apply_of n g.val)



/-- The sign twist sends the indicated partition-indexed element to a sum over all finite permutations. -/
theorem signTwistAlgHom_apply_partitionIndexedElement_eq_sum (n : ℕ) (la : Nat.Partition n) :
    haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) := Classical.decPred _
    signTwistAlgHom n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)
      = ∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la), MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g.val := by
  classical
  rw [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA, map_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [map_smul, signTwistAlgHom_apply_of, smul_smul]
  have hsq : ((Equiv.Perm.sign g.val : ℤ) : ℂ) * ((Equiv.Perm.sign g.val : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [hsq, one_smul]



private theorem lt_getD_iff (w : List ℕ) (r c : ℕ) :
    (∃ h : r < w.length, c < w[r]) ↔ c < w.getD r 0 := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge r w.length with hr | hr
  · rw [List.getElem?_eq_getElem hr, Option.getD_some]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hr, h⟩⟩
  · rw [List.getElem?_eq_none hr, Option.getD_none]
    exact ⟨fun ⟨h, _⟩ => absurd h (not_lt.mpr hr), fun h => absurd h (Nat.not_lt_zero c)⟩



private theorem mem_toYoungDiagram_iff {n : ℕ} (la : Nat.Partition n) (r c : ℕ) :
    (r, c) ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la) ↔ c < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD r 0 := by
  rw [RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition, YoungDiagram.mem_ofRowLens]
  exact lt_getD_iff _ r c



private theorem ofRowLens_congr {w1 w2 : List ℕ} (h : w1 = w2)
    (h1 : w1.SortedGE) (h2 : w2.SortedGE) :
    YoungDiagram.ofRowLens w1 h1 = YoungDiagram.ofRowLens w2 h2 := by
  subst h; rfl



private theorem conjugate_toYoungDiagram {n : ℕ} (la : Nat.Partition n) :
    (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (Partition.selfMap la)) = (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).transpose := by
  have hlist : (Partition.selfMap la).parts.sort (· ≥ ·)
      = (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).transpose.rowLens := by
    change (↑((RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).transpose.rowLens) : Multiset ℕ).sort (· ≥ ·) = _
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self (r := (· ≥ ·))
      (List.sortedGE_iff_pairwise.mp (YoungDiagram.rowLens_sorted _))
  conv_rhs => rw [← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).transpose)]
  rw [RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition]
  exact ofRowLens_congr hlist _ _



private theorem transpose_cell_iff {n : ℕ} (la : Nat.Partition n) (r c : ℕ) :
    c < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)).getD r 0 ↔ r < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD c 0 := by
  rw [← mem_toYoungDiagram_iff, conjugate_toYoungDiagram, YoungDiagram.mem_transpose,
    Prod.swap_prod_mk, mem_toYoungDiagram_iff]



private theorem sortedParts_sum {n : ℕ} (la : Nat.Partition n) : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = n := by
  rw [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList, ← Multiset.sum_coe, Multiset.sort_eq]
  exact la.parts_sum


private theorem transpose_cell_exists {n : ℕ} (la : Nat.Partition n) (k : Fin n) :
    ∃ m : Fin n,
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) m.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val
        ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) m.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val := by
  have hk : k.val < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by rw [sortedParts_sum]; exact k.isLt
  have hcell : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val
      < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)).getD (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val) 0 := by
    rw [transpose_cell_iff]; exact RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val hk
  obtain ⟨m, hm_lt, hrow, hcol⟩ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la))
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val) (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val) hcell
  rw [sortedParts_sum] at hm_lt
  exact ⟨⟨m, hm_lt⟩, hrow, hcol⟩


private noncomputable def transposePosFun {n : ℕ} (la : Nat.Partition n) (k : Fin n) : Fin n :=
  (transpose_cell_exists la k).choose

private theorem transposePosFun_row {n : ℕ} (la : Nat.Partition n) (k : Fin n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) (transposePosFun la k).val
      = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val :=
  (transpose_cell_exists la k).choose_spec.1

private theorem transposePosFun_col {n : ℕ} (la : Nat.Partition n) (k : Fin n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) (transposePosFun la k).val
      = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val :=
  (transpose_cell_exists la k).choose_spec.2

private theorem transposePosFun_injective {n : ℕ} (la : Nat.Partition n) :
    Function.Injective (transposePosFun la) := by
  intro k1 k2 h
  have hrow := transposePosFun_row la k1
  have hrow2 := transposePosFun_row la k2
  have hcol := transposePosFun_col la k1
  have hcol2 := transposePosFun_col la k2
  rw [h] at hrow hcol
  have hc : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k1.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k2.val := hrow.symm.trans hrow2
  have hr : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k1.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k2.val := hcol.symm.trans hcol2
  apply Fin.ext
  exact RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k1.val k2.val
    (by rw [sortedParts_sum]; exact k1.isLt) (by rw [sortedParts_sum]; exact k2.isLt) hr hc


private noncomputable def transposePerm {n : ℕ} (la : Nat.Partition n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (transposePosFun la)
    (Finite.injective_iff_bijective.mp (transposePosFun_injective la))

private theorem transposePerm_row {n : ℕ} (la : Nat.Partition n) (x : Fin n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) ((transposePerm la) x).val
      = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) x.val := by
  rw [transposePerm, Equiv.ofBijective_apply]; exact transposePosFun_row la x

private theorem transposePerm_col {n : ℕ} (la : Nat.Partition n) (x : Fin n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) ((transposePerm la) x).val
      = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) x.val := by
  rw [transposePerm, Equiv.ofBijective_apply]; exact transposePosFun_col la x

private theorem mem_rowSubgroup_iff {n : ℕ} (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la
      ↔ ∀ k, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ k).val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val := Iff.rfl

private theorem mem_columnSubgroup_iff {n : ℕ} (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la
      ↔ ∀ k, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ k).val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val := Iff.rfl


private theorem mem_rowSubgroup_conj {n : ℕ} (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n (Partition.selfMap la)
      ↔ (transposePerm la)⁻¹ * σ * transposePerm la ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la := by
  rw [mem_rowSubgroup_iff, mem_columnSubgroup_iff]

  have e1 : ∀ y : Fin n, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) ((transposePerm la)⁻¹ y).val
      = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) y.val := by
    intro y
    have hself : (transposePerm la) ((transposePerm la)⁻¹ y) = y := by simp
    have := transposePerm_row la ((transposePerm la)⁻¹ y)
    rw [hself] at this
    exact this.symm
  have key : ∀ k : Fin n,
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (((transposePerm la)⁻¹ * σ * transposePerm la) k).val
          = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val)
        ↔ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) (σ (transposePerm la k)).val
            = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) (transposePerm la k).val) := by
    intro k
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, e1, ← transposePerm_row la k]
  simp only [key]
  constructor
  · intro h k; exact h (transposePerm la k)
  · intro h m; obtain ⟨k, rfl⟩ := (transposePerm la).surjective m; exact h k


private theorem mem_columnSubgroup_conj {n : ℕ} (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n (Partition.selfMap la)
      ↔ (transposePerm la)⁻¹ * σ * transposePerm la ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la := by
  rw [mem_columnSubgroup_iff, mem_rowSubgroup_iff]
  have e1 : ∀ y : Fin n, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) ((transposePerm la)⁻¹ y).val
      = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) y.val := by
    intro y
    have hself : (transposePerm la) ((transposePerm la)⁻¹ y) = y := by simp
    have := transposePerm_col la ((transposePerm la)⁻¹ y)
    rw [hself] at this
    exact this.symm
  have key : ∀ k : Fin n,
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (((transposePerm la)⁻¹ * σ * transposePerm la) k).val
          = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val)
        ↔ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) (σ (transposePerm la k)).val
            = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (Partition.selfMap la)) (transposePerm la k).val) := by
    intro k
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, e1, ← transposePerm_col la k]
  simp only [key]
  constructor
  · intro h k; exact h (transposePerm la k)
  · intro h m; obtain ⟨k, rfl⟩ := (transposePerm la).surjective m; exact h k



private noncomputable def rowColConjEquiv {n : ℕ} (la : Nat.Partition n) :
    ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n (Partition.selfMap la)) ≃ ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) where
  toFun h := ⟨(transposePerm la)⁻¹ * h.val * transposePerm la,
    (mem_rowSubgroup_conj la h.val).mp h.prop⟩
  invFun g := ⟨transposePerm la * g.val * (transposePerm la)⁻¹, by
    rw [mem_rowSubgroup_conj]
    have h : (transposePerm la)⁻¹ * (transposePerm la * g.val * (transposePerm la)⁻¹)
        * transposePerm la = g.val := by group
    rw [h]; exact g.prop⟩
  left_inv h := by
    apply Subtype.ext
    change transposePerm la * ((transposePerm la)⁻¹ * h.val * transposePerm la)
      * (transposePerm la)⁻¹ = h.val
    group
  right_inv g := by
    apply Subtype.ext
    change (transposePerm la)⁻¹ * (transposePerm la * g.val * (transposePerm la)⁻¹)
      * transposePerm la = g.val
    group



private noncomputable def colRowConjEquiv {n : ℕ} (la : Nat.Partition n) :
    ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n (Partition.selfMap la)) ≃ ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) where
  toFun h := ⟨(transposePerm la)⁻¹ * h.val * transposePerm la,
    (mem_columnSubgroup_conj la h.val).mp h.prop⟩
  invFun g := ⟨transposePerm la * g.val * (transposePerm la)⁻¹, by
    rw [mem_columnSubgroup_conj]
    have h : (transposePerm la)⁻¹ * (transposePerm la * g.val * (transposePerm la)⁻¹)
        * transposePerm la = g.val := by group
    rw [h]; exact g.prop⟩
  left_inv h := by
    apply Subtype.ext
    change transposePerm la * ((transposePerm la)⁻¹ * h.val * transposePerm la)
      * (transposePerm la)⁻¹ = h.val
    group
  right_inv g := by
    apply Subtype.ext
    change (transposePerm la)⁻¹ * (transposePerm la * g.val * (transposePerm la)⁻¹)
      * transposePerm la = g.val
    group


private theorem conj_of_columnSum {n : ℕ} (la : Nat.Partition n) :
    haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) := Classical.decPred _
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)
        * (∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la), MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g.val)
        * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)⁻¹
      = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n (Partition.selfMap la) := by
  classical
  rw [Finset.mul_sum, Finset.sum_mul, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB,
    ← Equiv.sum_comp (rowColConjEquiv la)
      (fun g : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) => MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)
        * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g.val
        * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)⁻¹)]
  apply Finset.sum_congr rfl
  intro h _
  rw [← map_mul, ← map_mul]
  congr 1
  change transposePerm la * ((transposePerm la)⁻¹ * h.val * transposePerm la)
    * (transposePerm la)⁻¹ = h.val
  group


private theorem conj_of_rowSignSum {n : ℕ} (la : Nat.Partition n) :
    haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) := Classical.decPred _
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)
        * (∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la),
            ((Equiv.Perm.sign g.val : ℤ) : ℂ) • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g.val)
        * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)⁻¹
      = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n (Partition.selfMap la) := by
  classical
  rw [Finset.mul_sum, Finset.sum_mul, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA,
    ← Equiv.sum_comp (colRowConjEquiv la)
      (fun g : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) => MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)
        * (((Equiv.Perm.sign g.val : ℤ) : ℂ) • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g.val)
        * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)⁻¹)]
  apply Finset.sum_congr rfl
  intro h _
  have hperm : Equiv.Perm.sign (((colRowConjEquiv la) h).val) = Equiv.Perm.sign h.val := by
    change Equiv.Perm.sign ((transposePerm la)⁻¹ * h.val * transposePerm la)
      = Equiv.Perm.sign h.val
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, mul_right_comm,
      Int.units_mul_self, one_mul]
  have hval : transposePerm la * ((colRowConjEquiv la) h).val * (transposePerm la)⁻¹ = h.val := by
    change transposePerm la * ((transposePerm la)⁻¹ * h.val * transposePerm la)
      * (transposePerm la)⁻¹ = h.val
    group
  rw [mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul, hperm, hval]


private theorem conj_mul {n : ℕ} (τ : Equiv.Perm (Fin n)) (X Y : RepresentationTheory.PartitionAuxiliary.natIndexedType n) :
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ * (X * Y)
        * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹
      = (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ * X
          * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹)
        * (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ * Y
          * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹) := by
  have h1 : MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹
      * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  simp only [mul_assoc]
  rw [← mul_assoc (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹)
    (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ), h1, one_mul]



private theorem key_identity {n : ℕ} (la : Nat.Partition n) :
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)
        * signTwistAlgHom n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la)
        * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)⁻¹
      = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n (Partition.selfMap la) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n (Partition.selfMap la)
        := by
  classical
  rw [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC, map_mul, signTwistAlgHom_apply_partitionIndexedElement_eq_sum, signTwistAlgHom_apply_partitionIndexedElement_eq_signWeightedSum,
    conj_mul, conj_of_columnSum, conj_of_rowSignSum]



private theorem signTwist_span_singleton_maps {n : ℕ} (w z : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
    (hz : z ∈ Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {w}) :
    signTwistAlgHom n z ∈ Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {signTwistAlgHom n w} := by
  rw [Submodule.mem_span_singleton] at hz ⊢
  obtain ⟨r, rfl⟩ := hz
  refine ⟨signTwistAlgHom n r, ?_⟩
  rw [smul_eq_mul, smul_eq_mul, map_mul]


private theorem signTwist_signTwist {n : ℕ} (z : RepresentationTheory.PartitionAuxiliary.natIndexedType n) :
    signTwistAlgHom n (signTwistAlgHom n z) = z := by
  have hcomp : (signTwistAlgHom n).comp (signTwistAlgHom n) = AlgHom.id ℂ (RepresentationTheory.PartitionAuxiliary.natIndexedType n) := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      have hsq : ((Equiv.Perm.sign g : ℤ) : ℂ) * ((Equiv.Perm.sign g : ℤ) : ℂ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
      change signTwistAlgHom n (signTwistAlgHom n (MonoidAlgebra.of ℂ _ g)) = MonoidAlgebra.of ℂ _ g
      rw [signTwistAlgHom_apply_of, map_smul, signTwistAlgHom_apply_of, smul_smul, hsq, one_smul]
    · ext
  simpa using DFunLike.congr_fun hcomp z



private noncomputable def signTwistSpanEquiv {n : ℕ}
    (p q : Submodule (RepresentationTheory.PartitionAuxiliary.natIndexedType n) (RepresentationTheory.PartitionAuxiliary.natIndexedType n)) (w : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
    (hp : p = Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {w})
    (hq : q = Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {signTwistAlgHom n w}) :
    ↥p ≃ₗ[ℂ] ↥q where
  toFun x := ⟨signTwistAlgHom n x.val, by
    rw [hq]; exact signTwist_span_singleton_maps w x.val (by rw [← hp]; exact x.prop)⟩
  map_add' x y := by apply Subtype.ext; simp [map_add]
  map_smul' c x := by apply Subtype.ext; simp [map_smul]
  invFun y := ⟨signTwistAlgHom n y.val, by
    rw [hp]
    have := signTwist_span_singleton_maps (signTwistAlgHom n w) y.val (by rw [← hq]; exact y.prop)
    rwa [signTwist_signTwist] at this⟩
  left_inv x := by apply Subtype.ext; simp [signTwist_signTwist]
  right_inv y := by apply Subtype.ext; simp [signTwist_signTwist]

private theorem signTwistSpanEquiv_coe {n : ℕ}
    (p q : Submodule (RepresentationTheory.PartitionAuxiliary.natIndexedType n) (RepresentationTheory.PartitionAuxiliary.natIndexedType n)) (w : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
    (hp hq) (x : ↥p) :
    (signTwistSpanEquiv p q w hp hq x : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
      = signTwistAlgHom n (x : RepresentationTheory.PartitionAuxiliary.natIndexedType n) := rfl

private theorem signTwistSpanEquiv_equiv {n : ℕ}
    (p q : Submodule (RepresentationTheory.PartitionAuxiliary.natIndexedType n) (RepresentationTheory.PartitionAuxiliary.natIndexedType n)) (w : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
    (hp hq) (g : Equiv.Perm (Fin n)) (x : ↥p) :
    signTwistSpanEquiv p q w hp hq (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g • x)
      = ((Equiv.Perm.sign g : ℤ) : ℂ)
        • (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g • signTwistSpanEquiv p q w hp hq x) := by
  apply Subtype.ext
  simp only [signTwistSpanEquiv_coe, SetLike.val_smul, Submodule.coe_smul_of_tower,
    smul_eq_mul, map_mul, signTwistAlgHom_apply_of, smul_mul_assoc]



private noncomputable def rightMulSpanEquiv {n : ℕ}
    (p q : Submodule (RepresentationTheory.PartitionAuxiliary.natIndexedType n) (RepresentationTheory.PartitionAuxiliary.natIndexedType n)) (v w : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
    (τ : Equiv.Perm (Fin n))
    (hp : p = Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {v})
    (hq : q = Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {w})
    (hvw : v * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹
      = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹ * w)
    (hwv : w * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ
      = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ * v) :
    ↥p ≃ₗ[ℂ] ↥q where
  toFun y := ⟨y.val * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹, by
    rw [hq]
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (by rw [← hp]; exact y.prop)
    rw [Submodule.mem_span_singleton]
    refine ⟨s * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹, ?_⟩
    have : (s * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹) * w
        = y.val * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹ := by
      rw [← hs, smul_eq_mul]
      simp only [mul_assoc]
      rw [hvw]
    rwa [smul_eq_mul]⟩
  map_add' y y' := by apply Subtype.ext; simp [add_mul]
  map_smul' c y := by apply Subtype.ext; simp
  invFun z := ⟨z.val * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ, by
    rw [hp]
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (by rw [← hq]; exact z.prop)
    rw [Submodule.mem_span_singleton]
    refine ⟨s * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ, ?_⟩
    have : (s * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ) * v
        = z.val * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ := by
      rw [← hs, smul_eq_mul]
      simp only [mul_assoc]
      rw [hwv]
    rwa [smul_eq_mul]⟩
  left_inv y := by
    apply Subtype.ext
    change y.val * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹
      * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ = y.val
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  right_inv z := by
    apply Subtype.ext
    change z.val * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ
      * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹ = z.val
    rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

private theorem rightMulSpanEquiv_coe {n : ℕ}
    (p q : Submodule (RepresentationTheory.PartitionAuxiliary.natIndexedType n) (RepresentationTheory.PartitionAuxiliary.natIndexedType n)) (v w : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
    (τ : Equiv.Perm (Fin n)) (hp hq hvw hwv) (y : ↥p) :
    (rightMulSpanEquiv p q v w τ hp hq hvw hwv y : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
      = (y : RepresentationTheory.PartitionAuxiliary.natIndexedType n) * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) τ⁻¹ := rfl

private theorem rightMulSpanEquiv_equiv {n : ℕ}
    (p q : Submodule (RepresentationTheory.PartitionAuxiliary.natIndexedType n) (RepresentationTheory.PartitionAuxiliary.natIndexedType n)) (v w : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
    (τ : Equiv.Perm (Fin n)) (hp hq hvw hwv) (g : Equiv.Perm (Fin n)) (y : ↥p) :
    rightMulSpanEquiv p q v w τ hp hq hvw hwv (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g • y)
      = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g
        • rightMulSpanEquiv p q v w τ hp hq hvw hwv y := by
  apply Subtype.ext
  simp only [rightMulSpanEquiv_coe, SetLike.val_smul, smul_eq_mul, mul_assoc]



/-- There exists a map from the indicated partition-indexed subtype that intertwines permutation action with its sign twist. -/
@[source_ref "Chapter5/Problem5.24.1" (role := supporting)]
theorem exists_signTwistedEquivariantMap (n : ℕ) (la : Nat.Partition n) :
    ∃ e : ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) ≃ₗ[ℂ] ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n (Partition.selfMap la)),
      ∀ (g : Equiv.Perm (Fin n)) (x : ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la)),
        e ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) • x)
          = ((Equiv.Perm.sign g : ℤ) : ℂ)
              • ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) • e x) := by
  classical
  have hk := key_identity la
  have hτiτ : MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)⁻¹
      * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]

  have hφτ : signTwistAlgHom n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la)
        * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)⁻¹
      = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)⁻¹
        * (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n (Partition.selfMap la)
          * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n (Partition.selfMap la)) := by
    rw [← hk]
    simp only [mul_assoc]
    rw [← mul_assoc (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)⁻¹)
      (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)), hτiτ, one_mul]
  have hφτ' : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n (Partition.selfMap la)
        * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n (Partition.selfMap la))
        * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)
      = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (transposePerm la)
        * signTwistAlgHom n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) := by
    rw [← hk]
    simp only [mul_assoc]
    rw [hτiτ, mul_one]

  obtain ⟨E3, hE3⟩ := RepresentationTheory.SymmetricGroup.PartitionSubmodules.exists_equivariantMap n (Partition.selfMap la)
  refine ⟨(signTwistSpanEquiv (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la)
      (Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {signTwistAlgHom n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la)})
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) rfl rfl).trans
    ((rightMulSpanEquiv (Submodule.span (RepresentationTheory.PartitionAuxiliary.natIndexedType n) {signTwistAlgHom n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la)})
      (RepresentationTheory.SymmetricGroup.PartitionSubmodules.partitionSubmodule n (Partition.selfMap la))
      (signTwistAlgHom n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la))
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n (Partition.selfMap la) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n (Partition.selfMap la))
      (transposePerm la) rfl rfl hφτ hφτ').trans E3), fun g x => ?_⟩
  simp only [LinearEquiv.trans_apply]
  rw [signTwistSpanEquiv_equiv, map_smul, rightMulSpanEquiv_equiv, map_smul, hE3]

end RepresentationTheory.SymmetricGroupAlgebra.SignTwist
