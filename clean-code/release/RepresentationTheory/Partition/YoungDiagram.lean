/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions

namespace RepresentationTheory.Partition.YoungDiagram

private lemma getD_le_sum (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.sum := by
  induction l generalizing i with
  | nil => simp [List.getD]
  | cons a as ih =>
    cases i with
    | zero =>
      show (a :: as).getD 0 0 ≤ (a :: as).sum
      rw [List.getD_cons_zero, List.sum_cons]
      omega
    | succ i =>
      simp only [List.getD_cons_succ, List.sum_cons]
      exact le_trans (ih i) (Nat.le_add_left _ _)

/-- The sorted parts of a partition sum to its size. -/
lemma sum_sortedParts (n : ℕ) (la : Nat.Partition n) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
      la).sum = n := by
  have h := Multiset.sort_eq la.parts (· ≥ ·)
  have : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
    la) : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
  rw [Multiset.sum_coe] at this; rw [this, la.parts_sum]

/-- The finite type of row-column coordinates lying inside a partition's sorted parts. -/
noncomputable instance cellsFintype (n : ℕ) (la : Nat.Partition n) :
    Fintype { c : ℕ × ℕ //
      c.1 < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
        la).length ∧
      c.2 < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
        la).getD c.1 0 } := by
  haveI : Fintype { c : ℕ × ℕ //
      c ∈ (Finset.range (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
        la).length ×ˢ Finset.range (n+1)) } :=
    (Finset.range (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
      la).length ×ˢ Finset.range (n+1)).fintypeCoeSort
  apply Fintype.ofInjective
    (fun ⟨c, hc⟩ => (⟨c, by
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨hc.1, by
        have := getD_le_sum
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
            la) c.1
        have := sum_sortedParts n la; omega⟩
    ⟩ : { c : ℕ × ℕ //
        c ∈ (Finset.range (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
          la).length ×ˢ Finset.range (n+1)) }))
  intro ⟨a, _⟩ ⟨b, _⟩ h
  exact Subtype.ext (Subtype.mk.inj h)

/-- A finite-type structure on an auxiliary partition-indexed type. -/
noncomputable instance auxiliaryFintype (n : ℕ) (la : Nat.Partition n) :
    Fintype
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource
        n la) := by
  unfold RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource
  haveI := cellsFintype n la
  exact Subtype.fintype _

/-- An auxiliary partition-indexed type is finite. -/
instance auxiliary_finite (n : ℕ) (la : Nat.Partition n) :
    Finite
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource
        n la) := by
  classical
  unfold RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource
  change Finite { f : { c : ℕ × ℕ //
    c.1 < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
      la).length ∧
    c.2 < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
      la).getD c.1 0 } → Fin n // _ }
  exact Subtype.finite

end RepresentationTheory.Partition.YoungDiagram
