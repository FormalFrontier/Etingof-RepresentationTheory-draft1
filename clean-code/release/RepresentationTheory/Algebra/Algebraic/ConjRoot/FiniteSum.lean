/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

open Polynomial

namespace RepresentationTheory.Algebra.Algebraic.ConjRoot.FiniteSum

/-- A conjugate over the rationals of a finite sum of algebraic complex numbers can be expressed as a sum of conjugates of the individual summands. -/
@[source_ref "Chapter5/Lemma5.2.6" (role := primary)]
theorem exists_conjRoots_sum_eq_of_isConjRoot_sum
    (m : ℕ) (α : Fin m → ℂ) (hα : ∀ i, IsAlgebraic ℚ (α i))
    (β : ℂ) (hβ : IsConjRoot ℚ (∑ i, α i) β) :
    ∃ α' : Fin m → ℂ, (∀ i, IsConjRoot ℚ (α i) (α' i)) ∧ β = ∑ i, α' i := by
  classical
  set K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range α) with hK
  have mem : ∀ i, α i ∈ K :=
    fun i => IntermediateField.subset_adjoin ℚ (Set.range α) (Set.mem_range_self i)
  have hsum : (∑ i, α i) ∈ K := sum_mem (fun i _ => mem i)
  have hsplits : ∀ s ∈ Set.range α, IsIntegral ℚ s ∧
      ((minpoly ℚ s).map (algebraMap ℚ ℂ)).Splits := by
    rintro _ ⟨i, rfl⟩
    exact ⟨(hα i).isIntegral, IsAlgClosed.splits _⟩
  have hroot : (aeval β) (minpoly ℚ (∑ i, α i)) = 0 := hβ.aeval_eq_zero
  obtain ⟨φ, hφ⟩ :=
    IntermediateField.exists_algHom_adjoin_of_splits_of_aeval hsplits hsum hroot
  refine ⟨fun i => φ ⟨α i, mem i⟩, fun i => ?_, ?_⟩
  · apply isConjRoot_of_aeval_eq_zero (hα i).isIntegral
    rw [Polynomial.aeval_algHom_apply]
    have hz : (aeval (⟨α i, mem i⟩ : K)) (minpoly ℚ (α i)) = 0 := by
      rw [← map_eq_zero_iff K.val Subtype.val_injective, ← Polynomial.aeval_algHom_apply]
      simp
    rw [hz, map_zero]
  · have hsum' : (∑ i, (⟨α i, mem i⟩ : K)) = ⟨∑ i, α i, hsum⟩ := by
      apply Subtype.ext
      push_cast
      rfl
    calc β = φ ⟨∑ i, α i, hsum⟩ := hφ.symm
      _ = φ (∑ i, (⟨α i, mem i⟩ : K)) := by rw [hsum']
      _ = ∑ i, φ ⟨α i, mem i⟩ := by rw [map_sum]

end RepresentationTheory.Algebra.Algebraic.ConjRoot.FiniteSum
