/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier
-/

import RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty

/-!
# Matrix-bounded vectors

Definitions and finiteness results for integer vectors constrained by a square matrix.
-/

namespace RepresentationTheory.MatrixBoundedVectors

/-- The set of integer-valued vectors associated with a square integer matrix. -/
def integerVectors (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) :
    Set (Fin n → ℤ) :=
  {x | RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x ∧
    ∀ i, 0 ≤ x i}

open Matrix Finset

/-- The finite collection of bounded vectors associated with a square integer matrix. -/
def boundedVectors (n : ℕ)
    (adj : Matrix (Fin n) (Fin n) ℤ) (B : ℕ) :
    Finset (Fin n → Fin B) :=
  (univ : Finset (Fin n → Fin B)).filter fun v =>
    let x : Fin n → ℤ := fun i => (v i : ℤ)
    decide (x ≠ 0) &&
    decide (dotProduct x
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) = 2)

/-- A vector from the bounded finite collection, after coercing its coordinates to integers, belongs to the associated integer-vector set. -/
lemma mem_integerVectors_of_mem_boundedVectors {n : ℕ}
    {adj : Matrix (Fin n) (Fin n) ℤ}
    {B : ℕ} {v : Fin n → Fin B}
    (hv : v ∈ boundedVectors n adj B) :
    (fun i => (v i : ℤ)) ∈ integerVectors n adj := by
  simp only [boundedVectors, mem_filter, mem_univ, true_and,
    Bool.and_eq_true, decide_eq_true_eq] at hv
  exact ⟨⟨hv.1, hv.2⟩, fun i => Int.natCast_nonneg _⟩

/-- Casting the coordinates of a finite-valued vector to integers is injective. -/
lemma finNatCast_injective {n B : ℕ} :
    Function.Injective
      (fun (v : Fin n → Fin B) (i : Fin n) => (v i : ℤ)) := by
  intro v w h
  funext i
  have : (v i : ℤ) = (w i : ℤ) := congr_fun h i
  exact Fin.ext (by exact_mod_cast this)

/-- Under the stated coordinate bounds, the associated integer-vector set is finite and has the same cardinality as the bounded finite-vector collection. -/
lemma integerVectors_finite_ncard_eq_boundedVectors_card {n : ℕ}
    {adj : Matrix (Fin n) (Fin n) ℤ} {B : ℕ}
    (hbound : ∀ x : Fin n → ℤ,
      RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x →
      (∀ i, 0 ≤ x i) → ∀ i, x i < B) :
    (integerVectors n adj).Finite ∧
    Set.ncard (integerVectors n adj) =
      (boundedVectors n adj B).card := by
  suffices h : integerVectors n adj =
      ↑((boundedVectors n adj B).image
        (fun v i => (v i : ℤ))) by
    refine ⟨h ▸ ((boundedVectors n adj B).image _).finite_toSet,
      ?_⟩
    rw [h, Set.ncard_coe_finset,
      Finset.card_image_of_injective _ finNatCast_injective]
  ext x
  simp only [integerVectors, Set.mem_setOf_eq,
    Finset.coe_image, Set.mem_image, Finset.mem_coe]
  constructor
  · intro ⟨hroot, hpos⟩
    refine ⟨fun i => ⟨(x i).toNat, ?_⟩, ?_, ?_⟩
    · exact Int.toNat_lt (hpos i) |>.mpr (hbound x hroot hpos i)
    · simp only [boundedVectors, mem_filter, mem_univ, true_and,
        Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · intro heq
        exact hroot.1 (by
          ext i
          have := congr_fun heq i
          simp only [Int.toNat_of_nonneg (hpos i),
            Pi.zero_apply] at this
          exact this)
      · have hconv : (fun i => ((x i).toNat : ℤ)) = x :=
          funext fun i => Int.toNat_of_nonneg (hpos i)
        simp only [hconv]; exact hroot.2
    · funext i; exact Int.toNat_of_nonneg (hpos i)
  · intro ⟨v, hv, hvx⟩
    subst hvx
    exact mem_integerVectors_of_mem_boundedVectors hv

end RepresentationTheory.MatrixBoundedVectors
