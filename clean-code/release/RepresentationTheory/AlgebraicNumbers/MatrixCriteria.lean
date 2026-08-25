/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.AlgebraicNumbers.MatrixCriteria

open IntermediateField in
/-- Characterizes rational-algebraic complex numbers through zeros of characteristic polynomials arising from rational matrices. -/
@[source_ref "Chapter5/Definition5.2.2" (role := primary)]
theorem isAlgebraic_iff_exists_rat_matrix_charpoly_isRoot
    (z : ℂ) :
    IsAlgebraic ℚ z ↔
    ∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ),
      (Matrix.charpoly (M.map (algebraMap ℚ ℂ))).IsRoot z := by
  constructor
  · intro halg
    have hint : IsIntegral ℚ z := isAlgebraic_iff_isIntegral.mp halg
    set F := ℚ⟮z⟯ with hF
    let pb := adjoin.powerBasis hint
    let M := Algebra.leftMulMatrix pb.basis pb.gen
    refine ⟨_, M, ?_⟩
    rw [Matrix.charpoly_map, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        charpoly_leftMulMatrix]
    have hgen : (algebraMap F ℂ) pb.gen = z := by
      simp [pb, adjoin.powerBasis_gen]
    let ι := IsScalarTower.toAlgHom ℚ F ℂ
    have : ι pb.gen = z := hgen
    calc Polynomial.aeval z (minpoly ℚ pb.gen)
        = Polynomial.aeval (ι pb.gen) (minpoly ℚ pb.gen) := by rw [this]
      _ = ι (Polynomial.aeval pb.gen (minpoly ℚ pb.gen)) :=
          Polynomial.aeval_algHom_apply ι pb.gen (minpoly ℚ pb.gen)
      _ = ι 0 := by rw [minpoly.aeval]
      _ = 0 := map_zero ι
  · rintro ⟨n, M, hroot⟩
    rw [Matrix.charpoly_map] at hroot
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at hroot
    exact ⟨M.charpoly, M.charpoly_monic.ne_zero, hroot⟩

/-- Characterizes integer-integral complex numbers through zeros of characteristic polynomials arising from integer matrices. -/
@[source_ref "Chapter5/Definition5.2.2" (role := primary)]
theorem isIntegral_iff_exists_int_matrix_charpoly_isRoot
    (z : ℂ) :
    IsIntegral ℤ z ↔
    ∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ),
      (Matrix.charpoly (M.map (algebraMap ℤ ℂ))).IsRoot z := by
  constructor
  · intro hint
    let S := Algebra.adjoin ℤ ({z} : Set ℂ)
    let pb := Algebra.adjoin.powerBasis' hint
    let M := Algebra.leftMulMatrix pb.basis pb.gen
    refine ⟨_, M, ?_⟩
    rw [Matrix.charpoly_map, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        charpoly_leftMulMatrix]
    let ι := IsScalarTower.toAlgHom ℤ S ℂ
    have hgen : ι pb.gen = z := by
      simp [ι, pb, Algebra.adjoin.powerBasis'_gen]
    calc Polynomial.aeval z (minpoly ℤ pb.gen)
        = Polynomial.aeval (ι pb.gen) (minpoly ℤ pb.gen) := by rw [hgen]
      _ = ι (Polynomial.aeval pb.gen (minpoly ℤ pb.gen)) :=
          Polynomial.aeval_algHom_apply ι pb.gen (minpoly ℤ pb.gen)
      _ = ι 0 := by rw [minpoly.aeval]
      _ = 0 := map_zero ι
  · rintro ⟨n, M, hroot⟩
    rw [Matrix.charpoly_map] at hroot
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at hroot
    exact ⟨M.charpoly, M.charpoly_monic, hroot⟩

end RepresentationTheory.AlgebraicNumbers.MatrixCriteria
