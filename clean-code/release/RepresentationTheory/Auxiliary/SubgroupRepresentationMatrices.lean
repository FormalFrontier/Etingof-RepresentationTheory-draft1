/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliarySubgroupFunctions
import RepresentationTheory.Alignment.Attribute

/-!
# Matrices associated with subgroup representations

This module compares rational and complex column spans of integral matrices and applies the
comparison to matrices associated with subgroup representations.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix

namespace RepresentationTheory.Auxiliary.SubgroupRepresentationMatrices

open RepresentationTheory.AuxiliarySubgroupFunctions
  RepresentationTheory.FDRep.GroupAlgebraDecomposition

variable {ι κ : Type*} [Finite ι] [Finite κ]

/-- Converts every integer entry of a matrix to a rational number. -/
def Matrix.intCastToRat (M : Matrix ι κ ℤ) : Matrix ι κ ℚ :=
  M.map (Int.castRingHom ℚ)

/-- Converts every integer entry of a matrix to a complex number. -/
def Matrix.intCastToComplex (M : Matrix ι κ ℤ) : Matrix ι κ ℂ :=
  M.map (Int.castRingHom ℂ)

/-- Characterizes when the column range of a matrix spans the full module by linear independence
of its rows. -/
theorem matrixColumnsSpanTop_iff_rows_linearIndependent
    {K : Type*} [Field K] (M : Matrix ι κ K) :
    Submodule.span K (Set.range M.col) = ⊤ ↔ LinearIndependent K M.row := by
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite κ
  constructor
  · intro hspan
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank, ← M.rank_eq_finrank_span_row,
      M.rank_eq_finrank_span_cols, hspan, finrank_top,
      Module.finrank_fintype_fun_eq_card]
  · intro hrows
    apply Submodule.eq_top_iff_finrank_eq.mpr
    rw [← M.rank_eq_finrank_span_cols, hrows.rank_matrix,
      Module.finrank_fintype_fun_eq_card]

/-- For an integer matrix, rational column spanning is equivalent to complex column spanning after
entrywise conversion. -/
theorem integerMatrixRatColumnsSpanTop_iff_complexColumnsSpanTop (M : Matrix ι κ ℤ) :
    Submodule.span ℚ (Set.range (Matrix.intCastToRat M).col) = ⊤ ↔
      Submodule.span ℂ (Set.range (Matrix.intCastToComplex M).col) = ⊤ := by
  rw [matrixColumnsSpanTop_iff_rows_linearIndependent,
    matrixColumnsSpanTop_iff_rows_linearIndependent]
  change LinearIndependent ℚ (fun i j => (M i j : ℚ)) ↔
    LinearIndependent ℂ (fun i j => (M i j : ℂ))
  simpa [Function.comp_def] using
    (linearIndependent_algebraMap_comp_iff
      (R := ℚ) (S := ℂ) (v := fun i j => (M i j : ℚ))).symm

/-- Collects the rational and complex spanning equivalences and their row-linear-independence
characterizations for an integer matrix. -/
theorem integerMatrixSpanningAndRowIndependence (M : Matrix ι κ ℤ) :
    (Submodule.span ℚ (Set.range (Matrix.intCastToRat M).col) = ⊤ ↔
      Submodule.span ℂ (Set.range (Matrix.intCastToComplex M).col) = ⊤) ∧
    (Submodule.span ℚ (Set.range (Matrix.intCastToRat M).col) = ⊤ ↔
      LinearIndependent ℚ (Matrix.intCastToRat M).row) ∧
    (Submodule.span ℂ (Set.range (Matrix.intCastToComplex M).col) = ⊤ ↔
      LinearIndependent ℂ (Matrix.intCastToComplex M).row) := by
  exact ⟨integerMatrixRatColumnsSpanTop_iff_complexColumnsSpanTop M,
    matrixColumnsSpanTop_iff_rows_linearIndependent _,
    matrixColumnsSpanTop_iff_rows_linearIndependent _⟩

section Artin

variable {G : Type} [Group G] [Fintype G] [NeZero (Nat.card G : ℂ)]

/-- The displayed family of complex-valued representation characters is linearly independent. -/
theorem representationCharacterFamily_linearIndependent (D : DecompositionData ℂ G) :
    LinearIndependent ℂ (fun i : Fin D.count => (D.representation i).character) := by
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  haveI (i : Fin D.count) : CategoryTheory.Simple (D.representation i) :=
    D.simple_representation i
  have h_iso_iff : ∀ i k : Fin D.count,
      Nonempty ((D.representation i) ≅ (D.representation k)) ↔ i = k := by
    intro i k
    constructor
    · exact D.representation_index_eq_of_iso i k
    · rintro rfl
      exact ⟨CategoryTheory.Iso.refl _⟩
  have h_orth : ∀ i : Fin D.count,
      ⅟(Fintype.card G : ℂ) • ∑ g : G,
        (D.representation i).character g * (D.representation j).character g⁻¹ =
      if i = j then 1 else 0 := by
    intro i
    rw [RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple]
    simp [h_iso_iff]
  have lhs_zero : ∀ g,
      (∑ i : Fin D.count, c i * (D.representation i).character g) = 0 := by
    intro g
    have h := congr_fun hc g
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  have stepA : ⅟(Fintype.card G : ℂ) • ∑ g : G,
      (∑ i : Fin D.count, c i * (D.representation i).character g) *
      (D.representation j).character g⁻¹ = 0 := by
    simp_rw [lhs_zero, zero_mul, Finset.sum_const_zero, smul_zero]
  have stepB : ⅟(Fintype.card G : ℂ) • ∑ g : G,
      (∑ i : Fin D.count, c i * (D.representation i).character g) *
      (D.representation j).character g⁻¹ =
      ∑ i : Fin D.count, c i * (⅟(Fintype.card G : ℂ) • ∑ g : G,
        (D.representation i).character g * (D.representation j).character g⁻¹) := by
    calc
      _ = ⅟(Fintype.card G : ℂ) • ∑ g : G, ∑ i,
          c i * (D.representation i).character g *
            (D.representation j).character g⁻¹ := by
        congr 1
        apply Finset.sum_congr rfl
        intro g _
        rw [Finset.sum_mul]
      _ = ⅟(Fintype.card G : ℂ) • ∑ i, ∑ g : G,
          c i * (D.representation i).character g *
            (D.representation j).character g⁻¹ := by
        congr 1
        rw [Finset.sum_comm]
      _ = ⅟(Fintype.card G : ℂ) • ∑ i,
          c i * ∑ g : G, (D.representation i).character g *
            (D.representation j).character g⁻¹ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        conv_lhs => arg 2; ext g; rw [mul_assoc]
        rw [← Finset.mul_sum]
      _ = ∑ i, c i * (⅟(Fintype.card G : ℂ) •
          ∑ g : G, (D.representation i).character g *
            (D.representation j).character g⁻¹) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Algebra.mul_smul_comm]
  simp_rw [stepB, h_orth] at stepA
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at stepA
  exact stepA

/-- Associates to each finite representation index a representation of a specified subgroup. -/
def subgroupRepresentationFamily (D : DecompositionData ℂ G) (H : Subgroup G)
    (i : Fin D.count) : FDRep ℂ ↥H :=
  FDRep.of ((D.representation i).ρ.comp H.subtype)

/-- An integer-valued matrix associated with a finite group representation, subgroups, and
representation data. -/
def auxiliaryIntegerMatrix (D : DecompositionData ℂ G)
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) :
    Matrix (Fin D.count) κ ℤ :=
  fun i j => (Module.finrank ℂ (W j ⟶ subgroupRepresentationFamily D (H j) i) : ℤ)

/-- Produces group functions indexed by a family of subgroups and corresponding representations. -/
def auxiliarySubgroupRepresentationFunctions
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) : κ → G → ℂ :=
  fun j => auxiliaryFunction (H j) (W j).character

/-- Maps rational-valued coefficient vectors indexed by a finite representation index to
complex-valued group functions. -/
def rationalCoefficientFunctionMap (D : DecompositionData ℂ G) :
    (Fin D.count → ℚ) →ₗ[ℚ] (G → ℂ) :=
  Fintype.linearCombination ℚ (fun i : Fin D.count => (D.representation i).character)

/-- Maps complex-valued coefficient vectors indexed by a finite representation index to group
functions. -/
def complexCoefficientFunctionMap (D : DecompositionData ℂ G) :
    (Fin D.count → ℂ) →ₗ[ℂ] (G → ℂ) :=
  Fintype.linearCombination ℂ (fun i : Fin D.count => (D.representation i).character)

omit [Finite κ] in
/-- Evaluating the rational coefficient map on a converted integer-matrix column gives the
corresponding indexed group function. -/
theorem rationalCoefficientFunctionMap_apply_integerMatrixColumn
    (D : DecompositionData ℂ G) (H : κ → Subgroup G)
    (W : ∀ j, FDRep ℂ ↥(H j)) (j : κ) :
    rationalCoefficientFunctionMap D
        ((Matrix.intCastToRat (auxiliaryIntegerMatrix D H W)).col j) =
      auxiliarySubgroupRepresentationFunctions H W j := by
  symm
  simpa [rationalCoefficientFunctionMap, Matrix.intCastToRat, auxiliaryIntegerMatrix,
    subgroupRepresentationFamily, auxiliarySubgroupRepresentationFunctions,
    Fintype.linearCombination_apply, Matrix.col_apply, zsmul_eq_mul, Algebra.smul_def,
    smul_eq_mul] using
    (auxiliaryFunction_eq_sum_character D (H j) (W j))

omit [Finite κ] in
/-- Evaluating the complex coefficient map on a converted integer-matrix column gives the
corresponding indexed group function. -/
theorem complexCoefficientFunctionMap_apply_integerMatrixColumn
    (D : DecompositionData ℂ G) (H : κ → Subgroup G)
    (W : ∀ j, FDRep ℂ ↥(H j)) (j : κ) :
    complexCoefficientFunctionMap D
        ((Matrix.intCastToComplex (auxiliaryIntegerMatrix D H W)).col j) =
      auxiliarySubgroupRepresentationFunctions H W j := by
  symm
  simpa [complexCoefficientFunctionMap, Matrix.intCastToComplex, auxiliaryIntegerMatrix,
    subgroupRepresentationFamily, auxiliarySubgroupRepresentationFunctions,
    Fintype.linearCombination_apply, Matrix.col_apply, zsmul_eq_mul, Algebra.smul_def,
    smul_eq_mul] using
    (auxiliaryFunction_eq_sum_character D (H j) (W j))

/-- An auxiliary proposition involving a finite group representation, subgroups, and representation
data. -/
def auxiliaryRationalCondition (D : DecompositionData ℂ G)
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) : Prop :=
  Submodule.span ℚ (Set.range (auxiliarySubgroupRepresentationFunctions H W)) =
    Submodule.span ℚ (Set.range (fun i : Fin D.count => (D.representation i).character))

/-- An auxiliary proposition involving a finite group representation, subgroups, and representation
data. -/
def auxiliaryComplexCondition (D : DecompositionData ℂ G)
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) : Prop :=
  Submodule.span ℂ (Set.range (auxiliarySubgroupRepresentationFunctions H W)) =
    Submodule.span ℂ (Set.range (fun i : Fin D.count => (D.representation i).character))

omit [Finite κ] in
/-- Expresses the auxiliary rational proposition as spanning by converted integer-matrix
columns. -/
theorem auxiliaryRationalCondition_iff_integerMatrixColumnsSpan
    (D : DecompositionData ℂ G) (H : κ → Subgroup G)
    (W : ∀ j, FDRep ℂ ↥(H j)) :
    auxiliaryRationalCondition D H W ↔
      Submodule.span ℚ
        (Set.range (Matrix.intCastToRat (auxiliaryIntegerMatrix D H W)).col) = ⊤ := by
  let L := rationalCoefficientFunctionMap D
  have hL : Function.Injective L := by
    change Function.Injective (Fintype.linearCombination ℚ
      (fun i : Fin D.count => (D.representation i).character))
    exact ((representationCharacterFamily_linearIndependent D).restrict_scalars
      (smul_left_injective ℚ one_ne_zero)).fintypeLinearCombination_injective
  have hcols :
      Submodule.span ℚ (Set.range (auxiliarySubgroupRepresentationFunctions H W)) =
        (Submodule.span ℚ
          (Set.range (Matrix.intCastToRat (auxiliaryIntegerMatrix D H W)).col)).map L := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact (rationalCoefficientFunctionMap_apply_integerMatrixColumn D H W j).symm
  have hchars :
      Submodule.span ℚ
          (Set.range (fun i : Fin D.count => (D.representation i).character)) =
        Submodule.map L ⊤ := by
    rw [Submodule.map_top]
    exact (Fintype.range_linearCombination ℚ
      (fun i : Fin D.count => (D.representation i).character)).symm
  rw [auxiliaryRationalCondition, hcols, hchars]
  exact (Submodule.map_injective_of_injective hL).eq_iff

omit [Finite κ] in
/-- Expresses the auxiliary complex proposition as spanning by converted integer-matrix
columns. -/
theorem auxiliaryComplexCondition_iff_integerMatrixColumnsSpan
    (D : DecompositionData ℂ G) (H : κ → Subgroup G)
    (W : ∀ j, FDRep ℂ ↥(H j)) :
    auxiliaryComplexCondition D H W ↔
      Submodule.span ℂ
        (Set.range (Matrix.intCastToComplex (auxiliaryIntegerMatrix D H W)).col) = ⊤ := by
  let L := complexCoefficientFunctionMap D
  have hL : Function.Injective L := by
    change Function.Injective (Fintype.linearCombination ℂ
      (fun i : Fin D.count => (D.representation i).character))
    exact (representationCharacterFamily_linearIndependent D).fintypeLinearCombination_injective
  have hcols :
      Submodule.span ℂ (Set.range (auxiliarySubgroupRepresentationFunctions H W)) =
        (Submodule.span ℂ
          (Set.range (Matrix.intCastToComplex (auxiliaryIntegerMatrix D H W)).col)).map L := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact (complexCoefficientFunctionMap_apply_integerMatrixColumn D H W j).symm
  have hchars :
      Submodule.span ℂ
          (Set.range (fun i : Fin D.count => (D.representation i).character)) =
        Submodule.map L ⊤ := by
    rw [Submodule.map_top]
    exact (Fintype.range_linearCombination ℂ
      (fun i : Fin D.count => (D.representation i).character)).symm
  rw [auxiliaryComplexCondition, hcols, hchars]
  exact (Submodule.map_injective_of_injective hL).eq_iff

/-- Under simplicity of each displayed subgroup representation, relates the auxiliary rational and
complex propositions and their matrix row-independence forms. -/
@[source_ref"Chapter5/Remark5.26.2"(role:=primary),
  source_ref"Chapter5/Remark5.26.2"(role:=primary)]
theorem simpleSubgroupRepresentationFamily_auxiliaryConditions
    (D : DecompositionData ℂ G) (H : κ → Subgroup G)
    (W : ∀ j, FDRep ℂ ↥(H j)) (_hW : ∀ j, CategoryTheory.Simple (W j)) :
    (auxiliaryRationalCondition D H W ↔ auxiliaryComplexCondition D H W) ∧
    (auxiliaryRationalCondition D H W ↔
      LinearIndependent ℚ (Matrix.intCastToRat (auxiliaryIntegerMatrix D H W)).row) ∧
    (auxiliaryComplexCondition D H W ↔
      LinearIndependent ℂ (Matrix.intCastToComplex (auxiliaryIntegerMatrix D H W)).row) := by
  letI := Fintype.ofFinite κ
  have hQ := auxiliaryRationalCondition_iff_integerMatrixColumnsSpan D H W
  have hC := auxiliaryComplexCondition_iff_integerMatrixColumnsSpan D H W
  have hQC := integerMatrixRatColumnsSpanTop_iff_complexColumnsSpanTop
    (auxiliaryIntegerMatrix D H W)
  exact ⟨hQ.trans (hQC.trans hC.symm),
    hQ.trans (matrixColumnsSpanTop_iff_rows_linearIndependent _),
    hC.trans (matrixColumnsSpanTop_iff_rows_linearIndependent _)⟩

end Artin

end RepresentationTheory.Auxiliary.SubgroupRepresentationMatrices
