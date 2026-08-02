import EtingofRepresentationTheory.Chapter5.Theorem5_26_1

/-!
# Remark 5.26.2: rational and complex spans

The decomposition matrix used in Artin's theorem has irreducible representations of
`G` as its rows and a chosen finite family of induced representations as its columns.
Its entries are integral multiplicities.  Consequently it has full row rank over
`ℚ` exactly when it has full row rank over `ℂ`.

This file first records that linear-algebra fact for an arbitrary integral matrix,
then specializes it to the decomposition matrix of induced characters.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix

namespace Etingof.Remark5262

variable {ι κ : Type*} [Finite ι] [Finite κ]

/-- An integral matrix regarded as a rational matrix. -/
def rationalMatrix (M : Matrix ι κ ℤ) : Matrix ι κ ℚ :=
  M.map (Int.castRingHom ℚ)

/-- An integral matrix regarded as a complex matrix. -/
def complexMatrix (M : Matrix ι κ ℤ) : Matrix ι κ ℂ :=
  M.map (Int.castRingHom ℂ)

/-- For a finite matrix over a field, its columns span the whole row-coordinate
space exactly when its rows are linearly independent. -/
theorem columns_span_iff_rows_linearIndependent
    {K : Type*} [Field K] (M : Matrix ι κ K) :
    Submodule.span K (Set.range M.col) = ⊤ ↔
      LinearIndependent K M.row := by
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

/-- Full column span of an integral matrix is unchanged when the coefficient field
is extended from `ℚ` to `ℂ`. -/
theorem rational_columns_span_iff_complex_columns_span (M : Matrix ι κ ℤ) :
    Submodule.span ℚ (Set.range (rationalMatrix M).col) = ⊤ ↔
      Submodule.span ℂ (Set.range (complexMatrix M).col) = ⊤ := by
  rw [columns_span_iff_rows_linearIndependent,
    columns_span_iff_rows_linearIndependent]
  change LinearIndependent ℚ (fun i j => (M i j : ℚ)) ↔
    LinearIndependent ℂ (fun i j => (M i j : ℂ))
  simpa [Function.comp_def] using
    (linearIndependent_algebraMap_comp_iff
      (R := ℚ) (S := ℂ) (v := fun i j => (M i j : ℚ))).symm

/-- The three matrix conditions appearing in Remark 5.26.2, in book orientation:
columns are decompositions and rows are indexed by irreducibles. -/
theorem span_conditions_iff_row_independence (M : Matrix ι κ ℤ) :
    (Submodule.span ℚ (Set.range (rationalMatrix M).col) = ⊤ ↔
      Submodule.span ℂ (Set.range (complexMatrix M).col) = ⊤) ∧
    (Submodule.span ℚ (Set.range (rationalMatrix M).col) = ⊤ ↔
      LinearIndependent ℚ (rationalMatrix M).row) ∧
    (Submodule.span ℂ (Set.range (complexMatrix M).col) = ⊤ ↔
      LinearIndependent ℂ (complexMatrix M).row) := by
  exact ⟨rational_columns_span_iff_complex_columns_span M,
    columns_span_iff_rows_linearIndependent _,
    columns_span_iff_rows_linearIndependent _⟩

section Artin

variable {G : Type} [Group G] [Fintype G] [NeZero (Nat.card G : ℂ)]

/-- The irreducible characters in an `IrrepDecomp` are linearly independent. -/
theorem irrepCharacters_linearIndependent (D : IrrepDecomp ℂ G) :
    LinearIndependent ℂ (fun i : Fin D.n => (D.columnFDRep i).character) := by
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  haveI (i : Fin D.n) : CategoryTheory.Simple (D.columnFDRep i) :=
    D.columnFDRep_simple i
  have h_iso_iff : ∀ i k : Fin D.n,
      Nonempty ((D.columnFDRep i) ≅ (D.columnFDRep k)) ↔ i = k := by
    intro i k
    constructor
    · exact D.columnFDRep_injective i k
    · rintro rfl
      exact ⟨CategoryTheory.Iso.refl _⟩
  have h_orth : ∀ i : Fin D.n,
      ⅟(Fintype.card G : ℂ) • ∑ g : G,
        (D.columnFDRep i).character g * (D.columnFDRep j).character g⁻¹ =
      if i = j then 1 else 0 := by
    intro i
    rw [FDRep.char_orthonormal_fintype]
    simp [h_iso_iff]
  have lhs_zero : ∀ g,
      (∑ i : Fin D.n, c i * (D.columnFDRep i).character g) = 0 := by
    intro g
    have h := congr_fun hc g
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  have stepA : ⅟(Fintype.card G : ℂ) • ∑ g : G,
      (∑ i : Fin D.n, c i * (D.columnFDRep i).character g) *
      (D.columnFDRep j).character g⁻¹ = 0 := by
    simp_rw [lhs_zero, zero_mul, Finset.sum_const_zero, smul_zero]
  have stepB : ⅟(Fintype.card G : ℂ) • ∑ g : G,
      (∑ i : Fin D.n, c i * (D.columnFDRep i).character g) *
      (D.columnFDRep j).character g⁻¹ =
      ∑ i : Fin D.n, c i * (⅟(Fintype.card G : ℂ) • ∑ g : G,
        (D.columnFDRep i).character g * (D.columnFDRep j).character g⁻¹) := by
    calc
      _ = ⅟(Fintype.card G : ℂ) • ∑ g : G, ∑ i,
          c i * (D.columnFDRep i).character g *
            (D.columnFDRep j).character g⁻¹ := by
        congr 1
        apply Finset.sum_congr rfl
        intro g _
        rw [Finset.sum_mul]
      _ = ⅟(Fintype.card G : ℂ) • ∑ i, ∑ g : G,
          c i * (D.columnFDRep i).character g *
            (D.columnFDRep j).character g⁻¹ := by
        congr 1
        rw [Finset.sum_comm]
      _ = ⅟(Fintype.card G : ℂ) • ∑ i,
          c i * ∑ g : G, (D.columnFDRep i).character g *
            (D.columnFDRep j).character g⁻¹ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        conv_lhs => arg 2; ext g; rw [mul_assoc]
        rw [← Finset.mul_sum]
      _ = ∑ i, c i * (⅟(Fintype.card G : ℂ) •
          ∑ g : G, (D.columnFDRep i).character g *
            (D.columnFDRep j).character g⁻¹) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Algebra.mul_smul_comm]
  simp_rw [stepB, h_orth] at stepA
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at stepA
  exact stepA

/-- Restriction of the `i`th chosen irreducible representation to `H`. -/
def restrictedIrrep (D : IrrepDecomp ℂ G) (H : Subgroup G) (i : Fin D.n) :
    FDRep ℂ ↥H :=
  FDRep.of ((D.columnFDRep i).ρ.comp H.subtype)

/-- The decomposition matrix for a finite family of induced representations.

Rows are indexed by irreducible representations of `G`; columns are indexed by
the chosen pairs `(H j, W j)`.  The `(i,j)` entry is the Frobenius-reciprocity
multiplicity `dim Hom_{H_j}(W_j, Res_{H_j} V_i)`. -/
def decompositionMatrix (D : IrrepDecomp ℂ G)
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) :
    Matrix (Fin D.n) κ ℤ :=
  fun i j => (Module.finrank ℂ (W j ⟶ restrictedIrrep D (H j) i) : ℤ)

/-- The selected induced characters, one for each decomposition-matrix column. -/
def inducedCharacters (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) :
    κ → G → ℂ :=
  fun j => Etingof.inducedCharacter (H j) (W j).character

/-- Rational linear combinations of the chosen irreducible characters. -/
def rationalCharacterCombination (D : IrrepDecomp ℂ G) :
    (Fin D.n → ℚ) →ₗ[ℚ] (G → ℂ) :=
  Fintype.linearCombination ℚ (fun i : Fin D.n => (D.columnFDRep i).character)

/-- Complex linear combinations of the chosen irreducible characters. -/
def complexCharacterCombination (D : IrrepDecomp ℂ G) :
    (Fin D.n → ℂ) →ₗ[ℂ] (G → ℂ) :=
  Fintype.linearCombination ℂ (fun i : Fin D.n => (D.columnFDRep i).character)

omit [Finite κ] in
/-- Each column of the rational decomposition matrix maps to the corresponding
induced character. -/
theorem rationalCharacterCombination_column (D : IrrepDecomp ℂ G)
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) (j : κ) :
    rationalCharacterCombination D ((rationalMatrix (decompositionMatrix D H W)).col j) =
      inducedCharacters H W j := by
  symm
  simpa [rationalCharacterCombination, rationalMatrix, decompositionMatrix,
    restrictedIrrep, inducedCharacters, Fintype.linearCombination_apply,
    Matrix.col_apply, zsmul_eq_mul, Algebra.smul_def, smul_eq_mul] using
    (Etingof.inducedCharacter_eq_irrepDecomp_sum D (H j) (W j))

omit [Finite κ] in
/-- Each column of the complex decomposition matrix maps to the corresponding
induced character. -/
theorem complexCharacterCombination_column (D : IrrepDecomp ℂ G)
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) (j : κ) :
    complexCharacterCombination D ((complexMatrix (decompositionMatrix D H W)).col j) =
      inducedCharacters H W j := by
  symm
  simpa [complexCharacterCombination, complexMatrix, decompositionMatrix,
    restrictedIrrep, inducedCharacters, Fintype.linearCombination_apply,
    Matrix.col_apply, zsmul_eq_mul, Algebra.smul_def, smul_eq_mul] using
    (Etingof.inducedCharacter_eq_irrepDecomp_sum D (H j) (W j))

/-- The rational-span condition for a chosen finite family of induced
representations: its characters span all irreducible characters of `G`. -/
def RationalSpanCondition (D : IrrepDecomp ℂ G)
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) : Prop :=
  Submodule.span ℚ (Set.range (inducedCharacters H W)) =
    Submodule.span ℚ (Set.range (fun i : Fin D.n => (D.columnFDRep i).character))

/-- The complex-span version of `RationalSpanCondition`. -/
def ComplexSpanCondition (D : IrrepDecomp ℂ G)
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) : Prop :=
  Submodule.span ℂ (Set.range (inducedCharacters H W)) =
    Submodule.span ℂ (Set.range (fun i : Fin D.n => (D.columnFDRep i).character))

omit [Finite κ] in
/-- The book's rational character-span condition is exactly full column span of
the rational decomposition matrix. -/
theorem rationalSpanCondition_iff_columns_span (D : IrrepDecomp ℂ G)
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) :
    RationalSpanCondition D H W ↔
      Submodule.span ℚ
        (Set.range (rationalMatrix (decompositionMatrix D H W)).col) = ⊤ := by
  let L := rationalCharacterCombination D
  have hL : Function.Injective L := by
    change Function.Injective (Fintype.linearCombination ℚ
      (fun i : Fin D.n => (D.columnFDRep i).character))
    exact ((irrepCharacters_linearIndependent D).restrict_scalars
      (smul_left_injective ℚ one_ne_zero)).fintypeLinearCombination_injective
  have hcols :
      Submodule.span ℚ (Set.range (inducedCharacters H W)) =
        (Submodule.span ℚ
          (Set.range (rationalMatrix (decompositionMatrix D H W)).col)).map L := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact (rationalCharacterCombination_column D H W j).symm
  have hchars :
      Submodule.span ℚ
          (Set.range (fun i : Fin D.n => (D.columnFDRep i).character)) =
        Submodule.map L ⊤ := by
    rw [Submodule.map_top]
    exact (Fintype.range_linearCombination ℚ
      (fun i : Fin D.n => (D.columnFDRep i).character)).symm
  rw [RationalSpanCondition, hcols, hchars]
  exact (Submodule.map_injective_of_injective hL).eq_iff

omit [Finite κ] in
/-- The book's complex character-span condition is exactly full column span of
the complex decomposition matrix. -/
theorem complexSpanCondition_iff_columns_span (D : IrrepDecomp ℂ G)
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j)) :
    ComplexSpanCondition D H W ↔
      Submodule.span ℂ
        (Set.range (complexMatrix (decompositionMatrix D H W)).col) = ⊤ := by
  let L := complexCharacterCombination D
  have hL : Function.Injective L := by
    change Function.Injective (Fintype.linearCombination ℂ
      (fun i : Fin D.n => (D.columnFDRep i).character))
    exact (irrepCharacters_linearIndependent D).fintypeLinearCombination_injective
  have hcols :
      Submodule.span ℂ (Set.range (inducedCharacters H W)) =
        (Submodule.span ℂ
          (Set.range (complexMatrix (decompositionMatrix D H W)).col)).map L := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact (complexCharacterCombination_column D H W j).symm
  have hchars :
      Submodule.span ℂ
          (Set.range (fun i : Fin D.n => (D.columnFDRep i).character)) =
        Submodule.map L ⊤ := by
    rw [Submodule.map_top]
    exact (Fintype.range_linearCombination ℂ
      (fun i : Fin D.n => (D.columnFDRep i).character)).symm
  rw [ComplexSpanCondition, hcols, hchars]
  exact (Submodule.map_injective_of_injective hL).eq_iff

/-- **Remark 5.26.2.** For any finite chosen family of induced representations
`Ind_{H_j}^G W_j` (in particular, for a finite family selected from the system in
Theorem 5.26.1), the rational and complex span conditions are equivalent.  Both
are equivalent to linear independence of the rows of the book-oriented
decomposition matrix. -/
theorem _root_.Etingof.Remark5_26_2 (D : IrrepDecomp ℂ G)
    (H : κ → Subgroup G) (W : ∀ j, FDRep ℂ ↥(H j))
    (_hW : ∀ j, CategoryTheory.Simple (W j)) :
    (RationalSpanCondition D H W ↔ ComplexSpanCondition D H W) ∧
    (RationalSpanCondition D H W ↔
      LinearIndependent ℚ (rationalMatrix (decompositionMatrix D H W)).row) ∧
    (ComplexSpanCondition D H W ↔
      LinearIndependent ℂ (complexMatrix (decompositionMatrix D H W)).row) := by
  letI := Fintype.ofFinite κ
  have hQ := rationalSpanCondition_iff_columns_span D H W
  have hC := complexSpanCondition_iff_columns_span D H W
  have hQC := rational_columns_span_iff_complex_columns_span
    (decompositionMatrix D H W)
  exact ⟨hQ.trans (hQC.trans hC.symm),
    hQ.trans (columns_span_iff_rows_linearIndependent _),
    hC.trans (columns_span_iff_rows_linearIndependent _)⟩

end Artin

end Etingof.Remark5262
