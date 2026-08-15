/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteGroups.GL2Conjugacy
import RepresentationTheory.FiniteGroup.ComplexGroupAlgebraDecomposition
import RepresentationTheory.FiniteField.AuxiliaryRepresentations
import RepresentationTheory.GaloisFieldCharacters
import RepresentationTheory.FDRep.Completeness
import RepresentationTheory.Alignment.Attribute

/-!
# Irreducible representations of two-dimensional general linear groups

This module packages a complete family of irreducible complex representations of
`GL₂(𝔽_q)` and derives its cardinality from the conjugacy-class count.
-/

namespace RepresentationTheory.GeneralLinearGroupTwoIrreps

/-- Expresses `q^2 - 1` as `q - 1` plus twice a quotient. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary/Derived01" (role := supporting)]
theorem sub_one_add_twice_div_eq_sq_sub_one (q : ℕ) (hq : 1 ≤ q) :
    (q - 1) + q * (q - 1) / 2 + q * (q - 1) / 2 = q ^ 2 - 1 := by
  have he : 2 ∣ q * (q - 1) := by
    rcases Nat.even_or_odd q with h | h
    · exact Dvd.dvd.mul_right h.two_dvd _
    · have : Even (q - 1) := by rcases h with ⟨k, hk⟩; exact ⟨k, by omega⟩
      exact Dvd.dvd.mul_left this.two_dvd _
  obtain ⟨m, hm⟩ := he
  rw [hm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  zify [hq, h1] at hm ⊢
  nlinarith [hm]

/-- An auxiliary property of finite fields. -/
def HasAuxiliaryProperty (F : Type*) [Field F] [Fintype F] : Prop :=
  Nat.card (ConjClasses (Matrix.GeneralLinearGroup (Fin 2) F)) = Fintype.card F ^ 2 - 1

section GaloisField

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [Fintype (GaloisField p n)]

/-- The finite field satisfies the auxiliary property under the displayed assumptions. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := supporting)]
theorem galoisField_hasAuxiliaryProperty (hp2 : p ≠ 2) (hn : n ≠ 0) :
    HasAuxiliaryProperty (GaloisField p n) := by
  classical
  unfold HasAuxiliaryProperty
  exact RepresentationTheory.FiniteGroups.GL2Conjugacy.card_conjClasses_eq_fieldCard_sq_sub_one hp2 hn

/-- Computes the number of conjugacy classes of the two-dimensional general linear group. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := primary)]
theorem card_conjClasses_generalLinearGroup_two (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (Fintype.card (GaloisField p n) - 1)
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2
      = Nat.card (ConjClasses (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))) := by
  classical
  exact (sub_one_add_twice_div_eq_sq_sub_one _ Fintype.card_pos).trans
    (RepresentationTheory.FiniteGroups.GL2Conjugacy.card_conjClasses_eq_fieldCard_sq_sub_one hp2 hn).symm

/-- A supplied conjugacy-class count equals the displayed auxiliary expression. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := supporting)]
theorem eq_auxiliaryExpression_of_eq_card_conjClasses (numIrreps : ℕ)
    (bridge : numIrreps =
      Nat.card (ConjClasses (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))))
    (hp2 : p ≠ 2) (hn : n ≠ 0) :
    numIrreps = (Fintype.card (GaloisField p n) - 1)
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2 :=
  bridge.trans (card_conjClasses_generalLinearGroup_two p n hp2 hn).symm

/-- There is a matrix-algebra decomposition indexed by a type of the displayed cardinality. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := supporting)]
theorem exists_groupAlgebra_matrixDecomposition (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∃ (Irrep : Type) (_ : Fintype Irrep),
      (∃ d : Irrep → ℕ, (∀ j, d j ≠ 0) ∧
        Nonempty (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))
          ≃ₐ[ℂ] Π j, Matrix (Fin (d j)) (Fin (d j)) ℂ)) ∧
      Nat.card Irrep = (Fintype.card (GaloisField p n) - 1)
        + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2
        + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2 := by
  obtain ⟨Irrep, hFin, hcard, hdata⟩ :=
    RepresentationTheory.FiniteGroup.ComplexGroupAlgebraDecomposition.exists_type_indexed_matrix_block_decomposition_card_eq_conjClasses
      (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))
  exact ⟨Irrep, hFin, hdata,
    eq_auxiliaryExpression_of_eq_card_conjClasses p n (Nat.card Irrep) hcard hp2 hn⟩

/-- There exists a type with cardinality one less than the square of the field cardinality. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := supporting)]
theorem exists_auxiliaryType_card (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∃ (Irrep : Type) (_ : Fintype Irrep),
      Nat.card Irrep = Fintype.card (GaloisField p n) ^ 2 - 1 := by
  obtain ⟨Irrep, hFin, _, hcard⟩ := exists_groupAlgebra_matrixDecomposition p n hp2 hn
  exact ⟨Irrep, hFin, hcard.trans (sub_one_add_twice_div_eq_sq_sub_one _ Fintype.card_pos)⟩

open CategoryTheory in
/-- There exists a complete pairwise nonisomorphic family of simple representations of the stated size. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := primary)]
theorem exists_completeSimpleFamily_card (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∃ (m : ℕ) (V : Fin m → FDRep ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ U, Simple U → ∃ i, Nonempty (U ≅ V i)) ∧
      m = Fintype.card (GaloisField p n) ^ 2 - 1 := by
  classical
  haveI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) := inferInstance
  haveI : Invertible
      ((Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) : ℂ)) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  obtain ⟨m, V, hsimp, hinj, hsurj, hm⟩ :=
    RepresentationTheory.Group.SimpleRepresentations.exists_simpleReps_card_eq_conjClasses (k := ℂ)
      (G := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))
  refine ⟨m, V, hsimp, hinj, hsurj, ?_⟩
  rw [hm, ← Nat.card_eq_fintype_card]
  exact RepresentationTheory.FiniteGroups.GL2Conjugacy.card_conjClasses_eq_fieldCard_sq_sub_one hp2 hn

open CategoryTheory in
/-- A suitably sized pairwise nonisomorphic simple family contains every simple representation up to isomorphism. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := supporting)]
theorem simple_isIso_of_complete_family (hp2 : p ≠ 2) (hn : n ≠ 0) {N : ℕ}
    (W : Fin N → FDRep ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)))
    (hWsimple : ∀ i, Simple (W i))
    (hWnoniso : ∀ i j, Nonempty (W i ≅ W j) → i = j)
    (hN : N = (Fintype.card (GaloisField p n) - 1)
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2
      + Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2) :
    ∀ U, Simple U → ∃ i, Nonempty (U ≅ W i) := by
  classical
  haveI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) := inferInstance
  haveI : Invertible
      ((Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) : ℂ)) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  exact RepresentationTheory.FDRep.Completeness.simpleFDRepFamily_complete_of_card_eq_conjClasses W hWsimple hWnoniso
    (hN.trans (card_conjClasses_generalLinearGroup_two p n hp2 hn))

open CategoryTheory

/-- An auxiliary index type associated to a finite field. -/
abbrev AuxiliaryIndexFamily (hn : n ≠ 0) :=
  let _ : NeZero n := ⟨hn⟩
  RepresentationTheory.GaloisFieldCharacters.GaloisField.AuxiliaryIndex p n

/-- An auxiliary type depending on the displayed finite-field data. -/
abbrev AuxiliaryIndexType (hn : n ≠ 0) :=
  RepresentationTheory.FiniteField.AuxiliaryRepresentations.AuxiliaryRepresentationIndex p n ⊕ AuxiliaryIndexFamily p n hn

/-- An auxiliary finite-dimensional complex representation indexed by the auxiliary type. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := supporting),
  source_ref "Chapter5/Discussion_complementary_series_summary/Derived01" (role := supporting)]
noncomputable def auxiliaryRepresentation (hp2 : p ≠ 2) (hn : n ≠ 0)
    (i : AuxiliaryIndexType p n hn) :
    FDRep ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) := by
  classical
  letI : NeZero n := ⟨hn⟩
  letI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) :=
    Fintype.ofFinite _
  exact match i with
    | .inl j => RepresentationTheory.FiniteField.AuxiliaryRepresentations.AuxiliaryRepresentation p n j
    | .inr j => RepresentationTheory.GaloisFieldCharacters.GaloisField.fdRepOfAuxiliaryIndex p n hp2 j

/-- Every representation in the indexed family is simple. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := primary),
  source_ref "Chapter5/Discussion_complementary_series_summary/Derived01" (role := supporting)]
theorem auxiliaryRepresentation_simple (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∀ i : AuxiliaryIndexType p n hn, Simple (auxiliaryRepresentation p n hp2 hn i) := by
  classical
  letI : NeZero n := ⟨hn⟩
  letI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) :=
    Fintype.ofFinite _
  rintro (i | i)
  · simpa [auxiliaryRepresentation] using RepresentationTheory.FiniteField.AuxiliaryRepresentations.simple_auxiliaryRepresentation p n hn i
  · simpa [auxiliaryRepresentation] using RepresentationTheory.GaloisFieldCharacters.GaloisField.simple_fdRepOfAuxiliaryIndex p n hp2 i

/-- Representations indexed by the two displayed sum components are not isomorphic. -/
theorem auxiliaryRepresentation_sumComponents_nonisomorphic
    (hp2 : p ≠ 2) (hn : n ≠ 0)
    (i : RepresentationTheory.FiniteField.AuxiliaryRepresentations.AuxiliaryRepresentationIndex p n) (j : AuxiliaryIndexFamily p n hn) :
    ¬ Nonempty (auxiliaryRepresentation p n hp2 hn (.inl i) ≅
      auxiliaryRepresentation p n hp2 hn (.inr j)) := by
  classical
  letI : NeZero n := ⟨hn⟩
  letI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) :=
    Fintype.ofFinite _
  rintro ⟨e⟩
  have hdim := RepresentationTheory.FiniteField.AuxiliaryRepresentations.finrank_eq_of_iso e
  rw [show auxiliaryRepresentation p n hp2 hn (.inl i) = RepresentationTheory.FiniteField.AuxiliaryRepresentations.AuxiliaryRepresentation p n i by
      simp [auxiliaryRepresentation],
    show auxiliaryRepresentation p n hp2 hn (.inr j) = RepresentationTheory.GaloisFieldCharacters.GaloisField.fdRepOfAuxiliaryIndex p n hp2 j by
      simp [auxiliaryRepresentation],
    RepresentationTheory.FiniteField.AuxiliaryRepresentations.finrank_auxiliaryRepresentation p n hn i,
    RepresentationTheory.GaloisFieldCharacters.GaloisField.finrank_fdRepOfAuxiliaryIndex p n hp2 j] at hdim
  have hpprime : Nat.Prime p := Fact.out
  have hp3 : 3 ≤ p := (hpprime.two_le.lt_or_eq.resolve_right hp2.symm).succ_le
  have hq3 : 3 ≤ p ^ n := hp3.trans (Nat.le_pow (Nat.pos_of_ne_zero hn))
  rcases i with i | i
  · simp at hdim
    omega
  · rcases i with i | i
    · simp at hdim
      omega
    · simp at hdim
      omega

/-- Isomorphic representations in the indexed family have equal indices. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := primary),
  source_ref "Chapter5/Discussion_complementary_series_summary/Derived01" (role := supporting)]
theorem auxiliaryRepresentation_iso_injective (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∀ i j : AuxiliaryIndexType p n hn,
      Nonempty (auxiliaryRepresentation p n hp2 hn i ≅ auxiliaryRepresentation p n hp2 hn j) →
        i = j := by
  classical
  letI : NeZero n := ⟨hn⟩
  letI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) :=
    Fintype.ofFinite _
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (RepresentationTheory.FiniteField.AuxiliaryRepresentations.eq_of_auxiliaryRepresentation_iso p n hn i j h)
  · exact absurd h (auxiliaryRepresentation_sumComponents_nonisomorphic p n hp2 hn i j)
  · exact absurd (Nonempty.map Iso.symm h)
      (auxiliaryRepresentation_sumComponents_nonisomorphic p n hp2 hn j i)
  · apply congrArg Sum.inr
    apply RepresentationTheory.GaloisFieldCharacters.GaloisField.eq_of_fdRepOfAuxiliaryIndex_iso p n hp2 i j
    simpa [auxiliaryRepresentation] using h

/-- Computes the cardinality of the auxiliary index type. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := primary),
  source_ref "Chapter5/Discussion_complementary_series_summary/Derived01" (role := supporting)]
theorem card_auxiliaryIndexType (hn : n ≠ 0) :
    Nat.card (AuxiliaryIndexType p n hn) =
      (Fintype.card (GaloisField p n) - 1)
        + Fintype.card (GaloisField p n) *
            (Fintype.card (GaloisField p n) - 1) / 2
        + Fintype.card (GaloisField p n) *
            (Fintype.card (GaloisField p n) - 1) / 2 := by
  letI : NeZero n := ⟨hn⟩
  rw [Nat.card_sum, RepresentationTheory.FiniteField.AuxiliaryRepresentations.card_auxiliaryRepresentationIndex p n hn,
    RepresentationTheory.GaloisFieldCharacters.GaloisField.natCard_auxiliaryIndex p n, ← Nat.card_eq_fintype_card,
    GaloisField.card p n hn]

/-- Every simple representation is isomorphic to a unique member of the indexed family. -/
@[source_ref "Chapter5/Discussion_complementary_series_summary" (role := primary),
  source_ref "Chapter5/Discussion_complementary_series_summary/Derived01" (role := supporting)]
theorem existsUnique_auxiliaryRepresentation_iso (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∀ U : FDRep ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)), Simple U →
      ∃! i : AuxiliaryIndexType p n hn,
        Nonempty (U ≅ auxiliaryRepresentation p n hp2 hn i) := by
  classical
  letI : NeZero n := ⟨hn⟩
  letI : Fintype (AuxiliaryIndexType p n hn) := Fintype.ofFinite _
  let e := Fintype.equivFin (AuxiliaryIndexType p n hn)
  let W : Fin (Fintype.card (AuxiliaryIndexType p n hn)) →
      FDRep ℂ (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) :=
    fun j => auxiliaryRepresentation p n hp2 hn (e.symm j)
  have hWsimple : ∀ j, Simple (W j) := by
    intro j
    exact auxiliaryRepresentation_simple p n hp2 hn (e.symm j)
  have hWnoniso : ∀ i j, Nonempty (W i ≅ W j) → i = j := by
    intro i j hij
    apply e.symm.injective
    exact auxiliaryRepresentation_iso_injective p n hp2 hn (e.symm i) (e.symm j) hij
  have hcard : Fintype.card (AuxiliaryIndexType p n hn) =
      (Fintype.card (GaloisField p n) - 1)
        + Fintype.card (GaloisField p n) *
            (Fintype.card (GaloisField p n) - 1) / 2
        + Fintype.card (GaloisField p n) *
            (Fintype.card (GaloisField p n) - 1) / 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_auxiliaryIndexType p n hn
  intro U hU
  obtain ⟨j, hj⟩ := simple_isIso_of_complete_family p n hp2 hn W hWsimple hWnoniso hcard U hU
  refine ⟨e.symm j, hj, ?_⟩
  intro i hi
  apply auxiliaryRepresentation_iso_injective p n hp2 hn i (e.symm j)
  exact ⟨hi.some.symm ≪≫ hj.some⟩

end GaloisField

end RepresentationTheory.GeneralLinearGroupTwoIrreps
