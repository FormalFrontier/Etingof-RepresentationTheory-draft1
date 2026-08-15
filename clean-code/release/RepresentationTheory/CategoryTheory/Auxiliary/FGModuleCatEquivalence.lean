/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.FiniteAlgebraCandidates
import RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence
import RepresentationTheory.CategoryTheory.Abelian.FiniteLength
import RepresentationTheory.CategoryTheory.Projective.Auxiliary
import RepresentationTheory.RingTheory.ElementProperties
import RepresentationTheory.ModuleCat.FiniteUnderEquivalence

/-! # Finitely generated module category equivalences -/

open CategoryTheory

universe v u

namespace RepresentationTheory.CategoryTheory.Auxiliary.FGModuleCatEquivalence

/-- For a supplied object, produces the displayed auxiliary data and an equivalence with finitely generated modules over its opposite endomorphism ring. -/
theorem exists_auxiliary_fgModuleCat_equivalence_of_opposite_end_of_object
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [Linear k C]
    [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
    (P : C) [hp : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P] :
    ∃ (B : Type v) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧
        Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) ∧
          RepresentationTheory.RingAuxiliary.RingAuxiliary (End P)ᵐᵒᵖ B := by

  haveI : FiniteDimensional k (End P) :=
    @RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory.finiteDimensional_hom k _ C _ _ _ _ P P
  haveI : Module.Finite k (End P)ᵐᵒᵖ := inferInstance

  have hcat : Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) :=
    RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence.nonempty_fgModuleEquivalence (k := k) C P

  obtain ⟨B, instR, instA, instF, hbasic, hmor⟩ :=
    RepresentationTheory.RingTheory.ElementProperties.exists_nested_witnesses_with_two_conditions k (End P)ᵐᵒᵖ
  exact ⟨B, instR, instA, instF, hbasic, hcat, hmor⟩

/-- Produces the displayed auxiliary data, including an equivalence with finitely generated modules over the opposite endomorphism ring of a constructed object. -/
theorem exists_auxiliary_fgModuleCat_equivalence_of_opposite_end
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [Linear k C]
    [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C] :
    ∃ (P : C) (_ : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P) (B : Type v) (_ : Ring B) (_ : Algebra k B)
        (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧
        Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) ∧
          RepresentationTheory.RingAuxiliary.RingAuxiliary (End P)ᵐᵒᵖ B := by

  obtain ⟨P, ⟨hp⟩⟩ := RepresentationTheory.CategoryTheory.Projective.Auxiliary.exists_object_with_nonempty_auxiliary C
  haveI : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P := hp
  obtain ⟨B, instR, instA, instF, hbasic, hcat, hmor⟩ :=
    exists_auxiliary_fgModuleCat_equivalence_of_opposite_end_of_object (k := k) C P
  exact ⟨P, hp, B, instR, instA, instF, hbasic, hcat, hmor⟩

/-- For a supplied object with the stated auxiliary instance, constructs a displayed-predicate type whose finite-module category is equivalent to the given category. -/
theorem exists_auxiliary_fgModuleCat_equivalence_of_object
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [Linear k C]
    [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
    (P : C) [hp : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P] :
    ∃ (B : Type v) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧ Nonempty (C ≌ FGModuleCat.{v} B) := by
  haveI : FiniteDimensional k (End P) :=
    @RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory.finiteDimensional_hom k _ C _ _ _ _ P P
  haveI : Module.Finite k (End P)ᵐᵒᵖ := inferInstance
  have hcat : Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) :=
    RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence.nonempty_fgModuleEquivalence (k := k) C P
  obtain ⟨B, instR, instA, instF, hbasic, hmor⟩ :=
    RepresentationTheory.RingTheory.ElementProperties.exists_nested_witnesses_with_two_conditions k (End P)ᵐᵒᵖ
  obtain ⟨eFG⟩ := RepresentationTheory.RingAuxiliary.RingAuxiliary.exists_fgModuleCatEquivalence hmor
  obtain ⟨eC⟩ := hcat
  exact ⟨B, instR, instA, instF, hbasic, ⟨eC.trans eFG⟩⟩

/-- Constructs a type satisfying the displayed predicate and an equivalence from the given category to finitely generated modules over that type. -/
theorem exists_auxiliary_fgModuleCat_equivalence
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [Linear k C]
    [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C] :
    ∃ (B : Type v) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧ Nonempty (C ≌ FGModuleCat.{v} B) := by
  obtain ⟨P, ⟨hp⟩⟩ := RepresentationTheory.CategoryTheory.Projective.Auxiliary.exists_object_with_nonempty_auxiliary C
  haveI : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P := hp
  exact exists_auxiliary_fgModuleCat_equivalence_of_object (k := k) C P

/-- For a supplied object, constructs auxiliary data with the displayed module-category equivalence, finrank inequality, and comparison property. -/
theorem exists_auxiliary_fgModuleCat_base_with_finrank_bound_of_object
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [Linear k C]
    [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
    (P : C) [hp : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P] :
    ∃ (B : Type v) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{v, v, v} k B ∧
        RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧
          Nonempty (C ≌ FGModuleCat.{v} B) ∧
            RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k (End P)ᵐᵒᵖ B ∧
              Module.finrank k B ≤ Module.finrank k (End P)ᵐᵒᵖ ∧
                ∀ (B' : Type v) (_ : Ring B') (_ : Algebra k B') (_ : Module.Finite k B'),
                  RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B' →
                  RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k (End P)ᵐᵒᵖ B' →
                    Nonempty (B' ≃ₐ[k] B) := by
  haveI : FiniteDimensional k (End P) :=
    @RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory.finiteDimensional_hom k _ C _ _ _ _ P P
  haveI : Module.Finite k (End P)ᵐᵒᵖ := inferInstance

  obtain ⟨eC⟩ := RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence.nonempty_fgModuleEquivalence (k := k) C P

  obtain ⟨B, instR, instA, instF, hsplit, hbasic, hmor, hdim, huniq⟩ :=
    RepresentationTheory.Auxiliary.FiniteAlgebraCandidates.Auxiliary.exists_type_with_three_conditions_finrank_le_and_unique k (End P)ᵐᵒᵖ

  obtain ⟨eFG⟩ := RepresentationTheory.RingAuxiliary.RingAuxiliary.exists_fgModuleCatEquivalence
    (RepresentationTheory.RingAuxiliary.AlgebraAuxiliary.toRingAuxiliary hmor)
  exact ⟨B, instR, instA, instF, hsplit, hbasic, ⟨eC.trans eFG⟩, hmor, hdim, huniq⟩

/-- Constructs auxiliary data with the stated finite-module equivalence, relation, finrank bound, and algebra-equivalence comparison property. -/
theorem exists_auxiliary_fgModuleCat_base_with_finrank_bound
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [Linear k C]
    [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C] :
    ∃ (P : C) (_ : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P) (B : Type v) (_ : Ring B) (_ : Algebra k B)
        (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{v, v, v} k B ∧
        RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧
          Nonempty (C ≌ FGModuleCat.{v} B) ∧
            RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k (End P)ᵐᵒᵖ B ∧
              Module.finrank k B ≤ Module.finrank k (End P)ᵐᵒᵖ ∧
                ∀ (B' : Type v) (_ : Ring B') (_ : Algebra k B') (_ : Module.Finite k B'),
                  RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B' →
                  RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k (End P)ᵐᵒᵖ B' →
                    Nonempty (B' ≃ₐ[k] B) := by
  obtain ⟨P, ⟨hp⟩⟩ := RepresentationTheory.CategoryTheory.Projective.Auxiliary.exists_object_with_nonempty_auxiliary C
  haveI : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P := hp
  obtain ⟨B, instR, instA, instF, hsplit, hbasic, hequiv, hmor, hdim, huniq⟩ :=
    exists_auxiliary_fgModuleCat_base_with_finrank_bound_of_object (k := k) C P
  exact ⟨P, hp, B, instR, instA, instF, hsplit, hbasic, hequiv, hmor, hdim, huniq⟩

/-- For a finite algebra over the field, constructs a type carrying the displayed predicate and related to the input by the stated auxiliary condition. -/
theorem exists_auxiliary_type_with_related_type
    {k : Type v} [Field k] [IsAlgClosed k]
    (A : Type v) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (B : Type v) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧ RepresentationTheory.RingAuxiliary.RingAuxiliary' A B := by
  obtain ⟨B, instR, instA, instF, hbasic, hmor⟩ := RepresentationTheory.Auxiliary.FiniteAlgebraCandidates.Auxiliary.exists_type_with_two_conditions k A
  exact ⟨B, instR, instA, instF, hbasic,
    RepresentationTheory.RingAuxiliary.RingAuxiliary.toAuxiliaryRingProperty hmor⟩

end RepresentationTheory.CategoryTheory.Auxiliary.FGModuleCatEquivalence
