/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import RepresentationTheory.HomologicalComplexShortExactHomology
import Mathlib
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

/-!
# Homology sequences of subcomplexes

This file constructs the degreewise quotient of a differential-stable family of submodules and
also gives the abstract formulation for an arbitrary short exact sequence of complexes.
-/

open CategoryTheory

namespace RepresentationTheory.SubcomplexHomologySequence

/-- The type of integer-indexed cochain complexes of integer modules used by this construction. -/
abbrev IntCochainComplex :=
  HomologicalComplex (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)

/-- A degreewise family of submodules of a cochain complex that is preserved by its differential. -/
structure Subcomplex (D : IntCochainComplex) where
  /-- The submodule selected by a subcomplex in a specified degree. -/
  degreeSubmodule : (i : ℤ) → Submodule ℤ (D.X i)
  /-- The differential sends every element of a degree submodule into the degree submodule at the
  target index. -/
  d_mem : ∀ {i j : ℤ} {x : D.X i}, x ∈ degreeSubmodule i → D.d i j x ∈ degreeSubmodule j

namespace Subcomplex

variable {D : IntCochainComplex} (C : Subcomplex D)

/-- Returns the ambient cochain complex used between a subcomplex and its quotient. -/
def ambientComplex (D : IntCochainComplex) : IntCochainComplex where
  X i := @ModuleCat.of ℤ Int.instRing (D.X i) (D.X i).isAddCommGroup
    (AddCommGroup.toIntModule (D.X i))
  d i j := @ModuleCat.ofHom ℤ Int.instRing (D.X i) (D.X j)
    (D.X i).isAddCommGroup (AddCommGroup.toIntModule (D.X i))
    (D.X j).isAddCommGroup (AddCommGroup.toIntModule (D.X j))
    (D.d i j).hom.toAddMonoidHom.toIntLinearMap
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simpa using ConcreteCategory.congr_hom (D.shape i j hij) x
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change D.d j k (D.d i j x) = 0
    rw [← ConcreteCategory.comp_apply, D.d_comp_d]
    rfl

/-- Builds the cochain complex carried by the differential-stable degreewise submodules. -/
def subcomplex : IntCochainComplex where
  X i := ModuleCat.of ℤ (C.degreeSubmodule i)
  d i j := ModuleCat.ofHom <| (AddMonoidHom.mk'
    (fun x : C.degreeSubmodule i ↦
      (⟨D.d i j x, C.d_mem x.property⟩ : C.degreeSubmodule j))
    (by intro x y; ext; simp)).toIntLinearMap
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [D.shape i j hij]
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change D.d j k (D.d i j x) = 0
    rw [← ConcreteCategory.comp_apply, D.d_comp_d]
    rfl

/-- The cochain map from the subcomplex into its ambient complex. -/
def inclusionHom : C.subcomplex ⟶ ambientComplex D where
  f i := @ModuleCat.ofHom ℤ Int.instRing (C.degreeSubmodule i) (D.X i)
    (C.degreeSubmodule i).addCommGroup (AddCommGroup.toIntModule (C.degreeSubmodule i))
    (D.X i).isAddCommGroup (AddCommGroup.toIntModule (D.X i)) <|
      (AddMonoidHom.mk' (fun x : C.degreeSubmodule i ↦ (x : D.X i)) (by simp)).toIntLinearMap
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Forms the degreewise quotient of the ambient complex by the chosen subcomplex. -/
def quotientComplex : IntCochainComplex where
  X i := ModuleCat.of ℤ (D.X i ⧸ (C.degreeSubmodule i).toAddSubgroup)
  d i j := ModuleCat.ofHom <| (QuotientAddGroup.map (C.degreeSubmodule i).toAddSubgroup
    (C.degreeSubmodule j).toAddSubgroup (D.d i j).hom.toAddMonoidHom <| by
    intro x hx
    exact C.d_mem hx).toIntLinearMap
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using Quotient.inductionOn' with
    | _ x =>
    simp [D.shape i j hij]
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using Quotient.inductionOn' with
    | _ x =>
      have hd : D.d j k (D.d i j x) = 0 := by
        rw [← ConcreteCategory.comp_apply, D.d_comp_d]
        rfl
      simp [hd]

/-- The cochain map from the ambient complex to the quotient complex. -/
def quotientHom : ambientComplex D ⟶ C.quotientComplex where
  f i := @ModuleCat.ofHom ℤ Int.instRing (D.X i)
    (D.X i ⧸ (C.degreeSubmodule i).toAddSubgroup)
    (D.X i).isAddCommGroup (AddCommGroup.toIntModule (D.X i))
    (QuotientAddGroup.Quotient.addCommGroup (C.degreeSubmodule i).toAddSubgroup)
    (AddCommGroup.toIntModule (D.X i ⧸ (C.degreeSubmodule i).toAddSubgroup)) <|
      (QuotientAddGroup.mk' (C.degreeSubmodule i).toAddSubgroup).toIntLinearMap
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- The short complex consisting of the subcomplex, the ambient complex, and the quotient
complex. -/
def subcomplexQuotientSequence : ShortComplex IntCochainComplex :=
  ShortComplex.mk C.inclusionHom C.quotientHom (by
    ext i x
    change C.degreeSubmodule i at x
    change QuotientAddGroup.mk' (C.degreeSubmodule i).toAddSubgroup (x : D.X i) = 0
    rw [QuotientAddGroup.mk'_apply]
    exact (QuotientAddGroup.eq_zero_iff (x : D.X i)).mpr x.property)

/-- The subcomplex-to-ambient-to-quotient short complex is short exact. -/
theorem subcomplexQuotientSequence_shortExact : C.subcomplexQuotientSequence.ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact
      (fun x : C.degreeSubmodule i ↦ (x : D.X i))
      (QuotientAddGroup.mk' (C.degreeSubmodule i).toAddSubgroup)
    intro x
    change QuotientAddGroup.mk' (C.degreeSubmodule i).toAddSubgroup x = 0 ↔
      x ∈ Set.range (fun y : C.degreeSubmodule i ↦ (y : D.X i))
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property
  · intro x y h
    exact Subtype.ext h
  · exact QuotientAddGroup.mk'_surjective _

/-- If the projected differential vanishes in the quotient complex, then the original differential
belongs to the target degree submodule. -/
theorem d_mem_of_quotientMap_d_eq_zero (i j : ℤ) (x : D.X i)
    (hx : C.quotientComplex.d i j (C.quotientHom.f i x) = 0) :
    D.d i j x ∈ C.degreeSubmodule j := by
  change QuotientAddGroup.map (C.degreeSubmodule i).toAddSubgroup
    (C.degreeSubmodule j).toAddSubgroup
    (D.d i j).hom.toAddMonoidHom (by intro y hy; exact C.d_mem hy)
      (QuotientAddGroup.mk' (C.degreeSubmodule i).toAddSubgroup x) = 0 at hx
  rw [QuotientAddGroup.map_mk'] at hx
  exact (QuotientAddGroup.eq_zero_iff (D.d i j x)).mp hx

/-- Regards the differential of a quotient cocycle representative as an element of the target
degree submodule. -/
def dToDegreeSubmodule (i j : ℤ) (x : D.X i)
    (hx : C.quotientComplex.d i j (C.quotientHom.f i x) = 0) : C.degreeSubmodule j :=
  ⟨D.d i j x, C.d_mem_of_quotientMap_d_eq_zero i j x hx⟩

/-- The quotient-complex homology class determined by a representative whose projected
differential vanishes. -/
noncomputable def quotientHomologyClass (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j)
    (x : D.X i) (hx : C.quotientComplex.d i j (C.quotientHom.f i x) = 0) :
    C.quotientComplex.homology i :=
  C.quotientComplex.homologyπ i
    (C.quotientComplex.cyclesMk (C.quotientHom.f i x) j
      ((ComplexShape.up ℤ).next_eq' hij) hx)

/-- The subcomplex homology class represented by the differential of a lifted quotient cocycle. -/
noncomputable def boundaryHomologyClass (i j : ℤ)
    (x : D.X i) (hx : C.quotientComplex.d i j (C.quotientHom.f i x) = 0)
    (k : ℤ) (hk : (ComplexShape.up ℤ).next j = k) : C.subcomplex.homology j :=
  C.subcomplex.homologyπ j
    (C.subcomplex.cyclesMk (C.dToDegreeSubmodule i j x hx) k hk
      (C.subcomplexQuotientSequence_shortExact.d_eq_zero_of_f_eq_d_apply i j x
        (C.dToDegreeSubmodule i j x hx) rfl k))

/-- The connecting morphism from quotient homology in one degree to subcomplex homology in an
adjacent degree. -/
@[source_ref "Chapter7/Problem7.8.5" (role := supporting)]
noncomputable def connectingHom (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    C.quotientComplex.homology i ⟶ C.subcomplex.homology j :=
  C.subcomplexQuotientSequence_shortExact.δ i j hij

/-- Evaluating the connecting morphism on the quotient class of a cocycle gives the homology class
of its lifted differential. -/
theorem connectingHom_apply_quotientHomologyClass (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j)
    (x : D.X i) (hx : C.quotientComplex.d i j (C.quotientHom.f i x) = 0)
    (k : ℤ) (hk : (ComplexShape.up ℤ).next j = k) :
    C.connectingHom i j hij (C.quotientHomologyClass i j hij x hx) =
      C.boundaryHomologyClass i j x hx k hk := by
  simpa [connectingHom, quotientHomologyClass, boundaryHomologyClass,
    subcomplexQuotientSequence, quotientHom, inclusionHom, ambientComplex, subcomplex,
    dToDegreeSubmodule] using
    C.subcomplexQuotientSequence_shortExact.δ_apply i j hij (C.quotientHom.f i x) hx x rfl
      (C.dToDegreeSubmodule i j x hx) rfl k hk

/-- Representatives defining the same quotient homology class have equal lifted-differential
homology classes. -/
@[source_ref "Chapter7/Problem7.8.5" (role := supporting)]
theorem boundaryHomologyClass_eq_of_quotientHomologyClass_eq (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j)
    (x y : D.X i)
    (hx : C.quotientComplex.d i j (C.quotientHom.f i x) = 0)
    (hy : C.quotientComplex.d i j (C.quotientHom.f i y) = 0)
    (k : ℤ) (hk : (ComplexShape.up ℤ).next j = k)
    (hxy : C.quotientHomologyClass i j hij x hx =
      C.quotientHomologyClass i j hij y hy) :
    C.boundaryHomologyClass i j x hx k hk =
      C.boundaryHomologyClass i j y hy k hk := by
  rw [← C.connectingHom_apply_quotientHomologyClass i j hij x hx k hk,
    ← C.connectingHom_apply_quotientHomologyClass i j hij y hy k hk, hxy]

/-- Two representatives with the same image in the quotient complex determine the same
lifted-differential homology class. -/
@[source_ref "Chapter7/Problem7.8.5" (role := supporting)]
theorem boundaryHomologyClass_eq_of_quotientMap_eq (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) (x y : D.X i)
    (hx : C.quotientComplex.d i j (C.quotientHom.f i x) = 0)
    (hy : C.quotientComplex.d i j (C.quotientHom.f i y) = 0)
    (hproj : C.quotientHom.f i x = C.quotientHom.f i y)
    (k : ℤ) (hk : (ComplexShape.up ℤ).next j = k) :
    C.boundaryHomologyClass i j x hx k hk =
      C.boundaryHomologyClass i j y hy k hk := by
  apply C.boundaryHomologyClass_eq_of_quotientHomologyClass_eq i j hij x y hx hy k hk
  unfold quotientHomologyClass
  congr 2

/-- Identifies the explicitly constructed connecting morphism with the canonical connecting
morphism of the associated short exact complex. -/
theorem connectingHom_eq_delta (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    C.connectingHom i j hij = C.subcomplexQuotientSequence_shortExact.δ i j hij :=
  rfl

end Subcomplex

/-- The connecting morphism from the homology of the third complex to that of the first complex in
adjacent degrees. -/
noncomputable def connectingHom
    {S : ShortComplex IntCochainComplex}
    (hS : S.ShortExact) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  hS.δ i j hij

/-- Establishes exactness at three consecutive homology objects associated with a short exact
complex and adjacent integer degrees. -/
theorem shortExact_homologySequence_exact
    {S : ShortComplex IntCochainComplex}
    (hS : S.ShortExact) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact ∧
    (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i)
      (by rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact ∧
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact :=
  ⟨hS.homology_exact₁ i j hij, hS.homology_exact₂ i, hS.homology_exact₃ i j hij⟩

/-- Establishes exactness of the three consecutive parts of the homology sequence built from a
subcomplex and its quotient. -/
theorem subcomplex_homologySequence_exact
    {D : IntCochainComplex} (C : Subcomplex D)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (ShortComplex.mk (C.connectingHom i j hij)
      (HomologicalComplex.homologyMap C.subcomplexQuotientSequence.f j)
      (by simp [Subcomplex.connectingHom,
        ShortComplex.ShortExact.δ_comp C.subcomplexQuotientSequence_shortExact i j hij])).Exact ∧
    (ShortComplex.mk (HomologicalComplex.homologyMap C.subcomplexQuotientSequence.f i)
      (HomologicalComplex.homologyMap C.subcomplexQuotientSequence.g i)
      (by rw [← HomologicalComplex.homologyMap_comp, C.subcomplexQuotientSequence.zero,
          HomologicalComplex.homologyMap_zero])).Exact ∧
    (ShortComplex.mk (HomologicalComplex.homologyMap C.subcomplexQuotientSequence.g i)
      (C.connectingHom i j hij)
      (by simp [Subcomplex.connectingHom,
        ShortComplex.ShortExact.comp_δ
          C.subcomplexQuotientSequence_shortExact i j hij])).Exact := by
  simpa [Subcomplex.connectingHom] using
    shortExact_homologySequence_exact C.subcomplexQuotientSequence_shortExact i j hij

end RepresentationTheory.SubcomplexHomologySequence

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.SubcomplexHomologySequence.Auxiliary.statement013193 := _root_.RepresentationTheory.SubcomplexHomologySequence.shortExact_homologySequence_exact

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.SubcomplexHomologySequence.Auxiliary.statement013257 := _root_.RepresentationTheory.SubcomplexHomologySequence.subcomplex_homologySequence_exact

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.SubcomplexHomologySequence.Subcomplex.Auxiliary.statement013213 := _root_.RepresentationTheory.SubcomplexHomologySequence.Subcomplex.connectingHom_eq_delta

attribute [source_ref "Chapter7/Problem7.8.5" (role := primary)] _root_.RepresentationTheory.SubcomplexHomologySequence.Auxiliary.statement013193

attribute [source_ref "Chapter7/Problem7.8.5" (role := primary)] _root_.RepresentationTheory.SubcomplexHomologySequence.Auxiliary.statement013257

attribute [source_ref "Chapter7/Problem7.8.5" (role := supporting)] _root_.RepresentationTheory.SubcomplexHomologySequence.Subcomplex.Auxiliary.statement013213
