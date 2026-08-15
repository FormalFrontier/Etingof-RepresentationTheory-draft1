/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import RepresentationTheory.Algebra.FiniteDimensional.FGModuleCategory
import RepresentationTheory.ProjectiveDimension
import RepresentationTheory.AuxiliaryProjectiveResolution
import RepresentationTheory.CategoryTheory.ProjectiveResolution.ShortComplex
import RepresentationTheory.Alignment.Attribute

/-!
# Abelian projective-dimension results

This module relates projective-dimension bounds to higher Ext groups and develops finite
projective resolutions from those bounds.
-/

universe u

open CategoryTheory
open scoped ModuleCat

namespace RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension

variable (R : Type u) [Ring R]

/-- Characterizes a projective-dimension bound by subsingleton higher Ext groups. -/
@[source_ref "Chapter9/Problem9.4.2" (role := primary)]
theorem hasProjectiveDimensionLE_iff_ext_subsingleton (M : ModuleCat.{u} R) (d : ℕ) :
    HasProjectiveDimensionLE M d ↔
      ∀ (N : ModuleCat.{u} R) (i : ℕ), d < i → Subsingleton (Abelian.Ext M N i) := by
  constructor
  · intro h N i hi
    haveI : HasProjectiveDimensionLT M (d + 1) := h
    exact HasProjectiveDimensionLT.subsingleton M (d + 1) i (by omega) N
  · intro h
    apply HasProjectiveDimensionLT.mk
    intro i hi Y e
    exact (h Y i (by omega)).elim e 0

/--
For a short exact complex with projective middle object and no splitting, identifies the value at
the third object with the value at the first object plus one. -/
@[source_ref "Chapter9/Problem9.4.2" (role := primary)]
theorem
    right_endpoint_value_eq_left_endpoint_value_add_one_of_shortExact_of_projective_middle_of_no_splitting
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hP : Projective S.X₂) (hns : IsEmpty S.Splitting) :
    RepresentationTheory.ProjectiveDimension.projectiveDimension R S.X₃ =
      RepresentationTheory.ProjectiveDimension.projectiveDimension R S.X₁ + 1 := by
  haveI : Projective S.X₂ := hP
  have hX3proj : ¬ Projective S.X₃ := fun h => by
    haveI := h; exact hns.false hS.splittingOfProjective
  have hX3ne : ¬ Limits.IsZero S.X₃ := fun h => hX3proj h.projective
  have hX1ne : ¬ Limits.IsZero S.X₁ := fun h => by
    haveI := h.injective; exact hns.false hS.splittingOfInjective
  rw [RepresentationTheory.ProjectiveDimension.projectiveDimension_eq_projectiveDimensionAux
      S.X₃ hX3ne,
    RepresentationTheory.ProjectiveDimension.projectiveDimension_eq_projectiveDimensionAux
      S.X₁ hX1ne]
  change CategoryTheory.projectiveDimension S.X₃ = CategoryTheory.projectiveDimension S.X₁ + 1
  have aux (n : ℕ) : CategoryTheory.projectiveDimension S.X₃ ≤ (n : WithBot ℕ∞) ↔
      CategoryTheory.projectiveDimension S.X₁ + 1 ≤ (n : WithBot ℕ∞) := by
    match n with
    | 0 =>
      rw [CategoryTheory.projectiveDimension_le_iff, ← projective_iff_hasProjectiveDimensionLE_zero,
        Nat.cast_zero, ENat.WithBot.add_one_le_zero_iff, projectiveDimension_eq_bot_iff]
      exact iff_of_false hX3proj hX1ne
    | n + 1 =>
      nth_rw 2 [← Nat.cast_one, Nat.cast_add]
      simp only [ENat.WithBot.add_le_add_natCast_right_iff,
        CategoryTheory.projectiveDimension_le_iff]
      exact hS.hasProjectiveDimensionLT_X₃_iff n hP
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff, WithBot.add_eq_bot, WithBot.one_ne_bot,
      or_false]
    exact iff_of_false hX3ne hX1ne
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

/--
Decreases a projective-dimension bound along a short exact complex with projective middle object.
-/
theorem hasProjectiveDimensionLE_pred_of_shortExact_of_projective_middle
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hP : Projective S.X₂) (d : ℕ) (hd : 0 < d)
    (hM : HasProjectiveDimensionLE S.X₃ d) :
    HasProjectiveDimensionLE S.X₁ (d - 1) := by
  haveI : Projective S.X₂ := hP
  haveI : HasProjectiveDimensionLT S.X₂ d :=
    hasProjectiveDimensionLT_of_ge S.X₂ 1 d hd
  have h : HasProjectiveDimensionLT S.X₁ d :=
    hS.hasProjectiveDimensionLT_X₁ d inferInstance hM
  change HasProjectiveDimensionLT S.X₁ (d - 1 + 1)
  rwa [Nat.sub_add_cancel hd]

open RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData in
/-- Shows that the resolution object at a bounded projective dimension is projective. -/
@[source_ref "Chapter9/Problem9.4.2" (role := primary)]
theorem projectiveResolution_object_projective_of_hasProjectiveDimensionLE
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M) (d : ℕ)
    (hM : HasProjectiveDimensionLE M d) :
    Projective (stage_object P d) := by
  have key : ∀ n, n ≤ d → HasProjectiveDimensionLE (stage_object P n) (d - n) := by
    intro n
    induction n with
    | zero => intro _; simpa using hM
    | succ n ih =>
      intro hn
      have hpos : 0 < d - n := by omega
      have hstep := hasProjectiveDimensionLE_pred_of_shortExact_of_projective_middle R
        (stage_short_complex P n) (stage_short_complex_short_exact P n) inferInstance
        (d - n) hpos (by rw [stage_short_complex_X3]; exact ih (by omega))
      simpa only [stage_short_complex_X1, Nat.sub_sub] using hstep
  have hd0 := key d (le_refl d)
  rw [Nat.sub_self] at hd0
  rw [projective_iff_hasProjectiveDimensionLE_zero]
  exact hd0

open RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData in
/--
Provides projectivity and the exact-resolution structure at a degree bounding projective
dimension. -/
@[source_ref "Chapter9/Problem9.4.2" (role := primary)]
theorem projectiveResolution_structure_of_hasProjectiveDimensionLE
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M) (d : ℕ)
    (hM : HasProjectiveDimensionLE M d) :
    Projective (stage_object P d) ∧ stage_object P 0 = M ∧
      ∀ n, (stage_short_complex P n).ShortExact :=
  ⟨projectiveResolution_object_projective_of_hasProjectiveDimensionLE R M P d hM,
    stage_object_zero P, stage_short_complex_short_exact P⟩

open RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData in
/--
Establishes finiteness of the auxiliary objects of a projective resolution when its complex terms
are finite. -/
theorem projectiveResolution_finite_auxiliaryObjects_of_finite_complexTerms
    [IsNoetherianRing R]
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (hM : Module.Finite R ↥M) (hP : ∀ n, Module.Finite R ↥(P.complex.X n)) :
    ∀ n, Module.Finite R ↥(stage_object P n) := by
  intro n
  induction n with
  | zero => exact hM
  | succ n ih =>
    haveI : Module.Finite R ↥((stage_short_complex P n).X₂) := by
      rw [stage_short_complex_X2]; exact hP n
    have hinj : Function.Injective (stage_short_complex P n).f :=
      (ModuleCat.mono_iff_injective _).1 (stage_short_complex_short_exact P n).mono_f
    have hfin : Module.Finite R ↥(stage_object P (n + 1)) := by
      change Module.Finite R ↥((stage_short_complex P n).X₁)
      exact Module.Finite.of_injective (stage_short_complex P n).f.hom hinj
    exact hfin

open RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData in
/--
Packages projectivity, finiteness, and exactness properties of a finite projective resolution at a
bounded degree. -/
theorem finite_projectiveResolution_structure_of_hasProjectiveDimensionLE
    [IsNoetherianRing R]
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (hM : Module.Finite R ↥M) (hP : ∀ n, Module.Finite R ↥(P.complex.X n))
    (d : ℕ) (hd : HasProjectiveDimensionLE M d) :
    Projective (stage_object P d) ∧
      (∀ n, Module.Finite R ↥(stage_object P n)) ∧
      stage_object P 0 = M ∧ ∀ n, (stage_short_complex P n).ShortExact :=
  ⟨projectiveResolution_object_projective_of_hasProjectiveDimensionLE R M P d hd,
    projectiveResolution_finite_auxiliaryObjects_of_finite_complexTerms R M P hM hP,
    stage_object_zero P, stage_short_complex_short_exact P⟩

/--
Shows that a module finite over a finite algebra is finite over the base commutative ring. -/
theorem moduleFinite_over_base_of_moduleFinite_over_algebra
    {k : Type*} [CommRing k] [Algebra k R]
    [Module.Finite k R] (N : Type*) [AddCommGroup N] [Module R N] [Module k N]
    [IsScalarTower k R N] [Module.Finite R N] : Module.Finite k N :=
  Module.Finite.trans R N

/--
Constructs a projective resolution with finite scalar-restricted terms from a finite module of
bounded projective dimension. -/
@[source_ref "Chapter9/Problem9.4.2" (role := primary)]
theorem exists_finite_projectiveResolution_of_hasProjectiveDimensionLE
    {k : Type u} [Field k] [Algebra k R] [Module.Finite k R]
    (M : ModuleCat.{u} R) [Module k M] [IsScalarTower k R M] [Module.Finite k M]
    (d : ℕ) (hd : HasProjectiveDimensionLE M d) :
    ∃ P : ProjectiveResolution M,
      (∀ n, Module.Finite k ↥(P.complex.X n)) ∧
      Projective
        (RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData.stage_object
          P d) ∧
      Module.Finite k
        ↥(RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData.stage_object
          P d) ∧
      RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData.stage_object
        P 0 = M ∧
      ∀ n,
        (RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData.stage_short_complex
          P n).ShortExact := by
  letI : IsNoetherianRing R :=
    RepresentationTheory.Algebra.FiniteDimensional.FGModuleCategory.isNoetherianRing_of_finiteDimensional
      k R
  letI : Module.Finite R M := Module.Finite.of_restrictScalars_finite k R M
  obtain ⟨P, hP⟩ :=
    RepresentationTheory.AuxiliaryProjectiveResolution.exists_finite_projectiveResolution M
  have hPk : ∀ n, Module.Finite k ↥(P.complex.X n) := by
    intro n
    exact Module.Finite.trans R (P.complex.X n)
  obtain ⟨hproj, hsyzygy, hzero, hses⟩ :=
    finite_projectiveResolution_structure_of_hasProjectiveDimensionLE R M P inferInstance hP d hd
  have htop : Module.Finite k
      ↥(RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData.stage_object
        P d) := by
    letI : Module.Finite R
        ↥(RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData.stage_object
          P d) := hsyzygy d
    exact Module.Finite.trans R
      ↥(RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData.stage_object
        (C := ModuleCat R) P d)
  exact ⟨P, hPk, hproj, htop, hzero, hses⟩

end RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension
