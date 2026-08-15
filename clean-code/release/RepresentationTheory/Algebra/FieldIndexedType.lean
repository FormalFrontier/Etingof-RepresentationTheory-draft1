/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Projective
import RepresentationTheory.RingPredicateBounds
import RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension

/-!
# A type indexed by a field and a natural number

This module develops algebraic and module-theoretic properties of a quotient construction
determined by a field and a natural-number index.
-/

universe u

open Polynomial CategoryTheory

namespace RepresentationTheory.Algebra.FieldIndexedType

variable (k : Type u) [Field k] (n : ℕ)

/-- A type determined by a field and a natural-number index. -/
abbrev fieldNatType : Type u := k[X] ⧸ Ideal.span {(X : k[X]) ^ n}

/-- The designated element of the type indexed by a field and a natural number. -/
noncomputable def fieldNatTypeElement : fieldNatType k n :=
  Ideal.Quotient.mk (Ideal.span {(X : k[X]) ^ n}) X

/-- The index-th power of the designated element is zero. -/
theorem fieldNatTypeElement_pow_eq_zero : (fieldNatTypeElement k n) ^ n = 0 := by
  rw [fieldNatTypeElement, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- For positive indices, the predecessor power of the designated element is nonzero. -/
theorem fieldNatTypeElementPowPred_ne_zero_of_pos (hn : 0 < n) :
    (fieldNatTypeElement k n) ^ (n - 1) ≠ 0 := by
  rw [fieldNatTypeElement, ← map_pow]
  intro h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  have hne : (X : k[X]) ^ (n - 1) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have := Polynomial.natDegree_le_of_dvd h hne
  simp only [Polynomial.natDegree_X_pow] at this
  omega

/--
For positive indices, the kernel of multiplication by the designated element equals the range of
multiplication by its predecessor power. -/
theorem ker_mulLeft_element_eq_range_mulLeft_elementPowPred (hn : 0 < n) :
    LinearMap.ker (LinearMap.mulLeft (fieldNatType k n) (fieldNatTypeElement k n)) =
      LinearMap.range
        (LinearMap.mulLeft (fieldNatType k n) ((fieldNatTypeElement k n) ^ (n - 1))) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [LinearMap.mem_range]
    have hmul : (fieldNatTypeElement k n) *
        (Ideal.Quotient.mk (Ideal.span {(X : k[X]) ^ n}) p) =
        Ideal.Quotient.mk _ (X * p) := by
      rw [fieldNatTypeElement]; exact (map_mul _ _ _).symm
    rw [hmul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
    have hsplit : (X : k[X]) ^ n = X * X ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
    rw [hsplit, mul_dvd_mul_iff_left (Polynomial.X_ne_zero)] at hx
    obtain ⟨q, hq⟩ := hx
    refine ⟨Ideal.Quotient.mk _ q, ?_⟩
    rw [LinearMap.mulLeft_apply, fieldNatTypeElement, ← map_pow, ← map_mul, ← hq]
  · rintro _ ⟨r, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc,
      ← pow_succ', show (n - 1) + 1 = n by omega, fieldNatTypeElement_pow_eq_zero, zero_mul]

/--
For positive indices, the kernel of multiplication by the predecessor power equals the range of
multiplication by the designated element. -/
theorem ker_mulLeft_elementPowPred_eq_range_mulLeft_element (hn : 0 < n) :
    LinearMap.ker
        (LinearMap.mulLeft (fieldNatType k n) ((fieldNatTypeElement k n) ^ (n - 1))) =
      LinearMap.range (LinearMap.mulLeft (fieldNatType k n) (fieldNatTypeElement k n)) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [LinearMap.mem_range]
    have hmul : (fieldNatTypeElement k n) ^ (n - 1) *
        (Ideal.Quotient.mk (Ideal.span {(X : k[X]) ^ n}) p) =
        Ideal.Quotient.mk _ (X ^ (n - 1) * p) := by
      rw [fieldNatTypeElement, ← map_pow]; exact (map_mul _ _ _).symm
    rw [hmul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
    have hsplit : (X : k[X]) ^ n = X ^ (n - 1) * X := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    have hne : (X : k[X]) ^ (n - 1) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
    rw [hsplit, mul_dvd_mul_iff_left hne] at hx
    obtain ⟨q, hq⟩ := hx
    refine ⟨Ideal.Quotient.mk _ q, ?_⟩
    rw [LinearMap.mulLeft_apply, fieldNatTypeElement, ← map_mul, ← hq]
  · rintro _ ⟨r, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc,
      ← pow_succ, show (n - 1) + 1 = n by omega, fieldNatTypeElement_pow_eq_zero, zero_mul]

/-- Above index one, the square of the predecessor power of the designated element is zero. -/
theorem fieldNatTypeElementPowPred_sq_eq_zero_of_one_lt (hn : 1 < n) :
    (fieldNatTypeElement k n) ^ (n - 1) * (fieldNatTypeElement k n) ^ (n - 1) = 0 := by
  rw [← pow_add]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show n ≤ (n - 1) + (n - 1) by omega)
  rw [hm, pow_add, fieldNatTypeElement_pow_eq_zero, zero_mul]

/--
For indices greater than one, the range of multiplication by the designated element is not
projective as a module. -/
theorem not_projective_range_mulLeft_element (hn : 1 < n) :
    ¬ Projective (ModuleCat.of (fieldNatType k n)
      ↥(LinearMap.range (LinearMap.mulLeft (fieldNatType k n) (fieldNatTypeElement k n)))) := by
  letI : Small.{u} (fieldNatType k n) := ⟨⟨fieldNatType k n, ⟨Equiv.refl _⟩⟩⟩
  intro hProj
  set ft := LinearMap.mulLeft (fieldNatType k n) (fieldNatTypeElement k n) with hft
  haveI : Projective (ModuleCat.of (fieldNatType k n) ↥(LinearMap.range ft)) := hProj
  haveI : Module.Projective (fieldNatType k n) ↥(LinearMap.range ft) :=
    (IsProjective.iff_projective _).mpr hProj
  have hy0mem : (fieldNatTypeElement k n) ∈ LinearMap.range ft :=
    LinearMap.mem_range.mpr ⟨1, by rw [hft, LinearMap.mulLeft_apply, mul_one]⟩
  set y₀ : ↥(LinearMap.range ft) := ⟨fieldNatTypeElement k n, hy0mem⟩ with hy0
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property ft.rangeRestrict
    (LinearMap.id) ft.surjective_rangeRestrict
  set e := σ y₀ with he_def
  have hgen : (fieldNatTypeElement k n) * e = fieldNatTypeElement k n := by
    have h1 := LinearMap.congr_fun hσ y₀
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq] at h1
    have h2 : ft e = fieldNatTypeElement k n := congrArg Subtype.val h1
    rwa [hft, LinearMap.mulLeft_apply] at h2
  have hann : (fieldNatTypeElement k n) ^ (n - 1) * e = 0 := by
    have hz : ((fieldNatTypeElement k n) ^ (n - 1)) • y₀ = 0 := by
      apply Subtype.ext
      change (fieldNatTypeElement k n) ^ (n - 1) • (fieldNatTypeElement k n) =
        (0 : fieldNatType k n)
      rw [smul_eq_mul, ← pow_succ, show (n - 1) + 1 = n by omega,
        fieldNatTypeElement_pow_eq_zero]
    have hmap : ((fieldNatTypeElement k n) ^ (n - 1)) • e =
        σ (((fieldNatTypeElement k n) ^ (n - 1)) • y₀) := (map_smul σ _ _).symm
    rw [hz, map_zero] at hmap
    rw [← smul_eq_mul]; exact hmap
  apply fieldNatTypeElementPowPred_ne_zero_of_pos k n (by omega)
  have key : (fieldNatTypeElement k n) ^ (n - 1) * e =
      (fieldNatTypeElement k n) ^ (n - 1) := by
    have h3 : (fieldNatTypeElement k n) ^ (n - 2) * ((fieldNatTypeElement k n) * e) =
        (fieldNatTypeElement k n) ^ (n - 2) * (fieldNatTypeElement k n) := by
      rw [hgen]
    rw [← mul_assoc, ← pow_succ, show (n - 2) + 1 = n - 1 by omega] at h3
    exact h3
  rw [hann] at key
  exact key.symm

/--
For indices greater than one, the range of multiplication by the predecessor power is not
projective as a module. -/
theorem not_projective_range_mulLeft_elementPowPred (hn : 1 < n) :
    ¬ Projective (ModuleCat.of (fieldNatType k n)
      ↥(LinearMap.range
        (LinearMap.mulLeft (fieldNatType k n) ((fieldNatTypeElement k n) ^ (n - 1))))) := by
  letI : Small.{u} (fieldNatType k n) := ⟨⟨fieldNatType k n, ⟨Equiv.refl _⟩⟩⟩
  intro hProj
  set fs := LinearMap.mulLeft (fieldNatType k n) ((fieldNatTypeElement k n) ^ (n - 1)) with hfs
  haveI : Projective (ModuleCat.of (fieldNatType k n) ↥(LinearMap.range fs)) := hProj
  haveI : Module.Projective (fieldNatType k n) ↥(LinearMap.range fs) :=
    (IsProjective.iff_projective _).mpr hProj
  have hy1mem : (fieldNatTypeElement k n) ^ (n - 1) ∈ LinearMap.range fs :=
    LinearMap.mem_range.mpr ⟨1, by rw [hfs, LinearMap.mulLeft_apply, mul_one]⟩
  set y₁ : ↥(LinearMap.range fs) := ⟨(fieldNatTypeElement k n) ^ (n - 1), hy1mem⟩ with hy1
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property fs.rangeRestrict
    (LinearMap.id) fs.surjective_rangeRestrict
  set e := σ y₁ with he_def
  have hgen : (fieldNatTypeElement k n) ^ (n - 1) * e =
      (fieldNatTypeElement k n) ^ (n - 1) := by
    have h1 := LinearMap.congr_fun hσ y₁
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq] at h1
    have h2 : fs e = (fieldNatTypeElement k n) ^ (n - 1) := congrArg Subtype.val h1
    rwa [hfs, LinearMap.mulLeft_apply] at h2
  have hann : (fieldNatTypeElement k n) * e = 0 := by
    have hz : (fieldNatTypeElement k n) • y₁ = 0 := by
      apply Subtype.ext
      change (fieldNatTypeElement k n) • (fieldNatTypeElement k n) ^ (n - 1) =
        (0 : fieldNatType k n)
      rw [smul_eq_mul, ← pow_succ', show (n - 1) + 1 = n by omega,
        fieldNatTypeElement_pow_eq_zero]
    have hmap : (fieldNatTypeElement k n) • e = σ ((fieldNatTypeElement k n) • y₁) :=
      (map_smul σ _ _).symm
    rw [hz, map_zero] at hmap
    rw [← smul_eq_mul]; exact hmap
  apply fieldNatTypeElementPowPred_ne_zero_of_pos k n (by omega)
  have key : (fieldNatTypeElement k n) ^ (n - 1) * e = 0 := by
    have h3 : (fieldNatTypeElement k n) ^ (n - 2) * ((fieldNatTypeElement k n) * e) =
        (fieldNatTypeElement k n) ^ (n - 2) * 0 := by
      rw [hann]
    rw [← mul_assoc, ← pow_succ, show (n - 2) + 1 = n - 1 by omega, mul_zero] at h3
    exact h3
  exact hgen.symm.trans key

/--
For indices greater than one, the displayed construction on the indexed type is the greatest
element. -/
theorem fieldNatType_construction_eq_top_of_one_lt (hn : 1 < n) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant (fieldNatType k n) = ⊤ := by
  letI : Small.{u} (fieldNatType k n) := ⟨⟨fieldNatType k n, ⟨Equiv.refl _⟩⟩⟩
  set ft := LinearMap.mulLeft (fieldNatType k n) (fieldNatTypeElement k n) with hft
  set fs := LinearMap.mulLeft (fieldNatType k n) ((fieldNatTypeElement k n) ^ (n - 1)) with hfs
  set MA := ModuleCat.of (fieldNatType k n) ↥(LinearMap.range ft) with hMA
  set MB := ModuleCat.of (fieldNatType k n) ↥(LinearMap.range fs) with hMB
  haveI hRproj : Projective (ModuleCat.of (fieldNatType k n) (fieldNatType k n)) := inferInstance
  have sesA : (ft.rangeRestrict).shortComplexKer.ShortExact :=
    LinearMap.shortExact_shortComplexKer ft.surjective_rangeRestrict
  have sesB : (fs.rangeRestrict).shortComplexKer.ShortExact :=
    LinearMap.shortExact_shortComplexKer fs.surjective_rangeRestrict
  have shiftA : ∀ d, HasProjectiveDimensionLE MA (d + 1) → HasProjectiveDimensionLE MB d := by
    intro d hA
    have hker : HasProjectiveDimensionLT
        (ModuleCat.of (fieldNatType k n) ↥(LinearMap.ker ft.rangeRestrict)) (d + 1) := by
      have := RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension.hasProjectiveDimensionLE_pred_of_shortExact_of_projective_middle
        (fieldNatType k n) ft.rangeRestrict.shortComplexKer sesA hRproj (d + 1)
        (Nat.succ_pos d) hA
      simpa only [Nat.add_sub_cancel] using this
    haveI := hker
    have heq : LinearMap.ker ft.rangeRestrict = LinearMap.range fs := by
      rw [LinearMap.ker_rangeRestrict, hft, hfs];
      exact ker_mulLeft_element_eq_range_mulLeft_elementPowPred k n (by omega)
    exact hasProjectiveDimensionLT_of_iso ((LinearEquiv.ofEq _ _ heq).toModuleIso) (d + 1)
  have shiftB : ∀ d, HasProjectiveDimensionLE MB (d + 1) → HasProjectiveDimensionLE MA d := by
    intro d hB
    have hker : HasProjectiveDimensionLT
        (ModuleCat.of (fieldNatType k n) ↥(LinearMap.ker fs.rangeRestrict)) (d + 1) := by
      have := RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension.hasProjectiveDimensionLE_pred_of_shortExact_of_projective_middle
        (fieldNatType k n) fs.rangeRestrict.shortComplexKer sesB hRproj (d + 1)
        (Nat.succ_pos d) hB
      simpa only [Nat.add_sub_cancel] using this
    haveI := hker
    have heq : LinearMap.ker fs.rangeRestrict = LinearMap.range ft := by
      rw [LinearMap.ker_rangeRestrict, hft, hfs];
      exact ker_mulLeft_elementPowPred_eq_range_mulLeft_element k n (by omega)
    exact hasProjectiveDimensionLT_of_iso ((LinearEquiv.ofEq _ _ heq).toModuleIso) (d + 1)
  have hQ : ∀ d, ¬ HasProjectiveDimensionLE MA d ∧ ¬ HasProjectiveDimensionLE MB d := by
    intro d
    induction d with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [← projective_iff_hasProjectiveDimensionLE_zero];
        exact not_projective_range_mulLeft_element k n hn
      · rw [← projective_iff_hasProjectiveDimensionLE_zero];
        exact not_projective_range_mulLeft_elementPowPred k n hn
    | succ d ih => exact ⟨fun hA => ih.2 (shiftA d hA), fun hB => ih.1 (shiftB d hB)⟩
  apply RepresentationTheory.RingPredicateBounds.eq_top_of_forall_not_predicate
  intro d hAll
  exact (hQ d).1 (hAll MA)

end RepresentationTheory.Algebra.FieldIndexedType
