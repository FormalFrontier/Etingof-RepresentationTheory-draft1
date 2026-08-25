/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Homology.ProjectiveResolutionAuxiliary
import RepresentationTheory.DerivedFunctorExactness
import RepresentationTheory.Algebra.Module.DirectSumData
import RepresentationTheory.ModuleCat.RightTensor
import RepresentationTheory.Auxiliary.RingAndCategoryProperties
import RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension
import RepresentationTheory.Algebra.Homological.EquivalenceInvariance
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import RepresentationTheory.Alignment.Attribute

universe u v

open CategoryTheory Limits

namespace RepresentationTheory.HomologicalAlgebra.SymmetricAlgebra.ProjectiveDimension

/-- An additive functor's left-derived object at an object of projective dimension at most `d` is zero in every degree strictly greater than `d`. -/
theorem CategoryTheory.Functor.leftDerived_obj_isZero_of_projectiveDimensionLE_of_lt
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    {D : Type u} [Category.{v} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (X : C) (d i : ℕ)
    (hX : HasProjectiveDimensionLE X d) (hi : d < i) :
    IsZero ((F.leftDerived i).obj X) := by
  induction d generalizing X i with
  | zero =>
      haveI : HasProjectiveDimensionLE X 0 := hX
      haveI : Projective X := (projective_iff_hasProjectiveDimensionLE_zero X).mpr hX
      cases i with
      | zero => omega
      | succ j => exact Functor.isZero_leftDerived_obj_projective_succ F j X
  | succ d ih =>
      obtain ⟨p⟩ := EnoughProjectives.presentation X
      let S : ShortComplex C := ShortComplex.mk (kernel.ι p.f) p.f (by simp)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p.f }
      haveI : Projective S.X₂ := p.projective
      have hP : HasProjectiveDimensionLT S.X₂ (d + 1) :=
        hasProjectiveDimensionLT_of_ge S.X₂ 1 (d + 1) (by omega)
      have hK : HasProjectiveDimensionLE S.X₁ d :=
        hS.hasProjectiveDimensionLT_X₁ (d + 1) hP hX
      cases i with
      | zero => omega
      | succ i =>
          cases i with
          | zero => omega
          | succ j =>
              obtain ⟨δ, hExact⟩ :=
                RepresentationTheory.CategoryPair.AssociatedType.exists_connectingMorphism_exact F hS (j + 1) (j + 2) rfl
              have hHighP : IsZero ((F.leftDerived (j + 2)).obj S.X₂) :=
                Functor.isZero_leftDerived_obj_projective_succ F (j + 1) S.X₂
              have hLowP : IsZero ((F.leftDerived (j + 1)).obj S.X₂) :=
                Functor.isZero_leftDerived_obj_projective_succ F j S.X₂
              let e := RepresentationTheory.DerivedFunctorExactness.exactFiveIso hExact hHighP hLowP
              change ((F.leftDerived (j + 2)).obj S.X₃ ≅
                (F.leftDerived (j + 1)).obj S.X₁) at e
              have hKzero : IsZero ((F.leftDerived (j + 1)).obj S.X₁) :=
                ih S.X₁ (j + 1) hK (by omega)
              change IsZero ((F.leftDerived (j + 2)).obj S.X₃)
              exact IsZero.of_iso hKzero e

section SymmetricAlgebra

variable (k : Type u) [Field k]
variable (V : Type u) [AddCommGroup V] [Module k V]
variable {n : ℕ}

local notation "SV" => SymmetricAlgebra k V

/-- A symmetric algebra on a vector space with a basis indexed by `Fin n` satisfies the specified predicate at index `n`. -/
theorem SymmetricAlgebra.auxiliary_property_of_basis (b : Module.Basis (Fin n) k V) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty SV n :=
  (RepresentationTheory.Algebra.Homological.EquivalenceInvariance.ringProperty_iff_of_ringEquiv
    (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv n).mpr
      (RepresentationTheory.Auxiliary.RingAndCategoryProperties.Auxiliary.property_mvPolynomial_variable_count k n)

/-- Extension classes between modules over a symmetric algebra are subsingletons in degrees above the cardinality of a chosen basis. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
theorem SymmetricAlgebra.ext_subsingleton_of_basis_of_lt (b : Module.Basis (Fin n) k V)
    (M N : ModuleCat.{u} SV) (i : ℕ) (hi : n < i) :
    Subsingleton (Abelian.Ext M N i) :=
  (RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension.hasProjectiveDimensionLE_iff_ext_subsingleton SV M n).mp
    (SymmetricAlgebra.auxiliary_property_of_basis k V b M) N i hi

/-- Above the cardinality of a chosen basis, the specified indexed object associated with a right module and a left module is zero. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
theorem SymmetricAlgebra.auxiliary_bimodule_object_isZero_of_basis_of_lt
    (b : Module.Basis (Fin n) k V)
    (M : ModuleCat.{u} SVᵐᵒᵖ) (N : Type u) [AddCommGroup N] [Module SV N]
    (i : ℕ) (hi : n < i) :
    IsZero (RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k SV N M i) := by
  have hRight : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatPropertyThird SV n :=
    (RepresentationTheory.Algebra.Homological.EquivalenceInvariance.firstRingProperty_iff_secondRingProperty n).mpr
      (SymmetricAlgebra.auxiliary_property_of_basis k V b)
  exact CategoryTheory.Functor.leftDerived_obj_isZero_of_projectiveDimensionLE_of_lt
    (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k SV N) M n i (hRight M) hi

/-- Above the cardinality of a chosen basis, the specified indexed object formed from two modules and the displayed functorial input is zero. -/
theorem SymmetricAlgebra.auxiliary_module_object_isZero_of_basis_of_lt
    (b : Module.Basis (Fin n) k V)
    (M N : ModuleCat.{u} SV) (i : ℕ) (hi : n < i) :
    IsZero (RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k SV N
      ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) i) :=
  SymmetricAlgebra.auxiliary_bimodule_object_isZero_of_basis_of_lt k V b
    ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) N i hi

/-- A finite basis supplies the displayed projective-dimension bound, subsingleton higher extension classes, and vanishing of the specified indexed objects. -/
@[source_ref "Chapter8/Problem8.2.10" (role := primary)]
theorem SymmetricAlgebra.auxiliary_homological_bounds_of_basis
    (b : Module.Basis (Fin n) k V) :
    (∀ M : ModuleCat.{u} SV, HasProjectiveDimensionLE M n) ∧
      (∀ (M N : ModuleCat.{u} SV) (i : ℕ), n < i →
        Subsingleton (Abelian.Ext M N i)) ∧
      (∀ (M N : ModuleCat.{u} SV) (i : ℕ), n < i →
        IsZero (RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k SV N
          ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) i)) := by
  refine ⟨SymmetricAlgebra.auxiliary_property_of_basis k V b, ?_, ?_⟩
  · exact fun M N i hi => SymmetricAlgebra.ext_subsingleton_of_basis_of_lt k V b M N i hi
  · exact fun M N i hi => SymmetricAlgebra.auxiliary_module_object_isZero_of_basis_of_lt k V b M N i hi

/-- Extension classes between modules over the symmetric algebra of a finite-dimensional vector space are subsingletons in degrees above its rank. -/
theorem SymmetricAlgebra.ext_subsingleton_of_finrank_lt [FiniteDimensional k V]
    (M N : ModuleCat.{u} SV) (i : ℕ) (hi : Module.finrank k V < i) :
    Subsingleton (Abelian.Ext M N i) :=
  SymmetricAlgebra.ext_subsingleton_of_basis_of_lt k V (Module.finBasis k V) M N i hi

/-- Above the rank of a finite-dimensional vector space, the specified indexed object associated with a right module and a left module is zero. -/
theorem SymmetricAlgebra.auxiliary_bimodule_object_isZero_of_finrank_lt
    [FiniteDimensional k V]
    (M : ModuleCat.{u} SVᵐᵒᵖ) (N : Type u) [AddCommGroup N] [Module SV N]
    (i : ℕ) (hi : Module.finrank k V < i) :
    IsZero (RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k SV N M i) :=
  SymmetricAlgebra.auxiliary_bimodule_object_isZero_of_basis_of_lt k V
    (Module.finBasis k V) M N i hi

/-- Above the rank of a finite-dimensional vector space, the specified indexed object formed from two modules and the displayed functorial input is zero. -/
theorem SymmetricAlgebra.auxiliary_module_object_isZero_of_finrank_lt
    [FiniteDimensional k V]
    (M N : ModuleCat.{u} SV) (i : ℕ) (hi : Module.finrank k V < i) :
    IsZero (RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k SV N
      ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) i) :=
  SymmetricAlgebra.auxiliary_module_object_isZero_of_basis_of_lt k V
    (Module.finBasis k V) M N i hi

/-- Finite dimensionality supplies the displayed rank bound on projective dimension, subsingleton higher extension classes, and vanishing of the specified indexed objects. -/
theorem SymmetricAlgebra.auxiliary_homological_bounds_of_finiteDimensional
    [FiniteDimensional k V] :
    (∀ M : ModuleCat.{u} SV,
        HasProjectiveDimensionLE M (Module.finrank k V)) ∧
      (∀ (M N : ModuleCat.{u} SV) (i : ℕ), Module.finrank k V < i →
        Subsingleton (Abelian.Ext M N i)) ∧
      (∀ (M N : ModuleCat.{u} SV) (i : ℕ), Module.finrank k V < i →
        IsZero (RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k SV N
          ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite SV).obj M) i)) :=
  SymmetricAlgebra.auxiliary_homological_bounds_of_basis k V (Module.finBasis k V)

/-- For a vector space with a finite basis, the specified indexed property holds for its symmetric algebra exactly when it holds for the corresponding multivariable polynomial ring. -/
theorem SymmetricAlgebra.auxiliary_property_iff_mvPolynomial_of_basis
    (b : Module.Basis (Fin n) k V) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty SV n ↔
      RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty
        (MvPolynomial (Fin n) k) n :=
  RepresentationTheory.Algebra.Homological.EquivalenceInvariance.ringProperty_iff_of_ringEquiv
    (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv n

end SymmetricAlgebra

end RepresentationTheory.HomologicalAlgebra.SymmetricAlgebra.ProjectiveDimension
