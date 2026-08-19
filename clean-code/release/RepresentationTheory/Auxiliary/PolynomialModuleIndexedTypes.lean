/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID
import RepresentationTheory.Alignment.Attribute

universe u

namespace RepresentationTheory.Auxiliary.PolynomialModuleIndexedTypes

open _root_.CategoryTheory _root_.CategoryTheory.Limits Polynomial

variable {k : Type u} [Field k]

/-- The displayed type at index 0 on the polynomial module and any module object is additively equivalent to that object's carrier. -/
theorem Auxiliary.polynomialModule_indexZero_addEquiv (Z : ModuleCat.{u} k[X]) :
    Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
      (ModuleCat.of k[X] k[X]) Z 0 ≃+ Z) := by
  obtain ⟨e⟩ := RepresentationTheory.DerivedFunctorExactness.AuxiliaryDegreeZeroAddEquiv
    k[X] (ModuleCat.of k[X] k[X]) Z
  exact ⟨e.trans (ModuleCat.homAddEquiv.trans
    (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.LinearMap.addEquiv_from_self k[X] Z))⟩

/-- Linear maps from the quotient by a nonzero principal polynomial ideal to the polynomial ring form a subsingleton. -/
lemma Auxiliary.subsingleton_linearMap_principalQuotient_to_polynomial (f : k[X]) (hf : f ≠ 0) :
    Subsingleton ((k[X] ⧸ Ideal.span {f}) →ₗ[k[X]] k[X]) := by
  have hzero : ∀ ψ : (k[X] ⧸ Ideal.span {f}) →ₗ[k[X]] k[X], ψ = 0 := by
    intro ψ
    have h1 : ψ (Submodule.Quotient.mk (1 : k[X])) = 0 := by
      have hf1 : f • ψ (Submodule.Quotient.mk (1 : k[X])) = 0 := by
        rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
          (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton_self f), map_zero]
      exact (smul_eq_zero.mp hf1).resolve_left hf
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {f}) x
    rw [show (Submodule.Quotient.mk y : k[X] ⧸ Ideal.span {f})
          = y • Submodule.Quotient.mk (1 : k[X]) from by
        rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one], map_smul, h1, smul_zero,
      LinearMap.zero_apply]
  exact ⟨fun ψ φ => by rw [hzero ψ, hzero φ]⟩

/-- For a nonzero polynomial, the displayed type at index 0 on its principal quotient and the polynomial module is subsingleton. -/
theorem Auxiliary.subsingleton_indexZero_principalQuotient_to_polynomial
    (f : k[X]) (hf : f ≠ 0) :
    Subsingleton (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
      (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {f})) (ModuleCat.of k[X] k[X]) 0) := by
  haveI := RepresentationTheory.Auxiliary.PolynomialModuleIndexedTypes.Auxiliary.subsingleton_linearMap_principalQuotient_to_polynomial f hf
  obtain ⟨e⟩ := RepresentationTheory.DerivedFunctorExactness.AuxiliaryDegreeZeroAddEquiv
    k[X] (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {f})) (ModuleCat.of k[X] k[X])
  exact (e.trans ModuleCat.homAddEquiv).toEquiv.subsingleton

variable {M N : Type u} [AddCommGroup M] [Module k[X] M] [AddCommGroup N] [Module k[X] N]

/-- For a finite module over a polynomial ring and any module object, the displayed type at each index n + 2 is subsingleton. -/
theorem Auxiliary.finitePolynomialModule_subsingleton_indexAddTwo [Module.Finite k[X] M]
    (Z : ModuleCat.{u} k[X]) (n : ℕ) :
    Subsingleton (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
      (ModuleCat.of k[X] M) Z (n + 2)) := by
  haveI := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.ModuleCat.hasProjectiveDimensionLT_two_of_finite_of_isPrincipalIdealRing k[X] M
  exact HasProjectiveDimensionLT.subsingleton (ModuleCat.of k[X] M) 2 (n + 2) (by omega) Z

/-- Under the displayed nonvanishing condition, the type at index 1 is additively equivalent to an indexed family of quotients by spans of pairs of displayed polynomials. -/
theorem Auxiliary.indexOne_addEquiv_pi_quotient_span_pair
    (D : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData k[X] M)
    (E : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData k[X] N)
    (hD : ∀ i, D.quotientGenerator i ≠ 0) :
    Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
      (ModuleCat.of k[X] M) (ModuleCat.of k[X] N) 1 ≃+
      ∀ (i : D.Index) (l : E.summandIndex),
        (k[X] ⧸ Ideal.span {D.quotientGenerator i, E.combined_coefficient l})) := by
  haveI : ∀ i : Fin D.natParameter,
      Subsingleton (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
        (D.summand (Sum.inl i)) (ModuleCat.of k[X] N) 1) := fun _ =>
    RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryPolynomialModuleDegreeSuccSubsingleton
      k (ModuleCat.of k[X] N) 0
  haveI := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.subsingleton_pi
    fun i : Fin D.natParameter =>
      RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
        (D.summand (Sum.inl i)) (ModuleCat.of k[X] N) 1
  refine ⟨(RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.addEquiv_pi_left
    D (ModuleCat.of k[X] N) 1).trans
    (((RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.pi_sum _).trans
      (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.prod_right_of_subsingleton _ _)).trans
      (AddEquiv.piCongrRight fun i => ?_))⟩
  refine (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.addEquiv_pi_right
    (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {D.quotientGenerator i})) E 1).trans
    (AddEquiv.piCongrRight fun l => ?_)
  exact (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.CategoryTheory.Abelian.Ext.addEquiv_of_isos
    (Iso.refl _) (E.component_iso_quotient_span l) 1).trans
    (RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryPolynomialQuotientDegreeOneAddEquiv
      k (D.quotientGenerator i) (E.combined_coefficient l) (hD i)).some

/-- Under the displayed nonvanishing conditions, the type at index 0 is additively equivalent to a product of a finite function type and an indexed family of quotients by spans of pairs of displayed polynomials. -/
theorem Auxiliary.indexZero_addEquiv_finitePower_prod_pi_quotient
    (D : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData k[X] M)
    (E : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData k[X] N)
    (hD : ∀ i, D.quotientGenerator i ≠ 0) (hE : ∀ l, E.quotientGenerator l ≠ 0) :
    Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
      (ModuleCat.of k[X] M) (ModuleCat.of k[X] N) 0 ≃+
      (Fin D.natParameter → N) ×
        ∀ (i : D.Index) (l : E.Index),
          (k[X] ⧸ Ideal.span {D.quotientGenerator i, E.quotientGenerator l})) := by
  refine ⟨(RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.addEquiv_pi_left
    D (ModuleCat.of k[X] N) 0).trans
    ((RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.pi_sum _).trans
      (AddEquiv.prodCongr (AddEquiv.piCongrRight fun _ => ?_)
        (AddEquiv.piCongrRight fun i => ?_)))⟩
  · exact (RepresentationTheory.Auxiliary.PolynomialModuleIndexedTypes.Auxiliary.polynomialModule_indexZero_addEquiv
      (ModuleCat.of k[X] N)).some
  · haveI : ∀ l : Fin E.natParameter,
        Subsingleton (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
          (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {D.quotientGenerator i}))
          (E.summand (Sum.inl l)) 0) := fun _ =>
      RepresentationTheory.Auxiliary.PolynomialModuleIndexedTypes.Auxiliary.subsingleton_indexZero_principalQuotient_to_polynomial
        (D.quotientGenerator i) (hD i)
    haveI := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.subsingleton_pi
      fun l : Fin E.natParameter =>
        RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
          (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {D.quotientGenerator i}))
          (E.summand (Sum.inl l)) 0
    refine (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.addEquiv_pi_right
      (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {D.quotientGenerator i})) E 0).trans
      (((RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.pi_sum _).trans
        (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.prod_right_of_subsingleton _ _)).trans
        (AddEquiv.piCongrRight fun l => ?_))
    exact (RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryPolynomialQuotientDegreeZeroAddEquiv
      k (D.quotientGenerator i) (E.quotientGenerator l) (hE l)).some

/-- For finite modules over a polynomial ring, there exist auxiliary data yielding the displayed additive equivalences at indices 0 and 1, and the displayed type at every index n + 2 is subsingleton. -/
@[source_ref "Chapter8/Problem8.2.7" (role := supporting)]
theorem Auxiliary.finitePolynomialModules_indexZeroOne_addEquiv_and_indexAddTwo_subsingleton
    [Module.Finite k[X] M] [Module.Finite k[X] N] :
    ∃ (D : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData k[X] M)
      (E : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData k[X] N),
      Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
        (ModuleCat.of k[X] M) (ModuleCat.of k[X] N) 0 ≃+
        (Fin D.natParameter → N) ×
          ∀ (i : D.Index) (l : E.Index),
            (k[X] ⧸ Ideal.span {D.quotientGenerator i, E.quotientGenerator l})) ∧
      Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
        (ModuleCat.of k[X] M) (ModuleCat.of k[X] N) 1 ≃+
        ∀ (i : D.Index) (l : E.summandIndex),
          (k[X] ⧸ Ideal.span {D.quotientGenerator i, E.combined_coefficient l})) ∧
      ∀ n : ℕ, Subsingleton
        (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses
          (ModuleCat.of k[X] M) (ModuleCat.of k[X] N) (n + 2)) := by
  obtain ⟨D, hD⟩ := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.exists_data_with_nonzero_coefficients k[X] M
  obtain ⟨E, hE⟩ := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.exists_data_with_nonzero_coefficients k[X] N
  exact ⟨D, E,
    RepresentationTheory.Auxiliary.PolynomialModuleIndexedTypes.Auxiliary.indexZero_addEquiv_finitePower_prod_pi_quotient D E hD hE,
    RepresentationTheory.Auxiliary.PolynomialModuleIndexedTypes.Auxiliary.indexOne_addEquiv_pi_quotient_span_pair D E hD,
    fun n => RepresentationTheory.Auxiliary.PolynomialModuleIndexedTypes.Auxiliary.finitePolynomialModule_subsingleton_indexAddTwo
      (ModuleCat.of k[X] N) n⟩

example : True := by
  have := RepresentationTheory.Auxiliary.PolynomialModuleIndexedTypes.Auxiliary.finitePolynomialModules_indexZeroOne_addEquiv_and_indexAddTwo_subsingleton
    (k := ℚ) (M := ℚ[X]) (N := ℚ[X])
  trivial

end RepresentationTheory.Auxiliary.PolynomialModuleIndexedTypes
