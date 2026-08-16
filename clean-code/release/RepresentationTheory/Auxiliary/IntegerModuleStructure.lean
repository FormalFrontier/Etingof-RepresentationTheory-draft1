/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID
import RepresentationTheory.Alignment.Attribute

universe u

namespace RepresentationTheory.Auxiliary.IntegerModuleStructure

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RepresentationTheory.Algebra.Module.DirectSumData

/-- Identifies an integer quotient by one generated ideal with the cyclic module of matching absolute modulus. -/
noncomputable def intQuotientSpanIsoZModNatAbs (d : ℤ) :
    ModuleCat.of ℤ (ℤ ⧸ Ideal.span {d}) ≅ ModuleCat.of ℤ (ZMod d.natAbs) :=
  have hspan : Ideal.span {d} = Ideal.span {(d.natAbs : ℤ)} :=
    le_antisymm
      (Ideal.span_le.mpr (by
        simp only [Set.singleton_subset_iff, SetLike.mem_coe]
        exact Ideal.mem_span_singleton.mpr (Int.natAbs_dvd.mpr dvd_rfl)))
      (Ideal.span_le.mpr (by
        simp only [Set.singleton_subset_iff, SetLike.mem_coe]
        exact Ideal.mem_span_singleton.mpr (Int.dvd_natAbs.mpr dvd_rfl)))
  LinearEquiv.toModuleIso (Submodule.quotEquivOfEq _ _ hspan) ≪≫ RepresentationTheory.Algebra.Module.DirectSumData.intQuotientSpanNatCastModuleIsoZMod d.natAbs

/-- For each j, identifies the displayed integer module with ZMod at the natural absolute value of the displayed associated integer. -/
noncomputable def auxiliaryIndexedModuleIsoZModNatAbs {M : Type} [AddCommGroup M] (D : Module.DirectSumData ℤ M)
    (j : D.summandIndex) : D.summand j ≅ ModuleCat.of ℤ (ZMod (D.combined_coefficient j).natAbs) :=
  D.component_iso_quotient_span j ≪≫ intQuotientSpanIsoZModNatAbs (D.combined_coefficient j)

/-- Gives an additive equivalence between the displayed value at index zero and the carrier of Z. -/
theorem auxiliaryIntIndexZeroEquivCarrier (Z : ModuleCat.{0} ℤ) :
    Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ ℤ) Z 0 ≃+ Z) := by
  obtain ⟨e⟩ := RepresentationTheory.DerivedFunctorExactness.AuxiliaryDegreeZeroAddEquiv ℤ (ModuleCat.of ℤ ℤ) Z
  exact ⟨e.trans (ModuleCat.homAddEquiv.trans (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.LinearMap.addEquiv_from_self ℤ Z))⟩

/-- States that the displayed value at index zero is subsingleton when the ZMod modulus is nonzero. -/
theorem auxiliaryZModIntIndexZeroSubsingleton (a : ℕ) (ha : a ≠ 0) :
    Subsingleton (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ ℤ) 0) := by
  haveI : NeZero a := ⟨ha⟩
  haveI := RepresentationTheory.PolynomialQuotientZModAuxiliary.subsingleton_linearMapZModToInt a
  obtain ⟨e⟩ := RepresentationTheory.DerivedFunctorExactness.AuxiliaryDegreeZeroAddEquiv ℤ (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ ℤ)
  exact (e.trans ModuleCat.homAddEquiv).toEquiv.subsingleton

/-- Gives an additive equivalence between the displayed value at index one and ZMod (a.gcd c). -/
theorem auxiliaryZModIndexOneEquivGcd (a c : ℕ) (ha : a ≠ 0) :
    Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ (ZMod c)) 1
      ≃+ ZMod (Nat.gcd a c)) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [Nat.gcd_zero_right]
    obtain ⟨e⟩ := RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryIntZModDegreeOneQuotientAddEquiv a ha ℤ
    have h : Ideal.span {(a : ℤ)} • (⊤ : Submodule ℤ ℤ) = (Ideal.span {(a : ℤ)} : Ideal ℤ) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact ⟨e.trans ((Submodule.quotEquivOfEq _ _ h).toAddEquiv.trans
      (Int.quotientSpanNatEquivZMod a).toAddEquiv)⟩
  · exact RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryIntZModDegreeOneGcdAddEquiv a c ha hc

variable {M N : Type} [AddCommGroup M] [AddCommGroup N]

/-- States that the displayed value at index n + 2 is subsingleton for a finite integer module and an integer module Z. -/
theorem auxiliaryFiniteIntModuleIndexAddTwoSubsingleton [Module.Finite ℤ M] (Z : ModuleCat.{0} ℤ) (n : ℕ) :
    Subsingleton (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ M) Z (n + 2)) := by
  haveI := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.ModuleCat.hasProjectiveDimensionLT_two_of_finite_of_isPrincipalIdealRing ℤ M
  exact HasProjectiveDimensionLT.subsingleton (ModuleCat.of ℤ M) 2 (n + 2) (by omega) Z

/-- Gives an additive equivalence between the displayed value at index one and the shown family of quotients of N. -/
theorem auxiliaryIndexOneEquivIndexedScalarQuotients (D : Module.DirectSumData ℤ M) (hD : ∀ i, D.quotientGenerator i ≠ 0) :
    Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) 1 ≃+
      ∀ i : D.Index,
        (N ⧸ Ideal.span {((D.quotientGenerator i).natAbs : ℤ)} • (⊤ : Submodule ℤ N))) := by

  haveI : ∀ i : Fin D.natParameter,
      Subsingleton (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (D.summand (Sum.inl i)) (ModuleCat.of ℤ N) 1) := fun _ =>
    RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryIntModuleDegreeSuccSubsingleton (ModuleCat.of ℤ N) 0
  haveI := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.subsingleton_pi fun i : Fin D.natParameter =>
    RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (D.summand (Sum.inl i)) (ModuleCat.of ℤ N) 1

  refine ⟨(RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.addEquiv_pi_left D (ModuleCat.of ℤ N) 1).trans
    (((RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.pi_sum _).trans (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.prod_right_of_subsingleton _ _)).trans
      (AddEquiv.piCongrRight fun i => ?_))⟩
  have hne : (D.quotientGenerator i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hD i)
  exact (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.CategoryTheory.Abelian.Ext.addEquiv_of_isos (auxiliaryIndexedModuleIsoZModNatAbs D (Sum.inr i)) (Iso.refl _) 1).trans
    (RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryIntZModDegreeOneQuotientAddEquiv (D.quotientGenerator i).natAbs hne N).some

/-- Gives an additive equivalence between the displayed value at index one and the shown doubly indexed family of ZMod types with gcd moduli. -/
theorem auxiliaryIndexOneEquivIndexedZModGcd (D : Module.DirectSumData ℤ M) (E : Module.DirectSumData ℤ N)
    (hD : ∀ i, D.quotientGenerator i ≠ 0) :
    Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) 1 ≃+
      ∀ (i : D.Index) (l : E.summandIndex),
        ZMod (Nat.gcd (D.quotientGenerator i).natAbs (E.combined_coefficient l).natAbs)) := by
  haveI : ∀ i : Fin D.natParameter,
      Subsingleton (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (D.summand (Sum.inl i)) (ModuleCat.of ℤ N) 1) := fun _ =>
    RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryIntModuleDegreeSuccSubsingleton (ModuleCat.of ℤ N) 0
  haveI := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.subsingleton_pi fun i : Fin D.natParameter =>
    RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (D.summand (Sum.inl i)) (ModuleCat.of ℤ N) 1
  refine ⟨(RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.addEquiv_pi_left D (ModuleCat.of ℤ N) 1).trans
    (((RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.pi_sum _).trans (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.prod_right_of_subsingleton _ _)).trans
      (AddEquiv.piCongrRight fun i => ?_))⟩
  have hne : (D.quotientGenerator i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hD i)

  refine (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.CategoryTheory.Abelian.Ext.addEquiv_of_isos (auxiliaryIndexedModuleIsoZModNatAbs D (Sum.inr i)) (Iso.refl _) 1).trans
    ((RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.addEquiv_pi_right (ModuleCat.of ℤ (ZMod (D.quotientGenerator i).natAbs)) E 1).trans
      (AddEquiv.piCongrRight fun l => ?_))
  exact (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.CategoryTheory.Abelian.Ext.addEquiv_of_isos (Iso.refl _) (auxiliaryIndexedModuleIsoZModNatAbs E l) 1).trans
    (auxiliaryZModIndexOneEquivGcd (D.quotientGenerator i).natAbs (E.combined_coefficient l).natAbs hne).some

/-- Gives an additive equivalence between the displayed value at index zero and the product of the shown Fin-indexed function space with a doubly indexed family of ZMod types with gcd moduli. -/
theorem auxiliaryIndexZeroEquivFinFunctionsProdIndexedZModGcd (D : Module.DirectSumData ℤ M) (E : Module.DirectSumData ℤ N)
    (hD : ∀ i, D.quotientGenerator i ≠ 0) (hE : ∀ l, E.quotientGenerator l ≠ 0) :
    Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) 0 ≃+
      (Fin D.natParameter → N) ×
        ∀ (i : D.Index) (l : E.Index),
          ZMod (Nat.gcd (D.quotientGenerator i).natAbs (E.quotientGenerator l).natAbs)) := by
  refine ⟨(RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.addEquiv_pi_left D (ModuleCat.of ℤ N) 0).trans
    ((RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.pi_sum _).trans (AddEquiv.prodCongr (AddEquiv.piCongrRight fun _ => ?_)
      (AddEquiv.piCongrRight fun i => ?_)))⟩
  ·
    exact (auxiliaryIntIndexZeroEquivCarrier (ModuleCat.of ℤ N)).some
  ·
    have hne : (D.quotientGenerator i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hD i)
    haveI : NeZero (D.quotientGenerator i).natAbs := ⟨hne⟩
    haveI : ∀ l : Fin E.natParameter,
        Subsingleton (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ (ZMod (D.quotientGenerator i).natAbs))
          (E.summand (Sum.inl l)) 0) := fun _ =>
      auxiliaryZModIntIndexZeroSubsingleton (D.quotientGenerator i).natAbs hne
    haveI := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.subsingleton_pi fun l : Fin E.natParameter =>
      RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ (ZMod (D.quotientGenerator i).natAbs)) (E.summand (Sum.inl l)) 0
    refine (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.CategoryTheory.Abelian.Ext.addEquiv_of_isos (auxiliaryIndexedModuleIsoZModNatAbs D (Sum.inr i)) (Iso.refl _) 0).trans
      ((RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.addEquiv_pi_right (ModuleCat.of ℤ (ZMod (D.quotientGenerator i).natAbs)) E 0).trans
        (((RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.pi_sum _).trans (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.prod_right_of_subsingleton _ _)).trans
          (AddEquiv.piCongrRight fun l => ?_)))
    exact (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.CategoryTheory.Abelian.Ext.addEquiv_of_isos (Iso.refl _) (auxiliaryIndexedModuleIsoZModNatAbs E (Sum.inr l)) 0).trans
      (RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryIntZModDegreeZeroGcdAddEquiv (D.quotientGenerator i).natAbs (E.quotientGenerator l).natAbs hne
        (Int.natAbs_ne_zero.mpr (hE l))).some

/-- For finite integer modules, gives the displayed additive equivalences at indices zero and one and subsingleton values at indices n + 2. -/
@[source_ref "Chapter8/Problem8.2.7" (role := primary)]
theorem auxiliaryFiniteIntModuleIndexZeroOneEquivsAndAddTwoSubsingleton [Module.Finite ℤ M] [Module.Finite ℤ N] :
    ∃ (D : Module.DirectSumData ℤ M) (E : Module.DirectSumData ℤ N),
      Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) 0 ≃+
        (Fin D.natParameter → N) ×
          ∀ (i : D.Index) (l : E.Index),
            ZMod (Nat.gcd (D.quotientGenerator i).natAbs (E.quotientGenerator l).natAbs)) ∧
      Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) 1 ≃+
        ∀ (i : D.Index) (l : E.summandIndex),
          ZMod (Nat.gcd (D.quotientGenerator i).natAbs (E.combined_coefficient l).natAbs)) ∧
      ∀ n : ℕ, Subsingleton (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) (n + 2)) := by
  obtain ⟨D, hD⟩ := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.exists_data_with_nonzero_coefficients ℤ M
  obtain ⟨E, hE⟩ := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.exists_data_with_nonzero_coefficients ℤ N
  exact ⟨D, E, auxiliaryIndexZeroEquivFinFunctionsProdIndexedZModGcd D E hD hE, auxiliaryIndexOneEquivIndexedZModGcd D E hD,
    fun n => auxiliaryFiniteIntModuleIndexAddTwoSubsingleton (ModuleCat.of ℤ N) n⟩

section Examples

example : Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ (ZMod 6)) (ModuleCat.of ℤ (ZMod 4)) 1
    ≃+ ZMod 2) := by
  have h := auxiliaryZModIndexOneEquivGcd 6 4 (by norm_num)
  rwa [show Nat.gcd 6 4 = 2 from by norm_num] at h

example : Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of ℤ (ZMod 6)) (ModuleCat.of ℤ (ZMod 0)) 1
    ≃+ ZMod 6) := by
  have h := auxiliaryZModIndexOneEquivGcd 6 0 (by norm_num)
  rwa [Nat.gcd_zero_right] at h

example : True := by
  have := auxiliaryFiniteIntModuleIndexZeroOneEquivsAndAddTwoSubsingleton (M := ZMod 6) (N := ℤ × ZMod 4)
  trivial

end Examples

end RepresentationTheory.Auxiliary.IntegerModuleStructure
