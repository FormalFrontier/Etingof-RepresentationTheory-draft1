/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.ComponentEquivalences
import RepresentationTheory.Auxiliary.IntegerModuleStructure
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] RepresentationTheory.PolynomialQuotientZModAuxiliary.zModOppositeIntModule

/-- The quotient of `ZMod c` by the span of the image of `a` is additively equivalent to `ZMod (a.gcd c)`. -/
theorem Algebra.Auxiliary.zmodQuotientSpan_addEquiv_zmod_gcd (a c : ℕ) :
    Nonempty ((ZMod c ⧸ (Ideal.span {(a : ℤ)} • (⊤ : Submodule ℤ (ZMod c))))
      ≃+ ZMod (Nat.gcd a c)) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [Nat.gcd_zero_right]
    have h : Ideal.span {(a : ℤ)} • (⊤ : Submodule ℤ ℤ) = (Ideal.span {(a : ℤ)} : Ideal ℤ) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact ⟨(Submodule.quotEquivOfEq _ _ h).toAddEquiv.trans
      (Int.quotientSpanNatEquivZMod a).toAddEquiv⟩
  · haveI : NeZero c := ⟨hc⟩
    exact ⟨(RepresentationTheory.PolynomialQuotientZModAuxiliary.quotientZModLinearEquivGcd a c).toAddEquiv⟩

/-- The value at zero of the construction on `ZMod c` and the integer module on `ZMod a` is isomorphic to `ZMod (a.gcd c)`. -/
theorem Algebra.Auxiliary.componentAtZero_zmod_iso_zmod_gcd (a c : ℕ) :
    Nonempty (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ (ZMod c) (ModuleCat.of ℤᵐᵒᵖ (ZMod a)) 0
      ≅ AddCommGrpCat.of (ZMod (Nat.gcd a c))) := by
  obtain ⟨e⟩ := RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryIntZModModuleDegreeZeroQuotientIso a (ZMod c)
  obtain ⟨e'⟩ := RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.zmodQuotientSpan_addEquiv_zmod_gcd a c
  exact ⟨e ≪≫ e'.toAddCommGrpIso⟩

/-- An indexed object is isomorphic to the integer module carried by the cyclic group whose order is the absolute value of its associated coefficient. -/
noncomputable def Algebra.Auxiliary.indexedObject_iso_zmod_natAbs {M : Type} [AddCommGroup M]
    (D : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData ℤ M)
    (j : D.summandIndex) : D.oppositeSummand j ≅
      ModuleCat.of ℤᵐᵒᵖ (ZMod (D.combined_coefficient j).natAbs) :=
  (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite ℤ).mapIso
    (RepresentationTheory.Auxiliary.IntegerModuleStructure.auxiliaryIndexedModuleIsoZModNatAbs D j)

/-- An indexed module is linearly equivalent over the integers to the cyclic group whose order is the absolute value of its associated coefficient. -/
noncomputable def Algebra.Auxiliary.indexedModule_linearEquiv_zmod_natAbs {N : Type}
    [AddCommGroup N] (E : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData ℤ N)
    (l : E.summandIndex) : (E.summand l : Type) ≃ₗ[ℤ]
      ZMod (E.combined_coefficient l).natAbs :=
  (RepresentationTheory.Auxiliary.IntegerModuleStructure.auxiliaryIndexedModuleIsoZModNatAbs E l).toLinearEquiv

variable {M N : Type} [AddCommGroup M] [AddCommGroup N]

/-- Every component indexed by a natural number plus two is subsingleton when the first input is finite over the integers. -/
theorem Algebra.Auxiliary.componentAtNatAddTwo_subsingleton [Module.Finite ℤ M]
    (Y : Type) [AddCommGroup Y] (n : ℕ) :
    Subsingleton (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ Y
      (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleAsOpposite ℤ M) (n + 2)) := by
  obtain ⟨D⟩ := RepresentationTheory.Algebra.Module.DirectSumData.nonempty_directSumData ℤ M
  refine RepresentationTheory.Auxiliary.ComponentEquivalences.subsingleton_of_componentSubsingleton D Y (n + 2) fun j => ?_
  exact AddCommGrpCat.subsingleton_of_isZero
    ((RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryIntZModModuleDegreeSuccSuccIsZero
      (D.combined_coefficient j).natAbs Y n).of_iso
        (RepresentationTheory.Auxiliary.ComponentEquivalences.mapIso Y
          (RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.indexedObject_iso_zmod_natAbs D j) (n + 2)))

/-- For `D` and `E`, the value at zero is additively equivalent to the doubly indexed family of `ZMod`s whose moduli are gcds of the indexed integers. -/
theorem Algebra.Auxiliary.componentAtZero_addEquiv_pi_zmod_gcd
    (D : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData ℤ M)
    (E : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData ℤ N) :
    Nonempty (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ N
      (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleAsOpposite ℤ M) 0 ≃+
      ∀ (j : D.summandIndex) (l : E.summandIndex),
        ZMod (Nat.gcd (D.combined_coefficient j).natAbs (E.combined_coefficient l).natAbs)) := by
  refine ⟨(RepresentationTheory.Auxiliary.ComponentEquivalences.addEquivPi D E 0).trans
    (AddEquiv.piCongrRight fun j => AddEquiv.piCongrRight fun l => ?_)⟩
  exact ((RepresentationTheory.Auxiliary.ComponentEquivalences.mapLinearEquiv
      (RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.indexedModule_linearEquiv_zmod_natAbs E l)
      (D.oppositeSummand j) 0) ≪≫
    (RepresentationTheory.Auxiliary.ComponentEquivalences.mapIso
      (ZMod (E.combined_coefficient l).natAbs)
      (RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.indexedObject_iso_zmod_natAbs D j) 0) ≪≫
    (RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.componentAtZero_zmod_iso_zmod_gcd
      (D.combined_coefficient j).natAbs (E.combined_coefficient l).natAbs).some).addCommGroupIsoToAddEquiv

/-- If the indexed integers for `D` and `E` are nonzero, the value at one is additively equivalent to the doubly indexed family of `ZMod`s whose moduli are their pairwise gcds. -/
theorem Algebra.Auxiliary.componentAtOne_addEquiv_pi_zmod_gcd
    (D : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData ℤ M)
    (E : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData ℤ N)
    (hD : ∀ i, D.quotientGenerator i ≠ 0) (hE : ∀ l, E.quotientGenerator l ≠ 0) :
    Nonempty (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ N
      (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleAsOpposite ℤ M) 1 ≃+
      ∀ (i : D.Index) (l : E.Index),
        ZMod (Nat.gcd (D.quotientGenerator i).natAbs (E.quotientGenerator l).natAbs)) := by
  haveI : ∀ i : Fin D.natParameter,
      Subsingleton (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ N
        (D.oppositeSummand (Sum.inl i)) 1) := fun _ =>
    AddCommGrpCat.subsingleton_of_isZero
      ((RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryIntModuleDegreeSuccIsZero N 0).of_iso
        (RepresentationTheory.Auxiliary.ComponentEquivalences.mapIso N
          (RepresentationTheory.Algebra.Module.DirectSumData.regularModuleAsOppositeIso ℤ) 1))
  haveI := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.subsingleton_pi
    fun i : Fin D.natParameter =>
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ N
        (D.oppositeSummand (Sum.inl i)) 1 : Type)
  refine ⟨(RepresentationTheory.Auxiliary.ComponentEquivalences.addEquiv D N 1).trans
    (((RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.pi_sum _).trans
      (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.prod_right_of_subsingleton _ _)).trans
      (AddEquiv.piCongrRight fun i => ?_))⟩
  have hne : (D.quotientGenerator i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hD i)
  refine (RepresentationTheory.Auxiliary.ComponentEquivalences.mapIso N
    (RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.indexedObject_iso_zmod_natAbs D (Sum.inr i)) 1).addCommGroupIsoToAddEquiv.trans ?_
  haveI : ∀ l : Fin E.natParameter,
      Subsingleton (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ
        (E.summand (Sum.inl l))
        (ModuleCat.of ℤᵐᵒᵖ (ZMod (D.combined_coefficient (Sum.inr i)).natAbs)) 1) := fun _ =>
    AddCommGrpCat.subsingleton_of_isZero
      (RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryZModDegreeOneIsZero _ hne)
  haveI := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.subsingleton_pi
    fun l : Fin E.natParameter =>
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ
        (E.summand (Sum.inl l))
        (ModuleCat.of ℤᵐᵒᵖ (ZMod (D.combined_coefficient (Sum.inr i)).natAbs)) 1 : Type)
  refine (RepresentationTheory.Auxiliary.ComponentEquivalences.addEquivComponents E _ 1).trans
    (((RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.pi_sum _).trans
      (RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.AddEquiv.prod_right_of_subsingleton _ _)).trans
      (AddEquiv.piCongrRight fun l => ?_))
  exact ((RepresentationTheory.Auxiliary.ComponentEquivalences.mapLinearEquiv
      (RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.indexedModule_linearEquiv_zmod_natAbs E (Sum.inr l)) _ 1) ≪≫
    (RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryZModDegreeOneGcdIso
      (D.quotientGenerator i).natAbs (E.quotientGenerator l).natAbs hne
      (Int.natAbs_ne_zero.mpr (hE l))).some).addCommGroupIsoToAddEquiv

/-- There are choices `D` and `E` for which the values at zero and one are additively equivalent to doubly indexed families of `ZMod`s with gcd moduli, while every value at an index `n + 2` is subsingleton. -/
@[source_ref "Chapter8/Problem8.2.7" (role := supporting)]
theorem Algebra.Auxiliary.exists_gcdZModComponentEquivalences_and_higher_subsingleton
    [Module.Finite ℤ M] [Module.Finite ℤ N] :
    ∃ (D : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData ℤ M)
      (E : RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData ℤ N),
      Nonempty (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ N
        (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleAsOpposite ℤ M) 0 ≃+
        ∀ (j : D.summandIndex) (l : E.summandIndex),
          ZMod (Nat.gcd (D.combined_coefficient j).natAbs (E.combined_coefficient l).natAbs)) ∧
      Nonempty (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ N
        (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleAsOpposite ℤ M) 1 ≃+
        ∀ (i : D.Index) (l : E.Index),
          ZMod (Nat.gcd (D.quotientGenerator i).natAbs (E.quotientGenerator l).natAbs)) ∧
      ∀ n : ℕ, Subsingleton (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ N
        (RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleAsOpposite ℤ M) (n + 2)) := by
  obtain ⟨D, hD⟩ := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.exists_data_with_nonzero_coefficients ℤ M
  obtain ⟨E, hE⟩ := RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID.Auxiliary.exists_data_with_nonzero_coefficients ℤ N
  exact ⟨D, E,
    RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.componentAtZero_addEquiv_pi_zmod_gcd D E,
    RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.componentAtOne_addEquiv_pi_zmod_gcd D E hD hE,
    fun n => RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.componentAtNatAddTwo_subsingleton N n⟩

section Examples

example : Nonempty (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ
    (ZMod 4) (ModuleCat.of ℤᵐᵒᵖ (ZMod 6)) 0 ≅ AddCommGrpCat.of (ZMod 2)) := by
  have h := RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.componentAtZero_zmod_iso_zmod_gcd 6 4
  rwa [show Nat.gcd 6 4 = 2 from by norm_num] at h

example : Nonempty (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ
    (ZMod 0) (ModuleCat.of ℤᵐᵒᵖ (ZMod 6)) 0 ≅ AddCommGrpCat.of (ZMod 6)) := by
  have h := RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.componentAtZero_zmod_iso_zmod_gcd 6 0
  rwa [Nat.gcd_zero_right] at h

example : Limits.IsZero (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup ℤ ℤ
    (ModuleCat.of ℤᵐᵒᵖ (ZMod 6)) 1) :=
  RepresentationTheory.PolynomialQuotientZModAuxiliary.auxiliaryZModDegreeOneIsZero 6 (by norm_num)

example : True := by
  have := RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.exists_gcdZModComponentEquivalences_and_higher_subsingleton
    (M := ZMod 6) (N := ℤ × ZMod 4)
  trivial

end Examples

end RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences
