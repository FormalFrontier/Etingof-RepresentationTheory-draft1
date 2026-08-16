/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteGroupRepresentationExamples

open MonoidAlgebra

namespace RepresentationTheory.SimpleSymmetricGroupRepresentations

/-- A simple finite-dimensional complex representation of a symmetric group satisfies the stated property. -/
theorem simpleSymmetricGroupRepresentation_property (n : ℕ)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) ρ.asModule) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by
  classical
  haveI := hρ
  obtain ⟨I, ⟨φ_M⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
      (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) ρ.asModule
  haveI : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) I :=
    IsSimpleModule.congr φ_M.symm
  obtain ⟨la, ⟨φ_I⟩⟩ :=
    RepresentationTheory.SimpleModule.SubtypeRepresentation.exists_linearEquiv_to_subtype n I
  set Ψ := φ_M.trans φ_I with hΨ
  set c :=
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC
      n la with hc
  have hc_mem : c ∈ RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la :=
    Submodule.subset_span rfl
  set ψ : V →ₗ[ℂ] MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
    ((RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la).subtype.restrictScalars ℂ).comp
      ((Ψ.restrictScalars ℂ).toLinearMap.comp ρ.asModuleEquiv.symm.toLinearMap) with hψdef
  have hψ_apply : ∀ v : V,
      ψ v = (Ψ (ρ.asModuleEquiv.symm v) : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) := by
    intro v; rfl
  have hψ : ∀ (g : Equiv.Perm (Fin n)) (v : V),
      ψ (ρ g v) = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g * ψ v := by
    intro g v
    rw [hψ_apply, hψ_apply, ρ.asModuleEquiv_symm_map_rho, map_smul]
    simp only [Submodule.coe_smul, smul_eq_mul]
  have hcne : c ≠ 0 := by
    intro h0
    rw [hc] at h0
    exact RepresentationTheory.PartitionAuxiliary.self_mul_ne_zero n la
      (by rw [h0, mul_zero])
  set v₀ : V := ρ.asModuleEquiv (Ψ.symm ⟨c, hc_mem⟩) with hv₀def
  have hv₀ : ψ v₀ = c := by
    rw [hψ_apply, hv₀def, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  exact
    RepresentationTheory.FiniteGroupRepresentationExamples.auxiliaryPropertyOfEquivariantMapWithNonzeroRealImage
      ρ hρ ψ hψ c
      (RepresentationTheory.FiniteGroupRepresentationExamples.auxiliarySymmetricGroupCoefficient_im_eq_zero
        n la) v₀ hv₀ hcne

/-- The value associated with a simple finite-dimensional complex representation of a symmetric group is equal to one. -/
theorem simpleSymmetricGroupRepresentation_value_eq_one (n : ℕ)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) ρ.asModule) :
    RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = 1 :=
  RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_eq_one_of_auxiliary_property
    ρ hρ (simpleSymmetricGroupRepresentation_property n ρ hρ)

end RepresentationTheory.SimpleSymmetricGroupRepresentations
