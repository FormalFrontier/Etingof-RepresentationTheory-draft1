/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.AuxiliaryModuleData
import RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
import RepresentationTheory.GeneralLinear.InvariantSubtype

set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

/-!
# Auxiliary representations of general linear groups

This file constructs finite-dimensional general linear group representations from auxiliary
integer-valued parameters, together with character-twist preservation results for simplicity and
semisimplicity.
-/

noncomputable section

open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

/-! ## Invariant submodules -/

namespace RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary

section StableSubmodule

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- Regards a submodule preserved by every element of the represented monoid as a submodule over the monoid algebra. -/
def invariantSubmodule (rho : Representation k G V)
    (P : Submodule k rho.asModule)
    (hP : ∀ (g : G), ∀ x ∈ P, rho g (rho.asModuleEquiv x) ∈ P) :
    Submodule (MonoidAlgebra k G) rho.asModule where
  carrier := P
  add_mem' hx hy := P.add_mem hx hy
  zero_mem' := P.zero_mem
  smul_mem' r x hx := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r1 r2 h1 h2 => rw [add_smul]; exact P.add_mem h1 h2
    | single g a =>
        have hsingle : (MonoidAlgebra.single g a : MonoidAlgebra k G) =
            a • MonoidAlgebra.single g (1 : k) := by
          rw [MonoidAlgebra.smul_single', mul_one]
        rw [hsingle, smul_assoc]
        apply P.smul_mem
        rw [Representation.single_smul, one_smul]
        exact hP g x hx

/-- Membership in the induced monoid-algebra submodule is equivalent to membership in the original invariant submodule. -/
@[simp] theorem mem_invariantSubmodule_iff (rho : Representation k G V)
    (P : Submodule k rho.asModule)
    (hP : ∀ (g : G), ∀ x ∈ P, rho g (rho.asModuleEquiv x) ∈ P)
    (x : rho.asModule) :
    x ∈ invariantSubmodule rho P hP ↔ x ∈ P :=
  Iff.rfl

end StableSubmodule

end RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary

/-! ## Character twists -/

namespace RepresentationTheory.GeneralLinear.AuxiliaryRepresentations

section CharTwistSimple

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The auxiliary representation construction from a unit-valued monoid homomorphism preserves simplicity. -/
theorem isSimpleModule_auxiliaryRepresentationConstruction
    (c : G →* kˣ) (rho : Representation k G V)
    [hsimp : IsSimpleModule (MonoidAlgebra k G) rho.asModule] :
    IsSimpleModule (MonoidAlgebra k G) (twistByCharacter c rho).asModule := by
  haveI hnt : Nontrivial rho.asModule :=
    (Submodule.nontrivial_iff (MonoidAlgebra k G)).mp hsimp.toNontrivial
  haveI : Nontrivial (twistByCharacter c rho).asModule :=
    (show Nontrivial rho.asModule from hnt)
  haveI : Nontrivial (Submodule (MonoidAlgebra k G) (twistByCharacter c rho).asModule) :=
    (Submodule.nontrivial_iff (MonoidAlgebra k G)).mpr inferInstance
  rw [isSimpleModule_iff]
  refine ⟨fun W => ?_⟩
  let P : Submodule k rho.asModule := W.restrictScalars k
  have hmemP : ∀ x : rho.asModule, x ∈ P ↔
      (show (twistByCharacter c rho).asModule from x) ∈ W := fun _ => Iff.rfl
  have hP : ∀ (g : G), ∀ x ∈ P, rho g (rho.asModuleEquiv x) ∈ P := by
    intro g x hx
    rw [hmemP] at hx
    have heq : rho g (rho.asModuleEquiv x) =
        ((c g)⁻¹ : k) • ((MonoidAlgebra.single g (1 : k)) •
          (show (twistByCharacter c rho).asModule from x)) := by
      rw [Representation.single_smul, one_smul, twistByCharacter_apply, smul_smul,
        inv_mul_cancel₀ (Units.ne_zero (c g)), one_smul]
      rfl
    rw [hmemP, heq]
    exact (W.restrictScalars k).smul_mem _ (W.smul_mem _ hx)
  rcases hsimp.eq_bot_or_eq_top
      (RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary.invariantSubmodule
        rho P hP) with h | h
  · left
    rw [Submodule.eq_bot_iff] at h ⊢
    intro x hx
    exact h x
      ((RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary.mem_invariantSubmodule_iff
        rho P hP x).mpr ((hmemP x).mpr hx))
  · right
    rw [Submodule.eq_top_iff'] at h ⊢
    intro x
    exact (hmemP x).mp
      ((RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary.mem_invariantSubmodule_iff
        rho P hP x).mp (h x))

/-- The auxiliary representation construction from a unit-valued monoid homomorphism preserves semisimplicity. -/
theorem isSemisimpleModule_auxiliaryRepresentationConstruction
    (c : G →* kˣ) (rho : Representation k G V)
    [hss : IsSemisimpleModule (MonoidAlgebra k G) rho.asModule] :
    IsSemisimpleModule (MonoidAlgebra k G) (twistByCharacter c rho).asModule := by
  have hPrho : ∀ (W : Submodule (MonoidAlgebra k G) (twistByCharacter c rho).asModule)
      (g : G), ∀ x ∈ W.restrictScalars k, rho g (rho.asModuleEquiv x) ∈ W.restrictScalars k := by
    intro W g x hx
    have heq : rho g (rho.asModuleEquiv x) =
        ((c g)⁻¹ : k) • ((MonoidAlgebra.single g (1 : k)) •
          (show (twistByCharacter c rho).asModule from x)) := by
      rw [Representation.single_smul, one_smul, twistByCharacter_apply, smul_smul,
        inv_mul_cancel₀ (Units.ne_zero (c g)), one_smul]
      rfl
    rw [heq]
    exact (W.restrictScalars k).smul_mem _ (W.smul_mem _ hx)
  have hPchi : ∀ (V' : Submodule (MonoidAlgebra k G) rho.asModule)
      (g : G), ∀ x ∈ V'.restrictScalars k,
        (twistByCharacter c rho) g ((twistByCharacter c rho).asModuleEquiv x) ∈
          V'.restrictScalars k := by
    intro V' g x hx
    have heq : (twistByCharacter c rho) g ((twistByCharacter c rho).asModuleEquiv x) =
        ((c g : k)) • ((MonoidAlgebra.single g (1 : k)) • (show rho.asModule from x)) := by
      rw [Representation.single_smul, one_smul, twistByCharacter_apply]
      rfl
    rw [heq]
    exact (V'.restrictScalars k).smul_mem _ (V'.smul_mem _ hx)
  let toRho : Submodule (MonoidAlgebra k G) (twistByCharacter c rho).asModule →
      Submodule (MonoidAlgebra k G) rho.asModule :=
    fun W =>
      RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary.invariantSubmodule
        rho (W.restrictScalars k) (hPrho W)
  let toChi : Submodule (MonoidAlgebra k G) rho.asModule →
      Submodule (MonoidAlgebra k G) (twistByCharacter c rho).asModule :=
    fun V' =>
      RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary.invariantSubmodule
        (twistByCharacter c rho) (V'.restrictScalars k) (hPchi V')
  have mem_toRho : ∀ (W : Submodule (MonoidAlgebra k G) (twistByCharacter c rho).asModule)
      (x : rho.asModule), x ∈ toRho W ↔ x ∈ W :=
    fun W x =>
      RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary.mem_invariantSubmodule_iff
        rho _ (hPrho W) x
  have mem_toChi : ∀ (V' : Submodule (MonoidAlgebra k G) rho.asModule)
      (x : (twistByCharacter c rho).asModule), x ∈ toChi V' ↔ x ∈ V' :=
    fun V' x =>
      RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary.mem_invariantSubmodule_iff
        (twistByCharacter c rho) _ (hPchi V') x
  let e : Submodule (MonoidAlgebra k G) (twistByCharacter c rho).asModule ≃o
      Submodule (MonoidAlgebra k G) rho.asModule :=
    { toFun := toRho
      invFun := toChi
      left_inv := fun W => SetLike.ext fun x => by rw [mem_toChi, mem_toRho]
      right_inv := fun V' => SetLike.ext fun x => by rw [mem_toRho, mem_toChi]
      map_rel_iff' := by
        intro W1 W2
        constructor
        · intro h x hx
          exact (mem_toRho W2 x).mp (h ((mem_toRho W1 x).mpr hx))
        · intro h x hx
          exact (mem_toRho W2 x).mpr (h ((mem_toRho W1 x).mp hx)) }
  exact (isSemisimpleModule_iff _ _).mpr e.symm.complementedLattice

end CharTwistSimple

end RepresentationTheory.GeneralLinear.AuxiliaryRepresentations

/-! ## Auxiliary general linear representations -/

variable {k : Type*} [Field k] [IsAlgClosed k]

namespace RepresentationTheory.AuxiliaryModuleData

/-- The natural-valued weight associated with the parameter is antitone. -/
theorem auxiliaryIndex.toNatWeight_antitone {n : ℕ} (lam : auxiliaryIndex n) :
    Antitone lam.toNatAt := by
  intro i j hij
  exact Int.toNat_le_toNat (by simpa [auxiliaryIndex.toNatAt] using lam.property hij)

end RepresentationTheory.AuxiliaryModuleData

namespace RepresentationTheory.GeneralLinear.AuxiliaryRepresentations

/-- Assigns a finite-dimensional representation of the general linear group to each auxiliary parameter over an algebraically closed field. -/
@[source_ref "Chapter5/Discussion_after_Definition5.23.1" (role := supporting)]
noncomputable def auxiliaryGeneralLinearFDRep
    (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n)
    (k : Type*) [Field k] [IsAlgClosed k] :
    FDRep k (Matrix.GeneralLinearGroup (Fin n) k) :=
  FDRep.of (twistByCharacter (generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ)))
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation
      k n lam.toNatAt))

/-- Identifies the representation underlying the auxiliary finite-dimensional representation with the result of the displayed auxiliary construction. -/
@[simp] theorem auxiliaryGeneralLinearFDRep_representation_eq_auxiliaryConstruction
    (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) :
    FDRep.ρ (auxiliaryGeneralLinearFDRep n lam k) =
      twistByCharacter (generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ)))
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation
          k n lam.toNatAt) :=
  rfl

/-- When the shift is zero, the auxiliary values formed from the finite-dimensional representation and its natural-valued weight are equal. -/
theorem auxiliaryGeneralLinearFDRep_auxiliaryValue_eq_of_shift_eq_zero
    [CharZero k] (n : ℕ)
    (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n)
    (hshift : lam.toNat = 0) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter
        k n (auxiliaryGeneralLinearFDRep n lam k) =
      RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial
        n lam.toNatAt := by
  have hchar : (generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ))) = 1 := by
    rw [hshift]; simp
  have hrep2 :
      twistByCharacter (1 : Matrix.GeneralLinearGroup (Fin n) k →* kˣ)
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation
          k n lam.toNatAt) =
          RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation
            k n lam.toNatAt := by
    ext g v
    simp [twistByCharacter_apply]
  have hrep : auxiliaryGeneralLinearFDRep n lam k =
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation
        k n lam.toNatAt := by
    rw [auxiliaryGeneralLinearFDRep, hchar, hrep2,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation]
  rw [hrep,
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation_weightCharacter
      k n lam.toNatAt
    lam.toNatWeight_antitone]

/-- Over the complex numbers, the auxiliary general linear representation is simple when the sum of its natural weights is at most the rank. -/
theorem isSimpleModule_auxiliaryGeneralLinearFDRep_of_weightSum_le
    (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n)
    (hN : (∑ i, lam.toNatAt i) ≤ n) :
    IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) ℂ))
      (Representation.asModule (FDRep.ρ (auxiliaryGeneralLinearFDRep n lam ℂ))) := by
  haveI : IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) ℂ))
      (Representation.asModule
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation
          ℂ n lam.toNatAt)) :=
    RepresentationTheory.GeneralLinear.InvariantSubtype.GeneralLinear.isSimpleModule_representationComplex
      n lam.toNatAt lam.toNatWeight_antitone hN
  rw [auxiliaryGeneralLinearFDRep_representation_eq_auxiliaryConstruction]
  exact isSimpleModule_auxiliaryRepresentationConstruction
    (generalLinearGroupToUnits ℂ n ^ (-(lam.toNat : ℤ)))
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation
      ℂ n lam.toNatAt)

/-! ## Bare and alternative representations -/

/-- Defines an alternative general linear group action on an auxiliary space determined by the indexed parameter. -/
@[source_ref "Chapter5/Discussion_after_Definition5.23.1/Derived01" (role := supporting)]
noncomputable def generalLinearRepresentationOnAuxiliarySpaceAlt
    (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n)
    (k : Type*) [Field k] [IsAlgClosed k] :
    Representation k (Matrix.GeneralLinearGroup (Fin n) k)
      (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :=
  twistByCharacter (generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ)))
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation
      k n lam.toNatAt)

/-- Produces an auxiliary finite-dimensional representation of `GL (Fin n, k)` from the given indexed parameter. -/
noncomputable def auxiliaryGeneralLinearFDRepAlt
    (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n)
    (k : Type*) [Field k] [IsAlgClosed k] :
    FDRep k (Matrix.GeneralLinearGroup (Fin n) k) :=
  auxiliaryGeneralLinearFDRep n lam.auxiliaryMap k

/-- Defines the general linear group action on an auxiliary space indexed by the parameter. -/
noncomputable def generalLinearRepresentationOnAuxiliarySpace
    (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n)
    (k : Type*) [Field k] [IsAlgClosed k] :
    Representation k (Matrix.GeneralLinearGroup (Fin n) k)
      (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k) :=
  generalLinearRepresentationOnAuxiliarySpaceAlt n lam.auxiliaryMap k

end RepresentationTheory.GeneralLinear.AuxiliaryRepresentations
