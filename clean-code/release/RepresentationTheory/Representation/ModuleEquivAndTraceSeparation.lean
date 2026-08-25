/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Module.IndexedCoordinateProjections
import RepresentationTheory.AuxiliaryCharacter
import RepresentationTheory.UnitTupleActions
import RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
import RepresentationTheory.GeneralLinear.InvariantSubtype
import RepresentationTheory.AuxiliaryGeneralLinearTrace
import RepresentationTheory.Alignment.Attribute

open CategoryTheory

noncomputable section

namespace RepresentationTheory.Representation.ModuleEquivAndTraceSeparation

open AuxiliaryCharacter
open AuxiliaryGeneralLinearTrace
open GeneralLinear.InvariantSubtype.GeneralLinear
open GeneralLinearGroup.WeightCharacter
open Module.IndexedCoordinateProjections
open TensorPower
open UnitTupleActions

variable {k G : Type*} [CommSemiring k] [Monoid G]
variable {V W : Type*} [AddCommMonoid V] [Module k V]
  [AddCommMonoid W] [Module k W]

/-- A linear equivalence of modules induced by two representations, regarded as a linear
equivalence over the coefficient semiring. -/
def representationLinearEquiv {rho : Representation k G V} {sigma : Representation k G W}
    (equiv : Representation.asModule rho ≃ₗ[MonoidAlgebra k G]
      Representation.asModule sigma) : V ≃ₗ[k] W :=
  rho.asModuleEquiv.symm ≪≫ₗ equiv.restrictScalars k ≪≫ₗ sigma.asModuleEquiv

/-- The underlying linear equivalence of representation modules intertwines the actions of every
monoid element. -/
theorem representationLinearEquiv_intertwines {rho : Representation k G V}
    {sigma : Representation k G W}
    (equiv : Representation.asModule rho ≃ₗ[MonoidAlgebra k G]
      Representation.asModule sigma)
    (g : G) (v : V) :
    representationLinearEquiv equiv (rho g v) =
      sigma g (representationLinearEquiv equiv v) := by
  simp only [representationLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  rw [rho.asModuleEquiv_symm_map_rho, map_smul, sigma.asModuleEquiv_map_smul,
    MonoidAlgebra.of_apply, sigma.asAlgebraHom_single, one_smul]

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

omit [CharZero k] in
/-- The auxiliary value of a finite-dimensional representation is unchanged after rebuilding it
from its underlying representation. -/
theorem auxiliary_fdRep_value_of_representation_eq (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    weightCharacter k N (FDRep.of M.ρ) = weightCharacter k N M :=
  auxiliaryPolynomial_eq_of_linearEquiv
    k N M.ρ M.ρ (LinearEquiv.refl k M) (fun _ _ => rfl)

/-- The module underlying the finite-dimensional representation associated with an antitone
natural-valued family is simple. -/
@[source_ref"Chapter5/Discussion_after_Definition5.23.1/Derived01"(role:=supporting)]
theorem isSimpleModule_fdRep_of_antitone (N : ℕ) (lam : Fin N → ℕ)
    (hlam : Antitone lam) :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (schurRepresentation k N lam).ρ) := by
  letI : AddCommGroup (schurSubmodule k N lam) :=
    { Module.addCommMonoidToAddCommGroup k with
      toAddCommMonoid := (schurSubmodule k N lam).addCommMonoid }
  haveI := isSimpleModule_invariantSubtype (k := k) N lam hlam
  refine isSimpleModule_of_auxiliary_piTensorProduct_action k
    (N := N) (n := ∑ i, lam i)
    (M := ↥(schurSubmodule k N lam))
    (schurSubmoduleRepresentation k N lam) ?_
  intro g x
  apply Subtype.ext
  rfl

set_option linter.unusedDecidableInType false in
/-- A rational linear combination of traces of pairwise nonisomorphic simple finite-dimensional
representations has zero coefficients if it vanishes on all displayed diagonal elements. -/
theorem trace_coefficients_eq_zero_of_diagonal_sum_eq_zero
    (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLalg : ∀ i, GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (L i).ρ)
    (hLsimp : ∀ i, IsSimpleModule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (L i).ρ))
    (hLdist : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j))))
    (c : ι → ℚ)
    (htorus : ∀ t : Fin N → kˣ,
      ∑ i, (c i : k) • LinearMap.trace k (L i)
        ((L i).ρ (unitTupleElement k N t)) = 0) :
    ∀ i, c i = 0 := by
  classical
  have hdist : Pairwise (fun i j => ¬ Nonempty
      (Representation.asModule (L i).ρ ≃ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin N) k)] Representation.asModule (L j).ρ)) := by
    intro i j hij hcon
    obtain ⟨equiv⟩ := hcon
    exact hLdist hij ⟨Action.mkIso (representationLinearEquiv equiv).toFGModuleCatIso
      (fun g => by ext x; exact representationLinearEquiv_intertwines equiv g x)⟩
  have hLI := linearIndependent_moduleTraceLinearMap (𝕜 := k)
    (A := MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
    (fun i => Representation.asModule (L i).ρ) hLsimp hdist
  have hbridge : ∀ (i : ι) (g : Matrix.GeneralLinearGroup (Fin N) k),
      moduleTraceLinearMap (fun i => Representation.asModule (L i).ρ) i
        (MonoidAlgebra.of k _ g) = LinearMap.trace k (L i) ((L i).ρ g) := by
    intro i g
    have hmap : (scalarActionAlgHom
        (fun i => Representation.asModule (L i).ρ) i (MonoidAlgebra.of k _ g) :
          Representation.asModule (L i).ρ →ₗ[k] Representation.asModule (L i).ρ) =
        (L i).ρ g := by
      ext v
      rw [scalarActionAlgHom_apply, ← Representation.asAlgebraHom_of (L i).ρ g]
      rfl
    rw [moduleTraceLinearMap_apply, hmap]
    rfl
  have hF0 : ∀ a, (∑ i, (c i : k) •
      (moduleTraceLinearMap (fun i => Representation.asModule (L i).ρ) i :
        MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k) →ₗ[k] k)) a = 0 := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | hM g =>
        have hg0 := auxiliary_trace_sum_eq_zero_of_unit_tuple N L hLalg
          (fun i => (c i : k)) htorus g
        rw [LinearMap.sum_apply]
        simpa only [LinearMap.smul_apply, hbridge] using hg0
    | hadd x y hx hy => simp only [map_add, hx, hy, add_zero]
    | hsmul r x hx => simp only [map_smul, hx, smul_zero]
  have hfun : (∑ i, (c i : k) •
      (moduleTraceLinearMap (fun i => Representation.asModule (L i).ρ) i :
        MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k) →ₗ[k] k)) = 0 :=
    LinearMap.ext hF0
  intro i
  have hci : (c i : k) = 0 :=
    Fintype.linearIndependent_iff.mp hLI (fun i => (c i : k)) hfun i
  exact_mod_cast hci

end RepresentationTheory.Representation.ModuleEquivAndTraceSeparation
