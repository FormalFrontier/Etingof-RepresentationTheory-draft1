/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
import RepresentationTheory.GeneralLinearGroup.ExteriorPower

open scoped TensorProduct
open Matrix

noncomputable section

namespace RepresentationTheory.FiniteDimensionalRepresentations.Auxiliary

open RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
open RepresentationTheory.GeneralLinearGroup.Auxiliary
open RepresentationTheory.GeneralLinearGroup.ExteriorPower
open RepresentationTheory.GeneralLinearGroup.WeightCharacter

attribute [local instance] auxiliarySubtypeAddCommGroup

/-- The representation obtained from the auxiliary construction satisfies the displayed
auxiliary predicate. -/
theorem auxiliary_representation_property (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (N : ℕ) (lam : Fin N → ℕ) :
    HasAuxiliaryMapProperty N (FDRep.of (auxiliarySubtypeRepresentation k N lam)).ρ := by
  rw [FDRep.of_ρ']
  have hrestrict : HasAuxiliaryMapProperty N (schurSubmoduleRepresentation k N lam) :=
    (auxiliaryRepresentation_property k N (∑ i, lam i)).auxiliary_restrict
      (schurSubmodule k N lam)
      (fun g v hv => schurSubmodule_invariant k N lam g v hv)
  exact hrestrict.auxiliary_det_smul

end RepresentationTheory.FiniteDimensionalRepresentations.Auxiliary
