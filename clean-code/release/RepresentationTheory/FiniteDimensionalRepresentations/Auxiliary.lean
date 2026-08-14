import RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
import RepresentationTheory.GeneralLinearGroup.ExteriorPower

open scoped TensorProduct
open Matrix

noncomputable section

namespace RepresentationTheory.FiniteDimensionalRepresentations.Auxiliary

/-- The representation obtained from the auxiliary construction satisfies the displayed auxiliary predicate. -/
theorem auxiliary_representation_property (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (N : ℕ) (lam : Fin N → ℕ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N
      (FDRep.of (RepresentationTheory.GeneralLinearGroup.ExteriorPower.auxiliarySubtypeRepresentation k N lam)).ρ := by
  rw [FDRep.of_ρ']
  have hrestrict :
      RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k N lam) :=
    (RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.auxiliaryRepresentation_property k N (∑ i, lam i)).auxiliary_restrict
      (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N lam)
      (fun g v hv => RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule_invariant k N lam g v hv)
  exact hrestrict.auxiliary_det_smul

end RepresentationTheory.FiniteDimensionalRepresentations.Auxiliary
