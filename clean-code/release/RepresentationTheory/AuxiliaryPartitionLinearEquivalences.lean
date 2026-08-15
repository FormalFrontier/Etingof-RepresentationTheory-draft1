/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryPartitionLinearIndependentFamily
import RepresentationTheory.Alignment.Attribute








namespace RepresentationTheory.AuxiliaryPartitionLinearEquivalences

noncomputable section

/-- An auxiliary type indexed by a natural number and two partitions of that number. -/


noncomputable abbrev auxiliaryFamily
    (n : ℕ) (mu nu : Nat.Partition n) :=
  Fin (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryPartitionPairNat n nu mu) → ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu)

/-- Builds the auxiliary component linear equivalence from the displayed equality. -/


noncomputable def auxiliaryComponentLinearEquivOfEq (n : ℕ)
    (mu nu : Nat.Partition n)
    (h : RepresentationTheory.AuxiliaryPartitionDecomposition.auxiliaryNatValue n mu nu = RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryPartitionPairNat n nu mu) :
    ↥(RepresentationTheory.AuxiliaryPartitionDecomposition.auxiliarySubmodule n mu nu) ≃ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n]
      auxiliaryFamily n mu nu :=
  (RepresentationTheory.AuxiliaryPartitionDecomposition.auxiliarySubmoduleLinearEquiv n mu nu).trans
    (LinearEquiv.cast (R := RepresentationTheory.PartitionAuxiliary.natIndexedType n)
      (M := fun k : ℕ => Fin k → ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu)) h)

/-- Builds the auxiliary direct-sum linear equivalence from the displayed family of equalities. -/


noncomputable def auxiliaryDirectSumLinearEquivOfEq (n : ℕ)
    (mu : Nat.Partition n)
    (h : ∀ nu : Nat.Partition n,
      RepresentationTheory.AuxiliaryPartitionDecomposition.auxiliaryNatValue n mu nu = RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryPartitionPairNat n nu mu) :
    RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu ≃ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n]
      DirectSum (Nat.Partition n) (fun nu => auxiliaryFamily n mu nu) :=
  (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (fun nu : Nat.Partition n =>
        RepresentationTheory.AuxiliaryPartitionDecomposition.auxiliarySubmodule n mu nu))
      (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.isotypicComponent_isInternal n mu)).symm.trans
    (DFinsupp.mapRange.linearEquiv
      (fun nu => auxiliaryComponentLinearEquivOfEq n mu nu (h nu)))

/-- An auxiliary linear equivalence between the displayed subspace and one component of the partition-indexed family. -/


noncomputable def auxiliaryComponentLinearEquiv (n : ℕ)
    (mu nu : Nat.Partition n) :
    ↥(RepresentationTheory.AuxiliaryPartitionDecomposition.auxiliarySubmodule n mu nu) ≃ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n]
      auxiliaryFamily n mu nu :=
  auxiliaryComponentLinearEquivOfEq n mu nu
    (RepresentationTheory.AuxiliaryPartitionLinearIndependentFamily.auxiliary_nat_values_eq n mu nu)

/-- An auxiliary linear equivalence from the displayed partition-dependent space to a direct sum indexed by partitions. -/
@[source_ref "Chapter5/Discussion_proof_of_Proposition5.14.1" (role := primary),
  source_ref "Chapter5/Proposition5.14.1" (role := primary)]



noncomputable def auxiliaryDirectSumLinearEquiv (n : ℕ)
    (mu : Nat.Partition n) :
    RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu ≃ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n]
      DirectSum (Nat.Partition n) (fun nu => auxiliaryFamily n mu nu) :=
  auxiliaryDirectSumLinearEquivOfEq n mu
    (RepresentationTheory.AuxiliaryPartitionLinearIndependentFamily.auxiliary_nat_values_eq n mu)

end

end RepresentationTheory.AuxiliaryPartitionLinearEquivalences
