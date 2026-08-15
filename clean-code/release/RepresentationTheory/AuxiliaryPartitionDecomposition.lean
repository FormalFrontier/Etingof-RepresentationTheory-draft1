/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial

namespace RepresentationTheory.AuxiliaryPartitionDecomposition

open RepresentationTheory.PartitionAuxiliary
open RepresentationTheory.PartitionLinearMapVanishing
open SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter

/-- An auxiliary natural-number value associated with a pair of partitions. -/
noncomputable abbrev auxiliaryNatValue
    (n : ℕ) (mu nu : Nat.Partition n) : ℕ :=
  auxiliaryPartitionNat n mu nu

/-- An auxiliary partition-indexed submodule of the displayed module. -/
noncomputable abbrev auxiliarySubmodule
    (n : ℕ) (mu nu : Nat.Partition n) :=
  isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
    (partitionSubmodule n nu)

/-- An auxiliary type indexed by a natural number and two partitions of that number. -/
noncomputable abbrev auxiliaryFamily
    (n : ℕ) (mu nu : Nat.Partition n) :=
  Fin (auxiliaryNatValue n mu nu) → ↥(partitionSubmodule n nu)

/-- An auxiliary linear equivalence between the displayed submodule and the corresponding
partition-indexed type. -/
noncomputable def auxiliarySubmoduleLinearEquiv (n : ℕ) (mu nu : Nat.Partition n) :
    ↥(auxiliarySubmodule n mu nu) ≃ₗ[natIndexedType n]
      auxiliaryFamily n mu nu :=
  Classical.choice (nonempty_linearEquiv_isotypicComponent_pi n mu nu)

/-- An auxiliary linear equivalence from the displayed module to a direct sum indexed by
partitions. -/
noncomputable def auxiliaryDirectSumLinearEquiv (n : ℕ) (mu : Nat.Partition n) :
    partitionIndexedType n mu ≃ₗ[natIndexedType n]
      DirectSum (Nat.Partition n) (fun nu => auxiliaryFamily n mu nu) :=
  (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (fun nu : Nat.Partition n =>
        auxiliarySubmodule n mu nu))
      (isotypicComponent_isInternal n mu)).symm.trans
    (DFinsupp.mapRange.linearEquiv (fun nu => auxiliarySubmoduleLinearEquiv n mu nu))

/-- The auxiliary natural-number value is zero when the displayed relation between the partitions
fails. -/
theorem auxiliaryNatValue_eq_zero_of_not_relation
    (n : ℕ) (mu nu : Nat.Partition n)
    (h : ¬ partitionRelation nu mu) :
    auxiliaryNatValue n mu nu = 0 :=
  auxiliaryPartitionNat_eq_zero_of_not_auxiliaryRelation n mu nu h

/-- When the displayed relation between two partitions fails, the corresponding auxiliary type is
a subsingleton. -/
theorem auxiliaryFamily_subsingleton_of_not_relation
    (n : ℕ) (mu nu : Nat.Partition n)
    (h : ¬ partitionRelation nu mu) :
    Subsingleton (auxiliaryFamily n mu nu) := by
  change Subsingleton
    (Fin (auxiliaryPartitionNat n mu nu) → ↥(partitionSubmodule n nu))
  rw [auxiliaryPartitionNat_eq_zero_of_not_auxiliaryRelation n mu nu h]
  infer_instance

/-- The auxiliary natural-number value of a partition paired with itself is one. -/
theorem auxiliaryNatValue_self (n : ℕ) (mu : Nat.Partition n) :
    auxiliaryNatValue n mu mu = 1 :=
  auxiliaryPartitionNat_self n mu

/-- An auxiliary linear equivalence between a diagonal component and the displayed submodule. -/
noncomputable def auxiliaryDiagonalLinearEquiv (n : ℕ) (mu : Nat.Partition n) :
    auxiliaryFamily n mu mu ≃ₗ[natIndexedType n] ↥(partitionSubmodule n mu) := by
  change (Fin (auxiliaryPartitionNat n mu mu) → ↥(partitionSubmodule n mu))
    ≃ₗ[natIndexedType n] ↥(partitionSubmodule n mu)
  exact
    (LinearEquiv.cast (R := natIndexedType n)
      (M := fun k : ℕ => Fin k → ↥(partitionSubmodule n mu))
      (auxiliaryPartitionNat_self n mu)).trans
      (LinearEquiv.funUnique (Fin 1) (natIndexedType n)
        ↥(partitionSubmodule n mu))

end RepresentationTheory.AuxiliaryPartitionDecomposition
