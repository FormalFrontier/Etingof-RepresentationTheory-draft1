/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.PartitionedDecomposition

open scoped TensorProduct
open RepresentationTheory.Auxiliary.MutualCentralizers RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich RepresentationTheory.PartitionedDecomposition

universe u v

/-- There exist auxiliary data satisfying the displayed subsingleton-fiber, simple-module, uniqueness, equivariance, and compatibility conditions. -/
theorem RepresentationTheory.AuxiliarySimpleModuleData.exists_auxiliary_simple_module_data
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    ∃ (iota : Type) (_ : Fintype iota) (_ : DecidableEq iota)
      (S : iota → Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)),
      letI : ∀ i, AddCommGroup (S i) := fun i =>
        { Module.addCommMonoidToAddCommGroup k with
          toAddCommMonoid := (S i).addCommMonoid }
      ∃ (label : iota ↪ Nat.Partition n)
        (specht : ∀ i, ↥(S i) ≃ₗ[k] ↥(RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n (label i))),
      (∀ p, Subsingleton {i : iota // label i = p}) ∧
      (∀ i, IsSimpleModule
        (↥(Subalgebra.centralizer k
          (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))
        (↥(S i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)) ∧
      (∀ i j, Nonempty
        ((↥(S i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) ≃ₗ[
          ↥(Subalgebra.centralizer k
            (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))))]
          (↥(S j) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)) → i = j) ∧
      (∀ (i : iota) (a : MonoidAlgebra k (Equiv.Perm (Fin n))) (x : ↥(S i)),
        specht i ((RepresentationTheory.PartitionedDecomposition.symmetricGroupAlgebraAction k V n a) • x) = a • specht i x) ∧
      ∃ e : RepresentationTheory.PartitionedDecomposition.DecompositionData k n S label,
        ∀ (b : ↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n)) (x : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n),
          e.linearEquiv (b.val x) =
            RepresentationTheory.PartitionedDecomposition.decompositionCentralizerAction k n S label
              (⟨b.val, RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra
                k V n b.property⟩ :
                ↥(Subalgebra.centralizer k
                  (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n :
                    Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))
              (e.linearEquiv x) :=
  RepresentationTheory.PartitionedDecomposition.existsIndexedSimpleDecomposition k V n
