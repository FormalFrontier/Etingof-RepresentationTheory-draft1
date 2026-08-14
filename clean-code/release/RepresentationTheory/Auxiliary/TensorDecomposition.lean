/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.Auxiliary.MutualCentralizers
import RepresentationTheory.Centralizer.LinearMaps

open scoped TensorProduct

namespace RepresentationTheory.Auxiliary.TensorDecomposition

open RepresentationTheory.Auxiliary.MutualCentralizers
open RepresentationTheory.Centralizer.LinearMaps

set_option backward.isDefEq.respectTransparency false

universe u v

variable (k : Type u) [Field k]
  (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- The ring structure carried by the displayed subtype. -/
noncomputable local instance (priority := high) auxiliarySubtypeRing :
    Ring (permutationActionAlgebra k V n) := (permutationActionAlgebra k V n).toRing

set_option maxHeartbeats 3200000 in
-- The outer budget covers the centralizer transport and deep subalgebra instance chain.
set_option synthInstance.maxHeartbeats 1600000 in
/-- An auxiliary existence statement for an indexed direct sum of tensor products, where
linearly equivalent second tensor factors have equal indices. -/
@[source_ref"Chapter5/Theorem5.18.4"(role:=supporting)]
theorem existsAuxiliaryDirectSumTensorProductDecomposition
    [IsAlgClosed k] [CharZero k] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type (max u v))
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module (permutationActionAlgebra k V n) (S i))
      (_ : ∀ i, IsScalarTower k (permutationActionAlgebra k V n) (S i))
      (_ : ∀ i, IsSimpleModule (permutationActionAlgebra k V n) (S i))
      (_ : ∀ i j, Nonempty (S i ≃ₗ[permutationActionAlgebra k V n] S j) → i = j)
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → Type (max u v)) (_ : ∀ i, AddCommGroup (L i))
      (_ : ∀ i, Module k (L i))
      (_ : ∀ i, Module (auxiliaryEndomorphismAlgebra k V n) (L i))
      (_ : ∀ i, IsSimpleModule (auxiliaryEndomorphismAlgebra k V n) (L i)),
      (∀ i j, Nonempty (L i ≃ₗ[auxiliaryEndomorphismAlgebra k V n] L j) → i = j) ∧
      Nonempty (auxiliarySpace k V n ≃ₗ[k]
        DirectSum ι (fun i => S i ⊗[k] L i)) := by
  haveI := permutationActionAlgebra_semisimple k V n
  haveI := faithfulSMul_permutationActionAlgebra_auxiliarySpace k V n
  obtain ⟨ι, hι, hι_dec, S', hS'_simp, hS'_dist, hS'_fin, hL_simp, e, _he⟩ :=
    exists_auxiliarySpace_decomposition_evaluation k V n
  have h_eq : Subalgebra.centralizer k
      (permutationActionAlgebra k V n : Set (Module.End k (auxiliarySpace k V n))) =
        auxiliaryEndomorphismAlgebra k V n :=
    (mutual_centralizer_algebras k V n).2.symm
  haveI hsimpI : ∀ i, IsSimpleModule (permutationActionAlgebra k V n) (S' i) := hS'_simp
  rw [← h_eq]
  refine ⟨ι, hι, hι_dec, fun i => ↥(S' i),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance,
    hS'_simp, hS'_dist, hS'_fin,
    fun i => (↥(S' i) →ₗ[permutationActionAlgebra k V n] auxiliarySpace k V n),
    fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance,
    hL_simp, ?_, ⟨e⟩⟩
  intro i j hiso
  obtain ⟨f⟩ := hiso
  exact Subalgebra.centralizer.linearMapEquiv_index_eq k (auxiliarySpace k V n)
    (permutationActionAlgebra k V n) S' hS'_dist i j ⟨f⟩

end RepresentationTheory.Auxiliary.TensorDecomposition
