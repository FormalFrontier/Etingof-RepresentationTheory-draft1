/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import RepresentationTheory.SymmetricGroup.PartitionScalarAuxiliary
import RepresentationTheory.SimpleModuleTraceIdentities
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.AuxiliaryModuleData

noncomputable section

namespace RepresentationTheory.SymmetricGroup.SimpleModuleTrace

open scoped TensorProduct

open RepresentationTheory.Algebra.PartitionPermutation
open RepresentationTheory.Auxiliary.MutualCentralizers
open RepresentationTheory.AuxiliaryModuleData
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.SimpleModuleTraceIdentities
open RepresentationTheory.SymmetricGroup.PartitionScalarAuxiliary

/-- The ring structure on endomorphisms commuting with the finite symmetric-group action. -/
noncomputable local instance (priority := high) symmetricEndomorphismRing
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (n : ℕ) :
    Ring (permutationActionAlgebra k V n) := (permutationActionAlgebra k V n).toRing

/-! ### Simple submodules with prescribed permutation traces -/

/-- For an antitone natural-valued function on `Fin N`, the displayed expression is nonzero. -/
theorem complexValueNeZeroOfAntitone
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    symmetrizerEndomorphism ℂ N lam ≠ 0 := by
  intro h
  apply auxiliary_ne_bot_of_antitone (k := ℂ) N lam hlam
  change LinearMap.range (symmetrizerEndomorphism ℂ N lam) = ⊥
  rw [h, LinearMap.range_zero]

set_option maxHeartbeats 800000 in
-- Applying the generic trace-equivalence theorem needs the larger elaboration budgets.
set_option synthInstance.maxHeartbeats 400000 in
/-- Two simple complex submodules with equal prescribed traces for every restricted permutation
operator are linearly equivalent. -/
theorem nonemptyLinearEquivOfTraceEqComplex
    {N n : ℕ}
    (S S' : Submodule (permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (auxiliarySpace ℂ (Fin N → ℂ) n))
    [IsSimpleModule (↥(permutationActionAlgebra ℂ (Fin N → ℂ) n)) ↥S]
    [IsSimpleModule (↥(permutationActionAlgebra ℂ (Fin N → ℂ) n)) ↥S']
    (la : Nat.Partition n)
    (hS : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace ℂ ↥(S.restrictScalars ℂ)
          ((auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) n σ).toLinearMap.restrict
            (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
          partitionPermutationValue ℂ n la σ)
    (hS' : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace ℂ ↥(S'.restrictScalars ℂ)
          ((auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) n σ).toLinearMap.restrict
            (p := S'.restrictScalars ℂ) (q := S'.restrictScalars ℂ)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S' σ hv)) =
          partitionPermutationValue ℂ n la σ) :
    Nonempty (↥S ≃ₗ[↥(permutationActionAlgebra ℂ (Fin N → ℂ) n)] ↥S') :=
  nonemptyLinearEquiv_of_shared_trace_eq S S' la hS hS'

set_option maxHeartbeats 3200000 in
-- The direct-sum and tensor-product extensionality reduction needs the larger budgets.
set_option synthInstance.maxHeartbeats 1200000 in
/-- If the symmetrizer endomorphism vanishes on every block of a bimodule decomposition,
then it is the zero endomorphism. -/
private theorem youngSymEndomorphism_eq_zero_of_blocks_vanish
    (N : ℕ) (lam : Fin N → ℕ)
    {ι : Type} [DecidableEq ι]
    (S : ι → Submodule (permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))
      (auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i)))
    (e : auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i) ≃ₗ[ℂ]
      DirectSum ι (fun i => ↥(S i) ⊗[ℂ]
        (↥(S i) →ₗ[↥(permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))]
          auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i))))
    (he : ∀ (i : ι) (v : ↥(S i))
        (l : ↥(S i) →ₗ[↥(permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))]
          auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i)),
      e.symm (DirectSum.of _ i (v ⊗ₜ[ℂ] l)) = l v)
    (hvanish : ∀ (i : ι) (v : ↥(S i)), symmetrizerEndomorphism ℂ N lam v.val = 0) :
    symmetrizerEndomorphism ℂ N lam = 0 := by
  have hcomp : (symmetrizerEndomorphism ℂ N lam) ∘ₗ e.symm.toLinearMap = 0 := by
    apply DirectSum.linearMap_ext
    intro i
    apply TensorProduct.ext'
    intro v l
    simp only [LinearMap.comp_apply, LinearMap.zero_comp, LinearMap.zero_apply,
      DirectSum.lof_eq_of]
    have hbf := map_symmetrizerEndomorphism_tmul ℂ N lam S e he i v l
    have hzero : symmetrizerEndomorphismMem ℂ N lam • v = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_smul, ZeroMemClass.coe_zero, Subalgebra.smul_def,
        Module.End.smul_def, symmetrizerEndomorphismMem_val]
      exact hvanish i v
    rw [hzero, TensorProduct.zero_tmul, map_zero] at hbf
    have := congrArg e.symm hbf
    rwa [e.symm_apply_apply, map_zero] at this
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun hcomp (e x)
  rw [LinearMap.zero_apply, LinearMap.comp_apply] at hx
  rwa [LinearEquiv.coe_coe, e.symm_apply_apply] at hx

set_option maxHeartbeats 1600000 in
-- Choosing and comparing the block labels needs the larger elaboration budgets.
set_option synthInstance.maxHeartbeats 400000 in
set_option linter.unusedFintypeInType false in
/-- A decomposition into finite pairwise nonisomorphic simple complex submodules contains a
summand with the prescribed traces of all permutation operators; every other summand has traces
prescribed by a different partition. -/
theorem existsSimpleSubmoduleWithPrescribedTraceComplex
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule (permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))
      (auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i)))
    (hSimp : ∀ i,
      IsSimpleModule (↥(permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))) ↥(S i))
    (hDist : ∀ i j,
      Nonempty (↥(S i) ≃ₗ[↥(permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))]
        ↥(S j)) → i = j)
    (hSfin : ∀ i, Module.Finite ℂ ↥(S i))
    (e : auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i) ≃ₗ[ℂ]
      DirectSum ι (fun i => ↥(S i) ⊗[ℂ]
        (↥(S i) →ₗ[↥(permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))]
          auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i))))
    (he : ∀ (i : ι) (v : ↥(S i))
        (l : ↥(S i) →ₗ[↥(permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))]
          auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i)),
      e.symm (DirectSum.of _ i (v ⊗ₜ[ℂ] l)) = l v) :
    ∃ iLam : ι,
      (∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace ℂ ↥((S iLam).restrictScalars ℂ)
          ((auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ)
            (∑ i, lam i) σ).toLinearMap.restrict
            (p := (S iLam).restrictScalars ℂ) (q := (S iLam).restrictScalars ℂ)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule (S iLam) σ hv)) =
          partitionPermutationValue ℂ (∑ i, lam i) (partitionOfTuple N lam) σ) ∧
      (∀ i, i ≠ iLam → ∃ la' : Nat.Partition (∑ i, lam i),
        la' ≠ partitionOfTuple N lam ∧
        ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
          LinearMap.trace ℂ ↥((S i).restrictScalars ℂ)
            ((auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ)
              (∑ i, lam i) σ).toLinearMap.restrict
              (p := (S i).restrictScalars ℂ) (q := (S i).restrictScalars ℂ)
              (fun _ hv => mem_of_mem_symmetricInvariantSubmodule (S i) σ hv)) =
            partitionPermutationValue ℂ (∑ i, lam i) la' σ) := by
  have hlabexists : ∀ i, ∃ la' : Nat.Partition (∑ i, lam i),
      ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace ℂ ↥((S i).restrictScalars ℂ)
          ((auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ)
            (∑ i, lam i) σ).toLinearMap.restrict
            (p := (S i).restrictScalars ℂ) (q := (S i).restrictScalars ℂ)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule (S i) σ hv)) =
          partitionPermutationValue ℂ (∑ i, lam i) la' σ := by
    intro i
    haveI := hSimp i
    exact exists_trace_eq_of_isSimpleModule (S i)
  choose lab hlab using hlabexists
  have hUniq : ∀ i j, lab i = lab j → i = j := by
    intro i j hij
    haveI := hSimp i
    haveI := hSimp j
    apply hDist i j
    apply nonemptyLinearEquivOfTraceEqComplex (S i) (S j) (lab i) (hlab i)
    intro σ
    rw [hij]
    exact hlab j σ
  have hExists : ∃ iLam, lab iLam = partitionOfTuple N lam := by
    by_contra hcon
    push Not at hcon
    have hvanish : ∀ (i : ι) (v : ↥(S i)),
        symmetrizerEndomorphism ℂ N lam v.val = 0 := by
      intro i v
      haveI := hSimp i
      haveI : Module.Finite ℂ ↥((S i).restrictScalars ℂ) := hSfin i
      have hr := restriction_eq_zero_of_partition_ne N lam (S i) (lab i) (hlab i) (hcon i)
      have hv0 := LinearMap.congr_fun hr v
      rw [LinearMap.zero_apply] at hv0
      have := congrArg Subtype.val hv0
      rwa [LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] at this
    exact complexValueNeZeroOfAntitone N lam hlam
      (youngSymEndomorphism_eq_zero_of_blocks_vanish N lam S e he hvanish)
  obtain ⟨iLam, hLamEq⟩ := hExists
  refine ⟨iLam, ?_, ?_⟩
  · intro σ
    have := hlab iLam σ
    rwa [hLamEq] at this
  · intro i hi
    refine ⟨lab i, ?_, hlab i⟩
    intro hcontra
    exact hi (hUniq i iLam (hcontra.trans hLamEq.symm))

section General

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/-- Over an algebraically closed field of characteristic zero, the displayed value for an
antitone natural-valued function on `Fin N` is nonzero. -/
theorem valueNeZeroOfAntitone
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    symmetrizerEndomorphism k N lam ≠ 0 := by
  intro h
  apply auxiliary_ne_bot_of_antitone (k := k) N lam hlam
  change LinearMap.range (symmetrizerEndomorphism k N lam) = ⊥
  rw [h, LinearMap.range_zero]

set_option maxHeartbeats 3200000 in
-- The direct-sum and tensor-product extensionality reduction needs the larger budgets.
set_option synthInstance.maxHeartbeats 1200000 in
omit [IsAlgClosed k] [CharZero k] in
/-- General-field analogue of `youngSymEndomorphism_eq_zero_of_blocks_vanish`. -/
private theorem youngSymEndomorphism_eq_zero_of_blocks_vanish_general
    (N : ℕ) (lam : Fin N → ℕ)
    {ι : Type} [DecidableEq ι]
    (S : ι → Submodule (permutationActionAlgebra k (Fin N → k) (∑ i, lam i))
      (auxiliarySpace k (Fin N → k) (∑ i, lam i)))
    (e : auxiliarySpace k (Fin N → k) (∑ i, lam i) ≃ₗ[k]
      DirectSum ι (fun i => ↥(S i) ⊗[k]
        (↥(S i) →ₗ[↥(permutationActionAlgebra k (Fin N → k) (∑ i, lam i))]
          auxiliarySpace k (Fin N → k) (∑ i, lam i))))
    (he : ∀ (i : ι) (v : ↥(S i))
        (l : ↥(S i) →ₗ[↥(permutationActionAlgebra k (Fin N → k) (∑ i, lam i))]
          auxiliarySpace k (Fin N → k) (∑ i, lam i)),
      e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v)
    (hvanish : ∀ (i : ι) (v : ↥(S i)), symmetrizerEndomorphism k N lam v.val = 0) :
    symmetrizerEndomorphism k N lam = 0 := by
  have hcomp : (symmetrizerEndomorphism k N lam) ∘ₗ e.symm.toLinearMap = 0 := by
    apply DirectSum.linearMap_ext
    intro i
    apply TensorProduct.ext'
    intro v l
    simp only [LinearMap.comp_apply, LinearMap.zero_comp, LinearMap.zero_apply,
      DirectSum.lof_eq_of]
    have hbf := map_symmetrizerEndomorphism_tmul k N lam S e he i v l
    have hzero : symmetrizerEndomorphismMem k N lam • v = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_smul, ZeroMemClass.coe_zero, Subalgebra.smul_def,
        Module.End.smul_def, symmetrizerEndomorphismMem_val]
      exact hvanish i v
    rw [hzero, TensorProduct.zero_tmul, map_zero] at hbf
    have := congrArg e.symm hbf
    rwa [e.symm_apply_apply, map_zero] at this
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun hcomp (e x)
  rw [LinearMap.zero_apply, LinearMap.comp_apply] at hx
  rwa [LinearEquiv.coe_coe, e.symm_apply_apply] at hx

set_option maxHeartbeats 1600000 in
-- Choosing and comparing the block labels needs the larger elaboration budgets.
set_option synthInstance.maxHeartbeats 400000 in
set_option linter.unusedFintypeInType false in
/-- Over an algebraically closed field of characteristic zero, a decomposition into finite
pairwise nonisomorphic simple submodules contains a summand with the prescribed traces of all
permutation operators; every other summand has traces prescribed by a different partition. -/
theorem existsSimpleSubmoduleWithPrescribedTrace
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule (permutationActionAlgebra k (Fin N → k) (∑ i, lam i))
      (auxiliarySpace k (Fin N → k) (∑ i, lam i)))
    (hSimp : ∀ i,
      IsSimpleModule (↥(permutationActionAlgebra k (Fin N → k) (∑ i, lam i))) ↥(S i))
    (hDist : ∀ i j,
      Nonempty (↥(S i) ≃ₗ[↥(permutationActionAlgebra k (Fin N → k) (∑ i, lam i))]
        ↥(S j)) → i = j)
    (hSfin : ∀ i, Module.Finite k ↥(S i))
    (e : auxiliarySpace k (Fin N → k) (∑ i, lam i) ≃ₗ[k]
      DirectSum ι (fun i => ↥(S i) ⊗[k]
        (↥(S i) →ₗ[↥(permutationActionAlgebra k (Fin N → k) (∑ i, lam i))]
          auxiliarySpace k (Fin N → k) (∑ i, lam i))))
    (he : ∀ (i : ι) (v : ↥(S i))
        (l : ↥(S i) →ₗ[↥(permutationActionAlgebra k (Fin N → k) (∑ i, lam i))]
          auxiliarySpace k (Fin N → k) (∑ i, lam i)),
      e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v) :
    ∃ iLam : ι,
      (∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace k ↥((S iLam).restrictScalars k)
          ((auxiliarySpacePermutationEquiv k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
            (p := (S iLam).restrictScalars k) (q := (S iLam).restrictScalars k)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule (S iLam) σ hv)) =
          partitionPermutationValue k (∑ i, lam i) (partitionOfTuple N lam) σ) ∧
      (∀ i, i ≠ iLam → ∃ la' : Nat.Partition (∑ i, lam i),
        la' ≠ partitionOfTuple N lam ∧
        ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
          LinearMap.trace k ↥((S i).restrictScalars k)
            ((auxiliarySpacePermutationEquiv k (Fin N → k)
              (∑ i, lam i) σ).toLinearMap.restrict
              (p := (S i).restrictScalars k) (q := (S i).restrictScalars k)
              (fun _ hv => mem_of_mem_symmetricInvariantSubmodule (S i) σ hv)) =
            partitionPermutationValue k (∑ i, lam i) la' σ) := by
  have hlabexists : ∀ i, ∃ la' : Nat.Partition (∑ i, lam i),
      ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace k ↥((S i).restrictScalars k)
          ((auxiliarySpacePermutationEquiv k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
            (p := (S i).restrictScalars k) (q := (S i).restrictScalars k)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule (S i) σ hv)) =
          partitionPermutationValue k (∑ i, lam i) la' σ := by
    intro i
    haveI := hSimp i
    exact exists_trace_eq_of_isSimpleModule (S i)
  choose lab hlab using hlabexists
  have hUniq : ∀ i j, lab i = lab j → i = j := by
    intro i j hij
    haveI := hSimp i
    haveI := hSimp j
    apply hDist i j
    apply nonemptyLinearEquiv_of_shared_trace_eq (S i) (S j) (lab i) (hlab i)
    intro σ
    rw [hij]
    exact hlab j σ
  have hExists : ∃ iLam, lab iLam = partitionOfTuple N lam := by
    by_contra hcon
    push Not at hcon
    have hvanish : ∀ (i : ι) (v : ↥(S i)),
        symmetrizerEndomorphism k N lam v.val = 0 := by
      intro i v
      haveI := hSimp i
      haveI : Module.Finite k ↥((S i).restrictScalars k) := hSfin i
      have hr := restriction_eq_zero_of_partition_ne N lam (S i) (lab i) (hlab i) (hcon i)
      have hv0 := LinearMap.congr_fun hr v
      rw [LinearMap.zero_apply] at hv0
      have := congrArg Subtype.val hv0
      rwa [LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] at this
    exact valueNeZeroOfAntitone N lam hlam
      (youngSymEndomorphism_eq_zero_of_blocks_vanish_general N lam S e he hvanish)
  obtain ⟨iLam, hLamEq⟩ := hExists
  refine ⟨iLam, ?_, ?_⟩
  · intro σ
    have := hlab iLam σ
    rwa [hLamEq] at this
  · intro i hi
    refine ⟨lab i, ?_, hlab i⟩
    intro hcontra
    exact hi (hUniq i iLam (hcontra.trans hLamEq.symm))

end General

end RepresentationTheory.SymmetricGroup.SimpleModuleTrace

end
