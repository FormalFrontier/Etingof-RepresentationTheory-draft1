/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.Algebra.PartitionPermutation
import RepresentationTheory.SimpleModulesAndPartitionBounds
import RepresentationTheory.GeneralLinearGroup.WeightCharacter

noncomputable section

namespace RepresentationTheory.SimpleModuleTraceIdentities

open RepresentationTheory.Algebra.PartitionPermutation
open RepresentationTheory.Auxiliary.MutualCentralizers
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich
open RepresentationTheory.SimpleModulesAndPartitionBounds

/-- The ring structure on endomorphisms commuting with the finite symmetric-group action. -/
noncomputable local instance (priority := high) symmetricEndomorphismRing
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (n : ℕ) :
    Ring (permutationActionAlgebra k V n) := (permutationActionAlgebra k V n).toRing

/-! ### Simple-module trace identities -/

-- The module-ferrying infrastructure in this section needs only `[Field k]`; the
-- algebraic-closure and characteristic-zero hypotheses enter only at the classification /
-- character-injectivity steps (the public theorems below).
section Infrastructure

variable {k : Type} [Field k] {N n : ℕ}

/-- Codomain-restricted version of `permutationGroupAlgebraAction`, landing in
`permutationActionAlgebra`. This is a surjection `k[S_n] →ₐ[k] permutationActionAlgebra`. -/
private noncomputable def symGroupAlgHomToImageK :
    MonoidAlgebra k (Equiv.Perm (Fin n)) →ₐ[k]
      ↥(permutationActionAlgebra k (Fin N → k) n) :=
  AlgHom.codRestrict (permutationGroupAlgebraAction k (Fin N → k) n)
    (permutationActionAlgebra k (Fin N → k) n)
    (fun a => by rw [← range_permutationGroupAlgebraAction]; exact ⟨a, rfl⟩)

@[simp]
private theorem symGroupAlgHomToImageK_val (a : MonoidAlgebra k (Equiv.Perm (Fin n))) :
    ((symGroupAlgHomToImageK (k := k) (N := N) (n := n)) a).val =
      (permutationGroupAlgebraAction k (Fin N → k) n) a := rfl

private theorem symGroupAlgHomToImageK_surjective :
    Function.Surjective (symGroupAlgHomToImageK (k := k) (N := N) (n := n)) := by
  intro b
  have h_in : (b.val : Module.End k _) ∈
      (permutationGroupAlgebraAction k (Fin N → k) n).range := by
    rw [range_permutationGroupAlgebraAction]; exact b.prop
  obtain ⟨a, ha⟩ := h_in
  exact ⟨a, Subtype.ext ha⟩

private theorem symGroupAlgHomToImageK_of (σ : Equiv.Perm (Fin n)) :
    (symGroupAlgHomToImageK (k := k) (N := N) (n := n)) (MonoidAlgebra.of k _ σ) =
      ⟨(auxiliarySpacePermutationEquiv k (Fin N → k) n σ).toLinearMap,
        Algebra.subset_adjoin ⟨σ, rfl⟩⟩ := by
  apply Subtype.ext
  change (permutationGroupAlgebraAction k (Fin N → k) n) (MonoidAlgebra.of k _ σ) = _
  unfold permutationGroupAlgebraAction
  rw [MonoidAlgebra.lift_of]
  rfl

set_option maxHeartbeats 400000 in
-- Elaborating the transported subtype action requires the larger budgets.
set_option synthInstance.maxHeartbeats 200000 in
/-- Value-level description of the `↥(permutationActionAlgebra)`-action on a submodule
`S ≤ V^⊗n` via `symGroupAlgHomToImageK`. -/
private theorem symGroupAlgHomToImageK_smul_val
    (S : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n))
    (a : MonoidAlgebra k (Equiv.Perm (Fin n))) (x : ↥S) :
    ((symGroupAlgHomToImageK (k := k) (N := N) (n := n) a) • x).val =
      (permutationGroupAlgebraAction k (Fin N → k) n a) x.val := by
  rw [Submodule.coe_smul, Subalgebra.smul_def, Module.End.smul_def,
      symGroupAlgHomToImageK_val]

set_option synthInstance.maxHeartbeats 200000 in
-- Synthesizing the induced monoid-algebra module structure requires the larger budget.
/-- The `k[S_n]`-module structure on `↥(S.restrictScalars k)` induced from the
`permutationActionAlgebra`-module structure on `↥S` via `symGroupAlgHomToImageK`. -/
@[reducible] private noncomputable def submoduleAsSymGroupAlgebraModuleK
    (S : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n)) :
    Module (MonoidAlgebra k (Equiv.Perm (Fin n))) ↥(S.restrictScalars k) :=
  Module.compHom _ (symGroupAlgHomToImageK (k := k) (N := N) (n := n)).toRingHom

set_option synthInstance.maxHeartbeats 200000 in
-- Reducing the transported scalar action requires the larger synthesis budget.
/-- The smul of `submoduleAsSymGroupAlgebraModuleK` agrees with applying
`symGroupAlgHomToImageK(a)` to the carrier. -/
private theorem submoduleAsSymGroupAlgebraModuleK_smul_def
    (S : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n))
    (a : MonoidAlgebra k (Equiv.Perm (Fin n))) (v : ↥(S.restrictScalars k)) :
    letI := submoduleAsSymGroupAlgebraModuleK S
    (a • v).val = (permutationGroupAlgebraAction k (Fin N → k) n) a v.val := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Constructing the scalar tower for the transported module requires the larger budget.
/-- Scalar tower: `(c • a) • v = c • (a • v)` for `c : k`,
`a : k[S_n]`, `v : ↥(S.restrictScalars k)`. -/
private theorem submoduleAsSymGroupAlgebra_isScalarTowerK
    (S : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n)) :
    letI := submoduleAsSymGroupAlgebraModuleK S
    IsScalarTower k (MonoidAlgebra k (Equiv.Perm (Fin n))) ↥(S.restrictScalars k) := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  refine ⟨fun c a v => ?_⟩
  apply Subtype.ext
  rw [submoduleAsSymGroupAlgebraModuleK_smul_def, map_smul]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the semilinear carrier identification requires the larger budget.
/-- The identity-on-carrier `↥(S.restrictScalars k) → ↥S`, semilinear over the
surjective ring hom `symGroupAlgHomToImageK`. -/
private noncomputable def submoduleSemilinearIdK
    (S : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n)) :
    letI := submoduleAsSymGroupAlgebraModuleK S
    ↥(S.restrictScalars k) →ₛₗ[
      (symGroupAlgHomToImageK (k := k) (N := N) (n := n)).toRingHom] ↥S :=
  letI := submoduleAsSymGroupAlgebraModuleK S
  { toFun := fun v => ⟨v.val, v.prop⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

set_option synthInstance.maxHeartbeats 200000 in
-- Checking bijectivity through the transported module structure requires the larger budget.
private theorem submoduleSemilinearIdK_bijective
    (S : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n)) :
    letI := submoduleAsSymGroupAlgebraModuleK S
    Function.Bijective (submoduleSemilinearIdK S) := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  refine ⟨?_, ?_⟩
  · intro v w h
    apply Subtype.ext
    exact Subtype.ext_iff.mp h
  · rintro ⟨w, hw⟩; exact ⟨⟨w, hw⟩, rfl⟩

set_option maxHeartbeats 400000 in
-- Transferring simplicity across the surjective scalar map is elaboration-intensive.
set_option synthInstance.maxHeartbeats 200000 in
/-- Simplicity of `↥S` as a `↥(permutationActionAlgebra)`-module transfers to simplicity
of `↥(S.restrictScalars k)` as a `k[S_n]`-module. -/
private theorem submoduleAsSymGroupAlgebra_isSimpleModuleK
    (S : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n))
    [IsSimpleModule (↥(permutationActionAlgebra k (Fin N → k) n)) ↥S] :
    letI := submoduleAsSymGroupAlgebraModuleK S
    IsSimpleModule (MonoidAlgebra k (Equiv.Perm (Fin n))) ↥(S.restrictScalars k) := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  haveI : RingHomSurjective
      (symGroupAlgHomToImageK (k := k) (N := N) (n := n)).toRingHom :=
    ⟨symGroupAlgHomToImageK_surjective⟩
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (submoduleSemilinearIdK S)
    (submoduleSemilinearIdK_bijective S)).mpr ‹_›

/-- The action of `MonoidAlgebra.of k _ σ` on a Specht module is left
multiplication, i.e., `partitionSubtypeLinearEndomorphismOfPerm k n la' σ`. -/
private theorem spechtModuleK_smul_of
    (la' : Nat.Partition n) (σ : Equiv.Perm (Fin n)) (w : ↥(partitionSubmodule k n la')) :
    ((MonoidAlgebra.of k _ σ : MonoidAlgebra k (Equiv.Perm (Fin n))) • w :
        ↥(partitionSubmodule k n la')) =
      partitionSubtypeLinearEndomorphismOfPerm k n la' σ w := by
  apply Subtype.ext
  rfl

set_option maxHeartbeats 400000 in
-- Elaborating the restricted-action conjugation requires the larger budgets.
set_option synthInstance.maxHeartbeats 200000 in
/-- The conjugation step of the Specht identification over `k`. Given a `k[S_n]`-iso
`e : ↥(S.restrictScalars k) ≃ₗ partitionSubmodule k n la'`, the trace of the restricted
`σ`-action on `↥(S.restrictScalars k)` equals `partitionPermutationValue k n la' σ`. -/
private theorem trace_restrictedSymGroupAction_eq_of_spechtIsoK
    (S : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n))
    (la' : Nat.Partition n)
    (e : letI := submoduleAsSymGroupAlgebraModuleK S
         ↥(S.restrictScalars k) ≃ₗ[MonoidAlgebra k (Equiv.Perm (Fin n))]
           ↥(partitionSubmodule k n la'))
    (σ : Equiv.Perm (Fin n)) :
    LinearMap.trace k ↥(S.restrictScalars k)
        ((auxiliarySpacePermutationEquiv k (Fin N → k) n σ).toLinearMap.restrict
          (p := S.restrictScalars k) (q := S.restrictScalars k)
          (fun _ hv =>
            mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
      partitionPermutationValue k n la' σ := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  haveI := submoduleAsSymGroupAlgebra_isScalarTowerK S
  -- Convert `e` to a `k`-linear equiv.
  let ek : ↥(S.restrictScalars k) ≃ₗ[k] ↥(partitionSubmodule k n la') :=
    LinearEquiv.restrictScalars k e
  set restrictedAction :
      ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k) :=
    (auxiliarySpacePermutationEquiv k (Fin N → k) n σ).toLinearMap.restrict
      (p := S.restrictScalars k) (q := S.restrictScalars k)
      (fun _ hv =>
        mem_of_mem_symmetricInvariantSubmodule S σ hv)
  -- `ek` intertwines `restrictedAction` with `partitionSubtypeLinearEndomorphismOfPerm k n la' σ`.
  have h_intertwine : ∀ v : ↥(S.restrictScalars k),
      ek (restrictedAction v) = partitionSubtypeLinearEndomorphismOfPerm k n la' σ (ek v) := by
    intro v
    have h := e.map_smul (MonoidAlgebra.of k _ σ : MonoidAlgebra k (Equiv.Perm (Fin n))) v
    have h_lhs : (MonoidAlgebra.of k _ σ : MonoidAlgebra k (Equiv.Perm (Fin n))) • v =
        restrictedAction v := by
      apply Subtype.ext
      change (permutationGroupAlgebraAction k (Fin N → k) n) (MonoidAlgebra.of k _ σ) v.val =
        (auxiliarySpacePermutationEquiv k (Fin N → k) n σ).toLinearMap v.val
      unfold permutationGroupAlgebraAction
      rw [MonoidAlgebra.lift_of]
      rfl
    have h_rhs : (MonoidAlgebra.of k _ σ : MonoidAlgebra k (Equiv.Perm (Fin n))) • e v =
        partitionSubtypeLinearEndomorphismOfPerm k n la' σ (e v) :=
      spechtModuleK_smul_of la' σ (e v)
    rw [h_lhs, h_rhs] at h
    exact h
  have h_eq : restrictedAction = ek.symm.toLinearMap ∘ₗ
      (partitionSubtypeLinearEndomorphismOfPerm k n la' σ) ∘ₗ ek.toLinearMap := by
    apply LinearMap.ext
    intro v
    change restrictedAction v = ek.symm (partitionSubtypeLinearEndomorphismOfPerm k n la' σ (ek v))
    rw [← h_intertwine v, ek.symm_apply_apply]
  rw [h_eq]
  -- Trace conjugation: tr(ek.symm ∘ T ∘ ek) = tr(T) for `k`-linear T.
  have h_conj : ek.symm.toLinearMap ∘ₗ
      (partitionSubtypeLinearEndomorphismOfPerm k n la' σ) ∘ₗ ek.toLinearMap =
        ek.symm.conj (partitionSubtypeLinearEndomorphismOfPerm k n la' σ) := by
    rfl
  rw [h_conj]
  have ht := @LinearMap.trace_conj' k inferInstance
    (↥(partitionSubmodule k n la')) (partitionSubmodule k n la').addCommGroup
    (partitionSubmodule k n la').module'
    (↥(S.restrictScalars k)) (S.restrictScalars k).addCommGroup
    (S.restrictScalars k).module
    (partitionSubtypeLinearEndomorphismOfPerm k n la' σ) ek.symm
  rw [ht]
  rfl

end Infrastructure

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {N n : ℕ}

set_option maxHeartbeats 400000 in
-- Classifying the transported simple module requires the larger elaboration budgets.
set_option synthInstance.maxHeartbeats 200000 in
/-- For a simple submodule, there is a witness whose associated value equals the restricted trace
for every permutation. -/
theorem exists_trace_eq_of_isSimpleModule
    (S : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n))
    [IsSimpleModule (↥(permutationActionAlgebra k (Fin N → k) n)) ↥S] :
    ∃ la' : Nat.Partition n, ∀ σ : Equiv.Perm (Fin n),
      LinearMap.trace k ↥(S.restrictScalars k)
          ((auxiliarySpacePermutationEquiv k (Fin N → k) n σ).toLinearMap.restrict
            (p := S.restrictScalars k) (q := S.restrictScalars k)
            (fun _ hv =>
              mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
        partitionPermutationValue k n la' σ := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  haveI := submoduleAsSymGroupAlgebra_isScalarTowerK S
  haveI := submoduleAsSymGroupAlgebra_isSimpleModuleK S
  obtain ⟨la', ⟨e⟩⟩ :=
    exists_linear_equiv_membership_subtype_over_auxiliary_scalars k n ↥(S.restrictScalars k)
  exact ⟨la', fun σ => trace_restrictedSymGroupAction_eq_of_spechtIsoK S la' e σ⟩

set_option maxHeartbeats 1600000 in
-- Constructing the equivalence over the action subalgebra is elaboration-intensive.
set_option synthInstance.maxHeartbeats 400000 in
/-- Transfer a `k[S_n]`-linear equivalence between the restricted-scalar modules
`↥(S.restrictScalars k)` and `↥(S'.restrictScalars k)` to a `permutationActionAlgebra`-linear
equivalence `↥S ≃ₗ ↥S'`. -/
private noncomputable def transferToSymGroupImageEquivK
    (S S' : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n))
    (g : letI := submoduleAsSymGroupAlgebraModuleK S
         letI := submoduleAsSymGroupAlgebraModuleK S'
         ↥(S.restrictScalars k) ≃ₗ[MonoidAlgebra k (Equiv.Perm (Fin n))]
           ↥(S'.restrictScalars k)) :
    ↥S ≃ₗ[↥(permutationActionAlgebra k (Fin N → k) n)] ↥S' :=
  letI := submoduleAsSymGroupAlgebraModuleK S
  letI := submoduleAsSymGroupAlgebraModuleK S'
  { toFun := fun x => ⟨(g ⟨x.val, x.property⟩).val, (g ⟨x.val, x.property⟩).property⟩
    invFun := fun y =>
      ⟨(g.symm ⟨y.val, y.property⟩).val, (g.symm ⟨y.val, y.property⟩).property⟩
    left_inv := fun x => by
      apply Subtype.ext
      exact congrArg Subtype.val (g.symm_apply_apply ⟨x.val, x.property⟩)
    right_inv := fun y => by
      apply Subtype.ext
      exact congrArg Subtype.val (g.apply_symm_apply ⟨y.val, y.property⟩)
    map_add' := fun x y => by
      apply Subtype.ext
      exact congrArg Subtype.val (g.map_add ⟨x.val, x.property⟩ ⟨y.val, y.property⟩)
    map_smul' := fun b x => by
      obtain ⟨a, rfl⟩ := symGroupAlgHomToImageK_surjective b
      apply Subtype.ext
      have hxeq : (⟨((symGroupAlgHomToImageK (k := k) (N := N) (n := n) a) • x).val,
            ((symGroupAlgHomToImageK (k := k) (N := N) (n := n) a) • x).property⟩ :
            ↥(S.restrictScalars k))
            = a • (⟨x.val, x.property⟩ : ↥(S.restrictScalars k)) := by
        apply Subtype.ext
        rw [submoduleAsSymGroupAlgebraModuleK_smul_def, symGroupAlgHomToImageK_smul_val]
      change (g ⟨((symGroupAlgHomToImageK (k := k) (N := N) (n := n) a) • x).val,
            ((symGroupAlgHomToImageK (k := k) (N := N) (n := n) a) • x).property⟩).val = _
      rw [hxeq, map_smul, submoduleAsSymGroupAlgebraModuleK_smul_def,
          RingHom.id_apply, symGroupAlgHomToImageK_smul_val] }

set_option maxHeartbeats 800000 in
-- Comparing the two transported classifications requires the larger elaboration budgets.
set_option synthInstance.maxHeartbeats 400000 in
/-- Two simple submodules whose restricted traces equal the same prescribed values are linearly
equivalent. -/
theorem nonemptyLinearEquiv_of_common_trace_eq
    (S S' : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n))
    [IsSimpleModule (↥(permutationActionAlgebra k (Fin N → k) n)) ↥S]
    [IsSimpleModule (↥(permutationActionAlgebra k (Fin N → k) n)) ↥S']
    (la : Nat.Partition n)
    (hS : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace k ↥(S.restrictScalars k)
          ((auxiliarySpacePermutationEquiv k (Fin N → k) n σ).toLinearMap.restrict
            (p := S.restrictScalars k) (q := S.restrictScalars k)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
          partitionPermutationValue k n la σ)
    (hS' : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace k ↥(S'.restrictScalars k)
          ((auxiliarySpacePermutationEquiv k (Fin N → k) n σ).toLinearMap.restrict
            (p := S'.restrictScalars k) (q := S'.restrictScalars k)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S' σ hv)) =
          partitionPermutationValue k n la σ) :
    Nonempty (↥S ≃ₗ[↥(permutationActionAlgebra k (Fin N → k) n)] ↥S') := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  letI := submoduleAsSymGroupAlgebraModuleK S'
  haveI := submoduleAsSymGroupAlgebra_isScalarTowerK S
  haveI := submoduleAsSymGroupAlgebra_isScalarTowerK S'
  haveI := submoduleAsSymGroupAlgebra_isSimpleModuleK S
  haveI := submoduleAsSymGroupAlgebra_isSimpleModuleK S'
  -- Classify each restrictScalars module as a Specht module.
  obtain ⟨μ, ⟨eS⟩⟩ :=
    exists_linear_equiv_membership_subtype_over_auxiliary_scalars k n ↥(S.restrictScalars k)
  obtain ⟨μ', ⟨eS'⟩⟩ :=
    exists_linear_equiv_membership_subtype_over_auxiliary_scalars k n ↥(S'.restrictScalars k)
  -- Both labels equal `la` by Specht character injectivity.
  have hμ : μ = la := partitionPermutationValue_injective k n fun σ =>
    (trace_restrictedSymGroupAction_eq_of_spechtIsoK S μ eS σ).symm.trans (hS σ)
  have hμ' : μ' = la := partitionPermutationValue_injective k n fun σ =>
    (trace_restrictedSymGroupAction_eq_of_spechtIsoK S' μ' eS' σ).symm.trans (hS' σ)
  have hμμ' : μ = μ' := hμ.trans hμ'.symm
  subst hμμ'
  exact ⟨transferToSymGroupImageEquivK S S' (eS.trans eS'.symm)⟩

set_option maxHeartbeats 400000 in
-- Elaborating the public wrapper requires the larger synthesis budgets.
set_option synthInstance.maxHeartbeats 400000 in
/-- A shared family of restricted trace equalities for two simple submodules yields a linear
equivalence between them. -/
theorem nonemptyLinearEquiv_of_shared_trace_eq
    (S S' : Submodule (permutationActionAlgebra k (Fin N → k) n)
      (auxiliarySpace k (Fin N → k) n))
    [IsSimpleModule (↥(permutationActionAlgebra k (Fin N → k) n)) ↥S]
    [IsSimpleModule (↥(permutationActionAlgebra k (Fin N → k) n)) ↥S']
    (la : Nat.Partition n)
    (hS : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace k ↥(S.restrictScalars k)
          ((auxiliarySpacePermutationEquiv k (Fin N → k) n σ).toLinearMap.restrict
            (p := S.restrictScalars k) (q := S.restrictScalars k)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
          partitionPermutationValue k n la σ)
    (hS' : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace k ↥(S'.restrictScalars k)
          ((auxiliarySpacePermutationEquiv k (Fin N → k) n σ).toLinearMap.restrict
            (p := S'.restrictScalars k) (q := S'.restrictScalars k)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S' σ hv)) =
          partitionPermutationValue k n la σ) :
    Nonempty (↥S ≃ₗ[↥(permutationActionAlgebra k (Fin N → k) n)] ↥S') :=
  nonemptyLinearEquiv_of_common_trace_eq S S' la hS hS'

end RepresentationTheory.SimpleModuleTraceIdentities

end
