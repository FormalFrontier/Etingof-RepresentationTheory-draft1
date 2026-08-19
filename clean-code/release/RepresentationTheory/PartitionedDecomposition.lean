/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.TensorDecomposition
import RepresentationTheory.SimpleModulesAndPartitionBounds
import RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences
import RepresentationTheory.Alignment.Attribute

open scoped TensorProduct DirectSum
open RepresentationTheory.Auxiliary.MutualCentralizers RepresentationTheory.CentralizerDecomposition RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich

namespace RepresentationTheory.PartitionedDecomposition

universe u v



section DirectSumHelpers


/-- Builds a linear equivalence of direct sums from fiberwise linear equivalences. -/
noncomputable def DirectSum.linearEquivOfFamily {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    {A B : ι → Type*} [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [∀ i, AddCommMonoid (B i)] [∀ i, Module R (B i)]
    (f : ∀ i, A i ≃ₗ[R] B i) : (⨁ i, A i) ≃ₗ[R] ⨁ i, B i :=
  LinearEquiv.ofLinear
    (DirectSum.toModule R ι _ (fun i => (DirectSum.lof R ι B i).comp (f i).toLinearMap))
    (DirectSum.toModule R ι _ (fun i => (DirectSum.lof R ι A i).comp (f i).symm.toLinearMap))
    (by
      refine DirectSum.linearMap_ext R fun i => ?_
      ext x
      simp [DirectSum.toModule_lof])
    (by
      refine DirectSum.linearMap_ext R fun i => ?_
      ext x
      simp [DirectSum.toModule_lof])



/-- Auxiliary definition whose formal type is unavailable. -/
noncomputable def auxiliary {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    {α : ι → Type*} [∀ i, DecidableEq (α i)]
    (δ : ∀ i, α i → Type*) [∀ i j, AddCommMonoid (δ i j)] [∀ i j, Module R (δ i j)] :
    (⨁ s : (Σ i, α i), δ s.1 s.2) ≃ₗ[R] ⨁ i, ⨁ j, δ i j :=
  { DirectSum.sigmaLcurry R (δ := δ) with
    invFun := DirectSum.sigmaLuncurry R (δ := δ)
    left_inv := (DFinsupp.sigmaCurryEquiv (δ := δ)).left_inv
    right_inv := (DFinsupp.sigmaCurryEquiv (δ := δ)).right_inv }


/-- Identifies a direct sum over a unique index type with its distinguished fiber. -/
noncomputable def DirectSum.linearEquivOfUnique {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    [Unique ι] (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    (⨁ i, M i) ≃ₗ[R] M default :=
  { toFun := fun f => f default
    map_add' := fun f g => DFinsupp.add_apply f g default
    map_smul' := fun r f => DFinsupp.smul_apply r f default
    invFun := fun x => DirectSum.lof R ι M default x
    left_inv := fun f => by
      refine DFinsupp.ext fun i => ?_
      rw [Subsingleton.elim i default]
      simp
    right_inv := fun x => by simp }



/-- Identifies the tensor product of two direct sums over a subsingleton index with a direct sum of tensor products. -/
noncomputable def DirectSum.tensorProductLinearEquivOfSubsingleton {k : Type*} [CommRing k]
    {F : Type*} [Fintype F] [DecidableEq F] [Subsingleton F]
    (A B : F → Type*) [∀ f, AddCommGroup (A f)] [∀ f, Module k (A f)]
    [∀ f, AddCommGroup (B f)] [∀ f, Module k (B f)] :
    ((⨁ f, A f) ⊗[k] (⨁ f, B f)) ≃ₗ[k] ⨁ f, (A f ⊗[k] B f) :=
  let g : F × F ≃ F :=
    { toFun := Prod.fst
      invFun := fun f => (f, f)
      left_inv := fun _ => Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }
  (TensorProduct.directSum k k A B) ≪≫ₗ DirectSum.lequivCongrLeft k g

end DirectSumHelpers

variable (k : Type u) [Field k]
  (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)






/-- Reindexes an indexed direct sum into partition fibers along an embedding. -/
noncomputable def DirectSum.linearEquivReindexByEmbedding
    {E : Type*} [AddCommGroup E] [Module k E]
    {A : Subalgebra k (Module.End k E)} {iota : Type*} [DecidableEq iota]
    (S : iota → Submodule A E) (label : iota ↪ Nat.Partition n) :
    DirectSum iota (fun i => ↥(S i) ⊗[k] (↥(S i) →ₗ[A] E)) ≃ₗ[k]
      DirectSum (Nat.Partition n) (fun p =>
        DirectSum {i : iota // label i = p}
          (fun j => ↥(S j.1) ⊗[k] (↥(S j.1) →ₗ[A] E))) :=
  DirectSum.lequivCongrLeft k
      (Equiv.sigmaFiberEquiv (label : iota → Nat.Partition n)).symm
    ≪≫ₗ auxiliary (R := k)
      (fun p (j : {i : iota // label i = p}) =>
        ↥(S j.1) ⊗[k] (↥(S j.1) →ₗ[A] E))

set_option synthInstance.maxHeartbeats 200000 in


/-- The linear action on the decomposition induced by an element of the subalgebra. -/
noncomputable def decompositionSubalgebraAction
    {E : Type*} [AddCommGroup E] [Module k E]
    {A : Subalgebra k (Module.End k E)} {iota : Type*} [DecidableEq iota]
    (S : iota → Submodule A E) (label : iota ↪ Nat.Partition n) (a : A) :
    DirectSum (Nat.Partition n) (fun p =>
        DirectSum {i : iota // label i = p}
          (fun j => ↥(S j.1) ⊗[k] (↥(S j.1) →ₗ[A] E))) →ₗ[k]
      DirectSum (Nat.Partition n) (fun p =>
        DirectSum {i : iota // label i = p}
          (fun j => ↥(S j.1) ⊗[k] (↥(S j.1) →ₗ[A] E))) :=
  (DirectSum.linearEquivReindexByEmbedding k n S label).toLinearMap.comp
    ((RepresentationTheory.CentralizerDecomposition.algebraActionOnTensorDirectSum (k := k) (E := E) S a).comp
      (DirectSum.linearEquivReindexByEmbedding k n S label).symm.toLinearMap)

set_option synthInstance.maxHeartbeats 200000 in



/-- The linear action on the decomposition induced by an element of the centralizer. -/
noncomputable def decompositionCentralizerAction
    {E : Type*} [AddCommGroup E] [Module k E]
    {A : Subalgebra k (Module.End k E)} {iota : Type*} [DecidableEq iota]
    (S : iota → Submodule A E) (label : iota ↪ Nat.Partition n)
    (b : ↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) :
    DirectSum (Nat.Partition n) (fun p =>
        DirectSum {i : iota // label i = p}
          (fun j => ↥(S j.1) ⊗[k] (↥(S j.1) →ₗ[A] E))) →ₗ[k]
      DirectSum (Nat.Partition n) (fun p =>
        DirectSum {i : iota // label i = p}
          (fun j => ↥(S j.1) ⊗[k] (↥(S j.1) →ₗ[A] E))) :=
  (DirectSum.linearEquivReindexByEmbedding k n S label).toLinearMap.comp
    ((RepresentationTheory.CentralizerDecomposition.centralizerActionOnTensorDirectSum (k := k) (E := E) S b).comp
      (DirectSum.linearEquivReindexByEmbedding k n S label).symm.toLinearMap)



/-- Data indexed by submodules and embedded partitions. -/
structure DecompositionData
    {E : Type*} [AddCommGroup E] [Module k E]
    {A : Subalgebra k (Module.End k E)} {iota : Type*} [DecidableEq iota]
    (S : iota → Submodule A E) (label : iota ↪ Nat.Partition n) where
  /-- The linear equivalence from the ambient module to the indexed direct sum. -/
  linearEquiv : E ≃ₗ[k]
    DirectSum (Nat.Partition n) (fun p =>
      DirectSum {i : iota // label i = p}
        (fun j => ↥(S j.1) ⊗[k] (↥(S j.1) →ₗ[A] E)))
  /-- The decomposition equivalence commutes with the action of an algebra element. -/
  linearEquiv_apply_subalgebra : ∀ (a : A) (x : E),
    linearEquiv (a.val x) =
      decompositionSubalgebraAction k n S label a (linearEquiv x)
  /-- The decomposition equivalence commutes with the action of a centralizer element. -/
  linearEquiv_apply_centralizer :
    ∀ (b : ↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) (x : E),
      linearEquiv (b.val x) =
        decompositionCentralizerAction k n S label b (linearEquiv x)



/-- Constructs decomposition data from an auxiliary input. -/
noncomputable def _root_.RepresentationTheory.CentralizerDecomposition.AuxiliaryDecompositionData.toDecompositionData
    {E : Type*} [AddCommGroup E] [Module k E]
    {A : Subalgebra k (Module.End k E)} {iota : Type*} [DecidableEq iota]
    (S : iota → Submodule A E) (label : iota ↪ Nat.Partition n)
    (e : RepresentationTheory.CentralizerDecomposition.AuxiliaryDecompositionData (k := k) (E := E) (A := A) S) :
    DecompositionData k n S label := by
  let r := DirectSum.linearEquivReindexByEmbedding k n S label
  refine ⟨e.equiv ≪≫ₗ r, ?_, ?_⟩
  · intro a x
    simp only [LinearEquiv.trans_apply, decompositionSubalgebraAction,
      LinearMap.comp_apply]
    change r (e.equiv (a.val x)) =
      r (RepresentationTheory.CentralizerDecomposition.algebraActionOnTensorDirectSum (k := k) (E := E) S a
        (r.symm (r (e.equiv x))))
    rw [r.symm_apply_apply, e.equiv_apply_algebra]
  · intro b x
    simp only [LinearEquiv.trans_apply, decompositionCentralizerAction,
      LinearMap.comp_apply]
    change r (e.equiv (b.val x)) =
      r (RepresentationTheory.CentralizerDecomposition.centralizerActionOnTensorDirectSum (k := k) (E := E) S b
        (r.symm (r (e.equiv x))))
    rw [r.symm_apply_apply, e.equiv_apply_centralizer]




private def conjClassToPartition :
    ConjClasses (Equiv.Perm (Fin n)) → Nat.Partition n :=
  Quotient.lift
    (fun σ => (Fintype.card_fin n) ▸ σ.partition)
    (fun _ _ h => congrArg (Fintype.card_fin n ▸ ·) (Equiv.Perm.partition_eq_of_isConj.mp h))

private lemma conjClassToPartition_injective :
    Function.Injective (conjClassToPartition n) := by
  intro a b h
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b, rfl⟩ := b.mk_surjective
  change (Fintype.card_fin n ▸ a.partition) = (Fintype.card_fin n ▸ b.partition) at h
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  apply Equiv.Perm.partition_eq_of_isConj.mpr
  have : ∀ (m : ℕ) (hm : m = n) (p q : m.Partition),
      (hm ▸ p : Nat.Partition n) = (hm ▸ q : Nat.Partition n) → p = q := by
    intro m hm; subst hm; intro p q hpq; exact hpq
  exact this _ (Fintype.card_fin n) _ _ h


private lemma card_conjClasses_le_card_partition :
    Fintype.card (ConjClasses (Equiv.Perm (Fin n))) ≤ Fintype.card (Nat.Partition n) :=
  Fintype.card_le_of_injective _ (conjClassToPartition_injective n)





/-- The algebra homomorphism from the permutation monoid algebra into the displayed subalgebra. -/
noncomputable def symmetricGroupAlgebraAction :
    MonoidAlgebra k (Equiv.Perm (Fin n)) →ₐ[k] ↥(RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) :=
  AlgHom.codRestrict (RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction k V n) (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n)
    (fun a => by rw [← RepresentationTheory.Auxiliary.MutualCentralizers.range_permutationGroupAlgebraAction]; exact ⟨a, rfl⟩)

/-- Coercing the action homomorphism to the ambient endomorphism algebra gives the displayed map. -/
theorem symmetricGroupAlgebraAction_coe (a : MonoidAlgebra k (Equiv.Perm (Fin n))) :
    (symmetricGroupAlgebraAction k V n a : Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)) =
      RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction k V n a := rfl

/-- The permutation-algebra action homomorphism is surjective. -/
theorem symmetricGroupAlgebraAction_surjective :
    Function.Surjective (symmetricGroupAlgebraAction k V n) := by
  intro b
  obtain ⟨a, ha⟩ : (b : Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)) ∈ (RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction k V n).range := by
    rw [RepresentationTheory.Auxiliary.MutualCentralizers.range_permutationGroupAlgebraAction]; exact b.prop
  exact ⟨a, Subtype.ext ha⟩





/-- The cardinality of permutations of a finite type is invertible in a characteristic-zero field. -/
noncomputable instance invertibleCardPerm [CharZero k] :
    Invertible (Fintype.card (Equiv.Perm (Fin n)) : k) := by
  apply invertibleOfNonzero
  rw [Fintype.card_perm, Fintype.card_fin]
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)






/-- A pairwise inequivalent finite family of simple modules has cardinality bounded by the partitions. -/
theorem card_le_card_partitions [IsAlgClosed k] [CharZero k]
    {ι : Type} [Fintype ι]
    (S : ι → Type*) [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    [∀ i, Module (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (S i)]
    [∀ i, IsScalarTower k (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (S i)]
    [∀ i, IsSimpleModule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (S i)]
    (hdist : ∀ i j, Nonempty (S i ≃ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] S j) → i = j) :
    Fintype.card ι ≤ Fintype.card (Nat.Partition n) := by
  set q := symmetricGroupAlgebraAction k V n with hq
  have hq_surj := symmetricGroupAlgebraAction_surjective k V n

  letI modS : ∀ i, Module (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i =>
    Module.compHom (S i) q.toRingHom
  have hsmul : ∀ (i) (r : MonoidAlgebra k (Equiv.Perm (Fin n))) (x : S i),
      r • x = q r • x := fun i r x => rfl
  haveI towS : ∀ i, IsScalarTower k (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i => by
    refine ⟨fun c r x => ?_⟩
    rw [hsmul, hsmul, map_smul, smul_assoc]
  haveI : RingHomSurjective q.toRingHom := ⟨hq_surj⟩
  haveI simpS : ∀ i, IsSimpleModule (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i =>
    RepresentationTheory.Centralizer.LinearMaps.IsSimpleModule.restrictScalars_of_surjective
      (R := MonoidAlgebra k (Equiv.Perm (Fin n)))
      (S := RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (X := S i) q.toRingHom (hsmul i)
  have hdist' : ∀ i j,
      Nonempty (S i ≃ₗ[MonoidAlgebra k (Equiv.Perm (Fin n))] S j) → i = j := by
    intro i j ⟨f⟩
    refine hdist i j ⟨?_⟩
    refine { f.toAddEquiv with map_smul' := fun a x => ?_ }
    obtain ⟨r, rfl⟩ := hq_surj a
    change f (q r • x) = q r • f x
    rw [← hsmul, ← hsmul, f.map_smul]
  calc Fintype.card ι
      ≤ Fintype.card (ConjClasses (Equiv.Perm (Fin n))) :=
        RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences.card_le_card_conjClasses_of_simpleModule_family (k := k) (G := Equiv.Perm (Fin n)) S hdist'
    _ ≤ Fintype.card (Nat.Partition n) := card_conjClasses_le_card_partition n

set_option maxHeartbeats 1600000 in

set_option synthInstance.maxHeartbeats 800000 in








/-- A pairwise inequivalent family of simple modules admits compatible equivariant maps. -/
theorem existsEquivariantFamily [IsAlgClosed k] [CharZero k]
    {ι : Type}
    (S : ι → Type*) [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    [∀ i, Module (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (S i)]
    [∀ i, IsScalarTower k (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (S i)]
    [∀ i, IsSimpleModule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (S i)]
    (hdist : ∀ i j, Nonempty (S i ≃ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] S j) → i = j) :
    ∃ (label : ι ↪ Nat.Partition n)
      (specht : ∀ i, S i ≃ₗ[k] ↥(RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n (label i))),
      ∀ (i : ι) (a : MonoidAlgebra k (Equiv.Perm (Fin n))) (x : S i),
        specht i ((symmetricGroupAlgebraAction k V n a) • x) = a • specht i x := by
  classical
  let q := symmetricGroupAlgebraAction k V n
  have hq_surj : Function.Surjective q := symmetricGroupAlgebraAction_surjective k V n
  letI restrictedModule : ∀ i,
      Module (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i =>
    Module.compHom (S i) q.toRingHom
  have hsmul : ∀ (i) (a : MonoidAlgebra k (Equiv.Perm (Fin n))) (x : S i),
      a • x = q a • x := fun _ _ _ => rfl
  haveI restrictedTower : ∀ i,
      IsScalarTower k (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i => by
    refine ⟨fun c a x => ?_⟩
    rw [hsmul, hsmul, map_smul, smul_assoc]
  haveI : RingHomSurjective q.toRingHom := ⟨hq_surj⟩
  haveI restrictedSimple : ∀ i,
      IsSimpleModule (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i =>
    RepresentationTheory.Centralizer.LinearMaps.IsSimpleModule.restrictScalars_of_surjective
      (R := MonoidAlgebra k (Equiv.Perm (Fin n)))
      (S := RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (X := S i) q.toRingHom (hsmul i)
  choose label hlabel using fun i => RepresentationTheory.SimpleModulesAndPartitionBounds.exists_linear_equiv_membership_subtype_over_permutation_monoid_algebra k n (S i)
  let spechtIso : ∀ i, S i ≃ₗ[MonoidAlgebra k (Equiv.Perm (Fin n))]
      ↥(RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n (label i)) := fun i => Classical.choice (hlabel i)
  have hlabel_injective : Function.Injective label := by
    intro i j hij
    have hmid : Nonempty
        (↥(RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n (label i)) ≃ₗ[MonoidAlgebra k (Equiv.Perm (Fin n))]
          ↥(RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n (label j))) := by
      rw [hij]
      exact ⟨LinearEquiv.refl _ _⟩
    obtain ⟨mid⟩ := hmid
    let f := (spechtIso i).trans (mid.trans (spechtIso j).symm)
    apply hdist i j
    refine ⟨{ f.toAddEquiv with map_smul' := fun a x => ?_ }⟩
    obtain ⟨r, rfl⟩ := hq_surj a
    change f (q r • x) = q r • f x
    rw [← hsmul i, ← hsmul j, f.map_smul]
  let labelEmbedding : ι ↪ Nat.Partition n := ⟨label, hlabel_injective⟩
  let specht : ∀ i, S i ≃ₗ[k] ↥(RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n (labelEmbedding i)) :=
    fun i => LinearEquiv.restrictScalars k (spechtIso i)
  refine ⟨labelEmbedding, specht, ?_⟩
  intro i a x
  dsimp only [specht, labelEmbedding]
  rw [← hsmul i]
  exact (spechtIso i).map_smul a x



set_option maxHeartbeats 5000000 in

set_option synthInstance.maxHeartbeats 1800000 in













/-- There exist indexed simple submodules, labels, and compatible equivariant maps. -/
theorem existsIndexedSimpleDecomposition
    [IsAlgClosed k] [CharZero k] :
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
        specht i ((symmetricGroupAlgebraAction k V n a) • x) = a • specht i x) ∧
      ∃ e : DecompositionData k n S label,
        ∀ (b : ↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n)) (x : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n),
          e.linearEquiv (b.val x) =
            decompositionCentralizerAction k n S label
              (⟨b.val, RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra
                k V n b.property⟩ :
                ↥(Subalgebra.centralizer k
                  (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n :
                    Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))
              (e.linearEquiv x) := by
  classical
  haveI := RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra_semisimple k V n
  haveI := RepresentationTheory.Auxiliary.MutualCentralizers.faithfulSMul_permutationActionAlgebra_auxiliarySpace k V n
  obtain ⟨iota, hiota, hiotaDec, S, hSSimple, hSDistinct, hSFinite,
      hLSimple, e, he⟩ :=
    RepresentationTheory.Auxiliary.MutualCentralizers.exists_auxiliarySpace_decomposition_evaluation k V n
  letI := hiota
  letI := hiotaDec
  let coherentSAddCommGroup : ∀ i, AddCommGroup (S i) := fun i =>
    { Module.addCommMonoidToAddCommGroup k with
      toAddCommMonoid := (S i).addCommMonoid }
  letI := coherentSAddCommGroup
  haveI : ∀ i, IsSimpleModule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (S i) := hSSimple
  haveI : ∀ i, Module.Finite k ↥(S i) := hSFinite
  obtain ⟨label, specht, hspecht⟩ :=
    existsEquivariantFamily k V n (fun i => ↥(S i)) hSDistinct
  have hfib : ∀ p, Subsingleton {i : iota // label i = p} := fun p =>
    ⟨fun a b => Subtype.ext (label.injective (a.2.trans b.2.symm))⟩
  have hLDistinct : ∀ i j, Nonempty
      ((↥(S i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) ≃ₗ[
        ↥(Subalgebra.centralizer k
          (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))))]
        (↥(S j) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)) → i = j := by
    intro i j hiso
    exact RepresentationTheory.Centralizer.LinearMaps.Subalgebra.centralizer.linearMapEquiv_index_eq k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) S hSDistinct i j hiso
  let equivariant := RepresentationTheory.CentralizerDecomposition.AuxiliaryDecompositionData.ofEquiv
    (k := k) (E := RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) (A := RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) S e he
  let partitionEquivariant :=
    equivariant.toDecompositionData (k := k) (n := n) S label
  refine ⟨iota, hiota, hiotaDec, S, ?_⟩
  letI : ∀ i, AddCommGroup (S i) := coherentSAddCommGroup
  refine ⟨label, specht, hfib, hLSimple, hLDistinct, hspecht,
    partitionEquivariant, ?_⟩
  intro b x
  exact partitionEquivariant.linearEquiv_apply_centralizer
    (⟨b.val, RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra
      k V n b.property⟩ :
      ↥(Subalgebra.centralizer k
        (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))))) x






/-- There is a tensor-product direct-sum decomposition with simple or subsingleton summands. -/
@[source_ref "Chapter5/Theorem5.18.4" (role := primary)]
theorem existsTensorProductDecomposition
    [IsAlgClosed k] [CharZero k] :
    ∃ (S : Nat.Partition n → Type (max u v))
      (_ : ∀ p, AddCommGroup (S p))
      (_ : ∀ p, Module k (S p))
      (_ : ∀ p, Module (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (S p))
      (L : Nat.Partition n → Type (max u v))
      (_ : ∀ p, AddCommGroup (L p))
      (_ : ∀ p, Module k (L p))
      (_ : ∀ p, Module (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) (L p)),
      (∀ p, IsSimpleModule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (S p) ∨ Subsingleton (S p)) ∧
      (∀ p, IsSimpleModule (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) (L p) ∨ Subsingleton (L p)) ∧
      (∀ p q, ¬ Subsingleton (L p) →
        Nonempty (L p ≃ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n] L q) → p = q) ∧
      Nonempty (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n ≃ₗ[k]
        DirectSum (Nat.Partition n)
          (fun p => S p ⊗[k] L p)) := by
  classical
  obtain ⟨ι, fι, dι, S, acgS, modkS, modAS, towS, simpS, distS, finS,
      L, acgL, modkL, modBL, simpL, hLdist, ⟨iso⟩⟩ :=
    RepresentationTheory.Auxiliary.TensorDecomposition.existsAuxiliaryDirectSumTensorProductDecomposition k V n
  haveI := fι; haveI := dι
  letI := acgS
  letI := modkS
  letI := modAS
  haveI := towS
  haveI := simpS
  haveI := finS
  letI := acgL
  letI := modkL
  letI := modBL
  haveI := simpL




  obtain ⟨e, _specht, _spechtAction⟩ := existsEquivariantFamily k V n S distS

  set Fib : Nat.Partition n → Type := fun p => { i : ι // e i = p } with hFib
  haveI fibSub : ∀ p, Subsingleton (Fib p) := fun p =>
    ⟨fun a b => Subtype.ext (e.injective (a.2.trans b.2.symm))⟩

  refine ⟨fun p => ⨁ j : Fib p, S j.1, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun p => ⨁ j : Fib p, L j.1,
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance, ?_, ?_, ?_, ?_⟩
  ·
    intro p
    by_cases hp : Nonempty (Fib p)
    · haveI : Nonempty (Fib p) := hp
      haveI : Unique (Fib p) := uniqueOfSubsingleton (Classical.choice hp)
      exact Or.inl (IsSimpleModule.congr
        (DirectSum.linearEquivOfUnique (R := RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (fun j : Fib p => S j.1)))
    · rw [not_nonempty_iff] at hp
      haveI : IsEmpty (Fib p) := hp
      exact Or.inr inferInstance
  ·
    intro p
    by_cases hp : Nonempty (Fib p)
    · haveI : Nonempty (Fib p) := hp
      haveI : Unique (Fib p) := uniqueOfSubsingleton (Classical.choice hp)
      exact Or.inl (IsSimpleModule.congr
        (DirectSum.linearEquivOfUnique (R := RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) (fun j : Fib p => L j.1)))
    · rw [not_nonempty_iff] at hp
      haveI : IsEmpty (Fib p) := hp
      exact Or.inr inferInstance
  ·
    rintro p q hp_nss ⟨f⟩
    have hpne : Nonempty (Fib p) := by
      by_contra h
      rw [not_nonempty_iff] at h
      haveI : IsEmpty (Fib p) := h
      exact hp_nss inferInstance
    haveI : Nonempty (Fib p) := hpne
    haveI : Unique (Fib p) := uniqueOfSubsingleton (Classical.choice hpne)
    have hqne : Nonempty (Fib q) := by
      by_contra h
      rw [not_nonempty_iff] at h
      haveI : IsEmpty (Fib q) := h
      haveI : Subsingleton (⨁ j : Fib q, L j.1) := inferInstance
      exact hp_nss ⟨fun a b => f.injective (Subsingleton.elim (f a) (f b))⟩
    haveI : Nonempty (Fib q) := hqne
    haveI : Unique (Fib q) := uniqueOfSubsingleton (Classical.choice hqne)
    let eqp := DirectSum.linearEquivOfUnique (R := RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) (fun j : Fib p => L j.1)
    let eqq := DirectSum.linearEquivOfUnique (R := RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) (fun j : Fib q => L j.1)
    have hidx := hLdist (default : Fib p).1 (default : Fib q).1 ⟨eqp.symm ≪≫ₗ f ≪≫ₗ eqq⟩
    calc p = e (default : Fib p).1 := (default : Fib p).2.symm
      _ = e (default : Fib q).1 := by rw [hidx]
      _ = q := (default : Fib q).2
  ·
    refine ⟨iso ≪≫ₗ ?_⟩
    refine DirectSum.lequivCongrLeft k (Equiv.sigmaFiberEquiv (e : ι → Nat.Partition n)).symm
      ≪≫ₗ auxiliary (R := k) (fun p (j : Fib p) => S j.1 ⊗[k] L j.1)
      ≪≫ₗ DirectSum.linearEquivOfFamily (fun p =>
        (DirectSum.tensorProductLinearEquivOfSubsingleton (fun j : Fib p => S j.1) (fun j : Fib p => L j.1)).symm)

end RepresentationTheory.PartitionedDecomposition

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.PartitionedDecomposition.Auxiliary.statement016580 := _root_.RepresentationTheory.PartitionedDecomposition.existsIndexedSimpleDecomposition

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.PartitionedDecomposition.Auxiliary.statement018409 := _root_.RepresentationTheory.PartitionedDecomposition.auxiliary

attribute [source_ref "Chapter5/Discussion_after_Theorem5.22.1" (role := supporting)] _root_.RepresentationTheory.PartitionedDecomposition.Auxiliary.statement016580

attribute [source_ref "Chapter5/Theorem5.18.4" (role := primary)] _root_.RepresentationTheory.PartitionedDecomposition.Auxiliary.statement016580
