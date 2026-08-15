/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.PartitionPermutationRelations
import RepresentationTheory.FiniteGroups.CharacterRigidity
import RepresentationTheory.Representation.ModuleEquivAndTraceSeparation
import RepresentationTheory.InductionAndCoinduction
import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.Representation.FiniteProducts
import RepresentationTheory.FDRep.CharacterDecomposition
import RepresentationTheory.Alignment.Attribute

noncomputable section

open CategoryTheory Module

namespace RepresentationTheory.Auxiliary.FDRepPartitions

private theorem partitionSubspaceRepresentation_asModule_smul (n : ℕ) (la : Nat.Partition n)
    (a : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
    (v : (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n la).asModule) :
    a • v = (show ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) from a •
      (show ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) from v)) := by
  classical
  induction a using MonoidAlgebra.induction_on with
  | hM g =>
      change MonoidAlgebra.single g 1 • v = _
      rw [Representation.single_smul]
      simp only [one_smul, Representation.asModuleEquiv]
      simp [RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation,
        RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism]
      rfl
  | hadd x y hx hy =>
      rw [add_smul, hx, hy, add_smul]
  | hsmul r x hx =>
      rw [smul_assoc, hx, smul_assoc]

/-- For each natural number `n` and partition `la` of `n`, an auxiliary linear equivalence over the identity homomorphism of an auxiliary scalar ring, from an auxiliary representation’s underlying module to the subtype defined by the displayed auxiliary membership predicate. -/
noncomputable def auxiliaryRepresentationModuleLinearEquivSubtype (n : ℕ)
    (la : Nat.Partition n) :
    (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n la).asModule ≃ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n]
      RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la :=
  { (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n la).asModuleEquiv with
    map_smul' := fun a v => partitionSubspaceRepresentation_asModule_smul n la a v }

/-- Every simple finite-dimensional complex representation of `Perm (Fin n)` has a nonempty type of isomorphisms to an auxiliary representation at some formally elided index. -/
theorem exists_auxiliaryFDRepOfSimple (n : ℕ)
    (S : FDRep ℂ (Equiv.Perm (Fin n))) [Simple S] :
    ∃ la : Nat.Partition n,
      Nonempty (S ≅ RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep n la) := by
  haveI : IsSimpleModule (RepresentationTheory.PartitionAuxiliary.natIndexedType n)
      (Representation.asModule S.ρ) :=
    RepresentationTheory.SimpleRepresentationModules.isSimpleModule_of_simple_fdRep S
  obtain ⟨la, ⟨f⟩⟩ :=
    RepresentationTheory.SimpleModule.SubtypeRepresentation.exists_linearEquiv_to_subtype n
      (Representation.asModule S.ρ)
  let φ : Representation.asModule S.ρ ≃ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n]
      (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n la).asModule :=
    f ≪≫ₗ (auxiliaryRepresentationModuleLinearEquivSubtype n la).symm
  exact ⟨la, ⟨Action.mkIso
    (RepresentationTheory.Representation.ModuleEquivAndTraceSeparation.representationLinearEquiv φ).toFGModuleCatIso
    (fun g => by
      ext x
      exact RepresentationTheory.Representation.ModuleEquivAndTraceSeparation.representationLinearEquiv_intertwines φ g x)⟩⟩

/-- An auxiliary family assigning each partition of `n + 1` a finite-dimensional complex representation of `Perm (Fin n)`. -/
noncomputable def auxiliaryFDRepOfSuccessorPartitionPrime (n : ℕ)
    (μ : Nat.Partition (n + 1)) : FDRep ℂ (Equiv.Perm (Fin n)) :=
  FDRep.of
    ((RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) μ).ρ.comp
      (RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ n))

/-- An auxiliary family assigning each partition of `n + 1` a finite-dimensional complex representation of `Perm (Fin n)`. -/
noncomputable def auxiliaryFDRepOfSuccessorPartition (n : ℕ)
    (μ : Nat.Partition (n + 1)) : FDRep ℂ (Equiv.Perm (Fin n)) :=
  RepresentationTheory.Representation.FiniteProducts.finiteProduct
    (fun (p : ↥(RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred μ)) =>
      RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep n p.1)

/-- For each partition of `n + 1`, the two auxiliary finite-dimensional complex representations of `Perm (Fin n)` have a nonempty type of isomorphisms. -/
@[source_ref "Chapter5/Problem5.16.1" (role := primary)]
theorem auxiliaryFDRepOfSuccessorPartitionIso (n : ℕ)
    (μ : Nat.Partition (n + 1)) :
    Nonempty (auxiliaryFDRepOfSuccessorPartitionPrime n μ ≅
      auxiliaryFDRepOfSuccessorPartition n μ) := by
  apply RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
  funext σ
  unfold auxiliaryFDRepOfSuccessorPartitionPrime auxiliaryFDRepOfSuccessorPartition
  rw [RepresentationTheory.Representation.FiniteProducts.character_finiteProduct]
  change RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (n + 1) μ
      (RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ n σ) =
    ∑ p : ↥(RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred μ),
      RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n p.1 σ
  rw [RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.value_permutation_hom_succ_eq_sum_partition_finset_pred]
  exact (Finset.sum_attach
    (RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred μ)
    (fun p => RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n p σ)).symm

/-- An auxiliary family assigning each partition of `n` a finite-dimensional complex representation of `Perm (Fin (n + 1))`. -/
noncomputable def auxiliaryFDRepOfPartitionPrime (n : ℕ) (μ : Nat.Partition n) :
    FDRep ℂ (Equiv.Perm (Fin (n + 1))) :=
  FDRep.of (Representation.ind
    (RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ n)
    (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n μ))

/-- An auxiliary family assigning each partition of `n` a finite-dimensional complex representation of `Perm (Fin (n + 1))`. -/
noncomputable def auxiliaryFDRepOfPartition (n : ℕ) (μ : Nat.Partition n) :
    FDRep ℂ (Equiv.Perm (Fin (n + 1))) :=
  RepresentationTheory.Representation.FiniteProducts.finiteProduct
    (fun (p : ↥(RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_succ μ)) =>
      RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) p.1)

/-- An auxiliary operation sending a finite-dimensional complex representation of `Perm (Fin (n + 1))` to one of `Perm (Fin n)`. -/
noncomputable abbrev auxiliaryFDRepMapToPredecessor (n : ℕ)
    (S : FDRep ℂ (Equiv.Perm (Fin (n + 1)))) : FDRep ℂ (Equiv.Perm (Fin n)) :=
  (Action.res (FGModuleCat ℂ)
    (RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ n)).obj S

private theorem finrank_hom_auxiliaryFDRepOfPartitionPrime (n : ℕ)
    (μ : Nat.Partition n) (S : FDRep ℂ (Equiv.Perm (Fin (n + 1)))) :
    finrank ℂ (auxiliaryFDRepOfPartitionPrime n μ ⟶ S) =
      finrank ℂ
        (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep n μ ⟶
          auxiliaryFDRepMapToPredecessor n S) := by
  rw [← (FDRep.forget₂HomLinearEquiv (auxiliaryFDRepOfPartitionPrime n μ) S).finrank_eq]
  have hG :
      (forget₂ (FDRep ℂ (Equiv.Perm (Fin (n + 1))))
        (Rep ℂ (Equiv.Perm (Fin (n + 1))))).obj (auxiliaryFDRepOfPartitionPrime n μ) =
        Rep.ind
          (RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ n)
          (Rep.of (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n μ)) := rfl
  rw [hG, (Rep.indResHomEquiv
    (RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ n)
    (Rep.of (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n μ))
    ((forget₂ (FDRep ℂ (Equiv.Perm (Fin (n + 1))))
      (Rep ℂ (Equiv.Perm (Fin (n + 1))))).obj S)).finrank_eq]
  have hW : Rep.of
      (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation n μ) =
      (forget₂ (FDRep ℂ (Equiv.Perm (Fin n)))
        (Rep ℂ (Equiv.Perm (Fin n)))).obj
          (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep n μ) := rfl
  have hRes :
      (Rep.resFunctor
        (RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ n)).obj
          ((forget₂ (FDRep ℂ (Equiv.Perm (Fin (n + 1))))
            (Rep ℂ (Equiv.Perm (Fin (n + 1))))).obj S) =
        (forget₂ (FDRep ℂ (Equiv.Perm (Fin n)))
          (Rep ℂ (Equiv.Perm (Fin n)))).obj
            (auxiliaryFDRepMapToPredecessor n S) := rfl
  rw [← (FDRep.forget₂HomLinearEquiv
    (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep n μ)
    (auxiliaryFDRepMapToPredecessor n S)).finrank_eq, ← hW, ← hRes]

private theorem finrank_hom_symm' {G : Type} [Group G] [Finite G]
    (V W : FDRep ℂ G) : finrank ℂ (V ⟶ W) = finrank ℂ (W ⟶ V) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hVW := FDRep.scalar_product_char_eq_finrank_equivariant V W
  have hWV := FDRep.scalar_product_char_eq_finrank_equivariant W V
  have hcast : (finrank ℂ (V ⟶ W) : ℂ) = (finrank ℂ (W ⟶ V) : ℂ) := by
    rw [← hVW, ← hWV]
    congr 1
    rw [← Equiv.sum_comp (Equiv.inv G) (fun g => V.character g * W.character g⁻¹)]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    change W.character g * V.character g⁻¹ = V.character g⁻¹ * W.character g⁻¹⁻¹
    rw [inv_inv, mul_comm]
  exact_mod_cast hcast

open Classical in
private theorem partitionFDRep_predecessor_finrank_hom (n : ℕ) (μ : Nat.Partition n)
    (la : Nat.Partition (n + 1)) :
    finrank ℂ
      (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep n μ ⟶
        auxiliaryFDRepMapToPredecessor n
          (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) la)) =
      if (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ) ≤
        (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la) then 1 else 0 := by
  haveI : Invertible (Fintype.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hscalar := FDRep.scalar_product_char_eq_finrank_equivariant
    (auxiliaryFDRepMapToPredecessor n
      (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) la))
    (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep n μ)
  have hpair :
      RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.complex_function_operation n
        (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n μ)
        (fun σ => RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (n + 1) la
          (RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ n σ)) =
      (finrank ℂ
        (auxiliaryFDRepMapToPredecessor n
            (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) la) ⟶
          RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep n μ) : ℂ) := by
    have hres : ∀ σ : Equiv.Perm (Fin n),
        (auxiliaryFDRepMapToPredecessor n
          (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) la)).character σ =
          RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (n + 1) la
            (RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ n σ) := fun _ => rfl
    simpa [RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.complex_function_operation,
      invOf_eq_inv, smul_eq_mul,
      RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep_character_eq_auxiliary,
      hres, map_inv] using hscalar
  have hvalue :=
    RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.complex_function_operation_eq_indicator_le n μ la
  rw [hpair] at hvalue
  rw [finrank_hom_symm'
    (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep n μ)
    (auxiliaryFDRepMapToPredecessor n
      (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) la))]
  exact_mod_cast hvalue

/-- For each partition of `n`, the two auxiliary finite-dimensional complex representations of `Perm (Fin (n + 1))` have a nonempty type of isomorphisms. -/
@[source_ref "Chapter5/Problem5.16.1" (role := primary)]
theorem auxiliaryFDRepOfPartitionIso (n : ℕ) (μ : Nat.Partition n) :
    Nonempty (auxiliaryFDRepOfPartitionPrime n μ ≅ auxiliaryFDRepOfPartition n μ) := by
  classical
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_finrank_eq_of_finrank_hom_simple_eq _ _ _ rfl
    (fun S hS => ?_)
  haveI : Simple S := hS
  obtain ⟨la, ⟨e⟩⟩ := exists_auxiliaryFDRepOfSimple (n + 1) S
  have hleft : finrank ℂ (S ⟶ auxiliaryFDRepOfPartitionPrime n μ) =
      if (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ) ≤
        (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la) then 1 else 0 := by
    rw [finrank_hom_symm', finrank_hom_auxiliaryFDRepOfPartitionPrime]
    rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_eq_of_iso
      (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep n μ)
      ((Action.res (FGModuleCat ℂ)
        (RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ n)).mapIso e)]
    exact partitionFDRep_predecessor_finrank_hom n μ la
  have hiso :
      ∀ p : ↥(RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_succ μ),
      Nonempty
        (S ≅ RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) p.1) ↔
        la = p.1 := by
    intro p
    constructor
    · rintro ⟨f⟩
      exact (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep_iso_iff (n + 1) la p.1).mp
        ⟨e.symm ≪≫ f⟩
    · rintro rfl
      exact ⟨e⟩
  have hright : finrank ℂ (S ⟶ auxiliaryFDRepOfPartition n μ) =
      if (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ) ≤
        (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la) then 1 else 0 := by
    unfold auxiliaryFDRepOfPartition
    rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_eq_of_iso S
      (RepresentationTheory.Representation.FiniteProducts.finiteProductIsoBiproduct
        (fun p : ↥(RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_succ μ) =>
          RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) p.1))]
    rw [RepresentationTheory.FDRep.CharacterDecomposition.finrank_hom_biproduct]
    by_cases hmem : la ∈
      RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_succ μ
    · rw [if_pos (by simpa
        [RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_succ]
        using hmem)]
      calc
        ∑ p : ↥(RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_succ μ),
            finrank ℂ
              (S ⟶ RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) p.1) =
            finrank ℂ
              (S ⟶ RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) la) := by
          refine Finset.sum_eq_single (s := Finset.univ)
            (f := fun p : ↥(RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_succ μ) =>
              finrank ℂ
                (S ⟶ RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep (n + 1) p.1))
            (⟨la, hmem⟩ : ↥(RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_succ μ)) ?_ ?_
          · intro p _ hp
            rw [FDRep.finrank_hom_simple_simple, if_neg]
            intro hSp
            apply hp
            exact Subtype.ext ((hiso p).mp hSp).symm
          · simp
        _ = 1 := by rw [FDRep.finrank_hom_simple_simple, if_pos ⟨e⟩]
    · rw [if_neg (by simpa
        [RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_succ]
        using hmem)]
      apply Finset.sum_eq_zero
      intro p _
      rw [FDRep.finrank_hom_simple_simple, if_neg]
      intro hSp
      apply hmem
      rw [(hiso p).mp hSp]
      exact p.2
  rw [hleft, hright]

end RepresentationTheory.Auxiliary.FDRepPartitions
