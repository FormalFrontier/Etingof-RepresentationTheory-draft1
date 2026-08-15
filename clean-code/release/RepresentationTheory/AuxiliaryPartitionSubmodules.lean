/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryPartitionCardinality
import RepresentationTheory.Auxiliary.MembershipSubtypes










namespace RepresentationTheory.AuxiliaryPartitionSubmodules

noncomputable section

private abbrev G (n : ℕ) := Equiv.Perm (Fin n)
private abbrev Q (n : ℕ) (mu : Nat.Partition n) := G n ⧸ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu

private abbrev identityCosetVector (n : ℕ) (mu : Nat.Partition n) :
    RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu :=
  MonoidAlgebra.single (QuotientGroup.mk (1 : G n)) 1

/-- An auxiliary complex submodule indexed by a natural number and two partitions. -/




noncomputable def auxiliarySubmodule
    (n : ℕ) (mu nu : Nat.Partition n) : Submodule ℂ ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu) where
  carrier := {v | ∀ p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu,
    MonoidAlgebra.of ℂ (G n) p * (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n) = (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n)}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw p hp
    simp only [Submodule.coe_add, mul_add, hv p hp, hw p hp]
  smul_mem' := by
    intro c v hv p hp
    change MonoidAlgebra.of ℂ (G n) p * (c • (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n)) =
      c • (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
    rw [Algebra.mul_smul_comm, hv p hp]


private theorem permMod_smul_eq (n : ℕ) (mu : Nat.Partition n)
    (a : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (x : RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu) :
    a • x = (Representation.ofMulAction ℂ (G n) (Q n mu)).asAlgebraHom a x := rfl

private theorem of_smul_single (n : ℕ) (mu : Nat.Partition n)
    (g : G n) (q : Q n mu) (c : ℂ) :
    (MonoidAlgebra.of ℂ _ g : RepresentationTheory.PartitionAuxiliary.natIndexedType n) •
        (MonoidAlgebra.single q c : RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu) =
      MonoidAlgebra.single (g • q) c := by
  simp [permMod_smul_eq, Representation.ofMulAction_single]

private theorem permMod_smul_assoc (n : ℕ) (mu : Nat.Partition n)
    (r : ℂ) (a : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (x : RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu) :
    (r • a) • x = r • (a • x) := by
  change (Representation.ofMulAction ℂ (G n) (Q n mu)).asAlgebraHom (r • a) x =
    r • (Representation.ofMulAction ℂ (G n) (Q n mu)).asAlgebraHom a x
  simp only [map_smul, LinearMap.smul_apply]


private theorem rowSubgroup_fixes_identity (n : ℕ) (mu : Nat.Partition n)
    (p : G n) (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu) :
    p • (QuotientGroup.mk 1 : Q n mu) = QuotientGroup.mk 1 := by
  change QuotientGroup.mk (p * 1) = QuotientGroup.mk 1
  rw [mul_one, QuotientGroup.eq]
  simpa using (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu).inv_mem hp


private theorem equivariantMap_ext (n : ℕ) (mu nu : Nat.Partition n)
    (f g : RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu →ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n] ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu))
    (h : f (identityCosetVector n mu) = g (identityCosetVector n mu)) : f = g := by
  apply LinearMap.ext
  intro x
  let P : (Q n mu →₀ ℂ) → Prop := fun y =>
    f (MonoidAlgebra.ofCoeff y) = g (MonoidAlgebra.ofCoeff y)
  have hx : P x.coeff := by
    induction x.coeff using Finsupp.induction_linear with
    | zero => simp [P]
    | add x y hx hy => simpa [P, map_add] using congrArg₂ (· + ·) hx hy
    | single q c =>
      obtain ⟨σ, rfl⟩ := Quotient.exists_rep q
      have htranslate :
          (MonoidAlgebra.of ℂ _ σ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) • identityCosetVector n mu =
            (MonoidAlgebra.single (QuotientGroup.mk σ) 1 : RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu) := by
        rw [of_smul_single]
        rfl
      have hsingle :
          (MonoidAlgebra.single (QuotientGroup.mk σ) c : RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu) =
            c • ((MonoidAlgebra.of ℂ _ σ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) •
              identityCosetVector n mu) := by
        rw [htranslate]
        simp
      change f (MonoidAlgebra.single (QuotientGroup.mk σ) c) =
        g (MonoidAlgebra.single (QuotientGroup.mk σ) c)
      rw [hsingle, f.map_smul_of_tower, g.map_smul_of_tower, map_smul, map_smul, h]
  simpa [P] using hx

/-- An auxiliary complex-linear map from the displayed linear-map space to the partition-indexed submodule. -/

noncomputable def auxiliaryLinearMapToSubmodule (n : ℕ) (mu nu : Nat.Partition n) :
    (RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu →ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n] ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu)) →ₗ[ℂ]
      ↥(auxiliarySubmodule n mu nu) where
  toFun f := ⟨f (identityCosetVector n mu), by
    intro p hp
    have hfix : (MonoidAlgebra.of ℂ _ p : RepresentationTheory.PartitionAuxiliary.natIndexedType n) •
        identityCosetVector n mu = identityCosetVector n mu := by
      rw [of_smul_single, rowSubgroup_fixes_identity n mu p hp]
    exact congrArg Subtype.val (show
      (MonoidAlgebra.of ℂ _ p : RepresentationTheory.PartitionAuxiliary.natIndexedType n) • f (identityCosetVector n mu) =
        f (identityCosetVector n mu) by rw [← f.map_smul, hfix])⟩
  map_add' f g := by ext; rfl
  map_smul' c f := by ext; rfl


private theorem cosetRep_equivariance (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(auxiliarySubmodule n mu nu)) (σ : G n) (q : Q n mu) :
    MonoidAlgebra.of ℂ _ (Quotient.out (σ • q)) * (v.1 : RepresentationTheory.PartitionAuxiliary.natIndexedType n) =
      MonoidAlgebra.of ℂ _ σ * MonoidAlgebra.of ℂ _ (Quotient.out q) *
        (v.1 : RepresentationTheory.PartitionAuxiliary.natIndexedType n) := by
  have hEq : QuotientGroup.mk (Quotient.out (σ • q)) =
      (QuotientGroup.mk (σ * Quotient.out q) : Q n mu) := by
    rw [QuotientGroup.out_eq']
    change σ • q = QuotientGroup.mk (σ * Quotient.out q)
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have hmem := QuotientGroup.eq.mp hEq
  have hfactor : MonoidAlgebra.of ℂ _ σ * MonoidAlgebra.of ℂ _ (Quotient.out q) =
      MonoidAlgebra.of ℂ _ (Quotient.out (σ • q)) *
        MonoidAlgebra.of ℂ _ ((Quotient.out (σ • q))⁻¹ * (σ * Quotient.out q)) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [hfactor, mul_assoc, v.2 _ hmem]

private noncomputable def rowInvariantValue (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(auxiliarySubmodule n mu nu)) (q : Q n mu) : ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu) :=
  (MonoidAlgebra.of ℂ _ (Quotient.out q) : RepresentationTheory.PartitionAuxiliary.natIndexedType n) • v.1

private noncomputable def rowInvariantHomC (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(auxiliarySubmodule n mu nu)) :
    RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu →ₗ[ℂ] ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu) :=
  (Finsupp.lift ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu) ℂ (Q n mu)
    (rowInvariantValue n mu nu v)).comp
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] private theorem rowInvariantHomC_single (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(auxiliarySubmodule n mu nu)) (q : Q n mu) (c : ℂ) :
    rowInvariantHomC n mu nu v (MonoidAlgebra.single q c) =
      c • rowInvariantValue n mu nu v q := by
  simp [rowInvariantHomC, rowInvariantValue]

/-- Associates an auxiliary linear map to each element of the displayed partition-indexed submodule. -/

noncomputable def auxiliaryLinearMap (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(auxiliarySubmodule n mu nu)) :
    RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu →ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n] ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu) where
  toFun := rowInvariantHomC n mu nu v
  map_add' := (rowInvariantHomC n mu nu v).map_add
  map_smul' a x := by
    change rowInvariantHomC n mu nu v (a • x) = a • rowInvariantHomC n mu nu v x
    induction a using MonoidAlgebra.induction_on with
    | hM σ =>
        let P : (Q n mu →₀ ℂ) → Prop := fun y =>
          rowInvariantHomC n mu nu v
              ((MonoidAlgebra.of ℂ _ σ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) • MonoidAlgebra.ofCoeff y) =
            (MonoidAlgebra.of ℂ _ σ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) •
              rowInvariantHomC n mu nu v (MonoidAlgebra.ofCoeff y)
        have hx : P x.coeff := by
          induction x.coeff using Finsupp.induction_linear with
          | zero => simp [P]
          | add x y hx hy => simpa [P, smul_add, map_add] using congrArg₂ (· + ·) hx hy
          | single q c =>
            change rowInvariantHomC n mu nu v
                ((MonoidAlgebra.of ℂ _ σ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) •
                  (MonoidAlgebra.single q c : RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu)) = _
            rw [of_smul_single, rowInvariantHomC_single]
            change c • rowInvariantValue n mu nu v (σ • q) =
              (MonoidAlgebra.of ℂ _ σ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) •
                rowInvariantHomC n mu nu v (MonoidAlgebra.single q c)
            rw [rowInvariantHomC_single]
            apply Subtype.ext
            simp only [rowInvariantValue, SetLike.val_smul]
            change c • (MonoidAlgebra.of ℂ _ (Quotient.out (σ • q)) *
                (v.1 : RepresentationTheory.PartitionAuxiliary.natIndexedType n)) =
              MonoidAlgebra.of ℂ _ σ *
                (c • (MonoidAlgebra.of ℂ _ (Quotient.out q) *
                  (v.1 : RepresentationTheory.PartitionAuxiliary.natIndexedType n)))
            rw [Algebra.mul_smul_comm]
            congr 1
            simpa only [mul_assoc] using cosetRep_equivariance n mu nu v σ q
        simpa [P] using hx
    | hadd a b ha hb => rw [add_smul, map_add, ha, hb, add_smul]
    | hsmul r a ha => rw [permMod_smul_assoc, map_smul, ha, smul_assoc]

private theorem rowInvariantHom_apply_identity (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(auxiliarySubmodule n mu nu)) :
    auxiliaryLinearMap n mu nu v (identityCosetVector n mu) = v.1 := by
  change rowInvariantHomC n mu nu v (identityCosetVector n mu) = v.1
  rw [rowInvariantHomC_single]
  apply Subtype.ext
  change (1 : ℂ) • (MonoidAlgebra.of ℂ _
    (Quotient.out (QuotientGroup.mk (1 : G n) : Q n mu)) *
      (v.1 : RepresentationTheory.PartitionAuxiliary.natIndexedType n)) = (v.1 : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
  rw [one_smul]
  apply v.2
  have hEq : (QuotientGroup.mk (1 : G n) : Q n mu) =
      QuotientGroup.mk (Quotient.out (QuotientGroup.mk (1 : G n) : Q n mu)) :=
    (QuotientGroup.out_eq' _).symm
  simpa using QuotientGroup.eq.mp hEq

/-- An auxiliary linear equivalence between the displayed linear-map space and partition-indexed submodule. -/



noncomputable def auxiliaryLinearEquiv (n : ℕ)
    (mu nu : Nat.Partition n) :
    (RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu →ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n] ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu)) ≃ₗ[ℂ]
      ↥(auxiliarySubmodule n mu nu) :=
  LinearEquiv.ofBijective (auxiliaryLinearMapToSubmodule n mu nu) ⟨
    fun f g h => equivariantMap_ext n mu nu f g (congrArg Subtype.val h),
    fun v => ⟨auxiliaryLinearMap n mu nu v, by
      apply Subtype.ext
      exact rowInvariantHom_apply_identity n mu nu v⟩⟩

/-- The displayed auxiliary natural-number value equals the complex dimension of the corresponding submodule. -/

theorem auxiliary_nat_value_eq_finrank (n : ℕ)
    (mu nu : Nat.Partition n) :
    RepresentationTheory.AuxiliaryPartitionDecomposition.auxiliaryNatValue n mu nu = Module.finrank ℂ (auxiliarySubmodule n mu nu) := by
  change Module.finrank ℂ
      (RepresentationTheory.PartitionLinearMapVanishing.partitionIndexedType n mu →ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n] ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu)) = _
  exact (auxiliaryLinearEquiv n mu nu).finrank_eq



/-- An auxiliary complex-linear endomorphism of the displayed partition-dependent space. -/


noncomputable def auxiliaryEndomorphism (n : ℕ) (mu nu : Nat.Partition n) :
    RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu →ₗ[ℂ] RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu where
  toFun v := (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ •
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu : RepresentationTheory.PartitionAuxiliary.natIndexedType n) • v
  map_add' v w := by simp only [smul_add]
  map_smul' c v := by
    apply Subtype.ext
    change (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ •
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * (c • (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n))) =
      c • ((Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ •
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n)))
    rw [Algebra.mul_smul_comm]
    simp only [smul_smul]
    rw [mul_comm c]

/-- The value of the auxiliary endomorphism belongs to the displayed partition-indexed submodule. -/

theorem auxiliaryEndomorphism_mem (n : ℕ) (mu nu : Nat.Partition n)
    (v : RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu) :
    auxiliaryEndomorphism n mu nu v ∈ auxiliarySubmodule n mu nu := by
  intro p hp
  change MonoidAlgebra.of ℂ (G n) p *
      ((Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ •
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n))) =
    (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ •
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n))
  rw [Algebra.mul_smul_comm, ← mul_assoc, RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.perm_mul_eq_self_of_mem p hp]

/-- The auxiliary endomorphism fixes every element belonging to the displayed submodule. -/

@[simp] theorem auxiliaryEndomorphism_apply (n : ℕ) (mu nu : Nat.Partition n)
    (v : auxiliarySubmodule n mu nu) :
    auxiliaryEndomorphism n mu nu v.1 = v.1 := by
  classical
  apply Subtype.ext
  change (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ •
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * (v.1 : RepresentationTheory.PartitionAuxiliary.natIndexedType n)) = (v.1 : RepresentationTheory.PartitionAuxiliary.natIndexedType n)
  have hsum : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * (v.1 : RepresentationTheory.PartitionAuxiliary.natIndexedType n) =
      (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ) • (v.1 : RepresentationTheory.PartitionAuxiliary.natIndexedType n) := by
    simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun p _ => v.2 p.val p.prop), Finset.sum_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [hsum, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu))).ne'

/-- An auxiliary linear map from the ambient partition-dependent space into the displayed submodule. -/

noncomputable def auxiliaryAmbientToSubmodule (n : ℕ) (mu nu : Nat.Partition n) :
    RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu →ₗ[ℂ] auxiliarySubmodule n mu nu where
  toFun v := ⟨auxiliaryEndomorphism n mu nu v, auxiliaryEndomorphism_mem n mu nu v⟩
  map_add' v w := Subtype.ext ((auxiliaryEndomorphism n mu nu).map_add v w)
  map_smul' c v := Subtype.ext ((auxiliaryEndomorphism n mu nu).map_smul c v)

/-- The auxiliary map into the submodule sends an element of that submodule to the same element. -/

@[simp] theorem auxiliaryAmbientToSubmodule_apply (n : ℕ)
    (mu nu : Nat.Partition n) (v : auxiliarySubmodule n mu nu) :
    auxiliaryAmbientToSubmodule n mu nu v.1 = v := by
  apply Subtype.ext
  exact auxiliaryEndomorphism_apply n mu nu v

/-- Maps each auxiliary indexing object to an element of the displayed partition-indexed submodule. -/

noncomputable def auxiliaryGenerator (n : ℕ)
    (mu nu : Nat.Partition n) (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu) :
    auxiliarySubmodule n mu nu :=
  auxiliaryAmbientToSubmodule n mu nu (RepresentationTheory.Auxiliary.MembershipSubtypes.to_membershipSubtype T)

/-- The range of the auxiliary generating map spans the entire displayed submodule. -/



theorem auxiliary_span_range_eq_top (n : ℕ)
    (mu nu : Nat.Partition n) :
    Submodule.span ℂ (Set.range (auxiliaryGenerator n mu nu)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : auxiliaryAmbientToSubmodule n mu nu v.1 = v :=
    auxiliaryAmbientToSubmodule_apply n mu nu v
  let b := RepresentationTheory.Auxiliary.MembershipSubtypes.membershipSubtypeBasis (n := n) (la := nu)
  have hrepr := b.sum_repr v.1
  rw [← hv, ← hrepr, map_sum]
  apply Submodule.sum_mem
  intro T hT
  rw [map_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨T, ?_⟩
  simp only [auxiliaryGenerator, b, RepresentationTheory.Auxiliary.MembershipSubtypes.membershipSubtypeBasis_apply]

/-- An auxiliary type indexed by a natural number and two partitions of that number. -/


abbrev auxiliaryStructure (n : ℕ) (mu nu : Nat.Partition n) :=
  Module.Basis (RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) ℂ ↥(auxiliarySubmodule n mu nu)

/-- Given the displayed auxiliary structure, the two displayed natural-number quantities are equal. -/

theorem auxiliary_nat_value_eq_of_structure (n : ℕ)
    (mu nu : Nat.Partition n) (b : auxiliaryStructure n mu nu) :
    RepresentationTheory.AuxiliaryPartitionDecomposition.auxiliaryNatValue n mu nu = RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryPartitionPairNat n nu mu := by
  letI := Fintype.ofFinite (RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu)
  rw [auxiliary_nat_value_eq_finrank,
    Module.finrank_eq_card_basis b, RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryCard_eq_natCard,
    Nat.card_eq_fintype_card]

end

end RepresentationTheory.AuxiliaryPartitionSubmodules
