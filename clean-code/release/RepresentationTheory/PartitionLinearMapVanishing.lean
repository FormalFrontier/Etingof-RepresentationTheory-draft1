/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
import RepresentationTheory.YoungDiagram.PartitionConstructions
import RepresentationTheory.SymmetricGroup.PartitionDominance
import RepresentationTheory.SimpleModule.SubtypeRepresentation
import RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra
import RepresentationTheory.PartitionAuxiliary
open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
open RepresentationTheory.SymmetricGroup.PartitionDominance
open RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra
open RepresentationTheory.PartitionAuxiliary
namespace RepresentationTheory.PartitionLinearMapVanishing
/-- A binary relation between partitions of the same natural number. -/
def partitionRelation {n : ℕ} (mu la : Nat.Partition n) : Prop :=
  Partition.Dominates mu la
/-- An auxiliary binary predicate on pairs of partitions with a common size. -/
def partitionRelation' {n : ℕ} (mu la : Nat.Partition n) : Prop :=
  partitionRelation mu la ∧ mu ≠ la
/-- A type assigned to each partition of a natural number. -/
noncomputable abbrev partitionIndexedType (n : ℕ) (la : Nat.Partition n) :=
  MonoidAlgebra ℂ (Equiv.Perm (Fin n) ⧸ auxiliaryPartitionPermutationSubgroupB n la)
/-- The module structure on the type associated with a partition. -/
noncomputable instance partitionIndexedType.instModule (n : ℕ) (la : Nat.Partition n) :
    Module (natIndexedType n) (partitionIndexedType n la) :=
  Module.compHom _ (Representation.ofMulAction ℂ (Equiv.Perm (Fin n))
    (Equiv.Perm (Fin n) ⧸ auxiliaryPartitionPermutationSubgroupB n la)).asAlgebraHom.toRingHom
noncomputable section
private abbrev G' (n : ℕ) := Equiv.Perm (Fin n)
private abbrev Q (n : ℕ) (la : Nat.Partition n) :=
  G' n ⧸ auxiliaryPartitionPermutationSubgroupB n la
private lemma permMod_smul_eq (n : ℕ) (la : Nat.Partition n)
    (a : natIndexedType n) (x : partitionIndexedType n la) :
    a • x = (Representation.ofMulAction ℂ (G' n) (Q n la)).asAlgebraHom a x := rfl
private lemma of_smul_single (n : ℕ) (la : Nat.Partition n)
    (g : G' n) (q : Q n la) (c : ℂ) :
    (MonoidAlgebra.of ℂ _ g : natIndexedType n) •
      (MonoidAlgebra.single q c : partitionIndexedType n la) =
    MonoidAlgebra.single (g • q) c := by
  simp [permMod_smul_eq, Representation.ofMulAction_single]
private lemma rowSubgroup_fixes_identity (n : ℕ) (la : Nat.Partition n)
    (p : G' n) (hp : p ∈ auxiliaryPartitionPermutationSubgroupB n la) :
    (p • (QuotientGroup.mk 1 : Q n la)) = QuotientGroup.mk 1 := by
  change QuotientGroup.mk (p * 1) = QuotientGroup.mk 1
  rw [mul_one, QuotientGroup.eq]
  simpa using (auxiliaryPartitionPermutationSubgroupB n la).inv_mem hp
private lemma permMod_cyclic (n : ℕ) (la : Nat.Partition n) :
    Submodule.span (natIndexedType n)
      {(MonoidAlgebra.single (QuotientGroup.mk (1 : G' n)) (1 : ℂ) :
        partitionIndexedType n la)} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)
  | single q c =>
    rw [Submodule.mem_span_singleton]
    obtain ⟨σ, rfl⟩ := Quotient.exists_rep q
    refine ⟨MonoidAlgebra.single σ c, ?_⟩
    rw [permMod_smul_eq]
    simp [Representation.asAlgebraHom_single, Representation.ofMulAction_single, mul_one,
      show σ • (QuotientGroup.mk 1 : Q n la) = QuotientGroup.mk σ from by
        change QuotientGroup.mk (σ * 1) = QuotientGroup.mk σ; rw [mul_one]]
private lemma rowSymmetrizer_annihilates_specht (n : ℕ) (la mu : Nat.Partition n)
    (h : ¬ partitionRelation mu la)
    (v : natIndexedType n) (hv : v ∈ partitionSubmodule n mu) :
    auxiliaryPartitionGroupAlgebraElementB n la * v = 0 := by
  obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp hv
  rw [show v = x • auxiliaryPartitionGroupAlgebraElementC n mu from hx.symm]
  change
    auxiliaryPartitionGroupAlgebraElementB n la *
      (x * auxiliaryPartitionGroupAlgebraElementC n mu) = 0
  simp only [auxiliaryPartitionGroupAlgebraElementC]
  rw [show auxiliaryPartitionGroupAlgebraElementB n la *
      (x * (auxiliaryPartitionGroupAlgebraElementA n mu *
        auxiliaryPartitionGroupAlgebraElementB n mu)) =
    (auxiliaryPartitionGroupAlgebraElementB n la *
      (x * auxiliaryPartitionGroupAlgebraElementA n mu)) *
        auxiliaryPartitionGroupAlgebraElementB n mu
    from by simp only [mul_assoc],
    show auxiliaryPartitionGroupAlgebraElementB n la *
        (x * auxiliaryPartitionGroupAlgebraElementA n mu) =
      auxiliaryPartitionGroupAlgebraElementB n la * x *
        auxiliaryPartitionGroupAlgebraElementA n mu from by rw [mul_assoc],
    sandwich_eq_zero_of_not_dominates n la mu h, zero_mul]
end
set_option linter.style.longLine false in
/-- If the auxiliary partition relation holds, every linear map from the first partition-indexed type to the membership subtype for the second partition is zero. -/
theorem linearMap_to_mem_eq_zero_of_partitionRelation'
    (n : ℕ) (la mu : Nat.Partition n)
    (hdom : partitionRelation' la mu) :
    ∀ f : partitionIndexedType n la →ₗ[natIndexedType n]
      ↥(partitionSubmodule n mu), f = 0 := by
  classical
  have h_not_dom : ¬ partitionRelation mu la := by
    intro hmu
    exact hdom.2 (Partition.Dominates.antisymm hdom.1 hmu)
  intro f
  set e : partitionIndexedType n la := MonoidAlgebra.single (QuotientGroup.mk 1) 1 with he_def
  set v₀ := f e with hv₀_def
  suffices hv₀_zero : v₀ = 0 by
    apply LinearMap.ext; intro x
    have hx : x ∈ Submodule.span (natIndexedType n) {e} :=
      permMod_cyclic n la ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change f (a • e) = 0
    rw [f.map_smul]
    have : f e = (0 : ↥(partitionSubmodule n mu)) := by rw [← hv₀_def]; exact hv₀_zero
    rw [this, smul_zero]
  have h_inv : ∀ p ∈ auxiliaryPartitionPermutationSubgroupB n la,
      (MonoidAlgebra.of ℂ _ p : natIndexedType n) • v₀ = v₀ := by
    intro p hp
    have h_fix : (MonoidAlgebra.of ℂ _ p : natIndexedType n) • e = e := by
      rw [of_smul_single, rowSubgroup_fixes_identity n la p hp]
    change (MonoidAlgebra.of ℂ _ p) • (f e) = f e
    rw [← f.map_smul, h_fix]
  have h_inv_val : ∀ p ∈ auxiliaryPartitionPermutationSubgroupB n la,
      MonoidAlgebra.of ℂ (G' n) p * (v₀ : natIndexedType n) = (v₀ : natIndexedType n) :=
    fun p hp => congrArg Subtype.val (h_inv p hp)
  have h_row_sym : auxiliaryPartitionGroupAlgebraElementB n la * (v₀ : natIndexedType n) =
      (Fintype.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ) •
        (v₀ : natIndexedType n) := by
    simp only [auxiliaryPartitionGroupAlgebraElementB, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun p _ => h_inv_val p.val p.prop)]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  have h_annihilate : auxiliaryPartitionGroupAlgebraElementB n la * (v₀ : natIndexedType n) = 0 :=
    rowSymmetrizer_annihilates_specht n la mu h_not_dom (v₀ : natIndexedType n) v₀.prop
  have h_card_ne_zero : (Fintype.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hv₀_val_zero : (v₀ : natIndexedType n) = 0 := by
    rw [h_row_sym] at h_annihilate
    exact (smul_eq_zero.mp h_annihilate).resolve_left h_card_ne_zero
  exact Subtype.ext hv₀_val_zero
set_option linter.style.longLine false in
/-- If the partition relation fails in the reverse direction, every linear map into the corresponding membership subtype is zero. -/
@[source_ref "Chapter5/Proposition5.14.1" (role := supporting),
  source_ref "Chapter5/Discussion_proof_of_Proposition5.14.1" (role := primary)]
theorem linearMap_to_mem_eq_zero_of_not_partitionRelation
    (n : ℕ) (la mu : Nat.Partition n)
    (h_not_dom : ¬ partitionRelation mu la) :
    ∀ f : partitionIndexedType n la →ₗ[natIndexedType n]
      ↥(partitionSubmodule n mu), f = 0 := by
  classical
  intro f
  set e : partitionIndexedType n la := MonoidAlgebra.single (QuotientGroup.mk 1) 1 with he_def
  set v₀ := f e with hv₀_def
  suffices hv₀_zero : v₀ = 0 by
    apply LinearMap.ext; intro x
    have hx : x ∈ Submodule.span (natIndexedType n) {e} :=
      permMod_cyclic n la ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change f (a • e) = 0
    rw [f.map_smul]
    have : f e = (0 : ↥(partitionSubmodule n mu)) := by rw [← hv₀_def]; exact hv₀_zero
    rw [this, smul_zero]
  have h_inv : ∀ p ∈ auxiliaryPartitionPermutationSubgroupB n la,
      (MonoidAlgebra.of ℂ _ p : natIndexedType n) • v₀ = v₀ := by
    intro p hp
    have h_fix : (MonoidAlgebra.of ℂ _ p : natIndexedType n) • e = e := by
      rw [of_smul_single, rowSubgroup_fixes_identity n la p hp]
    change (MonoidAlgebra.of ℂ _ p) • (f e) = f e
    rw [← f.map_smul, h_fix]
  have h_inv_val : ∀ p ∈ auxiliaryPartitionPermutationSubgroupB n la,
      MonoidAlgebra.of ℂ (G' n) p * (v₀ : natIndexedType n) = (v₀ : natIndexedType n) :=
    fun p hp => congrArg Subtype.val (h_inv p hp)
  have h_row_sym : auxiliaryPartitionGroupAlgebraElementB n la * (v₀ : natIndexedType n) =
      (Fintype.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ) •
        (v₀ : natIndexedType n) := by
    simp only [auxiliaryPartitionGroupAlgebraElementB, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun p _ => h_inv_val p.val p.prop)]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  have h_annihilate : auxiliaryPartitionGroupAlgebraElementB n la * (v₀ : natIndexedType n) = 0 :=
    rowSymmetrizer_annihilates_specht n la mu h_not_dom (v₀ : natIndexedType n) v₀.prop
  have h_card_ne_zero : (Fintype.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hv₀_val_zero : (v₀ : natIndexedType n) = 0 := by
    rw [h_row_sym] at h_annihilate
    exact (smul_eq_zero.mp h_annihilate).resolve_left h_card_ne_zero
  exact Subtype.ext hv₀_val_zero
set_option linter.style.longLine false in
/-- When the target partition is lexicographically smaller than the source partition, every linear map into its membership subtype is zero. -/
@[source_ref "Chapter5/Proposition5.14.1" (role := primary)]
theorem linearMap_to_mem_eq_zero_of_lexLt
    (n : ℕ) (la mu : Nat.Partition n)
    (h : Partition.LexLt mu la) :
    ∀ f : partitionIndexedType n la →ₗ[natIndexedType n]
      ↥(partitionSubmodule n mu), f = 0 := by
  apply linearMap_to_mem_eq_zero_of_not_partitionRelation n la mu
  intro hdom
  exact h.not_dominates (fun k => hdom k)
noncomputable section
private lemma row_mul_rowSym_youngSymmetrizer (n : ℕ) (la : Nat.Partition n)
    (p : G' n) (hp : p ∈ auxiliaryPartitionPermutationSubgroupB n la) :
    MonoidAlgebra.of ℂ _ p *
      (auxiliaryPartitionGroupAlgebraElementB n la *
        auxiliaryPartitionGroupAlgebraElementC n la) =
    auxiliaryPartitionGroupAlgebraElementB n la *
      auxiliaryPartitionGroupAlgebraElementC n la := by
  rw [← mul_assoc, perm_mul_eq_self_of_mem p hp]
private lemma youngSymmetrizer_ne_zero (n : ℕ) (la : Nat.Partition n) :
    auxiliaryPartitionGroupAlgebraElementC n la ≠ 0 := by
  haveI := partitionSubmodule_isSimpleModule n la
  intro h
  have hbot : partitionSubmodule n la = ⊥ := Submodule.span_singleton_eq_bot.mpr h
  exact (isSimpleModule_iff_isAtom.mp ‹_›).1 hbot
private lemma rowSym_youngSym_ne_zero (n : ℕ) (la : Nat.Partition n) :
    auxiliaryPartitionGroupAlgebraElementB n la *
      auxiliaryPartitionGroupAlgebraElementC n la ≠ 0 := by
  classical
  set c := auxiliaryPartitionGroupAlgebraElementC n la
  have h_ca : c * auxiliaryPartitionGroupAlgebraElementB n la =
      (Fintype.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ) • c := by
    simp only [auxiliaryPartitionGroupAlgebraElementB, Finset.mul_sum]
    have key : ∀ g : ↥(auxiliaryPartitionPermutationSubgroupB n la),
        c * MonoidAlgebra.of ℂ _ g.val = c :=
      fun g => by
        change auxiliaryPartitionGroupAlgebraElementC n la *
          MonoidAlgebra.of ℂ _ g.val = auxiliaryPartitionGroupAlgebraElementC n la
        rw [auxiliaryPartitionGroupAlgebraElementC, mul_assoc, mul_perm_eq_self_of_mem g.val g.prop]
    simp_rw [key, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  have h_cac : c * (auxiliaryPartitionGroupAlgebraElementB n la * c) =
      (Fintype.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ) • (c * c) := by
    rw [← mul_assoc, h_ca, smul_mul_assoc]
  have h_csq_ne := self_mul_ne_zero n la
  have h_P_ne : (Fintype.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  intro h_ac_zero
  exact smul_ne_zero h_P_ne h_csq_ne (by rw [← h_cac, h_ac_zero, mul_zero])
private lemma of_mul_rowSym_youngSymmetrizer_ne_zero (n : ℕ) (la : Nat.Partition n) (g : G' n) :
    MonoidAlgebra.of ℂ _ g *
      (auxiliaryPartitionGroupAlgebraElementB n la *
        auxiliaryPartitionGroupAlgebraElementC n la) ≠ 0 := by
  intro h
  apply rowSym_youngSym_ne_zero n la
  have : MonoidAlgebra.of ℂ _ g⁻¹ * (MonoidAlgebra.of ℂ _ g *
      (auxiliaryPartitionGroupAlgebraElementB n la * auxiliaryPartitionGroupAlgebraElementC n la)) =
      auxiliaryPartitionGroupAlgebraElementB n la *
        auxiliaryPartitionGroupAlgebraElementC n la := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [h, mul_zero] at this
  exact this.symm
private lemma row_invariant_is_scalar_of_rowSym_youngSym (n : ℕ) (la : Nat.Partition n)
    (v : natIndexedType n) (hv : v ∈ partitionSubmodule n la)
    (hinv : ∀ p ∈ auxiliaryPartitionPermutationSubgroupB n la,
      MonoidAlgebra.of ℂ (G' n) p * v = v) :
    ∃ c : ℂ, v = c • (auxiliaryPartitionGroupAlgebraElementB n la *
      auxiliaryPartitionGroupAlgebraElementC n la) := by
  classical
  obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp hv
  rw [smul_eq_mul] at hx
  rw [← hx]
  have h_sum : auxiliaryPartitionGroupAlgebraElementB n la *
      (x * auxiliaryPartitionGroupAlgebraElementC n la) =
      (Fintype.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ) •
        (x * auxiliaryPartitionGroupAlgebraElementC n la) := by
    have key : ∀ p : auxiliaryPartitionPermutationSubgroupB n la,
        (MonoidAlgebra.of ℂ (G' n) p.val) * (x * auxiliaryPartitionGroupAlgebraElementC n la) =
         x * auxiliaryPartitionGroupAlgebraElementC n la := by
      intro p; have h := hinv p.val p.prop; rwa [← hx] at h
    simp only [auxiliaryPartitionGroupAlgebraElementB, Finset.sum_mul, key,
      Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ]
  obtain ⟨ℓ', hℓ'⟩ := exists_fixed_sign_sandwich_eq_smul_mul n la
  have h_sandwich : auxiliaryPartitionGroupAlgebraElementB n la *
      (x * auxiliaryPartitionGroupAlgebraElementC n la) =
      ℓ' x • (auxiliaryPartitionGroupAlgebraElementB n la *
        auxiliaryPartitionGroupAlgebraElementC n la) := by
    simp only [auxiliaryPartitionGroupAlgebraElementC]
    rw [show auxiliaryPartitionGroupAlgebraElementB n la *
        (x * (auxiliaryPartitionGroupAlgebraElementA n la *
          auxiliaryPartitionGroupAlgebraElementB n la)) =
        (auxiliaryPartitionGroupAlgebraElementB n la * x *
          auxiliaryPartitionGroupAlgebraElementA n la) *
            auxiliaryPartitionGroupAlgebraElementB n la from by
      simp only [mul_assoc]]
    rw [hℓ', smul_mul_assoc, mul_assoc]
  have h_card_ne_zero : (Fintype.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  rw [h_sandwich] at h_sum
  replace h_sum := congr_arg
    ((Fintype.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ)⁻¹ • ·) h_sum.symm
  simp only [smul_smul, inv_mul_cancel₀ h_card_ne_zero, one_smul] at h_sum
  exact ⟨(Fintype.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ)⁻¹ * ℓ' x,
    h_sum⟩
private lemma coset_rep_equivariance (n : ℕ) (la : Nat.Partition n)
    (σ : G' n) (q : Q n la) :
    MonoidAlgebra.of ℂ _ (Quotient.out (σ • q)) *
      (auxiliaryPartitionGroupAlgebraElementB n la * auxiliaryPartitionGroupAlgebraElementC n la) =
    MonoidAlgebra.of ℂ _ σ * MonoidAlgebra.of ℂ _ (Quotient.out q) *
      (auxiliaryPartitionGroupAlgebraElementB n la *
        auxiliaryPartitionGroupAlgebraElementC n la) := by
  have h_eq : QuotientGroup.mk (Quotient.out (σ • q)) =
      (QuotientGroup.mk (σ * Quotient.out q) : Q n la) := by
    rw [QuotientGroup.out_eq']
    change σ • q = QuotientGroup.mk (σ * Quotient.out q)
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have hmem := QuotientGroup.eq.mp h_eq
  have key : MonoidAlgebra.of ℂ _ σ * MonoidAlgebra.of ℂ _ (Quotient.out q) =
      MonoidAlgebra.of ℂ _ (Quotient.out (σ • q)) *
        MonoidAlgebra.of ℂ _ ((Quotient.out (σ • q))⁻¹ * (σ * Quotient.out q)) := by
    rw [← map_mul, ← map_mul]; congr 1; group
  rw [key, mul_assoc, row_mul_rowSym_youngSymmetrizer n la _ hmem]
end
noncomputable section
private abbrev canonicalHom_v (n : ℕ) (la : Nat.Partition n) (q : Q n la) :
    natIndexedType n :=
  MonoidAlgebra.of ℂ _ (Quotient.out q) *
    (auxiliaryPartitionGroupAlgebraElementB n la *
      auxiliaryPartitionGroupAlgebraElementC n la)
private noncomputable def canonicalHom_ℂ (n : ℕ) (la : Nat.Partition n) :
    partitionIndexedType n la →ₗ[ℂ] natIndexedType n :=
  Finsupp.lift (natIndexedType n) ℂ (Q n la) (canonicalHom_v n la) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
private lemma permMod_smul_assoc (n : ℕ) (la : Nat.Partition n)
    (r : ℂ) (a : natIndexedType n) (x : partitionIndexedType n la) :
    (r • a) • x = r • (a • x) := by
  change (Representation.ofMulAction ℂ (G' n) (Q n la)).asAlgebraHom (r • a) x =
    r • ((Representation.ofMulAction ℂ (G' n) (Q n la)).asAlgebraHom a x)
  simp only [map_smul, LinearMap.smul_apply]
set_option maxHeartbeats 3200000 in
private noncomputable def canonicalHom (n : ℕ) (la : Nat.Partition n) :
    partitionIndexedType n la →ₗ[natIndexedType n] ↥(partitionSubmodule n la) where
  toFun x :=
    ⟨canonicalHom_ℂ n la x, by
      simp only [canonicalHom_ℂ, LinearMap.comp_apply,
        Finsupp.lift_apply]
      apply Submodule.sum_mem; intro q _
      exact Submodule.smul_of_tower_mem (partitionSubmodule n la) (x.coeff q)
        (Submodule.mem_span_singleton.mpr
          ⟨MonoidAlgebra.of ℂ _ (Quotient.out q) * auxiliaryPartitionGroupAlgebraElementB n la,
           by simp [canonicalHom_v, smul_eq_mul, mul_assoc]⟩)⟩
  map_add' x y := Subtype.ext (map_add (canonicalHom_ℂ n la) x y)
  map_smul' a x := by
    refine Subtype.ext ?_
    simp only [RingHom.id_apply, SetLike.val_smul]
    change canonicalHom_ℂ n la (a • x) = a • canonicalHom_ℂ n la x
    induction a using MonoidAlgebra.induction_on with
    | hM σ =>
      induction x using MonoidAlgebra.induction_linear with
      | zero => simp [smul_zero, map_zero]
      | add x y hx hy =>
        rw [smul_add, map_add, hx, hy, ← smul_add, ← map_add]
      | single q c =>
        rw [of_smul_single]
        have lift_single : ∀ q' c', canonicalHom_ℂ n la (MonoidAlgebra.single q' c') =
            c' • canonicalHom_v n la q' := by
          intro q' c'
          simp [canonicalHom_ℂ, Finsupp.lift_apply, Finsupp.sum_single_index]
        rw [lift_single, lift_single]
        change c • canonicalHom_v n la (σ • q) =
          (MonoidAlgebra.of ℂ _ σ) * (c • canonicalHom_v n la q)
        rw [Algebra.mul_smul_comm]
        apply congrArg (c • ·)
        simp only [canonicalHom_v]
        rw [coset_rep_equivariance n la σ q, mul_assoc]
    | hadd a b ha hb =>
      rw [add_smul, map_add, ha, hb, add_smul]
    | hsmul r a ha =>
      rw [permMod_smul_assoc, map_smul, ha, smul_assoc]
private lemma canonicalHom_apply_identity (n : ℕ) (la : Nat.Partition n) :
    (canonicalHom n la (MonoidAlgebra.single (QuotientGroup.mk 1) 1) : natIndexedType n) =
      canonicalHom_v n la (QuotientGroup.mk 1) := by
  change canonicalHom_ℂ n la
    (MonoidAlgebra.single (QuotientGroup.mk (1 : G' n)) (1 : ℂ)) = _
  simp [canonicalHom_ℂ, Finsupp.lift_apply, Finsupp.sum_single_index]
private lemma equivariant_map_ext_of_agree_on_e (n : ℕ) (la : Nat.Partition n)
    (f g : partitionIndexedType n la →ₗ[natIndexedType n] ↥(partitionSubmodule n la))
    (h : f (MonoidAlgebra.single (QuotientGroup.mk 1) 1) =
         g (MonoidAlgebra.single (QuotientGroup.mk 1) 1)) : f = g := by
  apply LinearMap.ext; intro x
  have hx : x ∈ Submodule.span (natIndexedType n)
      {(MonoidAlgebra.single (QuotientGroup.mk (1 : G' n)) (1 : ℂ) :
        partitionIndexedType n la)} :=
    permMod_cyclic n la ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, map_smul, h]
private lemma equivariant_map_row_invariant (n : ℕ) (la : Nat.Partition n)
    (f : partitionIndexedType n la →ₗ[natIndexedType n] ↥(partitionSubmodule n la)) :
    ∀ p ∈ auxiliaryPartitionPermutationSubgroupB n la,
      MonoidAlgebra.of ℂ (G' n) p *
        (f (MonoidAlgebra.single (QuotientGroup.mk 1) 1) : natIndexedType n) =
        (f (MonoidAlgebra.single (QuotientGroup.mk 1) 1) : natIndexedType n) := by
  intro p hp
  have h_fix : (MonoidAlgebra.of ℂ _ p : natIndexedType n) •
      (MonoidAlgebra.single (QuotientGroup.mk (1 : G' n)) (1 : ℂ) : partitionIndexedType n la) =
      MonoidAlgebra.single (QuotientGroup.mk (1 : G' n)) (1 : ℂ) := by
    rw [of_smul_single, rowSubgroup_fixes_identity n la p hp]
  exact congrArg Subtype.val
    (show (MonoidAlgebra.of ℂ _ p) • f (MonoidAlgebra.single (QuotientGroup.mk 1) 1) =
          f (MonoidAlgebra.single (QuotientGroup.mk 1) 1) by rw [← f.map_smul, h_fix])
end
set_option linter.style.longLine false in
/-- The complex finrank of linear maps from the partition-indexed type to the indicated membership subtype is one. -/
@[source_ref "Chapter5/Proposition5.14.1" (role := primary),
  source_ref "Chapter5/Discussion_proof_of_Proposition5.14.1" (role := primary)]
theorem finrank_linearMap_to_mem_eq_one
    (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (partitionIndexedType n la →ₗ[natIndexedType n]
      ↥(partitionSubmodule n la)) = 1 := by
  classical
  set φ := canonicalHom n la
  set e : partitionIndexedType n la := MonoidAlgebra.single (QuotientGroup.mk 1) 1
  have hφe_val := canonicalHom_apply_identity n la
  have hφe_ne : φ e ≠ 0 := by
    intro h
    have h_val := congrArg Subtype.val h
    simp only [Submodule.coe_zero] at h_val
    rw [hφe_val, canonicalHom_v] at h_val
    exact of_mul_rowSym_youngSymmetrizer_ne_zero n la _ h_val
  obtain ⟨c₀, hc₀⟩ := row_invariant_is_scalar_of_rowSym_youngSym n la
    (φ e : natIndexedType n) (φ e).prop (equivariant_map_row_invariant n la φ)
  have hc₀_ne : c₀ ≠ 0 := by
    intro h; rw [h, zero_smul] at hc₀; exact hφe_ne (Subtype.ext hc₀)
  apply finrank_eq_one (R := ℂ) (v := φ)
  · exact fun h => hφe_ne (by rw [h, LinearMap.zero_apply])
  · intro f
    obtain ⟨c₁, hc₁⟩ := row_invariant_is_scalar_of_rowSym_youngSym n la
      (f e : natIndexedType n) (f e).prop (equivariant_map_row_invariant n la f)
    have h_agree : f e = (c₁ / c₀) • φ e := by
      apply Subtype.ext
      change (f e : natIndexedType n) = (c₁ / c₀) • (φ e : natIndexedType n)
      rw [hc₁, hc₀, smul_smul, div_mul_cancel₀ c₁ hc₀_ne]
    refine ⟨c₁ / c₀, ?_⟩
    apply equivariant_map_ext_of_agree_on_e
    rw [h_agree, LinearMap.smul_apply]
end RepresentationTheory.PartitionLinearMapVanishing
