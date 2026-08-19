/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
import RepresentationTheory.SymmetricGroup.PartitionDominance
import RepresentationTheory.Partitions.SquareScalar
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary results for partition representations

This module develops auxiliary submodules and coefficient calculations associated with partitions.
-/

namespace RepresentationTheory.PartitionAuxiliary

/-- An auxiliary family of types indexed by natural numbers. -/
abbrev natIndexedType (n : ℕ) := MonoidAlgebra ℂ (Equiv.Perm (Fin n))

/-- Associates each partition with a submodule of the corresponding auxiliary type. -/
noncomputable def partitionSubmodule (n : ℕ) (la : Nat.Partition n) :
    Submodule (natIndexedType n) (natIndexedType n) :=
  Submodule.span (natIndexedType n)
    {RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la}

noncomputable section
open scoped Classical

private abbrev G' (n : ℕ) := Equiv.Perm (Fin n)
private abbrev A' (n : ℕ) := MonoidAlgebra ℂ (G' n)

/-- Provides the function coercion from a monoid algebra to its coefficient functions. -/
local instance MonoidAlgebra.coeFun {R G : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R G) (fun _ => G → R) :=
  ⟨fun a => a.coeff⟩

private lemma monoidAlgebra_fintype_sum_apply {ι R G : Type*} [Fintype ι] [Semiring R]
    (f : ι → MonoidAlgebra R G) (a : G) :
    (∑ i, f i) a = ∑ i, f i a := by
  classical
  simpa only [Finsupp.finsetSum_apply] using
    Finsupp.ext_iff.mp (MonoidAlgebra.coeff_sum Finset.univ f) a

/-- The natural-number cast of the cardinality of the auxiliary object is nonzero. -/
instance cardNatCast_neZero (n : ℕ) : NeZero (Nat.card (G' n) : ℂ) :=
  ⟨by exact_mod_cast Nat.card_pos.ne'⟩

private lemma sandwich_scalar (n : ℕ) (la : Nat.Partition n) :
    ∃ f : A' n →ₗ[ℂ] ℂ, ∀ x,
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la * x *
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la =
          f x • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
  obtain ⟨ℓ, hℓ⟩ :=
    RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.exists_sign_fixed_sandwich_eq_smul n la
  refine ⟨ℓ.comp ((LinearMap.mulLeft ℂ
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la)).comp
    (LinearMap.mulRight ℂ
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la))), fun x => ?_⟩
  change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la * x *
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la =
    ℓ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la *
      (x * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)) •
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC]
  have : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la *
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * x *
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la *
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) =
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la *
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * x *
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) *
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := by
    simp only [mul_assoc]
  rw [this, hℓ]; simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC,
    mul_assoc]

private lemma trace_lmul_monoidAlgebra
    {G : Type*} [Group G] [Fintype G]
    (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G) (Algebra.lmul ℂ _ a) =
      Fintype.card G • a 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    MonoidAlgebra.basis_apply]
  have : ∀ g : G, ((MonoidAlgebra.basis G ℂ).repr
    (Algebra.lmul ℂ (MonoidAlgebra ℂ G) a (MonoidAlgebra.single g 1))) g = a 1 := by
    intro g
    change (a * MonoidAlgebra.single g 1).coeff g = a.coeff 1
    exact (MonoidAlgebra.mul_single_apply a (1 : ℂ) g g).trans (by simp)
  simp only [this, Finset.sum_const, Finset.card_univ]

private lemma sortedParts_sum (n : ℕ) (la : Nat.Partition n) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = n := by
  have h := Multiset.sort_eq la.parts (· ≥ ·)
  have :
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la : Multiset ℕ).sum =
        la.parts.sum := congrArg Multiset.sum h
  rw [Multiset.sum_coe] at this
  rw [this, la.parts_sum]

/-- A permutation lying in both displayed auxiliary membership predicates is the identity. -/
@[source_ref "Chapter5/Definition5.12.1" (role := primary)]
theorem perm_eq_one_of_mem_of_mem (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n))
    (hrow : σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)
    (hcol : σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    σ = 1 := by
  ext k
  simp only [Equiv.Perm.one_apply]
  have hsum :
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = n :=
    sortedParts_sum n la
  have hk : k.val <
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by
    rw [hsum]; exact k.isLt
  have hσk : (σ k).val <
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by
    rw [hsum]; exact (σ k).isLt
  exact RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)
    (σ k).val k.val hσk hk (hrow k) (hcol k)

private lemma columnAntisymmetrizer_apply_mem (n : ℕ) (la : Nat.Partition n) (σ : G' n)
    (hσ : σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la : A' n) σ =
      ((↑(Equiv.Perm.sign σ) : ℤ) : ℂ) := by
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA,
    MonoidAlgebra.of_apply]
  rw [monoidAlgebra_fintype_sum_apply]
  simp only [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_eq_single
    (⟨σ, hσ⟩ : ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la))]
  · simp
  · intro q _ hq
    have : (q : G' n) ≠ σ := fun h => hq (Subtype.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma columnAntisymmetrizer_apply_not_mem (n : ℕ) (la : Nat.Partition n) (σ : G' n)
    (hσ : σ ∉ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la : A' n) σ =
      0 := by
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA,
    MonoidAlgebra.of_apply]
  rw [monoidAlgebra_fintype_sum_apply]
  simp only [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  apply Finset.sum_eq_zero
  intro q _
  have : (q : G' n) ≠ σ := fun h => hσ (h ▸ q.prop)
  simp [this]

/-- The coefficient at the identity element of the partition-indexed element equals one. -/
lemma coeff_one_eq_one (n : ℕ) (la : Nat.Partition n) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : A' n) 1 =
      1 := by
  change (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la *
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la : A' n) 1 = 1
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA,
    MonoidAlgebra.of_apply, Finset.sum_mul]
  rw [monoidAlgebra_fintype_sum_apply]
  simp only [Algebra.smul_mul_assoc]
  rw [Finset.sum_eq_single
    (⟨1, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).one_mem⟩ :
      ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la))]
  · simp only [Equiv.Perm.sign_one]
    simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB,
      MonoidAlgebra.of_apply]
    simp only [Units.val_one, Int.cast_one, one_smul, MonoidAlgebra.single_mul_apply,
      inv_one, mul_one, one_mul]
    rw [monoidAlgebra_fintype_sum_apply,
      Finset.sum_eq_single
        (⟨1, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).one_mem⟩ :
          ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la))]
    · simp
    · intro p _ hp
      have hp_ne : (p : G' n) ≠ 1 := fun h => hp (Subtype.ext h)
      simp [hp_ne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro q _ hq
    have hq_ne : (q : G' n) ≠ 1 := fun h => hq (Subtype.ext h)
    suffices h :
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la : A' n)
          (q : G' n)⁻¹ = 0 by
      simp [MonoidAlgebra.smul_apply, MonoidAlgebra.single_mul_apply, h]
    simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB,
      MonoidAlgebra.of_apply]
    rw [monoidAlgebra_fintype_sum_apply]
    apply Finset.sum_eq_zero; intro p _
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · exfalso; exact hq_ne (inv_eq_one.mp (perm_eq_one_of_mem_of_mem n la (q : G' n)⁻¹
        (h ▸ p.prop)
        ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).inv_mem q.prop)))
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The square of the partition-indexed element is nonzero. -/
lemma self_mul_ne_zero (n : ℕ) (la : Nat.Partition n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la *
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la ≠ 0 := by
  set c := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la
  intro h_sq_zero
  set L : A' n →ₗ[ℂ] A' n := LinearMap.mulLeft ℂ c
  have h_nilp : IsNilpotent L := by
    refine ⟨2, LinearMap.ext fun x => ?_⟩
    change L (L x) = 0
    simp only [L, LinearMap.mulLeft_apply, ← mul_assoc, h_sq_zero, zero_mul]
  have h_tr_nilp := LinearMap.isNilpotent_trace_of_isNilpotent h_nilp
  have h_tr_zero : LinearMap.trace ℂ (A' n) L = 0 :=
    isNilpotent_iff_eq_zero.mp h_tr_nilp
  have hL : L = Algebra.lmul ℂ (A' n) c := rfl
  rw [hL, trace_lmul_monoidAlgebra, coeff_one_eq_one] at h_tr_zero
  simp only [nsmul_eq_mul, mul_one] at h_tr_zero
  have : (Fintype.card (G' n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  exact this h_tr_zero

/-- The submodule associated with any partition is simple as a module. -/
@[source_ref "Chapter5/Introduction_5.12" (role := supporting),
  source_ref "Chapter5/Theorem5.12.2" (role := supporting),
  source_ref "Chapter5/Discussion_proof_of_Theorem5.12.2" (role := supporting)]
theorem partitionSubmodule_isSimpleModule
    (n : ℕ) (la : Nat.Partition n) :
    IsSimpleModule (natIndexedType n) (partitionSubmodule n la) := by
  rw [isSimpleModule_iff_isAtom]
  obtain ⟨α, hα_eq⟩ :=
    RepresentationTheory.Partitions.SquareScalar.exists_mul_self_eq_smul n la
  have hα_ne : α ≠ 0 := fun h => self_mul_ne_zero n la (by rw [hα_eq, h, zero_smul])
  obtain ⟨f, hf⟩ := sandwich_scalar n la
  set c :=
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la with hc_def
  refine ⟨?_, ?_⟩
  · intro h
    have hc_zero : (c : A' n) = 0 :=
      (Submodule.mem_bot (R := A' n)).mp (h ▸ Submodule.subset_span rfl)
    exact self_mul_ne_zero n la (show c * c = 0 by rw [hc_zero, mul_zero])
  · intro N hN
    by_contra hN_ne_bot
    have hN_le := le_of_lt hN
    suffices c ∈ N by
      exact ne_of_lt hN
        (le_antisymm hN_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr this)))
    obtain ⟨P, hP⟩ := (inferInstance : IsSemisimpleModule (A' n) (A' n)).exists_isCompl N
    obtain ⟨n₀, hn₀, p₀, hp₀, hc_eq⟩ := Submodule.mem_sup.mp
      (show c ∈ N ⊔ P from hP.sup_eq_top ▸ Submodule.mem_top)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (show n₀ ∈ partitionSubmodule n la from hN_le hn₀)
    have hcn₀ : c * n₀ = f a • c := by
      rw [← ha]; change c * (a * c) = _; rw [← mul_assoc]; exact hf a
    have hcn₀_N : c * n₀ ∈ N := N.smul_mem _ hn₀
    by_cases hfa : f a = 0
    · rw [hfa, zero_smul] at hcn₀
      have hcc_cp₀ : c * c = c * p₀ := by
        calc c * c = c * (n₀ + p₀) := by rw [hc_eq]
          _ = c * n₀ + c * p₀ := mul_add _ _ _
          _ = c * p₀ := by rw [hcn₀, zero_add]
      have hαc_P : α • c ∈ P := by rw [← hα_eq, hcc_cp₀]; exact P.smul_mem _ hp₀
      have h1 : α • n₀ ∈ N := Submodule.smul_of_tower_mem N α hn₀
      have h2 : α • n₀ ∈ P := by
        rw [show α • n₀ = α • c - α • p₀ from by rw [← hc_eq, smul_add, add_sub_cancel_right]]
        exact P.sub_mem hαc_P (Submodule.smul_of_tower_mem P α hp₀)
      have h3 : α • n₀ = 0 :=
        (Submodule.mem_bot (R := A' n)).mp
          (hP.inf_eq_bot ▸ Submodule.mem_inf.mpr ⟨h1, h2⟩)
      have hn₀_zero : n₀ = 0 := (smul_eq_zero.mp h3).resolve_left hα_ne
      exfalso; apply hN_ne_bot; rw [eq_bot_iff]; intro x hx
      have hc_P : c ∈ P := by rw [← hc_eq, hn₀_zero, zero_add]; exact hp₀
      have hV_le_P : partitionSubmodule n la ≤ P :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hc_P)
      exact (Submodule.mem_bot (R := A' n)).mpr
        ((Submodule.mem_bot (R := A' n)).mp
          (hP.inf_eq_bot ▸ Submodule.mem_inf.mpr ⟨hx, hV_le_P (hN_le hx)⟩))
    · rw [hcn₀] at hcn₀_N
      rw [show c = (f a)⁻¹ • (f a • c) from by rw [inv_smul_smul₀ hfa]]
      exact Submodule.smul_of_tower_mem N (f a)⁻¹ hcn₀_N

end

end RepresentationTheory.PartitionAuxiliary
