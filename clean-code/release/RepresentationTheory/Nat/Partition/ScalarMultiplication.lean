/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.AuxiliarySubmodules
import RepresentationTheory.Alignment.Attribute









namespace RepresentationTheory.Nat.Partition.ScalarMultiplication

private abbrev G (n : ℕ) := Equiv.Perm (Fin n)
private abbrev A (n : ℕ) := MonoidAlgebra ℂ (G n)

/-- Provides the coefficient-function coercion for a monoid algebra over a semiring. -/
local instance MonoidAlgebra.instCoeFun {R M : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R M) (fun _ => M → R) :=
  ⟨fun a => a.coeff⟩



private lemma trace_mulRight_monoidAlgebra
    {H : Type*} [Group H] [Fintype H] (x : MonoidAlgebra ℂ H) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ H) (LinearMap.mulRight ℂ x) =
      Fintype.card H * x 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis H ℂ)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  have hdiag : ∀ g : H,
      (MonoidAlgebra.basis H ℂ).repr
          (LinearMap.mulRight ℂ x ((MonoidAlgebra.basis H ℂ) g)) g = x 1 := by
    intro g
    change (MonoidAlgebra.single g 1 * x : MonoidAlgebra ℂ H) g = x 1
    rw [MonoidAlgebra.single_mul_apply]
    simp
  simp_rw [hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]



private lemma trace_mulRight_rowCol_eq_colRow (n : ℕ) (la : Nat.Partition n) :
    LinearMap.trace ℂ (A n)
        (LinearMap.mulRight ℂ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)) =
      LinearMap.trace ℂ (A n)
        (LinearMap.mulRight ℂ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la)) := by
  let Ra := LinearMap.mulRight ℂ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la)
  let Rb := LinearMap.mulRight ℂ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)
  have hab : LinearMap.mulRight ℂ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) =
      Rb.comp Ra := by
    ext x
    simp only [Ra, Rb, LinearMap.mulRight_apply, LinearMap.comp_apply, mul_assoc]
  have hba : LinearMap.mulRight ℂ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) =
      Ra.comp Rb := by
    ext x
    simp only [Ra, Rb, LinearMap.mulRight_apply, LinearMap.comp_apply, mul_assoc]
  rw [hab, hba]
  exact LinearMap.trace_comp_comm' Ra Rb



private lemma trace_mulRight_youngProjector (n : ℕ) (la : Nat.Partition n) :
    LinearMap.trace ℂ (A n) (LinearMap.mulRight ℂ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementD n la)) =
      (Nat.factorial n : ℂ) /
        ((Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) *
          (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ)) := by
  let t : ℂ := ((Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) *
    (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ))⁻¹
  have hc : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementD n la =
      t • (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) := by
    simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementD, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementF, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementE,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, t]
    congr 1
    rw [mul_inv]
    ring
  rw [hc]
  have hmap : LinearMap.mulRight ℂ
      (t • (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)) =
      t • LinearMap.mulRight ℂ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) := by
    apply LinearMap.ext
    intro x
    change x * (t • (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)) =
      t • (x * (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la))
    exact Algebra.mul_smul_comm t x _
  rw [hmap]
  rw [map_smul, trace_mulRight_rowCol_eq_colRow,
    trace_mulRight_monoidAlgebra, show
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la from rfl,
    RepresentationTheory.PartitionAuxiliary.coeff_one_eq_one, mul_one, Fintype.card_perm, Fintype.card_fin]
  simp only [smul_eq_mul, t, div_eq_mul_inv]
  ring




/-- For each natural number and partition, multiplying the indexed element by itself yields the scalar multiple specified in the statement. -/
@[source_ref "Chapter5/Introduction_5.13" (role := supporting),
  source_ref "Chapter5/Lemma5.13.3" (role := primary)]
theorem partitionIndexedElement_mul_self_eq_smul_self (n : ℕ) (la : Nat.Partition n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementD n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementD n la =
      ((Nat.factorial n : ℂ) /
        ((Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) *
          (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ) *
          (Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) : ℂ))) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementD n la := by
  obtain ⟨β, hβne, hβsq⟩ := RepresentationTheory.AuxiliarySubmodules.product_sq_eq_smul n la
  let t : ℂ := ((Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) *
    (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ))⁻¹
  let γ : ℂ := t * β
  let c : A n := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementD n la
  have hc : c = t • (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) := by
    simp only [c, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementD, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementF, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementE,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, t]
    congr 1
    rw [mul_inv]
    ring
  have htne : t ≠ 0 := by
    apply inv_ne_zero
    exact mul_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hγne : γ ≠ 0 := mul_ne_zero htne hβne
  have hcsq : c * c = γ • c := by
    let r : A n := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la
    calc
      c * c = (t • r) * (t • r) := by rw [hc]
      _ = (t * t) • (r * r) := by
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
      _ = (t * t) • (β • r) := by rw [hβsq]
      _ = (t * β) • (t • r) := by
        simp only [smul_smul]
        congr 1
        ring
      _ = γ • c := by rw [hc]
  let R : A n →ₗ[ℂ] A n := LinearMap.mulRight ℂ c
  let e : A n →ₗ[ℂ] A n := γ⁻¹ • R
  have hproj : LinearMap.IsProj ((RepresentationTheory.AuxiliarySubmodules.indexedSubmodule n la).restrictScalars ℂ) e := by
    apply LinearMap.IsProj.mk
    · intro x
      simp only [e, R, LinearMap.smul_apply, LinearMap.mulRight_apply]
      apply Submodule.smul_mem
      change x * c ∈ RepresentationTheory.AuxiliarySubmodules.indexedSubmodule n la
      exact (RepresentationTheory.AuxiliarySubmodules.indexedSubmodule n la).smul_mem x (Submodule.subset_span rfl)
    · intro x hx
      simp only [e, R, LinearMap.smul_apply, LinearMap.mulRight_apply]
      change x ∈ RepresentationTheory.AuxiliarySubmodules.indexedSubmodule n la at hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      dsimp [c] at hcsq ⊢
      rw [mul_assoc, hcsq, Algebra.mul_smul_comm, smul_smul,
        inv_mul_cancel₀ hγne, one_smul]
  have htrace := hproj.trace
  have hfin : Module.finrank ℂ ((RepresentationTheory.AuxiliarySubmodules.indexedSubmodule n la).restrictScalars ℂ) =
      Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) := by
    exact LinearEquiv.finrank_eq
      ((RepresentationTheory.AuxiliarySubmodules.auxiliarySubmoduleLinearEquivIndexedSubmodule n la).restrictScalars ℂ).symm
  have htraceR : LinearMap.trace ℂ (A n) R =
      (Nat.factorial n : ℂ) /
        ((Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) *
          (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ)) := by
    simpa only [R, c] using trace_mulRight_youngProjector n la
  have htraceE : LinearMap.trace ℂ (A n) e = γ⁻¹ *
      ((Nat.factorial n : ℂ) /
        ((Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) *
          (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ))) := by
    simp only [e, map_smul, htraceR, smul_eq_mul]
  rw [htraceE, hfin] at htrace
  have hcne : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la ≠ 0 := by
    intro h
    exact RepresentationTheory.PartitionAuxiliary.self_mul_ne_zero n la (by rw [h, mul_zero])
  haveI : Nontrivial (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) := by
    refine ⟨⟨⟨RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la, Submodule.subset_span rfl⟩, 0, ?_⟩⟩
    intro h
    apply hcne
    simpa using congrArg Subtype.val h
  have hdimne : (Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hγ : γ =
      ((Nat.factorial n : ℂ) /
        ((Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) *
          (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ))) /
          (Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) : ℂ) := by
    rw [inv_mul_eq_iff_eq_mul₀ hγne] at htrace
    rw [eq_div_iff hdimne]
    exact htrace.symm
  change c * c = _
  rw [hcsq, hγ]
  congr 1
  field_simp

end RepresentationTheory.Nat.Partition.ScalarMultiplication
