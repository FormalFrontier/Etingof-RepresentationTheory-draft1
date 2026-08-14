/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich

noncomputable section

namespace RepresentationTheory.Algebra.PartitionPermutation

open MonoidAlgebra
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich
open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
open
  RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter

/-- The coercion from a monoid algebra to functions from its indexing type to its coefficient
type. -/
local instance MonoidAlgebra.coeFun {R M : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R M) (fun _ => M → R) :=
  ⟨fun a => a.coeff⟩

variable (k : Type*) [Field k] [CharZero k]

/-- Associates a permutation with a linear endomorphism of the subtype determined by a partition. -/
noncomputable def partitionSubtypeLinearEndomorphismOfPerm (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    ↥(partitionSubmodule k n la) →ₗ[k] ↥(partitionSubmodule k n la) where
  toFun := fun m => ⟨MonoidAlgebra.of k _ σ * m.1,
    (partitionSubmodule k n la).smul_mem (MonoidAlgebra.of k _ σ) m.2⟩
  map_add' := fun a b => Subtype.ext (mul_add _ a.1 b.1)
  map_smul' := fun r a => Subtype.ext (Algebra.mul_smul_comm r _ a.1)

/-- Returns a field element from a partition and a permutation of its finite index type. -/
noncomputable def partitionPermutationValue (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : k :=
  LinearMap.trace k _ (partitionSubtypeLinearEndomorphismOfPerm k n la σ)

omit [CharZero k] in
/-- The coefficient of the partition symmetrizer at the identity is `1`. -/
private lemma youngSymmetrizerK_apply_one (n : ℕ) (la : Nat.Partition n) :
    (partitionSymmetrizer k n la) 1 = 1 := by
  rw [partitionSymmetrizer_eq_map_int k n la, MonoidAlgebra.coeff_mapRingHom,
    integralPartitionSymmetrizer_coeff_one, map_one]

omit [CharZero k] in
/-- Trace of `x ↦ (of σ) · x · b` on `k[S_n]`, computed in the standard basis:
`trace = ∑_τ b(τ⁻¹ σ⁻¹ τ)`. -/
private lemma trace_mulLeft_of_comp_mulRight (n : ℕ) (σ : Equiv.Perm (Fin n))
    (b : MonoidAlgebra k (Equiv.Perm (Fin n))) :
    LinearMap.trace k _
        (LinearMap.mulLeft k (MonoidAlgebra.of k _ σ) ∘ₗ LinearMap.mulRight k b)
      = ∑ τ : Equiv.Perm (Fin n), b (τ⁻¹ * σ⁻¹ * τ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis (Equiv.Perm (Fin n)) k)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [LinearMap.comp_apply, MonoidAlgebra.basis_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply]
  have hrepr : ∀ (x : MonoidAlgebra k (Equiv.Perm (Fin n))) (g : Equiv.Perm (Fin n)),
      (MonoidAlgebra.basis (Equiv.Perm (Fin n)) k).repr x g = x g := fun _ _ => rfl
  rw [hrepr, MonoidAlgebra.of_apply, ← mul_assoc, MonoidAlgebra.single_mul_single, mul_one,
    MonoidAlgebra.coeff_single_mul_apply, one_mul, mul_inv_rev, mul_assoc]

/-- **Field-independence of the partition value.** Writing the partition symmetrizer over `ℤ`,
the value equals `(N₀ : k)⁻¹ * (M₀ : k)` for two fixed integers independent of `k`. -/
private lemma spechtModuleCharacterK_eq_intCast (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    partitionPermutationValue k n la σ
      = (((integralPartitionSymmetrizer n la * integralPartitionSymmetrizer n la) 1 : ℤ) : k)⁻¹
        * ((∑ τ : Equiv.Perm (Fin n),
          (integralPartitionSymmetrizer n la) (τ⁻¹ * σ⁻¹ * τ) : ℤ) : k) := by
  classical
  set c := partitionSymmetrizer k n la with hc
  obtain ⟨α, hα⟩ := partitionSymmetrizer_sq_smul k n la
  have hα_ne : α ≠ 0 := ne_zero_of_self_mul_eq_smul k n la α hα
  -- Fixed-point property: every element of the partition submodule is fixed by right
  -- multiplication by the idempotent.
  have hfix : ∀ s ∈ partitionSubmodule k n la, s * (α⁻¹ • c) = s := by
    intro s hs
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
    rw [smul_eq_mul, mul_smul_comm, mul_assoc, hα, mul_smul_comm, smul_smul,
      inv_mul_cancel₀ hα_ne, one_smul]
  -- The composite `of σ · - · (α⁻¹ • c)` lands in the partition submodule.
  set F := LinearMap.mulLeft k (MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ)
      ∘ₗ LinearMap.mulRight k (α⁻¹ • c) with hFdef
  have hmem : ∀ x, F x ∈ (partitionSubmodule k n la).restrictScalars k := by
    intro x
    rw [Submodule.restrictScalars_mem, hFdef, LinearMap.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply]
    have h1 : x * (α⁻¹ • c) ∈ partitionSubmodule k n la := by
      rw [mul_smul_comm]
      exact Submodule.smul_of_tower_mem _ α⁻¹
        (Submodule.smul_mem _ x (Submodule.subset_span rfl))
    exact Submodule.smul_mem _ (MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ) h1
  -- Rewrite the value as the trace of `F` on the whole group algebra.
  have hchar : partitionPermutationValue k n la σ = LinearMap.trace k _ F := by
    rw [partitionPermutationValue,
      show partitionSubtypeLinearEndomorphismOfPerm k n la σ
          = F.restrict (fun x (_ : x ∈ (partitionSubmodule k n la).restrictScalars k) => hmem x)
        from ?_]
    · exact LinearMap.trace_restrict_eq_of_forall_mem _ F hmem
    · apply LinearMap.ext
      intro s
      apply Subtype.ext
      change MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ * s.1 = F s.1
      rw [hFdef, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
        hfix s.1 s.2]
  -- Pull the scalar `α⁻¹` out of the trace and apply the trace formula.
  rw [hchar, hFdef]
  have hsmul : (LinearMap.mulLeft k (MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ) ∘ₗ
        LinearMap.mulRight k (α⁻¹ • c))
      = α⁻¹ • (LinearMap.mulLeft k (MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ)
        ∘ₗ LinearMap.mulRight k c) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
      LinearMap.smul_apply]
    rw [mul_smul_comm, mul_smul_comm]
  rw [hsmul, map_smul, trace_mulLeft_of_comp_mulRight, smul_eq_mul]
  -- Now identify `α⁻¹` and the sum with the integer expressions.
  have hα_int : α =
      (((integralPartitionSymmetrizer n la * integralPartitionSymmetrizer n la) 1 : ℤ) : k) := by
    have hcc : c * c =
        (MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom k))
          (integralPartitionSymmetrizer n la * integralPartitionSymmetrizer n la) := by
      rw [hc, partitionSymmetrizer_eq_map_int k n la, ← map_mul]
    have hval : (c * c) 1 = (((integralPartitionSymmetrizer n la *
        integralPartitionSymmetrizer n la) 1 : ℤ) : k) := by
      rw [hcc, MonoidAlgebra.coeff_mapRingHom]; rfl
    have : (c * c) 1 = α := by
      rw [hα, MonoidAlgebra.coeff_smul_apply, smul_eq_mul,
        youngSymmetrizerK_apply_one k n la, mul_one]
    rw [← this, hval]
  have hsum : (∑ τ : Equiv.Perm (Fin n), c (τ⁻¹ * σ⁻¹ * τ)) =
      ((∑ τ : Equiv.Perm (Fin n),
        (integralPartitionSymmetrizer n la) (τ⁻¹ * σ⁻¹ * τ) : ℤ) : k) := by
    push_cast
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [hc, partitionSymmetrizer_eq_map_int k n la, MonoidAlgebra.coeff_mapRingHom]
    rfl
  rw [hα_int, hsum]

/-- Over a characteristic-zero field, this value is the image of its rational instance. -/
lemma partitionPermutationValue_eq_algebraMap_rat (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    partitionPermutationValue k n la σ =
      algebraMap ℚ k (partitionPermutationValue ℚ n la σ) := by
  rw [spechtModuleCharacterK_eq_intCast k n la σ,
    spechtModuleCharacterK_eq_intCast ℚ n la σ, map_mul, map_inv₀, map_intCast, map_intCast]

/-- The complex-valued instance agrees with the other complex-valued expression on the same
inputs. -/
lemma partitionPermutationValue_complex_eq (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    partitionPermutationValue ℂ n la σ = auxiliaryPartitionPermutationValue n la σ := by
  have hys : partitionSymmetrizer ℂ n la = auxiliaryPartitionGroupAlgebraElementC n la := by
    rw [partitionSymmetrizer_eq_map_int ℂ n la, complexPartitionSymmetrizer_eq_map_int n la]
  have hmod : partitionSubmodule ℂ n la =
      RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la := by
    unfold RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule
      RepresentationTheory.PartitionAuxiliary.partitionSubmodule
    rw [hys]
  let e : ↥(partitionSubmodule ℂ n la) ≃ₗ[ℂ]
      ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) :=
    (LinearEquiv.ofEq _ _ hmod).restrictScalars ℂ
  have hint : auxiliarySubtypePermutationEndomorphism n la σ =
      e.conj (partitionSubtypeLinearEndomorphismOfPerm ℂ n la σ) := by
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply_apply]
    apply Subtype.ext
    rfl
  rw [partitionPermutationValue, auxiliaryPartitionPermutationValue, hint, LinearMap.trace_conj']

/-- In characteristic zero, a partition is determined by its values on all permutations. -/
theorem partitionPermutationValue_injective (n : ℕ) {μ ν : Nat.Partition n}
    (h : ∀ σ, partitionPermutationValue k n μ σ = partitionPermutationValue k n ν σ) :
    μ = ν := by
  apply eq_of_auxiliaryPartitionPermutationValue_eq n
  intro σ
  have hq : partitionPermutationValue ℚ n μ σ = partitionPermutationValue ℚ n ν σ := by
    have hkσ := h σ
    rw [partitionPermutationValue_eq_algebraMap_rat k n μ σ,
      partitionPermutationValue_eq_algebraMap_rat k n ν σ] at hkσ
    exact (algebraMap ℚ k).injective hkσ
  rw [← partitionPermutationValue_complex_eq n μ σ,
    ← partitionPermutationValue_complex_eq n ν σ,
    partitionPermutationValue_eq_algebraMap_rat ℂ n μ σ,
    partitionPermutationValue_eq_algebraMap_rat ℂ n ν σ, hq]

end RepresentationTheory.Algebra.PartitionPermutation

end
