/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.SimpleModulesAndPartitionBounds

open MvPolynomial Finset

noncomputable section

namespace RepresentationTheory.SymmetricGroup.PartitionScalarAuxiliary

open RepresentationTheory.Auxiliary.MutualCentralizers
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich
open RepresentationTheory.PartitionMonoidAlgebra

/-- The coercion that evaluates an element of a monoid algebra at an index. -/
local instance monoidAlgebraCoeFun {R M : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R M) (fun _ => M → R) :=
  ⟨fun a => a.coeff⟩

variable {k : Type*} [Field k] [CharZero k]

private abbrev G (n : ℕ) := Equiv.Perm (Fin n)

/-! ### General-`k` Specht block action and character -/

/-- The linear endomorphism of the displayed subtype associated with a permutation. -/
def permutationSubtypeEndomorphism (k : Type*) [Field k] (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    ↥(partitionSubmodule k n la) →ₗ[k] ↥(partitionSubmodule k n la) where
  toFun := fun ⟨m, hm⟩ => ⟨MonoidAlgebra.of k _ σ * m,
    (partitionSubmodule k n la).smul_mem (MonoidAlgebra.of k _ σ) hm⟩
  map_add' := fun ⟨a, _⟩ ⟨b, _⟩ => Subtype.ext (mul_add _ a b)
  map_smul' := fun _ ⟨m, _⟩ => Subtype.ext (Algebra.mul_smul_comm _ _ m)

/-- The scalar associated with a partition and a permutation. -/
def partitionPermutationScalar (k : Type*) [Field k] (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : k :=
  LinearMap.trace k _ (permutationSubtypeEndomorphism k n la σ)

/-! ### Left multiplication by a group-algebra element on a Specht block -/

/-- Left multiplication by `c ∈ k[S_n]` on the Specht block `partitionSubmodule k n la`. -/
private def mulLeftBlockK (n : ℕ) (c : MonoidAlgebra k (G n)) (la : Nat.Partition n) :
    ↥(partitionSubmodule k n la) →ₗ[k] ↥(partitionSubmodule k n la) :=
  LinearMap.codRestrict ((partitionSubmodule k n la).restrictScalars k)
    ((LinearMap.mulLeft k c).comp ((partitionSubmodule k n la).restrictScalars k).subtype)
    (fun v => (partitionSubmodule k n la).smul_mem c v.prop)

omit [CharZero k] in
private lemma mulLeftBlockK_of (n : ℕ) (la : Nat.Partition n) (σ : G n) :
    mulLeftBlockK n (MonoidAlgebra.of k _ σ) la = permutationSubtypeEndomorphism k n la σ := by
  ext ⟨m, hm⟩; rfl

private def mulLeftBlockKLinear (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra k (G n) →ₗ[k]
      (↥(partitionSubmodule k n la) →ₗ[k] ↥(partitionSubmodule k n la)) where
  toFun c := mulLeftBlockK n c la
  map_add' a b := by
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    exact add_mul a b m
  map_smul' r c := by
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    exact smul_mul_assoc r c m

omit [CharZero k] in
/-- Trace linearity: `∑_σ c(σ) · χ_{V_la}(σ) = trace of left mult by c on V_la`. -/
private lemma sum_coeff_char_eq_traceK (n : ℕ) (la : Nat.Partition n)
    (c : MonoidAlgebra k (G n)) :
    ∑ σ : G n, c σ * partitionPermutationScalar k n la σ =
      LinearMap.trace k _ (mulLeftBlockK n c la) := by
  symm
  have key : (LinearMap.trace k _) (mulLeftBlockK n c la) =
      ∑ σ ∈ c.coeff.support, c σ * partitionPermutationScalar k n la σ := by
    have hlin : mulLeftBlockK n c la = (mulLeftBlockKLinear n la) c := rfl
    rw [hlin]
    simp_rw [partitionPermutationScalar, ← mulLeftBlockK_of n la]
    have hc : c = ∑ σ ∈ c.coeff.support, c σ • MonoidAlgebra.of k (G n) σ := by
      conv_lhs => rw [← MonoidAlgebra.sum_coeff_single c]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
    conv_lhs => rw [show (mulLeftBlockKLinear n la) c =
        (mulLeftBlockKLinear n la)
          (∑ σ ∈ c.coeff.support, c σ • MonoidAlgebra.of k _ σ) from by rw [← hc]]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [map_smul, LinearMap.map_smul, smul_eq_mul]; rfl
  rw [key]
  apply Finset.sum_subset (Finset.subset_univ c.coeff.support)
  intro σ _ hσ
  have : c σ = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hσ
  simp [this]

/-! ### Off-diagonal vanishing -/

set_option maxHeartbeats 1600000 in
-- Constructing and comparing the subtype-valued intertwiner is elaboration-intensive.
/-- Off-diagonal: `c_λ` acts as `0` on `V_{la'}` when `la ≠ la'`. Uses general-`k`
Specht-module simplicity and distinctness. -/
private lemma mulLeft_youngSym_zero_of_neK (n : ℕ) (la la' : Nat.Partition n)
    (hne : la ≠ la') :
    mulLeftBlockK n (partitionSymmetrizer k n la) la' = 0 := by
  by_contra hT
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : partitionSubmodule k n la',
      mulLeftBlockK n (partitionSymmetrizer k n la) la' w₀ ≠ 0 := by
    by_contra hall; push Not at hall; exact hT (LinearMap.ext hall)
  set φ : partitionSubmodule k n la →ₗ[MonoidAlgebra k (G n)] partitionSubmodule k n la' :=
    { toFun := fun v => ⟨(v : MonoidAlgebra k (G n)) * (w₀ : MonoidAlgebra k (G n)),
        (partitionSubmodule k n la').smul_mem (v : MonoidAlgebra k (G n)) w₀.prop⟩
      map_add' := fun a b => Subtype.ext (add_mul (a : MonoidAlgebra k (G n)) b w₀)
      map_smul' := fun a v => Subtype.ext (mul_assoc a (v : MonoidAlgebra k (G n)) w₀) }
  have hφ_ne : φ ≠ 0 := by
    intro h
    apply hw₀
    let e : partitionSubmodule k n la :=
      ⟨partitionSymmetrizer k n la, Submodule.subset_span rfl⟩
    have he := LinearMap.congr_fun h e
    apply Subtype.ext
    change partitionSymmetrizer k n la * (w₀ : MonoidAlgebra k (G n)) = 0
    have hev := congrArg Subtype.val he
    change partitionSymmetrizer k n la * (w₀ : MonoidAlgebra k (G n)) = 0 at hev
    exact hev
  haveI : IsSimpleModule (MonoidAlgebra k (G n)) (partitionSubmodule k n la) :=
    isSimpleModule_partitionSubmodule k n la
  haveI : IsSimpleModule (MonoidAlgebra k (G n)) (partitionSubmodule k n la') :=
    isSimpleModule_partitionSubmodule k n la'
  have hφ_bij := LinearMap.bijective_of_ne_zero hφ_ne
  exact (isEmpty_linearEquiv_between_subtypes_of_ne k n la la' hne).false
    (LinearEquiv.ofBijective φ hφ_bij)

/-! ### Diagonal value -/

omit [CharZero k] in
/-- Identity coefficient of `c_λ` is `1`. -/
private lemma youngSymK_coeff_one (n : ℕ) (la : Nat.Partition n) :
    (partitionSymmetrizer k n la : MonoidAlgebra k (G n)) 1 = 1 := by
  rw [partitionSymmetrizer_eq_map_int]
  simp [MonoidAlgebra.coeff_mapRingHom, integralPartitionSymmetrizer_coeff_one]

omit [CharZero k] in
/-- Sandwich proportionality: `c * v = ((c * v)(1)) • c` for `v ∈ V_λ`. -/
private lemma mul_mem_specht_proportionalK (n : ℕ) (la : Nat.Partition n)
    (v : ↥(partitionSubmodule k n la)) :
    partitionSymmetrizer k n la * v.val =
      (partitionSymmetrizer k n la * v.val) 1 • partitionSymmetrizer k n la := by
  classical
  set c := partitionSymmetrizer k n la with hc
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp v.prop
  rw [smul_eq_mul] at ha
  obtain ⟨f, hf⟩ := exists_sandwich_eq_smul k n la
  -- `c * v = c * (a * c) = c * a * c = f a • c`.
  have hcv : c * v.val = f a • c := by
    rw [← ha, ← mul_assoc, hf a]
  rw [hcv]
  congr 1
  rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, youngSymK_coeff_one, mul_one]

omit [CharZero k] in
/-- Diagonal case: trace of `c_λ` on `V_λ` equals `α`. -/
private lemma trace_mulLeft_youngSym_eqK (n : ℕ) (la : Nat.Partition n)
    (α : k)
    (hα_sq : partitionSymmetrizer k n la * partitionSymmetrizer k n la =
      α • partitionSymmetrizer k n la) :
    LinearMap.trace k _ (mulLeftBlockK n (partitionSymmetrizer k n la) la) = α := by
  set c := partitionSymmetrizer k n la with hc_def
  set V := partitionSubmodule k n la
  set T := mulLeftBlockK n c la
  have hc_mem : c ∈ V := Submodule.subset_span rfl
  set e : V := ⟨c, hc_mem⟩
  let ι : k →ₗ[k] V := LinearMap.lsmul k V |>.flip e
  let π : V →ₗ[k] k :=
    { toFun := fun v => (c * v.val) 1
      map_add' := fun x y => by simp [mul_add]
      map_smul' := fun r x => by
        change (c * (r • x.val)) 1 = r * (c * x.val) 1
        rw [Algebra.mul_smul_comm, MonoidAlgebra.coeff_smul_apply, smul_eq_mul] }
  have hT_eq : T = ι.comp π := by
    apply LinearMap.ext; intro ⟨v, hv⟩; apply Subtype.ext
    exact mul_mem_specht_proportionalK n la ⟨v, hv⟩
  rw [hT_eq, LinearMap.trace_comp_comm']
  have h_comp : π.comp ι = α • LinearMap.id := by
    apply LinearMap.ext; intro x
    change (c * (x • c)) 1 = α * x
    rw [Algebra.mul_smul_comm, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    rw [hα_sq, MonoidAlgebra.coeff_smul_apply, smul_eq_mul,
      youngSymK_coeff_one, mul_one, mul_comm]
  rw [h_comp]; simp [map_smul, LinearMap.trace_id, Module.finrank_self]

/-! ### Character-orthogonality (Kronecker) identity over `k` -/

/-- Under the displayed product relation, the weighted sum is the scalar when the partitions
agree and zero otherwise. -/
theorem weighted_partitionScalar_sum_eq_ite (n : ℕ) (la la' : Nat.Partition n)
    (α : k)
    (hα_sq : partitionSymmetrizer k n la * partitionSymmetrizer k n la =
      α • partitionSymmetrizer k n la) :
    ∑ σ : G n, (partitionSymmetrizer k n la σ) * partitionPermutationScalar k n la' σ =
      if la = la' then α else 0 := by
  rw [sum_coeff_char_eq_traceK]
  split_ifs with h
  · subst h; exact trace_mulLeft_youngSym_eqK n la α hα_sq
  · rw [mulLeft_youngSym_zero_of_neK n la la' h, map_zero]

/-! ### A trace-zero idempotent over a characteristic-zero field is zero -/

/-- An idempotent endomorphism of a finite-dimensional vector space over a
characteristic-zero field with vanishing trace is the zero map. -/
private theorem isIdempotentElem_eq_zero_of_trace_eq_zero
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {e : V →ₗ[k] V} (he : IsIdempotentElem e)
    (htr : LinearMap.trace k V e = 0) :
    e = 0 := by
  have hproj : LinearMap.IsProj (LinearMap.range e) e :=
    LinearMap.IsIdempotentElem.isProj_range _ he
  have htr_eq : LinearMap.trace k V e = (Module.finrank k (LinearMap.range e) : k) :=
    hproj.trace
  rw [htr] at htr_eq
  have hfinrank_zero : Module.finrank k (LinearMap.range e) = 0 := by
    have h : ((Module.finrank k (LinearMap.range e) : ℕ) : k) = 0 := htr_eq.symm
    exact_mod_cast h
  rw [← LinearMap.range_eq_bot, ← Submodule.finrank_eq_zero]
  exact hfinrank_zero

/-! ### The two special-block endomorphism lemmas over `k` -/

set_option maxHeartbeats 800000 in
-- The `Module k ↥(S.restrictScalars k)` instance and `LinearMap.restrict`
-- reduction traverse the deep `Subalgebra → Subsemiring → Module → IsScalarTower`
-- synthesis chain for `permutationActionAlgebra`, which exceeds the default budgets.
set_option synthInstance.maxHeartbeats 400000 in
/-- Under the stated trace identities, the restricted operator vanishes for a partition distinct
from the specified one. -/
theorem restriction_eq_zero_of_partition_ne
    (N : ℕ) (lam : Fin N → ℕ)
    (S : Submodule (permutationActionAlgebra k (Fin N → k) (∑ i, lam i))
      (auxiliarySpace k (Fin N → k) (∑ i, lam i)))
    [Module.Finite k ↥(S.restrictScalars k)]
    (la' : Nat.Partition (∑ i, lam i))
    (h_label : ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace k ↥(S.restrictScalars k)
            ((auxiliarySpacePermutationEquiv k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
              (p := S.restrictScalars k) (q := S.restrictScalars k)
              (fun _ hv =>
                mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
          partitionPermutationScalar k (∑ i, lam i) la' σ)
    (h_ne : la' ≠ partitionOfTuple N lam) :
    (symmetrizerEndomorphism k N lam).restrict
        (p := S.restrictScalars k) (q := S.restrictScalars k)
        (fun _ hv =>
          S.smul_mem (symmetrizerEndomorphismMem k N lam) hv) = 0 := by
  let f : ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k) :=
    (symmetrizerEndomorphism k N lam).restrict
      (p := S.restrictScalars k) (q := S.restrictScalars k)
      (fun _ hv => S.smul_mem (symmetrizerEndomorphismMem k N lam) hv)
  change f = 0
  obtain ⟨α, hα_sq⟩ :=
    partitionSymmetrizer_sq_smul k (∑ i, lam i) (partitionOfTuple N lam)
  have hα_ne : α ≠ 0 :=
    ne_zero_of_self_mul_eq_smul k (∑ i, lam i) (partitionOfTuple N lam) α hα_sq
  have h_trace_f : LinearMap.trace k _ f =
      ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) σ) *
        LinearMap.trace k _
          ((auxiliarySpacePermutationEquiv k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
            (p := S.restrictScalars k) (q := S.restrictScalars k)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S σ hv)) :=
    Auxiliary.trace_symmetrizerEndomorphism_restrict N lam S
  have h_trace_zero : LinearMap.trace k _ f = 0 := by
    rw [h_trace_f]
    conv_lhs => arg 2; ext σ; rw [h_label σ]
    rw [weighted_partitionScalar_sum_eq_ite (∑ i, lam i) (partitionOfTuple N lam) la' α hα_sq,
        if_neg (fun h => h_ne h.symm)]
  have hf_sq : f * f = α • f :=
    Auxiliary.restrict_symmetrizerEndomorphism_sq N lam S α hα_sq
  let g : ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k) := α⁻¹ • f
  have hg_idem : IsIdempotentElem g := by
    change (α⁻¹ • f) * (α⁻¹ • f) = α⁻¹ • f
    rw [smul_mul_smul_comm, hf_sq, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]
  have hg_tr_zero : LinearMap.trace k _ g = 0 := by
    change LinearMap.trace k _ (α⁻¹ • f) = 0
    rw [LinearMap.map_smul, h_trace_zero, smul_zero]
  have hg_zero : g = 0 :=
    isIdempotentElem_eq_zero_of_trace_eq_zero
      (k := k) (V := ↥(S.restrictScalars k)) (e := g) hg_idem hg_tr_zero
  have hf_eq_smul_g : f = α • g := by
    change f = α • (α⁻¹ • f)
    rw [smul_smul, mul_inv_cancel₀ hα_ne, one_smul]
  rw [hf_eq_smul_g, hg_zero, smul_zero]

set_option maxHeartbeats 800000 in
-- The `Module k ↥(S.restrictScalars k)` instance and `LinearMap.restrict`
-- reduction traverse the deep `Subalgebra → Subsemiring → Module → IsScalarTower`
-- synthesis chain for `permutationActionAlgebra`, which exceeds the default budgets.
set_option synthInstance.maxHeartbeats 400000 in
/-- Under the stated trace identities, the restricted operator is a nonzero scalar multiple of an
idempotent with one-dimensional range. -/
theorem exists_rankOneIdempotent_smul_eq_restriction
    (N : ℕ) (lam : Fin N → ℕ)
    (S : Submodule (permutationActionAlgebra k (Fin N → k) (∑ i, lam i))
      (auxiliarySpace k (Fin N → k) (∑ i, lam i)))
    [Module.Finite k ↥(S.restrictScalars k)]
    (h_label : ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace k ↥(S.restrictScalars k)
            ((auxiliarySpacePermutationEquiv k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
              (p := S.restrictScalars k) (q := S.restrictScalars k)
              (fun _ hv =>
                mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
          partitionPermutationScalar k (∑ i, lam i) (partitionOfTuple N lam) σ) :
    ∃ (α : k) (π : ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k)),
      α ≠ 0 ∧ π * π = π ∧
      Module.finrank k (LinearMap.range π) = 1 ∧
      (symmetrizerEndomorphism k N lam).restrict
          (p := S.restrictScalars k) (q := S.restrictScalars k)
          (fun _ hv =>
            S.smul_mem (symmetrizerEndomorphismMem k N lam) hv) = α • π := by
  let f : ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k) :=
    (symmetrizerEndomorphism k N lam).restrict
      (p := S.restrictScalars k) (q := S.restrictScalars k)
      (fun _ hv => S.smul_mem (symmetrizerEndomorphismMem k N lam) hv)
  obtain ⟨α, hα_sq⟩ :=
    partitionSymmetrizer_sq_smul k (∑ i, lam i) (partitionOfTuple N lam)
  have hα_ne : α ≠ 0 :=
    ne_zero_of_self_mul_eq_smul k (∑ i, lam i) (partitionOfTuple N lam) α hα_sq
  have h_trace_f : LinearMap.trace k _ f =
      ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) σ) *
        LinearMap.trace k _
          ((auxiliarySpacePermutationEquiv k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
            (p := S.restrictScalars k) (q := S.restrictScalars k)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S σ hv)) :=
    Auxiliary.trace_symmetrizerEndomorphism_restrict N lam S
  have h_trace_eq_alpha : LinearMap.trace k _ f = α := by
    rw [h_trace_f]
    conv_lhs => arg 2; ext σ; rw [h_label σ]
    rw [weighted_partitionScalar_sum_eq_ite (∑ i, lam i) (partitionOfTuple N lam)
        (partitionOfTuple N lam) α hα_sq, if_pos rfl]
  have hf_sq : f * f = α • f :=
    Auxiliary.restrict_symmetrizerEndomorphism_sq N lam S α hα_sq
  set π : ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k) := α⁻¹ • f with hπ_def
  have hπ_idem : π * π = π := by
    rw [hπ_def, smul_mul_smul_comm, hf_sq, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]
  have hπ_proj : LinearMap.IsProj (LinearMap.range π) π :=
    { map_mem := fun x => LinearMap.mem_range_self π x
      map_id := fun x hx => by
        obtain ⟨y, rfl⟩ := hx
        exact LinearMap.congr_fun hπ_idem y }
  have hπ_trace : LinearMap.trace k _ π = 1 := by
    rw [hπ_def, LinearMap.map_smul, h_trace_eq_alpha, smul_eq_mul, inv_mul_cancel₀ hα_ne]
  letI : AddCommGroup (LinearMap.range π) :=
    { Module.addCommMonoidToAddCommGroup k with
      toAddCommMonoid := (LinearMap.range π).addCommMonoid }
  letI : AddCommGroup π.ker :=
    { Module.addCommMonoidToAddCommGroup k with
      toAddCommMonoid := π.ker.addCommMonoid }
  letI : Module.Free k (LinearMap.range π) := Module.Free.of_divisionRing k _
  letI : Module.Free k π.ker := Module.Free.of_divisionRing k _
  have hπ_rank : Module.finrank k (LinearMap.range π) = 1 := by
    have h := @LinearMap.IsProj.trace k inferInstance
      (↥(S.restrictScalars k)) (S.restrictScalars k).addCommGroup
      (S.restrictScalars k).module (LinearMap.range π) π hπ_proj
      inferInstance inferInstance inferInstance inferInstance
    rw [hπ_trace] at h
    exact_mod_cast h.symm
  have hf_eq : f = α • π := by
    rw [hπ_def, smul_smul, mul_inv_cancel₀ hα_ne, one_smul]
  exact ⟨α, π, hα_ne, hπ_idem, hπ_rank, hf_eq⟩

end RepresentationTheory.SymmetricGroup.PartitionScalarAuxiliary

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.SymmetricGroup.PartitionScalarAuxiliary.Auxiliary.statement024682 := _root_.RepresentationTheory.SymmetricGroup.PartitionScalarAuxiliary.exists_rankOneIdempotent_smul_eq_restriction

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.SymmetricGroup.PartitionScalarAuxiliary.Auxiliary.statement024684 := _root_.RepresentationTheory.SymmetricGroup.PartitionScalarAuxiliary.restriction_eq_zero_of_partition_ne
