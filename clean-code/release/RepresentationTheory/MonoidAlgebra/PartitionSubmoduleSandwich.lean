/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.PartitionAuxiliary

set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.cdot false

noncomputable section

namespace RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich

/-- A monoid-algebra element coerces to its coefficient function on the indexing type. -/
local instance monoidAlgebraCoeFun {R M : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R M) (fun _ => M → R) :=
  ⟨fun a => a.coeff⟩

private abbrev G' (n : ℕ) := Equiv.Perm (Fin n)
private abbrev AQ (n : ℕ) := MonoidAlgebra ℚ (G' n)

/-- A submodule of the permutation-group algebra associated with a partition. -/
def partitionSubmodule (k : Type*) [CommRing k] (n : ℕ) (la : Nat.Partition n) :
    Submodule (MonoidAlgebra k (Equiv.Perm (Fin n))) (MonoidAlgebra k (Equiv.Perm (Fin n))) :=
  Submodule.span _ {RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la}

private lemma mapRingHom_int_complex_injective (n : ℕ) :
    Function.Injective (MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n))
      (Int.castRingHom ℂ)) := by
  intro x y h
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  have hg := congrArg (fun z => z.coeff g) h
  simpa only [MonoidAlgebra.coeff_mapRingHom] using Int.cast_injective hg

/-- Sandwiching a permutation basis element equals its identity coefficient times the designated partition-indexed element. -/
theorem sandwich_perm_eq_coeff_one_smul (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer n la * MonoidAlgebra.of ℤ _ σ * RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer n la =
      (RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer n la * MonoidAlgebra.of ℤ _ σ * RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer n la) 1 •
        RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer n la := by
  set φ := MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℂ)
  set cZ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer n la
  set y := cZ * MonoidAlgebra.of ℤ _ σ * cZ

  have hφ_inj := mapRingHom_int_complex_injective n

  have hφc : φ cZ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la :=
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.complexPartitionSymmetrizer_eq_map_int n la).symm
  have hφσ : φ (MonoidAlgebra.of ℤ _ σ) = MonoidAlgebra.of ℂ _ σ := by
    change MonoidAlgebra.mapRingHom _ _ (MonoidAlgebra.single σ 1) =
      MonoidAlgebra.single σ 1
    rw [MonoidAlgebra.mapRingHom_single, map_one]

  obtain ⟨ℓ, hℓ⟩ := RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.exists_sign_fixed_sandwich_eq_smul n la

  have h_sandwich : ∀ x,
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la * x * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la =
        ℓ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * (x * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)) •
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
    intro x
    change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * x *
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) = _
    rw [show RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * x *
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) =
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * (x * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)) *
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la from by simp only [mul_assoc]]
    rw [hℓ]

  set f_val := ℓ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la *
    (MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la))
  have h_ℂ : φ y = f_val • φ cZ := by
    change φ (cZ * MonoidAlgebra.of ℤ _ σ * cZ) = _ • φ cZ
    rw [map_mul, map_mul, hφc, hφσ]
    exact h_sandwich (MonoidAlgebra.of ℂ _ σ)

  have hcZ1 : cZ 1 = 1 := RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer_coeff_one n la

  have hf_eq : f_val = ((y 1 : ℤ) : ℂ) := by

    have h1 : (f_val • φ cZ) (1 : Equiv.Perm (Fin n)) = f_val := by
      rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
      change f_val * ((cZ 1 : ℤ) : ℂ) = f_val
      rw [hcZ1, Int.cast_one, mul_one]
    have h2 : (φ y) (1 : Equiv.Perm (Fin n)) = ((y 1 : ℤ) : ℂ) := by
      rw [MonoidAlgebra.coe_mapRingHom]; rfl
    calc f_val = (f_val • φ cZ) 1 := h1.symm
      _ = (φ y) 1 := by rw [h_ℂ]
      _ = ((y 1 : ℤ) : ℂ) := h2

  apply hφ_inj
  rw [h_ℂ, hf_eq, map_zsmul, Int.cast_smul_eq_zsmul ℂ]

/-- Over the designated rational algebra, every sandwich by the partition-indexed element is a scalar multiple of that element. -/
theorem exists_sandwich_eq_smul_rat (n : ℕ) (la : Nat.Partition n) :
    ∃ f : AQ n →ₗ[ℚ] ℚ, ∀ x,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer ℚ n la * x * RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer ℚ n la =
        f x • RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer ℚ n la := by
  set ψ := MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℚ)
  set cZ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer n la
  set cQ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer ℚ n la
  have hψc : ψ cZ = cQ := (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer_eq_map_int ℚ n la).symm

  have basis_prop : ∀ σ : Equiv.Perm (Fin n), ∃ β : ℤ,
      cQ * MonoidAlgebra.of ℚ _ σ * cQ = (β : ℚ) • cQ := by
    intro σ
    set β := (cZ * MonoidAlgebra.of ℤ _ σ * cZ) 1
    refine ⟨β, ?_⟩
    have hψσ : ψ (MonoidAlgebra.of ℤ _ σ) = MonoidAlgebra.of ℚ _ σ := by
      change MonoidAlgebra.mapRingHom _ _ (MonoidAlgebra.single σ 1) =
        MonoidAlgebra.single σ 1
      rw [MonoidAlgebra.mapRingHom_single, map_one]
    have hZ := sandwich_perm_eq_coeff_one_smul n la σ
    calc cQ * MonoidAlgebra.of ℚ _ σ * cQ
        = ψ cZ * ψ (MonoidAlgebra.of ℤ _ σ) * ψ cZ := by rw [hψc, hψσ]
      _ = ψ (cZ * MonoidAlgebra.of ℤ _ σ * cZ) := by rw [map_mul, map_mul]
      _ = ψ (β • cZ) := by rw [hZ]
      _ = (β : ℚ) • cQ := by
          rw [map_zsmul, hψc]; rfl

  choose β hβ using basis_prop
  let f : AQ n →ₗ[ℚ] ℚ :=
    (Finsupp.lsum ℚ (fun σ => (β σ : ℚ) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ))) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap
  refine ⟨f, fun x => ?_⟩
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [mul_add, add_mul, map_add, add_smul]
    exact congr_arg₂ (· + ·) hx hy
  | single σ r =>
    have hf_single : f (MonoidAlgebra.single σ r) = (β σ : ℚ) * r := by
      change (Finsupp.lsum ℚ (fun σ => (β σ : ℚ) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))
        (Finsupp.single σ r) = _
      rw [Finsupp.lsum_single, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    have hsingle : MonoidAlgebra.single σ r = r • MonoidAlgebra.of ℚ _ σ := by
      simp [MonoidAlgebra.of_apply, mul_one]
    conv_lhs => rw [hsingle]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hβ, smul_smul, hf_single, mul_comm]

private lemma YoungSymmetrizerK_ℚ_apply_one (n : ℕ) (la : Nat.Partition n) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer ℚ n la 1 = 1 := by
  rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer_eq_map_int ℚ n la]
  simp [RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer_coeff_one]

private lemma YoungSymmetrizerK_ℚ_ne_zero (n : ℕ) (la : Nat.Partition n) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer ℚ n la ≠ 0 := by
  intro h
  have := YoungSymmetrizerK_ℚ_apply_one n la
  rw [h] at this
  exact zero_ne_one this

/-- The displayed cast of the cardinality of the designated auxiliary finite type is nonzero. -/
instance neZero_natCast_card_auxiliaryType (n : ℕ) : NeZero (Nat.card (G' n) : ℚ) :=
  ⟨by exact_mod_cast Nat.card_pos.ne'⟩

/-- The rational partition submodule is simple over the designated rational algebra. -/
theorem isSimpleModule_partitionSubmodule_rat (n : ℕ) (la : Nat.Partition n) :
    IsSimpleModule (AQ n) (partitionSubmodule ℚ n la) := by
  rw [isSimpleModule_iff_isAtom]
  obtain ⟨α, hα_eq⟩ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer_sq_smul ℚ n la
  have hα_ne : α ≠ 0 := RepresentationTheory.GeneralLinearGroup.WeightCharacter.ne_zero_of_partitionSymmetrizer_sq_eq_smul n la α hα_eq
  obtain ⟨f, hf⟩ := exists_sandwich_eq_smul_rat n la
  set c := RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer ℚ n la with hc_def
  refine ⟨?_, ?_⟩
  ·
    intro h
    have hc_zero : (c : AQ n) = 0 :=
      (Submodule.mem_bot (R := AQ n)).mp (h ▸ Submodule.subset_span rfl)
    exact YoungSymmetrizerK_ℚ_ne_zero n la hc_zero
  ·
    intro N hN
    by_contra hN_ne_bot
    have hN_le := le_of_lt hN
    suffices c ∈ N by
      exact ne_of_lt hN
        (le_antisymm hN_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr this)))
    obtain ⟨P, hP⟩ := (inferInstance : IsSemisimpleModule (AQ n) (AQ n)).exists_isCompl N
    obtain ⟨n₀, hn₀, p₀, hp₀, hc_eq⟩ := Submodule.mem_sup.mp
      (show c ∈ N ⊔ P from hP.sup_eq_top ▸ Submodule.mem_top)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (show n₀ ∈ partitionSubmodule ℚ n la from hN_le hn₀)
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
        (Submodule.mem_bot (R := AQ n)).mp (hP.inf_eq_bot ▸ Submodule.mem_inf.mpr ⟨h1, h2⟩)
      have hn₀_zero : n₀ = 0 := (smul_eq_zero.mp h3).resolve_left hα_ne
      exfalso; apply hN_ne_bot; rw [eq_bot_iff]; intro x hx
      have hc_P : c ∈ P := by rw [← hc_eq, hn₀_zero, zero_add]; exact hp₀
      have hV_le_P : partitionSubmodule ℚ n la ≤ P :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hc_P)
      exact (Submodule.mem_bot (R := AQ n)).mpr
        ((Submodule.mem_bot (R := AQ n)).mp
          (hP.inf_eq_bot ▸ Submodule.mem_inf.mpr ⟨hx, hV_le_P (hN_le hx)⟩))
    · rw [hcn₀] at hcn₀_N
      rw [show c = (f a)⁻¹ • (f a • c) from by rw [inv_smul_smul₀ hfa]]
      exact Submodule.smul_of_tower_mem N (f a)⁻¹ hcn₀_N

/-- Sandwiching any algebra element between the designated partition-indexed element gives a scalar multiple of that element. -/
theorem exists_sandwich_eq_smul (k : Type*) [CommRing k]
    (n : ℕ) (la : Nat.Partition n) :
    ∃ f : MonoidAlgebra k (Equiv.Perm (Fin n)) →ₗ[k] k, ∀ x,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la * x * RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la =
        f x • RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la := by
  set ψ := MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom k)
  set cZ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer n la
  set cK := RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la
  have hψc : ψ cZ = cK := (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer_eq_map_int k n la).symm

  have basis_prop : ∀ σ : Equiv.Perm (Fin n), ∃ β : ℤ,
      cK * MonoidAlgebra.of k _ σ * cK = (β : k) • cK := by
    intro σ
    set β := (cZ * MonoidAlgebra.of ℤ _ σ * cZ) 1
    refine ⟨β, ?_⟩
    have hψσ : ψ (MonoidAlgebra.of ℤ _ σ) = MonoidAlgebra.of k _ σ := by
      change MonoidAlgebra.mapRingHom _ _ (MonoidAlgebra.single σ 1) =
        MonoidAlgebra.single σ 1
      rw [MonoidAlgebra.mapRingHom_single, map_one]
    have hZ := sandwich_perm_eq_coeff_one_smul n la σ
    calc cK * MonoidAlgebra.of k _ σ * cK
        = ψ cZ * ψ (MonoidAlgebra.of ℤ _ σ) * ψ cZ := by rw [hψc, hψσ]
      _ = ψ (cZ * MonoidAlgebra.of ℤ _ σ * cZ) := by rw [map_mul, map_mul]
      _ = ψ (β • cZ) := by rw [hZ]
      _ = (β : k) • cK := by rw [map_zsmul, hψc, Int.cast_smul_eq_zsmul]

  choose β hβ using basis_prop
  let f : MonoidAlgebra k (Equiv.Perm (Fin n)) →ₗ[k] k :=
    (Finsupp.lsum k (fun σ => (β σ : k) • (LinearMap.id : k →ₗ[k] k))) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
  refine ⟨f, fun x => ?_⟩
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [mul_add, add_mul, map_add, add_smul]
    exact congr_arg₂ (· + ·) hx hy
  | single σ r =>
    have hf_single : f (MonoidAlgebra.single σ r) = (β σ : k) * r := by
      change (Finsupp.lsum k (fun σ => (β σ : k) • (LinearMap.id : k →ₗ[k] k)))
        (Finsupp.single σ r) = _
      rw [Finsupp.lsum_single, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    have hsingle : MonoidAlgebra.single σ r = r • MonoidAlgebra.of k _ σ := by
      simp [MonoidAlgebra.of_apply, mul_one]
    conv_lhs => rw [hsingle]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hβ, smul_smul, hf_single, mul_comm]

private lemma YoungSymmetrizerK_general_apply_one (k : Type*) [CommRing k]
    (n : ℕ) (la : Nat.Partition n) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la 1 = 1 := by
  rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer_eq_map_int k n la]
  simp [RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer_coeff_one]

private lemma YoungSymmetrizerK_general_ne_zero (k : Type*) [CommRing k] [Nontrivial k]
    (n : ℕ) (la : Nat.Partition n) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la ≠ 0 := by
  intro h
  have := YoungSymmetrizerK_general_apply_one k n la
  rw [h] at this
  exact zero_ne_one this

private theorem monoidAlgebra_trace_mulLeft_eq_general (k : Type*) [CommRing k]
    {G : Type*} [Group G] [Fintype G]
    (c : MonoidAlgebra k G) :
    LinearMap.trace k _ (LinearMap.mulLeft k c) = Fintype.card G * c.coeff 1 := by
  classical
  set b := MonoidAlgebra.basis G k
  rw [LinearMap.trace_eq_matrix_trace k b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  have hdiag : ∀ σ : G, b.repr (LinearMap.mulLeft k c (b σ)) σ = c.coeff 1 := by
    intro σ
    rw [LinearMap.mulLeft_apply, MonoidAlgebra.basis_apply]
    have hrepr : ∀ (x : MonoidAlgebra k G) (g : G), b.repr x g = x.coeff g :=
      fun _ _ => rfl
    rw [hrepr, MonoidAlgebra.coeff_mul_single_apply, mul_one, mul_inv_cancel]
  simp_rw [hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A scalar expressing the square of the designated partition-indexed element as its scalar multiple is nonzero. -/
theorem ne_zero_of_self_mul_eq_smul (k : Type*) [Field k] [CharZero k]
    (n : ℕ) (la : Nat.Partition n) (α : k)
    (hα_sq : RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la * RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la =
      α • RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la) :
    α ≠ 0 := by
  intro h0
  rw [h0, zero_smul] at hα_sq
  set c := RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la with hc_def
  have hnil : IsNilpotent (LinearMap.mulLeft k c) := by
    refine ⟨2, LinearMap.ext fun x => ?_⟩
    change (LinearMap.mulLeft k c) ((LinearMap.mulLeft k c) x) = 0
    simp only [LinearMap.mulLeft_apply, ← mul_assoc, hα_sq, zero_mul]
  have htr_nil := LinearMap.isNilpotent_trace_of_isNilpotent hnil
  rw [isNilpotent_iff_eq_zero] at htr_nil
  rw [monoidAlgebra_trace_mulLeft_eq_general] at htr_nil
  have hone : c.coeff 1 = 1 := YoungSymmetrizerK_general_apply_one k n la
  rw [hone, mul_one] at htr_nil
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    (by rwa [Fintype.card_perm, Fintype.card_fin] at htr_nil)

/-- In a characteristic-zero field, the cast of the cardinality of the finite permutation group is nonzero. -/
instance neZero_natCast_card_perm (k : Type*) [Field k] [CharZero k] (n : ℕ) :
    NeZero (Nat.card (Equiv.Perm (Fin n)) : k) :=
  ⟨by exact_mod_cast Nat.card_pos.ne'⟩

/-- Over a characteristic-zero field, each partition submodule is simple over the permutation-group algebra. -/
theorem isSimpleModule_partitionSubmodule (k : Type*) [Field k] [CharZero k]
    (n : ℕ) (la : Nat.Partition n) :
    IsSimpleModule (MonoidAlgebra k (Equiv.Perm (Fin n))) (partitionSubmodule k n la) := by
  rw [isSimpleModule_iff_isAtom]
  obtain ⟨α, hα_eq⟩ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer_sq_smul k n la
  have hα_ne : α ≠ 0 := ne_zero_of_self_mul_eq_smul k n la α hα_eq
  obtain ⟨f, hf⟩ := exists_sandwich_eq_smul k n la
  set c := RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la with hc_def
  refine ⟨?_, ?_⟩
  ·
    intro h
    have hc_mem : c ∈ partitionSubmodule k n la := Submodule.subset_span rfl
    have hc_zero : (c : MonoidAlgebra k (Equiv.Perm (Fin n))) = 0 :=
      (Submodule.mem_bot _).mp (h ▸ hc_mem)
    exact YoungSymmetrizerK_general_ne_zero k n la hc_zero
  ·
    intro N hN
    by_contra hN_ne_bot
    have hN_le := le_of_lt hN
    suffices c ∈ N by
      exact ne_of_lt hN
        (le_antisymm hN_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr this)))
    obtain ⟨P, hP⟩ :=
      (inferInstance : IsSemisimpleModule (MonoidAlgebra k (Equiv.Perm (Fin n)))
        (MonoidAlgebra k (Equiv.Perm (Fin n)))).exists_isCompl N
    obtain ⟨n₀, hn₀, p₀, hp₀, hc_eq⟩ := Submodule.mem_sup.mp
      (show c ∈ N ⊔ P from hP.sup_eq_top ▸ Submodule.mem_top)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (show n₀ ∈ partitionSubmodule k n la from hN_le hn₀)
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
        (Submodule.mem_bot _).mp (hP.inf_eq_bot ▸ Submodule.mem_inf.mpr ⟨h1, h2⟩)
      have hn₀_zero : n₀ = 0 := (smul_eq_zero.mp h3).resolve_left hα_ne
      exfalso; apply hN_ne_bot; rw [eq_bot_iff]; intro x hx
      have hc_P : c ∈ P := by rw [← hc_eq, hn₀_zero, zero_add]; exact hp₀
      have hV_le_P : partitionSubmodule k n la ≤ P :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hc_P)
      exact (Submodule.mem_bot _).mpr
        ((Submodule.mem_bot _).mp
          (hP.inf_eq_bot ▸ Submodule.mem_inf.mpr ⟨hx, hV_le_P (hN_le hx)⟩))
    · rw [hcn₀] at hcn₀_N
      rw [show c = (f a)⁻¹ • (f a • c) from by rw [inv_smul_smul₀ hfa]]
      exact Submodule.smul_of_tower_mem N (f a)⁻¹ hcn₀_N

end RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich
