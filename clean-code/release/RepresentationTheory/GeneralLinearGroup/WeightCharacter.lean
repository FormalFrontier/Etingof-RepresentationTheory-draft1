/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.SymmetricPolynomials.Alternant
import RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
import RepresentationTheory.Auxiliary.MutualCentralizers
import RepresentationTheory.Auxiliary.PermutationPolynomials
import RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial



open MvPolynomial Finset CategoryTheory
open scoped TensorProduct
open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
open RepresentationTheory.SymmetricPolynomials.Alternant

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false

set_option linter.flexible false in
section
namespace RepresentationTheory.GeneralLinearGroup.WeightCharacter

/-- A monoid-algebra element regarded as its coefficient function. -/
local instance monoidAlgebraCoeFun {R M : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R M) (fun _ => M → R) :=
  ⟨fun a => a.coeff⟩

/-- The ring structure on endomorphisms commuting with the finite symmetric-group action. -/
noncomputable local instance (priority := high) symmetricEndomorphismRing
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (n : ℕ) :
    Ring (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) := (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n).toRing




/-- The partition of the total sum canonically associated with a finite tuple of natural numbers. -/
def partitionOfTuple (N : ℕ) (lam : Fin N → ℕ) :
    Nat.Partition (∑ i, lam i) where
  parts := (Finset.univ.val.map lam).filter (0 < ·)
  parts_pos hi := (Multiset.mem_filter.mp hi).2
  parts_sum := by
    have h_filt : ∀ (s : Multiset ℕ), (s.filter (0 < ·)).sum = s.sum := by
      intro s
      induction s using Multiset.induction with
      | empty => simp
      | cons a s ih =>
        simp only [Multiset.filter_cons]
        split
        · simp [Multiset.sum_cons, ih]
        · rename_i h; push Not at h; simp [Nat.le_zero.mp h, ih]
    rw [h_filt]
    simp [Finset.sum]




/-- The group-algebra symmetrizer associated with a partition. -/
def partitionSymmetrizer (k : Type*) [CommRing k] (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra k (Equiv.Perm (Fin n)) :=
  haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) := Classical.decPred _
  haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) := Classical.decPred _
  (∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
    ((↑(Equiv.Perm.sign g.val) : ℤ) : k) • MonoidAlgebra.of k _ g.val) *
  (∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la), MonoidAlgebra.of k _ g.val)




/-- The integral group-algebra symmetrizer determined by a partition. -/
def integralPartitionSymmetrizer (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℤ (Equiv.Perm (Fin n)) :=
  haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) := Classical.decPred _
  haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) := Classical.decPred _
  (∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
    (↑(Equiv.Perm.sign g.val) : ℤ) • MonoidAlgebra.of ℤ _ g.val) *
  (∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la), MonoidAlgebra.of ℤ _ g.val)


private theorem mapRange_of {G : Type*} [Monoid G] (R : Type*) [CommRing R]
    (f : ℤ →+* R) (g : G) :
    MonoidAlgebra.mapRingHom G f (MonoidAlgebra.of ℤ G g) = MonoidAlgebra.of R G g := by
  change MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g 1) =
    MonoidAlgebra.single g 1
  rw [MonoidAlgebra.mapRingHom_single, map_one]


/-- A partition symmetrizer over a commutative ring is obtained from its integral form by scalar extension. -/
theorem partitionSymmetrizer_eq_map_int (k : Type*) [CommRing k] (n : ℕ)
    (la : Nat.Partition n) :
    partitionSymmetrizer k n la =
      MonoidAlgebra.mapRingHom _ (Int.castRingHom k) (integralPartitionSymmetrizer n la) := by
  classical
  simp only [partitionSymmetrizer, integralPartitionSymmetrizer, map_mul, map_sum, map_zsmul,
    mapRange_of, ← Int.cast_smul_eq_zsmul k]


/-- The complex symmetrizer is the scalar extension of the integral partition symmetrizer. -/
theorem complexPartitionSymmetrizer_eq_map_int (n : ℕ) (la : Nat.Partition n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la =
      MonoidAlgebra.mapRingHom _ (Int.castRingHom ℂ) (integralPartitionSymmetrizer n la) := by
  classical
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA, integralPartitionSymmetrizer,
    map_mul, map_sum, map_zsmul, mapRange_of, ← Int.cast_smul_eq_zsmul ℂ]

private theorem sortedParts_sum (n : ℕ) (la : Nat.Partition n) :
    (auxiliaryPartitionNatList la).sum = n := by
  simp only [auxiliaryPartitionNatList]
  have := la.parts_sum
  have h1 : (↑(la.parts.sort (· ≥ ·)) : Multiset ℕ) = la.parts := Multiset.sort_eq _ _
  have h2 : (↑(la.parts.sort (· ≥ ·)) : Multiset ℕ).sum =
      (la.parts.sort (· ≥ ·)).sum := Multiset.sum_coe _
  linarith [h2.symm.trans (congrArg Multiset.sum h1)]


/-- A permutation belonging to both specified auxiliary subsets must be the identity. -/
theorem Auxiliary.eq_one_of_mem_both (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n))
    (hrow : σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) (hcol : σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    σ = 1 := by
  ext k : 1
  have hr := hrow k
  have hc := hcol k
  simp only [Equiv.Perm.one_apply]
  have hk_lt : k.val < (auxiliaryPartitionNatList la).sum := by
    rw [sortedParts_sum]; exact k.isLt
  have hσk_lt : (σ k).val < (auxiliaryPartitionNatList la).sum := by
    rw [sortedParts_sum]; exact (σ k).isLt
  exact Fin.ext (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq (auxiliaryPartitionNatList la)
    (σ k).val k.val hσk_lt hk_lt hr hc)


/-- The identity permutation has coefficient one in the integral partition symmetrizer. -/
theorem integralPartitionSymmetrizer_coeff_one (n : ℕ) (la : Nat.Partition n) :
    integralPartitionSymmetrizer n la 1 = 1 := by
  classical

  have hinj : Function.Injective (Int.castRingHom ℂ : ℤ →+* ℂ) := Int.cast_injective
  apply hinj

  rw [show (Int.castRingHom ℂ) (integralPartitionSymmetrizer n la 1) =
      (MonoidAlgebra.mapRingHom _ (Int.castRingHom ℂ) (integralPartitionSymmetrizer n la)) 1
    from (MonoidAlgebra.coeff_mapRingHom (Int.castRingHom ℂ) _ _).symm]
  rw [← complexPartitionSymmetrizer_eq_map_int, (Int.castRingHom ℂ).map_one]

  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA]

  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, smul_mul_assoc]

  have hof : ∀ (g : Equiv.Perm (Fin n)),
      (MonoidAlgebra.of ℂ _ g : MonoidAlgebra ℂ _) = MonoidAlgebra.single g 1 :=
    fun _ => rfl
  simp_rw [hof, MonoidAlgebra.single_mul_single, mul_one]

  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, smul_eq_mul,
    Finsupp.single_apply, mul_ite, mul_one, mul_zero]

  rw [Fintype.sum_eq_single ⟨1, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).one_mem⟩]
  · rw [Fintype.sum_eq_single ⟨1, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).one_mem⟩]
    · simp [Equiv.Perm.sign_one]
    · intro ⟨p, hp⟩ hne
      rw [if_neg]
      intro hp1
      exact hne (Subtype.ext (by simpa using hp1))
  · intro ⟨q, hq⟩ hne
    apply Fintype.sum_eq_zero
    intro ⟨p, hp⟩
    rw [if_neg]
    intro hqp
    have heq : q = p⁻¹ := mul_eq_one_iff_eq_inv.mp hqp
    have hq_in_P : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la := heq ▸ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).inv_mem hp
    exact hne (Subtype.ext (Auxiliary.eq_one_of_mem_both n la q hq_in_P hq))


/-- The square of a partition symmetrizer is a scalar multiple of that symmetrizer. -/
theorem partitionSymmetrizer_sq_smul (k : Type*) [CommRing k] [CharZero k]
    (n : ℕ) (la : Nat.Partition n) :
    ∃ α : k, partitionSymmetrizer k n la * partitionSymmetrizer k n la =
      α • partitionSymmetrizer k n la := by

  obtain ⟨α_ℂ, hα⟩ := RepresentationTheory.Partitions.SquareScalar.exists_mul_self_eq_smul n la

  set cZ := integralPartitionSymmetrizer n la
  set β : ℤ := (cZ * cZ) 1
  set φ_ℂ := MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℂ)
  set φ_k := MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom k)

  have h_ℂ : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la = φ_ℂ cZ := complexPartitionSymmetrizer_eq_map_int n la
  have h_k : partitionSymmetrizer k n la = φ_k cZ := partitionSymmetrizer_eq_map_int k n la

  have hcZ1 : cZ 1 = 1 := integralPartitionSymmetrizer_coeff_one n la

  have hmul : φ_ℂ (cZ * cZ) = α_ℂ • φ_ℂ cZ := by
    rw [map_mul]; exact h_ℂ ▸ hα

  have hα_eq : α_ℂ = (β : ℂ) := by
    have h1 := congrArg (fun x => x.coeff 1) hmul
    simp only [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_smul_apply,
      smul_eq_mul, hcZ1, map_one, mul_one, φ_ℂ] at h1
    exact h1.symm

  have hZ : cZ * cZ = β • cZ := by
    ext σ
    have h1 := congrArg (fun x => x.coeff σ) hmul
    simp only [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_smul_apply,
      smul_eq_mul, hα_eq, φ_ℂ] at h1

    have h2 : ((cZ * cZ) σ : ℂ) = ((β * cZ σ : ℤ) : ℂ) := by push_cast; exact h1
    have h3 : (cZ * cZ) σ = β * cZ σ := Int.cast_injective h2

    rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, h3]

  exact ⟨(β : k), by
    rw [h_k, ← map_mul, hZ, map_zsmul, ← Int.cast_smul_eq_zsmul k]⟩




/-- The tensor-power endomorphism induced by the partition symmetrizer of a weight tuple. -/
def symmetrizerEndomorphism (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i)) :=
  RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction k (Fin N → k) (∑ i, lam i)
    (partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam))




/-- The natural general linear group action on a tensor power of its defining module. -/
def tensorPowerRepresentation (k : Type*) [Field k] (N n : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n) where
  toFun g := PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val)
  map_one' := by
    classical
    change PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (R := k) (1 : Matrix _ _ k)) =
      LinearMap.id
    have : (fun _ : Fin n => Matrix.mulVecLin (R := k) (1 : Matrix _ _ k)) =
        (fun _ : Fin n => (LinearMap.id : (Fin N → k) →ₗ[k] (Fin N → k))) :=
      funext fun _ => Matrix.mulVecLin_one
    rw [this, PiTensorProduct.map_id]
  map_mul' g₁ g₂ := by
    classical
    change PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (R := k) (g₁.val * g₂.val)) =
      (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin g₁.val)) ∘ₗ
      (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin g₂.val))
    have : (fun _ : Fin n => Matrix.mulVecLin (R := k) (g₁.val * g₂.val)) =
        (fun _ : Fin n => (Matrix.mulVecLin g₁.val).comp (Matrix.mulVecLin g₂.val)) :=
      funext fun _ => Matrix.mulVecLin_mul g₁.val g₂.val
    rw [this, PiTensorProduct.map_comp]




/-- The tensor-power action commutes with the endomorphism defining the distinguished subspace. -/
theorem tensorPowerRepresentation_comp_symmetrizerEndomorphism (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    tensorPowerRepresentation k N (∑ i, lam i) g ∘ₗ symmetrizerEndomorphism k N lam =
    symmetrizerEndomorphism k N lam ∘ₗ tensorPowerRepresentation k N (∑ i, lam i) g := by
  set n := ∑ i, lam i
  set V := Fin N → k
  set f : V →ₗ[k] V := Matrix.mulVecLin g.val

  have h_sym : (symmetrizerEndomorphism k N lam : Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)) ∈
      (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))) := by
    rw [← RepresentationTheory.Auxiliary.MutualCentralizers.range_permutationGroupAlgebraAction k V n]
    exact ⟨_, rfl⟩

  have h_diag : (tensorPowerRepresentation k N n g : Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)) ∈
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))) := by
    apply Algebra.subset_adjoin
    exact ⟨f, rfl⟩


  have hcent := RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra k V n h_diag
  rw [Subalgebra.mem_centralizer_iff] at hcent

  exact (hcent _ h_sym).symm


/-- The distinguished tensor-power subspace is stable under the natural general linear group action. -/
theorem schurSubmodule_invariant (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i))
    (hv : v ∈ LinearMap.range (symmetrizerEndomorphism k N lam)) :
    (tensorPowerRepresentation k N (∑ i, lam i) g) v ∈ LinearMap.range (symmetrizerEndomorphism k N lam) := by
  obtain ⟨w, rfl⟩ := hv
  exact ⟨(tensorPowerRepresentation k N (∑ i, lam i) g) w,
    (LinearMap.ext_iff.mp (tensorPowerRepresentation_comp_symmetrizerEndomorphism k N lam g) w).symm⟩




/-- The distinguished subspace of the relevant tensor power determined by a weight tuple. -/
def schurSubmodule (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    Submodule k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i)) :=
  LinearMap.range (symmetrizerEndomorphism k N lam)

/-- The additive commutative group structure inherited by the distinguished tensor-power subspace. -/
noncomputable local instance (priority := high) schurSubmoduleAddCommGroup
    (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    AddCommGroup (schurSubmodule k N lam) :=
  { Module.addCommMonoidToAddCommGroup k with
    toAddCommMonoid := (schurSubmodule k N lam).addCommMonoid }


/-- The general linear group representation obtained by restricting the tensor-power action to the distinguished subspace. -/
def schurSubmoduleRepresentation (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (schurSubmodule k N lam) where
  toFun g := (tensorPowerRepresentation k N (∑ i, lam i) g).restrict
    (p := schurSubmodule k N lam) (q := schurSubmodule k N lam)
    (fun v hv => schurSubmodule_invariant k N lam g v hv)
  map_one' := by
    ext ⟨v, hv⟩
    simp only [LinearMap.coe_restrict_apply]
    exact LinearMap.ext_iff.mp (map_one (tensorPowerRepresentation k N _)) v
  map_mul' g₁ g₂ := by
    ext ⟨v, hv⟩

    have h_mul := LinearMap.ext_iff.mp (map_mul (tensorPowerRepresentation k N (∑ i, lam i)) g₁ g₂) v



    simp only [LinearMap.coe_restrict_apply, Module.End.mul_apply] at h_mul ⊢
    exact h_mul


/-- The distinguished tensor-power subspace is finite-dimensional over the base field. -/
instance finite_schurSubmodule (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    Module.Finite k (schurSubmodule k N lam) :=
  inferInstance


/-- The finite-dimensional general linear group representation associated with a tuple of nonnegative weights. -/
@[reducible] def schurRepresentation (k : Type*) [Field k] [IsAlgClosed k]
    (N : ℕ) (lam : Fin N → ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  @FDRep.of k (Matrix.GeneralLinearGroup (Fin N) k) inferInstance inferInstance
    (schurSubmodule k N lam) inferInstance inferInstance inferInstance
    (schurSubmoduleRepresentation k N lam)




/-- The invertible diagonal matrix whose selected coordinate is a prescribed unit and whose other coordinates are one. -/
noncomputable def diagonalUnit (k : Type*) [Field k] (N : ℕ) (i : Fin N) (t : kˣ) :
    Matrix.GeneralLinearGroup (Fin N) k where
  val := Matrix.diagonal (Function.update 1 i (t : k))
  inv := Matrix.diagonal (Function.update 1 i ((t⁻¹ : kˣ) : k))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext j
    by_cases h : j = i
    · subst h; simp [Units.val_inv_eq_inv_val]
    · simp [Function.update_of_ne h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext j
    by_cases h : j = i
    · subst h; simp [Units.val_inv_eq_inv_val]
    · simp [Function.update_of_ne h]


/-- The simultaneous weight space of a finite-dimensional general linear group representation at a tuple of exponents. -/
noncomputable def weightSpace (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N → ℕ) : Submodule k M :=
  ⨅ (i : Fin N) (t : kˣ),
    LinearMap.ker (M.ρ (diagonalUnit k N i t) - ((t : k) ^ μ i) • LinearMap.id)




/-- Diagonal units supported at arbitrary coordinates commute. -/
theorem diagonalUnit_comm (k : Type*) [Field k] (N : ℕ) (i₁ : Fin N) (t₁ : kˣ)
    (i₂ : Fin N) (t₂ : kˣ) :
    diagonalUnit k N i₁ t₁ * diagonalUnit k N i₂ t₂ = diagonalUnit k N i₂ t₂ * diagonalUnit k N i₁ t₁ := by
  ext : 1
  change (diagonalUnit k N i₁ t₁).val * (diagonalUnit k N i₂ t₂).val =
    (diagonalUnit k N i₂ t₂).val * (diagonalUnit k N i₁ t₁).val
  simp only [diagonalUnit, Matrix.diagonal_mul_diagonal, mul_comm]


/-- The representation endomorphisms arising from any two coordinate diagonal units commute. -/
theorem commute_rep_diagonalUnit (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (i₁ : Fin N) (t₁ : kˣ) (i₂ : Fin N) (t₂ : kˣ) :
    Commute (M.ρ (diagonalUnit k N i₁ t₁)) (M.ρ (diagonalUnit k N i₂ t₂)) := by
  change M.ρ (diagonalUnit k N i₁ t₁) * M.ρ (diagonalUnit k N i₂ t₂) =
    M.ρ (diagonalUnit k N i₂ t₂) * M.ρ (diagonalUnit k N i₁ t₁)
  rw [← map_mul, ← map_mul, diagonalUnit_comm]




/-- A weight space lies in the maximal generalized eigenspace for every coordinate diagonal action. -/
theorem weightSpace_le_maxGenEigenspace (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N → ℕ) (i : Fin N) (t : kˣ) :
    weightSpace k N M μ ≤
      Module.End.maxGenEigenspace (M.ρ (diagonalUnit k N i t)) ((t : k) ^ μ i) := by
  intro v hv

  have h1 : weightSpace k N M μ ≤ ⨅ (s : kˣ),
      LinearMap.ker (M.ρ (diagonalUnit k N i s) - ((s : k) ^ μ i) • LinearMap.id) :=
    iInf_le _ i
  have h2 : ⨅ (s : kˣ),
      LinearMap.ker (M.ρ (diagonalUnit k N i s) - ((s : k) ^ μ i) • LinearMap.id) ≤
      LinearMap.ker (M.ρ (diagonalUnit k N i t) - ((t : k) ^ μ i) • LinearMap.id) :=
    iInf_le _ t
  have hker := LinearMap.mem_ker.mp (h2 (h1 hv))

  have hev : (M.ρ (diagonalUnit k N i t)) v = ((t : k) ^ μ i) • v := by
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hker

  exact Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hev)




/-- For every positive exponent, an algebraically closed field has a unit whose indicated power is not one. -/
theorem exists_unit_pow_ne_one (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ) (hn : n ≥ 1) :
    ∃ t : kˣ, (t : k) ^ n ≠ 1 := by
  by_contra h; push Not at h

  have hp_ne : (Polynomial.X ^ n - Polynomial.C (1 : k)) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by omega) 1

  have hfin : {a : k | a ^ n = 1}.Finite := by
    apply ((Polynomial.X ^ n - Polynomial.C (1 : k)).rootSet_finite k).subset
    intro a (ha : a ^ n = 1)
    rw [Polynomial.mem_rootSet]
    exact ⟨hp_ne, by simp [ha]⟩

  have hsub : {a : k | a ≠ 0} ⊆ {a : k | a ^ n = 1} :=
    fun a ha => by simpa using h (Units.mk0 a ha)

  have hinf : Set.Infinite {a : k | a ≠ 0} := by
    rw [show {a : k | a ≠ 0} = ({0} : Set k)ᶜ from by ext; simp]
    exact (Set.finite_singleton _).infinite_compl
  exact hinf.not_finite (hfin.subset hsub)


/-- Distinct natural exponents can be separated by evaluating powers of a unit in an algebraically closed field. -/
theorem exists_unit_pow_ne_pow (k : Type*) [Field k] [IsAlgClosed k] {a b : ℕ} (hab : a ≠ b) :
    ∃ t : kˣ, (t : k) ^ a ≠ (t : k) ^ b := by

  suffices ∀ {a b : ℕ}, a > b → ∃ t : kˣ, (t : k) ^ a ≠ (t : k) ^ b from by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · obtain ⟨t, ht⟩ := this h; exact ⟨t, ht.symm⟩
    · exact this h
  intro a b h
  obtain ⟨t, ht⟩ := exists_unit_pow_ne_one k (a - b) (by omega)
  refine ⟨t, fun heq => ht ?_⟩
  have hne : (t : k) ^ b ≠ 0 := pow_ne_zero _ (Units.ne_zero t)
  have : (t : k) ^ (a - b) * (t : k) ^ b = 1 * (t : k) ^ b := by
    rw [← pow_add, Nat.sub_add_cancel h.le, heq, one_mul]
  exact mul_right_cancel₀ hne this


/-- Only finitely many exponent tuples have a nonzero weight space in a finite-dimensional representation. -/
theorem finite_support_weightSpace (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    { μ : Fin N →₀ ℕ | weightSpace k N M (fun i => μ i) ≠ ⊥ }.Finite := by

  set f : Fin N × kˣ → Module.End k M := fun p => M.ρ (diagonalUnit k N p.1 p.2) with hf_def

  have h_comm : ∀ (p₁ p₂ : Fin N × kˣ), Commute (f p₁) (f p₂) :=
    fun p₁ p₂ => commute_rep_diagonalUnit k N M p₁.1 p₁.2 p₂.1 p₂.2
  have h_mapsTo : ∀ (p₁ p₂ : Fin N × kˣ) (φ : k),
      Set.MapsTo (f p₁)
        ((f p₂).maxGenEigenspace φ) ((f p₂).maxGenEigenspace φ) :=
    fun p₁ p₂ φ => Module.End.mapsTo_maxGenEigenspace_of_comm (h_comm p₂ p₁) φ

  have h_indep := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f h_mapsTo

  have h_fin := Submodule.finite_ne_bot_of_iSupIndep h_indep



  set χ : (Fin N →₀ ℕ) → (Fin N × kˣ → k) :=
    fun μ p => (p.2 : k) ^ (μ p.1) with hχ_def

  have h_inj : Function.Injective χ := by
    intro μ₁ μ₂ heq
    ext i
    by_contra hi
    obtain ⟨t, ht⟩ := exists_unit_pow_ne_pow k hi
    exact ht (congr_fun heq (i, t))

  have h_le : ∀ (μ : Fin N →₀ ℕ),
      weightSpace k N M (fun i => μ i) ≤
        ⨅ (p : Fin N × kˣ), (f p).maxGenEigenspace (χ μ p) := by
    intro μ
    apply le_iInf
    intro ⟨i, t⟩
    exact weightSpace_le_maxGenEigenspace k N M (fun j => μ j) i t

  refine (h_fin.preimage h_inj.injOn).subset ?_
  intro μ hμ
  simp only [Set.mem_setOf_eq] at hμ
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  exact fun h => hμ (eq_bot_iff.mpr (h ▸ h_le μ))




/-- The multivariable polynomial recording weight-space dimensions of a finite-dimensional general linear group representation. -/
noncomputable def weightCharacter (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    MvPolynomial (Fin N) ℚ :=
  have hfin : { μ : Fin N →₀ ℕ |
      weightSpace k N M (fun i => μ i) ≠ ⊥ }.Finite :=
    finite_support_weightSpace k N M
  hfin.toFinset.sum fun μ =>
    (Module.finrank k (weightSpace k N M (fun i => μ i)) : ℚ) •
      MvPolynomial.monomial μ 1

variable (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]



omit [CharZero k] in

/-- Each coefficient of the weight character is the dimension of the corresponding weight space. -/
theorem coeff_weightCharacter (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N →₀ ℕ) :
    (weightCharacter k N M).coeff μ =
      (Module.finrank k (weightSpace k N M (fun i => μ i)) : ℚ) := by
  unfold weightCharacter
  have key : ∀ (S : Finset (Fin N →₀ ℕ)) (c : (Fin N →₀ ℕ) → ℚ),
      (S.sum fun ν => c ν • MvPolynomial.monomial ν (1 : ℚ)).coeff μ =
        if μ ∈ S then c μ else 0 := by
    intro S c
    simp only [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    split_ifs with h
    · rw [Finset.sum_eq_single μ]
      · simp
      · intro ν _ hne; exact if_neg hne
      · intro h'; exact absurd h h'
    · exact Finset.sum_eq_zero fun ν hν => by
        rw [if_neg]; exact fun heq => h (heq ▸ hν)
  rw [key]
  split_ifs with hmem
  · rfl
  · have hbot : weightSpace k N M (fun i => μ i) = ⊥ := by
      by_contra h
      exact hmem ((finite_support_weightSpace k N M).mem_toFinset.mpr h)
    rw [hbot]; simp




private theorem alternant_det_associated_prod' (N : ℕ) :
    Associated (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) := by
  have h1 : RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N) =
      (Matrix.vandermonde (MvPolynomial.X : Fin N → MvPolynomial (Fin N) ℚ)).submatrix
        id (@Fin.revPerm N) := by
    ext i j
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix, Matrix.vandermonde, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents, Matrix.of_apply,
      Matrix.submatrix_apply, id, Fin.revPerm_apply]
    congr 2
    simp only [Fin.rev, Fin.val_mk]
    omega
  rw [h1, Matrix.det_permute', Matrix.det_vandermonde]
  have hu : IsUnit (↑↑(@Fin.revPerm N).sign : MvPolynomial (Fin N) ℚ) :=
    (Units.map (algebraMap ℤ (MvPolynomial (Fin N) ℚ)).toMonoidHom
      (@Fin.revPerm N).sign).isUnit
  exact (associated_isUnit_mul_left_iff hu).mpr (Associated.refl _)


/-- The determinant of the specified auxiliary matrix is nonzero. -/
theorem Auxiliary.det_ne_zero (N : ℕ) :
    (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det ≠ (0 : MvPolynomial (Fin N) ℚ) := by
  obtain ⟨u, hu⟩ := alternant_det_associated_prod' N
  intro h
  have hprod : ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hij : j ≠ i := (Finset.mem_Ioi.mp hj).ne'
    intro heq

    have : (MvPolynomial.eval (fun k : Fin N => if k = j then (1 : ℚ) else 0))
        (MvPolynomial.X j - MvPolynomial.X i) = 0 :=
      congr_arg _ heq |>.trans (map_zero _)
    simp [hij.symm] at this
  exact hprod (by rw [← hu, h, zero_mul])








/-- The endomorphism induced by a quasi-idempotent partition symmetrizer satisfies the same quadratic relation. -/
theorem symmetrizerEndomorphism_sq (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (α : k)
    (hα_sq : partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam)) :
    symmetrizerEndomorphism k N lam * symmetrizerEndomorphism k N lam =
      α • symmetrizerEndomorphism k N lam := by
  unfold symmetrizerEndomorphism
  rw [← map_mul, hα_sq, map_smul]


/-- For a nonzero quasi-idempotence scalar, the distinguished subspace is the range of the squared symmetrizer endomorphism. -/
theorem schurSubmodule_eq_range_symmetrizerEndomorphism_sq (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (α : k) (hα : α ≠ 0)
    (hα_sq : partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam)) :
    schurSubmodule k N lam = LinearMap.range (symmetrizerEndomorphism k N lam *
      symmetrizerEndomorphism k N lam) := by
  unfold schurSubmodule
  rw [show symmetrizerEndomorphism k N lam * symmetrizerEndomorphism k N lam =
    α • symmetrizerEndomorphism k N lam from symmetrizerEndomorphism_sq k N lam α hα_sq]
  ext v; simp [LinearMap.mem_range, LinearMap.smul_apply]
  constructor
  · rintro ⟨w, rfl⟩; exact ⟨α⁻¹ • w, by rw [map_smul, smul_comm, inv_smul_smul₀ hα]⟩
  · rintro ⟨w, rfl⟩; exact ⟨α • w, by rw [map_smul]⟩


/-- When the symmetrizer squares to a scalar multiple of itself, its endomorphism acts by that scalar on the distinguished subspace. -/
theorem symmetrizerEndomorphism_apply_of_mem (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (α : k)
    (hα_sq : partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam))
    (v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i))
    (hv : v ∈ schurSubmodule k N lam) :
    symmetrizerEndomorphism k N lam v = α • v := by
  obtain ⟨w, rfl⟩ := hv
  change (symmetrizerEndomorphism k N lam * symmetrizerEndomorphism k N lam) w = α • symmetrizerEndomorphism k N lam w
  rw [symmetrizerEndomorphism_sq k N lam α hα_sq]
  rfl




/-- The symmetrizer endomorphism bundled as an element commuting with the symmetric-group action. -/
def symmetrizerEndomorphismMem (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    ↥(RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) (∑ i, lam i)) :=
  ⟨symmetrizerEndomorphism k N lam, by
    rw [← RepresentationTheory.Auxiliary.MutualCentralizers.range_permutationGroupAlgebraAction]; exact ⟨_, rfl⟩⟩

/-- The underlying map of the bundled symmetrizer endomorphism is the original endomorphism. -/
@[simp]
theorem symmetrizerEndomorphismMem_val (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    (symmetrizerEndomorphismMem k N lam).val = symmetrizerEndomorphism k N lam := rfl







set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 2400000 in
set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 1000000 in

/-- Under an isotypic direct-sum decomposition, the symmetrizer endomorphism acts on a pure tensor through its first factor. -/
theorem map_symmetrizerEndomorphism_tmul
    (k : Type*) [Field k]
    (N : ℕ) (lam : Fin N → ℕ)
    {ι : Type} [DecidableEq ι]
    (S : ι → Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) (∑ i, lam i))
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i)))
    (e : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i) ≃ₗ[k]
      DirectSum ι (fun i => ↥(S i) ⊗[k]
        (↥(S i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) (∑ i, lam i)]
          RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i))))
    (he : ∀ (i : ι) (v : ↥(S i))
        (l : ↥(S i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) (∑ i, lam i)]
          RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i)),
      e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v)
    (i : ι) (v : ↥(S i))
    (l : ↥(S i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) (∑ i, lam i)]
      RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i)) :
    e (symmetrizerEndomorphism k N lam
        (e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)))) =
      DirectSum.of _ i ((symmetrizerEndomorphismMem k N lam • v) ⊗ₜ[k] l) := by
  set A := RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) (∑ i, lam i) with hA


  have hsmul : ((symmetrizerEndomorphismMem k N lam : ↥A) • (l v)
      : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i)) =
      symmetrizerEndomorphism k N lam (l v) := by
    rw [Subalgebra.smul_def, Module.End.smul_def, symmetrizerEndomorphismMem_val]


  have hl : symmetrizerEndomorphism k N lam (l v) =
      l ((symmetrizerEndomorphismMem k N lam : ↥A) • v) := by
    rw [← hsmul, ← l.map_smul (symmetrizerEndomorphismMem k N lam) v]
  rw [he i v l, hl, ← he i ((symmetrizerEndomorphismMem k N lam : ↥A) • v) l,
    e.apply_symm_apply]




/-- A submodule over the symmetric endomorphism algebra is closed under the action of each permutation. -/
lemma mem_of_mem_symmetricInvariantSubmodule
    {k : Type*} [Field k] {N n : ℕ}
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n))
    (σ : Equiv.Perm (Fin n))
    {v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n} (hv : v ∈ S) :
    (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k (Fin N → k) n σ).toLinearMap v ∈ S := by
  have h_in : (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k (Fin N → k) n σ).toLinearMap ∈
      (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) n :
        Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n))) :=
    Algebra.subset_adjoin ⟨σ, rfl⟩
  exact S.smul_mem ⟨_, h_in⟩ hv


private lemma youngSymEndomorphism_mem_of_symGroupImage_submodule
    {k : Type*} [Field k] {N : ℕ} (lam : Fin N → ℕ)
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) (∑ i, lam i))
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i)))
    {v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i)} (hv : v ∈ S) :
    symmetrizerEndomorphism k N lam v ∈ S :=
  S.smul_mem (symmetrizerEndomorphismMem k N lam) hv


private lemma youngSymEndomorphism_eq_sum_symGroupAction
    {k : Type*} [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    symmetrizerEndomorphism k N lam =
    ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
      (partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) σ) •
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k (Fin N → k) (∑ i, lam i) σ).toLinearMap := by
  set c := partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) with hc
  have hE : symmetrizerEndomorphism k N lam =
      c.coeff.sum (fun σ a => a •
        (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k (Fin N → k) (∑ i, lam i) σ).toLinearMap) := by
    unfold symmetrizerEndomorphism RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction
    rw [MonoidAlgebra.lift_apply]
    rfl
  rw [hE, Finsupp.sum]
  apply Finset.sum_subset (Finset.subset_univ c.coeff.support)
  intro σ _ hmem
  simp only [Finsupp.mem_support_iff, not_not] at hmem
  rw [hmem, zero_smul]






set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in
set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 800000 in

/-- The trace of the restricted symmetrizer endomorphism is a coefficient-weighted sum of restricted permutation traces. -/
theorem Auxiliary.trace_symmetrizerEndomorphism_restrict
    {k : Type*} [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) (∑ i, lam i))
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i)))
    [Module.Finite k ↥(S.restrictScalars k)] :
    LinearMap.trace k ↥(S.restrictScalars k)
        ((symmetrizerEndomorphism k N lam).restrict
          (p := S.restrictScalars k) (q := S.restrictScalars k)
          (fun _ hv =>
            youngSymEndomorphism_mem_of_symGroupImage_submodule lam S hv)) =
      ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) σ) *
        LinearMap.trace k ↥(S.restrictScalars k)
          ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
            (p := S.restrictScalars k) (q := S.restrictScalars k)
            (fun _ hv =>
              mem_of_mem_symmetricInvariantSubmodule S σ hv)) := by
  have h_eq : (symmetrizerEndomorphism k N lam).restrict
        (p := S.restrictScalars k) (q := S.restrictScalars k)
        (fun _ hv =>
          youngSymEndomorphism_mem_of_symGroupImage_submodule lam S hv) =
      ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) σ) •
        (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
          (p := S.restrictScalars k) (q := S.restrictScalars k)
          (fun _ hv =>
            mem_of_mem_symmetricInvariantSubmodule S σ hv) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have h_pt := LinearMap.ext_iff.mp
      (youngSymEndomorphism_eq_sum_symGroupAction (k := k) N lam) v.val
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply] at h_pt
    simp only [LinearMap.restrict_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]
    exact h_pt
  rw [h_eq, map_sum]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [LinearMap.map_smul, smul_eq_mul]


set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 80000 in

/-- Restricting a quasi-idempotent symmetrizer endomorphism to an invariant subspace preserves its quadratic relation. -/
theorem Auxiliary.restrict_symmetrizerEndomorphism_sq
    {k : Type*} [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) (∑ i, lam i))
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) (∑ i, lam i)))
    (α : k)
    (hα_sq : partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer k (∑ i, lam i) (partitionOfTuple N lam)) :
    ((symmetrizerEndomorphism k N lam).restrict
        (p := S.restrictScalars k) (q := S.restrictScalars k)
        (fun _ hv =>
          youngSymEndomorphism_mem_of_symGroupImage_submodule lam S hv)) *
      ((symmetrizerEndomorphism k N lam).restrict
        (p := S.restrictScalars k) (q := S.restrictScalars k)
        (fun _ hv =>
          youngSymEndomorphism_mem_of_symGroupImage_submodule lam S hv)) =
    α • (symmetrizerEndomorphism k N lam).restrict
        (p := S.restrictScalars k) (q := S.restrictScalars k)
        (fun _ hv =>
          youngSymEndomorphism_mem_of_symGroupImage_submodule lam S hv) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have h_sq : symmetrizerEndomorphism k N lam * symmetrizerEndomorphism k N lam =
      α • symmetrizerEndomorphism k N lam :=
    symmetrizerEndomorphism_sq k N lam α hα_sq
  have h_pt := LinearMap.ext_iff.mp h_sq v.val
  simp only [Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.restrict_apply, SetLike.val_smul_of_tower]
  exact h_pt



section SpechtBridge

variable {N n : ℕ}


private noncomputable def symGroupAlgHomToImage :
    RepresentationTheory.PartitionAuxiliary.natIndexedType n →ₐ[ℂ] ↥(RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n) :=
  AlgHom.codRestrict (RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction ℂ (Fin N → ℂ) n)
    (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
    (fun a => by rw [← RepresentationTheory.Auxiliary.MutualCentralizers.range_permutationGroupAlgebraAction]; exact ⟨a, rfl⟩)

@[simp]
private theorem symGroupAlgHomToImage_val (a : RepresentationTheory.PartitionAuxiliary.natIndexedType n) :
    ((symGroupAlgHomToImage (N := N) (n := n)) a).val =
      (RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction ℂ (Fin N → ℂ) n) a := rfl

private theorem symGroupAlgHomToImage_surjective :
    Function.Surjective (symGroupAlgHomToImage (N := N) (n := n)) := by
  intro b
  have h_in : (b.val : Module.End ℂ _) ∈ (RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction ℂ (Fin N → ℂ) n).range := by
    rw [RepresentationTheory.Auxiliary.MutualCentralizers.range_permutationGroupAlgebraAction]; exact b.prop
  obtain ⟨a, ha⟩ := h_in
  exact ⟨a, Subtype.ext ha⟩

private theorem symGroupAlgHomToImage_of (σ : Equiv.Perm (Fin n)) :
    (symGroupAlgHomToImage (N := N) (n := n)) (MonoidAlgebra.of ℂ _ σ) =
      ⟨(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) n σ).toLinearMap,
        Algebra.subset_adjoin ⟨σ, rfl⟩⟩ := by
  apply Subtype.ext
  change (RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction ℂ (Fin N → ℂ) n) (MonoidAlgebra.of ℂ _ σ) = _
  unfold RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction
  rw [MonoidAlgebra.lift_of]
  rfl

set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in


set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in

private theorem symGroupAlgHomToImage_smul_val
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) n))
    (a : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (x : ↥S) :
    ((symGroupAlgHomToImage (N := N) (n := n) a) • x).val =
      (RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction ℂ (Fin N → ℂ) n a) x.val := by
  rw [Submodule.coe_smul, Subalgebra.smul_def, Module.End.smul_def,
      symGroupAlgHomToImage_val]

set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in




@[reducible] private noncomputable def submoduleAsSymGroupAlgebraModule
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) n)) :
    Module (RepresentationTheory.PartitionAuxiliary.natIndexedType n) ↥(S.restrictScalars ℂ) :=
  Module.compHom _ (symGroupAlgHomToImage (N := N) (n := n)).toRingHom

set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in




private theorem submoduleAsSymGroupAlgebraModule_smul_def
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) n))
    (a : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (v : ↥(S.restrictScalars ℂ)) :
    letI := submoduleAsSymGroupAlgebraModule S
    (a • v).val = (RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction ℂ (Fin N → ℂ) n) a v.val := rfl

set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in




private theorem submoduleAsSymGroupAlgebra_isScalarTower
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) n)) :
    letI := submoduleAsSymGroupAlgebraModule S
    IsScalarTower ℂ (RepresentationTheory.PartitionAuxiliary.natIndexedType n) ↥(S.restrictScalars ℂ) := by
  letI := submoduleAsSymGroupAlgebraModule S
  refine ⟨fun c a v => ?_⟩
  apply Subtype.ext
  rw [submoduleAsSymGroupAlgebraModule_smul_def, map_smul]
  rfl

set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in




private noncomputable def submoduleSemilinearId
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) n)) :
    letI := submoduleAsSymGroupAlgebraModule S
    ↥(S.restrictScalars ℂ) →ₛₗ[(symGroupAlgHomToImage (N := N) (n := n)).toRingHom] ↥S :=
  letI := submoduleAsSymGroupAlgebraModule S
  { toFun := fun v => ⟨v.val, v.prop⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in

private theorem submoduleSemilinearId_bijective
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) n)) :
    letI := submoduleAsSymGroupAlgebraModule S
    Function.Bijective (submoduleSemilinearId S) := by
  letI := submoduleAsSymGroupAlgebraModule S
  refine ⟨?_, ?_⟩
  · intro v w h
    apply Subtype.ext
    exact Subtype.ext_iff.mp h
  · rintro ⟨w, hw⟩; exact ⟨⟨w, hw⟩, rfl⟩

set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in





set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in

private theorem submoduleAsSymGroupAlgebra_isSimpleModule
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) n))
    [IsSimpleModule (↥(RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)) ↥S] :
    letI := submoduleAsSymGroupAlgebraModule S
    IsSimpleModule (RepresentationTheory.PartitionAuxiliary.natIndexedType n) ↥(S.restrictScalars ℂ) := by
  letI := submoduleAsSymGroupAlgebraModule S
  haveI : RingHomSurjective
      (symGroupAlgHomToImage (N := N) (n := n)).toRingHom :=
    ⟨symGroupAlgHomToImage_surjective⟩
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (submoduleSemilinearId S)
    (submoduleSemilinearId_bijective S)).mpr ‹_›


private theorem spechtModule_smul_of
    (la' : Nat.Partition n) (σ : Equiv.Perm (Fin n)) (w : ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la')) :
    ((MonoidAlgebra.of ℂ _ σ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) • w : ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la')) =
      RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism n la' σ w := by
  apply Subtype.ext
  rfl

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in
set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in

private theorem trace_restrictedSymGroupAction_eq_of_spechtIso
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) n))
    (la' : Nat.Partition n)
    (e : letI := submoduleAsSymGroupAlgebraModule S
         ↥(S.restrictScalars ℂ) ≃ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n] ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la'))
    (σ : Equiv.Perm (Fin n)) :
    LinearMap.trace ℂ ↥(S.restrictScalars ℂ)
        ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) n σ).toLinearMap.restrict
          (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
          (fun _ hv =>
            mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
      RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n la' σ := by
  letI := submoduleAsSymGroupAlgebraModule S
  haveI := submoduleAsSymGroupAlgebra_isScalarTower S

  let eℂ : ↥(S.restrictScalars ℂ) ≃ₗ[ℂ] ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la') :=
    LinearEquiv.restrictScalars ℂ e
  set restrictedAction :
      ↥(S.restrictScalars ℂ) →ₗ[ℂ] ↥(S.restrictScalars ℂ) :=
    (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) n σ).toLinearMap.restrict
      (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
      (fun _ hv =>
        mem_of_mem_symmetricInvariantSubmodule S σ hv)

  have h_intertwine : ∀ v : ↥(S.restrictScalars ℂ),
      eℂ (restrictedAction v) = RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism n la' σ (eℂ v) := by
    intro v
    have h := e.map_smul (MonoidAlgebra.of ℂ _ σ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) v
    have h_lhs : (MonoidAlgebra.of ℂ _ σ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) • v =
        restrictedAction v := by
      apply Subtype.ext
      change (RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction ℂ (Fin N → ℂ) n) (MonoidAlgebra.of ℂ _ σ) v.val =
        (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) n σ).toLinearMap v.val
      unfold RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction
      rw [MonoidAlgebra.lift_of]
      rfl
    have h_rhs : (MonoidAlgebra.of ℂ _ σ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) • e v =
        RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism n la' σ (e v) := spechtModule_smul_of la' σ (e v)
    rw [h_lhs, h_rhs] at h
    exact h
  have h_eq : restrictedAction = eℂ.symm.toLinearMap ∘ₗ
      (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism n la' σ) ∘ₗ eℂ.toLinearMap := by
    apply LinearMap.ext
    intro v
    change restrictedAction v = eℂ.symm (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism n la' σ (eℂ v))
    rw [← h_intertwine v, eℂ.symm_apply_apply]
  rw [h_eq]

  have h_conj : eℂ.symm.toLinearMap ∘ₗ
      (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism n la' σ) ∘ₗ eℂ.toLinearMap =
        eℂ.symm.conj (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism n la' σ) := by
    rfl
  rw [h_conj]
  have ht := @LinearMap.trace_conj' ℂ inferInstance
    (↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la')) (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la').addCommGroup
    (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la').module'
    (↥(S.restrictScalars ℂ)) (S.restrictScalars ℂ).addCommGroup
    (S.restrictScalars ℂ).module
    (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism n la' σ) eℂ.symm
  rw [ht]
  rfl

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in


set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in

/-- Every simple submodule for the symmetric endomorphism algebra has the permutation character associated with some partition. -/
theorem Auxiliary.exists_partition_character_eq_of_simple
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) n))
    [IsSimpleModule (↥(RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)) ↥S] :
    ∃ la' : Nat.Partition n, ∀ σ : Equiv.Perm (Fin n),
      LinearMap.trace ℂ ↥(S.restrictScalars ℂ)
          ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) n σ).toLinearMap.restrict
            (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
            (fun _ hv =>
              mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
        RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n la' σ := by
  letI := submoduleAsSymGroupAlgebraModule S
  haveI := submoduleAsSymGroupAlgebra_isScalarTower S
  haveI := submoduleAsSymGroupAlgebra_isSimpleModule S
  obtain ⟨la', ⟨e⟩⟩ :=
    RepresentationTheory.SimpleModule.SubtypeRepresentation.exists_linearEquiv_to_subtype n ↥(S.restrictScalars ℂ)
  exact ⟨la', fun σ => trace_restrictedSymGroupAction_eq_of_spechtIso S la' e σ⟩

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 1600000 in
set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 400000 in

private noncomputable def transferToSymGroupImageEquiv
    (S S' : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) n))
    (g : letI := submoduleAsSymGroupAlgebraModule S
         letI := submoduleAsSymGroupAlgebraModule S'
         ↥(S.restrictScalars ℂ) ≃ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n] ↥(S'.restrictScalars ℂ)) :
    ↥S ≃ₗ[↥(RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)] ↥S' :=
  letI := submoduleAsSymGroupAlgebraModule S
  letI := submoduleAsSymGroupAlgebraModule S'
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
      obtain ⟨a, rfl⟩ := symGroupAlgHomToImage_surjective b
      apply Subtype.ext
      have hxeq : (⟨((symGroupAlgHomToImage (N := N) (n := n) a) • x).val,
            ((symGroupAlgHomToImage (N := N) (n := n) a) • x).property⟩ :
            ↥(S.restrictScalars ℂ))
            = a • (⟨x.val, x.property⟩ : ↥(S.restrictScalars ℂ)) := by
        apply Subtype.ext
        rw [submoduleAsSymGroupAlgebraModule_smul_def, symGroupAlgHomToImage_smul_val]
      change (g ⟨((symGroupAlgHomToImage (N := N) (n := n) a) • x).val,
            ((symGroupAlgHomToImage (N := N) (n := n) a) • x).property⟩).val = _
      rw [hxeq, map_smul, submoduleAsSymGroupAlgebraModule_smul_def,
          RingHom.id_apply, symGroupAlgHomToImage_smul_val] }

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in
set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 400000 in

/-- Two simple invariant subspaces with the same permutation character are linearly equivalent over the commutant algebra. -/
theorem Auxiliary.nonempty_linearEquiv_of_simple_character_eq
    (S S' : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) n))
    [IsSimpleModule (↥(RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)) ↥S]
    [IsSimpleModule (↥(RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)) ↥S']
    (la : Nat.Partition n)
    (hS : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace ℂ ↥(S.restrictScalars ℂ)
          ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) n σ).toLinearMap.restrict
            (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
          RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n la σ)
    (hS' : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace ℂ ↥(S'.restrictScalars ℂ)
          ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) n σ).toLinearMap.restrict
            (p := S'.restrictScalars ℂ) (q := S'.restrictScalars ℂ)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S' σ hv)) =
          RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n la σ) :
    Nonempty (↥S ≃ₗ[↥(RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) n)] ↥S') := by
  letI := submoduleAsSymGroupAlgebraModule S
  letI := submoduleAsSymGroupAlgebraModule S'
  haveI := submoduleAsSymGroupAlgebra_isScalarTower S
  haveI := submoduleAsSymGroupAlgebra_isScalarTower S'
  haveI := submoduleAsSymGroupAlgebra_isSimpleModule S
  haveI := submoduleAsSymGroupAlgebra_isSimpleModule S'

  obtain ⟨μ, ⟨eS⟩⟩ := RepresentationTheory.SimpleModule.SubtypeRepresentation.exists_linearEquiv_to_subtype n ↥(S.restrictScalars ℂ)
  obtain ⟨μ', ⟨eS'⟩⟩ := RepresentationTheory.SimpleModule.SubtypeRepresentation.exists_linearEquiv_to_subtype n ↥(S'.restrictScalars ℂ)

  have hμ : μ = la := RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.eq_of_auxiliaryPartitionPermutationValue_eq n fun σ =>
    (trace_restrictedSymGroupAction_eq_of_spechtIso S μ eS σ).symm.trans (hS σ)
  have hμ' : μ' = la := RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.eq_of_auxiliaryPartitionPermutationValue_eq n fun σ =>
    (trace_restrictedSymGroupAction_eq_of_spechtIso S' μ' eS' σ).symm.trans (hS' σ)
  have hμμ' : μ = μ' := hμ.trans hμ'.symm
  subst hμμ'

  exact ⟨transferToSymGroupImageEquiv S S' (eS.trans eS'.symm)⟩

end SpechtBridge




private theorem youngSymEndomorphism_normalized_isProj
    (k' : Type*) [Field k'] (N : ℕ) (lam : Fin N → ℕ)
    (α : k') (hα : α ≠ 0)
    (hα_sq : partitionSymmetrizer k' (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer k' (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer k' (∑ i, lam i) (partitionOfTuple N lam)) :
    LinearMap.IsProj (schurSubmodule k' N lam) (α⁻¹ • symmetrizerEndomorphism k' N lam) where
  map_mem x := by
    simp only [LinearMap.smul_apply, schurSubmodule, LinearMap.mem_range]
    exact ⟨α⁻¹ • x, by rw [map_smul]⟩
  map_id x hx := by
    simp only [LinearMap.smul_apply]
    rw [symmetrizerEndomorphism_apply_of_mem k' N lam α hα_sq x hx]
    rw [smul_smul, inv_mul_cancel₀ hα, one_smul]


private theorem youngSymEndomorphism_normalized_isIdempotent
    (k' : Type*) [Field k'] (N : ℕ) (lam : Fin N → ℕ)
    (α : k') (hα : α ≠ 0)
    (hα_sq : partitionSymmetrizer k' (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer k' (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer k' (∑ i, lam i) (partitionOfTuple N lam)) :
    IsIdempotentElem (α⁻¹ • symmetrizerEndomorphism k' N lam) :=
  (youngSymEndomorphism_normalized_isProj k' N lam α hα hα_sq).isIdempotentElem


set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 80000 in

private theorem trace_normalized_youngSym_eq_finrank
    (N : ℕ) (lam : Fin N → ℕ)
    (α : ℚ) (hα : α ≠ 0)
    (hα_sq : partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam)) :
    LinearMap.trace ℚ _ (α⁻¹ • symmetrizerEndomorphism ℚ N lam) =
      (Module.finrank ℚ (schurSubmodule ℚ N lam) : ℚ) := by
  letI : Module.Free ℚ (schurSubmodule ℚ N lam) :=
    Module.Free.of_divisionRing ℚ _
  letI : AddCommGroup (LinearMap.ker (α⁻¹ • symmetrizerEndomorphism ℚ N lam)) :=
    { Module.addCommMonoidToAddCommGroup ℚ with
      toAddCommMonoid := (LinearMap.ker (α⁻¹ • symmetrizerEndomorphism ℚ N lam)).addCommMonoid }
  letI : Module.Free ℚ (LinearMap.ker (α⁻¹ • symmetrizerEndomorphism ℚ N lam)) :=
    Module.Free.of_divisionRing ℚ _
  exact (youngSymEndomorphism_normalized_isProj ℚ N lam α hα hα_sq).trace




/-- The finitely supported multiplicity function counting how often each value occurs in a finite map. -/
def fiberCount (N : ℕ) {n : ℕ} (f : Fin n → Fin N) : Fin N →₀ ℕ where
  toFun i := (Finset.univ.filter (fun j => f j = i)).card
  support := Finset.univ.filter (fun i => 0 < (Finset.univ.filter (fun j => f j = i)).card)
  mem_support_toFun i := by simp [Finset.card_pos, Finset.filter_nonempty_iff]


/-- A product of variables indexed by a finite map is the monomial whose exponents count the fibers of that map. -/
lemma prod_X_eq_monomial_count (N : ℕ) {n : ℕ} (f : Fin n → Fin N) :
    ∏ j : Fin n, (MvPolynomial.X (f j) : MvPolynomial (Fin N) ℚ) =
      MvPolynomial.monomial (fiberCount N f) 1 := by

  rw [← Finset.prod_fiberwise_of_maps_to (g := f) (fun _ _ => Finset.mem_univ _)]

  have hfiber : ∀ i ∈ Finset.univ (α := Fin N),
      ∏ j ∈ Finset.univ.filter (fun k => f k = i),
        (MvPolynomial.X (f j) : MvPolynomial (Fin N) ℚ) =
      MvPolynomial.X i ^ (Finset.univ.filter (fun k => f k = i)).card := by
    intro i _
    rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
        Finset.prod_const]
  rw [Finset.prod_congr rfl hfiber]

  symm
  rw [MvPolynomial.monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [fiberCount]


private lemma coeff_monomial_one (N : ℕ) (w μ : Fin N →₀ ℕ) :
    (MvPolynomial.monomial w (1 : ℚ)).coeff μ = if w = μ then 1 else 0 := by
  simp [MvPolynomial.coeff_monomial]


private lemma permTracePoly_coeff_eq_card (N : ℕ) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (μ : Fin N →₀ ℕ) :
    (RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial N σ).coeff μ =
      ((Finset.univ.filter fun f : Fin n → Fin N =>
        (∀ j, f (σ j) = f j) ∧ fiberCount N f = μ).card : ℚ) := by
  unfold RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial
  rw [MvPolynomial.coeff_sum]

  simp_rw [prod_X_eq_monomial_count, coeff_monomial_one]

  rw [Finset.sum_boole, Nat.cast_inj]

  rw [Finset.filter_filter]


/-- The pure-tensor basis of a tensor power, indexed by functions between finite types. -/
noncomputable abbrev piTensorProductBasis (k' : Type*) [Field k'] (N n : ℕ) :=
  (_root_.Basis.piTensorProduct (R := k') (fun _ : Fin n => Pi.basisFun k' (Fin N)))


private lemma symGroupAction_tensorStdBasis (k' : Type*) [Field k'] (N n : ℕ)
    (σ : Equiv.Perm (Fin n)) (f : Fin n → Fin N) :
    (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k' (Fin N → k') n σ) (piTensorProductBasis k' N n f) =
      piTensorProductBasis k' N n (f ∘ σ.symm) := by
  simp only [piTensorProductBasis, _root_.Basis.piTensorProduct_apply, RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv,
    PiTensorProduct.reindex_tprod, Function.comp, Pi.basisFun_apply]


private lemma youngSym_diagonal_entry (k' : Type*) [Field k'] (N : ℕ) (lam : Fin N → ℕ)
    (f : Fin (∑ i, lam i) → Fin N) :
    (piTensorProductBasis k' N (∑ i, lam i)).repr
      (symmetrizerEndomorphism k' N lam (piTensorProductBasis k' N (∑ i, lam i) f)) f =
    ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (∑ i, lam i)) => ∀ j, f (σ j) = f j),
      partitionSymmetrizer k' (∑ i, lam i) (partitionOfTuple N lam) σ := by
  set c := partitionSymmetrizer k' (∑ i, lam i) (partitionOfTuple N lam)

  have hE : symmetrizerEndomorphism k' N lam =
      c.coeff.sum (fun σ a => a •
        (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k' (Fin N → k') (∑ i, lam i) σ).toLinearMap) := by
    unfold symmetrizerEndomorphism RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction
    rw [MonoidAlgebra.lift_apply]
    rfl
  rw [hE, Finsupp.sum]
  simp only [← LinearEquiv.coe_toLinearMap]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearEquiv.coe_toLinearMap, map_sum, map_smul,
    Finsupp.coe_smul, Pi.smul_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply]

  conv_lhs =>
    arg 2; ext x
    rw [show (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k' (Fin N → k') (∑ i, lam i) x) ((piTensorProductBasis k' N (∑ i, lam i)) f) =
      piTensorProductBasis k' N (∑ i, lam i) (f ∘ x.symm) from symGroupAction_tensorStdBasis k' N (∑ i, lam i) x f]

  simp only [Module.Basis.repr_self, Finsupp.single_apply]

  simp only [smul_eq_mul, Finset.sum_filter]

  rw [← Finset.sum_subset (Finset.subset_univ c.coeff.support)]
  · congr 1; ext σ


    have hiff : f ∘ σ.symm = f ↔ ∀ j, f (σ j) = f j := by
      constructor
      · intro h j
        have : (f ∘ σ.symm) (σ j) = f (σ j) := congr_fun h (σ j)
        simp [Function.comp_apply] at this
        exact this.symm
      · intro h
        funext j
        simp only [Function.comp_apply]
        exact h (σ.symm j) |>.symm.trans (by simp [Equiv.apply_symm_apply])
    split_ifs with h1 h2 h2
    · ring
    · exact absurd (hiff.mp h1) h2
    · exact absurd (hiff.mpr h2) h1
    · ring
  · intro σ _ hmem
    simp only [Finsupp.mem_support_iff, not_not] at hmem
    simp [hmem]

omit [CharZero k] in

private lemma diagUnit_mulVecLin_basisFun (N : ℕ) (i : Fin N) (t : kˣ)
    (m : Fin N) :
    Matrix.mulVecLin (R := k) (diagonalUnit k N i t).val (Pi.basisFun k (Fin N) m) =
      (Function.update (1 : Fin N → k) i (t : k)) m • Pi.basisFun k (Fin N) m := by
  simp only [diagonalUnit, Matrix.mulVecLin_apply, Pi.basisFun_apply]
  rw [Matrix.mulVec_single (M := (Matrix.diagonal (Function.update (1 : Fin N → k) i (t : k))))]
  simp only [
    Function.update_apply, Pi.one_apply]
  ext x
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hm : m = i <;> by_cases hx : x = m <;> simp_all

omit [CharZero k] in
/-- A coordinate diagonal unit acts on a pure-tensor basis vector by the corresponding coordinate-count power. -/
lemma tensorPowerRepresentation_apply_basis (N n : ℕ) (i : Fin N) (t : kˣ)
    (f : Fin n → Fin N) :
    (tensorPowerRepresentation k N n (diagonalUnit k N i t)) (piTensorProductBasis k N n f) =
      ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) •
        piTensorProductBasis k N n f := by

  change PiTensorProduct.map (fun _ => Matrix.mulVecLin (diagonalUnit k N i t).val)
      (piTensorProductBasis k N n f) =
    ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) •
      piTensorProductBasis k N n f
  simp only [piTensorProductBasis, _root_.Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    diagUnit_mulVecLin_basisFun k N i t]
  rw [(PiTensorProduct.tprod k).map_smul_univ
    (fun j => (Function.update (1 : Fin N → k) i (t : k)) (f j))
    (fun j => Pi.basisFun k (Fin N) (f j))]
  congr 1

  simp only [Function.update_apply, Pi.one_apply]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]




private lemma tensorWeight_comp_equiv {N n : ℕ} (f : Fin n → Fin N)
    (σ : Equiv.Perm (Fin n)) :
    fiberCount N (f ∘ σ) = fiberCount N f := by
  ext i
  simp only [fiberCount, Finsupp.coe_mk, Function.comp]
  have h : Finset.univ.filter (fun j => f (σ j) = i) =
      (Finset.univ.filter (fun j => f j = i)).map σ.symm.toEmbedding := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro h; exact ⟨σ j, h, σ.symm_apply_apply j⟩
    · rintro ⟨a, ha, rfl⟩; rwa [σ.apply_symm_apply]
  rw [h, Finset.card_map]


private lemma repr_symGroupAction {N n : ℕ}
    (k' : Type*) [Field k'] (σ : Equiv.Perm (Fin n)) (v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k' (Fin N → k') n)
    (g : Fin n → Fin N) :
    (piTensorProductBasis k' N n).repr
      ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k' (Fin N → k') n σ) v) g =
    (piTensorProductBasis k' N n).repr v (g ∘ σ) := by
  set B := piTensorProductBasis k' N n

  have h : (Finsupp.lapply g).comp (B.repr.toLinearMap.comp
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k' (Fin N → k') n σ).toLinearMap) =
    (Finsupp.lapply (g ∘ σ)).comp B.repr.toLinearMap := by
    apply B.ext
    intro f
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Finsupp.lapply_apply]
    rw [symGroupAction_tensorStdBasis k' N _ σ f]
    rw [B.repr_self, Finsupp.single_apply, B.repr_self, Finsupp.single_apply]
    simp only [Equiv.comp_symm_eq]
  exact LinearMap.ext_iff.mp h v


private lemma sum_swap_weight_youngSym (N : ℕ) (lam : Fin N → ℕ)
    (μ : Fin N →₀ ℕ) :
    ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℚ) *
          ((Finset.univ.filter fun f : Fin (∑ i, lam i) → Fin N =>
            (∀ j, f (σ j) = f j) ∧ fiberCount N f = μ).card : ℚ) =
    ∑ f ∈ Finset.univ.filter (fun f : Fin (∑ i, lam i) → Fin N => fiberCount N f = μ),
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (∑ i, lam i)) => ∀ j, f (σ j) = f j),
        (partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℚ) := by

  conv_lhs =>
    arg 2; ext σ
    rw [show (partitionSymmetrizer ℚ _ (partitionOfTuple N lam) σ : ℚ) *
          ((Finset.univ.filter fun f : Fin (∑ i, lam i) → Fin N =>
            (∀ j, f (σ j) = f j) ∧ fiberCount N f = μ).card : ℚ) =
        ∑ f ∈ Finset.univ.filter (fun f : Fin (∑ i, lam i) → Fin N =>
            (∀ j, f (σ j) = f j) ∧ fiberCount N f = μ),
          (partitionSymmetrizer ℚ _ (partitionOfTuple N lam) σ : ℚ) from by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]]

  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  congr 1; ext f
  by_cases hf : fiberCount N f = μ
  · simp only [hf, and_true, if_true]
  · simp only [hf, and_false, if_false, Finset.sum_const_zero]


private lemma weight_restricted_diag_sum (N : ℕ) (lam : Fin N → ℕ) (μ : Fin N →₀ ℕ) :
    ∑ f ∈ Finset.univ.filter (fun f : Fin (∑ i, lam i) → Fin N => fiberCount N f = μ),
      (piTensorProductBasis ℚ N (∑ i, lam i)).repr
        (symmetrizerEndomorphism ℚ N lam (piTensorProductBasis ℚ N (∑ i, lam i) f)) f =
    ∑ f ∈ Finset.univ.filter (fun f : Fin (∑ i, lam i) → Fin N => fiberCount N f = μ),
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (∑ i, lam i)) => ∀ j, f (σ j) = f j),
        (partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℚ) := by
  apply Finset.sum_congr rfl
  intro f _
  exact youngSym_diagonal_entry ℚ N lam f

omit [CharZero k] in

/-- In the pure-tensor basis, a coordinate diagonal action scales each coordinate by the size of the corresponding fiber. -/
lemma repr_tensorPowerRepresentation_diagonalUnit (N n : ℕ) (i : Fin N) (t : kˣ)
    (g : Fin n → Fin N) (v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n) :
    (piTensorProductBasis k N n).repr (tensorPowerRepresentation k N n (diagonalUnit k N i t) v) g =
    ((t : k) ^ (Finset.univ.filter (fun j => g j = i)).card) *
      (piTensorProductBasis k N n).repr v g := by
  set B := piTensorProductBasis k N n

  have hbasis : ∀ f, B.repr (tensorPowerRepresentation k N n (diagonalUnit k N i t) (B f)) g =
      ((t : k) ^ (Finset.univ.filter (fun j => g j = i)).card) * B.repr (B f) g := by
    intro f
    rw [tensorPowerRepresentation_apply_basis k N n i t, LinearEquiv.map_smul, Finsupp.smul_apply,
      smul_eq_mul, B.repr_self, Finsupp.single_apply]
    by_cases hfg : f = g
    · subst hfg; simp
    · simp [hfg]

  set L := ((Finsupp.lapply g).comp B.repr.toLinearMap).comp
    (tensorPowerRepresentation k N n (diagonalUnit k N i t))
  set R := ((t : k) ^ (Finset.univ.filter (fun j => g j = i)).card) •
    ((Finsupp.lapply g).comp B.repr.toLinearMap)
  suffices L = R from LinearMap.ext_iff.mp this v
  apply B.ext; intro f
  simp only [L, R, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Finsupp.lapply_apply,
    LinearMap.smul_apply, smul_eq_mul]
  exact hbasis f


set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in

private lemma youngSym_repr_zero_of_ne_weight (k' : Type*) [Field k'] (N : ℕ) (lam : Fin N → ℕ)
    (f g : Fin (∑ i, lam i) → Fin N)
    (hne : fiberCount N g ≠ fiberCount N f) :
    (piTensorProductBasis k' N (∑ i, lam i)).repr
      (symmetrizerEndomorphism k' N lam (piTensorProductBasis k' N (∑ i, lam i) f)) g = 0 := by
  set B := piTensorProductBasis k' N (∑ i, lam i)



  set c := partitionSymmetrizer k' (∑ i, lam i) (partitionOfTuple N lam)
  have hE : symmetrizerEndomorphism k' N lam =
      c.coeff.sum (fun σ a => a • (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k' (Fin N → k') (∑ i, lam i) σ :
        RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k' (Fin N → k') (∑ i, lam i) →ₗ[k']
        RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k' (Fin N → k') (∑ i, lam i))) := by
    unfold symmetrizerEndomorphism RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction
    rw [MonoidAlgebra.lift_apply]; rfl
  rw [hE, Finsupp.sum, LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero; intro σ _
  simp only [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]


  change c σ * B.repr ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv k' (Fin N → k') (∑ i, lam i) σ) (B f)) g = 0

  rw [repr_symGroupAction k' σ (B f) g]

  rw [B.repr_self, Finsupp.single_apply]
  split_ifs with h
  ·
    exact absurd (by rw [h, tensorWeight_comp_equiv] : fiberCount N f = fiberCount N g).symm hne
  · ring


set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 1600000 in

set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 80000 in

private lemma finrank_glWeightSpace_eq_restricted_trace
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (hα : α ≠ 0)
    (hα_sq : partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam))
    (μ : Fin N →₀ ℕ) :
    (Module.finrank k (weightSpace k N (schurRepresentation k N lam) (fun i => μ i)) : ℚ) =
    α⁻¹ * ∑ f ∈ Finset.univ.filter (fun f : Fin (∑ i, lam i) → Fin N => fiberCount N f = μ),
      (piTensorProductBasis ℚ N (∑ i, lam i)).repr
        (symmetrizerEndomorphism ℚ N lam (piTensorProductBasis ℚ N (∑ i, lam i) f)) f := by
  set n := ∑ i, lam i
  set la := partitionOfTuple N lam
  set cZ := integralPartitionSymmetrizer n la
  set β : ℤ := (cZ * cZ) 1

  have hα_eq_β : α = (β : ℚ) := by
    have h1 : (MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℚ)) (cZ * cZ) =
        α • (MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℚ)) cZ := by
      rw [map_mul]; exact (partitionSymmetrizer_eq_map_int ℚ n la) ▸ hα_sq
    have h2 := congrArg (fun x => x.coeff 1) h1
    simp only [MonoidAlgebra.coeff_mapRingHom,
      MonoidAlgebra.coeff_smul_apply, smul_eq_mul, mul_comm α] at h2


    change α = ((cZ * cZ) 1 : ℤ)
    have h3 : (cZ 1 : ℚ) = 1 := by simp [cZ, integralPartitionSymmetrizer_coeff_one]
    change (↑((cZ * cZ) 1) : ℚ) = (↑(cZ 1) : ℚ) * α at h2
    rw [h3, one_mul] at h2; linarith

  have hZ : cZ * cZ = β • cZ := by
    ext σ
    have h_ℚ : (MonoidAlgebra.mapRingHom _ (Int.castRingHom ℚ)) (cZ * cZ) =
        (β : ℚ) • (MonoidAlgebra.mapRingHom _ (Int.castRingHom ℚ)) cZ := by
      rw [map_mul, ← hα_eq_β]; exact (partitionSymmetrizer_eq_map_int ℚ n la) ▸ hα_sq
    have h2 := congrArg (fun x => x.coeff σ) h_ℚ
    simp only [MonoidAlgebra.coeff_mapRingHom,
      MonoidAlgebra.coeff_smul_apply, smul_eq_mul] at h2
    rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul]


    change (↑((cZ * cZ) σ) : ℚ) = ↑β * (↑(cZ σ) : ℚ) at h2
    exact_mod_cast h2

  have hcK_sq : partitionSymmetrizer k n la * partitionSymmetrizer k n la =
      (β : k) • partitionSymmetrizer k n la := by
    rw [partitionSymmetrizer_eq_map_int k n la, ← map_mul, hZ, map_zsmul,
      ← Int.cast_smul_eq_zsmul k]
  have hE_sq := symmetrizerEndomorphism_sq k N lam (β : k) hcK_sq
  have hβ_ne : (β : ℤ) ≠ 0 := by
    intro h; apply hα; rw [hα_eq_β, h, Int.cast_zero]
  have hβ_k_ne : (β : k) ≠ 0 := Int.cast_ne_zero.mpr hβ_ne

  set B := piTensorProductBasis k N n
  set E_k := symmetrizerEndomorphism k N lam
  set wt_μ := Finset.univ.filter (fun f : Fin n → Fin N => fiberCount N f = μ)
  set I_μ : Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n) :=
    ∑ f ∈ wt_μ, LinearMap.smulRight (B.coord f) (B f)

  have hI_basis : ∀ g : Fin n → Fin N,
      I_μ (B g) = if fiberCount N g = μ then B g else 0 := by
    intro g
    simp only [I_μ, LinearMap.sum_apply, LinearMap.smulRight_apply]


    have hcoord : ∀ f, (B.coord f) (B g) = if g = f then 1 else 0 := by
      intro f; change (B.repr (B g)) f = _; rw [B.repr_self, Finsupp.single_apply]
    split_ifs with hg
    · rw [Finset.sum_eq_single g]
      · rw [hcoord, if_pos rfl, one_smul]
      · intro f _ hfg; rw [hcoord, if_neg (Ne.symm hfg), zero_smul]
      · intro hg'; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩) hg'
    · apply Finset.sum_eq_zero; intro f hf
      have hfg : g ≠ f := fun h => hg (h ▸ (Finset.mem_filter.mp hf).2)
      rw [hcoord, if_neg hfg, zero_smul]

  have hI_idem : I_μ * I_μ = I_μ := by
    apply B.ext; intro g
    change I_μ (I_μ (B g)) = I_μ (B g)
    rw [hI_basis]; split_ifs with h <;> simp [hI_basis, h]

  have hI_Ek : ∀ g, I_μ (E_k (B g)) = if fiberCount N g = μ then E_k (B g) else 0 := by
    intro g

    conv_lhs => rw [(B.sum_repr (E_k (B g))).symm]
    simp only [map_sum, map_smul, hI_basis]

    split_ifs with hg
    ·
      conv_rhs => rw [(B.sum_repr (E_k (B g))).symm]
      apply Finset.sum_congr rfl; intro h _
      split_ifs with hh
      · rfl
      ·
        rw [youngSym_repr_zero_of_ne_weight k N lam g h
          (fun heq => hh (heq.trans hg))]; simp
    ·
      apply Finset.sum_eq_zero; intro h _
      split_ifs with hh
      ·
        rw [youngSym_repr_zero_of_ne_weight k N lam g h
          (fun heq => hg (heq.symm.trans hh))]; simp
      · simp

  have hcomm : E_k * I_μ = I_μ * E_k := by
    apply B.ext; intro g
    change E_k (I_μ (B g)) = I_μ (E_k (B g))
    rw [hI_basis, hI_Ek]
    split_ifs with h <;> simp

  set Φ := (β : k)⁻¹ • (E_k * I_μ : Module.End k _) with hΦ_def
  have hΦ_idem : IsIdempotentElem Φ := by
    have h1 : ∀ v, E_k (I_μ (E_k (I_μ v))) = (β : k) • (E_k (I_μ v)) := by
      intro v

      have hc := LinearMap.ext_iff.mp hcomm (I_μ v)
      change E_k (I_μ (I_μ v)) = I_μ (E_k (I_μ v)) at hc
      rw [← hc, show I_μ (I_μ v) = I_μ v from LinearMap.ext_iff.mp hI_idem v]
      exact LinearMap.ext_iff.mp hE_sq (I_μ v)
    rw [IsIdempotentElem]; show Φ * Φ = Φ; rw [hΦ_def]
    apply LinearMap.ext; intro w
    change (β : k)⁻¹ • E_k (I_μ ((β : k)⁻¹ • E_k (I_μ w))) = (β : k)⁻¹ • E_k (I_μ w)
    rw [map_smul, map_smul, h1, smul_smul, smul_smul]
    congr 1; field_simp

  have hweight_supp : ∀ (v : schurSubmodule k N lam),
      v ∈ weightSpace k N (schurRepresentation k N lam) (fun i => (μ i : ℕ)) →
      ∀ g : Fin n → Fin N, fiberCount N g ≠ μ →
      B.repr (v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n) g = 0 := by
    intro ⟨v, hv_im⟩ hv_wt g hg
    obtain ⟨i, hi⟩ : ∃ i : Fin N, fiberCount N g i ≠ μ i := by
      by_contra h; push Not at h; exact hg (DFunLike.ext _ _ h)
    obtain ⟨t, ht⟩ := exists_unit_pow_ne_pow k hi

    have h1 : weightSpace k N (schurRepresentation k N lam) (fun i => (μ i : ℕ)) ≤
        ⨅ (s : kˣ), LinearMap.ker
          ((schurRepresentation k N lam).ρ (diagonalUnit k N i s) -
            ((s : k) ^ (μ i : ℕ)) • LinearMap.id) := iInf_le _ i
    have h2 : ⨅ (s : kˣ), LinearMap.ker
        ((schurRepresentation k N lam).ρ (diagonalUnit k N i s) -
          ((s : k) ^ (μ i : ℕ)) • LinearMap.id) ≤
        LinearMap.ker ((schurRepresentation k N lam).ρ (diagonalUnit k N i t) -
          ((t : k) ^ (μ i : ℕ)) • LinearMap.id) := iInf_le _ t
    have hker := h2 (h1 hv_wt)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hker
    have hval : tensorPowerRepresentation k N n (diagonalUnit k N i t) v = (t : k) ^ (μ i : ℕ) • v := by
      have := congr_arg Subtype.val hker

      exact this



    have h3a : B.repr (tensorPowerRepresentation k N n (diagonalUnit k N i t) v) g =
        (t : k) ^ (Finset.univ.filter fun j => g j = i).card * B.repr v g :=
      repr_tensorPowerRepresentation_diagonalUnit k N n i t g v
    have h3b : B.repr (tensorPowerRepresentation k N n (diagonalUnit k N i t) v) g =
        (t : k) ^ (μ i : ℕ) * B.repr v g := by
      rw [hval, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
    have h4 : ((t : k) ^ (Finset.univ.filter fun j => g j = i).card -
        (t : k) ^ (μ i : ℕ)) * B.repr v g = 0 := by
      rw [sub_mul, sub_eq_zero]; exact h3a.symm.trans h3b
    exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr ht)

  have hI_fix : ∀ v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n,
      (∀ g, fiberCount N g ≠ μ → B.repr v g = 0) → I_μ v = v := by
    intro v hsupp
    conv_lhs => rw [(B.sum_repr v).symm]
    conv_rhs => rw [(B.sum_repr v).symm]
    simp only [map_sum, map_smul, hI_basis]
    apply Finset.sum_congr rfl; intro g _
    split_ifs with hg
    · rfl
    · rw [hsupp g hg]; simp

  have h_map : Submodule.map (schurSubmodule k N lam).subtype
      (weightSpace k N (schurRepresentation k N lam) fun i => (μ i : ℕ)) = LinearMap.range Φ := by
    ext v; simp only [Submodule.mem_map, LinearMap.mem_range]; constructor
    ·
      rintro ⟨⟨w, hw_im⟩, hw_wt, rfl⟩
      have hIw : I_μ w = w := hI_fix w (hweight_supp ⟨w, hw_im⟩ hw_wt)
      have hEw := symmetrizerEndomorphism_apply_of_mem k N lam (β : k) hcK_sq w hw_im
      refine ⟨w, ?_⟩
      change (β : k)⁻¹ • E_k (I_μ w) = w
      rw [hIw, hEw, smul_smul, inv_mul_cancel₀ hβ_k_ne, one_smul]
    ·
      rintro ⟨w, rfl⟩

      have hv_im : Φ w ∈ schurSubmodule k N lam := by
        change (β : k)⁻¹ • E_k (I_μ w) ∈ LinearMap.range E_k
        exact ⟨(β : k)⁻¹ • I_μ w, by rw [map_smul]⟩

      have hIΦ : I_μ (Φ w) = Φ w := by
        change I_μ ((β : k)⁻¹ • E_k (I_μ w)) = (β : k)⁻¹ • E_k (I_μ w)
        rw [map_smul]; congr 1

        have hc := LinearMap.ext_iff.mp hcomm (I_μ w)
        change E_k (I_μ (I_μ w)) = I_μ (E_k (I_μ w)) at hc
        rw [← hc, show I_μ (I_μ w) = I_μ w from LinearMap.ext_iff.mp hI_idem w]


      have hval : ∀ i : Fin N, ∀ t : kˣ,
          tensorPowerRepresentation k N n (diagonalUnit k N i t) (Φ w) =
            (t : k) ^ (μ i : ℕ) • (Φ w) := by
        intro i t
        conv_lhs => rw [← B.sum_repr (Φ w)]
        conv_rhs => rw [← B.sum_repr (Φ w)]
        simp only [map_sum, map_smul, Finset.smul_sum]
        apply Finset.sum_congr rfl; intro g _
        by_cases hg : fiberCount N g = μ
        · have hB : tensorPowerRepresentation k N n (diagonalUnit k N i t) (B g) =
              (↑t : k) ^ (Finset.univ.filter (fun j => g j = i)).card • B g :=
            tensorPowerRepresentation_apply_basis k N n i t g
          rw [hB, smul_smul, smul_smul]
          congr 1
          have hcard : (Finset.univ.filter (fun j => g j = i)).card = μ i :=
            Finsupp.ext_iff.mp hg i
          rw [hcard, mul_comm]
        · have h0 : B.repr (Φ w) g = 0 := by
            have key : B.repr (I_μ (Φ w)) g = 0 := by
              simp only [I_μ, LinearMap.sum_apply, LinearMap.smulRight_apply]
              rw [map_sum, Finsupp.finsetSum_apply]
              apply Finset.sum_eq_zero; intro f hf
              rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
                B.repr_self, Finsupp.single_apply]
              split_ifs with hfg
              · exact absurd (hfg ▸ (Finset.mem_filter.mp hf).2) hg
              · ring
            rwa [hIΦ] at key
          simp [h0]

      have hv_wt : ⟨Φ w, hv_im⟩ ∈ weightSpace k N (schurRepresentation k N lam)
          (fun i => (μ i : ℕ)) := by
        rw [weightSpace]; simp only [Submodule.mem_iInf]; intro i t
        rw [LinearMap.mem_ker]
        have h := hval i t
        simp only [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply]
        apply Subtype.ext
        simp only [schurRepresentation, FDRep.of_ρ',
          Submodule.coe_smul_of_tower]
        exact h
      exact ⟨⟨Φ w, hv_im⟩, hv_wt, rfl⟩


  set D_ℤ : ℤ := ∑ f ∈ wt_μ,
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ j, f (σ j) = f j),
      integralPartitionSymmetrizer n la σ

  have hD_k : ∑ f ∈ wt_μ, B.repr (E_k (B f)) f = (D_ℤ : k) := by
    simp only [D_ℤ]; rw [Int.cast_sum]
    apply Finset.sum_congr rfl; intro f _
    rw [youngSym_diagonal_entry k N lam f, Int.cast_sum]
    apply Finset.sum_congr rfl; intro σ _
    rw [partitionSymmetrizer_eq_map_int k n la, MonoidAlgebra.coeff_mapRingHom]
    norm_cast

  have hD_ℚ : ∑ f ∈ wt_μ, (piTensorProductBasis ℚ N n).repr
      (symmetrizerEndomorphism ℚ N lam ((piTensorProductBasis ℚ N n) f)) f = (D_ℤ : ℚ) := by
    simp only [D_ℤ]; rw [Int.cast_sum]
    apply Finset.sum_congr rfl; intro f _
    rw [youngSym_diagonal_entry ℚ N lam f, Int.cast_sum]
    apply Finset.sum_congr rfl; intro σ _
    rw [partitionSymmetrizer_eq_map_int ℚ n la, MonoidAlgebra.coeff_mapRingHom]
    norm_cast

  suffices h_int : (Module.finrank k
      (weightSpace k N (schurRepresentation k N lam) fun i => (μ i : ℕ)) : ℤ) * β = D_ℤ by

    have h_ℚ := congr_arg (Int.cast (R := ℚ)) h_int
    push_cast at h_ℚ


    simp only [n] at hD_ℚ
    rw [hD_ℚ]

    have hαβ : (α : ℚ) = (β : ℚ) := by exact_mod_cast hα_eq_β
    rw [← h_ℚ, hαβ]; field_simp [hα]


  letI : AddCommGroup (LinearMap.range Φ) :=
    { Module.addCommMonoidToAddCommGroup k with
      toAddCommMonoid := (LinearMap.range Φ).addCommMonoid }
  letI : Module.Free k (LinearMap.range Φ) := Module.Free.of_divisionRing k _
  letI : AddCommGroup (LinearMap.ker Φ) :=
    { Module.addCommMonoidToAddCommGroup k with
      toAddCommMonoid := (LinearMap.ker Φ).addCommMonoid }
  letI : Module.Free k (LinearMap.ker Φ) := Module.Free.of_divisionRing k _
  have h_fr_eq : Module.finrank k (LinearMap.range Φ) =
      Module.finrank k (weightSpace k N (schurRepresentation k N lam) fun i => (μ i : ℕ)) := by
    rw [← h_map]; exact Submodule.finrank_map_subtype_eq _ _
  have h_trace_fr : LinearMap.trace k _ Φ =
      (Module.finrank k (weightSpace k N (schurRepresentation k N lam) fun i => (μ i : ℕ)) : k) := by
    rw [← h_fr_eq]; exact ((LinearMap.isProj_range_iff_isIdempotentElem Φ).mpr hΦ_idem).trace

  have h_trace_sum : LinearMap.trace k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n) Φ =
      (β : k)⁻¹ * ∑ f ∈ wt_μ, B.repr (E_k (B f)) f := by
    rw [LinearMap.trace_eq_matrix_trace k B]
    simp only [Matrix.trace, Matrix.diag]

    simp only [LinearMap.toMatrix_apply]

    have hΦ_expand : ∀ x, B.repr (Φ (B x)) x = (↑β)⁻¹ * B.repr (E_k (I_μ (B x))) x := by
      intro x; rw [hΦ_def, LinearMap.smul_apply, Module.End.mul_apply, map_smul,
        Finsupp.smul_apply, smul_eq_mul]
    conv_lhs => arg 2; ext x; rw [hΦ_expand x]
    rw [← Finset.mul_sum]

    have h_sum : ∑ x, B.repr (E_k (I_μ (B x))) x = ∑ f ∈ wt_μ, B.repr (E_k (B f)) f := by
      trans ∑ g : Fin n → Fin N,
        if fiberCount N g = μ then B.repr (E_k (B g)) g else 0
      · apply Finset.sum_congr rfl; intro g _
        rw [hI_basis]; split_ifs with h
        · rfl
        · simp [map_zero]
      · exact (Finset.sum_filter _ _).symm
    rw [h_sum]

  have h_combined : (Module.finrank k
      (weightSpace k N (schurRepresentation k N lam) fun i => (μ i : ℕ)) : k) =
      (β : k)⁻¹ * (D_ℤ : k) := by
    rw [← h_trace_fr]; exact h_trace_sum.trans (congr_arg _ hD_k)

  have h_k_eq : (Module.finrank k
      (weightSpace k N (schurRepresentation k N lam) fun i => (μ i : ℕ)) : k) * (β : k) =
      (D_ℤ : k) := by
    rw [h_combined]; field_simp [hβ_k_ne]

  have h_cast : ((Module.finrank k
      (weightSpace k N (schurRepresentation k N lam) fun i => (μ i : ℕ)) : ℤ) * β : k) =
      (D_ℤ : k) := by push_cast; exact h_k_eq
  exact_mod_cast h_cast

private lemma finrank_weight_eq_card_sum
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (hα : α ≠ 0)
    (hα_sq : partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam))
    (μ : Fin N →₀ ℕ) :
    (Module.finrank k (weightSpace k N (schurRepresentation k N lam) (fun i => μ i)) : ℚ) =
      α⁻¹ * ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℚ) *
          ((Finset.univ.filter fun f : Fin (∑ i, lam i) → Fin N =>
            (∀ j, f (σ j) = f j) ∧ fiberCount N f = μ).card : ℚ) := by

  rw [finrank_glWeightSpace_eq_restricted_trace k N lam hlam α hα hα_sq μ]

  rw [weight_restricted_diag_sum N lam μ]

  congr 1
  exact (sum_swap_weight_youngSym N lam μ).symm


private theorem weight_trace_coefficient_identity
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (hα : α ≠ 0)
    (hα_sq : partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam))
    (μ : Fin N →₀ ℕ) :
    (Module.finrank k (weightSpace k N (schurRepresentation k N lam) (fun i => μ i)) : ℚ) =
      α⁻¹ * ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℚ) *
          (RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial N σ).coeff μ := by
  rw [finrank_weight_eq_card_sum k N lam hlam α hα hα_sq μ]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact (permTracePoly_coeff_eq_card N σ μ).symm


/-- The character of the representation attached to a decreasing tuple has a power-sum expansion obtained from its partition symmetrizer. -/
theorem weightCharacter_schurRepresentation_eq_symmetrizerSum
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (hα : α ≠ 0)
    (hα_sq : partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam)) :
    weightCharacter k N (schurRepresentation k N lam) =
      α⁻¹ • ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℚ) •
          RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial N σ := by
  ext μ
  rw [coeff_weightCharacter]
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_sum]
  exact weight_trace_coefficient_identity k N lam hlam α hα hα_sq μ




/-- The partition of a finite cardinality given by the cycle lengths of a permutation. -/
noncomputable def cycleType {n : ℕ} (σ : Equiv.Perm (Fin n)) : Nat.Partition n where
  parts := RepresentationTheory.PermutationPolynomialAuxiliary.permutationNatMultiset n σ
  parts_pos hi := RepresentationTheory.PermutationPolynomialAuxiliary.permutationNatMultiset_pos σ _ hi
  parts_sum := RepresentationTheory.PermutationPolynomialAuxiliary.permutationNatMultiset_sum n σ


/-- The polynomial associated with a permutation is the power-sum polynomial indexed by its cycle type. -/
theorem permutationPowerSum_eq_cycleType {n : ℕ} (N : ℕ) (σ : Equiv.Perm (Fin n)) :
    RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial' N σ = MvPolynomial.psumPart (Fin N) ℚ (cycleType σ) := by
  unfold RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial' MvPolynomial.psumPart cycleType
  rfl


/-- Auxiliary combinatorial data associated with a decreasing tuple and having the tuple's total size. -/
def Auxiliary.partitionDataOfAntitone (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N (∑ i, lam i) where
  parts := lam
  parts_antitone := hlam
  sum_parts := rfl



set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in

private theorem monoidAlgebra_trace_mulLeft_eq'
    {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (c : MonoidAlgebra ℚ G) :
    LinearMap.trace ℚ _ (LinearMap.mulLeft ℚ c) =
      Fintype.card G * c 1 := by
  set b := MonoidAlgebra.basis G ℚ
  rw [LinearMap.trace_eq_matrix_trace ℚ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  have hdiag : ∀ σ : G, b.repr (LinearMap.mulLeft ℚ c (b σ)) σ = c 1 := by
    intro σ
    rw [LinearMap.mulLeft_apply, MonoidAlgebra.basis_apply]
    have hrepr : ∀ (x : MonoidAlgebra ℚ G) (g : G), b.repr x g = x g := fun _ _ => rfl
    rw [hrepr, MonoidAlgebra.coeff_mul_single_apply, mul_one, mul_inv_cancel]
  simp_rw [hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in

/-- A rational scalar expressing the square of a partition symmetrizer as a multiple of itself is nonzero. -/
theorem ne_zero_of_partitionSymmetrizer_sq_eq_smul
    (n : ℕ) (la : Nat.Partition n)
    (α : ℚ)
    (hα_sq : partitionSymmetrizer ℚ n la * partitionSymmetrizer ℚ n la =
      α • partitionSymmetrizer ℚ n la) :
    α ≠ 0 := by
  intro h0
  rw [h0, zero_smul] at hα_sq
  set c := partitionSymmetrizer ℚ n la with hc_def
  have hnil : IsNilpotent (LinearMap.mulLeft ℚ c) := by
    refine ⟨2, LinearMap.ext fun x => ?_⟩
    change (LinearMap.mulLeft ℚ c) ((LinearMap.mulLeft ℚ c) x) = 0
    simp only [LinearMap.mulLeft_apply, ← mul_assoc, hα_sq, zero_mul]
  have htr_nil := LinearMap.isNilpotent_trace_of_isNilpotent hnil
  rw [isNilpotent_iff_eq_zero] at htr_nil
  rw [monoidAlgebra_trace_mulLeft_eq'] at htr_nil
  have hone : c 1 = 1 := by
    rw [hc_def, partitionSymmetrizer_eq_map_int ℚ n la]
    simp [MonoidAlgebra.coeff_mapRingHom, integralPartitionSymmetrizer_coeff_one]
  rw [hone, mul_one] at htr_nil
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    (by rwa [Fintype.card_perm, Fintype.card_fin] at htr_nil)




private lemma youngSym_coeff_cast' (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (partitionSymmetrizer ℚ n la σ : ℂ) = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la σ := by
  rw [partitionSymmetrizer_eq_map_int ℚ n la, complexPartitionSymmetrizer_eq_map_int n la]
  simp only [MonoidAlgebra.coeff_mapRingHom]
  exact_mod_cast rfl


private lemma youngSym_sq_ℂ' (n : ℕ) (la : Nat.Partition n)
    (α : ℚ) (hα : partitionSymmetrizer ℚ n la * partitionSymmetrizer ℚ n la =
      α • partitionSymmetrizer ℚ n la) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la = (α : ℂ) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
  set cZ := integralPartitionSymmetrizer n la
  set β : ℤ := (cZ * cZ) 1
  set φ_ℚ := MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℚ)
  set φ_ℂ := MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℂ)
  have h_ℚ : partitionSymmetrizer ℚ n la = φ_ℚ cZ := partitionSymmetrizer_eq_map_int ℚ n la
  have h_ℂ : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la = φ_ℂ cZ := complexPartitionSymmetrizer_eq_map_int n la
  have hcZ1 : cZ 1 = 1 := integralPartitionSymmetrizer_coeff_one n la
  have hmul_ℚ : φ_ℚ (cZ * cZ) = α • φ_ℚ cZ := by rw [map_mul]; exact h_ℚ ▸ hα
  have hα_eq : α = (β : ℚ) := by
    have h1 := congrArg (fun x => x.coeff 1) hmul_ℚ
    simp only [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_smul_apply,
      smul_eq_mul, hcZ1, map_one, mul_one, φ_ℚ] at h1
    exact h1.symm
  have hZ : cZ * cZ = β • cZ := by
    ext σ
    have h1 := congrArg (fun x => x.coeff σ) hmul_ℚ
    simp only [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_smul_apply,
      smul_eq_mul, hα_eq, φ_ℚ] at h1
    have h2 : ((cZ * cZ) σ : ℚ) = ((β * cZ σ : ℤ) : ℚ) := by push_cast; exact h1
    have h3 : (cZ * cZ) σ = β * cZ σ := Int.cast_injective h2
    rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, h3]
  rw [h_ℂ, ← map_mul, hZ, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
  congr 1; exact_mod_cast hα_eq.symm

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 1600000 in


private def mulLeftOnSpecht' (n : ℕ) (c : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (la' : Nat.Partition n) :
    ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la') →ₗ[ℂ] ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la') :=
  LinearMap.codRestrict ((RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la').restrictScalars ℂ)
    ((LinearMap.mulLeft ℂ c).comp
      ((RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la').restrictScalars ℂ).subtype)
    (fun v => (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la').smul_mem c v.prop)

private lemma mulLeftOnSpecht_of' (n : ℕ) (la' : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    mulLeftOnSpecht' n (MonoidAlgebra.of ℂ _ σ) la' = RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism n la' σ := by
  ext ⟨m, hm⟩; rfl

private noncomputable def mulLeftOnSpechtLinear' (n : ℕ) (la' : Nat.Partition n) :
    RepresentationTheory.PartitionAuxiliary.natIndexedType n →ₗ[ℂ] (↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la') →ₗ[ℂ] ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la')) where
  toFun c := mulLeftOnSpecht' n c la'
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


private lemma sum_coeff_char_eq_trace' (n : ℕ) (la' : Nat.Partition n) (c : RepresentationTheory.PartitionAuxiliary.natIndexedType n) :
    ∑ σ : Equiv.Perm (Fin n), c σ * RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n la' σ =
      LinearMap.trace ℂ _ (mulLeftOnSpecht' n c la') := by
  symm
  have key : (LinearMap.trace ℂ _) (mulLeftOnSpecht' n c la') =
      ∑ σ ∈ c.coeff.support, c σ * RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n la' σ := by
    have hlin : mulLeftOnSpecht' n c la' = (mulLeftOnSpechtLinear' n la') c := rfl
    rw [hlin]
    simp_rw [RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue, ← mulLeftOnSpecht_of' n la']
    have hc : c = ∑ σ ∈ c.coeff.support,
        c σ • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ := by
      conv_lhs => rw [← MonoidAlgebra.sum_coeff_single c]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
    conv_lhs => rw [show (mulLeftOnSpechtLinear' n la') c =
        (mulLeftOnSpechtLinear' n la')
          (∑ σ ∈ c.coeff.support, c σ • MonoidAlgebra.of ℂ _ σ) from by rw [← hc]]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [map_smul, LinearMap.map_smul, smul_eq_mul]; rfl
  rw [key]
  apply Finset.sum_subset (Finset.subset_univ c.coeff.support)
  intro σ _ hσ
  have : c σ = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hσ
  simp [this]

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 1600000 in


private lemma mulLeft_youngSym_zero_of_ne' (n : ℕ) (la la' : Nat.Partition n) (hne : la ≠ la') :
    mulLeftOnSpecht' n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) la' = 0 := by
  by_contra hT
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la',
      mulLeftOnSpecht' n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) la' w₀ ≠ 0 := by
    by_contra hall; push Not at hall; exact hT (LinearMap.ext hall)
  set φ : RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la →ₗ[RepresentationTheory.PartitionAuxiliary.natIndexedType n] RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la' :=
    { toFun := fun v => ⟨(v : RepresentationTheory.PartitionAuxiliary.natIndexedType n) * (w₀ : RepresentationTheory.PartitionAuxiliary.natIndexedType n),
        (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la').smul_mem (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n) w₀.prop⟩
      map_add' := fun a b => Subtype.ext (add_mul (a : RepresentationTheory.PartitionAuxiliary.natIndexedType n) b w₀)
      map_smul' := fun a v => Subtype.ext (mul_assoc a (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n) w₀) }
  have hφ_ne : φ ≠ 0 := by
    intro h
    apply hw₀
    let e : RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la :=
      ⟨RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la, Submodule.subset_span rfl⟩
    have he := LinearMap.congr_fun h e
    apply Subtype.ext
    change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la * (w₀ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) = 0
    have hev := congrArg Subtype.val he
    change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la * (w₀ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) = 0 at hev
    exact hev
  haveI : IsSimpleModule (RepresentationTheory.PartitionAuxiliary.natIndexedType n) (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) :=
    RepresentationTheory.PartitionAuxiliary.partitionSubmodule_isSimpleModule n la
  haveI : IsSimpleModule (RepresentationTheory.PartitionAuxiliary.natIndexedType n) (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la') :=
    RepresentationTheory.PartitionAuxiliary.partitionSubmodule_isSimpleModule n la'
  have hφ_bij := LinearMap.bijective_of_ne_zero hφ_ne
  exact (RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra.isEmpty_linearEquiv_of_ne_partition n la la' hne).false (LinearEquiv.ofBijective φ hφ_bij)


private lemma youngSym_coeff_one' (n : ℕ) (la : Nat.Partition n) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) 1 = 1 := by
  rw [complexPartitionSymmetrizer_eq_map_int]
  simp [MonoidAlgebra.coeff_mapRingHom, integralPartitionSymmetrizer_coeff_one]


private lemma mul_mem_specht_proportional' (n : ℕ) (la : Nat.Partition n)
    (v : ↥(RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la)) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la * v.val =
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la * v.val) 1 • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
  classical
  set c := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp v.prop
  rw [smul_eq_mul] at ha
  obtain ⟨ℓ, hℓ⟩ := RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.exists_sign_fixed_sandwich_eq_smul n la
  have h_sandwich : ∀ x,
      c * x * c = ℓ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * (x * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)) • c := by
    intro x
    change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * x *
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) = _
    rw [show RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * x *
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) =
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * (x * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)) *
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la from by simp only [mul_assoc]]
    rw [hℓ]
  have hsand := h_sandwich a
  conv_lhs at hsand => rw [mul_assoc]
  conv_lhs => rw [show v.val = a * c from ha.symm, hsand]
  conv_rhs => rw [show v.val = a * c from ha.symm, hsand]
  congr 1
  rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, youngSym_coeff_one', mul_one]


private lemma trace_mulLeft_youngSym_eq' (n : ℕ) (la : Nat.Partition n)
    (α : ℂ) (_hα_ne : α ≠ 0)
    (hα_sq : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la = α • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) :
    LinearMap.trace ℂ _ (mulLeftOnSpecht' n (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) la) = α := by
  set c := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la with hc_def
  set V := RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la
  set T := mulLeftOnSpecht' n c la
  have hc_mem : c ∈ V := Submodule.subset_span rfl
  set e : V := ⟨c, hc_mem⟩
  let ι : ℂ →ₗ[ℂ] V := LinearMap.lsmul ℂ V |>.flip e
  let π : V →ₗ[ℂ] ℂ :=
    { toFun := fun v => (c * v.val) 1
      map_add' := fun x y => by simp [mul_add]
      map_smul' := fun r x => by
        change (c * (r • x.val)) 1 = r * (c * x.val) 1
        rw [Algebra.mul_smul_comm, MonoidAlgebra.coeff_smul_apply, smul_eq_mul] }
  have hT_eq : T = ι.comp π := by
    apply LinearMap.ext; intro ⟨v, hv⟩; apply Subtype.ext
    exact mul_mem_specht_proportional' n la ⟨v, hv⟩
  rw [hT_eq, LinearMap.trace_comp_comm']
  have h_comp : π.comp ι = α • LinearMap.id := by
    apply LinearMap.ext; intro x
    change (c * (x • c)) 1 = α * x
    rw [Algebra.mul_smul_comm, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    rw [hα_sq, MonoidAlgebra.coeff_smul_apply, smul_eq_mul,
      youngSym_coeff_one', mul_one, mul_comm]
  rw [h_comp]; simp [map_smul, LinearMap.trace_id, Module.finrank_self]


private theorem youngSym_trace_kronecker' (n : ℕ) (la la' : Nat.Partition n)
    (α : ℚ) (hα_sq : partitionSymmetrizer ℚ n la * partitionSymmetrizer ℚ n la =
      α • partitionSymmetrizer ℚ n la) :
    ∑ σ : Equiv.Perm (Fin n),
      (partitionSymmetrizer ℚ n la σ : ℂ) * RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n la' σ =
      if la = la' then (α : ℂ) else 0 := by
  conv_lhs => arg 2; ext σ; rw [youngSym_coeff_cast']
  have hα_ℂ := youngSym_sq_ℂ' n la α hα_sq
  have hα_ne : (α : ℂ) ≠ 0 := by exact_mod_cast ne_zero_of_partitionSymmetrizer_sq_eq_smul n la α hα_sq
  rw [sum_coeff_char_eq_trace']
  split_ifs with h
  · subst h; exact trace_mulLeft_youngSym_eq' n la (α : ℂ) hα_ne hα_ℂ
  · rw [mulLeft_youngSym_zero_of_ne' n la la' h, map_zero]




private theorem isIdempotentElem_eq_zero_of_trace_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    {e : V →ₗ[K] V} (he : IsIdempotentElem e)
    (htr : LinearMap.trace K V e = 0) :
    e = 0 := by
  have hproj : LinearMap.IsProj (LinearMap.range e) e :=
    LinearMap.IsIdempotentElem.isProj_range _ he
  have htr_eq : LinearMap.trace K V e = (Module.finrank K (LinearMap.range e) : K) :=
    hproj.trace
  rw [htr] at htr_eq
  have hfinrank_zero : Module.finrank K (LinearMap.range e) = 0 := by
    have h : ((Module.finrank K (LinearMap.range e) : ℕ) : K) = 0 := htr_eq.symm
    exact_mod_cast h
  rw [← LinearMap.range_eq_bot, ← Submodule.finrank_eq_zero]
  exact hfinrank_zero


private lemma youngSymmetrizerK_complex_eq (n : ℕ) (la : Nat.Partition n) :
    partitionSymmetrizer ℂ n la = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
  rw [partitionSymmetrizer_eq_map_int ℂ n la, complexPartitionSymmetrizer_eq_map_int n la]

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in




set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in

/-- A simple constituent indexed by a different partition is annihilated by the symmetrizer endomorphism. -/
theorem Auxiliary.restrict_symmetrizerEndomorphism_eq_zero_of_character_ne
    (N : ℕ) (lam : Fin N → ℕ)
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i)))
    [Module.Finite ℂ ↥(S.restrictScalars ℂ)]
    (la' : Nat.Partition (∑ i, lam i))
    (h_label : ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace ℂ ↥(S.restrictScalars ℂ)
            ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) (∑ i, lam i) σ).toLinearMap.restrict
              (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
              (fun _ hv =>
                mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
          RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (∑ i, lam i) la' σ)
    (h_ne : la' ≠ partitionOfTuple N lam) :
    (symmetrizerEndomorphism ℂ N lam).restrict
        (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
        (fun _ hv =>
          youngSymEndomorphism_mem_of_symGroupImage_submodule lam S hv) = 0 := by

  let f : ↥(S.restrictScalars ℂ) →ₗ[ℂ] ↥(S.restrictScalars ℂ) :=
    (symmetrizerEndomorphism ℂ N lam).restrict
      (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
      (fun _ hv =>
        youngSymEndomorphism_mem_of_symGroupImage_submodule lam S hv)
  change f = 0

  obtain ⟨α, hα_sq⟩ :=
    partitionSymmetrizer_sq_smul ℚ (∑ i, lam i) (partitionOfTuple N lam)
  have hα_ne : α ≠ 0 :=
    ne_zero_of_partitionSymmetrizer_sq_eq_smul _ (partitionOfTuple N lam) α hα_sq
  have hα_ℂ_ne : (α : ℂ) ≠ 0 := by exact_mod_cast hα_ne
  have hα_sq_ℂ :
      partitionSymmetrizer ℂ (∑ i, lam i) (partitionOfTuple N lam) *
        partitionSymmetrizer ℂ (∑ i, lam i) (partitionOfTuple N lam) =
      (α : ℂ) • partitionSymmetrizer ℂ (∑ i, lam i) (partitionOfTuple N lam) := by
    rw [youngSymmetrizerK_complex_eq]
    exact youngSym_sq_ℂ' _ _ α hα_sq

  have h_trace_f : LinearMap.trace ℂ _ f =
      ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer ℂ (∑ i, lam i) (partitionOfTuple N lam) σ) *
        LinearMap.trace ℂ _
          ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) (∑ i, lam i) σ).toLinearMap.restrict
            (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S σ hv)) :=
    Auxiliary.trace_symmetrizerEndomorphism_restrict N lam S

  have h_trace_eq_sum : LinearMap.trace ℂ _ f =
      ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer ℂ (∑ i, lam i) (partitionOfTuple N lam) σ) *
          RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (∑ i, lam i) la' σ := by
    rw [h_trace_f]
    exact Finset.sum_congr rfl fun σ _ => by rw [h_label σ]

  have h_trace_zero : LinearMap.trace ℂ _ f = 0 := by
    have h_coef_cast : ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer ℂ (∑ i, lam i) (partitionOfTuple N lam) σ : ℂ) =
          ((partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℚ) : ℂ) := by
      intro σ
      rw [youngSym_coeff_cast', ← youngSymmetrizerK_complex_eq]
    rw [h_trace_eq_sum]
    conv_lhs => arg 2; ext σ; rw [h_coef_cast σ]
    rw [youngSym_trace_kronecker' _ (partitionOfTuple N lam) la' α hα_sq,
        if_neg (fun h => h_ne h.symm)]

  have hf_sq : f * f = (α : ℂ) • f :=
    Auxiliary.restrict_symmetrizerEndomorphism_sq N lam S (α : ℂ) hα_sq_ℂ

  let g : ↥(S.restrictScalars ℂ) →ₗ[ℂ] ↥(S.restrictScalars ℂ) := (α : ℂ)⁻¹ • f
  have hg_idem : IsIdempotentElem g := by
    change ((α : ℂ)⁻¹ • f) * ((α : ℂ)⁻¹ • f) = (α : ℂ)⁻¹ • f
    rw [smul_mul_smul_comm, hf_sq, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hα_ℂ_ne, mul_one]

  have hg_tr_zero : LinearMap.trace ℂ _ g = 0 := by
    change LinearMap.trace ℂ _ ((α : ℂ)⁻¹ • f) = 0
    rw [LinearMap.map_smul, h_trace_zero, smul_zero]

  have hg_zero : g = 0 :=
    isIdempotentElem_eq_zero_of_trace_eq_zero
      (K := ℂ) (V := ↥(S.restrictScalars ℂ)) (e := g) hg_idem hg_tr_zero

  have hf_eq_smul_g : f = (α : ℂ) • g := by
    change f = (α : ℂ) • ((α : ℂ)⁻¹ • f)
    rw [smul_smul, mul_inv_cancel₀ hα_ℂ_ne, one_smul]
  rw [hf_eq_smul_g, hg_zero, smul_zero]






set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in
set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 400000 in

/-- The expected permutation character yields a nonzero scalar and a rank-one idempotent expressing the restricted symmetrizer action. -/
theorem Auxiliary.exists_rankOneProjection_of_character_eq
    (N : ℕ) (lam : Fin N → ℕ)
    (S : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i)))
    [Module.Finite ℂ ↥(S.restrictScalars ℂ)]
    (h_label : ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace ℂ ↥(S.restrictScalars ℂ)
            ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) (∑ i, lam i) σ).toLinearMap.restrict
              (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
              (fun _ hv =>
                mem_of_mem_symmetricInvariantSubmodule S σ hv)) =
          RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (∑ i, lam i) (partitionOfTuple N lam) σ) :
    ∃ (α : ℂ) (π : ↥(S.restrictScalars ℂ) →ₗ[ℂ] ↥(S.restrictScalars ℂ)),
      α ≠ 0 ∧ π * π = π ∧
      Module.finrank ℂ (LinearMap.range π) = 1 ∧
      (symmetrizerEndomorphism ℂ N lam).restrict
          (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
          (fun _ hv =>
            youngSymEndomorphism_mem_of_symGroupImage_submodule lam S hv) = α • π := by

  let f : ↥(S.restrictScalars ℂ) →ₗ[ℂ] ↥(S.restrictScalars ℂ) :=
    (symmetrizerEndomorphism ℂ N lam).restrict
      (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
      (fun _ hv =>
        youngSymEndomorphism_mem_of_symGroupImage_submodule lam S hv)

  obtain ⟨α, hα_sq⟩ :=
    partitionSymmetrizer_sq_smul ℚ (∑ i, lam i) (partitionOfTuple N lam)
  have hα_ne : α ≠ 0 :=
    ne_zero_of_partitionSymmetrizer_sq_eq_smul _ (partitionOfTuple N lam) α hα_sq
  have hα_ℂ_ne : (α : ℂ) ≠ 0 := by exact_mod_cast hα_ne
  have hα_sq_ℂ :
      partitionSymmetrizer ℂ (∑ i, lam i) (partitionOfTuple N lam) *
        partitionSymmetrizer ℂ (∑ i, lam i) (partitionOfTuple N lam) =
      (α : ℂ) • partitionSymmetrizer ℂ (∑ i, lam i) (partitionOfTuple N lam) := by
    rw [youngSymmetrizerK_complex_eq]
    exact youngSym_sq_ℂ' _ _ α hα_sq

  have h_trace_f : LinearMap.trace ℂ _ f =
      ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer ℂ (∑ i, lam i) (partitionOfTuple N lam) σ) *
        LinearMap.trace ℂ _
          ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (Fin N → ℂ) (∑ i, lam i) σ).toLinearMap.restrict
            (p := S.restrictScalars ℂ) (q := S.restrictScalars ℂ)
            (fun _ hv => mem_of_mem_symmetricInvariantSubmodule S σ hv)) :=
    Auxiliary.trace_symmetrizerEndomorphism_restrict N lam S

  have h_trace_eq_alpha : LinearMap.trace ℂ _ f = (α : ℂ) := by
    have h_coef_cast : ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (partitionSymmetrizer ℂ (∑ i, lam i) (partitionOfTuple N lam) σ : ℂ) =
          ((partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℚ) : ℂ) := by
      intro σ
      rw [youngSym_coeff_cast', ← youngSymmetrizerK_complex_eq]
    rw [h_trace_f]
    conv_lhs => arg 2; ext σ; rw [h_label σ, h_coef_cast σ]
    rw [youngSym_trace_kronecker' _ (partitionOfTuple N lam) (partitionOfTuple N lam) α hα_sq,
        if_pos rfl]

  have hf_sq : f * f = (α : ℂ) • f :=
    Auxiliary.restrict_symmetrizerEndomorphism_sq N lam S (α : ℂ) hα_sq_ℂ

  set π : ↥(S.restrictScalars ℂ) →ₗ[ℂ] ↥(S.restrictScalars ℂ) := (α : ℂ)⁻¹ • f with hπ_def

  have hπ_idem : π * π = π := by
    rw [hπ_def, smul_mul_smul_comm, hf_sq, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hα_ℂ_ne, mul_one]

  have hπ_proj : LinearMap.IsProj (LinearMap.range π) π :=
    { map_mem := fun x => LinearMap.mem_range_self π x
      map_id := fun x hx => by
        obtain ⟨y, rfl⟩ := hx
        exact LinearMap.congr_fun hπ_idem y }

  have hπ_trace : LinearMap.trace ℂ _ π = 1 := by
    rw [hπ_def, LinearMap.map_smul, h_trace_eq_alpha, smul_eq_mul, inv_mul_cancel₀ hα_ℂ_ne]

  letI : AddCommGroup (LinearMap.range π) :=
    { Module.addCommMonoidToAddCommGroup ℂ with
      toAddCommMonoid := (LinearMap.range π).addCommMonoid }
  letI : AddCommGroup π.ker :=
    { Module.addCommMonoidToAddCommGroup ℂ with
      toAddCommMonoid := π.ker.addCommMonoid }
  letI : Module.Free ℂ (LinearMap.range π) := Module.Free.of_divisionRing ℂ _
  letI : Module.Free ℂ π.ker := Module.Free.of_divisionRing ℂ _
  have hπ_rank : Module.finrank ℂ (LinearMap.range π) = 1 := by
    have h := @LinearMap.IsProj.trace ℂ inferInstance
      (↥(S.restrictScalars ℂ)) (S.restrictScalars ℂ).addCommGroup
      (S.restrictScalars ℂ).module (LinearMap.range π) π hπ_proj
      inferInstance inferInstance inferInstance inferInstance
    rw [hπ_trace] at h
    exact_mod_cast h.symm

  have hf_eq : f = (α : ℂ) • π := by
    rw [hπ_def, smul_smul, mul_inv_cancel₀ hα_ℂ_ne, one_smul]
  exact ⟨(α : ℂ), π, hα_ℂ_ne, hπ_idem, hπ_rank, hf_eq⟩




private lemma sortedParts_getD_eq_of_antitone
    (n : ℕ) (f : Fin n → ℕ) (hf : Antitone f) (i : Fin n) :
    ((auxiliaryPartitionNatList (partitionOfTuple n f)).getD i.val 0 : ℕ) = f i := by
  unfold auxiliaryPartitionNatList partitionOfTuple
  simp only [Fin.univ_val_map]


  have h_sorted : ((List.ofFn f).filter (0 < ·)).SortedGE := by
    rw [List.sortedGE_iff_pairwise]
    exact List.Pairwise.filter _ (List.sortedGE_ofFn_iff.mpr hf).pairwise




  have h_sort_eq : ((↑(List.ofFn f) : Multiset ℕ).filter (0 < ·)).sort (· ≥ ·) =
      (List.ofFn f).filter (0 < ·) := by
    rw [Multiset.filter_coe]
    have h_perm : ((↑((List.ofFn f).filter (0 < ·)) : Multiset ℕ).sort (· ≥ ·)).Perm
        ((List.ofFn f).filter (0 < ·)) :=
      Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)
    have h_sort_sorted : (↑((List.ofFn f).filter (0 < ·)) : Multiset ℕ).sort (· ≥ ·)
        |>.SortedGE := by
      rw [List.sortedGE_iff_pairwise]
      exact Multiset.pairwise_sort _ _
    exact h_perm.eq_of_sortedGE h_sort_sorted h_sorted
  rw [h_sort_eq]






  suffices h_filter_eq : ∀ (m : ℕ) (g : Fin m → ℕ), Antitone g →
      ∀ j : Fin m, ((List.ofFn g).filter (0 < ·)).getD j.val 0 = g j by
    exact h_filter_eq n f hf i
  intro m g hg j
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    rw [List.ofFn_succ]
    by_cases hg0 : 0 < g 0
    ·
      simp only [List.filter_cons, decide_eq_true_eq.mpr hg0, ↓reduceIte]
      cases j using Fin.cases with
      | zero => simp [List.getD]
      | succ j' =>
        simp only [List.getD]
        have hgs : Antitone (g ∘ Fin.succ) :=
          fun a b hab => hg (show Fin.succ a ≤ Fin.succ b from Fin.succ_le_succ_iff.mpr hab)
        exact ih (g ∘ Fin.succ) hgs j'
    ·
      push Not at hg0
      have hg0' : g 0 = 0 := Nat.le_zero.mp hg0
      simp only [List.filter_cons, show decide (0 < g 0) = false from
        decide_eq_false (not_lt.mpr hg0), Bool.false_eq_true, ↓reduceIte]

      have hall : ∀ k : Fin (m + 1), g k = 0 :=
        fun k => Nat.le_zero.mp (hg0' ▸ hg (Fin.zero_le k))

      have h_empty : List.filter (fun x => decide (0 < x))
          (List.ofFn (fun i : Fin m => g i.succ)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx; rw [List.mem_ofFn] at hx; obtain ⟨k, rfl⟩ := hx
        simp [hall k.succ]
      rw [h_empty]; simp [hall j]


private theorem alternantDet_eq_sign_mul_vandermondeProd' (N : ℕ) :
    (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det =
      ((Equiv.Perm.sign (@Fin.revPerm N) : ℤ) : MvPolynomial (Fin N) ℚ) *
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ) := by
  have h1 : RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N) =
      (Matrix.vandermonde (MvPolynomial.X : Fin N → MvPolynomial (Fin N) ℚ)).submatrix
        id (@Fin.revPerm N) := by
    ext i j
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix, Matrix.vandermonde, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents, Matrix.of_apply,
      Matrix.submatrix_apply, id, Fin.revPerm_apply]
    congr 2
    simp only [Fin.rev, Fin.val_mk]
    omega
  rw [h1, Matrix.det_permute', Matrix.det_vandermonde]


private lemma shiftedExps_eq_toFinsupp_add_rhoShift
    (n : ℕ) (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition n n) :
    Finsupp.equivFunOnFinite.symm (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase n bp.parts) =
      RepresentationTheory.PermutationPolynomialAuxiliary.partitionNatFinsupp (bp.sum_parts ▸ partitionOfTuple n bp.parts) + RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryFinsupp n := by

  have h_sorted : auxiliaryPartitionNatList (bp.sum_parts ▸ partitionOfTuple n bp.parts) =
      auxiliaryPartitionNatList (partitionOfTuple n bp.parts) := by

    have : ∀ (m k : ℕ) (h : m = k) (p : Nat.Partition m),
        auxiliaryPartitionNatList (h ▸ p) = auxiliaryPartitionNatList p := by
      intro m k h p; subst h; rfl
    exact this _ _ bp.sum_parts _
  ext i
  simp only [Finsupp.coe_add, Pi.add_apply,
    RepresentationTheory.PermutationPolynomialAuxiliary.partitionNatFinsupp, RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryFinsupp, RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase,
    Finsupp.coe_equivFunOnFinite_symm, h_sorted]
  congr 1
  exact (sortedParts_getD_eq_of_antitone n bp.parts bp.parts_antitone i).symm


private lemma map_psumPart (n : ℕ) (μ : Nat.Partition n) :
    MvPolynomial.map (algebraMap ℚ ℂ) (MvPolynomial.psumPart (Fin n) ℚ μ) =
      MvPolynomial.psumPart (Fin n) ℂ μ := by
  simp only [MvPolynomial.psumPart, MvPolynomial.psum]
  rw [map_multiset_prod]
  congr 1
  rw [Multiset.map_map]
  congr 1; ext m
  rw [Function.comp_apply, map_sum]
  congr 1; ext i
  simp [map_pow, MvPolynomial.map_X]


private lemma psumPart_fullCycleType_eq_cycleTypePsumProduct
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.psumPart (Fin n) ℂ (cycleType σ) =
      RepresentationTheory.PermutationPolynomialAuxiliary.permutationPolynomialAuxiliary n σ := by
  rw [RepresentationTheory.PermutationPolynomialAuxiliary.permutationPolynomialAuxiliary_eq_prod_psum]
  simp only [MvPolynomial.psumPart, cycleType]


private lemma map_vandermondeProd (n : ℕ) :
    MvPolynomial.map (algebraMap ℚ ℂ)
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) =
      RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPolynomial n := by
  simp only [RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPolynomial, map_prod, map_sub, MvPolynomial.map_X]

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in

private lemma charValue_eq_spechtModuleCharacter_of_eq
    (n : ℕ) (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition n n) (σ : Equiv.Perm (Fin n)) :
    (RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff n bp (cycleType σ) : ℂ) =
      RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n (bp.sum_parts ▸ partitionOfTuple n bp.parts) σ := by
  set la : Nat.Partition n := bp.sum_parts ▸ partitionOfTuple n bp.parts
  set μ := cycleType σ
  set e := Finsupp.equivFunOnFinite.symm (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase n bp.parts)
  set s := (Equiv.Perm.sign (@Fin.revPerm n) : ℤ)

  have hcast : (RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff n bp μ : ℂ) =
      MvPolynomial.coeff e (MvPolynomial.map (algebraMap ℚ ℂ)
        ((RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix n (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents n)).det *
          MvPolynomial.psumPart (Fin n) ℚ μ)) := by
    change (algebraMap ℚ ℂ) (RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff n bp μ) = _
    rw [RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff, MvPolynomial.coeff_map]
  rw [hcast]

  rw [alternantDet_eq_sign_mul_vandermondeProd' n]

  rw [show ((s : MvPolynomial (Fin n) ℚ) *
    ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) *
    MvPolynomial.psumPart (Fin n) ℚ μ =
    (s : MvPolynomial (Fin n) ℚ) *
    ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) *
    MvPolynomial.psumPart (Fin n) ℚ μ) from by ring]

  rw [map_mul, map_mul, map_psumPart, map_vandermondeProd]
  rw [show MvPolynomial.map (algebraMap ℚ ℂ) (s : MvPolynomial (Fin n) ℚ) =
    (s : MvPolynomial (Fin n) ℂ) from by simp only [map_intCast]]


  have hint : (s : MvPolynomial (Fin n) ℂ) = MvPolynomial.C (s : ℂ) := by
    simp only [MvPolynomial.C_apply]
    rfl
  rw [hint, MvPolynomial.C_mul', MvPolynomial.coeff_smul, smul_eq_mul]

  rw [show e = RepresentationTheory.PermutationPolynomialAuxiliary.partitionNatFinsupp la + RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryFinsupp n from
    shiftedExps_eq_toFinsupp_add_rhoShift n bp]

  rw [psumPart_fullCycleType_eq_cycleTypePsumProduct]

  have h515 := RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySignSmul_eq_coefficient n la σ
  rw [← h515, zsmul_eq_mul, ← mul_assoc]

  have hs : (s : ℂ) * (s : ℂ) = 1 := by
    have h1 := Int.units_mul_self (Equiv.Perm.sign (@Fin.revPerm n))

    have h2 : (s : ℤ) * (s : ℤ) = 1 := by
      change (↑(Equiv.Perm.sign Fin.revPerm) : ℤ) * ↑(Equiv.Perm.sign Fin.revPerm) = ↑(1 : ℤˣ)
      rw [← Units.val_mul, h1]
    exact_mod_cast h2
  rw [hs, one_mul]



private lemma sum_getD_eq_sum (l : List ℕ) (n : ℕ) (hlen : l.length ≤ n) :
    ∑ i : Fin n, l.getD i.val 0 = l.sum := by
  induction n generalizing l with
  | zero =>
    have := List.eq_nil_of_length_eq_zero (by omega : l.length = 0)
    subst this; rfl
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    cases l with
    | nil => simp
    | cons a t =>
      simp only [List.getD_cons_zero, List.sum_cons, Fin.val_zero]
      congr 1
      have hstep : ∀ i : Fin n, (a :: t).getD i.succ.val 0 = t.getD i.val 0 := by
        intro ⟨i, _⟩; simp
      simp_rw [hstep]
      exact ih t (by simpa using hlen)


private lemma getD_antitone_of_pairwise (l : List ℕ) (h : l.Pairwise (· ≥ ·)) :
    Antitone (fun i : Fin n => l.getD i.val 0) := by
  intro i j hij
  change l.getD j.val 0 ≤ l.getD i.val 0
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · by_cases hj : j.val < l.length
    · have hi : i.val < l.length := by omega
      rw [List.getD_eq_getElem (hn := hj), List.getD_eq_getElem (hn := hi)]
      exact List.pairwise_iff_get.mp h ⟨i.val, hi⟩ ⟨j.val, hj⟩ hlt
    · rw [List.getD_eq_default (hn := by omega)]
      exact Nat.zero_le _

private def canonicalBP (N n : ℕ) (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition n n where
  parts := fun i => (auxiliaryPartitionNatList (bp.sum_parts ▸ partitionOfTuple N bp.parts)).getD i.val 0
  parts_antitone := by
    set l := auxiliaryPartitionNatList (bp.sum_parts ▸ partitionOfTuple N bp.parts)
    exact getD_antitone_of_pairwise l (Multiset.pairwise_sort _ _)
  sum_parts := by
    set la := (bp.sum_parts ▸ partitionOfTuple N bp.parts)
    set l := auxiliaryPartitionNatList la
    have hpos : ∀ x ∈ l, 0 < x := by
      intro x hx
      apply la.parts_pos
      have h_sort := Multiset.sort_eq (r := (· ≥ ·)) la.parts
      rw [show la.parts.sort (· ≥ ·) = l from rfl] at h_sort
      exact h_sort ▸ Multiset.mem_coe.mpr hx
    have hlen : l.length ≤ n := by
      have hsum : l.sum = n := sortedParts_sum n la
      suffices h : ∀ (m : List ℕ), (∀ x ∈ m, 0 < x) → m.length ≤ m.sum by
        linarith [h l hpos]
      intro m hm
      induction m with
      | nil => exact Nat.zero_le _
      | cons a t iht =>
        simp only [List.length_cons, List.sum_cons]
        have ha := hm a (by simp)
        have := iht (fun x hx => hm x (by simp [hx]))
        omega
    rw [sum_getD_eq_sum l n hlen, sortedParts_sum]


private lemma canonicalBP_weightToPartition (N n : ℕ) (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    ((canonicalBP N n bp).sum_parts ▸ partitionOfTuple n (canonicalBP N n bp).parts :
      Nat.Partition n) =
    (bp.sum_parts ▸ partitionOfTuple N bp.parts : Nat.Partition n) := by
  set la := (bp.sum_parts ▸ partitionOfTuple N bp.parts)
  set l := auxiliaryPartitionNatList la
  have hrec : ∀ (m k : ℕ) (h : m = k) (p : Nat.Partition m), (h ▸ p).parts = p.parts := by
    intros m k h p; subst h; rfl
  apply Nat.Partition.ext
  rw [hrec _ _ (canonicalBP N n bp).sum_parts, hrec _ _ bp.sum_parts]



  have hpos : ∀ x ∈ l, 0 < x := by
    intro x hx
    exact la.parts_pos ((Multiset.sort_eq (r := (· ≥ ·)) la.parts) ▸
      Multiset.mem_coe.mpr hx)

  have hlen : l.length ≤ n := by
    have hsum : l.sum = n := sortedParts_sum n la
    suffices hl : ∀ (m : List ℕ), (∀ x ∈ m, 0 < x) → m.length ≤ m.sum by linarith [hl l hpos]
    intro m hm; induction m with
    | nil => exact Nat.zero_le _
    | cons a t ih =>
      simp only [List.length_cons, List.sum_cons]
      have := hm a (by simp); have := ih (fun x hx => hm x (by simp [hx])); omega




  suffices h_lhs : (partitionOfTuple n (canonicalBP N n bp).parts).parts = la.parts by
    rw [h_lhs]; rw [show la.parts = (partitionOfTuple N bp.parts).parts from
      (hrec _ _ bp.sum_parts (partitionOfTuple N bp.parts)).symm ▸ rfl]

  change (Finset.univ.val.map (fun i : Fin n => l.getD i.val 0)).filter (0 < ·) = la.parts
  rw [Fin.univ_val_map, Multiset.filter_coe]

  suffices h : (List.ofFn (fun i : Fin n => l.getD i.val 0)).filter (fun x => decide (0 < x)) = l by
    rw [h]; exact Multiset.sort_eq _ _

  suffices key : ∀ (m : ℕ) (ll : List ℕ), (∀ x ∈ ll, 0 < x) → ll.length ≤ m →
      (List.ofFn (fun i : Fin m => ll.getD i.val 0)).filter (fun x => decide (0 < x)) = ll by
    exact key n l hpos hlen
  intro m; induction m with
  | zero => intro ll _ hlen; simp [List.eq_nil_of_length_eq_zero (by omega : ll.length = 0)]
  | succ m ih =>
    intro ll hll hlen
    simp only [List.ofFn_succ, Fin.val_zero, List.filter_cons]
    cases ll with
    | nil =>
      simp only [List.getD_nil, List.ofFn_const, List.filter_replicate,
        show ¬ decide (0 < 0) = true from by simp]
      simp
    | cons a t =>
      simp only [List.getD_cons_zero]
      have ha : 0 < a := hll a (by simp)
      rw [show decide (0 < a) = true from decide_eq_true ha]
      simp only [ite_true]
      congr 1


      change (List.ofFn (fun i : Fin m => t.getD i.val 0)).filter (fun x => decide (0 < x)) = t
      exact ih t (fun x hx => hll x (by simp [hx]))
        (by simp only [List.length_cons] at hlen; omega)


private def FinPartition.dropLast (N n : ℕ) (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition (N + 1) n)
    (h0 : bp.parts (Fin.last N) = 0) : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n where
  parts i := bp.parts (i.castSucc)
  parts_antitone i j hij := bp.parts_antitone (Fin.castSucc_le_castSucc_iff.mpr hij)
  sum_parts := by
    have hsplit : ∑ i : Fin (N + 1), bp.parts i =
        (∑ i : Fin N, bp.parts i.castSucc) + bp.parts (Fin.last N) :=
      Fin.sum_univ_castSucc bp.parts
    rw [h0, add_zero] at hsplit
    linarith [bp.sum_parts]


private def FinPartition.extend {N n : ℕ}
    (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition (N + 1) n where
  parts i :=
    if h : (i : ℕ) < N then bp.parts ⟨i, h⟩ else 0
  parts_antitone := by
    intro i j hij
    simp only
    split_ifs with h1 h2
    · exact bp.parts_antitone hij
    · exfalso; omega
    · exact Nat.zero_le _
    · exact le_refl _
  sum_parts := by
    have : ∑ i : Fin (N + 1), (if h : (i : ℕ) < N then
        bp.parts ⟨i, h⟩ else 0) =
        ∑ i : Fin N, bp.parts i := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, lt_irrefl,
        dite_false, add_zero]
      congr 1; funext i; simp [i.isLt]
    rw [this, bp.sum_parts]

private lemma FinPartition.extend_last {N n : ℕ}
    (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    (FinPartition.extend bp).parts (Fin.last N) = 0 := by
  simp [extend, Fin.val_last]

private lemma FinPartition.extend_dropLast {N n : ℕ}
    (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    FinPartition.dropLast N n (FinPartition.extend bp) (FinPartition.extend_last bp) = bp := by
  have : ∀ (a b : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n),
      a.parts = b.parts → a = b := by
    intro ⟨_, _, _⟩ ⟨_, _, _⟩ h; simp_all
  apply this; funext i
  change (if h : (Fin.castSucc i : ℕ) < N then
    bp.parts ⟨↑(Fin.castSucc i), h⟩ else 0) = bp.parts i
  simp [Fin.val_castSucc, i.isLt]


private noncomputable def restrictLastVar (N : ℕ) :
    MvPolynomial (Fin (N + 1)) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  MvPolynomial.aeval (fun i : Fin (N + 1) =>
    if h : i.val < N then MvPolynomial.X (⟨i.val, h⟩ : Fin N) else 0)


private lemma coeff_restrictLastVar (N : ℕ) (p : MvPolynomial (Fin (N + 1)) ℚ)
    (e : Fin N →₀ ℕ) :
    (restrictLastVar N p).coeff e =
      p.coeff (Finsupp.equivFunOnFinite.symm (fun i : Fin (N + 1) =>
        if h : i.val < N then e ⟨i.val, h⟩ else 0)) := by

  set ext_e : (Fin N →₀ ℕ) → (Fin (N + 1) →₀ ℕ) :=
    fun g => Finsupp.equivFunOnFinite.symm (fun i =>
      if h : (i : ℕ) < N then g ⟨i.val, h⟩ else 0) with hext_def

  have hext_val : ∀ (g : Fin N →₀ ℕ) (i : Fin (N + 1)) (hi : (i : ℕ) < N),
      ext_e g i = g ⟨i.val, hi⟩ := by
    intro g i hi; simp [ext_e, Finsupp.equivFunOnFinite, hi]
  have hext_last : ∀ (g : Fin N →₀ ℕ), ext_e g (Fin.last N) = 0 := by
    intro g; simp [ext_e, Finsupp.equivFunOnFinite, Fin.val_last]

  suffices ∀ (q : MvPolynomial (Fin (N + 1)) ℚ) (g : Fin N →₀ ℕ),
      (restrictLastVar N q).coeff g = q.coeff (ext_e g) by
    exact this p e
  intro q
  induction q using MvPolynomial.induction_on with
  | C a =>
    intro g
    simp only [restrictLastVar, MvPolynomial.aeval_C]
    change MvPolynomial.coeff g (MvPolynomial.C a) = _
    rw [MvPolynomial.coeff_C, MvPolynomial.coeff_C]
    simp only [eq_comm (a := (0 : _ →₀ ℕ))]
    congr 1; ext1; constructor
    · rintro rfl; ext i; simp [ext_e, Finsupp.equivFunOnFinite]
    · intro h; ext j; have := DFunLike.congr_fun h (Fin.castSucc j)
      simp [ext_e, Finsupp.equivFunOnFinite, j.isLt] at this; exact this
  | add p q hp hq =>
    intro g; simp only [map_add, MvPolynomial.coeff_add, hp, hq]
  | mul_X p i hp =>
    intro g
    simp only [restrictLastVar] at hp ⊢
    rw [map_mul, MvPolynomial.aeval_X]
    by_cases hi : (i : ℕ) < N
    ·
      rw [dif_pos hi]
      simp only [MvPolynomial.coeff_mul_X', Finsupp.mem_support_iff]
      rw [show ext_e g i = g ⟨i.val, hi⟩ from hext_val g i hi]
      split_ifs with h
      ·
        rw [hp]; congr 1
        refine Finsupp.ext fun j => ?_

        rw [Finsupp.tsub_apply, Finsupp.single_apply]
        by_cases hj : (j : ℕ) < N
        · rw [hext_val _ j hj, hext_val g j hj, Finsupp.tsub_apply, Finsupp.single_apply]
          congr 1; simp only [Fin.ext_iff]
        · have hj_eq : j = Fin.last N := by ext; simp [Fin.val_last]; omega
          subst hj_eq
          rw [hext_last, hext_last]
          have : ¬(i = Fin.last N) := by intro h; simp [h, Fin.val_last] at hi
          simp [this]
      · rfl
    ·
      rw [dif_neg hi, mul_zero, MvPolynomial.coeff_zero]
      simp only [MvPolynomial.coeff_mul_X', Finsupp.mem_support_iff]
      have : ¬(ext_e g i ≠ 0) := by
        push Not
        have hi_eq : i = Fin.last N := by
          ext; simp only [Fin.val_last]; omega
        rw [hi_eq]; exact hext_last g
      simp [this]


private lemma restrictLastVar_alternantDet (N : ℕ) :
    restrictLastVar N (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix (N + 1) (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents (N + 1))).det =
      (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) *
        (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det := by

  rw [AlgHom.map_det]

  set R := (restrictLastVar N).mapMatrix (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix (N + 1) (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents (N + 1)))

  have hR_entry : ∀ (i : Fin (N + 1)) (j : Fin (N + 1)),
      R i j = if h : (i : ℕ) < N then
        (MvPolynomial.X (⟨i.val, h⟩ : Fin N)) ^ (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents (N + 1) j)
      else if (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents (N + 1) j) = 0 then 1 else 0 := by
    intro i j
    simp only [R, AlgHom.mapMatrix_apply, Matrix.map_apply, RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix, Matrix.of_apply,
      restrictLastVar, map_pow, MvPolynomial.aeval_X]
    split_ifs with hi hv
    · rfl
    · rw [hv]; simp
    · exact zero_pow hv

  have hR_last_j : ∀ j : Fin (N + 1), R (Fin.last N) j =
      if j = Fin.last N then 1 else 0 := by
    intro j
    rw [hR_entry]
    simp only [Fin.val_last, lt_irrefl, dite_false, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents]
    have key : N - (j : ℕ) = 0 ↔ j = Fin.last N := by
      constructor
      · intro h; ext; simp [Fin.val_last]; omega
      · intro h; simp [h, Fin.val_last]
    simp [key]

  rw [Matrix.det_succ_row R (Fin.last N)]

  have hterm : ∀ j : Fin (N + 1),
      (-1) ^ ((Fin.last N : ℕ) + (j : ℕ)) * R (Fin.last N) j *
        (R.submatrix (Fin.last N).succAbove j.succAbove).det =
      if j = Fin.last N then
        (-1) ^ ((Fin.last N : ℕ) + (Fin.last N : ℕ)) *
          (R.submatrix (Fin.last N).succAbove (Fin.last N).succAbove).det
      else 0 := by
    intro j
    rw [hR_last_j j]
    split_ifs with hj
    · subst hj; ring
    · ring
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

  have hsign : (-1 : MvPolynomial (Fin N) ℚ) ^ ((Fin.last N : ℕ) + (Fin.last N : ℕ)) = 1 := by
    simp [Fin.val_last, Even.neg_one_pow ⟨N, rfl⟩]
  rw [hsign, one_mul]




  have hsucc : ∀ (i : Fin N), (Fin.last N).succAbove i = Fin.castSucc i := by
    intro i; simp [Fin.succAbove, Fin.lt_def, Fin.val_last, i.isLt]




  have hminor_entry : ∀ (i j : Fin N),
      (R.submatrix (Fin.last N).succAbove (Fin.last N).succAbove) i j =
        MvPolynomial.X i * (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N) i j) := by
    intro i j
    simp only [Matrix.submatrix_apply, hsucc, hR_entry, Fin.val_castSucc, i.isLt, dif_pos]
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix, Matrix.of_apply, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents]
    have hi : (i : ℕ) < N := i.isLt
    have hj : (j : ℕ) < N := j.isLt
    have hfin : (⟨i.val, hi⟩ : Fin N) = i := Fin.ext rfl
    rw [hfin]
    have hexp : N + 1 - 1 - (j.castSucc : ℕ) = (N - 1 - (j : ℕ)) + 1 := by
      simp [Fin.val_castSucc]; omega
    rw [hexp, pow_succ']

  have hdet_minor :
      (R.submatrix (Fin.last N).succAbove (Fin.last N).succAbove).det =
        (∏ i : Fin N, MvPolynomial.X i) *
          (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det := by
    have : R.submatrix (Fin.last N).succAbove (Fin.last N).succAbove =
        Matrix.of (fun i j => MvPolynomial.X i *
          RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N) i j) := by
      funext i j; exact hminor_entry i j
    rw [this, Matrix.det_mul_column]
  exact hdet_minor


private lemma restrictLastVar_psum (N k : ℕ) (hk : k ≠ 0) :
    restrictLastVar N (MvPolynomial.psum (Fin (N + 1)) ℚ k) =
      MvPolynomial.psum (Fin N) ℚ k := by
  simp only [MvPolynomial.psum, restrictLastVar, map_sum, map_pow, MvPolynomial.aeval_X]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, dif_neg (lt_irrefl N), zero_pow hk, add_zero, Fin.val_castSucc]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi : (i : ℕ) < N := i.isLt
  simp [hi]


private lemma restrictLastVar_psumPart {n : ℕ} (N : ℕ) (μ : Nat.Partition n) :
    restrictLastVar N (MvPolynomial.psumPart (Fin (N + 1)) ℚ μ) =
      MvPolynomial.psumPart (Fin N) ℚ μ := by
  simp only [MvPolynomial.psumPart]
  rw [map_multiset_prod (restrictLastVar N), Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro k hk
  exact restrictLastVar_psum N k (μ.parts_pos hk).ne'


private lemma prod_X_eq_monomial_ones (N : ℕ) :
    (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun _ : Fin N => 1)) 1 := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  apply Finset.prod_congr rfl
  intro i _
  simp [Finsupp.equivFunOnFinite]

private lemma coeff_prod_X_mul (N : ℕ) (p : MvPolynomial (Fin N) ℚ) (e : Fin N →₀ ℕ) :
    ((∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) * p).coeff
      (e + Finsupp.equivFunOnFinite.symm (fun _ : Fin N => 1)) = p.coeff e := by
  set ones := Finsupp.equivFunOnFinite.symm (fun _ : Fin N => 1)
  rw [prod_X_eq_monomial_ones, add_comm]
  rw [MvPolynomial.coeff_monomial_mul, one_mul]

private lemma charValue_remove_trailing_zero (N n : ℕ)
    (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition (N + 1) n)
    (h0 : bp.parts (Fin.last N) = 0) (μ : Nat.Partition n) :
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff (N + 1) bp μ = RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N (FinPartition.dropLast N n bp h0) μ := by
  simp only [RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff]
  set p := (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix (N + 1) (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents (N + 1))).det *
    MvPolynomial.psumPart (Fin (N + 1)) ℚ μ
  set e_small := Finsupp.equivFunOnFinite.symm
    (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N (FinPartition.dropLast N n bp h0).parts)
  set ones := Finsupp.equivFunOnFinite.symm (fun _ : Fin N => 1)


  have hstep1 : MvPolynomial.coeff (e_small + ones) (restrictLastVar N p) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (fun i : Fin (N + 1) =>
        if h : (i : ℕ) < N then (e_small + ones) ⟨i.val, h⟩ else 0)) p :=
    coeff_restrictLastVar N p (e_small + ones)

  have hexp_eq : (Finsupp.equivFunOnFinite.symm (fun i : Fin (N + 1) =>
      if h : (i : ℕ) < N then (e_small + ones) ⟨i.val, h⟩ else 0)) =
      Finsupp.equivFunOnFinite.symm (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase (N + 1) bp.parts) := by
    apply Finsupp.ext; intro i
    change (if h : (i : ℕ) < N then (e_small + ones) ⟨i.val, h⟩ else 0) =
      RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase (N + 1) bp.parts i
    by_cases h : (i : ℕ) < N
    · simp only [dif_pos h, Finsupp.coe_add, Pi.add_apply]
      change RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N (FinPartition.dropLast N n bp h0).parts ⟨i.val, h⟩ + 1 =
        RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase (N + 1) bp.parts i
      simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase, FinPartition.dropLast]
      have : bp.parts (Fin.castSucc ⟨i.val, h⟩) = bp.parts i := by
        congr 1
      rw [this]; omega
    · simp only [dif_neg h]
      have hi_last : i = Fin.last N := Fin.ext (by simp [Fin.val_last]; omega)
      rw [hi_last]; simp [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase, h0, Fin.val_last]
  rw [hexp_eq] at hstep1
  rw [← hstep1]


  simp only [p, map_mul, restrictLastVar_alternantDet, restrictLastVar_psumPart, mul_assoc]

  rw [coeff_prod_X_mul]


private lemma charValue_extend_zero (N n : ℕ) (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n)
    (μ : Nat.Partition n) :
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N bp μ = RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff (N + 1) (FinPartition.extend bp) μ := by
  have h := charValue_remove_trailing_zero N n (FinPartition.extend bp) (FinPartition.extend_last bp) μ
  rw [FinPartition.extend_dropLast bp] at h
  exact h.symm


private lemma wtp_dropLast (N n : ℕ) (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition (N + 1) n)
    (h0 : bp.parts (Fin.last N) = 0) :
    ((FinPartition.dropLast N n bp h0).sum_parts ▸ partitionOfTuple N (FinPartition.dropLast N n bp h0).parts :
      Nat.Partition n) =
    (bp.sum_parts ▸ partitionOfTuple (N + 1) bp.parts : Nat.Partition n) := by
  have hrec : ∀ (m k : ℕ) (h : m = k) (p : Nat.Partition m), (h ▸ p).parts = p.parts := by
    intros; subst_vars; rfl
  apply Nat.Partition.ext
  rw [hrec, hrec]
  simp only [partitionOfTuple, FinPartition.dropLast, Fin.univ_val_map, Multiset.filter_coe]
  congr 1
  conv_rhs => rw [List.ofFn_succ' bp.parts, List.concat_eq_append, List.filter_append]
  simp [h0]


private lemma wtp_extend (N n : ℕ) (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) :
    ((FinPartition.extend bp).sum_parts ▸ partitionOfTuple (N + 1) (FinPartition.extend bp).parts :
      Nat.Partition n) =
    (bp.sum_parts ▸ partitionOfTuple N bp.parts : Nat.Partition n) := by
  have h := wtp_dropLast N n (FinPartition.extend bp) (FinPartition.extend_last bp)
  rw [FinPartition.extend_dropLast bp] at h
  exact h.symm


private lemma bp_trailing_zero_of_gt (N n : ℕ) (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n)
    (hN : N > n) :
    bp.parts (⟨N - 1, by omega⟩ : Fin N) = 0 := by
  by_contra h
  have hpos : 0 < bp.parts ⟨N - 1, by omega⟩ := Nat.pos_of_ne_zero h
  have hall : ∀ i : Fin N, 1 ≤ bp.parts i := fun i => by
    have hi := i.isLt
    have hle : i ≤ ⟨N - 1, by omega⟩ := by exact Fin.mk_le_mk.mpr (by omega)
    exact le_trans hpos (bp.parts_antitone hle)
  have hge : N ≤ ∑ i : Fin N, bp.parts i :=
    le_trans (by simp) (Finset.sum_le_sum fun i _ => hall i)
  linarith [bp.sum_parts]


private lemma antitone_eq_of_filter_pos_eq'
    (N : ℕ) (lam lam' : Fin N → ℕ)
    (hlam : Antitone lam) (hlam' : Antitone lam')
    (h : (Finset.univ.val.map lam).filter (0 < ·) =
         (Finset.univ.val.map lam').filter (0 < ·)) :
    lam = lam' := by
  have h_full : Finset.univ.val.map lam = Finset.univ.val.map lam' := by
    apply Multiset.ext'; intro a
    by_cases ha : 0 < a
    · have := congr_arg (Multiset.count a) h
      rwa [Multiset.count_filter_of_pos ha, Multiset.count_filter_of_pos ha] at this
    · push Not at ha; obtain rfl := Nat.le_zero.mp ha
      have hc : (Finset.univ.val.map lam).card = (Finset.univ.val.map lam').card := by simp
      have hfc := congr_arg Multiset.card h
      have key : ∀ (m : Multiset ℕ), Multiset.count 0 m = m.card - (m.filter (0 < ·)).card := by
        intro m
        have h_split := congr_arg Multiset.card (Multiset.filter_add_not (0 < ·) m)
        rw [Multiset.card_add] at h_split
        rw [Multiset.count_eq_card_filter_eq]
        have : Multiset.filter (fun a => 0 = a) m = Multiset.filter (fun a => ¬ 0 < a) m := by
          congr 1; ext a; simp [eq_comm]
        rw [this]; omega
      rw [key, key]; omega
  simp only [Fin.univ_val_map] at h_full
  have h_perm := Multiset.coe_eq_coe.mp h_full
  exact List.ofFn_injective
    (h_perm.eq_of_sortedGE (List.sortedGE_ofFn_iff.mpr hlam) (List.sortedGE_ofFn_iff.mpr hlam'))

private lemma weightToPartition_eq_iff'
    (N n : ℕ) (lam lam' : Fin N → ℕ)
    (hlam : Antitone lam) (hlam' : Antitone lam')
    (hsum : ∑ i, lam i = n) (hsum' : ∑ i, lam' i = n) :
    (hsum ▸ partitionOfTuple N lam : Nat.Partition n) =
      (hsum' ▸ partitionOfTuple N lam') ↔ lam = lam' := by
  constructor
  · intro h
    apply antitone_eq_of_filter_pos_eq' N lam lam' hlam hlam'
    have h1 := congr_arg Nat.Partition.parts h
    have hrec : ∀ (m k : ℕ) (heq : m = k) (p : Nat.Partition m),
        (heq ▸ p).parts = p.parts := by
      intros m k heq p; subst heq; rfl
    rw [hrec _ _ hsum, hrec _ _ hsum'] at h1
    exact h1
  · intro h; subst h; rfl



private lemma canonicalBP_eq_of_weightToPartition_eq
    (N₁ N₂ n : ℕ) (bp₁ : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N₁ n)
    (bp₂ : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N₂ n)
    (h : (bp₁.sum_parts ▸ partitionOfTuple N₁ bp₁.parts :
            Nat.Partition n) =
         (bp₂.sum_parts ▸ partitionOfTuple N₂ bp₂.parts :
            Nat.Partition n)) :
    canonicalBP N₁ n bp₁ = canonicalBP N₂ n bp₂ := by
  have hparts : (canonicalBP N₁ n bp₁).parts =
      (canonicalBP N₂ n bp₂).parts := by
    funext i
    change (auxiliaryPartitionNatList (bp₁.sum_parts ▸ partitionOfTuple N₁ bp₁.parts :
            Nat.Partition n)).getD i.val 0 =
         (auxiliaryPartitionNatList (bp₂.sum_parts ▸ partitionOfTuple N₂ bp₂.parts :
            Nat.Partition n)).getD i.val 0
    rw [h]
  have : ∀ (a b : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition n n), a.parts = b.parts → a = b := by
    intro ⟨_, _, _⟩ ⟨_, _, _⟩ h; simp_all
  exact this _ _ hparts





private lemma charValue_reduce_to_n (N n : ℕ) (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n)
    (μ : Nat.Partition n) :
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N bp μ = RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff n (canonicalBP N n bp) μ := by






  suffices key : ∀ (d : ℕ) (N' : ℕ) (bp' : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N' n) (μ' : Nat.Partition n),
      (N' - n) + (n - N') = d →
      RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N' bp' μ' = RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff n (canonicalBP N' n bp') μ' from
    key ((N - n) + (n - N)) N bp μ rfl
  intro d
  induction d with
  | zero =>
    intro N' bp' μ' hd
    have hNn : N' = n := by omega
    subst hNn

    suffices h : canonicalBP N' N' bp' = bp' by rw [h]
    have hext : ∀ (a b : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N' N'), a.parts = b.parts → a = b := by
      intro ⟨_, _, _⟩ ⟨_, _, _⟩ h; simp_all
    apply hext

    have hwtp := canonicalBP_weightToPartition N' N' bp'
    exact ((weightToPartition_eq_iff' N' N'
      (canonicalBP N' N' bp').parts bp'.parts
      (canonicalBP N' N' bp').parts_antitone bp'.parts_antitone
      (canonicalBP N' N' bp').sum_parts bp'.sum_parts).mp hwtp)
  | succ d ihd =>
    intro N' bp' μ' hd
    by_cases hlt : N' < n
    ·
      rw [charValue_extend_zero N' n bp' μ']
      rw [ihd (N' + 1) (FinPartition.extend bp') μ' (by omega)]
      congr 1
      exact canonicalBP_eq_of_weightToPartition_eq (N' + 1) N' n
        (FinPartition.extend bp') bp' (wtp_extend N' n bp')
    ·
      have hgt : N' > n := by omega
      obtain ⟨N'', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N' ≠ 0)
      have h0 := bp_trailing_zero_of_gt (N'' + 1) n bp' (by omega)
      have h0' : bp'.parts (Fin.last N'') = 0 := by

        convert h0 using 2
        simp [Fin.ext_iff]
      rw [charValue_remove_trailing_zero N'' n bp' h0' μ']
      rw [ihd N'' (FinPartition.dropLast N'' n bp' h0') μ' (by omega)]
      congr 1
      exact canonicalBP_eq_of_weightToPartition_eq N'' (N'' + 1) n
        (FinPartition.dropLast N'' n bp' h0') bp' (wtp_dropLast N'' n bp' h0')


private lemma charValue_stability
    (N₁ N₂ n : ℕ) (bp₁ : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N₁ n) (bp₂ : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N₂ n)
    (h : (bp₁.sum_parts ▸ partitionOfTuple N₁ bp₁.parts : Nat.Partition n) =
         (bp₂.sum_parts ▸ partitionOfTuple N₂ bp₂.parts : Nat.Partition n))
    (μ : Nat.Partition n) :
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N₁ bp₁ μ = RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N₂ bp₂ μ := by
  rw [charValue_reduce_to_n N₁ n bp₁ μ, charValue_reduce_to_n N₂ n bp₂ μ]
  congr 1
  exact canonicalBP_eq_of_weightToPartition_eq N₁ N₂ n bp₁ bp₂ h


/-- The rational cast of the auxiliary character value agrees with the corresponding permutation value. -/
theorem Auxiliary.cast_characterValue_eq
    (N : ℕ) (n : ℕ) (lam' : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n) (σ : Equiv.Perm (Fin n)) :
    (RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam' (cycleType σ) : ℂ) =
      RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n (lam'.sum_parts ▸ partitionOfTuple N lam'.parts) σ := by

  set bp_n := canonicalBP N n lam'
  have hstab := charValue_stability N n n lam' bp_n
    (by rw [canonicalBP_weightToPartition]) (cycleType σ)
  rw [hstab]

  have hbridge := charValue_eq_spechtModuleCharacter_of_eq n bp_n σ
  rw [hbridge]

  congr 1
  exact canonicalBP_weightToPartition N n lam'


private lemma antitone_eq_of_filter_pos_eq
    (N : ℕ) (lam lam' : Fin N → ℕ)
    (hlam : Antitone lam) (hlam' : Antitone lam')
    (h : (Finset.univ.val.map lam).filter (0 < ·) =
         (Finset.univ.val.map lam').filter (0 < ·)) :
    lam = lam' := by

  have h_full : Finset.univ.val.map lam = Finset.univ.val.map lam' := by
    apply Multiset.ext'; intro a
    by_cases ha : 0 < a
    · have := congr_arg (Multiset.count a) h
      rwa [Multiset.count_filter_of_pos ha, Multiset.count_filter_of_pos ha] at this
    · push Not at ha; obtain rfl := Nat.le_zero.mp ha
      have hc : (Finset.univ.val.map lam).card = (Finset.univ.val.map lam').card := by simp
      have hfc := congr_arg Multiset.card h
      have key : ∀ (m : Multiset ℕ), Multiset.count 0 m = m.card - (m.filter (0 < ·)).card := by
        intro m
        have h_split := congr_arg Multiset.card (Multiset.filter_add_not (0 < ·) m)
        rw [Multiset.card_add] at h_split
        rw [Multiset.count_eq_card_filter_eq]
        have : Multiset.filter (fun a => 0 = a) m = Multiset.filter (fun a => ¬ 0 < a) m := by
          congr 1; ext a; simp [eq_comm]
        rw [this]; omega
      rw [key, key]; omega



  simp only [Fin.univ_val_map] at h_full
  have h_perm := Multiset.coe_eq_coe.mp h_full
  exact List.ofFn_injective
    (h_perm.eq_of_sortedGE (List.sortedGE_ofFn_iff.mpr hlam) (List.sortedGE_ofFn_iff.mpr hlam'))

private lemma weightToPartition_eq_iff
    (N n : ℕ) (lam lam' : Fin N → ℕ)
    (_hlam : Antitone lam) (_hlam' : Antitone lam')
    (hsum : ∑ i, lam i = n) (hsum' : ∑ i, lam' i = n) :
    (hsum ▸ partitionOfTuple N lam : Nat.Partition n) =
      (hsum' ▸ partitionOfTuple N lam') ↔ lam = lam' := by
  constructor
  · intro h
    apply antitone_eq_of_filter_pos_eq N lam lam' _hlam _hlam'
    have h1 := congr_arg Nat.Partition.parts h
    have hrec : ∀ (m k : ℕ) (heq : m = k) (p : Nat.Partition m),
        (heq ▸ p).parts = p.parts := by
      intros m k heq p; subst heq; rfl
    rw [hrec _ _ hsum, hrec _ _ hsum'] at h1
    exact h1
  · intro h; subst h; rfl




/-- The symmetrizer-weighted character sum is its quasi-idempotence scalar on the matching partition data and zero otherwise. -/
theorem symmetrizer_character_sum
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (hα_sq : partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam))
    (lam' : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N (∑ i, lam i)) :
    ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
      (partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℚ) *
        RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam' (cycleType σ) =
      if lam'.parts = lam then α else 0 := by

  set la'_np : Nat.Partition (∑ i, lam i) := lam'.sum_parts ▸ partitionOfTuple N lam'.parts

  have h_trace := youngSym_trace_kronecker' (∑ i, lam i) (partitionOfTuple N lam)
    la'_np α hα_sq

  have h_bridge : ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
      (RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam' (cycleType σ) : ℂ) =
        RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (∑ i, lam i) la'_np σ :=
    fun σ => Auxiliary.cast_characterValue_eq N (∑ i, lam i) lam' σ

  have h_cond : (partitionOfTuple N lam = la'_np) ↔ (lam'.parts = lam) := by
    rw [weightToPartition_eq_iff N (∑ i, lam i) lam lam'.parts hlam lam'.parts_antitone rfl lam'.sum_parts]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

  have h_ℂ : ∀ σ, (partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℂ) *
      (RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam' (cycleType σ) : ℂ) =
      (partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℂ) *
        RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (∑ i, lam i) la'_np σ := by
    intro σ; congr 1; exact h_bridge σ
  have h_sum : (∑ σ, (partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℚ) *
      RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam' (cycleType σ) : ℂ) =
      if lam'.parts = lam then (α : ℂ) else 0 := by
    simp_rw [h_ℂ, h_trace]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (h_cond.mp h1) h2
    · exact absurd (h_cond.mpr h2) h1
    · rfl
  have hinj := (algebraMap ℚ ℂ).injective
  apply hinj
  convert h_sum using 1
  · push_cast; rfl
  · split_ifs <;> simp



set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 1600000 in

/-- The symmetrizer-weighted sum of permutation power sums is a nonzero scalar multiple of the associated symmetric polynomial. -/
theorem symmetrizer_powerSum_sum_eq_smul_schurPolynomial
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (_hα : α ≠ 0)
    (hα_sq : partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) *
      partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) =
      α • partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam)) :
    ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
      (partitionSymmetrizer ℚ (∑ i, lam i) (partitionOfTuple N lam) σ : ℚ) •
        RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial N σ = α • RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam := by
  set n := ∑ i, lam i with hn
  set la := partitionOfTuple N lam
  set c := partitionSymmetrizer ℚ n la
  set Δ := (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det
  set F := ∑ σ : Equiv.Perm (Fin n), c.coeff σ • RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial N σ

  have hΔ : Δ ≠ 0 := Auxiliary.det_ne_zero N
  apply mul_right_cancel₀ hΔ
  rw [smul_mul_assoc, RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase]


  rw [← sub_eq_zero]
  apply RepresentationTheory.SymmetricPolynomials.Alternant.eq_zero_of_alternating_coeff_strictAnti_eq_zero
  ·
    intro σ
    rw [map_sub, smul_sub]
    congr 1
    ·
      rw [map_mul, RepresentationTheory.SymmetricPolynomials.Alternant.rename_det_alternantMatrix]

      have hF_sym : (MvPolynomial.rename σ) F = F := by
        simp only [F, map_sum]
        apply Finset.sum_congr rfl
        intro τ _
        rw [AlgHom.map_smul_of_tower]
        congr 1
        rw [RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial_eq_auxiliaryPermutationPolynomial' N τ, permutationPowerSum_eq_cycleType N τ]
        exact (RepresentationTheory.SymmetricPolynomials.Alternant.psumPart_isSymmetric N (cycleType τ)) σ
      rw [hF_sym, mul_comm F (Equiv.Perm.sign σ • Δ), smul_mul_assoc, mul_comm]
    ·
      rw [AlgHom.map_smul_of_tower, RepresentationTheory.SymmetricPolynomials.Alternant.rename_det_alternantMatrix, smul_comm]
  ·
    intro e he
    rw [MvPolynomial.coeff_sub]

    rw [MvPolynomial.coeff_smul, smul_eq_mul]


    change MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) (F * Δ) -
      α * MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N (Auxiliary.partitionDataOfAntitone N lam hlam).parts)).det = 0
    rw [RepresentationTheory.SymmetricPolynomials.Alternant.coeff_det_alternantMatrix_of_strictAnti (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase_strictAnti (Auxiliary.partitionDataOfAntitone N lam hlam)) he]








    show MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) (F * Δ) -
      α * (if RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N (Auxiliary.partitionDataOfAntitone N lam hlam).parts = e then 1 else 0) = 0

    have hF_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) (F * Δ) =
        ∑ σ : Equiv.Perm (Fin n),
          c.coeff σ * MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
            (Δ * RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial N σ) := by
      show MvPolynomial.coeff _ (F * Δ) = _
      simp only [F, Finset.sum_mul, MvPolynomial.coeff_sum]
      apply Finset.sum_congr rfl; intro σ _
      rw [smul_mul_assoc, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm (RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial N σ) Δ]
    rw [hF_coeff]

    conv_lhs =>
      arg 1; arg 2; ext σ
      rw [RepresentationTheory.Auxiliary.PermutationPolynomials.auxiliaryPermutationPolynomial_eq_auxiliaryPermutationPolynomial' N σ, permutationPowerSum_eq_cycleType N σ]


    by_cases hbp : ∃ lam' : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n, RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam'.parts = e
    ·
      obtain ⟨lam', hlam'⟩ := hbp

      have h_cv : ∀ σ,
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
            (Δ * MvPolynomial.psumPart (Fin N) ℚ (cycleType σ)) =
          RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff N lam' (cycleType σ) := by
        intro σ; rw [← hlam']; rfl
      simp_rw [h_cv]

      have horth := symmetrizer_character_sum N lam hlam α hα_sq lam'
      rw [horth]


      simp only [Auxiliary.partitionDataOfAntitone]
      by_cases heq : lam'.parts = lam
      ·
        rw [if_pos heq, if_pos (by rw [← hlam']; congr 1; exact heq.symm), mul_one, sub_self]
      ·
        rw [if_neg heq]
        rw [if_neg (by intro h; exact heq (by
          have : RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam = e := h
          have : RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam = RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam'.parts := this.trans hlam'.symm
          funext j; have := congr_fun this j; simp [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase] at this; omega))]
        simp
    ·

      have hne : RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N (Auxiliary.partitionDataOfAntitone N lam hlam).parts ≠ e := by
        intro h; exact hbp ⟨Auxiliary.partitionDataOfAntitone N lam hlam, h⟩
      rw [if_neg hne, mul_zero, sub_zero]



      apply Finset.sum_eq_zero; intro σ _
      suffices h : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
          (Δ * MvPolynomial.psumPart (Fin N) ℚ (cycleType σ)) = 0 by
        rw [h, mul_zero]


      by_contra h'
      have h'' : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
          (Δ * MvPolynomial.psumPart (Fin N) ℚ (cycleType σ)) ≠ 0 := by
        exact fun heq => h' heq
      have hF := (RepresentationTheory.SymmetricPolynomials.Alternant.det_alternantMatrix_isHomogeneous (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).mul
        (RepresentationTheory.SymmetricPolynomials.Alternant.psumPart_isHomogeneous N (cycleType σ))
      have hd := hF h''
      have hweight : Finsupp.weight (1 : Fin N → ℕ) (Finsupp.equivFunOnFinite.symm e) =
          ∑ j : Fin N, e j := by
        simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      rw [hweight] at hd
      obtain ⟨lam', hlam'⟩ := RepresentationTheory.SymmetricPolynomials.Alternant.exists_finPartition_addStaircase_eq e he (by exact_mod_cast hd)
      exact hbp ⟨lam', hlam'⟩


/-- A weakly decreasing weight tuple gives a representation whose weight character is the associated symmetric polynomial. -/
@[source_ref "Chapter5/Discussion_computing_characters_of_L_lambda" (role := primary)]
theorem schurRepresentation_weightCharacter
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    weightCharacter k N (schurRepresentation k N lam) = RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam := by

  obtain ⟨α, hα_sq⟩ := partitionSymmetrizer_sq_smul ℚ (∑ i, lam i) (partitionOfTuple N lam)
  have hα : α ≠ 0 :=
    ne_zero_of_partitionSymmetrizer_sq_eq_smul _ (partitionOfTuple N lam) α hα_sq

  rw [weightCharacter_schurRepresentation_eq_symmetrizerSum k N lam hlam α hα hα_sq]

  rw [symmetrizer_powerSum_sum_eq_smul_schurPolynomial N lam hlam α hα hα_sq]

  rw [smul_smul, inv_mul_cancel₀ hα, one_smul]




/-- Multiplying the relevant weight character by the base alternant determinant yields the shifted alternant determinant. -/
theorem weightCharacter_mul_det_eq_alternantDet
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    weightCharacter k N (schurRepresentation k N lam) * (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det =
      (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam)).det := by
  rw [schurRepresentation_weightCharacter k N lam hlam, RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase]


/-- A weight-space dimension in the representation indexed by a decreasing tuple equals the matching coefficient of its symmetric polynomial. -/
theorem finrank_weightSpace_schurRepresentation
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (μ : Fin N →₀ ℕ) :
    (Module.finrank k (weightSpace k N (schurRepresentation k N lam) (fun i => μ i)) : ℚ) =
      (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam).coeff μ := by

  have h_poly : weightCharacter k N (schurRepresentation k N lam) = RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam := by


    have hΔ := Auxiliary.det_ne_zero N
    apply mul_right_cancel₀ hΔ
    rw [weightCharacter_mul_det_eq_alternantDet k N lam hlam,
        RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase]
  rw [← coeff_weightCharacter, h_poly]


/-- The weight character of the representation attached to a weakly decreasing tuple is its corresponding symmetric polynomial. -/
@[source_ref "Chapter5/Theorem5.22.1" (role := supporting)]
theorem weightCharacter_schurRepresentation_eq
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    weightCharacter k N (schurRepresentation k N lam) = RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam := by
  ext μ
  rw [coeff_weightCharacter, finrank_weightSpace_schurRepresentation k N lam hlam]




/-- The rational dimension expression attached to a tuple of nonnegative weights. -/
noncomputable def schurDimension (N : ℕ) (lam : Fin N → ℕ) : ℚ :=
  ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
    (((lam i : ℚ) - (lam j : ℚ)) + (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) /
      ((((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)))


/-- Evaluating a weight character at all variables equal to one sums the dimensions of its nonzero weight spaces. -/
theorem Auxiliary.eval_one_eq_weightMultiplicitySum (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    MvPolynomial.eval (fun _ => (1 : ℚ)) (weightCharacter k N M) =
      (finite_support_weightSpace k N M).toFinset.sum
        (fun μ => (Module.finrank k (weightSpace k N M (fun i => μ i)) : ℚ)) := by
  unfold weightCharacter
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one, MvPolynomial.eval_monomial]
  simp



omit [CharZero k] in

/-- The endomorphism induced on a tensor power by a coordinate diagonal unit is semisimple. -/
theorem isSemisimple_tensorPowerRepresentation_diagonalUnit (N n : ℕ) (i : Fin N) (u : kˣ) :
    Module.End.IsSemisimple (tensorPowerRepresentation k N n (diagonalUnit k N i u)) := by
  classical
  set D := tensorPowerRepresentation k N n (diagonalUnit k N i u) with hD
  set S : Finset k := (Finset.range (n + 1)).image (fun m => (u : k) ^ m) with hS
  set p : Polynomial k := ∏ s ∈ S, (Polynomial.X - Polynomial.C s) with hp
  have hsqfree : Squarefree p := by
    apply Polynomial.Separable.squarefree
    rw [hp]
    exact Polynomial.separable_prod_X_sub_C_iff'.mpr (fun x _ y _ h => h)
  have haeval : (Polynomial.aeval D) p = 0 := by
    refine (piTensorProductBasis k N n).ext (fun g => ?_)
    set c : ℕ := (Finset.univ.filter (fun j => g j = i)).card with hc
    have hev : D (piTensorProductBasis k N n g) = ((u : k) ^ c) • piTensorProductBasis k N n g := by
      rw [hD]; exact tensorPowerRepresentation_apply_basis k N n i u g
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul hev]
    have hcn : c ≤ n := by
      rw [hc]
      exact le_trans (Finset.card_filter_le _ _) (by simp [Finset.card_univ])
    have hmem : (u : k) ^ c ∈ S := by
      rw [hS]; exact Finset.mem_image.mpr ⟨c, Finset.mem_range.mpr (by omega), rfl⟩
    have heval : p.eval ((u : k) ^ c) = 0 := by
      rw [hp, Polynomial.eval_prod]
      exact Finset.prod_eq_zero hmem (by simp)
    rw [heval, zero_smul, LinearMap.zero_apply]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsqfree haeval

omit [CharZero k] in

/-- Every coordinate diagonal unit induces a semisimple endomorphism on the representation associated with a weight tuple. -/
theorem isSemisimple_schurRepresentation_diagonalUnit (N : ℕ) (lam : Fin N → ℕ) (i : Fin N) (t : kˣ) :
    Module.End.IsSemisimple ((schurRepresentation k N lam).ρ (diagonalUnit k N i t)) := by
  have hinvt : schurSubmodule k N lam ∈
      Module.End.invtSubmodule (tensorPowerRepresentation k N (∑ i, lam i) (diagonalUnit k N i t)) :=
    fun v hv => schurSubmodule_invariant k N lam (diagonalUnit k N i t) v hv
  have hss := (isSemisimple_tensorPowerRepresentation_diagonalUnit k N (∑ i, lam i) i t).restrict hinvt
  exact hss

set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in


/-- The dimension of a representation associated with a weakly decreasing tuple equals its weight character evaluated at one. -/
theorem finrank_schurRepresentation_eq_eval_one_weightCharacter (N : ℕ) (lam : Fin N → ℕ)
    (hlam : Antitone lam) :
    (Module.finrank k (schurRepresentation k N lam) : ℚ) =
      MvPolynomial.eval (fun _ => (1 : ℚ))
        (weightCharacter k N (schurRepresentation k N lam)) := by
  classical
  rw [Auxiliary.eval_one_eq_weightMultiplicitySum]
  set n := ∑ i, lam i with hn
  set s := (finite_support_weightSpace k N (schurRepresentation k N lam)).toFinset with hs

  set f : Fin N × kˣ → Module.End k (schurRepresentation k N lam) :=
    fun q => (schurRepresentation k N lam).ρ (diagonalUnit k N q.1 q.2) with hf
  have hcomm : ∀ q₁ q₂ : Fin N × kˣ, Commute (f q₁) (f q₂) :=
    fun q₁ q₂ => commute_rep_diagonalUnit k N (schurRepresentation k N lam) q₁.1 q₁.2 q₂.1 q₂.2
  have hfss : ∀ q : Fin N × kˣ, Module.End.IsFinitelySemisimple (f q) :=
    fun q => (isSemisimple_schurRepresentation_diagonalUnit k N lam q.1 q.2).isFinitelySemisimple

  set χ : (Fin N →₀ ℕ) → (Fin N × kˣ → k) := fun μ q => (q.2 : k) ^ (μ q.1) with hχ

  have hkey : ∀ μ : Fin N →₀ ℕ, weightSpace k N (schurRepresentation k N lam) (fun i => μ i) =
      ⨅ q : Fin N × kˣ, (f q).maxGenEigenspace (χ μ q) := by
    intro μ
    rw [iInf_prod, weightSpace]
    refine iInf_congr (fun i => iInf_congr (fun t => ?_))
    rw [(hfss (i, t)).maxGenEigenspace_eq_eigenspace (χ μ (i, t)), Module.End.eigenspace_def]
    rfl

  have h_mapsTo : ∀ (q₁ q₂ : Fin N × kˣ) (φ : k),
      Set.MapsTo (f q₁) ((f q₂).maxGenEigenspace φ) ((f q₂).maxGenEigenspace φ) :=
    fun q₁ q₂ φ =>
      @Module.End.mapsTo_maxGenEigenspace_of_comm k _ inferInstance inferInstance
        inferInstance (f q₂) (f q₁) (hcomm q₂ q₁) φ
  have h_indep0 := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f h_mapsTo
  have h_inj : Function.Injective χ := by
    intro μ₁ μ₂ heq
    ext i
    by_contra hi
    obtain ⟨t, ht⟩ := exists_unit_pow_ne_pow k hi
    exact ht (congr_fun heq (i, t))
  have h_indep_all :
      iSupIndep (fun μ : Fin N →₀ ℕ => weightSpace k N (schurRepresentation k N lam) (fun i => μ i)) := by
    have hrw : (fun μ : Fin N →₀ ℕ => weightSpace k N (schurRepresentation k N lam) (fun i => μ i)) =
        (fun c : (Fin N × kˣ → k) => ⨅ q, (f q).maxGenEigenspace (c q)) ∘ χ :=
      funext hkey
    rw [hrw]
    exact h_indep0.comp h_inj

  have h_span_all :
      ⨆ μ : Fin N →₀ ℕ, weightSpace k N (schurRepresentation k N lam) (fun i => μ i) = ⊤ := by
    refine top_unique ?_
    have htop :=
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        f (fun q₁ q₂ _ => hcomm q₁ q₂) (fun q => Module.End.iSup_maxGenEigenspace_eq_top (f q))
    rw [← htop]
    refine iSup_le (fun c => ?_)
    by_cases hEc : (⨅ q, (f q).maxGenEigenspace (c q)) = ⊥
    · rw [hEc]; exact bot_le
    · obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hEc

      have hev : ∀ q, f q v = c q • v := by
        intro q
        have hmem : v ∈ (f q).maxGenEigenspace (c q) := (Submodule.mem_iInf _).mp hv_mem q
        rw [(hfss q).maxGenEigenspace_eq_eigenspace (c q)] at hmem
        exact Module.End.mem_eigenspace_iff.mp hmem

      set ι : (schurRepresentation k N lam) →ₗ[k] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n :=
        Submodule.subtype (schurSubmodule k N lam) with hι
      have hint : ∀ (i : Fin N) (t : kˣ) (w : schurRepresentation k N lam),
          ι (f (i, t) w) = tensorPowerRepresentation k N n (diagonalUnit k N i t) (ι w) := by
        intro i t w
        simp only [hι, hf, schurRepresentation, FDRep.of_ρ']
        rfl
      have hι_inj : Function.Injective ι := Subtype.coe_injective
      have hcoe_ne : ι v ≠ 0 := fun h => hv_ne (hι_inj (by rw [h, map_zero]))
      obtain ⟨g₀, hg₀⟩ : ∃ g₀, (piTensorProductBasis k N n).repr (ι v) g₀ ≠ 0 := by
        by_contra h
        push Not at h
        exact hcoe_ne ((piTensorProductBasis k N n).repr.map_eq_zero_iff.mp (Finsupp.ext h))

      have hc_eq : c = χ (fiberCount N g₀) := by
        funext q
        obtain ⟨i, t⟩ := q
        have hcoeq : tensorPowerRepresentation k N n (diagonalUnit k N i t) (ι v) = c (i, t) • ι v := by
          have h1 := congrArg ι (hev (i, t))
          rw [map_smul, hint] at h1
          exact h1
        have hrepr := congrArg (fun w => (piTensorProductBasis k N n).repr w g₀) hcoeq
        simp only [repr_tensorPowerRepresentation_diagonalUnit, map_smul, Finsupp.coe_smul, Pi.smul_apply,
          smul_eq_mul] at hrepr

        have hcancel := mul_right_cancel₀ hg₀ hrepr
        change c (i, t) = (t : k) ^ ((fiberCount N g₀) i)
        rw [← hcancel]
        rfl
      rw [hc_eq, ← hkey (fiberCount N g₀)]
      exact le_iSup (fun μ : Fin N →₀ ℕ =>
        weightSpace k N (schurRepresentation k N lam) (fun i => μ i)) (fiberCount N g₀)

  have h_indep : iSupIndep
      (fun ν : ↥s => weightSpace k N (schurRepresentation k N lam) (fun i => (ν : Fin N →₀ ℕ) i)) :=
    h_indep_all.comp Subtype.coe_injective
  have h_span : ⨆ ν : ↥s,
      weightSpace k N (schurRepresentation k N lam) (fun i => (ν : Fin N →₀ ℕ) i) = ⊤ := by
    refine top_unique ?_
    rw [← h_span_all]
    refine iSup_le (fun μ => ?_)
    by_cases hμ : μ ∈ s
    · exact le_iSup (fun ν : ↥s =>
        weightSpace k N (schurRepresentation k N lam) (fun i => (ν : Fin N →₀ ℕ) i)) ⟨μ, hμ⟩
    · have hbot : weightSpace k N (schurRepresentation k N lam) (fun i => μ i) = ⊥ := by
        by_contra h
        exact hμ ((finite_support_weightSpace k N (schurRepresentation k N lam)).mem_toFinset.mpr h)
      rw [hbot]; exact bot_le

  have hInt : DirectSum.IsInternal
      (fun ν : ↥s => weightSpace k N (schurRepresentation k N lam) (fun i => (ν : Fin N →₀ ℕ) i)) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h_indep h_span
  have hfr : Module.finrank k (schurRepresentation k N lam) =
      ∑ ν : ↥s, Module.finrank k
        (weightSpace k N (schurRepresentation k N lam) (fun i => (ν : Fin N →₀ ℕ) i)) := by
    have e := LinearEquiv.ofBijective (DirectSum.coeLinearMap
      (fun ν : ↥s =>
        weightSpace k N (schurRepresentation k N lam) (fun i => (ν : Fin N →₀ ℕ) i))) hInt
    rw [← LinearEquiv.finrank_eq e, Module.finrank_directSum]
  rw [hfr, Nat.cast_sum]
  exact (Finset.sum_coe_sort s (fun μ =>
    (Module.finrank k (weightSpace k N (schurRepresentation k N lam) (fun i => μ i)) : ℚ))).symm ▸ rfl




private noncomputable def qFactor (a b : ℕ) : Polynomial ℚ :=
  (-(Polynomial.X : Polynomial ℚ) ^ b) *
    ∑ t ∈ Finset.range (a - b), (Polynomial.X : Polynomial ℚ) ^ t

private lemma qFactor_mul (a b : ℕ) (h : b ≤ a) :
    (Polynomial.X : Polynomial ℚ) ^ b - (Polynomial.X : Polynomial ℚ) ^ a
      = ((Polynomial.X : Polynomial ℚ) - 1) * qFactor a b := by
  have h1 : (∑ t ∈ Finset.range (a - b), (Polynomial.X : Polynomial ℚ) ^ t) *
      ((Polynomial.X : Polynomial ℚ) - 1) = (Polynomial.X : Polynomial ℚ) ^ (a - b) - 1 :=
    geom_sum_mul _ _
  have h2 : (Polynomial.X : Polynomial ℚ) ^ b * (Polynomial.X : Polynomial ℚ) ^ (a - b)
      = (Polynomial.X : Polynomial ℚ) ^ a := by rw [← pow_add]; congr 1; omega
  unfold qFactor
  symm
  calc ((Polynomial.X : Polynomial ℚ) - 1) *
          ((-(Polynomial.X : Polynomial ℚ) ^ b) *
            ∑ t ∈ Finset.range (a - b), (Polynomial.X : Polynomial ℚ) ^ t)
      = (-(Polynomial.X : Polynomial ℚ) ^ b) *
          ((∑ t ∈ Finset.range (a - b), (Polynomial.X : Polynomial ℚ) ^ t) *
            ((Polynomial.X : Polynomial ℚ) - 1)) := by ring
    _ = (-(Polynomial.X : Polynomial ℚ) ^ b) *
          ((Polynomial.X : Polynomial ℚ) ^ (a - b) - 1) := by rw [h1]
    _ = (Polynomial.X : Polynomial ℚ) ^ b -
          (Polynomial.X : Polynomial ℚ) ^ b * (Polynomial.X : Polynomial ℚ) ^ (a - b) := by ring
    _ = (Polynomial.X : Polynomial ℚ) ^ b - (Polynomial.X : Polynomial ℚ) ^ a := by rw [h2]

private lemma eval_one_qFactor (a b : ℕ) :
    Polynomial.eval 1 (qFactor a b) = -((a - b : ℕ) : ℚ) := by
  unfold qFactor
  rw [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X,
      one_pow, Polynomial.eval_geom_sum]
  simp


private lemma aeval_pow_alternant_det (N : ℕ) (e : Fin N → ℕ) :
    MvPolynomial.aeval (fun i : Fin N => (Polynomial.X : Polynomial ℚ) ^ (i : ℕ))
        (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e).det =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        ((Polynomial.X : Polynomial ℚ) ^ e j - (Polynomial.X : Polynomial ℚ) ^ e i) := by
  rw [AlgHom.map_det]
  rw [show (MvPolynomial.aeval
        (fun i : Fin N => (Polynomial.X : Polynomial ℚ) ^ (i : ℕ))).mapMatrix (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e)
      = Matrix.transpose (Matrix.vandermonde (fun k : Fin N => (Polynomial.X : Polynomial ℚ) ^ e k))
        from ?_]
  · rw [Matrix.det_transpose, Matrix.det_vandermonde]
  · ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix, Matrix.of_apply,
      map_pow, MvPolynomial.aeval_X, Matrix.transpose_apply, Matrix.vandermonde_apply]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]


private lemma prod_factor_X_sub_one (N : ℕ) (e : Fin N → ℕ)
    (hmono : ∀ i j : Fin N, i < j → e j ≤ e i) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        ((Polynomial.X : Polynomial ℚ) ^ e j - (Polynomial.X : Polynomial ℚ) ^ e i))
      = ((Polynomial.X : Polynomial ℚ) - 1) ^ (∑ i : Fin N, (Finset.Ioi i).card) *
          ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, qFactor (e i) (e j) := by
  have inner : ∀ i : Fin N,
      (∏ j ∈ Finset.Ioi i, ((Polynomial.X : Polynomial ℚ) - 1) * qFactor (e i) (e j))
        = ((Polynomial.X : Polynomial ℚ) - 1) ^ (Finset.Ioi i).card *
            ∏ j ∈ Finset.Ioi i, qFactor (e i) (e j) := by
    intro i
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj =>
      qFactor_mul (e i) (e j) (hmono i j (Finset.mem_Ioi.mp hj))]
  rw [Finset.prod_congr rfl fun i _ => inner i]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

private lemma eval_one_prod_qFactor (N : ℕ) (e : Fin N → ℕ) :
    Polynomial.eval 1 (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, qFactor (e i) (e j))
      = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (-((e i - e j : ℕ) : ℚ)) := by
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact eval_one_qFactor (e i) (e j)

private lemma eval_one_aeval_pow (N : ℕ) (p : MvPolynomial (Fin N) ℚ) :
    Polynomial.eval 1 (MvPolynomial.aeval
        (fun i : Fin N => (Polynomial.X : Polynomial ℚ) ^ (i : ℕ)) p)
      = MvPolynomial.eval (fun _ => (1 : ℚ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one, hp]


/-- Evaluating the symmetric polynomial of a decreasing tuple at one gives its rational dimension expression. -/
theorem eval_one_schurPolynomial (N : ℕ) (lam : Fin N → ℕ)
    (hlam : Antitone lam) :
    MvPolynomial.eval (fun _ => (1 : ℚ)) (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) = schurDimension N lam := by

  have hmono_delta : ∀ i j : Fin N, i < j → RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j ≤ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp hij
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents]; omega
  have hmono_eps : ∀ i j : Fin N, i < j → RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j ≤ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp hij
    have hlij : lam j ≤ lam i := hlam (le_of_lt hij)
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]; omega

  have hcast_delta : ∀ i j : Fin N, i < j →
      ((RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i - RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j : ℕ) : ℚ) = ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) := by
    intro i j hij
    have hle := hmono_delta i j hij
    have hi : (i : ℕ) ≤ N - 1 := Nat.le_sub_one_of_lt i.isLt
    have hj : (j : ℕ) ≤ N - 1 := Nat.le_sub_one_of_lt j.isLt
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents] at hle ⊢
    rw [Nat.cast_sub hle, Nat.cast_sub hi, Nat.cast_sub hj]; ring
  have hcast_eps : ∀ i j : Fin N, i < j →
      ((RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j : ℕ) : ℚ)
        = ((lam i : ℚ) - (lam j : ℚ)) + (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := by
    intro i j hij
    have hle := hmono_eps i j hij
    have hi : (i : ℕ) ≤ N - 1 := Nat.le_sub_one_of_lt i.isLt
    have hj : (j : ℕ) ≤ N - 1 := Nat.le_sub_one_of_lt j.isLt
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase] at hle ⊢
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_add, Nat.cast_sub hi, Nat.cast_sub hj]; ring

  have hmaster := congrArg
    (MvPolynomial.aeval (fun i : Fin N => (Polynomial.X : Polynomial ℚ) ^ (i : ℕ)))
    (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase N lam)
  rw [map_mul, aeval_pow_alternant_det, aeval_pow_alternant_det] at hmaster
  rw [prod_factor_X_sub_one N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam) hmono_eps,
      prod_factor_X_sub_one N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N) hmono_delta] at hmaster
  set P : ℕ := ∑ i : Fin N, (Finset.Ioi i).card with hP
  set S := MvPolynomial.aeval (fun i : Fin N => (Polynomial.X : Polynomial ℚ) ^ (i : ℕ))
      (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) with hS
  set Gδ := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      qFactor (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i) (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j) with hGδ
  set Gε := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      qFactor (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i) (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j) with hGε

  have hXne : ((Polynomial.X : Polynomial ℚ) - 1) ^ P ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg (Polynomial.eval (0 : ℚ)) h
    simp at this
  have hcancel : S * Gδ = Gε := by
    apply mul_left_cancel₀ hXne
    rw [← hmaster]; ring

  have hSval : Polynomial.eval 1 S = MvPolynomial.eval (fun _ => (1 : ℚ)) (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) := by
    rw [hS]; exact eval_one_aeval_pow N (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam)
  have hGδval : Polynomial.eval 1 Gδ = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (-((RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i - RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j : ℕ) : ℚ)) := by
    rw [hGδ]; exact eval_one_prod_qFactor N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)
  have hGεval : Polynomial.eval 1 Gε = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (-((RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j : ℕ) : ℚ)) := by
    rw [hGε]; exact eval_one_prod_qFactor N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam)
  have heval := congrArg (Polynomial.eval 1) hcancel
  rw [Polynomial.eval_mul, hSval, hGδval, hGεval] at heval

  have hden_ne : (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (-((RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i - RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j : ℕ) : ℚ))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro i _
    rw [Finset.prod_ne_zero_iff]; intro j hj
    simp only [Finset.mem_Ioi] at hj
    rw [neg_ne_zero, Nat.cast_ne_zero]
    have hij' : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp hj
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents]; omega

  have hweyl : schurDimension N lam
      = (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (-((RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j : ℕ) : ℚ)))
        / (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (-((RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i - RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j : ℕ) : ℚ))) := by
    rw [show schurDimension N lam
        = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
            ((-((RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j : ℕ) : ℚ))
              / (-((RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i - RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j : ℕ) : ℚ))) from ?_]
    · simp_rw [Finset.prod_div_distrib]
    · rw [schurDimension]
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
      have hij := Finset.mem_Ioi.mp hj
      rw [neg_div_neg_eq, hcast_eps i j hij, hcast_delta i j hij]
  rw [hweyl, eq_div_iff hden_ne]
  exact heval


/-- The dimension of the representation indexed by a weakly decreasing tuple is given by its rational dimension expression. -/
@[source_ref "Chapter5/Theorem5.22.1" (role := supporting)]
theorem finrank_schurRepresentation_eq (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    (Module.finrank k (schurRepresentation k N lam) : ℚ) = schurDimension N lam := by
  rw [finrank_schurRepresentation_eq_eval_one_weightCharacter k N lam hlam, weightCharacter_schurRepresentation_eq k N lam hlam,
      eval_one_schurPolynomial N lam hlam]

end RepresentationTheory.GeneralLinearGroup.WeightCharacter

end
