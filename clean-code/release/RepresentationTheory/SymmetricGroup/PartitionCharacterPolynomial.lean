/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.PermutationPolynomialAuxiliary
import RepresentationTheory.SimpleModule.SubtypeRepresentation
import RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra
import RepresentationTheory.PartitionAuxiliary
import RepresentationTheory.Combinatorics.PermutationPowerSeries
import RepresentationTheory.Alignment.Attribute

set_option linter.dupNamespace false
set_option linter.style.cdot false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter

open RepresentationTheory.PermutationPolynomialAuxiliary
open RepresentationTheory.SimpleModule.SubtypeRepresentation
open RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra
open RepresentationTheory.PartitionAuxiliary
open RepresentationTheory.PartitionLinearMapVanishing
open RepresentationTheory.Combinatorics.PermutationPowerSeries
open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions

/-- An auxiliary multivariable polynomial indexed by `n`. -/
@[source_ref "Chapter5/Introduction_5.15" (role := supporting)]
noncomputable def auxiliaryPolynomial (n : ℕ) : MvPolynomial (Fin n) ℂ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (MvPolynomial.X j - MvPolynomial.X i)

/-- An auxiliary natural-valued finitely supported function on `Fin n`. -/
@[source_ref "Chapter5/Introduction_5.15" (role := supporting)]
noncomputable def auxiliaryFinsupp (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => n - 1 - i.val)

/-- An auxiliary complex-linear endomorphism of the displayed subtype, indexed by a permutation of `Fin n`. -/
noncomputable def auxiliarySubtypePermutationEndomorphism (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : ↥(partitionSubmodule n la) →ₗ[ℂ] ↥(partitionSubmodule n la) where
  toFun := fun ⟨m, hm⟩ => ⟨MonoidAlgebra.of ℂ _ σ * m,
    (partitionSubmodule n la).smul_mem (MonoidAlgebra.of ℂ _ σ) hm⟩
  map_add' := fun ⟨a, _⟩ ⟨b, _⟩ => Subtype.ext (mul_add _ a b)
  map_smul' := fun _ ⟨m, _⟩ => Subtype.ext (Algebra.mul_smul_comm _ _ m)

/-- An auxiliary complex value indexed by a partition and a permutation of `Fin n`. -/
noncomputable def auxiliaryPartitionPermutationValue (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  LinearMap.trace ℂ _ (auxiliarySubtypePermutationEndomorphism n la σ)

/-- The complex representation of permutations of `Fin n` on the subspace associated with a partition. -/
noncomputable def partitionSubspaceRepresentation (n : ℕ) (la : Nat.Partition n) :
    Representation ℂ (Equiv.Perm (Fin n)) (partitionSubmodule n la) where
  toFun := auxiliarySubtypePermutationEndomorphism n la
  map_one' := LinearMap.ext fun ⟨m, hm⟩ => Subtype.ext (show
      (MonoidAlgebra.of ℂ _ (1 : Equiv.Perm (Fin n)) * m : natIndexedType n) = m by
    rw [map_one, one_mul])
  map_mul' := fun σ τ => LinearMap.ext fun ⟨m, hm⟩ => Subtype.ext (show
      (MonoidAlgebra.of ℂ _ (σ * τ) * m : natIndexedType n) =
        MonoidAlgebra.of ℂ _ σ * (MonoidAlgebra.of ℂ _ τ * m) by
    rw [map_mul, mul_assoc])

/-- The finite-dimensional complex representation of permutations of `Fin n` associated with a partition of `n`. -/
noncomputable def partitionFDRep (n : ℕ) (la : Nat.Partition n) :
    FDRep ℂ (Equiv.Perm (Fin n)) :=
  FDRep.of (partitionSubspaceRepresentation n la)

/-- The character of the displayed finite-dimensional representation equals an auxiliary value. -/
theorem partitionFDRep_character_eq_auxiliary (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    (partitionFDRep n la).character σ = auxiliaryPartitionPermutationValue n la σ := rfl

section spechtSimple
open CategoryTheory

private lemma reflect_simple_of_full_faithful {C D : Type*}
    [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance
        (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) :=
        (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

set_option backward.isDefEq.respectTransparency false in
/-- The finite-dimensional representation associated with a partition is simple. -/
noncomputable instance partitionFDRep_simple (n : ℕ) (la : Nat.Partition n) :
    Simple (partitionFDRep n la) := by
  haveI hsimple := partitionSubmodule_isSimpleModule n la

  have smul_eq : ∀ (a : natIndexedType n) (v : (partitionSubspaceRepresentation n la).asModule),
      a • v = (show ↥(partitionSubmodule n la) from a • (show ↥(partitionSubmodule n la) from v)) := by
    intro a v
    induction a using MonoidAlgebra.induction_on with
    | hM g =>
      change MonoidAlgebra.single g 1 • v = _
      rw [Representation.single_smul]
      simp only [one_smul, Representation.asModuleEquiv]
      simp [partitionSubspaceRepresentation, auxiliarySubtypePermutationEndomorphism]
      rfl
    | hadd x y hx hy =>
      rw [add_smul, hx, hy, add_smul]
    | hsmul r x hx =>
      rw [smul_assoc, hx, smul_assoc]

  haveI : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin n)))
      (partitionSubspaceRepresentation n la).asModule := by
    haveI : Nontrivial (partitionSubspaceRepresentation n la).asModule := hsimple.nontrivial
    refine { eq_bot_or_eq_top := fun m => ?_ }
    let m' : Submodule (natIndexedType n) (partitionSubmodule n la) :=
      { carrier := m.carrier
        add_mem' := m.add_mem'
        zero_mem' := m.zero_mem'
        smul_mem' := fun a v hv => by
          have := m.smul_mem a hv; rwa [smul_eq] at this }
    cases hsimple.eq_bot_or_eq_top m' with
    | inl h =>
      left; ext x; simp only [Submodule.mem_bot]
      exact ⟨fun hx => by
        have : x ∈ m'.carrier := hx
        rw [h] at this; exact this,
      fun hx => by rw [hx]; exact m.zero_mem⟩
    | inr h =>
      right; ext x; simp only [Submodule.mem_top, iff_true]
      have : x ∈ m'.carrier := by rw [h]; exact Submodule.mem_top
      exact this

  let E := Rep.equivalenceModuleMonoidAlgebra (k := ℂ) (G := Equiv.Perm (Fin n))
  haveI : Simple (E.functor.obj ((forget₂
      (FDRep ℂ (Equiv.Perm (Fin n))) (Rep ℂ (Equiv.Perm (Fin n)))).obj
      (partitionFDRep n la))) := by
    change Simple
      (ModuleCat.of (MonoidAlgebra ℂ (Equiv.Perm (Fin n)))
        (partitionSubspaceRepresentation n la).asModule)
    exact simple_of_isSimpleModule
  haveI : Simple ((forget₂
      (FDRep ℂ (Equiv.Perm (Fin n))) (Rep ℂ (Equiv.Perm (Fin n)))).obj
      (partitionFDRep n la)) :=
    reflect_simple_of_full_faithful E.functor _
  exact reflect_simple_of_full_faithful
    (forget₂ (FDRep ℂ (Equiv.Perm (Fin n)))
      (Rep ℂ (Equiv.Perm (Fin n)))) _

end spechtSimple

noncomputable section

/-- An auxiliary natural-valued finitely supported function associated with a permutation of `Fin n`. -/
def auxiliaryPermutationFinsupp (n : ℕ) (π : Equiv.Perm (Fin n)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (π⁻¹ j).val)

/-- The auxiliary polynomial equals the displayed sum of sign-weighted monomials. -/
theorem auxiliaryPolynomial_eq_sum (n : ℕ) :
    auxiliaryPolynomial n =
      ∑ π : Equiv.Perm (Fin n),
        (Equiv.Perm.sign π : ℤ) • MvPolynomial.monomial (auxiliaryPermutationFinsupp n π) (1 : ℂ) := by

  have hvand : auxiliaryPolynomial n =
      (Matrix.vandermonde (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℂ))).det := by
    simp only [auxiliaryPolynomial, Matrix.det_vandermonde]
  rw [hvand, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _

  congr 1
  simp only [Matrix.vandermonde_apply]

  rw [Fintype.prod_equiv σ
    (fun i => MvPolynomial.X (σ i) ^ (i : ℕ))
    (fun j => MvPolynomial.X j ^ (auxiliaryPermutationFinsupp n σ) j)
    (fun i => by simp [auxiliaryPermutationFinsupp, Finsupp.equivFunOnFinite])]

  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
    Finsupp.prod_fintype _ _ (fun i => by simp)]

/-- The coefficient at `α + e` of a monomial at `e` times `P` is the monomial scalar times the coefficient of `P` at `α`. -/
theorem coeff_add_monomial_mul {n : ℕ} (e α : Fin n →₀ ℕ) (c : ℂ)
    (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.coeff (α + e) (MvPolynomial.monomial e c * P) =
      c * MvPolynomial.coeff α P := by
  rw [mul_comm, MvPolynomial.coeff_mul_monomial]; ring

/-- An auxiliary assertion whose type was unavailable from the displayed formal output. -/
theorem auxiliaryResultB (n : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (α : Fin n →₀ ℕ) :
    MvPolynomial.coeff α (auxiliaryPolynomial n * P) =
      ∑ π : Equiv.Perm (Fin n),
        (Equiv.Perm.sign π : ℤ) • (if _ : auxiliaryPermutationFinsupp n π ≤ α
          then (MvPolynomial.coeff (α - auxiliaryPermutationFinsupp n π) P : ℂ) else 0) := by

  rw [auxiliaryPolynomial_eq_sum]
  simp only [Finset.sum_mul, smul_mul_assoc, MvPolynomial.coeff_sum]
  congr 1; ext π

  rw [← Int.cast_smul_eq_zsmul (R := ℂ) (Equiv.Perm.sign π : ℤ), MvPolynomial.coeff_smul,
    MvPolynomial.coeff_monomial_mul', one_mul, Int.cast_smul_eq_zsmul (R := ℂ)]
  simp only [dite_eq_ite]

/-- The natural cast of an auxiliary natural value equals the displayed polynomial coefficient. -/
theorem natCast_auxiliary_eq_coeff (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    (partitionPermutationValue n la σ : ℂ) =
      MvPolynomial.coeff (partitionNatFinsupp la) (permutationPolynomialAuxiliary n σ) :=
  partitionPermutationValue_eq_coefficient n la σ

private theorem MvPolynomial.IsSymmetric.pow {σ : Type*} {R : Type*} [CommSemiring R]
    {P : MvPolynomial σ R} (hP : P.IsSymmetric) (k : ℕ) : (P ^ k).IsSymmetric := by
  induction k with
  | zero => simp [MvPolynomial.IsSymmetric.one]
  | succ k ih => rw [pow_succ]; exact ih.mul hP

private theorem multiset_prod_isSymmetric {σ : Type*} {R : Type*} [CommSemiring R]
    (s : Multiset (MvPolynomial σ R)) (hs : ∀ p ∈ s, MvPolynomial.IsSymmetric p) :
    (s.prod).IsSymmetric := by
  induction s using Multiset.induction with
  | empty => simp [MvPolynomial.IsSymmetric.one]
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (hs a (Multiset.mem_cons_self a s)).mul
      (ih (fun p hp => hs p (Multiset.mem_cons_of_mem hp)))

/-- The permutation-indexed auxiliary multivariable polynomial is symmetric. -/
theorem auxiliaryPolynomial_isSymmetric (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationPolynomialAuxiliary n σ).IsSymmetric := by
  unfold permutationPolynomialAuxiliary
  apply MvPolynomial.IsSymmetric.mul
  · exact multiset_prod_isSymmetric _ (fun p hp => by
      rw [Multiset.mem_map] at hp
      obtain ⟨m, _, rfl⟩ := hp
      exact MvPolynomial.psum_isSymmetric (Fin n) ℂ m)
  · exact MvPolynomial.IsSymmetric.pow (MvPolynomial.psum_isSymmetric (Fin n) ℂ 1) _

/-- A symmetric multivariable polynomial has the same coefficient after permuting the domain of an exponent vector. -/
theorem IsSymmetric.coeff_mapDomain_perm {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P.IsSymmetric)
    (d : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n)) :
    P.coeff (d.mapDomain σ) = P.coeff d := by
  conv_lhs => rw [← hP σ]
  exact MvPolynomial.coeff_rename_mapDomain σ σ.injective P d

/-- An auxiliary natural number indexed by two partitions of `n`. -/
noncomputable def auxiliaryPartitionNat (n : ℕ) (mu nu : Nat.Partition n) : ℕ :=
  Module.finrank ℂ (partitionIndexedType n mu →ₗ[natIndexedType n] ↥(partitionSubmodule n nu))

/-- The auxiliary natural number is zero when the displayed auxiliary relation holds. -/
theorem auxiliaryPartitionNat_eq_zero_of_auxiliaryRelation (n : ℕ) (mu nu : Nat.Partition n)
    (h : partitionRelation' mu nu) :
    auxiliaryPartitionNat n mu nu = 0 := by
  simp only [auxiliaryPartitionNat]
  have hall : ∀ f : partitionIndexedType n mu →ₗ[natIndexedType n] ↥(partitionSubmodule n nu), f = 0 :=
    linearMap_to_mem_eq_zero_of_partitionRelation' n mu nu h
  have : Subsingleton (partitionIndexedType n mu →ₗ[natIndexedType n] ↥(partitionSubmodule n nu)) :=
    ⟨fun f g => by rw [hall f, hall g]⟩
  exact Module.finrank_zero_of_subsingleton

/-- The auxiliary natural number is zero when the displayed auxiliary relation fails in the specified direction. -/
theorem auxiliaryPartitionNat_eq_zero_of_not_auxiliaryRelation (n : ℕ) (mu nu : Nat.Partition n)
    (h : ¬ partitionRelation nu mu) :
    auxiliaryPartitionNat n mu nu = 0 := by
  simp only [auxiliaryPartitionNat]
  have hall : ∀ f : partitionIndexedType n mu →ₗ[natIndexedType n] ↥(partitionSubmodule n nu), f = 0 :=
    linearMap_to_mem_eq_zero_of_not_partitionRelation n mu nu h
  have : Subsingleton (partitionIndexedType n mu →ₗ[natIndexedType n] ↥(partitionSubmodule n nu)) :=
    ⟨fun f g => by rw [hall f, hall g]⟩
  exact Module.finrank_zero_of_subsingleton

/-- The auxiliary natural number at two equal partition arguments is one. -/
theorem auxiliaryPartitionNat_self (n : ℕ) (la : Nat.Partition n) :
    auxiliaryPartitionNat n la la = 1 :=
  finrank_linearMap_to_mem_eq_one n la

private abbrev G_n (n : ℕ) := Equiv.Perm (Fin n)
private abbrev Q_n (n : ℕ) (la : Nat.Partition n) := G_n n ⧸ auxiliaryPartitionPermutationSubgroupB n la

/-- An auxiliary complex-linear endomorphism indexed by a partition and a permutation of `Fin n`. -/
noncomputable def auxiliaryPermutationEndomorphism (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : partitionIndexedType n la →ₗ[ℂ] partitionIndexedType n la :=
  Representation.ofMulAction ℂ (G_n n) (Q_n n la) σ

/-- The natural cast of an auxiliary natural value equals the trace of the displayed endomorphism. -/
theorem natCast_auxiliary_eq_trace (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    (partitionPermutationValue n la σ : ℂ) =
      LinearMap.trace ℂ _ (auxiliaryPermutationEndomorphism n la σ) := by
  classical
  simp only [partitionPermutationValue, auxiliaryPermutationEndomorphism]
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis (Q_n n la) ℂ)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    Representation.ofMulAction]
  have hb : ∀ q : Q_n n la,
      (MonoidAlgebra.basis (Q_n n la) ℂ q) = MonoidAlgebra.single q 1 :=
    fun q => rfl
  have hr : ∀ v : MonoidAlgebra ℂ (Q_n n la),
      (MonoidAlgebra.basis (Q_n n la) ℂ).repr v = v.coeff :=
    fun v => rfl
  simp only [hb, hr]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [Finsupp.single_apply, Finset.sum_boole, MulAction.mem_fixedBy]

private lemma permMod_smul_eq' (n : ℕ) (la : Nat.Partition n)
    (a : natIndexedType n) (x : partitionIndexedType n la) :
    a • x = (Representation.ofMulAction ℂ (G_n n) (Q_n n la)).asAlgebraHom a x := rfl

/-- The complex scalars, auxiliary scalar ring, and partition-indexed space form a scalar tower. -/
noncomputable instance isScalarTower_partitionSpace (n : ℕ) (la : Nat.Partition n) :
    IsScalarTower ℂ (natIndexedType n) (partitionIndexedType n la) where
  smul_assoc c a m := by

    simp only [permMod_smul_eq']

    rw [map_smul (Representation.ofMulAction ℂ (G_n n) (Q_n n la)).asAlgebraHom c a]

    simp [LinearMap.smul_apply]

/-- A complex submodule of a partition-indexed space, indexed by a second partition. -/
noncomputable def partitionComponent (n : ℕ) (mu nu : Nat.Partition n) :
    Submodule ℂ (partitionIndexedType n mu) :=
  (isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
    (partitionSubmodule n nu)).restrictScalars ℂ

/-- Distinct partitions have no linear equivalence between their associated subspaces over the auxiliary scalar ring. -/
theorem isEmpty_linearEquiv_of_ne (n : ℕ) (nu₁ nu₂ : Nat.Partition n) (hne : nu₁ ≠ nu₂) :
    IsEmpty (↥(partitionSubmodule n nu₁) ≃ₗ[natIndexedType n] ↥(partitionSubmodule n nu₂)) :=
  isEmpty_linearEquiv_of_ne_partition n nu₁ nu₂ hne

/-- Two partition-indexed finite-dimensional representations are isomorphic exactly when their partitions are equal. -/
theorem partitionFDRep_iso_iff (n : ℕ) (ν₁ ν₂ : Nat.Partition n) :
    Nonempty (partitionFDRep n ν₁ ≅ partitionFDRep n ν₂) ↔ ν₁ = ν₂ := by
  constructor
  · rintro ⟨f⟩
    by_contra hne
    let φ : ↥(partitionSubmodule n ν₁) ≃ₗ[ℂ] ↥(partitionSubmodule n ν₂) :=
      FDRep.isoToLinearEquiv f

    have hφ_group : ∀ (σ : Equiv.Perm (Fin n)) (v : ↥(partitionSubmodule n ν₁)),
        φ (auxiliarySubtypePermutationEndomorphism n ν₁ σ v) = auxiliarySubtypePermutationEndomorphism n ν₂ σ (φ v) := by
      intro σ v
      have h := FDRep.Iso.conj_ρ f σ
      change φ ((partitionFDRep n ν₁).ρ σ v) = (partitionFDRep n ν₂).ρ σ (φ v)
      have hconj : (FDRep.isoToLinearEquiv f).conj ((partitionFDRep n ν₁).ρ σ) (φ v) =
          φ ((partitionFDRep n ν₁).ρ σ v) := by
        simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
        change φ (((partitionFDRep n ν₁).ρ σ) (φ.symm (φ v))) = φ (((partitionFDRep n ν₁).ρ σ) v)
        rw [φ.symm_apply_apply]
      rw [h, hconj]

    have hφ_smul : ∀ (a : natIndexedType n) (v : ↥(partitionSubmodule n ν₁)),
        φ (a • v) = a • (φ v) := by
      intro a
      induction a using MonoidAlgebra.induction_on with
      | hM g =>
        intro v

        have e1 : (MonoidAlgebra.of ℂ _ g : natIndexedType n) • v =
            auxiliarySubtypePermutationEndomorphism n ν₁ g v := rfl
        have e2 : (MonoidAlgebra.of ℂ _ g : natIndexedType n) • (φ v) =
            auxiliarySubtypePermutationEndomorphism n ν₂ g (φ v) := rfl
        rw [e1, e2, hφ_group g v]
      | hadd f g hf hg => intro v; rw [add_smul, map_add, hf, hg, add_smul]
      | hsmul r f hf => intro v; rw [smul_assoc, map_smul, hf, smul_assoc]
    exact (isEmpty_linearEquiv_of_ne n ν₁ ν₂ hne).false
      { φ with map_smul' := hφ_smul }
  · rintro rfl; exact ⟨CategoryTheory.Iso.refl _⟩

/-- Every simple submodule of a partition-indexed space is linearly equivalent to a subspace associated with some partition. -/
theorem exists_partition_linearEquiv_of_isSimpleModule (n : ℕ) (mu : Nat.Partition n)
    (S : Submodule (natIndexedType n) (partitionIndexedType n mu))
    [IsSimpleModule (natIndexedType n) S] :
    ∃ nu : Nat.Partition n, Nonempty (↥S ≃ₗ[natIndexedType n] ↥(partitionSubmodule n nu)) :=
  exists_linearEquiv_to_subtype n S

private theorem isotypicComponent_disjoint_of_ne (n : ℕ) (mu : Nat.Partition n)
    (nu₁ nu₂ : Nat.Partition n) (hne : nu₁ ≠ nu₂) :
    Disjoint
      (isotypicComponent (natIndexedType n)
        (partitionIndexedType n mu) (partitionSubmodule n nu₁))
      (isotypicComponent (natIndexedType n)
        (partitionIndexedType n mu) (partitionSubmodule n nu₂)) := by

  rw [disjoint_iff]
  set I := isotypicComponent (natIndexedType n)
    (partitionIndexedType n mu) (partitionSubmodule n nu₁) ⊓
    isotypicComponent (natIndexedType n)
    (partitionIndexedType n mu) (partitionSubmodule n nu₂)

  haveI : IsSemisimpleModule (natIndexedType n) I := inferInstance

  rcases IsSemisimpleModule.eq_bot_or_exists_simple_le I with h | ⟨S, hS_le, hS_simple⟩
  · exact h
  · exfalso

    have hS_le₁ : S ≤ isotypicComponent (natIndexedType n)
        (partitionIndexedType n mu) (partitionSubmodule n nu₁) :=
      hS_le.trans inf_le_left

    have hS_le₂ : S ≤ isotypicComponent (natIndexedType n)
        (partitionIndexedType n mu) (partitionSubmodule n nu₂) :=
      hS_le.trans inf_le_right

    haveI := hS_simple
    haveI : IsSimpleModule (natIndexedType n) (partitionSubmodule n nu₁) :=
      partitionSubmodule_isSimpleModule n nu₁
    haveI : IsSimpleModule (natIndexedType n) (partitionSubmodule n nu₂) :=
      partitionSubmodule_isSimpleModule n nu₂
    have h₁ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (natIndexedType n)
        (partitionIndexedType n mu) (partitionSubmodule n nu₁)) S hS_le₁
    have h₂ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (natIndexedType n)
        (partitionIndexedType n mu) (partitionSubmodule n nu₂)) S hS_le₂
    obtain ⟨e₁⟩ := h₁
    obtain ⟨e₂⟩ := h₂
    exact (isEmpty_linearEquiv_of_ne n nu₁ nu₂ hne).false (e₁.symm.trans e₂)

private theorem iSup_isotypicComponent_eq_top (n : ℕ) (mu : Nat.Partition n) :
    ⨆ nu : Nat.Partition n,
      isotypicComponent (natIndexedType n) (partitionIndexedType n mu) (partitionSubmodule n nu) = ⊤ := by
  rw [eq_top_iff, ← sSup_isotypicComponents (natIndexedType n) (partitionIndexedType n mu)]
  apply sSup_le
  intro c hc
  obtain ⟨S, hS_simple, rfl⟩ := hc

  haveI := hS_simple
  obtain ⟨nu, ⟨e⟩⟩ := exists_partition_linearEquiv_of_isSimpleModule n mu S
  rw [e.isotypicComponent_eq]
  exact le_iSup (fun nu => isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
    (partitionSubmodule n nu)) nu

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in

private theorem iSupIndep_isotypicComponent (n : ℕ)
    (mu : Nat.Partition n) :
    iSupIndep (fun nu : Nat.Partition n =>
      isotypicComponent (natIndexedType n)
        (partitionIndexedType n mu) (partitionSubmodule n nu)) := by

  have mem_of_ne_bot : ∀ nu,
      isotypicComponent (natIndexedType n)
        (partitionIndexedType n mu) (partitionSubmodule n nu) ≠ ⊥ →
      isotypicComponent (natIndexedType n)
        (partitionIndexedType n mu) (partitionSubmodule n nu) ∈
        isotypicComponents (natIndexedType n)
          (partitionIndexedType n mu) := by
    intro nu hbot
    obtain ⟨S, hS_le, hS_simple⟩ :=
      (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left
        hbot
    haveI := hS_simple
    haveI := partitionSubmodule_isSimpleModule n nu
    obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (natIndexedType n)
        (partitionIndexedType n mu) (partitionSubmodule n nu)) S hS_le
    exact ⟨S, hS_simple, e.symm.isotypicComponent_eq⟩
  rw [iSupIndep_def]
  intro nu
  by_cases hbot : isotypicComponent (natIndexedType n)
      (partitionIndexedType n mu) (partitionSubmodule n nu) = ⊥
  · simp [hbot]
  ·

    apply (sSupIndep_isotypicComponents (natIndexedType n)
      (partitionIndexedType n mu) (mem_of_ne_bot nu hbot)).mono_right
    apply iSup₂_le
    intro nu' hne
    by_cases hbot' : isotypicComponent (natIndexedType n)
        (partitionIndexedType n mu) (partitionSubmodule n nu') = ⊥
    · simp [hbot']
    ·
      have hne_val : isotypicComponent (natIndexedType n)
          (partitionIndexedType n mu) (partitionSubmodule n nu') ≠
          isotypicComponent (natIndexedType n)
            (partitionIndexedType n mu)
            (partitionSubmodule n nu) := by
        intro heq
        obtain ⟨S, hS_le, hS_simple⟩ :=
          (IsSemisimpleModule.eq_bot_or_exists_simple_le
            _).resolve_left hbot
        haveI := hS_simple
        haveI := partitionSubmodule_isSimpleModule n nu
        haveI := partitionSubmodule_isSimpleModule n nu'
        obtain ⟨e₁⟩ := isIsotypicOfType_submodule_iff.mp
          (IsIsotypicOfType.isotypicComponent (natIndexedType n)
            (partitionIndexedType n mu) (partitionSubmodule n nu))
          S hS_le
        obtain ⟨e₂⟩ := isIsotypicOfType_submodule_iff.mp
          (IsIsotypicOfType.isotypicComponent (natIndexedType n)
            (partitionIndexedType n mu) (partitionSubmodule n nu'))
          S (heq ▸ hS_le)
        exact (isEmpty_linearEquiv_of_ne n nu nu' hne.symm).false
          (e₁.symm.trans e₂)
      exact le_sSup ⟨mem_of_ne_bot nu' hbot', hne_val⟩

/-- The family of partition components gives an internal direct sum. -/
theorem partitionComponent_isInternal (n : ℕ)
    (mu : Nat.Partition n) :
    DirectSum.IsInternal (fun nu : Nat.Partition n =>
      partitionComponent n mu nu) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  ·
    have h := iSupIndep_isotypicComponent n mu
    rw [iSupIndep_def] at h ⊢
    intro nu
    simp only [partitionComponent]
    specialize h nu
    rw [disjoint_iff] at h ⊢
    simp only [← Submodule.restrictScalars_iSup]
    rw [← Submodule.restrictScalars_inf,
        Submodule.restrictScalars_eq_bot_iff]
    exact h
  ·
    simp only [partitionComponent]
    rw [← Submodule.restrictScalars_iSup,
        show (⨆ i, isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
          (partitionSubmodule n i)) = (⊤ : Submodule (natIndexedType n) (partitionIndexedType n mu))
          from iSup_isotypicComponent_eq_top n mu,
        Submodule.restrictScalars_top]

/-- The partition-indexed family of isotypic components gives an internal direct sum. -/
theorem isotypicComponent_isInternal (n : ℕ)
    (mu : Nat.Partition n) :
    DirectSum.IsInternal (fun nu : Nat.Partition n =>
      isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
        (partitionSubmodule n nu)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨iSupIndep_isotypicComponent n mu, iSup_isotypicComponent_eq_top n mu⟩

private lemma permModuleEndomorphism_eq_smul (n : ℕ) (mu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (v : partitionIndexedType n mu) :
    auxiliaryPermutationEndomorphism n mu σ v =
      (MonoidAlgebra.of ℂ _ σ : natIndexedType n) • v := by
  simp only [permMod_smul_eq', auxiliaryPermutationEndomorphism]
  simp [Representation.asAlgebraHom_single]

/-- The displayed auxiliary endomorphism maps the displayed auxiliary set into itself. -/
theorem auxiliaryPermutationEndomorphism_mapsTo_auxiliary (n : ℕ) (mu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (nu : Nat.Partition n) :
    Set.MapsTo (auxiliaryPermutationEndomorphism n mu σ)
      (partitionComponent n mu nu) (partitionComponent n mu nu) := by
  intro v hv
  rw [permModuleEndomorphism_eq_smul]
  exact (isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
    (partitionSubmodule n nu)).smul_mem _ hv

/-- Each partition component is finite as a complex module. -/
instance partitionComponent_module_finite (n : ℕ) (mu nu : Nat.Partition n) :
    Module.Finite ℂ (partitionComponent n mu nu) :=
  inferInstance

/-- Each partition component is free as a complex module. -/
instance partitionComponent_module_free (n : ℕ) (mu nu : Nat.Partition n) :
    Module.Free ℂ (partitionComponent n mu nu) :=
  Module.Free.of_divisionRing ℂ (↥(partitionComponent n mu nu))

private lemma trace_pi_diag {k : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Free ℂ V] [Module.Finite ℂ V] (f : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ (Fin k → V) (LinearMap.pi (fun i => f ∘ₗ LinearMap.proj i)) =
    (k : ℂ) * LinearMap.trace ℂ V f := by
  classical
  let bV := Module.Free.chooseBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis fun _ : Fin k => bV),
      LinearMap.trace_eq_matrix_trace ℂ bV]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    Pi.basis_apply, Pi.basis_repr,
    LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp [Finset.sum_const]

private lemma isotypicComponent_isIsotypicOfType (n : ℕ) (mu nu : Nat.Partition n) :
    IsIsotypicOfType (natIndexedType n)
      (isotypicComponent (natIndexedType n) (partitionIndexedType n mu) (partitionSubmodule n nu))
      (partitionSubmodule n nu) := by
  haveI : IsSimpleModule (natIndexedType n) (partitionSubmodule n nu) :=
    partitionSubmodule_isSimpleModule n nu
  exact IsIsotypicOfType.isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
    (partitionSubmodule n nu)

private lemma restrict_val_eq_smul (n : ℕ) (mu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (nu : Nat.Partition n)
    (v : ↥(partitionComponent n mu nu)) :
    ((auxiliaryPermutationEndomorphism n mu σ).restrict
      (auxiliaryPermutationEndomorphism_mapsTo_auxiliary n mu σ nu) v : partitionIndexedType n mu) =
    (MonoidAlgebra.of ℂ _ σ : natIndexedType n) • (v : partitionIndexedType n mu) :=
  permModuleEndomorphism_eq_smul n mu σ v

private lemma conj_restrict_eq_pi_spechtAction (n : ℕ) (mu nu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (e_R : ↥(isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
      (partitionSubmodule n nu)) ≃ₗ[natIndexedType n] (Fin k → ↥(partitionSubmodule n nu))) :
    (e_R.restrictScalars ℂ).conj
      ((auxiliaryPermutationEndomorphism n mu σ).restrict
        (auxiliaryPermutationEndomorphism_mapsTo_auxiliary n mu σ nu)) =
    LinearMap.pi (fun i => auxiliarySubtypePermutationEndomorphism n nu σ ∘ₗ LinearMap.proj i) := by

  set r : natIndexedType n := MonoidAlgebra.of ℂ _ σ
  apply LinearMap.ext; intro v

  have h_restrict : ∀ (w : ↥(isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
      (partitionSubmodule n nu))),
    ((auxiliaryPermutationEndomorphism n mu σ).restrict
      (auxiliaryPermutationEndomorphism_mapsTo_auxiliary n mu σ nu) w : partitionIndexedType n mu) =
      r • (w : partitionIndexedType n mu) := by
    intro w; exact permModuleEndomorphism_eq_smul n mu σ w

  change (e_R.restrictScalars ℂ) (((auxiliaryPermutationEndomorphism n mu σ).restrict
      (auxiliaryPermutationEndomorphism_mapsTo_auxiliary n mu σ nu))
        ((e_R.restrictScalars ℂ).symm v)) =
      (LinearMap.pi (fun i => auxiliarySubtypePermutationEndomorphism n nu σ ∘ₗ LinearMap.proj i)) v

  have h_eq : (e_R ((auxiliaryPermutationEndomorphism n mu σ).restrict
      (auxiliaryPermutationEndomorphism_mapsTo_auxiliary n mu σ nu) (e_R.symm v)) :
      Fin k → ↥(partitionSubmodule n nu)) = e_R (r • e_R.symm v) := by
    congr 1; apply Subtype.ext; exact h_restrict _

  change (e_R ((auxiliaryPermutationEndomorphism n mu σ).restrict
      (auxiliaryPermutationEndomorphism_mapsTo_auxiliary n mu σ nu) (e_R.symm v))) = _
  rw [h_eq, map_smul e_R, LinearEquiv.apply_symm_apply]

  rfl

private lemma hom_from_wrong_isotypic_eq_zero (n : ℕ) (mu : Nat.Partition n)
    (nu la : Nat.Partition n) (hla : la ≠ nu)
    (f : partitionIndexedType n mu →ₗ[natIndexedType n] ↥(partitionSubmodule n nu))
    (x : partitionIndexedType n mu)
    (hx : x ∈ isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
      (partitionSubmodule n la)) : f x = 0 := by
  set R := natIndexedType n
  set V := ↥(partitionSubmodule n nu)
  set U := partitionIndexedType n mu
  haveI : IsSimpleModule R V := partitionSubmodule_isSimpleModule n nu
  haveI : IsSimpleModule R (partitionSubmodule n la) := partitionSubmodule_isSimpleModule n la

  suffices h : isotypicComponent R U (partitionSubmodule n la) ≤ LinearMap.ker f from
    LinearMap.mem_ker.mp (h hx)

  apply sSup_le
  intro S ⟨e_S⟩

  haveI : IsSimpleModule R S := IsSimpleModule.congr e_S

  intro s hs
  rw [LinearMap.mem_ker]

  rcases LinearMap.bijective_or_eq_zero (R := R) (M := ↥S) (N := V)
      { toFun := fun t => f t.val
        map_add' := fun a b => by simp only [Submodule.coe_add, map_add]
        map_smul' := fun r t => by simp only [Submodule.coe_smul, map_smul, RingHom.id_apply] }
      with h_bij | h_zero
  ·
    exfalso
    have e_SV := LinearEquiv.ofBijective _ h_bij
    exact (isEmpty_linearEquiv_of_ne n la nu hla).false (e_S.symm.trans e_SV)
  ·
    have h := congr_fun (congr_arg DFunLike.coe h_zero) ⟨s, hs⟩
    rw [LinearMap.zero_apply] at h
    exact h

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 40000 in

private lemma multiplicity_eq_spechtMultiplicity (n : ℕ) (mu nu : Nat.Partition n)
    (k : ℕ) (e_R : ↥(isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
      (partitionSubmodule n nu)) ≃ₗ[natIndexedType n] (Fin k → ↥(partitionSubmodule n nu))) :
    k = auxiliaryPartitionNat n mu nu := by

  set R := natIndexedType n
  set V := ↥(partitionSubmodule n nu)
  set U := partitionIndexedType n mu
  set C := isotypicComponent R U V

  haveI : IsSimpleModule R V := partitionSubmodule_isSimpleModule n nu
  haveI : Module.Finite ℂ V := inferInstance
  haveI : FiniteDimensional ℂ V := inferInstance

  have h_schur : Module.finrank ℂ (V →ₗ[R] V) = 1 := by
    have h_bij := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ (A := R) (V := V)
    rw [LinearEquiv.finrank_eq
      (LinearEquiv.ofBijective (Algebra.linearMap ℂ (Module.End R V)) h_bij).symm]
    exact Module.finrank_self ℂ

  haveI : Module.Free ℂ (V →ₗ[R] V) := Module.Free.of_divisionRing ℂ (V →ₗ[R] V)
  have h_lsum_finrank : Module.finrank ℂ ((Fin k → V) →ₗ[R] V) = k := by
    rw [LinearEquiv.finrank_eq (LinearMap.lsum (R := R) ℂ (φ := fun _ : Fin k => V) (M := V)).symm,
        Module.finrank_pi_fintype, h_schur, Finset.sum_const, Finset.card_fin, smul_eq_mul,
        mul_one]

  have h_transport : Module.finrank ℂ (↥C →ₗ[R] V) = k := by
    have e_hom : (↥C →ₗ[R] V) ≃ₗ[ℂ] ((Fin k → V) →ₗ[R] V) :=
      { toFun := fun f => f.comp e_R.symm.toLinearMap
        invFun := fun g => g.comp e_R.toLinearMap
        left_inv := fun f => by
          apply LinearMap.ext; intro x
          simp only [LinearMap.comp_apply]
          congr 1; exact e_R.symm_apply_apply x
        right_inv := fun g => by
          apply LinearMap.ext; intro v
          simp only [LinearMap.comp_apply]
          congr 1; exact e_R.apply_symm_apply v
        map_add' := fun f g => by apply LinearMap.ext; intro; simp
        map_smul' := fun c f => by
          apply LinearMap.ext; intro x
          simp [LinearMap.smul_apply] }
    rw [LinearEquiv.finrank_eq e_hom]; exact h_lsum_finrank

  have h_restrict : Module.finrank ℂ (U →ₗ[R] V) = k := by

    have h_indep := iSupIndep_isotypicComponent n mu

    set D : Submodule R U := ⨆ (la : Nat.Partition n) (_ : la ≠ nu),
      isotypicComponent R U (partitionSubmodule n la) with hD_def

    have h_disj : Disjoint C D := by
      exact h_indep.disjoint_biSup (show nu ∉ {la : Nat.Partition n | la ≠ nu} from fun h => h rfl)
    have h_codisj : Codisjoint C D := by
      rw [codisjoint_iff, eq_top_iff, ← iSup_isotypicComponent_eq_top n mu]
      apply iSup_le; intro la
      by_cases h : la = nu
      · exact h ▸ le_sup_left
      · exact le_sup_of_le_right (le_iSup_of_le la (le_iSup_of_le h le_rfl))
    have h_compl : IsCompl C D := ⟨h_disj, h_codisj⟩

    set proj_C : U →ₗ[R] ↥C := Submodule.projectionOnto C D h_compl

    have h_vanish_D : ∀ (f : U →ₗ[R] V) (d : U), d ∈ D → f d = 0 := by
      intro f d hd

      have : D ≤ LinearMap.ker f := by
        rw [hD_def]
        apply iSup₂_le
        intro la hla x hx
        exact LinearMap.mem_ker.mpr (hom_from_wrong_isotypic_eq_zero n mu nu la hla f x hx)
      exact LinearMap.mem_ker.mp (this hd)

    have e_restrict : (U →ₗ[R] V) ≃ₗ[ℂ] (↥C →ₗ[R] V) :=
      { toFun := fun f => f.comp C.subtype
        invFun := fun g => g.comp proj_C
        left_inv := fun f => by
          apply LinearMap.ext; intro u
          change (f.comp C.subtype).comp proj_C u = f u
          simp only [LinearMap.comp_apply]

          have h_decomp : f u = f (C.subtype (proj_C u)) + f (u - C.subtype (proj_C u)) := by
            rw [← map_add f]; congr 1; abel
          rw [h_decomp]

          have h_mem_D : u - C.subtype (proj_C u) ∈ D := by
            rw [← Submodule.ker_projectionOnto h_compl]
            rw [LinearMap.mem_ker, map_sub]
            have : proj_C (C.subtype (proj_C u)) = proj_C u :=
              Submodule.projectionOnto_apply_left h_compl (proj_C u)
            rw [this, sub_self]
          rw [h_vanish_D f _ h_mem_D, add_zero]
        right_inv := fun g => by
          apply LinearMap.ext; intro ⟨x, hx⟩
          change g.comp proj_C (C.subtype ⟨x, hx⟩) = g ⟨x, hx⟩
          simp only [LinearMap.comp_apply, Submodule.subtype_apply]
          congr 1
          exact Submodule.projectionOnto_apply_left h_compl ⟨x, hx⟩
        map_add' := fun f g => by apply LinearMap.ext; intro; simp [LinearMap.comp_apply]
        map_smul' := fun c f => by
          apply LinearMap.ext; intro x
          simp [LinearMap.comp_apply, LinearMap.smul_apply] }
    rw [LinearEquiv.finrank_eq e_restrict]; exact h_transport

  unfold auxiliaryPartitionNat; linarith

/-- An isotypic component is linearly equivalent over the auxiliary scalar ring to an indexed family of copies of a partition subspace. -/
theorem nonempty_linearEquiv_isotypicComponent_pi
    (n : ℕ) (mu nu : Nat.Partition n) :
    Nonempty
      (↥(isotypicComponent (natIndexedType n) (partitionIndexedType n mu)
          (partitionSubmodule n nu)) ≃ₗ[natIndexedType n]
        (Fin (auxiliaryPartitionNat n mu nu) → ↥(partitionSubmodule n nu))) := by
  have hiso := isotypicComponent_isIsotypicOfType n mu nu
  haveI : Module.Finite ℂ
      (↥(isotypicComponent (natIndexedType n) (partitionIndexedType n mu) (partitionSubmodule n nu))) :=
    partitionComponent_module_finite n mu nu
  haveI : Module.Finite (natIndexedType n)
      (isotypicComponent (natIndexedType n) (partitionIndexedType n mu) (partitionSubmodule n nu)) :=
    Module.Finite.of_restrictScalars_finite ℂ _ _
  obtain ⟨k, ⟨e_R⟩⟩ := hiso.linearEquiv_fun
  rw [← multiplicity_eq_spechtMultiplicity n mu nu k e_R]
  exact ⟨e_R⟩

/-- There is a complex-linear equivalence between the displayed auxiliary subtypes. -/
theorem nonempty_linearEquiv_auxiliary (n : ℕ) (mu nu : Nat.Partition n) :
    Nonempty (↥(partitionComponent n mu nu) ≃ₗ[ℂ]
      (Fin (auxiliaryPartitionNat n mu nu) → ↥(partitionSubmodule n nu))) := by
  obtain ⟨e_R⟩ := nonempty_linearEquiv_isotypicComponent_pi n mu nu
  exact ⟨e_R.restrictScalars ℂ⟩

private theorem trace_pi_diagonal {m : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Module.Free ℂ V]
    (f : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ _ (LinearMap.pi (fun (i : Fin m) => f ∘ₗ LinearMap.proj i)) =
      (m : ℂ) * LinearMap.trace ℂ _ f := by

  set g := LinearMap.pi (fun (i : Fin m) => f ∘ₗ LinearMap.proj i)

  have hg_single : ∀ (i : Fin m) (v : V), g (Pi.single i v) = Pi.single i (f v) := by
    intro i v
    ext k
    simp only [g, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Pi.single_apply]
    split <;> simp [*]

  set b := Module.Free.chooseBasis ℂ V
  haveI : Fintype (Module.Free.ChooseBasisIndex ℂ V) :=
    FiniteDimensional.fintypeBasisIndex b
  set pb := Pi.basis (fun (_ : Fin m) => b)
  rw [LinearMap.trace_eq_matrix_trace ℂ pb g, LinearMap.trace_eq_matrix_trace ℂ b f]

  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  conv_lhs =>
    arg 2; ext p
    rw [show pb (p) = Pi.single p.1 (b p.2) from Pi.basis_apply _ p]
  simp only [hg_single]
  have hrepr : ∀ (i : Fin m) (j : Module.Free.ChooseBasisIndex ℂ V),
      (pb.repr (Pi.single i (f (b j)))) ⟨i, j⟩ = (b.repr (f (b j))) j := by
    intro i j
    simp [pb, Pi.basis_repr, Pi.single_eq_same]
  simp_rw [hrepr]
  simp_rw [Fintype.sum_sigma, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in

/-- An auxiliary assertion whose displayed formal type contains an elided expression. -/
theorem auxiliaryResultE (n : ℕ) (mu nu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n))
    (_e : ↥(partitionComponent n mu nu) ≃ₗ[ℂ]
      (Fin (auxiliaryPartitionNat n mu nu) → ↥(partitionSubmodule n nu))) :
    LinearMap.trace ℂ _ ((auxiliaryPermutationEndomorphism n mu σ).restrict
      (auxiliaryPermutationEndomorphism_mapsTo_auxiliary n mu σ nu)) =
    (auxiliaryPartitionNat n mu nu : ℂ) * LinearMap.trace ℂ _
      (auxiliarySubtypePermutationEndomorphism n nu σ) := by

  set A := natIndexedType n
  set C_R := isotypicComponent A (partitionIndexedType n mu) (partitionSubmodule n nu) with hCR_def

  letI : Module ℂ ↥C_R := (C_R.restrictScalars ℂ).module

  haveI iST : IsScalarTower ℂ A ↥C_R :=
    ⟨fun c a m => Subtype.ext (smul_assoc c a (m : partitionIndexedType n mu))⟩

  haveI : IsSimpleModule A ↥(partitionSubmodule n nu) := partitionSubmodule_isSimpleModule n nu

  have hiso : IsIsotypicOfType A C_R (partitionSubmodule n nu) :=
    IsIsotypicOfType.isotypicComponent _ _ _

  haveI : Module.Finite ℂ ↥C_R := by
    change Module.Finite ℂ ↥(C_R.restrictScalars ℂ)
    infer_instance

  haveI : Module.Finite A ↥C_R :=
    @Module.Finite.of_restrictScalars_finite ℂ A ↥C_R _ _ _ _ _ _ iST _

  obtain ⟨m', ⟨e'⟩⟩ := hiso.linearEquiv_fun

  let e'_ℂ : ↥C_R ≃ₗ[ℂ] (Fin m' → ↥(partitionSubmodule n nu)) :=
    { toFun := e', invFun := e'.symm, map_add' := e'.map_add,
      left_inv := e'.left_inv, right_inv := e'.right_inv,
      map_smul' := fun c x => e'.toLinearMap.map_smul_of_tower c x }

  set f := (auxiliaryPermutationEndomorphism n mu σ).restrict
    (auxiliaryPermutationEndomorphism_mapsTo_auxiliary n mu σ nu) with hf_def

  have hconj_eq : ∀ v i,
      (e'_ℂ.conj f v) i = (MonoidAlgebra.of ℂ _ σ : A) • v i := by
    intro v i
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]

    have hfsmul : (f (e'_ℂ.symm v) : partitionIndexedType n mu) =
        (MonoidAlgebra.of ℂ _ σ : A) • ((e'_ℂ.symm v : ↥C_R) : partitionIndexedType n mu) :=
      permModuleEndomorphism_eq_smul n mu σ _

    have hfsmul' : f (e'_ℂ.symm v) = (MonoidAlgebra.of ℂ _ σ : A) • (e'_ℂ.symm v) :=
      Subtype.ext hfsmul

    have step : e'_ℂ (f (e'_ℂ.symm v)) = (MonoidAlgebra.of ℂ _ σ : A) • v :=
      show e' (f (e'.symm v)) = _ by
        rw [show (f (e'.symm v) : ↥C_R) = (MonoidAlgebra.of ℂ _ σ : A) • (e'.symm v) from
          Subtype.ext (permModuleEndomorphism_eq_smul n mu σ _),
          e'.map_smul, LinearEquiv.apply_symm_apply]
    exact congr_fun step i

  have hact : ∀ (v : ↥(partitionSubmodule n nu)),
      (MonoidAlgebra.of ℂ _ σ : A) • v = auxiliarySubtypePermutationEndomorphism n nu σ v := by
    intro ⟨m, hm⟩; rfl

  have hconj_pi : e'_ℂ.conj f =
      LinearMap.pi (fun (i : Fin m') => auxiliarySubtypePermutationEndomorphism n nu σ ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext; intro w; funext i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply]
    rw [← hact]
    exact hconj_eq w i

  have htrace : LinearMap.trace ℂ _ f =
      (m' : ℂ) * LinearMap.trace ℂ _ (auxiliarySubtypePermutationEndomorphism n nu σ) := by
    calc LinearMap.trace ℂ _ f
        = LinearMap.trace ℂ _ (e'_ℂ.conj f) :=
          (LinearMap.trace_conj' (M := ↥C_R) (N := Fin m' → ↥(partitionSubmodule n nu)) f e'_ℂ).symm
      _ = LinearMap.trace ℂ _ (LinearMap.pi (fun (i : Fin m') =>
            auxiliarySubtypePermutationEndomorphism n nu σ ∘ₗ LinearMap.proj i)) := by rw [hconj_pi]
      _ = (m' : ℂ) * LinearMap.trace ℂ _ (auxiliarySubtypePermutationEndomorphism n nu σ) := trace_pi_diagonal _
  rw [htrace]

  congr 1

  have hdim_e' : Module.finrank ℂ ↥C_R =
      m' * Module.finrank ℂ ↥(partitionSubmodule n nu) := by
    rw [LinearEquiv.finrank_eq e'_ℂ, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_fin,
      smul_eq_mul]
  have hdim_e : Module.finrank ℂ ↥C_R =
      auxiliaryPartitionNat n mu nu * Module.finrank ℂ ↥(partitionSubmodule n nu) := by
    rw [show (Module.finrank ℂ ↥C_R) =
        Module.finrank ℂ ↥(partitionComponent n mu nu) from rfl,
      LinearEquiv.finrank_eq _e, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_fin,
      smul_eq_mul]

  haveI : Nontrivial ↥(partitionSubmodule n nu) :=
    IsSimpleModule.nontrivial (natIndexedType n) _
  have hpos : 0 < Module.finrank ℂ ↥(partitionSubmodule n nu) := Module.finrank_pos
  exact_mod_cast Nat.eq_of_mul_eq_mul_right hpos (hdim_e'.symm.trans hdim_e)

/-- An auxiliary assertion whose displayed formal type contains an elided expression. -/
theorem auxiliaryResultD (n : ℕ) (mu nu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    LinearMap.trace ℂ _ ((auxiliaryPermutationEndomorphism n mu σ).restrict
      (auxiliaryPermutationEndomorphism_mapsTo_auxiliary n mu σ nu)) =
    (auxiliaryPartitionNat n mu nu : ℂ) * auxiliaryPartitionPermutationValue n nu σ := by
  obtain ⟨e⟩ := nonempty_linearEquiv_auxiliary n mu nu
  rw [auxiliaryResultE n mu nu σ e]

  rfl

/-- The natural cast of an auxiliary natural value equals the displayed sum of products of auxiliary values. -/
@[source_ref "Chapter5/Discussion_proof_of_Theorem5.15.1" (role := supporting)]
theorem natCast_auxiliary_eq_sum_auxiliary_mul_auxiliary (n : ℕ) (mu : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (partitionPermutationValue n mu σ : ℂ) =
      ∑ nu : Nat.Partition n,
        (auxiliaryPartitionNat n mu nu : ℂ) * auxiliaryPartitionPermutationValue n nu σ := by

  rw [natCast_auxiliary_eq_trace]

  rw [LinearMap.trace_eq_sum_trace_restrict (partitionComponent_isInternal n mu)
    (auxiliaryPermutationEndomorphism_mapsTo_auxiliary n mu σ)]

  congr 1; ext nu
  exact auxiliaryResultD n mu nu σ

/-- Forms a partition of `n` from a natural-valued finitely supported vector whose entries sum to `n`. -/
noncomputable def partitionOfFinsuppSum {n : ℕ} (v : Fin n →₀ ℕ)
    (hsum : ∑ i : Fin n, v i = n) : Nat.Partition n :=
  Nat.Partition.ofSums n (Finset.univ.val.map v) (by
    change Finset.univ.sum v = n
    exact hsum)

private lemma list_sum_eq_fin_sum_getD (l : List ℕ) (n : ℕ) (h : l.length ≤ n) :
    l.sum = ∑ i : Fin n, l.getD i 0 := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
    cases n with
    | zero => simp [List.length] at h
    | succ n =>
      have ht : t.length ≤ n := Nat.succ_le_succ_iff.mp (by simpa [List.length] using h)
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
      rw [List.sum_cons, ih n ht]

/-- Under the stated pointwise bound, the entries of the difference between the combined exponent and the permutation exponent sum to `n`. -/
theorem sum_add_sub_auxiliaryPermutationFinsupp {n : ℕ} (la : Nat.Partition n)
    (π : Equiv.Perm (Fin n))
    (h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n) :
    ∑ i : Fin n, (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π) i = n := by

  have hcancel := tsub_add_cancel_of_le h

  have key : ∑ i : Fin n, (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π) i +
      ∑ i : Fin n, (auxiliaryPermutationFinsupp n π) i =
      ∑ i : Fin n, (partitionNatFinsupp la) i + ∑ i : Fin n, (auxiliaryFinsupp n) i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1; ext i; exact congr_fun (congr_arg DFunLike.coe hcancel) i

  have hperm : ∑ i : Fin n, (auxiliaryPermutationFinsupp n π) i = ∑ i : Fin n, i.val := by
    simp only [auxiliaryPermutationFinsupp, Finsupp.coe_equivFunOnFinite_symm]
    exact Fintype.sum_equiv π⁻¹ _ _ (fun _ => rfl)

  have hrho : ∑ i : Fin n, (auxiliaryFinsupp n) i = ∑ i : Fin n, i.val := by
    simp only [auxiliaryFinsupp, Finsupp.coe_equivFunOnFinite_symm]
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
    simp only [Fin.revPerm_apply, Fin.val_rev]; omega

  have hla : ∑ i : Fin n, (partitionNatFinsupp la) i = n := by
    have hfs : (partitionNatFinsupp la).sum (fun _ m => m) =
        ∑ i : Fin n, (partitionNatFinsupp la) i :=
      Finsupp.sum_fintype _ _ (fun _ => rfl)
    rw [← hfs, partitionNatFinsupp, Finsupp.equivFunOnFinite_symm_sum]
    have hsorted : (auxiliaryPartitionNatList la).sum = n := by
      unfold auxiliaryPartitionNatList
      have h := congrArg Multiset.sum (Multiset.sort_eq la.parts (· ≥ ·))
      rw [Multiset.sum_coe] at h; linarith [la.parts_sum]
    have hlen : (auxiliaryPartitionNatList la).length ≤ n := by
      calc (auxiliaryPartitionNatList la).length
          ≤ (auxiliaryPartitionNatList la).sum := List.length_le_sum_of_one_le _ (fun i hi => by
            unfold auxiliaryPartitionNatList at hi
            exact la.parts_pos (Multiset.sort_eq la.parts (· ≥ ·) ▸ Multiset.mem_coe.mpr hi))
        _ = n := hsorted
    linarith [list_sum_eq_fin_sum_getD (auxiliaryPartitionNatList la) n hlen]

  omega

private lemma card_filter_getD_eq_count (l : List ℕ) (n : ℕ) (hn : l.length ≤ n)
    (c : ℕ) (hc : c ≠ 0) :
    ((Finset.univ : Finset (Fin n)).val.filter
      (fun i : Fin n => c = l.getD (↑i) 0)).card = l.count c := by

  rw [← Multiset.count_map (f := fun i : Fin n => l.getD (↑i) 0)]

  induction l generalizing n with
  | nil =>
    simp only [List.getD_nil, List.count_nil, Multiset.map_const', Multiset.count_replicate]
    exact if_neg (Ne.symm hc)
  | cons a t ih =>
    cases n with
    | zero => simp at hn
    | succ m =>
      have htlen : t.length ≤ m := by simp at hn; omega

      have huniv : (Finset.univ : Finset (Fin (m + 1))).val =
          (0 : Fin (m + 1)) ::ₘ (Finset.univ : Finset (Fin m)).val.map Fin.succ := by
        rw [Fin.univ_succ, Finset.cons_val, Finset.map_val]
        simp only [Function.Embedding.coeFn_mk]
      rw [huniv, Multiset.map_cons, Multiset.map_map]
      simp only [Function.comp, Fin.val_succ, List.getD_cons_succ,
        Fin.val_zero, List.getD_cons_zero]
      rw [Multiset.count_cons, ih m htlen]
      by_cases h : c = a
      · subst h; simp [List.count_cons_self]
      · rw [if_neg h, List.count_cons_of_ne (Ne.symm h)]; omega

/-- A symmetric polynomial has equal coefficients at the displayed exponent vector and at an auxiliary exponent vector. -/
theorem IsSymmetric.coeff_eq_auxiliary {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P.IsSymmetric)
    (v : Fin n →₀ ℕ) (hsum : ∑ i : Fin n, v i = n) :
    P.coeff v = P.coeff (partitionNatFinsupp (partitionOfFinsuppSum v hsum)) := by

  set w := partitionNatFinsupp (partitionOfFinsuppSum v hsum) with hw_def

  suffices hfiber : ∀ c : ℕ, Fintype.card {i : Fin n // v i = c} =
      Fintype.card {i : Fin n // w i = c} by
    let e := fun c => Fintype.equivOfCardEq (hfiber c)
    let σ : Fin n ≃ Fin n := Equiv.ofFiberEquiv (f := v) (g := w) e
    have hσ : ∀ i, w (σ i) = v i := Equiv.ofFiberEquiv_map e
    have : P.coeff w = P.coeff (w.mapDomain σ.symm) :=
      (IsSymmetric.coeff_mapDomain_perm P hP w σ.symm).symm
    rw [this]; congr 1; ext i
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm]; exact (hσ i).symm

  set p := partitionOfFinsuppSum v hsum
  set M := Finset.univ.val.map (⇑v) with hM_def
  set Mw := Finset.univ.val.map (⇑w) with hMw_def

  have hcard_eq_count : ∀ (f : Fin n →₀ ℕ) (c : ℕ),
      Fintype.card {i : Fin n // f i = c} =
      Multiset.count c (Finset.univ.val.map (⇑f)) := by
    intro f c
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun x _ => ⟨fun h => h.symm, fun h => h.symm⟩)
  intro c
  rw [hcard_eq_count v c, hcard_eq_count w c]

  have hparts : p.parts = M.filter (· ≠ 0) := by
    simp [p, partitionOfFinsuppSum, Nat.Partition.ofSums, M]

  have hsorted_eq : ((auxiliaryPartitionNatList p) : Multiset ℕ) = p.parts :=
    Multiset.sort_eq p.parts (· ≥ ·)

  have hparts_w : Mw.filter (· ≠ 0) = p.parts := by

    rw [hsorted_eq.symm]

    ext c'
    simp only [Multiset.coe_count, Multiset.count_filter]
    split_ifs with hc'
    ·
      rw [show Mw = Finset.univ.val.map (⇑w) from rfl, hw_def, partitionNatFinsupp]
      simp only [Finsupp.coe_equivFunOnFinite_symm, Multiset.count_map]

      have hlen : (auxiliaryPartitionNatList p).length ≤ n := by
        calc (auxiliaryPartitionNatList p).length = p.parts.card := by
              simp [auxiliaryPartitionNatList, Multiset.length_sort]
            _ ≤ p.parts.sum := by
              suffices h : ∀ (s : Multiset ℕ), (∀ x ∈ s, 0 < x) → s.card ≤ s.sum from
                h p.parts (fun x hx => p.parts_pos hx)
              intro s hs
              induction s using Multiset.induction with
              | empty => simp
              | cons a t ih =>
                rw [Multiset.card_cons, Multiset.sum_cons]
                have := hs a (Multiset.mem_cons_self a t)
                have := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
                omega
            _ = n := p.parts_sum
      exact card_filter_getD_eq_count (auxiliaryPartitionNatList p) n hlen c' hc'
    ·
      push Not at hc'
      subst hc'
      symm; rw [List.count_eq_zero]
      exact fun h => Nat.lt_irrefl 0 (p.parts_pos (hsorted_eq ▸ Multiset.mem_coe.mpr h))
  by_cases hc : c = 0
  ·
    subst hc
    have hcardM : M.card = n := by simp [M]
    have hcardMw : Mw.card = n := by simp [Mw]

    have h_count_zero : ∀ s : Multiset ℕ,
        Multiset.count 0 s = s.card - (s.filter (· ≠ 0)).card := by
      intro s
      have h := Multiset.filter_add_not (· ≠ (0 : ℕ)) s
      have hc := congr_arg Multiset.card h
      rw [Multiset.card_add] at hc
      have hfilt : s.filter (fun a => ¬(a ≠ 0)) = s.filter (· = 0) :=
        Multiset.filter_congr (fun x _ => by simp)
      rw [hfilt] at hc
      have hcnt : (s.filter (· = 0)).card = Multiset.count 0 s := by
        rw [Multiset.filter_eq' s 0, Multiset.card_replicate]
      omega
    rw [h_count_zero M, h_count_zero Mw, hcardM, hcardMw]
    congr 1; rw [hparts.symm, hparts_w]
  ·
    have hfv : Multiset.count c (M.filter (· ≠ 0)) = Multiset.count c M :=
      Multiset.count_filter_of_pos hc
    have hfw : Multiset.count c (Mw.filter (· ≠ 0)) = Multiset.count c Mw :=
      Multiset.count_filter_of_pos hc
    rw [← hfv, ← hfw]
    exact congrArg (Multiset.count c) (hparts.symm.trans hparts_w.symm)

private theorem permExponent_revPerm (n : ℕ) :
    auxiliaryPermutationFinsupp n Fin.revPerm = auxiliaryFinsupp n := by
  ext j
  simp only [auxiliaryPermutationFinsupp, auxiliaryFinsupp, Finsupp.coe_equivFunOnFinite_symm]

  show (Fin.revPerm⁻¹ j).val = n - 1 - j.val
  have : Fin.revPerm⁻¹ = (Fin.revPerm (n := n)) := by
    ext i; simp [Fin.revPerm]
  rw [this]; simp [Fin.revPerm_apply]; omega

private theorem rhoShift_le_toFinsupp_add_rhoShift {n : ℕ} (la : Nat.Partition n) :
    auxiliaryFinsupp n ≤ partitionNatFinsupp la + auxiliaryFinsupp n := by
  intro i
  simp only [Finsupp.add_apply, le_add_iff_nonneg_left]
  exact Nat.zero_le _

private theorem toFinsupp_add_rhoShift_sub_rhoShift {n : ℕ} (la : Nat.Partition n) :
    partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryFinsupp n = partitionNatFinsupp la := by
  ext i
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.add_apply]
  omega

private theorem finsuppToPartition_toFinsupp {n : ℕ} (la : Nat.Partition n)
    (hsum : ∑ i : Fin n, partitionNatFinsupp la i = n) :
    partitionOfFinsuppSum (partitionNatFinsupp la) hsum = la := by

  have hsorted : ((auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts :=
    Multiset.sort_eq la.parts (· ≥ ·)
  have hlen : (auxiliaryPartitionNatList la).length ≤ n := by
    calc (auxiliaryPartitionNatList la).length
        ≤ (auxiliaryPartitionNatList la).sum := List.length_le_sum_of_one_le _ (fun i hi => by
          exact la.parts_pos (hsorted ▸ Multiset.mem_coe.mpr hi))
      _ = n := by
          have h := congrArg Multiset.sum hsorted
          rw [Multiset.sum_coe] at h; linarith [la.parts_sum]
  suffices h : (partitionOfFinsuppSum (partitionNatFinsupp la) hsum).parts = la.parts from
    Nat.Partition.ext h
  simp only [partitionOfFinsuppSum, Nat.Partition.ofSums_parts,
    partitionNatFinsupp, Finsupp.coe_equivFunOnFinite_symm]

  rw [← hsorted]

  set sp := (auxiliaryPartitionNatList la)
  have hmap : (List.map (fun i : Fin n => sp.getD i.val 0) (List.finRange n)) =
      sp ++ List.replicate (n - sp.length) 0 := by
    apply List.ext_getElem
    · simp [List.length_finRange]; omega
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_finRange]
      simp only [Fin.val_cast, List.getD]
      by_cases hlt : i < sp.length
      · rw [List.getElem_append_left hlt, sp.getElem?_eq_getElem hlt, Option.getD_some]
      · push Not at hlt
        rw [List.getElem_append_right (by omega), List.getElem_replicate,
            sp.getElem?_eq_none (by omega), Option.getD_none]
  rw [show Finset.univ.val = ↑(List.finRange n) from rfl,
      Multiset.map_coe, hmap]

  simp only [← Multiset.coe_add]
  rw [Multiset.filter_add]
  have hfsp : Multiset.filter (fun x => x ≠ 0) (↑sp : Multiset ℕ) = ↑sp :=
    Multiset.filter_eq_self.mpr (fun x hx => by
      exact Nat.pos_iff_ne_zero.mp (la.parts_pos (hsorted ▸ hx)))
  have hfrep : Multiset.filter (fun x => x ≠ 0)
      (↑(List.replicate (n - sp.length) 0) : Multiset ℕ) = 0 :=
    Multiset.filter_eq_nil.mpr (fun x hx => by
      simp only [ne_eq, not_not]
      exact (List.mem_replicate.mp (Multiset.mem_coe.mp hx)).2)
  rw [hfsp, hfrep, add_zero]

private theorem multiset_entries_eq_of_partition_eq {n : ℕ}
    (la : Nat.Partition n)
    (v : Fin n →₀ ℕ) (hsum : ∑ i, v i = n)
    (heq : partitionOfFinsuppSum v hsum = la) :
    Finset.univ.val.map v = Finset.univ.val.map (partitionNatFinsupp la) := by

  set M₁ := Finset.univ.val.map (v : Fin n → ℕ)
  set M₂ := Finset.univ.val.map (partitionNatFinsupp la : Fin n → ℕ)

  have hcard : M₁.card = M₂.card := by simp [M₁, M₂]

  have hfilt_v : M₁.filter (· ≠ 0) = la.parts := by
    have h1 : (partitionOfFinsuppSum v hsum).parts = M₁.filter (· ≠ 0) := by
      simp [partitionOfFinsuppSum, Nat.Partition.ofSums_parts, M₁]
    rw [heq] at h1; exact h1.symm
  have hla_sum : ∑ i : Fin n, (partitionNatFinsupp la) i = n := by
    have hfs : (partitionNatFinsupp la).sum (fun _ m => m) =
        ∑ i : Fin n, (partitionNatFinsupp la) i :=
      Finsupp.sum_fintype _ _ (fun _ => rfl)
    rw [← hfs, partitionNatFinsupp, Finsupp.equivFunOnFinite_symm_sum]
    have hsorted : (auxiliaryPartitionNatList la).sum = n := by
      unfold auxiliaryPartitionNatList
      have h := congrArg Multiset.sum (Multiset.sort_eq la.parts (· ≥ ·))
      rw [Multiset.sum_coe] at h; linarith [la.parts_sum]
    have hlen : (auxiliaryPartitionNatList la).length ≤ n := by
      calc (auxiliaryPartitionNatList la).length
          ≤ (auxiliaryPartitionNatList la).sum := List.length_le_sum_of_one_le _ (fun i hi => by
            unfold auxiliaryPartitionNatList at hi
            exact la.parts_pos (Multiset.sort_eq la.parts (· ≥ ·) ▸ Multiset.mem_coe.mpr hi))
        _ = n := hsorted
    linarith [list_sum_eq_fin_sum_getD (auxiliaryPartitionNatList la) n hlen]
  have hfilt_la : M₂.filter (· ≠ 0) = la.parts := by
    have hla_eq := finsuppToPartition_toFinsupp la hla_sum
    have h1 : (partitionOfFinsuppSum (partitionNatFinsupp la) hla_sum).parts =
        M₂.filter (· ≠ 0) := by
      simp [partitionOfFinsuppSum, Nat.Partition.ofSums_parts, M₂]
    rw [hla_eq] at h1; exact h1.symm

  have hfilt : M₁.filter (· ≠ 0) = M₂.filter (· ≠ 0) := by rw [hfilt_v, hfilt_la]
  ext a
  by_cases ha : a = 0
  ·
    subst ha

    suffices h : M₁.count 0 = M₂.count 0 from h

    have := congrArg Multiset.card hfilt

    have hc1 : M₁.count 0 + (M₁.filter (· ≠ 0)).card = M₁.card := by
      have := congrArg Multiset.card (Multiset.filter_add_not (p := (· ≠ 0)) M₁)
      simp only [Multiset.card_add] at this
      have : (M₁.filter (fun x => ¬(x ≠ 0))).card = M₁.count 0 := by
        simp only [not_not]
        rw [Multiset.filter_eq' M₁ 0, Multiset.card_replicate]
      omega
    have hc2 : M₂.count 0 + (M₂.filter (· ≠ 0)).card = M₂.card := by
      have := congrArg Multiset.card (Multiset.filter_add_not (p := (· ≠ 0)) M₂)
      simp only [Multiset.card_add] at this
      have : (M₂.filter (fun x => ¬(x ≠ 0))).card = M₂.count 0 := by
        simp only [not_not]
        rw [Multiset.filter_eq' M₂ 0, Multiset.card_replicate]
      omega
    omega
  ·
    have h1 : ∀ M : Multiset ℕ, Multiset.count a (M.filter (fun x => x ≠ 0)) = Multiset.count a M := by
      intro M; exact Multiset.count_filter_of_pos ha
    have : Multiset.count a (M₁.filter (· ≠ 0)) = Multiset.count a (M₂.filter (· ≠ 0)) := by
      rw [hfilt]
    rw [h1, h1] at this; exact this

private theorem inner_product_eq_of_partition_eq {n : ℕ}
    (la : Nat.Partition n)
    (π : Equiv.Perm (Fin n))
    (hle : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n)
    (heq : partitionOfFinsuppSum
      (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
      (sum_add_sub_auxiliaryPermutationFinsupp la π hle) = la) :
    ∑ i : Fin n, ((partitionNatFinsupp la i : ℤ) + (auxiliaryFinsupp n i : ℤ)) *
        (auxiliaryPermutationFinsupp n π i : ℤ) =
    ∑ i : Fin n, ((partitionNatFinsupp la i : ℤ) + (auxiliaryFinsupp n i : ℤ)) *
        (auxiliaryFinsupp n i : ℤ) := by

  set v := partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π with hv_def
  have hsum_v := sum_add_sub_auxiliaryPermutationFinsupp la π hle
  have hmulti := multiset_entries_eq_of_partition_eq la v hsum_v heq

  have hsq_int : ∑ i : Fin n, ((v i : ℤ)) ^ 2 =
      ∑ i : Fin n, ((partitionNatFinsupp la i : ℤ)) ^ 2 := by
    have hmaps : (Finset.univ.val.map v).map (fun x : ℕ => (x : ℤ) ^ 2) =
        (Finset.univ.val.map (partitionNatFinsupp la)).map (fun x : ℕ => (x : ℤ) ^ 2) := by
      rw [hmulti]
    have lhs : (Finset.univ.val.map v).map (fun x : ℕ => (x : ℤ) ^ 2) =
        Finset.univ.val.map (fun i => (v i : ℤ) ^ 2) := by rw [Multiset.map_map]; rfl
    have rhs : (Finset.univ.val.map (partitionNatFinsupp la)).map (fun x : ℕ => (x : ℤ) ^ 2) =
        Finset.univ.val.map (fun i => (partitionNatFinsupp la i : ℤ) ^ 2) := by
      rw [Multiset.map_map]; rfl
    rw [lhs, rhs] at hmaps
    exact congr_arg Multiset.sum hmaps

  have hv_eq : ∀ i : Fin n, (v i : ℤ) =
      (partitionNatFinsupp la i : ℤ) + (auxiliaryFinsupp n i : ℤ) - (auxiliaryPermutationFinsupp n π i : ℤ) := by
    intro i
    simp only [hv_def, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply]
    have := Finsupp.coe_le_coe.mpr hle i
    simp only [Finsupp.coe_add, Pi.add_apply] at this
    omega

  have hsq2 : ∑ i : Fin n, ((partitionNatFinsupp la i : ℤ) + (auxiliaryFinsupp n i : ℤ) -
      (auxiliaryPermutationFinsupp n π i : ℤ)) ^ 2 =
    ∑ i : Fin n, ((partitionNatFinsupp la i : ℤ)) ^ 2 := by
    convert hsq_int using 1; congr 1; ext i; rw [hv_eq]

  have hperm_sq : ∑ i : Fin n, ((auxiliaryPermutationFinsupp n π i : ℤ)) ^ 2 =
      ∑ i : Fin n, ((auxiliaryFinsupp n i : ℤ)) ^ 2 := by

    have h1 : ∑ i : Fin n, ((auxiliaryPermutationFinsupp n π i : ℤ)) ^ 2 =
        ∑ i : Fin n, ((i.val : ℤ)) ^ 2 := by
      have hf : ∀ i : Fin n, (auxiliaryPermutationFinsupp n π i : ℤ) = ((π⁻¹ i).val : ℤ) := by
        intro i; simp [auxiliaryPermutationFinsupp, Finsupp.equivFunOnFinite]
      simp_rw [hf]
      exact Equiv.sum_comp π⁻¹ (fun i : Fin n => ((i.val : ℤ)) ^ 2)

    have h2 : ∑ i : Fin n, ((auxiliaryFinsupp n i : ℤ)) ^ 2 =
        ∑ i : Fin n, ((i.val : ℤ)) ^ 2 := by
      have hg : ∀ i : Fin n, (auxiliaryFinsupp n i : ℤ) = ((Fin.rev i).val : ℤ) := by
        intro i; simp [auxiliaryFinsupp, Finsupp.equivFunOnFinite, Fin.rev]; omega
      simp_rw [hg]
      exact Equiv.sum_comp (Fin.revOrderIso (n := n)).toEquiv
        (fun i : Fin n => ((i.val : ℤ)) ^ 2)
    linarith

  have hsq3 : ∑ i : Fin n, ((partitionNatFinsupp la i : ℤ) + (auxiliaryFinsupp n i : ℤ) -
      (auxiliaryFinsupp n i : ℤ)) ^ 2 =
    ∑ i : Fin n, ((partitionNatFinsupp la i : ℤ)) ^ 2 := by
    congr 1; ext i; congr 1; omega
  have hsq4 : ∑ i : Fin n, ((partitionNatFinsupp la i : ℤ) + (auxiliaryFinsupp n i : ℤ) -
      (auxiliaryPermutationFinsupp n π i : ℤ)) ^ 2 =
    ∑ i : Fin n, ((partitionNatFinsupp la i : ℤ) + (auxiliaryFinsupp n i : ℤ) -
      (auxiliaryFinsupp n i : ℤ)) ^ 2 := by rw [hsq2, hsq3]

  set af : Fin n → ℤ := fun i => (partitionNatFinsupp la i : ℤ) + (auxiliaryFinsupp n i : ℤ)
  set ef : Fin n → ℤ := fun i => (auxiliaryPermutationFinsupp n π i : ℤ)
  set rf : Fin n → ℤ := fun i => (auxiliaryFinsupp n i : ℤ)

  suffices h : ∑ i, af i * rf i = ∑ i, af i * ef i by linarith

  have hzero : ∑ i, ((af i - ef i) ^ 2 - (af i - rf i) ^ 2) = 0 := by
    rw [Finset.sum_sub_distrib]; linarith

  have hpw : ∀ i : Fin n,
      (af i - ef i) ^ 2 - (af i - rf i) ^ 2 =
      2 * af i * (rf i - ef i) + (ef i ^ 2 - rf i ^ 2) := by intro i; ring
  simp_rw [hpw] at hzero
  rw [Finset.sum_add_distrib] at hzero
  have hperm_sq' : ∑ i, (ef i ^ 2 - rf i ^ 2) = 0 := by
    rw [Finset.sum_sub_distrib]; linarith
  have hmul : ∑ i, 2 * af i * (rf i - ef i) = 0 := by linarith
  have hmul' : ∑ i, (af i * rf i - af i * ef i) = 0 := by
    have : ∀ i : Fin n, 2 * af i * (rf i - ef i) = 2 * (af i * rf i - af i * ef i) := by
      intro i; ring
    simp_rw [this, ← Finset.mul_sum] at hmul
    linarith
  linarith [Finset.sum_sub_distrib (f := fun i => af i * rf i) (g := fun i => af i * ef i)
    (s := Finset.univ)]

private theorem shifted_partition_strict_mono {n : ℕ} (la : Nat.Partition n) :
    StrictAnti (fun i : Fin n => (partitionNatFinsupp la i : ℤ) + (auxiliaryFinsupp n i : ℤ)) := by
  intro i j hij
  simp only

  have hla_mono : (partitionNatFinsupp la j : ℤ) ≤ (partitionNatFinsupp la i : ℤ) := by
    simp only [partitionNatFinsupp, Finsupp.coe_equivFunOnFinite_symm]
    apply Int.ofNat_le.mpr
    set sp := (auxiliaryPartitionNatList la)
    have hsorted : sp.Pairwise (· ≥ ·) := Multiset.pairwise_sort la.parts (· ≥ ·)
    by_cases hj : j.val < sp.length
    · have hi : i.val < sp.length := by omega
      have hsorted' := List.pairwise_iff_getElem.mp hsorted i.val j.val hi hj hij
      simp only [List.getD] at hsorted' ⊢
      rw [sp.getElem?_eq_getElem hi, sp.getElem?_eq_getElem hj, Option.getD_some, Option.getD_some]
      exact hsorted'
    · push Not at hj
      simp only [List.getD, sp.getElem?_eq_none (by omega), Option.getD_none]
      exact Nat.zero_le _
  have hρ_strict : (auxiliaryFinsupp n j : ℤ) < (auxiliaryFinsupp n i : ℤ) := by
    simp [auxiliaryFinsupp, Finsupp.equivFunOnFinite]
    omega
  linarith

private theorem rev_of_permExponent_eq_rhoShift {n : ℕ} (π : Equiv.Perm (Fin n))
    (h : auxiliaryPermutationFinsupp n π = auxiliaryFinsupp n) : π = Fin.revPerm := by

  have hinv : π⁻¹ = Fin.revPerm := by
    ext i
    have hi := congr_fun (congr_arg DFunLike.coe h) i
    simp [auxiliaryPermutationFinsupp, auxiliaryFinsupp, Finsupp.equivFunOnFinite] at hi
    simp [Fin.revPerm]
    omega
  have : Fin.revPerm⁻¹ = (Fin.revPerm : Equiv.Perm (Fin n)) := by
    ext i; simp [Fin.revPerm]
  rw [← inv_inv π, hinv, this]

set_option linter.flexible false in
private theorem sum_fin_subset_le_sum_top (n : ℕ) (S : Finset (Fin n))
    (k : ℕ) (hk : k ≤ n) (hcard : S.card = k) :
    S.sum (fun j => (j.val : ℤ)) ≤
    ∑ i ∈ Finset.range k, ((n - 1 - i : ℕ) : ℤ) := by

  suffices hmin : ∀ (T : Finset (Fin n)) (m b : ℕ), T.card = m →
      (∀ j ∈ T, b ≤ j.val) →
      ∑ i ∈ Finset.range m, ((b + i : ℕ) : ℤ) ≤ T.sum (fun j => (j.val : ℤ)) by

    have hSc_card : (Finset.univ \ S).card = n - k := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
        Fintype.card_fin, hcard]
    have hSc_lb := hmin _ _ 0 hSc_card (fun j _ => Nat.zero_le _)
    simp at hSc_lb
    have huniv : Finset.univ.sum (fun j : Fin n => (j.val : ℤ)) =
        ∑ i ∈ Finset.range n, (i : ℤ) := by
      rw [← Fin.sum_univ_eq_sum_range]
    have hS_eq : S.sum (fun j => (j.val : ℤ)) =
        Finset.univ.sum (fun j : Fin n => (j.val : ℤ)) -
        (Finset.univ \ S).sum (fun j => (j.val : ℤ)) := by
      have := Finset.sum_sdiff (f := fun j : Fin n => (j.val : ℤ)) (Finset.subset_univ S)
      linarith
    rw [hS_eq, huniv]
    suffices hrhs : ∑ i ∈ Finset.range k, ((n - 1 - i : ℕ) : ℤ) =
        ∑ i ∈ Finset.range n, (i : ℤ) - ∑ i ∈ Finset.range (n - k), (i : ℤ) by
      linarith
    have : ∑ i ∈ Finset.range k, ((n - 1 - i : ℕ) : ℤ) =
        ∑ i ∈ Finset.range k, ((n : ℤ) - 1 - i) := by
      apply Finset.sum_congr rfl; intro i hi
      simp at hi; omega
    rw [this]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

    have gauss : ∀ p : ℕ, 2 * ∑ i ∈ Finset.range p, (i : ℤ) = (p : ℤ) * ((p : ℤ) - 1) := by
      intro p; induction p with
      | zero => simp
      | succ p ih => rw [Finset.sum_range_succ]; push_cast; linarith
    have g1 := gauss k; have g2 := gauss n; have g3 := gauss (n - k)

    have hnk : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by omega
    rw [hnk] at g3

    nlinarith

  intro T m b hT hb
  induction m generalizing T b with
  | zero =>
    rw [Finset.card_eq_zero.mp hT]; simp
  | succ m ih =>
    have hT_nonempty : T.Nonempty := Finset.card_pos.mp (hT ▸ Nat.succ_pos m)
    obtain ⟨t_min, ht_min_mem, ht_min_le⟩ :=
      T.exists_min_image (fun j : Fin n => j.val) hT_nonempty
    set T' := T.erase t_min
    have hT'_card : T'.card = m := by
      rw [Finset.card_erase_of_mem ht_min_mem, hT]; rfl

    have hT'_lb : ∀ j ∈ T', t_min.val + 1 ≤ j.val := by
      intro j hj
      have hj_mem : j ∈ T := Finset.mem_of_mem_erase hj
      have hj_ne : j ≠ t_min := Finset.ne_of_mem_erase hj
      exact Nat.lt_of_le_of_ne (ht_min_le j hj_mem) (fun h => hj_ne (Fin.ext h).symm)

    have hih := ih T' (t_min.val + 1) hT'_card hT'_lb

    have hsum_split : T.sum (fun j => (j.val : ℤ)) =
        (t_min.val : ℤ) + T'.sum (fun j => (j.val : ℤ)) := by
      rw [← Finset.add_sum_erase _ _ ht_min_mem]
    rw [hsum_split, Finset.sum_range_succ']

    push_cast
    have hb_le : (b : ℤ) ≤ t_min.val := Int.ofNat_le.mpr (hb t_min ht_min_mem)

    have hih' : ∑ i ∈ Finset.range m, ((t_min.val : ℤ) + 1 + i) ≤
        T'.sum (fun j => (j.val : ℤ)) := by
      refine le_trans ?_ hih
      apply Finset.sum_le_sum; intro i _; push_cast; omega

    change ∑ x ∈ Finset.range m, ((b : ℤ) + (↑x + 1)) + ((b : ℤ) + 0) ≤
        (t_min.val : ℤ) + T'.sum (fun j => (j.val : ℤ))
    have h1 : ∑ x ∈ Finset.range m, ((b : ℤ) + (↑x + 1)) ≤
        ∑ x ∈ Finset.range m, ((t_min.val : ℤ) + 1 + ↑x) :=
      Finset.sum_le_sum (fun i _ => by linarith)
    linarith [hih']

set_option linter.flexible false in
private theorem rhoShift_partial_sum_ge {n : ℕ}
    (π : Equiv.Perm (Fin n)) (k : ℕ) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).sum
      (fun i => (auxiliaryPermutationFinsupp n π i : ℤ)) ≤
    (Finset.univ.filter (fun i : Fin n => i.val < k)).sum
      (fun i => (auxiliaryFinsupp n i : ℤ)) := by

  set F := Finset.univ.filter (fun j : Fin n => j.val < k)

  have hLHS : F.sum (fun i => (auxiliaryPermutationFinsupp n π i : ℤ)) =
      (F.map π⁻¹.toEmbedding).sum (fun j => (j.val : ℤ)) := by
    simp only [Finset.sum_map, Equiv.toEmbedding_apply, auxiliaryPermutationFinsupp,
      Finsupp.coe_equivFunOnFinite_symm]

  have hRHS : F.sum (fun i => (auxiliaryFinsupp n i : ℤ)) =
      ∑ i ∈ Finset.range (min k n), ((n - 1 - i : ℕ) : ℤ) := by
    have hrho : ∀ i : Fin n, (auxiliaryFinsupp n i : ℤ) = ((n - 1 - i.val : ℕ) : ℤ) := by
      intro i; simp [auxiliaryFinsupp, Finsupp.equivFunOnFinite]
    simp_rw [hrho]

    apply Finset.sum_nbij (fun i : Fin n => i.val) (fun i hi => ?_) (fun i j hi hj h => ?_)
        (fun b hb => ?_) (fun i hi => ?_)
    ·
      simp [F] at hi; simp; omega
    ·
      exact Fin.val_injective h
    ·
      simp at hb; refine ⟨⟨b, by omega⟩, ?_, rfl⟩
      simp [F]; omega
    ·
      rfl
  rw [hLHS, hRHS]
  by_cases hk : k ≤ n
  · rw [min_eq_left hk]
    refine sum_fin_subset_le_sum_top n _ k hk ?_
    rw [Finset.card_map]

    have hkn := hk
    trans (Finset.range k).card
    · apply Finset.card_eq_of_equiv
      exact {
        toFun := fun ⟨⟨i, hi⟩, hm⟩ => ⟨i, by simp [F] at hm; exact Finset.mem_range.mpr hm⟩
        invFun := fun ⟨i, hm⟩ => ⟨⟨i, by have := Finset.mem_range.mp hm; omega⟩,
          by simp [F]; exact Finset.mem_range.mp hm⟩
        left_inv := fun ⟨⟨i, hi⟩, hm⟩ => by simp
        right_inv := fun ⟨i, hm⟩ => by simp
      }
    · exact Finset.card_range k
  · push Not at hk
    rw [min_eq_right (le_of_lt hk)]

    have hF_univ : F = Finset.univ := by ext ⟨i, hi⟩; simp [F]; omega
    rw [hF_univ]

    have hmap_univ : Finset.univ.map (π⁻¹).toEmbedding = Finset.univ := by
      ext j; simp
    rw [hmap_univ]

    rw [← Fin.sum_univ_eq_sum_range]
    apply le_of_eq
    apply Finset.sum_nbij Fin.rev
      (fun i _ => Finset.mem_univ _)
      (fun i j _ _ h => Fin.rev_injective h)
      (fun j _ => ⟨Fin.rev j, Finset.mem_univ _, Fin.rev_rev j⟩)
      (fun ⟨i, hi⟩ _ => by simp [Fin.rev]; omega)

private lemma sortedParts_take_sum_eq {n : ℕ} (p : Nat.Partition n) (k : ℕ) :
    ((auxiliaryPartitionNatList p).take k).sum =
    (Finset.univ.filter (fun i : Fin n => i.val < k)).sum
      (partitionNatFinsupp p) := by
  set sp := (auxiliaryPartitionNatList p)

  have hsp_mem : ∀ i ∈ sp, 0 < i := fun i hi =>
    p.parts_pos ((Multiset.sort_eq p.parts (· ≥ ·) ▸
      Multiset.mem_coe.mpr hi : i ∈ p.parts))
  have hsp_sum : sp.sum = n := by
    have h1 : (sp : Multiset ℕ).sum = p.parts.sum :=
      congrArg Multiset.sum (Multiset.sort_eq p.parts (· ≥ ·))
    rwa [Multiset.sum_coe, p.parts_sum] at h1
  have hlen : sp.length ≤ n :=
    le_trans (List.length_le_sum_of_one_le _ (fun i hi => hsp_mem i hi))
      (le_of_eq hsp_sum)
  have htake_len : (sp.take k).length ≤ n := by
    simp only [List.length_take]; omega
  rw [list_sum_eq_fin_sum_getD (sp.take k) n htake_len]

  have getD_take_eq : ∀ i : ℕ,
      (sp.take k).getD i 0 = if i < k then sp.getD i 0 else 0 := by
    intro i
    by_cases hik : i < k
    · simp only [hik, ite_true]
      by_cases hil : i < sp.length
      · have hilt : i < (sp.take k).length := by
          simp [List.length_take]; omega
        rw [List.getD_eq_getElem _ _ hilt,
            List.getD_eq_getElem _ _ hil,
            ← List.getElem_take' hil hik]
      · rw [List.getD_eq_default _ _ (by simp [List.length_take]; omega),
            List.getD_eq_default _ _ (by omega)]
    · simp only [hik, ite_false]
      exact List.getD_eq_default _ _
        (by simp [List.length_take]; omega)
  simp_rw [getD_take_eq]
  rw [← Finset.sum_filter]
  congr 1

private lemma finsuppToPartition_sort_perm {n : ℕ}
    (v : Fin n →₀ ℕ) (hsum : ∑ i, v i = n) :
    ∃ σ : Equiv.Perm (Fin n),
      ∀ i, v i = partitionNatFinsupp (partitionOfFinsuppSum v hsum) (σ i) := by
  set w := partitionNatFinsupp (partitionOfFinsuppSum v hsum) with hw_def
  set p := partitionOfFinsuppSum v hsum
  have hcard_eq_count : ∀ (f : Fin n →₀ ℕ) (c : ℕ),
      Fintype.card {i : Fin n // f i = c} =
      Multiset.count c (Finset.univ.val.map (⇑f)) := by
    intro f c
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun x _ => ⟨fun h => h.symm, fun h => h.symm⟩)
  suffices hfiber : ∀ c : ℕ, Fintype.card {i : Fin n // v i = c} =
      Fintype.card {i : Fin n // w i = c} by
    exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hfiber c)),
      fun i => (Equiv.ofFiberEquiv_map _ i).symm⟩
  set M := Finset.univ.val.map (⇑v) with hM_def
  set Mw := Finset.univ.val.map (⇑w) with hMw_def
  have hparts : p.parts = M.filter (· ≠ 0) := by
    simp [p, partitionOfFinsuppSum, Nat.Partition.ofSums, M]
  have hsorted_eq : ((auxiliaryPartitionNatList p) : Multiset ℕ) = p.parts :=
    Multiset.sort_eq p.parts (· ≥ ·)
  have hparts_w : Mw.filter (· ≠ 0) = p.parts := by
    rw [hsorted_eq.symm]
    ext c'
    simp only [Multiset.coe_count, Multiset.count_filter]
    split_ifs with hc'
    · rw [show Mw = Finset.univ.val.map (⇑w) from rfl, hw_def, partitionNatFinsupp]
      simp only [Finsupp.coe_equivFunOnFinite_symm, Multiset.count_map]
      have hlen : (auxiliaryPartitionNatList p).length ≤ n := by
        calc (auxiliaryPartitionNatList p).length = p.parts.card := by
              simp [auxiliaryPartitionNatList, Multiset.length_sort]
            _ ≤ p.parts.sum := by
              suffices h : ∀ (s : Multiset ℕ), (∀ x ∈ s, 0 < x) → s.card ≤ s.sum from
                h p.parts (fun x hx => p.parts_pos hx)
              intro s hs
              induction s using Multiset.induction with
              | empty => simp
              | cons a t ih =>
                rw [Multiset.card_cons, Multiset.sum_cons]
                have := hs a (Multiset.mem_cons_self a t)
                have := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
                omega
            _ = n := p.parts_sum
      exact card_filter_getD_eq_count (auxiliaryPartitionNatList p) n hlen c' hc'
    · push Not at hc'; subst hc'
      symm; rw [List.count_eq_zero]
      exact fun h => Nat.lt_irrefl 0 (p.parts_pos (hsorted_eq ▸ Multiset.mem_coe.mpr h))
  intro c
  rw [hcard_eq_count v c, hcard_eq_count w c]
  by_cases hc : c = 0
  · subst hc
    have hcardM : M.card = n := by simp [M]
    have hcardMw : Mw.card = n := by simp [Mw]
    have h_count_zero : ∀ s : Multiset ℕ,
        Multiset.count 0 s = s.card - (s.filter (· ≠ 0)).card := by
      intro s
      have h := Multiset.filter_add_not (· ≠ (0 : ℕ)) s
      have hc := congr_arg Multiset.card h
      rw [Multiset.card_add] at hc
      have hfilt : s.filter (fun a => ¬(a ≠ 0)) = s.filter (· = 0) :=
        Multiset.filter_congr (fun x _ => by simp)
      rw [hfilt] at hc
      have hcnt : (s.filter (· = 0)).card = Multiset.count 0 s := by
        rw [Multiset.filter_eq' s 0, Multiset.card_replicate]
      omega
    rw [h_count_zero M, h_count_zero Mw, hcardM, hcardMw]
    congr 1; rw [hparts.symm, hparts_w]
  · have hfv : Multiset.count c (M.filter (· ≠ 0)) = Multiset.count c M :=
      Multiset.count_filter_of_pos hc
    have hfw : Multiset.count c (Mw.filter (· ≠ 0)) = Multiset.count c Mw :=
      Multiset.count_filter_of_pos hc
    rw [← hfv, ← hfw]
    exact congrArg (Multiset.count c) (hparts.symm.trans hparts_w.symm)

private lemma finsuppToPartition_toFinsupp_antitone {n : ℕ}
    (v : Fin n →₀ ℕ) (hsum : ∑ i, v i = n) :
    Antitone (fun i : Fin n =>
      partitionNatFinsupp (partitionOfFinsuppSum v hsum) i) := by
  intro i j hij

  change (auxiliaryPartitionNatList (partitionOfFinsuppSum v hsum)).getD j.val 0 ≤
         (auxiliaryPartitionNatList (partitionOfFinsuppSum v hsum)).getD i.val 0
  set sp := (auxiliaryPartitionNatList (partitionOfFinsuppSum v hsum))

  have hsorted : sp.Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
  by_cases hj : j.val < sp.length
  · have hi : i.val < sp.length := lt_of_le_of_lt hij hj
    simp only [List.getD_eq_getElem sp 0 hi, List.getD_eq_getElem sp 0 hj]
    exact List.Pairwise.rel_get_of_le hsorted
      (show (⟨i.val, hi⟩ : Fin sp.length) ≤ ⟨j.val, hj⟩ from hij)
  · simp only [List.getD_eq_default sp 0 (by omega : sp.length ≤ j.val)]
    exact Nat.zero_le _

private theorem sorted_shifted_strict_dominates {n : ℕ}
    (la : Nat.Partition n)
    (π : Equiv.Perm (Fin n))
    (hπ : π ≠ Fin.revPerm)
    (hle : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n) :
    partitionRelation'
      (partitionOfFinsuppSum
        (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
        (sum_add_sub_auxiliaryPermutationFinsupp la π hle))
      la := by
  constructor
  ·

    set v := partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π
    set mu := partitionOfFinsuppSum v (sum_add_sub_auxiliaryPermutationFinsupp la π hle)
    set F := fun k' => Finset.univ.filter (fun i : Fin n => i.val < k')
    intro k

    rw [sortedParts_take_sum_eq la k, sortedParts_take_sum_eq mu k]

    suffices h : ((F k).sum (fun i => (partitionNatFinsupp la i : ℤ))) ≤
        ((F k).sum (fun i => (partitionNatFinsupp mu i : ℤ))) by
      exact_mod_cast h

    have hv_ge_la : (F k).sum (fun i => (partitionNatFinsupp la i : ℤ)) ≤
        (F k).sum (fun i => (v i : ℤ)) := by

      have hrho := rhoShift_partial_sum_ge π k

      suffices hsuff : (F k).sum (fun i => (v i : ℤ)) -
          (F k).sum (fun i => (partitionNatFinsupp la i : ℤ)) =
          (F k).sum (fun i => (auxiliaryFinsupp n i : ℤ)) -
           (F k).sum (fun i => (auxiliaryPermutationFinsupp n π i : ℤ)) by
        linarith
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      congr 1; ext i
      have hle_i : auxiliaryPermutationFinsupp n π i ≤ (partitionNatFinsupp la + auxiliaryFinsupp n) i := hle i
      simp only [Finsupp.coe_add, Pi.add_apply] at hle_i
      simp only [v, Finsupp.coe_tsub, Finsupp.coe_add, Pi.add_apply, Pi.sub_apply]
      push_cast [Nat.cast_sub hle_i]; ring

    obtain ⟨σ, hσ⟩ := finsuppToPartition_sort_perm v (sum_add_sub_auxiliaryPermutationFinsupp la π hle)

    have hanti_mu : Antitone (fun i : Fin n => (partitionNatFinsupp mu i : ℤ)) := by
      intro i j hij; exact Nat.cast_le.mpr (finsuppToPartition_toFinsupp_antitone v _ hij)
    have hmono : Monovary (fun i : Fin n => (partitionNatFinsupp mu i : ℤ))
        (fun i : Fin n => if (i : Fin n).val < k then (1 : ℤ) else 0) := by
      intro i j hlt
      simp only at hlt
      split_ifs at hlt with h1 h2
      · omega
      · omega
      · exact hanti_mu (show j ≤ i by omega)
      · omega
    have hrearr := hmono.sum_smul_comp_perm_le_sum_smul (σ := σ⁻¹)
    simp only [zsmul_eq_mul, mul_ite, mul_one, mul_zero] at hrearr

    have hLHS : ∑ i : Fin n, (if (σ⁻¹ i).val < k then (partitionNatFinsupp mu i : ℤ) else 0) =
        ∑ j : Fin n, (if j.val < k then (v j : ℤ) else 0) := by
      rw [← Equiv.sum_comp σ]

      congr 1; ext j
      simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
      split_ifs with h
      · exact_mod_cast (hσ j).symm
      · rfl

    have hRHS : ∑ i : Fin n, (if i.val < k then (partitionNatFinsupp mu i : ℤ) else 0) =
        (F k).sum (fun i => (partitionNatFinsupp mu i : ℤ)) := by
      rw [← Finset.sum_filter]

    have hLHS' : ∑ j : Fin n, (if j.val < k then (v j : ℤ) else 0) =
        (F k).sum (fun i => (v i : ℤ)) := by
      rw [← Finset.sum_filter]

    have hv_le_mu : (F k).sum (fun i => (v i : ℤ)) ≤
        (F k).sum (fun i => (partitionNatFinsupp mu i : ℤ)) := by
      calc (F k).sum (fun i => (v i : ℤ))
          = ∑ j : Fin n, (if j.val < k then (v j : ℤ) else 0) := hLHS'.symm
        _ = ∑ i : Fin n, (if (σ⁻¹ i).val < k then (partitionNatFinsupp mu i : ℤ) else 0) := hLHS.symm
        _ ≤ ∑ i : Fin n, (if i.val < k then (partitionNatFinsupp mu i : ℤ) else 0) := by

          convert hrearr using 2 <;> rfl
        _ = (F k).sum (fun i => (partitionNatFinsupp mu i : ℤ)) := hRHS
    linarith
  ·

    intro heq
    apply hπ

    have hip := inner_product_eq_of_partition_eq la π hle heq

    have hmono := shifted_partition_strict_mono la

    set f : Fin n → ℤ := fun i => (partitionNatFinsupp la i : ℤ) + (auxiliaryFinsupp n i : ℤ)
    set g : Fin n → ℤ := fun i => (auxiliaryFinsupp n i : ℤ)

    set σ := (π⁻¹ : Equiv.Perm (Fin n)).trans Fin.revPerm

    have hg_anti : StrictAnti g := by
      intro i j hij
      simp [g, auxiliaryFinsupp, Finsupp.equivFunOnFinite]
      omega
    have hfg : Monovary f g := by

      intro i j hlt

      have hji : j < i := by
        by_contra h; push Not at h
        rcases h.eq_or_lt with rfl | hlt2
        · exact lt_irrefl _ hlt
        · exact not_lt.mpr (le_of_lt (hg_anti hlt2)) hlt

      exact le_of_lt (hmono hji)

    have hsum_eq : ∑ i, f i * g (σ i) = ∑ i, f i * g i := by

      suffices hsuff : ∀ i, g (σ i) = (auxiliaryPermutationFinsupp n π i : ℤ) by
        simp_rw [hsuff]; exact hip
      intro i
      simp [σ, g, auxiliaryFinsupp, auxiliaryPermutationFinsupp, Finsupp.equivFunOnFinite, Fin.revPerm]
      omega

    have hm := hfg.sum_mul_comp_perm_eq_sum_mul_iff.mp hsum_eq

    have hanti : Antitone (g ∘ σ) := by
      intro i j hij
      by_contra h; push Not at h

      have := hm h

      rcases hij.eq_or_lt with rfl | hlt
      · exact lt_irrefl _ h
      · exact not_le.mpr (hmono hlt) this

    have hpe : auxiliaryPermutationFinsupp n π = auxiliaryFinsupp n := by
      ext i

      have hpi_anti : Antitone (fun i : Fin n => (π⁻¹ i : Fin n)) := by
        intro i j hij

        have h1 : ∀ k : Fin n, (g ∘ σ) k = ((π⁻¹ k).val : ℤ) := by
          intro k
          simp [σ, g, auxiliaryFinsupp, Finsupp.equivFunOnFinite, Fin.revPerm]
          omega
        have := hanti hij
        rw [h1 i, h1 j] at this
        exact Fin.le_iff_val_le_val.mpr (Int.le_of_ofNat_le_ofNat this)

      have hcomp_mono : StrictMono ((⇑π⁻¹ : Fin n → Fin n) ∘ Fin.rev) := by
        intro i j hij
        have hrev := Fin.rev_strictAnti hij
        have hle := hpi_anti (le_of_lt hrev)

        exact lt_of_le_of_ne hle (fun h => by
          have := Fin.rev_injective ((π⁻¹).injective h)
          exact absurd this (ne_of_lt hij))

      have hcomp_surj : Function.Surjective ((⇑π⁻¹ : Fin n → Fin n) ∘ Fin.rev) :=
        (π⁻¹.surjective).comp Fin.rev_surjective
      have hid : ∀ k : Fin n, (π⁻¹ (Fin.rev k) : ℕ) = k.val := by
        intro k
        exact Fin.coe_orderIso_apply (hcomp_mono.orderIsoOfSurjective _ hcomp_surj) k

      have key : (π⁻¹ i : ℕ) = (Fin.revPerm i).val := by
        have := hid (Fin.rev i)
        simp [Fin.rev_rev] at this
        simp [Fin.revPerm]
        omega
      simp [auxiliaryPermutationFinsupp, auxiliaryFinsupp, Finsupp.equivFunOnFinite, Fin.revPerm] at key ⊢
      omega
    exact rev_of_permExponent_eq_rhoShift π hpe

private noncomputable def alternatingKostkaInt {n : ℕ}
    (la nu : Nat.Partition n) : ℤ :=
  ∑ π : Equiv.Perm (Fin n),
    (Equiv.Perm.sign π : ℤ) *
      if h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
      then (auxiliaryPartitionNat n
        (partitionOfFinsuppSum
          (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
          (sum_add_sub_auxiliaryPermutationFinsupp la π h))
        nu : ℤ)
      else 0

private theorem alternatingKostka_eq_cast {n : ℕ} (la nu : Nat.Partition n) :
    (∑ π : Equiv.Perm (Fin n),
      (Equiv.Perm.sign π : ℤ) •
        (if h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
         then ((auxiliaryPartitionNat n
           (partitionOfFinsuppSum
             (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
             (sum_add_sub_auxiliaryPermutationFinsupp la π h))
           nu : ℕ) : ℂ)
         else (0 : ℂ))) = (alternatingKostkaInt la nu : ℂ) := by
  simp only [alternatingKostkaInt, Int.cast_sum, Int.cast_mul]
  congr 1; ext π
  rw [zsmul_eq_mul]
  congr 1
  split <;> simp

private theorem alternatingKostka_diag {n : ℕ} (la : Nat.Partition n) :
    alternatingKostkaInt la la = Equiv.Perm.sign (Fin.revPerm (n := n)) := by
  unfold alternatingKostkaInt
  set rev := Fin.revPerm (n := n)
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ rev)]

  have hrev_le : auxiliaryPermutationFinsupp n rev ≤ partitionNatFinsupp la + auxiliaryFinsupp n :=
    permExponent_revPerm n ▸ rhoShift_le_toFinsupp_add_rhoShift la
  simp only [dif_pos hrev_le]
  have hsub : partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n rev =
      partitionNatFinsupp la := by
    rw [permExponent_revPerm]; exact toFinsupp_add_rhoShift_sub_rhoShift la

  have hrest : ∑ π ∈ Finset.univ.erase rev,
      (Equiv.Perm.sign π : ℤ) *
        (if h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
        then (auxiliaryPartitionNat n
          (partitionOfFinsuppSum
            (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
            (sum_add_sub_auxiliaryPermutationFinsupp la π h))
          la : ℤ)
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro π hπ
    rw [Finset.mem_erase] at hπ
    by_cases hle : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
    · simp only [dif_pos hle]
      have hdom := sorted_shifted_strict_dominates la π hπ.1 hle
      rw [auxiliaryPartitionNat_eq_zero_of_auxiliaryRelation n _ la hdom]
      simp
    · simp [dif_neg hle]
  rw [hrest, add_zero]

  suffices ∀ (v : Fin n →₀ ℕ) (_ : v = partitionNatFinsupp la)
      (hsum : ∑ i, v i = n),
      (Equiv.Perm.sign rev : ℤ) *
        (auxiliaryPartitionNat n (partitionOfFinsuppSum v hsum) la : ℤ) =
      (Equiv.Perm.sign rev : ℤ) by
    exact this _ hsub _
  intro v hv hsum
  subst hv
  rw [finsuppToPartition_toFinsupp, auxiliaryPartitionNat_self]
  simp

private theorem coeff_eq_youngsRule_expansion'
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (π : Equiv.Perm (Fin n))
    (h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n) :
    (MvPolynomial.coeff
      (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
      (permutationPolynomialAuxiliary n σ) : ℂ) =
    ∑ nu : Nat.Partition n,
      ((auxiliaryPartitionNat n
        (partitionOfFinsuppSum
          (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
          (sum_add_sub_auxiliaryPermutationFinsupp la π h))
        nu : ℕ) : ℂ) * auxiliaryPartitionPermutationValue n nu σ := by
  rw [IsSymmetric.coeff_eq_auxiliary _ (auxiliaryPolynomial_isSymmetric n σ)]
  · rw [← natCast_auxiliary_eq_coeff]
    exact natCast_auxiliary_eq_sum_auxiliary_mul_auxiliary n _ σ

set_option linter.flexible false in
/-- The displayed sum of paired auxiliary values at a permutation and its inverse is `n!` for equal partitions and zero otherwise. -/
@[source_ref "Chapter5/Discussion_proof_of_Frobenius_character_formula" (role := supporting)]
theorem sum_auxiliaryPartitionPermutationValue_mul_inv (n : ℕ) (ν μ : Nat.Partition n) :
    ∑ σ : Equiv.Perm (Fin n),
      auxiliaryPartitionPermutationValue n ν σ * auxiliaryPartitionPermutationValue n μ σ⁻¹ =
    (Nat.factorial n : ℂ) * if ν = μ then 1 else 0 := by
  classical
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) = (Nat.factorial n : ℂ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hne : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 := by
    rw [hcard]; exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  haveI : NeZero (Fintype.card (Equiv.Perm (Fin n)) : ℂ) := ⟨hne⟩
  haveI : Invertible (Fintype.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero hne
  have horth := FDRep.char_orthonormal (partitionFDRep n ν) (partitionFDRep n μ)
  rw [partitionFDRep_iso_iff] at horth
  simp only [partitionFDRep_character_eq_auxiliary] at horth
  rw [Nat.card_eq_fintype_card] at horth

  rw [mul_comm] at horth
  rw [← div_eq_mul_inv] at horth
  rw [div_eq_iff hne] at horth
  rw [mul_comm, hcard] at horth
  by_cases h : ν = μ <;> simp [h] at horth ⊢ <;> exact horth

/-- Two partitions are equal when their displayed auxiliary values agree for every permutation. -/
theorem eq_of_auxiliaryPartitionPermutationValue_eq (n : ℕ) {μ ν : Nat.Partition n}
    (h : ∀ σ, auxiliaryPartitionPermutationValue n μ σ = auxiliaryPartitionPermutationValue n ν σ) : μ = ν := by
  by_contra hne
  have h1 := sum_auxiliaryPartitionPermutationValue_mul_inv n μ ν
  have h2 := sum_auxiliaryPartitionPermutationValue_mul_inv n μ μ
  rw [if_neg hne, mul_zero] at h1
  rw [if_pos rfl, mul_one] at h2
  have key : (∑ σ : Equiv.Perm (Fin n),
        auxiliaryPartitionPermutationValue n μ σ * auxiliaryPartitionPermutationValue n ν σ⁻¹) =
      ∑ σ : Equiv.Perm (Fin n),
        auxiliaryPartitionPermutationValue n μ σ * auxiliaryPartitionPermutationValue n μ σ⁻¹ :=
    Finset.sum_congr rfl fun σ _ => by rw [h σ⁻¹]
  rw [key, h2] at h1
  exact Nat.factorial_ne_zero n (by exact_mod_cast h1)

private theorem alternatingKostka_norm_sq_eq_one {n : ℕ} (la : Nat.Partition n) :
    ∑ nu : Nat.Partition n, alternatingKostkaInt la nu ^ 2 = 1 := by

  have hinj : Function.Injective (Int.cast : ℤ → ℂ) := Int.cast_injective
  apply hinj; push_cast

  set L : Nat.Partition n → ℂ := fun nu => (alternatingKostkaInt la nu : ℂ)
  set χ := fun nu σ => auxiliaryPartitionPermutationValue n nu σ
  set θ : Equiv.Perm (Fin n) → ℂ := fun σ =>
    ∑ π : Equiv.Perm (Fin n),
      (Equiv.Perm.sign π : ℤ) •
        (if h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
         then (MvPolynomial.coeff
                 (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
                 (permutationPolynomialAuxiliary n σ) : ℂ)
         else 0)
  have hn : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

  have hY : ∀ σ, θ σ = ∑ nu : Nat.Partition n, L nu * χ nu σ := by
    intro σ; simp only [θ, L, χ]

    have hstep : ∀ (π : Equiv.Perm (Fin n)),
        (Equiv.Perm.sign π : ℤ) •
          (if h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
           then (MvPolynomial.coeff
                   (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
                   (permutationPolynomialAuxiliary n σ) : ℂ)
           else 0) =
        ∑ nu : Nat.Partition n,
          ((Equiv.Perm.sign π : ℤ) •
            (if h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
             then ((auxiliaryPartitionNat n
               (partitionOfFinsuppSum
                 (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
                 (sum_add_sub_auxiliaryPermutationFinsupp la π h))
               nu : ℕ) : ℂ)
             else 0)) *
            auxiliaryPartitionPermutationValue n nu σ := by
      intro π
      by_cases hle : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
      · simp only [dif_pos hle]
        rw [coeff_eq_youngsRule_expansion' n la σ π hle, Finset.smul_sum]
        congr 1; ext nu; rw [smul_mul_assoc]
      · simp only [dif_neg hle, smul_zero]
        exact (Finset.sum_eq_zero (fun nu _ => by simp)).symm
    conv_lhs => arg 2; ext π; rw [hstep π]
    rw [Finset.sum_comm]
    congr 1; ext nu; rw [← Finset.sum_mul]; congr 1
    exact alternatingKostka_eq_cast la nu

  have hI : ∀ σ, θ σ⁻¹ = θ σ := by
    intro σ; simp only [θ, permutationPolynomialAuxiliary_inv]

  have hC : ∑ σ : Equiv.Perm (Fin n), θ σ ^ 2 = (Nat.factorial n : ℂ) := by

    set α_fun : Fin n → ℕ := fun i => (partitionNatFinsupp la + auxiliaryFinsupp n) i

    have hα_inj : Function.Injective α_fun := by
      have hsa := shifted_partition_strict_mono la

      have hsa' : StrictAnti (fun i : Fin n => (α_fun i : ℤ)) := by
        intro i j hij
        have := hsa hij
        simp only [α_fun, Finsupp.coe_add, Pi.add_apply, Nat.cast_add] at this ⊢
        exact this
      exact fun i j h => hsa'.injective (by exact_mod_cast h : (α_fun i : ℤ) = α_fun j)

    have hvcd := double_signed_permutation_sum_eq_one_of_injective n α_fun hα_inj

    suffices hrel : ∑ σ : Equiv.Perm (Fin n), θ σ ^ 2 =
        (Nat.factorial n : ℂ) *
          (∑ π : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
            ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
            (if (∀ i, (π⁻¹ i : Fin n).val ≤ α_fun i) ∧
                (∀ i, (τ⁻¹ i : Fin n).val ≤ α_fun i)
             then MvPowerSeries.coeff
                    (RepresentationTheory.Combinatorics.PermutationPowerSeries.auxiliaryFinsupp n
                      (fun i => α_fun i - (π⁻¹ i : Fin n).val)
                      (fun i => α_fun i - (τ⁻¹ i : Fin n).val))
                    (auxiliaryPowerSeries n ℂ)
             else 0)) by
      rw [hrel, hvcd, mul_one]

    simp only [θ, sq]
    simp_rw [Finset.sum_mul_sum]

    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext π; rw [Finset.sum_comm]

    rw [Finset.mul_sum]
    congr 1; ext π; rw [Finset.mul_sum]
    congr 1; ext τ

    have hcond : ∀ (σ : Equiv.Perm (Fin n)),
        (auxiliaryPermutationFinsupp n σ ≤ partitionNatFinsupp la + auxiliaryFinsupp n) ↔
        (∀ i, (σ⁻¹ i : Fin n).val ≤ α_fun i) := by
      intro σ; constructor <;> intro hle i <;>
        (have := hle i;
         simp only [auxiliaryPermutationFinsupp, Finsupp.coe_equivFunOnFinite_symm, α_fun,
           Finsupp.coe_add, Pi.add_apply] at this ⊢; exact this)

    have hsub_eq : ∀ (σ : Equiv.Perm (Fin n)),
        ⇑(partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n σ) =
        (fun i => α_fun i - (σ⁻¹ i : Fin n).val) := by
      intro σ; ext i
      simp [α_fun, auxiliaryPermutationFinsupp, Finsupp.equivFunOnFinite, Finsupp.coe_tsub,
        Pi.sub_apply, Finsupp.coe_add, Pi.add_apply]

    by_cases hπ : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n <;>
    by_cases hτ : auxiliaryPermutationFinsupp n τ ≤ partitionNatFinsupp la + auxiliaryFinsupp n
    ·
      simp only [dif_pos hπ, dif_pos hτ, zsmul_eq_mul]
      rw [if_pos ⟨(hcond π).mp hπ, (hcond τ).mp hτ⟩]

      have hpbc := sum_auxiliaryPolynomial_coeff_mul_eq_factorial_mul_auxiliaryPowerSeries_coeff_auxiliaryFinsupp n
        (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
        (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n τ)
        (sum_add_sub_auxiliaryPermutationFinsupp la π hπ)
        (sum_add_sub_auxiliaryPermutationFinsupp la τ hτ)
      rw [hsub_eq π, hsub_eq τ] at hpbc

      simp_rw [mul_mul_mul_comm ((Equiv.Perm.sign π : ℤ) : ℂ) _ ((Equiv.Perm.sign τ : ℤ) : ℂ)]
      rw [← Finset.mul_sum, hpbc]; ring
    ·
      simp only [dif_pos hπ, dif_neg hτ, zsmul_eq_mul, mul_zero]
      rw [if_neg (fun h => hτ ((hcond τ).mpr h.2))]
      simp only [mul_zero]
      exact Finset.sum_eq_zero fun σ _ => by ring
    ·
      simp only [dif_neg hπ, dif_pos hτ, zsmul_eq_mul]
      rw [if_neg (fun h => hπ ((hcond π).mpr h.1))]
      simp only [mul_zero]
      exact Finset.sum_eq_zero fun σ _ => by ring
    ·
      simp only [dif_neg hπ, dif_neg hτ, zsmul_eq_mul, mul_zero]
      rw [if_neg (fun h => hπ ((hcond π).mpr h.1))]
      simp only [mul_zero]
      exact Finset.sum_eq_zero fun σ _ => by ring

  have hP : (Nat.factorial n : ℂ) * ∑ nu, L nu ^ 2 =
      ∑ σ : Equiv.Perm (Fin n), θ σ * θ σ⁻¹ := by

    conv_rhs => arg 2; ext σ; rw [hY σ, hY σ⁻¹]

    simp_rw [Finset.sum_mul_sum]

    simp_rw [mul_mul_mul_comm (L _) _ (L _)]

    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := Finset.univ (α := Equiv.Perm (Fin n)))]

    simp_rw [← Finset.mul_sum]

    simp only [χ]
    simp_rw [sum_auxiliaryPartitionPermutationValue_mul_inv n]

    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

    simp_rw [← sq, ← Finset.sum_mul]
    ring

  have hEq : ∑ σ : Equiv.Perm (Fin n), θ σ * θ σ⁻¹ =
      ∑ σ : Equiv.Perm (Fin n), θ σ ^ 2 := by
    congr 1; ext σ; rw [hI σ, sq]
  suffices h : (Nat.factorial n : ℂ) * ∑ nu, L nu ^ 2 = Nat.factorial n by
    exact mul_left_cancel₀ hn (h.trans (mul_one _).symm)
  calc (Nat.factorial n : ℂ) * ∑ nu, L nu ^ 2
      = ∑ σ : Equiv.Perm (Fin n), θ σ * θ σ⁻¹ := hP
    _ = ∑ σ : Equiv.Perm (Fin n), θ σ ^ 2 := hEq
    _ = Nat.factorial n := hC

private theorem alternating_kostka_eq_zero_of_strict_dom {n : ℕ}
    (la nu : Nat.Partition n)
    (hne : la ≠ nu)
    (_hdom : partitionRelation nu la) :
    (∑ π : Equiv.Perm (Fin n),
      (Equiv.Perm.sign π : ℤ) •
        (if h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
         then ((auxiliaryPartitionNat n
           (partitionOfFinsuppSum
             (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
             (sum_add_sub_auxiliaryPermutationFinsupp la π h))
           nu : ℕ) : ℂ)
         else (0 : ℂ))) = 0 := by
  rw [alternatingKostka_eq_cast]
  suffices h : alternatingKostkaInt la nu = 0 by simp [h]

  have h_norm := alternatingKostka_norm_sq_eq_one la

  have h_diag := alternatingKostka_diag la
  have h_diag_sq : alternatingKostkaInt la la ^ 2 = 1 := by
    rw [h_diag]
    rcases Int.isUnit_iff.mp (Units.isUnit (Equiv.Perm.sign (Fin.revPerm (n := n)))) with h | h <;>
      simp [h]

  have hsplit : alternatingKostkaInt la la ^ 2 +
      ∑ x ∈ Finset.univ.erase la, alternatingKostkaInt la x ^ 2 =
      ∑ nu : Nat.Partition n, alternatingKostkaInt la nu ^ 2 :=
    Finset.add_sum_erase _ (fun nu => alternatingKostkaInt la nu ^ 2) (Finset.mem_univ la)

  have hrest : ∑ x ∈ Finset.univ.erase la, alternatingKostkaInt la x ^ 2 = 0 := by
    linarith

  have hmem : nu ∈ Finset.univ.erase la :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
  have hnu_sq : alternatingKostkaInt la nu ^ 2 = 0 := by
    have h1 := Finset.single_le_sum (fun x _ => sq_nonneg (alternatingKostkaInt la x)) hmem
    have h2 := sq_nonneg (alternatingKostkaInt la nu)
    omega
  exact sq_eq_zero_iff.mp hnu_sq

/-- An auxiliary assertion whose type was unavailable from the displayed formal output. -/
@[source_ref "Chapter5/Discussion_proof_of_Frobenius_character_formula" (role := supporting),
  source_ref "Chapter5/Discussion_proof_of_Theorem5.15.1" (role := supporting)]
theorem auxiliaryResultA {n : ℕ} (la nu : Nat.Partition n) :
    (∑ π : Equiv.Perm (Fin n),
      (Equiv.Perm.sign π : ℤ) •
        (if h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
         then ((auxiliaryPartitionNat n
           (partitionOfFinsuppSum
             (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
             (sum_add_sub_auxiliaryPermutationFinsupp la π h))
           nu : ℕ) : ℂ)
         else (0 : ℂ))) =
      (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) •
        (if la = nu then (1 : ℂ) else (0 : ℂ)) := by
  set rev := Fin.revPerm (n := n)
  by_cases hla_nu : la = nu
  ·
    subst hla_nu
    simp only [if_true]

    have hrev_mem : rev ∈ Finset.univ := Finset.mem_univ _

    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hrev_mem]
    have hrev_le : auxiliaryPermutationFinsupp n rev ≤ partitionNatFinsupp la + auxiliaryFinsupp n :=
      permExponent_revPerm n ▸ rhoShift_le_toFinsupp_add_rhoShift la

    have hrest : (∑ π ∈ Finset.univ \ {rev},
        (Equiv.Perm.sign π : ℤ) •
          (if h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
           then ((auxiliaryPartitionNat n
             (partitionOfFinsuppSum
               (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
               (sum_add_sub_auxiliaryPermutationFinsupp la π h))
             la : ℕ) : ℂ)
           else (0 : ℂ))) = 0 := by

      apply Finset.sum_eq_zero
      intro π hπ
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hπ

      by_cases hle : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
      · simp only [dif_pos hle]

        have hdom : partitionRelation'
            (partitionOfFinsuppSum
              (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
              (sum_add_sub_auxiliaryPermutationFinsupp la π hle))
            la := sorted_shifted_strict_dominates la π hπ hle
        rw [auxiliaryPartitionNat_eq_zero_of_auxiliaryRelation n _ la hdom]
        simp
      · simp [dif_neg hle]
    rw [hrest, add_zero]
    simp only [dif_pos hrev_le]

    have hsub : partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n rev =
        partitionNatFinsupp la := by
      rw [permExponent_revPerm]; exact toFinsupp_add_rhoShift_sub_rhoShift la

    suffices h : ∀ (v : Fin n →₀ ℕ) (hv : v = partitionNatFinsupp la)
        (hsum : ∑ i, v i = n),
        (Equiv.Perm.sign rev : ℤ) • ((auxiliaryPartitionNat n
          (partitionOfFinsuppSum v hsum) la : ℕ) : ℂ) =
        (Equiv.Perm.sign rev : ℤ) • (1 : ℂ) by
      exact h _ hsub _
    intro v hv hsum
    subst hv
    rw [finsuppToPartition_toFinsupp]
    congr 1
    simp [auxiliaryPartitionNat_self]
  ·
    simp only [if_neg hla_nu, smul_zero]
    by_cases hdom : partitionRelation nu la
    ·

      exact alternating_kostka_eq_zero_of_strict_dom la nu hla_nu hdom
    ·

      apply Finset.sum_eq_zero
      intro π _
      by_cases hle : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
      · simp only [dif_pos hle]
        have h_not_dom_sort : ¬ partitionRelation nu
            (partitionOfFinsuppSum
              (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
              (sum_add_sub_auxiliaryPermutationFinsupp la π hle)) := by
          intro habs
          apply hdom
          by_cases hπ : π = rev
          ·
            subst hπ
            have hsub : partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n rev =
                partitionNatFinsupp la := by
              rw [permExponent_revPerm]; exact toFinsupp_add_rhoShift_sub_rhoShift la
            suffices ∀ (v : Fin n →₀ ℕ) (_ : v = partitionNatFinsupp la)
                (hsum : ∑ i, v i = n),
                partitionRelation nu (partitionOfFinsuppSum v hsum) →
                partitionRelation nu la by
              exact this _ hsub _ habs
            intro v hv hsum hd
            subst hv
            rwa [finsuppToPartition_toFinsupp] at hd
          ·
            have hsdom := sorted_shifted_strict_dominates la π hπ hle

            intro k
            exact le_trans (hsdom.1 k) (habs k)
        rw [auxiliaryPartitionNat_eq_zero_of_not_auxiliaryRelation n _ nu h_not_dom_sort]
        simp
      · simp [dif_neg hle]

private theorem coeff_eq_youngsRule_expansion
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (π : Equiv.Perm (Fin n))
    (h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n) :
    (MvPolynomial.coeff
      (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
      (permutationPolynomialAuxiliary n σ) : ℂ) =
    ∑ nu : Nat.Partition n,
      ((auxiliaryPartitionNat n
        (partitionOfFinsuppSum
          (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
          (sum_add_sub_auxiliaryPermutationFinsupp la π h))
        nu : ℕ) : ℂ) * auxiliaryPartitionPermutationValue n nu σ := by

  rw [IsSymmetric.coeff_eq_auxiliary _ (auxiliaryPolynomial_isSymmetric n σ)]
  ·
    rw [← natCast_auxiliary_eq_coeff]

    exact natCast_auxiliary_eq_sum_auxiliary_mul_auxiliary n _ σ

private theorem smul_dite_sum {α : Prop} [Decidable α] {ι : Type*} [Fintype ι]
    (z : ℤ) (f : α → ι → ℂ) :
    z • (if h : α then ∑ i, f h i else (0 : ℂ)) =
      ∑ i, z • (if h : α then f h i else 0) := by
  by_cases hα : α
  · simp only [dif_pos hα, Finset.smul_sum]
  · simp only [dif_neg hα, smul_zero, Finset.sum_const_zero]

private theorem smul_dite_mul {α : Prop} [Decidable α]
    (z : ℤ) (f : α → ℂ) (c : ℂ) :
    z • (if h : α then f h * c else (0 : ℂ)) =
      (z • (if h : α then f h else 0)) * c := by
  by_cases hα : α
  · simp only [dif_pos hα, smul_mul_assoc]
  · simp only [dif_neg hα, smul_zero, zero_mul]

/-- An auxiliary assertion whose type was unavailable from the displayed formal output. -/
@[source_ref "Chapter5/Discussion_proof_of_Theorem5.15.1" (role := supporting)]
theorem auxiliaryResultC
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) • auxiliaryPartitionPermutationValue n la σ =
      ∑ π : Equiv.Perm (Fin n),
        (Equiv.Perm.sign π : ℤ) • (if _h : auxiliaryPermutationFinsupp n π ≤
            partitionNatFinsupp la + auxiliaryFinsupp n
          then (MvPolynomial.coeff
            (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
            (permutationPolynomialAuxiliary n σ) : ℂ) else 0) := by

  have hcoeff : ∀ (π : Equiv.Perm (Fin n)),
      (Equiv.Perm.sign π : ℤ) •
        (if h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
          then (MvPolynomial.coeff
            (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
            (permutationPolynomialAuxiliary n σ) : ℂ) else 0) =
      ∑ nu : Nat.Partition n,
        ((Equiv.Perm.sign π : ℤ) •
          (if h : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
            then ((auxiliaryPartitionNat n
              (partitionOfFinsuppSum
                (partitionNatFinsupp la + auxiliaryFinsupp n - auxiliaryPermutationFinsupp n π)
                (sum_add_sub_auxiliaryPermutationFinsupp la π h))
              nu : ℕ) : ℂ)
            else 0)) * auxiliaryPartitionPermutationValue n nu σ := by
    intro π
    by_cases hle : auxiliaryPermutationFinsupp n π ≤ partitionNatFinsupp la + auxiliaryFinsupp n
    · simp only [dif_pos hle]
      rw [coeff_eq_youngsRule_expansion n la σ π hle, Finset.smul_sum]
      congr 1; ext nu; rw [smul_mul_assoc]
    · simp only [dif_neg hle, smul_zero]
      exact (Finset.sum_eq_zero (fun nu _ => by simp)).symm

  conv_rhs => arg 2; ext π; rw [hcoeff π]
  rw [Finset.sum_comm]

  conv_rhs => arg 2; ext y; rw [← Finset.sum_mul, auxiliaryResultA la y]

  simp_rw [smul_mul_assoc]
  rw [← Finset.smul_sum]

  congr 1

  have hvan : ∀ y ∈ Finset.univ, y ≠ la →
      (if la = y then (1 : ℂ) else 0) * auxiliaryPartitionPermutationValue n y σ = 0 :=
    fun y _ hy => by simp [Ne.symm hy]
  rw [Finset.sum_eq_single la (fun b hb hne => hvan b hb hne)
    (fun h => absurd (Finset.mem_univ la) h)]
  simp

end

/-- Relates a signed scalar multiple of an auxiliary value to a coefficient of a polynomial product. -/
@[source_ref "Chapter5/Theorem5.15.1" (role := supporting)]
theorem auxiliarySignSmul_eq_coefficient
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) • auxiliaryPartitionPermutationValue n la σ =
      MvPolynomial.coeff (partitionNatFinsupp la + auxiliaryFinsupp n)
        (auxiliaryPolynomial n * permutationPolynomialAuxiliary n σ) := by
  rw [auxiliaryResultC,
      auxiliaryResultB]

end RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter
