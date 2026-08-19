/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial
import RepresentationTheory.Alignment.Attribute

/-!
# Partition polynomials with an independent variable count

This module develops the coefficient formula for partitions in an independently chosen number of
polynomial variables.
-/

namespace RepresentationTheory.PartitionPolynomials

open scoped BigOperators

open RepresentationTheory.PermutationPolynomialAuxiliary
  RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
  RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter
  RepresentationTheory.SymmetricGroup.PartitionDominance

/-- The auxiliary multivariate polynomial associated with a permutation. -/
noncomputable def auxiliaryPermutationPolynomial (N n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin N) ℂ :=
  (σ.cycleType.map (MvPolynomial.psum (Fin N) ℂ)).prod *
    MvPolynomial.psum (Fin N) ℂ 1 ^ (n - σ.support.card)

/-- Associates an exponent vector indexed by `Fin N` to a partition. -/
@[source_ref"Chapter5/Introduction_5.15"(role:=supporting)]
noncomputable def partitionExponentVector {n : ℕ} (N : ℕ) (la : Nat.Partition n) :
    Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (auxiliaryPartitionNatList la).getD i 0)

/-- Associates a derived exponent vector indexed by `Fin N` to a partition. -/
noncomputable def partitionDerivedExponentVector {n : ℕ} (N : ℕ) (la : Nat.Partition n) :
    Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun i => (auxiliaryPartitionNatList la).getD (N - 1 - i.val) 0 + i.val)

/-- A ring homomorphism from polynomials in `Fin (N + 1)` variables to polynomials in `Fin N`
variables. -/
noncomputable def dropFirstVariableHom (N : ℕ) :
    MvPolynomial (Fin (N + 1)) ℂ →+* MvPolynomial (Fin N) ℂ :=
  (Polynomial.constantCoeff :
      Polynomial (MvPolynomial (Fin N) ℂ) →+* MvPolynomial (Fin N) ℂ).comp
    (MvPolynomial.finSuccEquiv ℂ N).toRingHom

/-- The variable homomorphism sends the zero-indexed variable to zero. -/
lemma dropFirstVariableHom_X_zero (N : ℕ) :
    dropFirstVariableHom N (MvPolynomial.X 0) = 0 := by
  simp [dropFirstVariableHom, MvPolynomial.finSuccEquiv_X_zero]

/-- The variable homomorphism sends each successor-indexed variable to its predecessor-indexed
variable. -/
lemma dropFirstVariableHom_X_succ (N : ℕ) (i : Fin N) :
    dropFirstVariableHom N (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [dropFirstVariableHom, MvPolynomial.finSuccEquiv_X_succ]

/-- The variable homomorphism preserves a positive polynomial sum after lowering the ambient
size. -/
lemma dropFirstVariableHom_psum (N m : ℕ) (hm : 0 < m) :
    dropFirstVariableHom N (MvPolynomial.psum (Fin (N + 1)) ℂ m) =
      MvPolynomial.psum (Fin N) ℂ m := by
  simp [MvPolynomial.psum, Fin.sum_univ_succ, dropFirstVariableHom_X_zero,
    dropFirstVariableHom_X_succ, hm.ne']

private lemma dropFirstMv_psumProduct (N : ℕ) (s : Multiset ℕ)
    (hs : ∀ m ∈ s, 0 < m) :
    dropFirstVariableHom N ((s.map (MvPolynomial.psum (Fin (N + 1)) ℂ)).prod) =
      (s.map (MvPolynomial.psum (Fin N) ℂ)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons m s ih =>
      have hm : 0 < m := hs m (by simp)
      have hs' : ∀ a ∈ s, 0 < a := fun a ha => hs a (by simp [ha])
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul,
        dropFirstVariableHom_psum N m hm, ih hs']

private lemma dropFirstMv_cycleTypeProduct (N n : ℕ) (σ : Equiv.Perm (Fin n)) :
    dropFirstVariableHom N
        ((σ.cycleType.map (MvPolynomial.psum (Fin (N + 1)) ℂ)).prod) =
      (σ.cycleType.map (MvPolynomial.psum (Fin N) ℂ)).prod := by
  apply dropFirstMv_psumProduct
  intro m hm
  exact lt_trans Nat.zero_lt_one (Equiv.Perm.one_lt_of_mem_cycleType hm)

/-- Applying the variable homomorphism to the auxiliary permutation polynomial lowers its
ambient size. -/
theorem dropFirstVariableHom_auxiliaryPermutationPolynomial
    (N n : ℕ) (σ : Equiv.Perm (Fin n)) :
    dropFirstVariableHom N (auxiliaryPermutationPolynomial (N + 1) n σ) =
      auxiliaryPermutationPolynomial N n σ := by
  simp only [auxiliaryPermutationPolynomial, map_mul, map_pow,
    dropFirstMv_cycleTypeProduct,
    dropFirstVariableHom_psum N 1 Nat.zero_lt_one]

/-- Computes the image of an auxiliary polynomial under the variable homomorphism. -/
theorem dropFirstVariableHom_auxiliaryPolynomial (N : ℕ) :
    dropFirstVariableHom N (auxiliaryPolynomial (N + 1)) =
      (∏ i : Fin N, MvPolynomial.X i) * auxiliaryPolynomial N := by
  simp [auxiliaryPolynomial, Fin.prod_univ_succ,
    Fin.prod_Ioi_succ, dropFirstVariableHom_X_zero, dropFirstVariableHom_X_succ]

/-- The exponent vector assigning one to every index of `Fin N`. -/
noncomputable def allOneExponentVector (N : ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

/-- Describes the derived exponent vector at successor ambient size by consing zero and adding the
all-one vector. -/
lemma partitionDerivedExponentVector_succ_eq_cons_add_allOneExponentVector
    {n N : ℕ} (la : Nat.Partition n)
    (hlen : (auxiliaryPartitionNatList la).length ≤ N) :
    partitionDerivedExponentVector (N + 1) la =
      (partitionDerivedExponentVector N la + allOneExponentVector N).cons 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (auxiliaryPartitionNatList la).getD N 0 = 0
    exact List.getD_eq_default (auxiliaryPartitionNatList la) 0 hlen
  · simp only [Finsupp.cons_succ, Finsupp.coe_add, Pi.add_apply]
    have hidx : N - (j.val + 1) = N - 1 - j.val := by omega
    change (auxiliaryPartitionNatList la).getD (N - (j.val + 1)) 0 + (j.val + 1) =
      (auxiliaryPartitionNatList la).getD (N - 1 - j.val) 0 + j.val + 1
    rw [hidx]
    omega

/-- The monomial with the all-one exponent vector is the product of all variables. -/
lemma monomial_allOneExponentVector (N : ℕ) :
    MvPolynomial.monomial (allOneExponentVector N) (1 : ℂ) =
      ∏ i : Fin N, MvPolynomial.X i := by
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
    Finsupp.prod_fintype]
  · simp [allOneExponentVector]
  · intro i
    simp

/-- Shows that the indicated coefficient is unchanged when the ambient size is increased by one. -/
theorem coefficient_partitionDerivedExponentVector_mul_auxiliaryPermutationPolynomial_succ
    {n N : ℕ} (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (hlen : (auxiliaryPartitionNatList la).length ≤ N) :
    MvPolynomial.coeff (partitionDerivedExponentVector (N + 1) la)
        (auxiliaryPolynomial (N + 1) * auxiliaryPermutationPolynomial (N + 1) n σ) =
      MvPolynomial.coeff (partitionDerivedExponentVector N la)
        (auxiliaryPolynomial N * auxiliaryPermutationPolynomial N n σ) := by
  rw [partitionDerivedExponentVector_succ_eq_cons_add_allOneExponentVector la hlen]
  rw [← MvPolynomial.finSuccEquiv_coeff_coeff
    (partitionDerivedExponentVector N la + allOneExponentVector N)
    (auxiliaryPolynomial (N + 1) * auxiliaryPermutationPolynomial (N + 1) n σ) 0]
  change MvPolynomial.coeff (partitionDerivedExponentVector N la + allOneExponentVector N)
      (dropFirstVariableHom N
        (auxiliaryPolynomial (N + 1) * auxiliaryPermutationPolynomial (N + 1) n σ)) = _
  rw [map_mul, dropFirstVariableHom_auxiliaryPolynomial,
    dropFirstVariableHom_auxiliaryPermutationPolynomial, mul_assoc]
  rw [← monomial_allOneExponentVector]
  simpa using coeff_add_monomial_mul (allOneExponentVector N)
    (partitionDerivedExponentVector N la) 1
    (auxiliaryPolynomial N * auxiliaryPermutationPolynomial N n σ)

private lemma rename_psumProduct (N : ℕ) (e : Equiv.Perm (Fin N))
    (s : Multiset ℕ) :
    MvPolynomial.rename e
        ((s.map (MvPolynomial.psum (Fin N) ℂ)).prod) =
      (s.map (MvPolynomial.psum (Fin N) ℂ)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons m s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul,
        MvPolynomial.rename_psum, ih]

/-- Renaming variables by a permutation leaves the auxiliary permutation polynomial unchanged. -/
lemma rename_auxiliaryPermutationPolynomial (N n : ℕ) (σ : Equiv.Perm (Fin n))
    (e : Equiv.Perm (Fin N)) :
    MvPolynomial.rename e (auxiliaryPermutationPolynomial N n σ) =
      auxiliaryPermutationPolynomial N n σ := by
  simp only [auxiliaryPermutationPolynomial, map_mul, map_pow,
    rename_psumProduct, MvPolynomial.rename_psum]

/-- Renaming variables in the auxiliary polynomial scales it by the sign of the renaming
permutation. -/
lemma rename_auxiliaryPolynomial_eq_sign_smul (N : ℕ) (e : Equiv.Perm (Fin N)) :
    MvPolynomial.rename e (auxiliaryPolynomial N) =
      (Equiv.Perm.sign e : ℤ) • auxiliaryPolynomial N := by
  unfold auxiliaryPolynomial
  simp only [map_prod, map_sub, MvPolynomial.rename_X]
  rw [e.prod_Ioi_comp_eq_sign_mul_prod
    (f := fun i j => MvPolynomial.X j - MvPolynomial.X i)]
  · simp [zsmul_eq_mul]
  · intro i j
    ring

/-- Describes the derived partition exponent vector using reversal, the partition exponent vector,
and an auxiliary vector. -/
lemma partitionDerivedExponentVector_eq_reversed_partitionExponentVector_add_auxiliary
    {n N : ℕ} (la : Nat.Partition n) :
    partitionDerivedExponentVector N la =
      (partitionExponentVector N la + auxiliaryFinsupp N).mapDomain
        (Fin.revPerm (n := N)) := by
  ext i
  have hidx : N - (i.val + 1) = N - 1 - i.val := by omega
  rw [show i = Fin.revPerm (Fin.revPerm i) by simp [Fin.revPerm]]
  rw [Finsupp.mapDomain_apply (Fin.revPerm (n := N)).injective]
  simp [partitionDerivedExponentVector, partitionExponentVector, auxiliaryFinsupp,
    Fin.revPerm, hidx]
  omega

/-- Identifies the partition exponent vector with the corresponding auxiliary construction. -/
lemma partitionExponentVector_eq_auxiliary {n : ℕ} (la : Nat.Partition n) :
    partitionExponentVector n la = partitionNatFinsupp la := rfl

/-- Relates the auxiliary permutation polynomial with equal ambient and permutation sizes to an
auxiliary polynomial. -/
lemma auxiliaryPermutationPolynomial_self_eq_auxiliary (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    auxiliaryPermutationPolynomial n n σ = permutationPolynomialAuxiliary n σ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Specializes the coefficient computation to equal partition and ambient sizes. -/
theorem coefficient_partitionDerivedExponentVector_mul_auxiliaryPermutationPolynomial_self
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.coeff (partitionDerivedExponentVector n la)
        (auxiliaryPolynomial n * auxiliaryPermutationPolynomial n n σ) =
      auxiliaryPartitionPermutationValue n la σ := by
  let e := Fin.revPerm (n := n)
  let α := partitionNatFinsupp la + auxiliaryFinsupp n
  let F := auxiliaryPolynomial n * permutationPolynomialAuxiliary n σ
  have hrename := MvPolynomial.coeff_rename_mapDomain e e.injective F α
  have hexp : partitionDerivedExponentVector n la = α.mapDomain e := by
    simpa [α, e, partitionExponentVector_eq_auxiliary] using
      (partitionDerivedExponentVector_eq_reversed_partitionExponentVector_add_auxiliary
        (N := n) la)
  have hrename' :
      (Equiv.Perm.sign e : ℤ) •
          MvPolynomial.coeff (partitionDerivedExponentVector n la) F =
        MvPolynomial.coeff α F := by
    rw [← hexp] at hrename
    have hp : MvPolynomial.rename e (permutationPolynomialAuxiliary n σ) =
        permutationPolynomialAuxiliary n σ := by
      simpa only [auxiliaryPermutationPolynomial_self_eq_auxiliary] using
        (rename_auxiliaryPermutationPolynomial n n σ e)
    rw [map_mul, rename_auxiliaryPolynomial_eq_sign_smul, hp] at hrename
    rw [smul_mul_assoc, MvPolynomial.coeff_smul] at hrename
    simpa only [F] using hrename
  have hmain := auxiliarySignSmul_eq_coefficient n la σ
  change (Equiv.Perm.sign e : ℤ) • auxiliaryPartitionPermutationValue n la σ =
    MvPolynomial.coeff α F at hmain
  rw [← hmain] at hrename'
  rcases Int.isUnit_iff.mp (Units.isUnit (Equiv.Perm.sign e)) with hs | hs
  · simpa only [auxiliaryPermutationPolynomial_self_eq_auxiliary, F, hs, one_zsmul]
      using hrename'
  · simpa only [auxiliaryPermutationPolynomial_self_eq_auxiliary, F, hs, neg_zsmul,
      one_zsmul, neg_inj] using hrename'

private theorem frobeniusCoefficientRev_add {n N : ℕ} (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hlen : (auxiliaryPartitionNatList la).length ≤ N) (k : ℕ) :
    MvPolynomial.coeff (partitionDerivedExponentVector (N + k) la)
        (auxiliaryPolynomial (N + k) * auxiliaryPermutationPolynomial (N + k) n σ) =
      MvPolynomial.coeff (partitionDerivedExponentVector N la)
        (auxiliaryPolynomial N * auxiliaryPermutationPolynomial N n σ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hlen' : (auxiliaryPartitionNatList la).length ≤ N + k :=
        le_trans hlen (Nat.le_add_right N k)
      exact
        (coefficient_partitionDerivedExponentVector_mul_auxiliaryPermutationPolynomial_succ
          la σ hlen').trans ih

/-- Computes a coefficient at the derived partition exponent vector after multiplication by the
auxiliary permutation polynomial. -/
theorem coefficient_partitionDerivedExponentVector_mul_auxiliaryPermutationPolynomial
    {n N : ℕ} (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (hlen : (auxiliaryPartitionNatList la).length ≤ N) :
    MvPolynomial.coeff (partitionDerivedExponentVector N la)
        (auxiliaryPolynomial N * auxiliaryPermutationPolynomial N n σ) =
      auxiliaryPartitionPermutationValue n la σ := by
  let L := (auxiliaryPartitionNatList la).length
  have hLn : L ≤ n := by
    change (auxiliaryPartitionNatList la).length ≤ n
    have hsum : (auxiliaryPartitionNatList la).sum = n := by
      unfold auxiliaryPartitionNatList
      have h := congrArg Multiset.sum (Multiset.sort_eq la.parts (· ≥ ·))
      rw [Multiset.sum_coe] at h
      linarith [la.parts_sum]
    calc
      (auxiliaryPartitionNatList la).length ≤ (auxiliaryPartitionNatList la).sum :=
        List.length_le_sum_of_one_le _ (fun i hi => by
          have := Partition.zero_lt_of_mem_sortedParts la i hi
          omega)
      _ = n := hsum
  have hN := frobeniusCoefficientRev_add la σ (N := L) (le_refl L) (N - L)
  have hn := frobeniusCoefficientRev_add la σ (N := L) (le_refl L) (n - L)
  rw [Nat.add_sub_of_le hlen] at hN
  rw [Nat.add_sub_of_le hLn] at hn
  exact hN.trans
    (hn.symm.trans
      (coefficient_partitionDerivedExponentVector_mul_auxiliaryPermutationPolynomial_self
        n la σ))

set_option backward.isDefEq.respectTransparency false in
/-- Expresses a signed auxiliary value as a coefficient of a multivariate polynomial. -/
@[source_ref"Chapter5/Theorem5.15.1"(role:=supporting),
  source_ref"Chapter5/Discussion_proof_of_Frobenius_character_formula"(role:=primary)]
theorem signedAuxiliaryValue_eq_coefficient {n N : ℕ} (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hlen : (auxiliaryPartitionNatList la).length ≤ N) :
    (Equiv.Perm.sign (Fin.revPerm (n := N)) : ℤ) •
        auxiliaryPartitionPermutationValue n la σ =
      MvPolynomial.coeff (partitionExponentVector N la + auxiliaryFinsupp N)
        (auxiliaryPolynomial N * auxiliaryPermutationPolynomial N n σ) := by
  let e := Fin.revPerm (n := N)
  let α := partitionExponentVector N la + auxiliaryFinsupp N
  let F := auxiliaryPolynomial N * auxiliaryPermutationPolynomial N n σ
  have hrename := MvPolynomial.coeff_rename_mapDomain e e.injective F α
  have hexp : partitionDerivedExponentVector N la = α.mapDomain e := by
    simpa [α, e] using
      partitionDerivedExponentVector_eq_reversed_partitionExponentVector_add_auxiliary
        (N := N) la
  rw [← hexp] at hrename
  rw [map_mul, rename_auxiliaryPolynomial_eq_sign_smul,
    rename_auxiliaryPermutationPolynomial N n σ e] at hrename
  rw [smul_mul_assoc, MvPolynomial.coeff_smul] at hrename
  rw [coefficient_partitionDerivedExponentVector_mul_auxiliaryPermutationPolynomial la σ hlen]
    at hrename
  simpa only [e, α, F] using hrename

end RepresentationTheory.PartitionPolynomials
