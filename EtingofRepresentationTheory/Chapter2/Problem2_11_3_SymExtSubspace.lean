import EtingofRepresentationTheory.Chapter2.Problem2_11_3_SymExtPow

/-!
# Problem 2.11.3(e): the symmetric and exterior powers as subspaces of `V^{⊗ n}`

Etingof's part (e) asks, in characteristic zero, for a natural identification of the *quotients*

* `S^n V = V^{⊗ n} / ⟨T - s T⟩` with the subspace of `T ∈ V^{⊗ n}` satisfying `T = s T` for every
  transposition `s`, and
* `⋀^n V = V^{⊗ n} / ⟨T : s T = T for some transposition s⟩` with the subspace of `T` satisfying
  `T = -s T` for every transposition `s`.

The identification is by averaging. Writing `(n !)⁻¹ ∑_σ σ` for the symmetrizer and
`(n !)⁻¹ ∑_σ sgn(σ) σ` for the antisymmetrizer, each is an idempotent on `V^{⊗ n}` whose image is
the corresponding subspace and whose kernel is exactly the relation subspace cut out by the
corresponding quotient. Both need `n !` invertible in `k`, which is why the problem assumes
characteristic zero; the results below carry the weaker hypothesis `(n.factorial : k) ≠ 0`
instead, and `Etingof.Problem2_11_3.factorial_cast_ne_zero` supplies it from `CharZero k`.

Everything happens inside `PiTensorProduct`; Mathlib's `ExteriorAlgebra` is deliberately not
involved.

## Main definitions

* `Etingof.Problem2_11_3.symTensorSubmodule` : the symmetric tensors `{T | ∀ s, s T = T}`.
* `Etingof.Problem2_11_3.altTensorSubmodule` : the antisymmetric tensors `{T | ∀ s, s T = -T}`.
* `Etingof.Problem2_11_3.symmetrizer` and `antisymmetrizer` : the two averaging operators.

## Main results

* `Etingof.Problem2_11_3.symPowEquivSymTensor` : `S^n V ≃ₗ[k] symTensorSubmodule k V n`.
* `Etingof.Problem2_11_3.extPowEquivAltTensor` : `⋀^n V ≃ₗ[k] altTensorSubmodule k V n`.
* `Etingof.Problem2_11_3.symPowEquivSymTensor_mkQ` and `extPowEquivAltTensor_mkQ` : each
  isomorphism precomposed with the quotient map is the corresponding averaging operator. This is
  the compatibility that makes the identifications the natural ones.
* `Etingof.Problem2_11_3.ker_symmetrizer` and `ker_antisymmetrizer` : the kernels of the averaging
  operators are exactly the relation subspaces defining `S^n V` and `⋀^n V`.
* `Etingof.Problem2_11_3.range_symmetrizer` and `range_antisymmetrizer` : their ranges are exactly
  the symmetric and antisymmetric subspaces.
-/

namespace Etingof.Problem2_11_3

open PiTensorProduct
open scoped TensorProduct

section Subspaces

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]

/-- The subspace of **symmetric tensors**: those `T ∈ V^{⊗ n}` fixed by every transposition of the
tensor factors. Part (e) identifies it with the book's `S^n V`. -/
def symTensorSubmodule (n : ℕ) : Submodule k (TensorPow k V n) where
  carrier := {T | ∀ i j : Fin n, i ≠ j → permAct (Equiv.swap i j) T = T}
  add_mem' hx hy i j hij := by rw [map_add, hx i j hij, hy i j hij]
  zero_mem' i j _ := map_zero _
  smul_mem' c x hx i j hij := by rw [map_smul, hx i j hij]

/-- The subspace of **antisymmetric tensors**: those `T ∈ V^{⊗ n}` negated by every transposition
of the tensor factors. Part (e) identifies it with the book's `⋀^n V`. -/
def altTensorSubmodule (n : ℕ) : Submodule k (TensorPow k V n) where
  carrier := {T | ∀ i j : Fin n, i ≠ j → permAct (Equiv.swap i j) T = -T}
  add_mem' hx hy i j hij := by rw [map_add, hx i j hij, hy i j hij, neg_add]
  zero_mem' i j _ := by rw [map_zero, neg_zero]
  smul_mem' c x hx i j hij := by rw [map_smul, hx i j hij, smul_neg]

variable {k V}

/-- Membership in the symmetric-tensor subspace is invariance under every transposition. -/
lemma mem_symTensorSubmodule_iff {n : ℕ} {T : TensorPow k V n} :
    T ∈ symTensorSubmodule k V n ↔ ∀ i j : Fin n, i ≠ j → permAct (Equiv.swap i j) T = T :=
  Iff.rfl

/-- Membership in the alternating-tensor subspace is negation under every transposition. -/
lemma mem_altTensorSubmodule_iff {n : ℕ} {T : TensorPow k V n} :
    T ∈ altTensorSubmodule k V n ↔ ∀ i j : Fin n, i ≠ j → permAct (Equiv.swap i j) T = -T :=
  Iff.rfl

/-- The sign of a permutation, as a scalar. -/
lemma sign_cast_mul_self (k : Type*) [Field k] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : k) * ((Equiv.Perm.sign σ : ℤ) : k) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-- A symmetric tensor is fixed by *every* permutation of the tensor factors, not merely by the
transpositions appearing in the definition. -/
lemma permAct_eq_self_of_mem_symTensorSubmodule {n : ℕ} {T : TensorPow k V n}
    (hT : T ∈ symTensorSubmodule k V n) (σ : Equiv.Perm (Fin n)) : permAct σ T = T := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact permAct_one T
  | swap_mul τ i j hij ihτ => rw [permAct_mul, ihτ, hT i j hij]

/-- An antisymmetric tensor is scaled by the sign of every permutation of the tensor factors. -/
lemma permAct_eq_sign_smul_of_mem_altTensorSubmodule {n : ℕ} {T : TensorPow k V n}
    (hT : T ∈ altTensorSubmodule k V n) (σ : Equiv.Perm (Fin n)) :
    permAct σ T = ((Equiv.Perm.sign σ : ℤ) : k) • T := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul τ i j hij ihτ =>
      rw [permAct_mul, ihτ, map_smul, hT i j hij, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
        Units.val_mul]
      push_cast
      rw [smul_neg, neg_mul, one_mul, neg_smul]

end Subspaces

section Averaging

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]

/-- The **symmetrizer** `T ↦ (n !)⁻¹ ∑_σ σ T` on `V^{⊗ n}`. -/
noncomputable def symmetrizer (n : ℕ) : TensorPow k V n →ₗ[k] TensorPow k V n :=
  (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), (permAct σ).toLinearMap

/-- The **antisymmetrizer** `T ↦ (n !)⁻¹ ∑_σ sgn(σ) σ T` on `V^{⊗ n}`. -/
noncomputable def antisymmetrizer (n : ℕ) : TensorPow k V n →ₗ[k] TensorPow k V n :=
  (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign σ : ℤ) : k) • (permAct σ).toLinearMap

variable {V}

/-- In characteristic zero `n !` is invertible, which is the hypothesis the averaging operators
need. -/
lemma factorial_cast_ne_zero [CharZero k] (n : ℕ) : (n.factorial : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr n.factorial_ne_zero

/-- A transposition of `Fin n` forces `2 ≤ n`, and then `n !` invertible forces `2` invertible. -/
lemma two_ne_zero_of_factorial_cast_ne_zero {n : ℕ} (hfac : (n.factorial : k) ≠ 0) (hn : 2 ≤ n) :
    (2 : k) ≠ 0 := by
  intro h2
  refine hfac ?_
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (by norm_num) hn
  rw [hm]
  push_cast
  rw [h2, zero_mul]

/-- The symmetric group on Fin n has cardinality n factorial. -/
lemma card_perm_fin (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  simp [Fintype.card_perm]

variable {k}

/-- Two distinct indices in `Fin n` force `2 ≤ n`. -/
lemma two_le_of_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) : 2 ≤ n := by
  have hi := i.isLt
  have hj := j.isLt
  have : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  omega

/-- Evaluation of the symmetrizer is the average over all permutations. -/
lemma symmetrizer_apply {n : ℕ} (T : TensorPow k V n) :
    symmetrizer k V n T = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), permAct σ T := by
  simp [symmetrizer, LinearMap.sum_apply]

/-- Evaluation of the antisymmetrizer is the signed average over all permutations. -/
lemma antisymmetrizer_apply {n : ℕ} (T : TensorPow k V n) :
    antisymmetrizer k V n T
      = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : k) • permAct σ T := by
  simp [antisymmetrizer, LinearMap.sum_apply]

/-- Summing a constant tensor over all permutations scales it by n factorial. -/
lemma sum_const_perm {n : ℕ} (T : TensorPow k V n) :
    (∑ _σ : Equiv.Perm (Fin n), T) = (n.factorial : k) • T := by
  rw [Finset.sum_const, Finset.card_univ, card_perm_fin, Nat.cast_smul_eq_nsmul]

/-- Precomposing the symmetrizer with a permutation of the tensor factors changes nothing. -/
lemma symmetrizer_permAct {n : ℕ} (τ : Equiv.Perm (Fin n)) (T : TensorPow k V n) :
    symmetrizer k V n (permAct τ T) = symmetrizer k V n T := by
  rw [symmetrizer_apply, symmetrizer_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ => ?_
  rw [Equiv.coe_mulRight, permAct_mul]

/-- The image of the symmetrizer consists of symmetric tensors. -/
lemma permAct_symmetrizer {n : ℕ} (τ : Equiv.Perm (Fin n)) (T : TensorPow k V n) :
    permAct τ (symmetrizer k V n T) = symmetrizer k V n T := by
  rw [symmetrizer_apply, map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  rw [Equiv.coe_mulLeft, permAct_mul]

/-- The symmetrizer of a tensor belongs to the symmetric-tensor subspace. -/
lemma symmetrizer_mem_symTensorSubmodule {n : ℕ} (T : TensorPow k V n) :
    symmetrizer k V n T ∈ symTensorSubmodule k V n :=
  fun _ _ _ => permAct_symmetrizer _ T

/-- The image of the antisymmetrizer consists of antisymmetric tensors. -/
lemma permAct_antisymmetrizer {n : ℕ} (τ : Equiv.Perm (Fin n)) (T : TensorPow k V n) :
    permAct τ (antisymmetrizer k V n T)
      = ((Equiv.Perm.sign τ : ℤ) : k) • antisymmetrizer k V n T := by
  have key : ∑ σ : Equiv.Perm (Fin n), permAct τ (((Equiv.Perm.sign σ : ℤ) : k) • permAct σ T)
      = ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign τ : ℤ) : k) • (((Equiv.Perm.sign σ : ℤ) : k) • permAct σ T) := by
    refine Fintype.sum_equiv (Equiv.mulLeft τ)
      (fun σ => permAct τ (((Equiv.Perm.sign σ : ℤ) : k) • permAct σ T))
      (fun ρ => ((Equiv.Perm.sign τ : ℤ) : k) • (((Equiv.Perm.sign ρ : ℤ) : k) • permAct ρ T))
      fun σ => ?_
    rw [Equiv.coe_mulLeft, map_smul, permAct_mul, smul_smul]
    congr 1
    simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
    rw [← mul_assoc, sign_cast_mul_self, one_mul]
  rw [antisymmetrizer_apply, map_smul, map_sum, key, ← Finset.smul_sum]
  exact smul_comm _ _ _

/-- The antisymmetrizer of a tensor belongs to the alternating-tensor subspace. -/
lemma antisymmetrizer_mem_altTensorSubmodule {n : ℕ} (T : TensorPow k V n) :
    antisymmetrizer k V n T ∈ altTensorSubmodule k V n := by
  intro i j hij
  rw [permAct_antisymmetrizer, Equiv.Perm.sign_swap hij]
  push_cast
  rw [neg_one_smul]

/-- The symmetrizer is the identity on symmetric tensors. -/
lemma symmetrizer_eq_self_of_mem {n : ℕ} (hfac : (n.factorial : k) ≠ 0) {T : TensorPow k V n}
    (hT : T ∈ symTensorSubmodule k V n) : symmetrizer k V n T = T := by
  rw [symmetrizer_apply,
    Finset.sum_congr rfl fun σ _ => permAct_eq_self_of_mem_symTensorSubmodule hT σ,
    sum_const_perm, smul_smul, inv_mul_cancel₀ hfac, one_smul]

/-- The antisymmetrizer is the identity on antisymmetric tensors. -/
lemma antisymmetrizer_eq_self_of_mem {n : ℕ} (hfac : (n.factorial : k) ≠ 0) {T : TensorPow k V n}
    (hT : T ∈ altTensorSubmodule k V n) : antisymmetrizer k V n T = T := by
  rw [antisymmetrizer_apply,
    Finset.sum_congr rfl fun σ _ => by
      rw [permAct_eq_sign_smul_of_mem_altTensorSubmodule hT σ, smul_smul, sign_cast_mul_self,
        one_smul],
    sum_const_perm, smul_smul, inv_mul_cancel₀ hfac, one_smul]

/-- The range of the symmetrizer is exactly the symmetric tensors. -/
theorem range_symmetrizer {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    LinearMap.range (symmetrizer k V n) = symTensorSubmodule k V n := by
  refine le_antisymm ?_ fun T hT => ⟨T, symmetrizer_eq_self_of_mem hfac hT⟩
  rintro _ ⟨T, rfl⟩
  exact symmetrizer_mem_symTensorSubmodule T

/-- The range of the antisymmetrizer is exactly the antisymmetric tensors. -/
theorem range_antisymmetrizer {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    LinearMap.range (antisymmetrizer k V n) = altTensorSubmodule k V n := by
  refine le_antisymm ?_ fun T hT => ⟨T, antisymmetrizer_eq_self_of_mem hfac hT⟩
  rintro _ ⟨T, rfl⟩
  exact antisymmetrizer_mem_altTensorSubmodule T

end Averaging

section Kernels

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Every difference `T - σ T` lies in the relation subspace defining `S^n V`, not only the ones
coming from transpositions. -/
lemma sub_permAct_mem_symRelSubmodule {n : ℕ} (σ : Equiv.Perm (Fin n)) (T : TensorPow k V n) :
    T - permAct σ T ∈ symRelSubmodule k V n := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul τ i j hij ihτ =>
      have hgen : permAct τ T - permAct (Equiv.swap i j) (permAct τ T) ∈ symRelSubmodule k V n :=
        Submodule.subset_span ⟨permAct τ T, i, j, hij, rfl⟩
      have hsum := Submodule.add_mem _ ihτ hgen
      rwa [sub_add_sub_cancel, ← permAct_mul] at hsum

/-- `T + s T` is fixed by the transposition `s`, hence lies in the relation subspace defining
`⋀^n V`. -/
lemma add_permAct_swap_mem_extRelSubmodule {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (T : TensorPow k V n) :
    T + permAct (Equiv.swap i j) T ∈ extRelSubmodule k V n := by
  refine Submodule.subset_span ⟨i, j, hij, ?_⟩
  rw [map_add, ← permAct_mul, Equiv.swap_mul_self, permAct_one, add_comm]

/-- Every combination `T - sgn(σ) σ T` lies in the relation subspace defining `⋀^n V`. -/
lemma sub_sign_smul_permAct_mem_extRelSubmodule {n : ℕ} (σ : Equiv.Perm (Fin n))
    (T : TensorPow k V n) :
    T - ((Equiv.Perm.sign σ : ℤ) : k) • permAct σ T ∈ extRelSubmodule k V n := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul τ i j hij ihτ =>
      set U : TensorPow k V n := ((Equiv.Perm.sign τ : ℤ) : k) • permAct τ T with hU
      have hgen : U + permAct (Equiv.swap i j) U ∈ extRelSubmodule k V n :=
        add_permAct_swap_mem_extRelSubmodule hij U
      have hsum := Submodule.add_mem _ ihτ hgen
      have hrw : T - U + (U + permAct (Equiv.swap i j) U)
          = T - ((Equiv.Perm.sign (Equiv.swap i j * τ) : ℤ) : k)
              • permAct (Equiv.swap i j * τ) T := by
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, Units.val_mul, permAct_mul, hU,
          map_smul]
        push_cast
        rw [neg_one_mul, neg_smul, sub_neg_eq_add]
        abel
      rwa [hrw] at hsum

/-- `T - (symmetrizer T)` always lies in the relation subspace defining `S^n V`: the symmetrizer
induces the identity on the quotient `S^n V`. -/
lemma sub_symmetrizer_mem_symRelSubmodule {n : ℕ} (hfac : (n.factorial : k) ≠ 0)
    (T : TensorPow k V n) :
    T - symmetrizer k V n T ∈ symRelSubmodule k V n := by
  have key : T - symmetrizer k V n T
      = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), (T - permAct σ T) := by
    rw [Finset.sum_sub_distrib, sum_const_perm, smul_sub, smul_smul, inv_mul_cancel₀ hfac,
      one_smul, symmetrizer_apply]
  rw [key]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun σ _ => sub_permAct_mem_symRelSubmodule σ T)

/-- `T - (antisymmetrizer T)` always lies in the relation subspace defining `⋀^n V`. -/
lemma sub_antisymmetrizer_mem_extRelSubmodule {n : ℕ} (hfac : (n.factorial : k) ≠ 0)
    (T : TensorPow k V n) :
    T - antisymmetrizer k V n T ∈ extRelSubmodule k V n := by
  have key : T - antisymmetrizer k V n T
      = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n),
          (T - ((Equiv.Perm.sign σ : ℤ) : k) • permAct σ T) := by
    rw [Finset.sum_sub_distrib, sum_const_perm, smul_sub, smul_smul, inv_mul_cancel₀ hfac,
      one_smul, antisymmetrizer_apply]
  rw [key]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun σ _ => sub_sign_smul_permAct_mem_extRelSubmodule σ T)

/-- The antisymmetrizer kills every tensor fixed by a transposition: pairing `σ` with `σ s`
cancels the sum against itself. -/
lemma antisymmetrizer_eq_zero_of_permAct_eq {n : ℕ} (hfac : (n.factorial : k) ≠ 0) {i j : Fin n}
    (hij : i ≠ j) {T : TensorPow k V n} (hT : permAct (Equiv.swap i j) T = T) :
    antisymmetrizer k V n T = 0 := by
  set S : TensorPow k V n :=
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : k) • permAct σ T with hS
  have hreindex : ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign (σ * Equiv.swap i j) : ℤ) : k) • permAct (σ * Equiv.swap i j) T = S :=
    Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j)) _ _ fun σ => by
      rw [Equiv.coe_mulRight]
  have hneg : ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign (σ * Equiv.swap i j) : ℤ) : k) • permAct (σ * Equiv.swap i j) T = -S := by
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, Units.val_mul, permAct_mul, hT]
    push_cast
    rw [mul_neg_one, neg_smul]
  have h2 : (2 : k) ≠ 0 := two_ne_zero_of_factorial_cast_ne_zero k hfac (two_le_of_ne hij)
  have hSS : (2 : k) • S = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hreindex, hneg]
    exact neg_add_cancel S
  rcases smul_eq_zero.mp hSS with h | h
  · exact absurd h h2
  · rw [antisymmetrizer_apply, ← hS, h, smul_zero]

/-- **The kernel of the symmetrizer is exactly the relation subspace defining `S^n V`.** -/
theorem ker_symmetrizer {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    LinearMap.ker (symmetrizer k V n) = symRelSubmodule k V n := by
  refine le_antisymm (fun T hT => ?_) ?_
  · have h0 : symmetrizer k V n T = 0 := hT
    have key := sub_symmetrizer_mem_symRelSubmodule hfac T
    rwa [h0, sub_zero] at key
  · rw [symRelSubmodule, Submodule.span_le]
    rintro _ ⟨T, i, j, hij, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, symmetrizer_permAct, sub_self]

/-- **The kernel of the antisymmetrizer is exactly the relation subspace defining `⋀^n V`.** -/
theorem ker_antisymmetrizer {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    LinearMap.ker (antisymmetrizer k V n) = extRelSubmodule k V n := by
  refine le_antisymm (fun T hT => ?_) ?_
  · have h0 : antisymmetrizer k V n T = 0 := hT
    have key := sub_antisymmetrizer_mem_extRelSubmodule hfac T
    rwa [h0, sub_zero] at key
  · rw [extRelSubmodule, Submodule.span_le]
    rintro T ⟨i, j, hij, hT⟩
    exact antisymmetrizer_eq_zero_of_permAct_eq hfac hij hT

end Kernels

section Identification

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- **Problem 2.11.3(e), symmetric case.** When `n !` is invertible in `k` — in particular in
characteristic zero — the book's quotient `S^n V` is naturally isomorphic to the subspace of
symmetric tensors in `V^{⊗ n}`, by averaging over the permutations of the tensor factors. -/
noncomputable def symPowEquivSymTensor {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    SymPow k V n ≃ₗ[k] symTensorSubmodule k V n :=
  LinearEquiv.ofLinear
    (Submodule.liftQ _
      ((symmetrizer k V n).codRestrict _ symmetrizer_mem_symTensorSubmodule)
      (by rw [LinearMap.ker_codRestrict, ker_symmetrizer hfac]))
    ((symRelSubmodule k V n).mkQ ∘ₗ (symTensorSubmodule k V n).subtype)
    (by
      refine LinearMap.ext fun T => Subtype.ext ?_
      exact symmetrizer_eq_self_of_mem hfac T.2)
    (by
      refine LinearMap.ext fun x => ?_
      obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
      refine (Submodule.Quotient.eq _).2 ?_
      have h := sub_symmetrizer_mem_symRelSubmodule hfac T
      rw [← neg_sub] at h
      simpa using neg_mem h)

/-- **Problem 2.11.3(e), exterior case.** When `n !` is invertible in `k`, the book's quotient
`⋀^n V` is naturally isomorphic to the subspace of antisymmetric tensors in `V^{⊗ n}`, by signed
averaging over the permutations of the tensor factors. -/
noncomputable def extPowEquivAltTensor {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    ExtPow k V n ≃ₗ[k] altTensorSubmodule k V n :=
  LinearEquiv.ofLinear
    (Submodule.liftQ _
      ((antisymmetrizer k V n).codRestrict _ antisymmetrizer_mem_altTensorSubmodule)
      (by rw [LinearMap.ker_codRestrict, ker_antisymmetrizer hfac]))
    ((extRelSubmodule k V n).mkQ ∘ₗ (altTensorSubmodule k V n).subtype)
    (by
      refine LinearMap.ext fun T => Subtype.ext ?_
      exact antisymmetrizer_eq_self_of_mem hfac T.2)
    (by
      refine LinearMap.ext fun x => ?_
      obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
      refine (Submodule.Quotient.eq _).2 ?_
      have h := sub_antisymmetrizer_mem_extRelSubmodule hfac T
      rw [← neg_sub] at h
      simpa using neg_mem h)

/-- **The identification of part (e) is the symmetrizer**: composing `S^n V ≃ symmetric tensors`
with the quotient map `V^{⊗ n} → S^n V` recovers `T ↦ (n !)⁻¹ ∑_σ σ T`. -/
theorem symPowEquivSymTensor_mkQ {n : ℕ} (hfac : (n.factorial : k) ≠ 0) (T : TensorPow k V n) :
    (symPowEquivSymTensor (V := V) hfac ((symRelSubmodule k V n).mkQ T) : TensorPow k V n)
      = symmetrizer k V n T := rfl

/-- **The identification of part (e) is the antisymmetrizer**: composing
`⋀^n V ≃ antisymmetric tensors` with the quotient map `V^{⊗ n} → ⋀^n V` recovers
`T ↦ (n !)⁻¹ ∑_σ sgn(σ) σ T`. -/
theorem extPowEquivAltTensor_mkQ {n : ℕ} (hfac : (n.factorial : k) ≠ 0) (T : TensorPow k V n) :
    (extPowEquivAltTensor (V := V) hfac ((extRelSubmodule k V n).mkQ T) : TensorPow k V n)
      = antisymmetrizer k V n T := rfl

/-- The inverse of the symmetric identification is the quotient map restricted to the symmetric
tensors. -/
@[simp]
theorem symPowEquivSymTensor_symm_apply {n : ℕ} (hfac : (n.factorial : k) ≠ 0)
    (T : symTensorSubmodule k V n) :
    (symPowEquivSymTensor (V := V) hfac).symm T
      = (symRelSubmodule k V n).mkQ (T : TensorPow k V n) := rfl

/-- The inverse of the exterior identification is the quotient map restricted to the antisymmetric
tensors. -/
@[simp]
theorem extPowEquivAltTensor_symm_apply {n : ℕ} (hfac : (n.factorial : k) ≠ 0)
    (T : altTensorSubmodule k V n) :
    (extPowEquivAltTensor (V := V) hfac).symm T
      = (extRelSubmodule k V n).mkQ (T : TensorPow k V n) := rfl

/-- Characteristic-zero form of the symmetric identification of part (e). -/
noncomputable def symPowEquivSymTensorOfCharZero [CharZero k] (n : ℕ) :
    SymPow k V n ≃ₗ[k] symTensorSubmodule k V n :=
  symPowEquivSymTensor (factorial_cast_ne_zero k n)

/-- Characteristic-zero form of the exterior identification of part (e). -/
noncomputable def extPowEquivAltTensorOfCharZero [CharZero k] (n : ℕ) :
    ExtPow k V n ≃ₗ[k] altTensorSubmodule k V n :=
  extPowEquivAltTensor (factorial_cast_ne_zero k n)

end Identification

end Etingof.Problem2_11_3

-- The leaf names follow Mathlib conventions; the underscore comes solely from the stable
-- book-number namespace Problem2_11_3, which is part of this project's public API.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_11_3.symTensorSubmodule Etingof.Problem2_11_3.altTensorSubmodule
  Etingof.Problem2_11_3.symmetrizer Etingof.Problem2_11_3.antisymmetrizer
  Etingof.Problem2_11_3.symPowEquivSymTensor Etingof.Problem2_11_3.extPowEquivAltTensor
  Etingof.Problem2_11_3.symPowEquivSymTensorOfCharZero
  Etingof.Problem2_11_3.extPowEquivAltTensorOfCharZero
