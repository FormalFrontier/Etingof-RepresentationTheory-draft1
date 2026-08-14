/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.PermutationPolynomialAuxiliary
set_option linter.style.longLine false
set_option linter.style.whitespace false
open MvPolynomial Finset
namespace RepresentationTheory.Auxiliary.PermutationPolynomials
open RepresentationTheory.PermutationPolynomialAuxiliary
noncomputable section
variable {n : ℕ} (N : ℕ)
/-- An auxiliary rational multivariate polynomial indexed by a natural parameter and a permutation of a finite type. -/
def auxiliaryPermutationPolynomial (σ : Equiv.Perm (Fin n)) : MvPolynomial (Fin N) ℚ :=
  ∑ f ∈ (univ.filter fun f : Fin n → Fin N => ∀ j, f (σ j) = f j),
    ∏ j : Fin n, X (f j)
/-- A second auxiliary rational multivariate polynomial indexed by a natural parameter and a permutation of a finite type. -/
def auxiliaryPermutationPolynomial' (σ : Equiv.Perm (Fin n)) : MvPolynomial (Fin N) ℚ :=
  ((permutationNatMultiset n σ).map (psum (Fin N) ℚ)).prod
private lemma prod_X_comp_eq_prod_pow
    {L : ℕ} (π : Fin n → Fin L) (lens : Fin L → ℕ)
    (hπ_card : ∀ i, (univ.filter (fun k => π k = i)).card = lens i)
    (g : Fin L → Fin N) :
    ∏ j : Fin n, X (g (π j)) =
      (∏ i : Fin L, X (g i) ^ lens i : MvPolynomial (Fin N) ℚ) := by
  rw [← Finset.prod_fiberwise_of_maps_to
    (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin L)))
    (g := π) (fun _ _ => mem_univ _)
    (f := fun j => (X (g (π j)) : MvPolynomial (Fin N) ℚ))]
  apply Finset.prod_congr rfl
  intro i _
  have hsub : ∀ j ∈ univ.filter (fun k => π k = i),
      (X (g (π j)) : MvPolynomial (Fin N) ℚ) = X (g i) := by
    intro j hj; rw [show π j = i from (mem_filter.mp hj).2]
  rw [Finset.prod_congr rfl hsub, Finset.prod_const, hπ_card]
private lemma fixed_coloring_const_on_orbit {σ : Equiv.Perm (Fin n)}
    {f : Fin n → Fin N} (hf : ∀ j, f (σ j) = f j)
    {x y : Fin n} (h : σ.SameCycle x y) : f x = f y := by
  obtain ⟨i, rfl⟩ := h
  induction i using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show (↑k + 1 : ℤ) = 1 + ↑k from by ring, zpow_add, zpow_one,
      Equiv.Perm.mul_apply, hf, ih]
  | pred k ih =>
    rw [show (-(↑k : ℤ) - 1 : ℤ) = -1 + -(↑k : ℤ) from by ring, zpow_add, zpow_neg_one,
      Equiv.Perm.mul_apply]
    have hinv : f (σ⁻¹ ((σ ^ (-(↑k : ℤ))) x)) = f ((σ ^ (-(↑k : ℤ))) x) := by
      conv_rhs => rw [← Equiv.apply_symm_apply σ ((σ ^ (-(↑k : ℤ))) x)]
      exact (hf _).symm
    rw [hinv, ih]
/-- The two auxiliary rational multivariate polynomials associated with the same parameter and permutation agree. -/
@[source_ref "Chapter5/Discussion_computing_characters_of_L_lambda" (role := supporting)]
theorem auxiliaryPermutationPolynomial_eq_auxiliaryPermutationPolynomial' (σ : Equiv.Perm (Fin n)) :
    auxiliaryPermutationPolynomial N σ = auxiliaryPermutationPolynomial' N σ := by
  classical
  obtain ⟨π, hπ_orbit, hπ_card⟩ := exists_sameCycle_class_indexing σ
  have hπ_surj : Function.Surjective π := by
    intro i; by_contra h; push Not at h
    have h1 := hπ_card i
    have h2 : (univ.filter (fun k : Fin n => π k = i)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _; exact h k
    rw [h2] at h1
    have := permutationNatMultiset_pos σ _
      (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
    omega
  have hrep : ∀ i, π ((hπ_surj i).choose) = i :=
    fun i => (hπ_surj i).choose_spec
  unfold auxiliaryPermutationPolynomial'
  rw [← Multiset.prod_map_toList, ← List.ofFn_getElem_eq_map, List.prod_ofFn]
  simp_rw [psum]
  rw [prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  unfold auxiliaryPermutationPolynomial
  symm
  apply Finset.sum_nbij (fun g => g ∘ π)
  · intro g _; simp only [mem_filter, mem_univ, true_and, Function.comp_apply]
    intro j
    have : π (σ j) = π j :=
      (hπ_orbit _ _).mpr ((Equiv.Perm.SameCycle.refl σ j).apply_left)
    rw [this]
  · intro g₁ _ g₂ _ h
    funext i; obtain ⟨k, hk⟩ := hπ_surj i
    have := congr_fun h k
    simp only [Function.comp_apply] at this
    rwa [hk] at this
  · intro f hf
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hf
    exact ⟨fun i => f ((hπ_surj i).choose), mem_univ _, by
      funext j; simp only [Function.comp_apply]
      exact fixed_coloring_const_on_orbit N hf
        ((hπ_orbit _ _).mp (hrep (π j)))⟩
  · intro g _
    exact (prod_X_comp_eq_prod_pow N π
      (fun i => (permutationNatMultiset n σ).toList[↑i]) hπ_card g).symm
end
end RepresentationTheory.Auxiliary.PermutationPolynomials

