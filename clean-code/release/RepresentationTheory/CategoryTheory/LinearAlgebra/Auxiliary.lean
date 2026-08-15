/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.Abelian.FiniteLength
import RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Matrix.Basis

universe w u v

/-!
# Auxiliary linear algebra in finite linear categories

This module gives linear equivalences and dimension formulas for finite biproducts, together with
elementary bounds and a commutativity criterion for products of square matrix algebras.
-/

open CategoryTheory CategoryTheory.Limits Module

namespace RepresentationTheory.CategoryTheory.LinearAlgebra.Auxiliary

section BiproductHom

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [HasFiniteBiproducts C]
variable {J : Type*} [Finite J] {K : Type*} [Finite K] (f : J → C) (g : K → C)

/-- The linear equivalence between morphisms of finite biproducts and families of component morphisms. -/
noncomputable def biproductHomLinearEquiv :
    (⨁ f ⟶ ⨁ g) ≃ₗ[k] ∀ (j : J) (l : K), (f j ⟶ g l) where
  toFun m := fun j l => biproduct.ι f j ≫ m ≫ biproduct.π g l
  map_add' m m' := by
    funext j l; simp [Preadditive.comp_add, Preadditive.add_comp]
  map_smul' r m := by
    funext j l; simp [Linear.comp_smul, Linear.smul_comp]
  invFun M := biproduct.desc fun j => biproduct.lift fun l => M j l
  left_inv m := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro l
    simp
  right_inv M := by
    funext j l
    simp

/-- The dimension of morphisms between finite biproducts is the double sum of the component dimensions. -/
theorem finrank_biproductHom [Fintype J] [Fintype K]
    (hfin : ∀ (j : J) (l : K), FiniteDimensional k (f j ⟶ g l)) :
    finrank k (⨁ f ⟶ ⨁ g) = ∑ j, ∑ l, finrank k (f j ⟶ g l) := by
  haveI : ∀ (j : J) (l : K), Module.Finite k (f j ⟶ g l) := hfin
  rw [(biproductHomLinearEquiv f g (k := k)).finrank_eq, Module.finrank_pi_fintype k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Module.finrank_pi_fintype k]

end BiproductHom

section Cartan

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C]
  [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
  [Linear k C]
  [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
  [HasFiniteBiproducts C]
variable {ι : Type v} [Fintype ι]

/-- A natural-number-valued quantity assigned to an ordered pair of indices in a family of objects. -/
noncomputable def familyPairNat (k : Type w) [Field k] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear k C] (P : ι → C) (i j : ι) : ℕ :=
  finrank k (P i ⟶ P j)

private theorem sum_sigma_fin (n : ι → ℕ) (G : ι → ℕ) :
    (∑ p : Σ i, Fin (n i), G p.1) = ∑ i, n i * G i := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

private theorem sum_sigma_cartan (c : ι → ι → ℕ) (n : ι → ℕ) :
    (∑ p : Σ i, Fin (n i), ∑ q : Σ j, Fin (n j), c p.1 q.1)
      = ∑ i, ∑ j, c i j * n i * n j := by
  calc (∑ p : Σ i, Fin (n i), ∑ q : Σ j, Fin (n j), c p.1 q.1)
      = ∑ i, n i * ∑ q : Σ j, Fin (n j), c i q.1 :=
        sum_sigma_fin n (fun x => ∑ q : Σ j, Fin (n j), c x q.1)
    _ = ∑ i, n i * ∑ j, n j * c i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_sigma_fin n (fun j => c i j)]
    _ = ∑ i, ∑ j, c i j * n i * n j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- Computes the dimension of the endomorphism object as a sum over pairs of indexed summands. -/
theorem auxiliaryFinrankEndEqSumHomFinrank (P : ι → C) (n : ι → ℕ) :
    finrank k
        (End
          (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
            P n)) =
      ∑ p : Σ i, Fin (n i), ∑ q : Σ j, Fin (n j), finrank k (P p.1 ⟶ P q.1) :=
  finrank_biproductHom (fun p : Σ i, Fin (n i) => P p.1)
    (fun q : Σ j, Fin (n j) => P q.1)
    fun p q =>
      RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory.finiteDimensional_hom
        (P p.1) (P q.1)

/-- Expresses the dimension of the indicated opposite endomorphism space as a multiplicity-weighted sum of the natural-number-valued pair function. -/
theorem auxiliaryFinrankOpEndEqWeightedFamilyPairSum (P : ι → C) (n : ι → ℕ) :
    finrank k
        ((End
          (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
            P n))ᵐᵒᵖ) =
      ∑ i, ∑ j, familyPairNat k P i j * n i * n j := by
  rw [← (MulOpposite.opLinearEquiv k
      (M := End
        (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
          P n))).finrank_eq,
    auxiliaryFinrankEndEqSumHomFinrank P n]
  exact sum_sigma_cartan (familyPairNat k P) n

end Cartan

section Minimal

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C]
  [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
  [Linear k C]
  [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
  [HasFiniteBiproducts C]
variable {ι : Type v} [Fintype ι]

private theorem cartan_term_le (c n₁ n₂ : ℕ) (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂) :
    c ≤ c * n₁ * n₂ := by
  calc c = c * 1 * 1 := by ring
    _ ≤ c * n₁ * n₂ := by gcongr

private theorem cartan_term_lt (c n : ℕ) (hc : 1 ≤ c) (hn : 2 ≤ n) : c < c * n * n := by
  have h4 : 1 < n * n := by have := Nat.mul_le_mul hn hn; omega
  calc c = c * 1 := (mul_one c).symm
    _ < c * (n * n) := mul_lt_mul_of_pos_left h4 (by omega)
    _ = c * n * n := (mul_assoc c n n).symm

/-- For positive multiplicities, the unweighted pair-function sum is bounded by the indicated opposite endomorphism dimension. -/
theorem auxiliaryFamilyPairSumLeFinrankOpEnd (P : ι → C) (n : ι → ℕ)
    (hn : ∀ i, 1 ≤ n i) :
    (∑ i, ∑ j, familyPairNat k P i j) ≤
      finrank k
        ((End
          (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
            P n))ᵐᵒᵖ) := by
  rw [auxiliaryFinrankOpEndEqWeightedFamilyPairSum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  exact cartan_term_le _ _ _ (hn i) (hn j)

/-- For constant multiplicity one, the opposite endomorphism dimension is the sum of all values of the natural-number-valued pair function. -/
theorem auxiliaryFinrankOpEndOneEqFamilyPairSum (P : ι → C) :
    finrank k
        ((End
          (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
            P (fun _ => 1)))ᵐᵒᵖ) =
      ∑ i, ∑ j, familyPairNat k P i j := by
  rw [auxiliaryFinrankOpEndEqWeightedFamilyPairSum]
  simp

/-- Under the displayed lower bounds, the opposite endomorphism dimension equals the unweighted pair-function sum exactly when every multiplicity is one. -/
theorem auxiliaryFinrankOpEndEqFamilyPairSumIff (P : ι → C) (n : ι → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hdiag : ∀ i, 1 ≤ familyPairNat k P i i) :
    finrank k
        ((End
          (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
            P n))ᵐᵒᵖ) =
        ∑ i, ∑ j, familyPairNat k P i j ↔
      ∀ i, n i = 1 := by
  rw [auxiliaryFinrankOpEndEqWeightedFamilyPairSum]
  constructor
  · intro h
    by_contra hne
    simp only [not_forall] at hne
    obtain ⟨i₀, hi₀⟩ := hne
    have hi₀2 : 2 ≤ n i₀ := by have := hn i₀; omega
    have hlt : (∑ i, ∑ j, familyPairNat k P i j) <
        ∑ i, ∑ j, familyPairNat k P i j * n i * n j := by
      refine Finset.sum_lt_sum (fun i _ => Finset.sum_le_sum fun j _ =>
        cartan_term_le _ _ _ (hn i) (hn j)) ⟨i₀, Finset.mem_univ _, ?_⟩
      refine Finset.sum_lt_sum (fun j _ => cartan_term_le _ _ _ (hn i₀) (hn j))
        ⟨i₀, Finset.mem_univ _, ?_⟩
      exact cartan_term_lt _ _ (hdiag i₀) hi₀2
    omega
  · intro h
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [h i, h j]
    ring

omit [HasFiniteBiproducts C] [Fintype ι] in
/-- Nontrivial endomorphisms at an indexed object force the corresponding diagonal value of the pair function to be at least one. -/
theorem one_le_familyPairNat_self (P : ι → C) (i : ι) [Nontrivial (P i ⟶ P i)] :
    1 ≤ familyPairNat k P i i := by
  haveI : FiniteDimensional k (P i ⟶ P i) :=
    RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory.finiteDimensional_hom
      (P i) (P i)
  exact Module.finrank_pos

end Minimal

section Commutativity

variable {k : Type w} [Field k]

/-- For distinct indices in a finite type, there exist two elements whose products in opposite orders are unequal. -/
theorem exists_noncommuting_elements_of_ne {m : Type*} [Fintype m] {a b : m}
    (hab : a ≠ b) : ∃ x y : Matrix m m k, x * y ≠ y * x := by
  classical
  refine ⟨Matrix.single a b 1, Matrix.single b a 1, ?_⟩
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_one]
  intro h
  have h2 := congrFun (congrFun h a) a
  rw [Matrix.single_apply_same, Matrix.single_apply_of_row_ne hab.symm b a 1] at h2
  exact one_ne_zero h2

/-- Square matrices over a subsingleton finite index type commute under multiplication. -/
theorem matrix_mul_comm_of_subsingleton {m : Type*} [Fintype m] [Subsingleton m]
    (x y : Matrix m m k) : x * y = y * x := by
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : l = i := Subsingleton.elim l i
  subst this
  exact mul_comm _ _

/-- With positive dimensions, all displayed square matrix products commute exactly when every dimension is one. -/
theorem forall_matrix_mul_comm_iff {ι : Type*} (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    (∀ x y : (∀ i, Matrix (Fin (n i)) (Fin (n i)) k), x * y = y * x) ↔
      ∀ i, n i = 1 := by
  classical
  constructor
  · intro hcomm i
    by_contra hni
    have hi2 : 2 ≤ n i := by have := hn i; omega
    obtain ⟨x₀, y₀, hxy⟩ := exists_noncommuting_elements_of_ne (k := k)
      (m := Fin (n i)) (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩)
      (Fin.ne_of_val_ne (by simp))
    have key := congrFun (hcomm (Function.update 1 i x₀) (Function.update 1 i y₀)) i
    rw [Pi.mul_apply, Pi.mul_apply, Function.update_self, Function.update_self] at key
    exact hxy key
  · intro h x y
    funext i
    rw [Pi.mul_apply, Pi.mul_apply]
    haveI : Subsingleton (Fin (n i)) := by rw [h i]; infer_instance
    exact matrix_mul_comm_of_subsingleton _ _

end Commutativity

end RepresentationTheory.CategoryTheory.LinearAlgebra.Auxiliary
