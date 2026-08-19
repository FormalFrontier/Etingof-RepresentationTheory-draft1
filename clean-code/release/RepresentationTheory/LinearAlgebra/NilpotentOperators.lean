/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Module.PID
import RepresentationTheory.LieAlgebra.Sl2Representations
import RepresentationTheory.Alignment.Attribute

/-! # Nilpotent operators -/

open RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices
open RepresentationTheory.LieAlgebra.Sl2Representations

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RepresentationTheory.LinearAlgebra.NilpotentOperators

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement (n : ℕ) : Module.End ℂ (Fin n → ℂ) where
  toFun v k := if h : (k : ℕ) + 1 < n then v ⟨(k : ℕ) + 1, h⟩ else 0
  map_add' u w := by ext k; simp only [Pi.add_apply]; split <;> simp
  map_smul' c v := by
    ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> simp

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact (n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    distinguishedElement n v k = if h : (k : ℕ) + 1 < n then v ⟨(k : ℕ) + 1, h⟩ else 0 := rfl

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux1 (n : ℕ) (k : Fin n) :
    distinguishedElement n (coordinateVector n k)
      = if h : 0 < (k : ℕ) then coordinateVector n ⟨(k : ℕ) - 1, by omega⟩ else 0 := by
  ext j
  rw [auxiliary_fact]
  by_cases hk : 0 < (k : ℕ)
  · simp only [hk, dite_true]
    by_cases hj : (j : ℕ) + 1 < n
    · simp only [hj, dite_true, coordinateVector_apply, Fin.ext_iff]
      by_cases hjk : (j : ℕ) + 1 = (k : ℕ)
      · rw [if_pos hjk, if_pos (by omega)]
      · rw [if_neg hjk, if_neg (by omega)]
    · simp only [hj, dite_false, coordinateVector_apply, Fin.ext_iff]
      rw [if_neg (by omega)]
  · simp only [hk, dite_false, Pi.zero_apply]
    by_cases hj : (j : ℕ) + 1 < n
    · simp only [hj, dite_true, coordinateVector_apply, Fin.ext_iff]
      rw [if_neg (by omega)]
    · simp only [hj, dite_false]

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux2 (n m : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    (distinguishedElement n ^ m) v k
      = if h : (k : ℕ) + m < n then v ⟨(k : ℕ) + m, h⟩ else 0 := by
  induction m generalizing k with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Nat.add_zero]
    rw [dif_pos k.isLt]
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, auxiliary_fact]
    by_cases hk1 : (k : ℕ) + 1 < n
    · rw [dif_pos hk1, ih ⟨(k : ℕ) + 1, hk1⟩]
      by_cases hkm : (k : ℕ) + 1 + m < n
      · rw [dif_pos hkm, dif_pos (by omega)]
        exact congrArg v (Fin.ext (show (k : ℕ) + 1 + m = (k : ℕ) + (m + 1) by omega))
      · rw [dif_neg hkm, dif_neg (by omega)]
    · rw [dif_neg hk1, dif_neg (by omega)]

/-- The two displayed expressions are equal. -/
theorem displayed_eq (n : ℕ) : distinguishedElement n ^ n = 0 := by
  apply LinearMap.ext
  intro v
  funext k
  rw [auxiliary_fact_aux2, dif_neg (by omega), LinearMap.zero_apply, Pi.zero_apply]

/-- The specified endomorphism is nilpotent. -/
theorem isNilpotent (n : ℕ) : IsNilpotent (distinguishedElement n) :=
  ⟨n, displayed_eq n⟩

/-- The specified element belongs to the kernel of the displayed map. -/
theorem mem_ker_aux1 (n k : ℕ) (v : Fin n → ℂ) :
    v ∈ LinearMap.ker (distinguishedElement n ^ k) ↔ ∀ j : Fin n, k ≤ (j : ℕ) → v j = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j hj
    have hidx : ((j : ℕ) - k) + k < n := by have := j.isLt; omega
    have hc := congrFun h ⟨(j : ℕ) - k, by omega⟩
    rw [auxiliary_fact_aux2, dif_pos hidx, Pi.zero_apply] at hc
    rwa [show (⟨(j : ℕ) - k + k, hidx⟩ : Fin n) = j from
      Fin.ext (show (j : ℕ) - k + k = (j : ℕ) by omega)] at hc
  · intro h
    funext i
    rw [auxiliary_fact_aux2, Pi.zero_apply]
    by_cases hlt : (i : ℕ) + k < n
    · rw [dif_pos hlt]; exact h ⟨(i : ℕ) + k, hlt⟩ (Nat.le_add_left k (i : ℕ))
    · rw [dif_neg hlt]

/-- The kernel of the `k`-th power of the displayed endomorphism has finite rank `min k n`. -/
theorem finrank_ker_pow (n k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (distinguishedElement n ^ k)) = min k n := by
  set ι := {i : Fin n // (i : ℕ) < k} with hι
  have hli : LinearIndependent ℂ (fun i : ι => Pi.basisFun ℂ (Fin n) i.1) :=
    (Pi.basisFun ℂ (Fin n)).linearIndependent.comp Subtype.val Subtype.val_injective
  have hspan : LinearMap.ker (distinguishedElement n ^ k)
      = Submodule.span ℂ (Set.range (fun i : ι => Pi.basisFun ℂ (Fin n) i.1)) := by
    refine le_antisymm ?_ ?_
    · intro w hw
      have hz := (mem_ker_aux1 n k w).mp hw
      have hrepr : w = ∑ j : Fin n, w j • Pi.basisFun ℂ (Fin n) j := by
        conv_lhs => rw [← (Pi.basisFun ℂ (Fin n)).sum_repr w]
        simp only [Pi.basisFun_repr]
      rw [hrepr]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hjk : (j : ℕ) < k
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hjk⟩, rfl⟩)
      · rw [hz j (by omega), zero_smul]; exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, mem_ker_aux1]
      intro j hj
      simp only [Pi.basisFun_apply, Pi.single_apply]
      rw [if_neg]
      rintro rfl
      exact absurd i.2 (by omega)
  rw [hspan, finrank_span_eq_card hli]
  rw [← Fintype.card_fin (min k n)]
  refine Fintype.card_congr
    { toFun := fun i => ⟨(i.1 : ℕ), lt_min i.2 i.1.isLt⟩
      invFun := fun j => ⟨⟨(j : ℕ), lt_of_lt_of_le j.isLt (min_le_right k n)⟩,
        lt_of_lt_of_le j.isLt (min_le_left k n)⟩
      left_inv := fun i => Subtype.ext (Fin.ext rfl)
      right_inv := fun j => Fin.ext rfl }

/-- A linear equivalence between the displayed modules. -/
noncomputable def linearEquiv_aux1 (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) where
  toFun v k := ((k : ℕ).factorial : ℂ) * v k
  map_add' u w := by ext k; simp [mul_add]
  map_smul' c v := by ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  invFun v k := (((k : ℕ).factorial : ℂ))⁻¹ * v k
  left_inv v := by
    ext k
    have hfac : ((k : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  right_inv v := by
    ext k
    have hfac : ((k : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux5 (n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    linearEquiv_aux1 n v k = ((k : ℕ).factorial : ℂ) * v k := rfl

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux7 (n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    (linearEquiv_aux1 n).symm v k = (((k : ℕ).factorial : ℂ))⁻¹ * v k := rfl

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux6 (n : ℕ) (k : Fin n) :
    linearEquiv_aux1 n (coordinateVector n k) =
      ((k : ℕ).factorial : ℂ) • coordinateVector n k := by
  ext j
  rw [map_apply_aux5, Pi.smul_apply, smul_eq_mul, coordinateVector_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk]

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux8 (n : ℕ) (k : Fin n) :
    (linearEquiv_aux1 n).symm (coordinateVector n k) =
      (((k : ℕ).factorial : ℂ))⁻¹ • coordinateVector n k := by
  ext j
  rw [map_apply_aux7, Pi.smul_apply, smul_eq_mul, coordinateVector_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk]

/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom_aux1 (n : ℕ) :
    complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ (Fin n → ℂ) :=
  ((linearEquiv_aux1 n).conjAlgEquiv ℂ : _ →ₐ[ℂ] _).toLieHom.comp
    (finFunctionRepresentation n)

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux11 (n : ℕ) (x : complexTwoByTwoMatrixLieSubalgebra) :
    lieHom_aux1 n x =
      (linearEquiv_aux1 n).conjAlgEquiv ℂ (finFunctionRepresentation n x) := rfl

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux12 (n : ℕ) :
    lieHom_aux1 n raisingElement = distinguishedElement n := by
  refine (Pi.basisFun ℂ (Fin n)).ext fun k => ?_
  rw [Pi.basisFun_apply]
  change lieHom_aux1 n raisingElement (coordinateVector n k) =
    distinguishedElement n (coordinateVector n k)
  have he : finFunctionRepresentation n raisingElement (coordinateVector n k)
      = ((k : ℕ) : ℂ) • coordinateVector n ⟨(k : ℕ) - 1, by omega⟩ := by
    have h := bracket_raising_coordinateVector n (k : ℕ) k.isLt
    rw [Fin.eta] at h
    rw [← bracket_eq_representation_apply]
    exact h
  rw [map_apply_aux11, LinearEquiv.conjAlgEquiv_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [map_apply_aux8, map_smul, he]
  simp only [map_smul, map_apply_aux6]
  rw [auxiliary_fact_aux1]
  by_cases hk : 0 < (k : ℕ)
  · rw [dif_pos hk, smul_smul, smul_smul]
    have hscalar : (((k : ℕ).factorial : ℂ))⁻¹ * ((k : ℕ) : ℂ)
        * (((k : ℕ) - 1).factorial : ℂ) = 1 := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (k : ℕ) ≠ 0)
      rw [hm, Nat.factorial_succ]
      have hm1 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
      have hmf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      push_cast
      field_simp
    rw [hscalar, one_smul]
  · rw [dif_neg hk]
    have hk0 : (k : ℕ) = 0 := by omega
    simp [hk0]

/-- There exists a value satisfying the displayed conditions. -/
theorem exists_witness (n : ℕ) :
    ∃ ρ : complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ (Fin n → ℂ),
      ρ raisingElement = distinguishedElement n :=
  ⟨lieHom_aux1 n, map_apply_aux12 n⟩

/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom {ι : Type*} {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ (W i)) :
    complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ (∀ i, W i) where
  toFun x := LinearMap.piMap fun i => ρ i x
  map_add' x y := by
    apply LinearMap.ext; intro v; funext j
    simp only [LinearMap.coe_piMap, Pi.map_apply, map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' r x := by
    apply LinearMap.ext; intro v; funext j
    simp only [LinearMap.coe_piMap, Pi.map_apply, map_smul, RingHom.id_apply,
      LinearMap.smul_apply, Pi.smul_apply]
  map_lie' {x y} := by
    apply LinearMap.ext; intro v; funext j
    simp only [LinearMap.coe_piMap, Pi.map_apply, LieHom.map_lie,
      LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Pi.sub_apply,
      Module.End.mul_apply]

/-- The displayed map sends the specified input to the stated value. -/
@[simp]
theorem map_apply_aux9 {ι : Type*} {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ (W i))
    (x : complexTwoByTwoMatrixLieSubalgebra) (v : ∀ i, W i) (j : ι) :
    lieHom ρ x v j = ρ j x (v j) := rfl

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux10 {ι : Type*} {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ (W i)) :
    lieHom ρ raisingElement = LinearMap.piMap fun i => ρ i raisingElement := rfl

/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom_aux2 {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (ρ : complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ W) :
    complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V :=
  (e.symm.lieConj.toLieHom).comp ρ

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux13 {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (ρ : complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ W)
    (x : complexTwoByTwoMatrixLieSubalgebra) :
    lieHom_aux2 e ρ x = e.symm.lieConj (ρ x) := rfl

/-- There exists a value satisfying the displayed conditions. -/
theorem exists_witness_aux1 {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (n : ι → ℕ) (A : Module.End ℂ V)
    (e : V ≃ₗ[ℂ] ∀ i, Fin (n i) → ℂ)
    (hA : ∀ v, e (A v) = LinearMap.piMap (fun i => distinguishedElement (n i)) (e v)) :
    ∃ ρ : complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V,
      ρ raisingElement = A := by
  refine ⟨lieHom_aux2 e (lieHom fun i => lieHom_aux1 (n i)), ?_⟩
  have hE : (lieHom fun i => lieHom_aux1 (n i)) raisingElement
      = LinearMap.piMap fun i => distinguishedElement (n i) := by
    rw [map_apply_aux10]
    congr 1; funext i; exact map_apply_aux12 (n i)
  apply LinearMap.ext; intro v
  rw [map_apply_aux13, hE, LinearEquiv.lieConj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_symm, ← hA v, LinearEquiv.symm_apply_apply]

open Polynomial
open scoped DirectSum

/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux1 (e : ℕ) : Polynomial ℂ →ₗ[ℂ] (Fin e → ℂ) :=
  LinearMap.pi fun k : Fin e => Polynomial.lcoeff ℂ (e - 1 - (k : ℕ))

/-- The indicated polynomial coefficient has the displayed value. -/
@[simp] theorem coeff_eq (e : ℕ) (p : Polynomial ℂ) (k : Fin e) :
    linearMap_aux1 e p k = p.coeff (e - 1 - (k : ℕ)) := rfl

/-- The scalar restriction of the span of `X ^ e` is contained in the kernel of the coefficient map. -/
theorem span_X_pow_le_ker (e : ℕ) :
    ((Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}).restrictScalars ℂ)
      ≤ LinearMap.ker (linearMap_aux1 e) := by
  intro x hx
  rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [LinearMap.mem_ker]
  ext k
  simp only [coeff_eq, Pi.zero_apply]
  have hdvd : (X : Polynomial ℂ) ^ e ∣ c • (X : Polynomial ℂ) ^ e :=
    ⟨c, by rw [smul_eq_mul]; ring⟩
  exact (Polynomial.X_pow_dvd_iff.mp hdvd) _ (by omega)

/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux2 (e : ℕ) :
    (Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) →ₗ[ℂ]
      (Fin e → ℂ) :=
  Submodule.liftQ ((Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}).restrictScalars ℂ)
    (linearMap_aux1 e) (span_X_pow_le_ker e)

/-- The descended map applied to a polynomial quotient class agrees with the coefficient map on the polynomial. -/
theorem quotientDesc_mk (e : ℕ) (p : Polynomial ℂ) :
    linearMap_aux2 e (Submodule.Quotient.mk p) = linearMap_aux1 e p := rfl

/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux3 (e : ℕ) : (Fin e → ℂ) →ₗ[ℂ] Polynomial ℂ :=
  ∑ j : Fin e, (Polynomial.monomial (e - 1 - (j : ℕ))).comp (LinearMap.proj j)

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux2 (e : ℕ) (v : Fin e → ℂ) :
    linearMap_aux3 e v =
      ∑ j : Fin e, Polynomial.monomial (e - 1 - (j : ℕ)) (v j) := by
  simp only [linearMap_aux3, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

/-- The indicated polynomial coefficient has the displayed value. -/
theorem coeff_eq_aux1 (e : ℕ) (v : Fin e → ℂ) (d : ℕ) :
    (linearMap_aux3 e v).coeff d =
      ∑ j : Fin e, (if e - 1 - (j : ℕ) = d then v j else 0) := by
  rw [map_apply_aux2, Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun j _ => Polynomial.coeff_monomial

/-- A linear map between the displayed modules. -/
noncomputable def linearMap (e : ℕ) :
    (Fin e → ℂ) →ₗ[ℂ]
      (Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) :=
  ((Submodule.mkQ _).restrictScalars ℂ).comp (linearMap_aux3 e)

/-- The linear map to the polynomial quotient sends a coordinate vector to the quotient class of its reconstructed polynomial. -/
@[simp] theorem quotientLinearMap_apply (e : ℕ) (v : Fin e → ℂ) :
    linearMap e v = Submodule.Quotient.mk (linearMap_aux3 e v) := rfl

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux1 (e : ℕ) (v : Fin e → ℂ) :
    linearMap_aux2 e (linearMap e v) = v := by
  ext k
  rw [quotientLinearMap_apply, quotientDesc_mk, coeff_eq, coeff_eq_aux1]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
  · intro j _ hjk
    refine if_neg fun h => hjk ?_
    have hj := j.isLt; have hk := k.isLt
    exact Fin.ext (by omega)
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply (e : ℕ)
    (q : Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) :
    linearMap e (linearMap_aux2 e q) = q := by
  induction q using Submodule.Quotient.induction_on with
  | H p =>
    rw [quotientDesc_mk, quotientLinearMap_apply, Submodule.Quotient.eq,
      Submodule.mem_span_singleton]
    have hdvd : (X : Polynomial ℂ) ^ e ∣ (linearMap_aux3 e (linearMap_aux1 e p) - p) := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      rw [Polynomial.coeff_sub, coeff_eq_aux1]
      simp only [coeff_eq]
      rw [Finset.sum_eq_single (⟨e - 1 - d, by omega⟩ : Fin e)]
      · simp only []
        rw [if_pos (by omega)]
        have : e - 1 - (e - 1 - d) = d := by omega
        rw [this]; ring
      · intro j _ hj
        refine if_neg fun h => hj (Fin.ext ?_)
        simp only []; omega
      · intro h; exact absurd (Finset.mem_univ _) h
    obtain ⟨c, hc⟩ := hdvd
    exact ⟨c, by rw [smul_eq_mul, mul_comm]; exact hc.symm⟩

/-- A linear equivalence between the displayed modules. -/
noncomputable def linearEquiv (e : ℕ) :
    (Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) ≃ₗ[ℂ]
      (Fin e → ℂ) :=
  { linearMap_aux2 e with
    invFun := linearMap e
    left_inv := map_apply e
    right_inv := map_apply_aux1 e }

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux4 (e : ℕ)
    (q : Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) :
    linearEquiv e q = linearMap_aux2 e q := rfl

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux3 (e : ℕ)
    (q : Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e}) :
    linearEquiv e ((X : Polynomial ℂ) • q) =
      distinguishedElement e (linearEquiv e q) := by
  induction q using Submodule.Quotient.induction_on with
  | H p =>
    simp only [map_apply_aux4]
    rw [show (X : Polynomial ℂ) • (Submodule.Quotient.mk p :
          Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ) {(X : Polynomial ℂ) ^ e})
          = Submodule.Quotient.mk (X * p) from by
        rw [← Submodule.Quotient.mk_smul]; congr 1]
    rw [quotientDesc_mk, quotientDesc_mk]
    ext k
    rw [coeff_eq, auxiliary_fact]
    by_cases hk : (k : ℕ) + 1 < e
    · rw [dif_pos hk, coeff_eq]
      have : e - 1 - (k : ℕ) = (e - 1 - ((k : ℕ) + 1)) + 1 := by omega
      rw [this, coeff_X_mul]
    · rw [dif_neg hk]
      have h0 : e - 1 - (k : ℕ) = 0 := by omega
      rw [h0]; exact coeff_X_mul_zero p

/-- A nilpotent endomorphism makes the module torsion for the powers of `X` under polynomial evaluation. -/
theorem isTorsion_powers_of_isNilpotent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (hA : IsNilpotent A) :
    Module.IsTorsion' (Module.AEval' A) (Submonoid.powers (X : Polynomial ℂ)) := by
  obtain ⟨N, hN⟩ := hA
  intro x
  refine ⟨⟨(X : Polynomial ℂ) ^ N, N, rfl⟩, ?_⟩
  obtain ⟨m, rfl⟩ := (Module.AEval'.of A).surjective x
  change (X : Polynomial ℂ) ^ N • Module.AEval'.of A m = 0
  rw [Module.AEval'.X_pow_smul_of]
  have : A ^ N • m = (0 : V) := by rw [hN]; simp
  rw [this, map_zero]

/-- There exists a value satisfying the displayed conditions. -/
theorem exists_witness_aux2 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Module.End ℂ V) (hA : IsNilpotent A) :
    ∃ ρ : complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V,
      ρ raisingElement = A := by
  obtain ⟨d, k, ⟨Ψ⟩⟩ := Module.torsion_by_prime_power_decomposition (R := Polynomial ℂ)
    (M := Module.AEval' A) Polynomial.irreducible_X
      (isTorsion_powers_of_isNilpotent A hA)
  set funOn := DirectSum.linearEquivFunOnFintype (Polynomial ℂ) (Fin d)
    (fun i => Polynomial ℂ ⧸ Submodule.span (Polynomial ℂ)
      {(X : Polynomial ℂ) ^ (k i)}) with hfunOn
  set e : V ≃ₗ[ℂ] (∀ i : Fin d, Fin (k i) → ℂ) :=
    (Module.AEval'.of A) ≪≫ₗ (Ψ.restrictScalars ℂ) ≪≫ₗ (funOn.restrictScalars ℂ) ≪≫ₗ
      (LinearEquiv.piCongrRight fun i => linearEquiv (k i)) with he
  refine exists_witness_aux1 k A e ?_
  intro v
  funext i
  simp only [he, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.piCongrRight_apply, LinearMap.coe_piMap, Pi.map_apply]
  rw [show Module.AEval'.of A (A v) = (X : Polynomial ℂ) • Module.AEval'.of A v from
      (Module.AEval'.X_smul_of A v).symm, map_smul, map_smul, Pi.smul_apply,
      map_apply_aux3]

end RepresentationTheory.LinearAlgebra.NilpotentOperators
