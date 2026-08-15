/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization

noncomputable section

namespace RepresentationTheory.AuxiliaryWeightSpaces.Duality

open RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.GeneralLinearGroup.WeightCharacter

variable {k : Type*} [Field k] {N : ℕ}

/-- Taking inverses of the unit parameter gives the inverse auxiliary coordinate element. -/
theorem auxiliaryCoordinateElement_inv
    (k : Type*) [Field k] (N : ℕ) (i : Fin N) (t : kˣ) :
    (diagonalUnit k N i t)⁻¹ = diagonalUnit k N i t⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  exact (diagonalUnit k N i t).val_inv

/-- Distinct integer exponents can be separated by powers of a unit in a characteristic-zero
field. -/
theorem exists_unit_pow_ne_of_ne
    (k : Type*) [Field k] [CharZero k] {a b : ℤ} (hab : a ≠ b) :
    ∃ t : kˣ, ((t ^ a : kˣ) : k) ≠ ((t ^ b : kˣ) : k) := by
  refine ⟨Units.mk0 (2 : k) (by norm_num), ?_⟩
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  intro h
  apply hab
  have htrans : ∀ n : ℤ, (2 : k) ^ n = algebraMap ℚ k ((2 : ℚ) ^ n) := by
    intro n
    rw [map_zpow₀, map_ofNat]
  rw [htrans a, htrans b] at h
  have hQ : (2 : ℚ) ^ a = (2 : ℚ) ^ b := (algebraMap ℚ k).injective h
  exact zpow_right_injective₀ (by norm_num) (by norm_num) hQ

/-- The dimension of an auxiliary weight space is counted by basis vectors with that weight. -/
theorem finrank_auxiliaryWeightSpace_eq_card
    (k : Type*) [Field k] [CharZero k]
    (N d : ℕ) {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (b : Module.Basis (Fin d) k W) (wt : Fin d → Fin N → ℤ)
    (hb : ∀ (c : Fin d) (i : Fin N) (t : kˣ),
      σ (diagonalUnit k N i t) (b c) = ((t ^ wt c i : kˣ) : k) • b c)
    (ν : Fin N → ℤ) :
    Module.finrank k (integerTupleSubmodule k N σ ν) =
      (Finset.univ.filter (fun c => wt c = ν)).card := by
  classical
  have hspan : integerTupleSubmodule k N σ ν =
      Submodule.span k
        (Set.range (fun c : {c : Fin d // wt c = ν} => b c.val)) := by
    apply le_antisymm
    · intro w hw
      simp only [integerTupleSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        sub_eq_zero] at hw
      set r := b.repr w with hr
      have hzero : ∀ c, wt c ≠ ν → r c = 0 := by
        intro c hc
        obtain ⟨i, hi⟩ : ∃ i, wt c i ≠ ν i := by
          by_contra h
          push Not at h
          exact hc (funext h)
        obtain ⟨t, ht⟩ := exists_unit_pow_ne_of_ne k hi
        have expand : σ (diagonalUnit k N i t) w =
            ∑ dd, (r dd * ((t ^ wt dd i : kˣ) : k)) • b dd := by
          conv_lhs =>
            rw [show w = ∑ dd, r dd • b dd from (b.sum_repr w).symm]
          rw [map_sum]
          refine Finset.sum_congr rfl (fun dd _ => ?_)
          rw [map_smul, hb dd i t, smul_smul]
        have e1 : b.repr (σ (diagonalUnit k N i t) w) c =
            r c * ((t ^ wt c i : kˣ) : k) := by
          rw [expand, map_sum, Finsupp.finsetSum_apply]
          simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
            Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq' Finset.univ c
            (fun dd => r dd * ((t ^ wt dd i : kˣ) : k))]
          simp
        have e2 : b.repr (σ (diagonalUnit k N i t) w) c =
            ((t ^ ν i : kˣ) : k) * r c := by
          rw [hw i t, map_smul, Finsupp.smul_apply, smul_eq_mul]
        have key : r c * ((t ^ wt c i : kˣ) : k) =
            ((t ^ ν i : kˣ) : k) * r c := by
          rw [← e1, e2]
        have h0 : r c *
            (((t ^ wt c i : kˣ) : k) - ((t ^ ν i : kˣ) : k)) = 0 := by
          linear_combination key
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exact absurd (sub_eq_zero.1 h) ht
      rw [show w = ∑ c, r c • b c from (b.sum_repr w).symm]
      apply Submodule.sum_mem
      intro c _
      by_cases hc : wt c = ν
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span ⟨⟨c, hc⟩, rfl⟩)
      · rw [hzero c hc, zero_smul]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      simp only [SetLike.mem_coe, integerTupleSubmodule, Submodule.mem_iInf,
        LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, sub_eq_zero]
      intro i t
      rw [hb c.val i t, show wt c.val i = ν i from congrFun c.property i]
  rw [hspan,
    finrank_span_eq_card
      (show LinearIndependent k
          (fun c : {c : Fin d // wt c = ν} => b c.val) from
        b.linearIndependent.comp Subtype.val Subtype.val_injective),
    Fintype.card_subtype]

/-- A dual basis vector has the negation of the displayed auxiliary weight. -/
theorem dualBasis_hasNegatedAuxiliaryWeight
    (k : Type*) [Field k] (N d : ℕ)
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (b : Module.Basis (Fin d) k W) (wt : Fin d → Fin N → ℤ)
    (hb : ∀ (c : Fin d) (i : Fin N) (t : kˣ),
      σ (diagonalUnit k N i t) (b c) = ((t ^ wt c i : kˣ) : k) • b c)
    (c : Fin d) (i : Fin N) (t : kˣ) :
    (Representation.dual σ) (diagonalUnit k N i t) (b.dualBasis c) =
      ((t ^ (-wt c i) : kˣ) : k) • b.dualBasis c := by
  apply Module.Basis.ext b
  intro e
  rw [Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, auxiliaryCoordinateElement_inv, hb e i t⁻¹, map_smul,
    LinearMap.smul_apply, Module.Basis.dualBasis_apply_self]
  by_cases h : e = c
  · subst h
    rw [if_pos rfl, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    congr 1
    rw [inv_zpow, zpow_neg]
  · rw [if_neg h, smul_zero, smul_zero]

/-- The dual auxiliary weight space has the dimension of the space indexed by the negated
weight. -/
theorem finrank_dualAuxiliaryWeightSpace
    (k : Type*) [Field k] [CharZero k]
    (N d : ℕ) {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (b : Module.Basis (Fin d) k W) (wt : Fin d → Fin N → ℤ)
    (hb : ∀ (c : Fin d) (i : Fin N) (t : kˣ),
      σ (diagonalUnit k N i t) (b c) = ((t ^ wt c i : kˣ) : k) • b c)
    (μ : Fin N → ℤ) :
    Module.finrank k
        (integerTupleSubmodule k N (Representation.dual σ) μ) =
      Module.finrank k (integerTupleSubmodule k N σ (fun i => -μ i)) := by
  classical
  rw [finrank_auxiliaryWeightSpace_eq_card k N d
        (Representation.dual σ) b.dualBasis (fun c i => -wt c i)
        (fun c i t =>
          dualBasis_hasNegatedAuxiliaryWeight k N d σ b wt hb c i t) μ,
    finrank_auxiliaryWeightSpace_eq_card k N d σ b wt hb
      (fun i => -μ i)]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    funext i
    have := congrFun h i
    omega
  · intro h
    funext i
    have := congrFun h i
    omega

/-- The auxiliary space indexed by natural weights agrees with its integer-indexed
counterpart. -/
theorem natAuxiliaryWeightSpace_eq_intAuxiliaryWeightSpace
    (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (μ : Fin N → ℕ) :
    weightSpace k N M (fun i => μ i) =
      integerTupleSubmodule k N M.ρ (fun i => (μ i : ℤ)) := by
  simp only [weightSpace, integerTupleSubmodule]
  refine iInf_congr fun i => iInf_congr fun t => ?_
  have hs : ((t ^ (μ i : ℤ) : kˣ) : k) = (t : k) ^ μ i := by
    rw [Units.val_zpow_eq_zpow_val, zpow_natCast]
  rw [hs]

/-- Under the stated spanning condition, a dual auxiliary-polynomial coefficient is the dimension
at the opposite weight. -/
theorem dualAuxiliaryPolynomial_coeff_eq_finrank_negWeightSpace
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N : ℕ) (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤)
    (μ : Fin N →₀ ℕ) :
    (weightCharacter k N (FDRep.of (Representation.dual M.ρ))).coeff μ =
      (Module.finrank k
        (integerTupleSubmodule k N M.ρ (fun i => -(μ i : ℤ))) : ℚ) := by
  obtain ⟨d, v, wt, hv⟩ := exists_auxiliary_weight_vector_data M h_span
  have hvℤ : ∀ (c : Fin d) (i : Fin N) (t : kˣ),
      M.ρ (diagonalUnit k N i t) (v c) =
        ((t ^ (wt c i : ℤ) : kˣ) : k) • v c := by
    intro c i t
    rw [hv c i t, Units.val_zpow_eq_zpow_val, zpow_natCast]
  have hmain := finrank_dualAuxiliaryWeightSpace k N d M.ρ v
    (fun c i => (wt c i : ℤ)) hvℤ (fun i => (μ i : ℤ))
  rw [coeff_weightCharacter k N
      (FDRep.of (Representation.dual M.ρ)) μ,
    natAuxiliaryWeightSpace_eq_intAuxiliaryWeightSpace k N
      (FDRep.of (Representation.dual M.ρ)) (fun i => μ i),
    FDRep.of_ρ', hmain]

end RepresentationTheory.AuxiliaryWeightSpaces.Duality
