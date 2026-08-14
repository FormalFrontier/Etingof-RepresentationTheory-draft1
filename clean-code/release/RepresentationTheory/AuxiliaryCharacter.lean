/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary
import RepresentationTheory.TensorPower

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.cdot false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false

open CategoryTheory MvPolynomial

open scoped TensorProduct

noncomputable section

universe u

namespace RepresentationTheory.AuxiliaryCharacter

private theorem alternant_det_injective (N : ℕ) (e₁ e₂ : Fin N → ℕ)
    (he₁ : StrictAnti e₁) (he₂ : StrictAnti e₂)
    (h : (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e₁).det = (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e₂).det) :
    e₁ = e₂ := by

  have hc₁ := RepresentationTheory.SymmetricPolynomials.Alternant.coeff_det_alternantMatrix_of_strictAnti he₁ he₁
  simp only [ite_true] at hc₁

  rw [h, RepresentationTheory.SymmetricPolynomials.Alternant.coeff_det_alternantMatrix_of_strictAnti he₂ he₁] at hc₁

  revert hc₁; split_ifs with heq
  · exact fun _ => heq.symm
  · exact fun h => absurd h one_ne_zero.symm

private theorem shiftedExps_strictAnti' (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    StrictAnti (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam) := by
  intro i j hij; simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]
  exact Nat.add_lt_add_of_le_of_lt (hlam hij.le) (Nat.sub_lt_sub_left (by omega) hij)

private theorem shiftedExps_injective (N : ℕ) :
    Function.Injective (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N) := by
  intro lam₁ lam₂ h
  funext j; exact Nat.add_right_cancel (congr_fun h j)

/-- Two antitone functions coincide when their associated auxiliary polynomials agree. -/
theorem antitone_eq_of_auxiliaryPolynomial_eq (N : ℕ) (lam₁ lam₂ : Fin N → ℕ)
    (hlam₁ : Antitone lam₁) (hlam₂ : Antitone lam₂)
    (h : RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam₁ = RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam₂) :
    lam₁ = lam₂ := by
  have h_alt : (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam₁)).det =
      (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam₂)).det := by
    have hΔ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.Auxiliary.det_ne_zero N
    apply mul_right_cancel₀ hΔ
    rw [← RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase, ← RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase, h]
  exact shiftedExps_injective N
    (alternant_det_injective N _ _ (shiftedExps_strictAnti' N lam₁ hlam₁)
      (shiftedExps_strictAnti' N lam₂ hlam₂) h_alt)

/-- The indexed family of auxiliary polynomials is linearly independent over the rationals. -/
theorem auxiliaryPolynomial_linearIndependent (N : ℕ) :
    LinearIndependent ℚ (fun (lam : {lam : Fin N → ℕ // Antitone lam}) =>
      RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam.val) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum μ hμ

  have hmul : ∑ lam ∈ s, g lam • (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.val)).det = 0 := by
    have step : (∑ lam ∈ s, g lam • RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam.val) *
          (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det = 0 := by
      rw [hsum, zero_mul]
    rw [Finset.sum_mul] at step
    simp only [smul_mul_assoc, RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase] at step
    exact step

  have hcoeff := congr_arg
    (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N μ.val))) hmul
  rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hcoeff
  simp only [MvPolynomial.coeff_smul, smul_eq_mul] at hcoeff

  have h_each : ∀ lam ∈ s,
      g lam * MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N μ.val))
        (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.val)).det =
          if lam = μ then g lam else 0 := by
    intro lam _
    rw [RepresentationTheory.SymmetricPolynomials.Alternant.coeff_det_alternantMatrix_of_strictAnti (shiftedExps_strictAnti' N lam.val lam.prop)
      (shiftedExps_strictAnti' N μ.val μ.prop)]
    rcases eq_or_ne lam μ with heq | hne
    · subst heq; rw [if_pos rfl, if_pos rfl, mul_one]
    · have h_ne : RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam.val ≠ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N μ.val :=
        fun h => hne (Subtype.ext (shiftedExps_injective N h))
      rw [if_neg h_ne, if_neg hne, mul_zero]
  rw [Finset.sum_congr rfl h_each, Finset.sum_ite_eq' s μ g, if_pos hμ] at hcoeff
  exact hcoeff

private lemma homogeneousComponent_mul_of_isHomogeneous_right
    {σ R : Type*} [CommSemiring R]
    (φ ψ : MvPolynomial σ R) {n : ℕ} (hψ : ψ.IsHomogeneous n) (k : ℕ) :
    MvPolynomial.homogeneousComponent (k + n) (φ * ψ) =
      MvPolynomial.homogeneousComponent k φ * ψ := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_homogeneousComponent]
  split_ifs with hd
  · rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [MvPolynomial.coeff_homogeneousComponent]
    have hdeg : d.degree = x.1.degree + x.2.degree := by
      rw [← hx]; exact map_add Finsupp.degree x.1 x.2
    split_ifs with h1
    · rfl
    · have h2 : x.2.degree ≠ n := fun h => h1 (by omega)
      rw [hψ.coeff_eq_zero h2, mul_zero, mul_zero]
  · symm
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [MvPolynomial.coeff_homogeneousComponent]
    have hdeg : d.degree = x.1.degree + x.2.degree := by
      rw [← hx]; exact map_add Finsupp.degree x.1 x.2
    split_ifs with h1
    · have h2 : x.2.degree ≠ n := fun h => hd (by omega)
      rw [hψ.coeff_eq_zero h2, mul_zero]
    · exact zero_mul _

private lemma degree_eq_weight_one_apply {σ : Type*} (d : σ →₀ ℕ) :
    Finsupp.degree d = Finsupp.weight 1 d := by
  rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]

/-- The auxiliary polynomial is homogeneous in the total degree of its index function. -/
theorem auxiliaryPolynomial_isHomogeneous (N : ℕ) (lam : Fin N → ℕ) :
    (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam).IsHomogeneous (∑ i, lam i) := by
  intro d hd

  rw [← degree_eq_weight_one_apply]

  by_contra hne
  have halt : (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam)).det.IsHomogeneous
      ((∑ i, lam i) + (∑ j : Fin N, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j)) := by
    have h := RepresentationTheory.SymmetricPolynomials.Alternant.det_alternantMatrix_isHomogeneous (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam)
    have heq : ∑ j : Fin N, RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j =
        (∑ i, lam i) + (∑ j : Fin N, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j) := by
      simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents, Finset.sum_add_distrib]
    rw [heq] at h
    exact h
  have hΔhom : (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det.IsHomogeneous
      (∑ j : Fin N, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j) :=
    RepresentationTheory.SymmetricPolynomials.Alternant.det_alternantMatrix_isHomogeneous (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)
  have hΔne : (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det ≠ 0 :=
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.Auxiliary.det_ne_zero N

  have hprod_eq := homogeneousComponent_mul_of_isHomogeneous_right
    (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det hΔhom d.degree
  rw [RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase] at hprod_eq

  have hne' : d.degree + (∑ j : Fin N, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j) ≠
      (∑ i, lam i) + (∑ j : Fin N, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j) := fun heq => hne (by omega)
  have halt_zero :
      MvPolynomial.homogeneousComponent (d.degree + (∑ j : Fin N, RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j))
        (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam)).det = 0 := by
    rw [MvPolynomial.homogeneousComponent_of_mem halt, if_neg hne']
  rw [halt_zero] at hprod_eq

  have h_eq_zero : MvPolynomial.homogeneousComponent d.degree (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) = 0 :=
    (mul_eq_zero.mp hprod_eq.symm).resolve_right hΔne

  have h_coeff_zero :
      MvPolynomial.coeff d (MvPolynomial.homogeneousComponent d.degree (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam)) = 0 := by
    rw [h_eq_zero]; exact MvPolynomial.coeff_zero d
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos rfl] at h_coeff_zero
  exact hd h_coeff_zero

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- The family of auxiliary weight spaces is independent under suprema. -/
theorem iSupIndep_auxiliaryWeightSpace (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    iSupIndep (fun μ : Fin N →₀ ℕ => RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i)) := by
  set f : Fin N × kˣ → Module.End k M := fun p => M.ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N p.1 p.2)
  have h_comm : ∀ (p₁ p₂ : Fin N × kˣ), Commute (f p₁) (f p₂) :=
    fun p₁ p₂ => RepresentationTheory.GeneralLinearGroup.WeightCharacter.commute_rep_diagonalUnit k N M p₁.1 p₁.2 p₂.1 p₂.2
  have h_mapsTo : ∀ (p₁ p₂ : Fin N × kˣ) (φ : k),
      Set.MapsTo (f p₁) ((f p₂).maxGenEigenspace φ) ((f p₂).maxGenEigenspace φ) :=
    fun p₁ p₂ φ => Module.End.mapsTo_maxGenEigenspace_of_comm (h_comm p₂ p₁) φ
  have h_indep := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f h_mapsTo

  set χ : (Fin N →₀ ℕ) → (Fin N × kˣ → k) :=
    fun μ p => (p.2 : k) ^ (μ p.1)
  have h_inj : Function.Injective χ := by
    intro μ₁ μ₂ heq
    ext i
    by_contra hi
    obtain ⟨t, ht⟩ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.exists_unit_pow_ne_pow k hi
    exact ht (congr_fun heq (i, t))

  exact (h_indep.comp h_inj).mono (fun μ =>
    le_iInf (fun p => RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace_le_maxGenEigenspace k N M (fun j => μ j) p.1 p.2))

/-- The ambient dimension is the sum of the dimensions of its auxiliary weight spaces. -/
theorem finrank_eq_sum_finrank_auxiliaryWeightSpace (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_top : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤) :
    Module.finrank k M =
      ∑ μ ∈ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N M).toFinset,
        Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i)) := by
  set p : (Fin N →₀ ℕ) → Submodule k M :=
    fun μ => RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) with hp_def
  have h_indep : iSupIndep p := iSupIndep_auxiliaryWeightSpace k N M
  have hs_fin : {μ | p μ ≠ ⊥}.Finite := RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N M
  haveI : Fintype {μ // p μ ≠ ⊥} := hs_fin.fintype

  have h_internal : DirectSum.IsInternal (fun μ : {μ // p μ ≠ ⊥} => p μ.val) := by
    rw [DirectSum.isInternal_ne_bot_iff]
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨h_indep, h_top⟩

  let e : DirectSum {μ // p μ ≠ ⊥} (fun μ => (p μ.val : Submodule k M)) ≃ₗ[k] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap _) h_internal
  rw [← LinearEquiv.finrank_eq e, Module.finrank_directSum]

  rw [← Finset.sum_attach hs_fin.toFinset (fun μ => Module.finrank k (p μ)),
    show hs_fin.toFinset.attach = (Finset.univ : Finset {x // x ∈ hs_fin.toFinset})
      from Finset.attach_eq_univ]

  refine Fintype.sum_equiv
    ({ toFun := fun ⟨x, hx⟩ => ⟨x, (Set.Finite.mem_toFinset hs_fin).mpr hx⟩,
       invFun := fun ⟨x, hx⟩ => ⟨x, (Set.Finite.mem_toFinset hs_fin).mp hx⟩,
       left_inv := fun _ => rfl, right_inv := fun _ => rfl } :
      {μ // p μ ≠ ⊥} ≃ {x // x ∈ hs_fin.toFinset})
    (fun μ => Module.finrank k (p μ.val))
    (fun μ => Module.finrank k (p μ.val)) (fun _ => rfl)

/-- Equal auxiliary polynomials give equal dimensions when both displayed weight families are exhaustive. -/
theorem finrank_eq_of_auxiliaryPolynomial_eq (N : ℕ)
    (M₁ M₂ : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h₁_top : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M₁ (fun i => μ i) = ⊤)
    (h₂_top : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M₂ (fun i => μ i) = ⊤)
    (h_char : RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N M₁ = RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N M₂) :
    Module.finrank k M₁ = Module.finrank k M₂ := by

  have h_ptw : ∀ μ : Fin N →₀ ℕ,
      Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M₁ (fun i => μ i)) =
      Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M₂ (fun i => μ i)) := by
    intro μ
    have h₁ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter k N M₁ μ
    have h₂ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter k N M₂ μ
    have h_ℚ : ((Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M₁ (fun i => μ i)) : ℚ) =
        (Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M₂ (fun i => μ i)) : ℚ)) := by
      rw [← h₁, ← h₂, h_char]
    exact_mod_cast h_ℚ

  rw [finrank_eq_sum_finrank_auxiliaryWeightSpace k N M₁ h₁_top,
      finrank_eq_sum_finrank_auxiliaryWeightSpace k N M₂ h₂_top]
  set S₁ := (RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N M₁).toFinset
  set S₂ := (RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N M₂).toFinset
  have h_extend : ∀ (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (S : Finset (Fin N →₀ ℕ))
      (hS : (RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N M).toFinset ⊆ S),
      ∑ μ ∈ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N M).toFinset,
          Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i)) =
        ∑ μ ∈ S, Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i)) := by
    intro M S hS
    apply Finset.sum_subset hS
    intro μ _ hμ
    rw [Set.Finite.mem_toFinset] at hμ
    simp only [Set.mem_setOf_eq, not_not] at hμ
    rw [hμ, finrank_bot]
  rw [h_extend M₁ (S₁ ∪ S₂) Finset.subset_union_left,
      h_extend M₂ (S₁ ∪ S₂) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun μ _ => h_ptw μ)

/-- Every nonzero auxiliary weight space has the total degree forced by the equal auxiliary polynomial. -/
theorem auxiliaryWeight_degree_eq_of_polynomial_eq (N : ℕ)
    (lam : Fin N → ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N M = RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam)
    (μ : Fin N → ℕ) (hμ : 0 < Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M μ)) :
    ∑ i, μ i = ∑ i, lam i := by
  set d : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm μ with hd_def

  have hd_fun : (fun i : Fin N => (d i : ℕ)) = μ := by
    funext i; rfl

  have hcoeff_char : (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N M).coeff d > 0 := by
    rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter k N M d, hd_fun]
    exact_mod_cast hμ

  have hcoeff_schur : (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam).coeff d ≠ 0 := by
    rw [← h]; exact ne_of_gt hcoeff_char

  have h_weight : Finsupp.weight 1 d = ∑ i, lam i :=
    auxiliaryPolynomial_isHomogeneous N lam hcoeff_schur
  have hd_deg_lam : d.degree = ∑ i, lam i := by
    rw [degree_eq_weight_one_apply]; exact h_weight

  have hd_deg_mu : d.degree = ∑ i, μ i := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_congr rfl (fun i _ => congrFun hd_fun i)
  omega

private def onesFinsupp (N : ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

private theorem onesFinsupp_apply (N : ℕ) (i : Fin N) : onesFinsupp N i = 1 := by
  simp [onesFinsupp]

private theorem onesFinsupp_support (N : ℕ) : (onesFinsupp N).support = Finset.univ := by
  ext i; simp [onesFinsupp]

private theorem prod_X_eq_monomial_ones (N : ℕ) :
    (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) =
      MvPolynomial.monomial (onesFinsupp N) 1 := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial (R := ℚ) (s := onesFinsupp N),
    onesFinsupp_support]
  simp_rw [onesFinsupp_apply, pow_one]

/-- The stated shift and boundary conditions multiply the auxiliary polynomial by the product of all variables. -/
theorem auxiliaryPolynomial_eq_product_X_mul_of_weightSpaceShift (N : ℕ)
    (M₁ M₂ : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_shift : ∀ ν : Fin N → ℕ,
      Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M₁ (fun i => ν i + 1)) =
        Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M₂ ν))
    (h_vanish : ∀ μ : Fin N → ℕ, (∃ i, μ i = 0) →
      Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M₁ μ) = 0) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N M₁ =
      (∏ i : Fin N, MvPolynomial.X i) * RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N M₂ := by
  ext μ
  rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter, prod_X_eq_monomial_ones, coeff_monomial_mul']
  split_ifs with h
  ·
    rw [one_mul, RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter]
    have hge : ∀ i : Fin N, 1 ≤ μ i := fun i => by
      have := h i; rwa [onesFinsupp_apply] at this
    have key : (fun i => (μ - onesFinsupp N) i + 1) = (⇑μ : Fin N → ℕ) := by
      ext i; simp [Finsupp.tsub_apply, onesFinsupp_apply, Nat.sub_add_cancel (hge i)]
    have := h_shift (fun i => (μ - onesFinsupp N) i)
    rw [key] at this
    exact_mod_cast this
  ·
    have hexists : ∃ i : Fin N, (μ i : ℕ) = 0 := by
      by_contra hall
      push Not at hall
      exact h fun i => by rw [onesFinsupp_apply]; exact Nat.one_le_iff_ne_zero.mpr (hall i)
    exact_mod_cast h_vanish (⇑μ) hexists

open scoped DirectSum in
open Representation in
omit [CharZero k] in
private lemma directSum_rep_coord (N : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → Type _) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (ρ : ∀ i, Representation k (Matrix.GeneralLinearGroup (Fin N) k) (V i))
    (g : Matrix.GeneralLinearGroup (Fin N) k) (x : DirectSum ι V) (j : ι) :
    (Representation.directSum ρ g x) j = ρ j g (x j) := by
  change (DirectSum.lmap (fun m => ρ m g)) x j = ρ j g (x j)
  rw [DirectSum.lmap_apply]

open scoped DirectSum in
open Representation in
omit [CharZero k] in
private lemma mem_glWeightSpace_directSum_iff (N : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → Type _) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module.Finite k (V i)]
    (ρ : ∀ i, Representation k (Matrix.GeneralLinearGroup (Fin N) k) (V i))
    (μ : Fin N → ℕ) (x : DirectSum ι V) :
    x ∈ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (Representation.directSum ρ)) μ ↔
      ∀ j : ι, x j ∈ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (ρ j)) μ := by
  simp only [RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace, Submodule.mem_iInf, LinearMap.mem_ker, FDRep.of_ρ',
    LinearMap.sub_apply, LinearMap.smul_apply]

  constructor
  · intro h j i t

    have hit : Representation.directSum ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t) x -
        (↑t : k) ^ μ i • x = 0 := h i t

    have h_comp : (Representation.directSum ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t) x -
        (↑t : k) ^ μ i • x) j = (0 : DirectSum ι V) j := by rw [hit]
    rw [DFinsupp.sub_apply, DFinsupp.smul_apply, directSum_rep_coord,
      DFinsupp.zero_apply] at h_comp

    exact h_comp
  · intro h i t

    refine DFinsupp.ext fun j => ?_
    change (Representation.directSum ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t) x -
        (↑t : k) ^ μ i • x) j = (0 : DirectSum ι V) j
    rw [DFinsupp.sub_apply, DFinsupp.smul_apply, directSum_rep_coord,
      DFinsupp.zero_apply]
    have := h j i t
    exact this

open scoped DirectSum in
open Representation in
omit [CharZero k] in
/-- Constructs the linear equivalence from a direct sum of auxiliary weight spaces to the corresponding combined space. -/
noncomputable def directSumAuxiliaryWeightSpaceEquiv (N : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → Type _) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module.Finite k (V i)]
    (ρ : ∀ i, Representation k (Matrix.GeneralLinearGroup (Fin N) k) (V i))
    (μ : Fin N → ℕ) :
    DirectSum ι (fun j => ↥(RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (ρ j)) μ)) ≃ₗ[k]
      ↥(RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (Representation.directSum ρ)) μ) := by

  let fwd₀ : DirectSum ι (fun j => ↥(RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (ρ j)) μ)) →ₗ[k]
      DirectSum ι V :=
    DirectSum.lmap (fun j => (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (ρ j)) μ).subtype)
  have h_inj : Function.Injective fwd₀ :=
    (DirectSum.lmap_injective _).mpr (fun _ => Subtype.val_injective)
  have h_range : LinearMap.range fwd₀ =
      (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (Representation.directSum ρ)) μ) := by
    ext z
    simp only [LinearMap.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      rw [mem_glWeightSpace_directSum_iff]
      intro j

      change (x j).val ∈ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (ρ j)) μ
      exact (x j).2
    · intro hz
      rw [mem_glWeightSpace_directSum_iff] at hz

      refine ⟨∑ j : ι, DirectSum.of
        (fun j' => ↥(RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (ρ j')) μ)) j ⟨z j, hz j⟩, ?_⟩

      rw [map_sum]
      simp only [fwd₀]

      ext j
      rw [DFinsupp.finsetSum_apply]
      simp [DirectSum.of_apply]

  exact (LinearEquiv.ofInjective fwd₀ h_inj).trans
    (LinearEquiv.ofEq _ _ h_range)

open scoped DirectSum in
open Representation in
omit [CharZero k] in
private lemma finrank_glWeightSpace_directSum (N : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → Type _) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module.Finite k (V i)]
    (ρ : ∀ i, Representation k (Matrix.GeneralLinearGroup (Fin N) k) (V i))
    (μ : Fin N → ℕ) :
    Module.finrank k
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (Representation.directSum ρ)) μ) =
      ∑ j : ι, Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (ρ j)) μ) := by
  rw [← LinearEquiv.finrank_eq (directSumAuxiliaryWeightSpaceEquiv k N V ρ μ),
    Module.finrank_directSum]

open scoped DirectSum in
open Representation in
omit [CharZero k] in
/-- The auxiliary polynomial of a finite direct sum is the sum of the individual polynomials. -/
theorem auxiliaryPolynomial_directSum (N : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → Type _) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module.Finite k (V i)]
    (ρ : ∀ i, Representation k (Matrix.GeneralLinearGroup (Fin N) k) (V i)) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (FDRep.of (Representation.directSum ρ)) =
      ∑ j : ι, RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (FDRep.of (ρ j)) := by
  ext μ
  rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter, MvPolynomial.coeff_sum]
  simp_rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter]
  exact_mod_cast finrank_glWeightSpace_directSum k N V ρ μ

omit [CharZero k] in
private theorem glWeightSpace_map_eq_of_rep_iso (N : ℕ)
    {V W : Type _} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (ρV : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (ρW : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (e : V ≃ₗ[k] W)
    (hequiv : ∀ g : Matrix.GeneralLinearGroup (Fin N) k, ∀ v : V,
      e (ρV g v) = ρW g (e v))
    (μ : Fin N → ℕ) :
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of ρV) μ).map (e : V →ₗ[k] W) =
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of ρW) μ := by
  ext w
  simp only [Submodule.mem_map, RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply,
    LinearEquiv.coe_coe]
  constructor
  · rintro ⟨v, hv, rfl⟩ i t
    have h : ρV (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t) v = ((t : k) ^ μ i) • v := sub_eq_zero.mp (hv i t)
    have h' : e (ρV (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t) v) = ((t : k) ^ μ i) • e v := by
      rw [h, map_smul]
    rw [hequiv] at h'
    exact sub_eq_zero.mpr h'
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    intro i t
    have h : ρW (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t) w = ((t : k) ^ μ i) • w := sub_eq_zero.mp (hw i t)
    have h1 : e (ρV (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t) (e.symm w)) = ((t : k) ^ μ i) • w := by
      rw [hequiv, e.apply_symm_apply, h]
    have h2 : e (((t : k) ^ μ i) • e.symm w) = ((t : k) ^ μ i) • w := by
      rw [map_smul, e.apply_symm_apply]
    exact sub_eq_zero.mpr (e.injective (h1.trans h2.symm))

omit [CharZero k] in
/-- An intertwining linear equivalence preserves the auxiliary polynomial. -/
theorem auxiliaryPolynomial_eq_of_linearEquiv (N : ℕ)
    {V W : Type _} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (ρV : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (ρW : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (e : V ≃ₗ[k] W)
    (hequiv : ∀ g : Matrix.GeneralLinearGroup (Fin N) k, ∀ v : V,
      e (ρV g v) = ρW g (e v)) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (FDRep.of ρV) = RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (FDRep.of ρW) := by
  ext μ
  rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter, RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter]
  congr 1
  rw [← glWeightSpace_map_eq_of_rep_iso k N ρV ρW e hequiv]
  exact (e.finrank_map_eq (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of ρV) μ)).symm

open scoped DirectSum in
open Representation in
omit [CharZero k] in
/-- Tensoring with a trivial finite module scales the auxiliary polynomial by its dimension. -/
theorem auxiliaryPolynomial_trivialTensor (N : ℕ)
    (S : Type _) [AddCommGroup S] [Module k S] [Module.Finite k S]
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N
        (FDRep.of ((Representation.trivial k
          (Matrix.GeneralLinearGroup (Fin N) k) S).tprod L.ρ)) =
      (Module.finrank k S : ℚ) • RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N L := by
  classical

  set n := Module.finrank k S with hn_def
  let b : Module.Basis (Fin n) k S := Module.finBasis k S

  let e : TensorProduct k S L ≃ₗ[k] (⨁ _ : Fin n, L) :=
    (b.equivFun.rTensor L) ≪≫ₗ TensorProduct.comm k (Fin n → k) L ≪≫ₗ
      TensorProduct.piScalarRight k k L (Fin n) ≪≫ₗ
      (DirectSum.linearEquivFunOnFintype k (Fin n) (fun _ : Fin n => L)).symm

  have hequiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : TensorProduct k S L),
      e (((Representation.trivial k
            (Matrix.GeneralLinearGroup (Fin N) k) S).tprod L.ρ) g v) =
        Representation.directSum (fun _ : Fin n => L.ρ) g (e v) := by
    intro g
    suffices h : (e.toLinearMap ∘ₗ
        ((Representation.trivial k
          (Matrix.GeneralLinearGroup (Fin N) k) S).tprod L.ρ) g) =
        (Representation.directSum (fun _ : Fin n => L.ρ) g).comp e.toLinearMap by
      intro v; exact LinearMap.congr_fun h v
    apply TensorProduct.ext'
    intro s ℓ

    refine DFinsupp.ext fun j => ?_

    have hrhs_comp :
        (Representation.directSum (fun _ : Fin n => L.ρ) g (e (s ⊗ₜ[k] ℓ))) j =
          L.ρ g ((e (s ⊗ₜ[k] ℓ)) j) :=
      directSum_rep_coord k N (fun _ : Fin n => L) (fun _ => L.ρ) g _ j

    have he : ∀ (x : L),
        e (s ⊗ₜ[k] x) = (DirectSum.linearEquivFunOnFintype k (Fin n)
          (fun _ : Fin n => L)).symm (fun j : Fin n => (b.equivFun s j) • x) := by
      intro x
      simp only [e, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
        TensorProduct.comm_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]

    have hcomp : ∀ (f : Fin n → L),
        ((DirectSum.linearEquivFunOnFintype k (Fin n) (fun _ : Fin n => L)).symm f)
            j = f j := by
      intro f

      change (DFinsupp.equivFunOnFintype.symm f : ⨁ _ : Fin n, L) j = f j
      rw [show (DFinsupp.equivFunOnFintype.symm f : ⨁ _ : Fin n, L) j
            = DFinsupp.equivFunOnFintype (DFinsupp.equivFunOnFintype.symm f) j from rfl,
          DFinsupp.equivFunOnFintype.apply_symm_apply]

    have hlhs :
        (e (((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
              S).tprod L.ρ) g (s ⊗ₜ[k] ℓ))) j = (b.equivFun s j) • L.ρ g ℓ := by
      rw [show ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                  S).tprod L.ρ) g (s ⊗ₜ[k] ℓ) = s ⊗ₜ[k] L.ρ g ℓ from by
            simp [Representation.tprod_apply, TensorProduct.map_tmul]]
      rw [he (L.ρ g ℓ), hcomp]

    have hrhs :
        L.ρ g ((e (s ⊗ₜ[k] ℓ)) j) = (b.equivFun s j) • L.ρ g ℓ := by
      rw [he ℓ, hcomp, map_smul]

    calc (e (((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
            S).tprod L.ρ) g (s ⊗ₜ[k] ℓ))) j
        = (b.equivFun s j) • L.ρ g ℓ := hlhs
      _ = L.ρ g ((e (s ⊗ₜ[k] ℓ)) j) := hrhs.symm
      _ = (Representation.directSum (fun _ : Fin n => L.ρ) g (e (s ⊗ₜ[k] ℓ))) j :=
          hrhs_comp.symm
      _ = (((Representation.directSum (fun _ : Fin n => L.ρ) g).comp e.toLinearMap)
              (s ⊗ₜ[k] ℓ)) j := rfl

  rw [auxiliaryPolynomial_eq_of_linearEquiv k N _ _ e hequiv, auxiliaryPolynomial_directSum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

  exact (Nat.cast_smul_eq_nsmul ℚ n (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N L)).symm

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 60000 in
/-- Provides a finite auxiliary decomposition together with an equivariant linear equivalence. -/
theorem exists_auxiliaryRepresentationDecomposition
    (N n : ℕ) (_hN : n ≤ N) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type u)
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ)),
      ∃ (e : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n ≃ₗ[k]
          (DirectSum ι (fun i => S i ⊗[k] (L i : Type u)))),
        ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n),
          e (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v) := by
  classical

  obtain ⟨ι, hιFin, hιDec, S', hS'_simp, hS'_dist, hSi_fin, L, hL_simp, L_carrier,
      e, he, h_act⟩ :=
    RepresentationTheory.TensorPower.exists_tensorProduct_decomposition_with_action k N n
  let coherentSAddCommGroup : ∀ i, AddCommGroup (S' i) := fun i =>
    { Module.addCommMonoidToAddCommGroup k with
      toAddCommMonoid := (S' i).addCommMonoid }
  letI : ∀ i, AddCommGroup (S' i) := coherentSAddCommGroup
  refine ⟨ι, hιFin, hιDec, fun i => ↥(S' i),
    fun _ => inferInstance, fun _ => inferInstance,
    fun i => hSi_fin i, L, hL_simp, ?_, ?_⟩
  · exact e
  intro g v

  have h_lin :
      (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n g) ∘ₗ (e.symm : _ →ₗ[k] _) =
        (e.symm : _ →ₗ[k] _) ∘ₗ
          (Representation.directSum (fun i =>
            (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
              (↥(S' i))).tprod (L i).ρ) g) := by
    refine DirectSum.linearMap_ext k fun i => ?_
    apply TensorProduct.ext'
    intro s l
    change (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n g) (e.symm
        (DirectSum.lof k ι (fun i => ↥(S' i) ⊗[k] (L i : Type u)) i
          (s ⊗ₜ[k] l))) =
      e.symm ((Representation.directSum (fun i =>
        (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
          (↥(S' i))).tprod (L i).ρ) g)
        (DirectSum.lof k ι _ i (s ⊗ₜ[k] l)))

    rw [DirectSum.lof_eq_of, he i s l]

    change _ = e.symm (DirectSum.lmap
      (fun i => ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (DirectSum.of _ i (s ⊗ₜ[k] l)))
    rw [DirectSum.lmap_of, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply, he i s ((L i).ρ g l)]

    exact (h_act i g l s).symm

  have h := LinearMap.congr_fun h_lin (e v)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [show (e.symm : _ →ₗ[k] _) (e v) = v from e.symm_apply_apply v] at h
  rw [show (e.symm : _ →ₗ[k] _) ((Representation.directSum (fun i =>
      (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (e v)) =
    e.symm ((Representation.directSum (fun i =>
      (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (e v)) from rfl] at h
  exact (LinearEquiv.eq_symm_apply e).mp h

/-- Provides a finite auxiliary decomposition whose weighted polynomial sum has the specified value. -/
theorem exists_auxiliaryPolynomialDecomposition
    (N n : ℕ) (hN : n ≤ N) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type u)
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k)),
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (FDRep.of (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n)) =
        ∑ i : ι, (Module.finrank k (S i) : ℚ) • RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (L i) := by

  obtain ⟨ι, hιFin, hιDec, S, hS_acg, hS_mod, hS_fin, L, _hL_simp, e, he⟩ :=
    exists_auxiliaryRepresentationDecomposition k N n hN
  refine ⟨ι, hιFin, hιDec, S, hS_acg, hS_mod, hS_fin, L, ?_⟩

  have h_iso := auxiliaryPolynomial_eq_of_linearEquiv k N (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n)
    (Representation.directSum (fun i =>
      (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (S i)).tprod (L i).ρ)) e he
  rw [h_iso]

  rw [auxiliaryPolynomial_directSum]

  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact auxiliaryPolynomial_trivialTensor k N (S i) (L i)

omit [CharZero k] in
private theorem tensorStdBasis_mem_glWeightSpace (N n : ℕ) (f : Fin n → Fin N) :
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n f) ∈
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n))
        (fun i => (RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f) i) := by
  simp only [RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace, Submodule.mem_iInf]
  intro i t
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]
  change (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t)) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n f) =
      (t : k) ^ ((RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f) i) • RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n f
  rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation_apply_basis k N n i t f]
  rfl

private lemma sum_X_pow_eq_sum_prod (N n : ℕ) :
    (∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n =
      ∑ f : Fin n → Fin N, ∏ j : Fin n, (MvPolynomial.X (f j) : MvPolynomial (Fin N) ℚ) := by
  classical
  rw [Finset.sum_pow' (s := (Finset.univ : Finset (Fin N)))
    (f := fun i : Fin N => (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) n,
    Fintype.piFinset_univ]

private lemma sum_X_pow_eq_sum_monomial (N n : ℕ) :
    (∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n =
      ∑ f : Fin n → Fin N, MvPolynomial.monomial (RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f) (1 : ℚ) := by
  rw [sum_X_pow_eq_sum_prod]
  exact Finset.sum_congr rfl (fun f _ => RepresentationTheory.GeneralLinearGroup.WeightCharacter.prod_X_eq_monomial_count N f)

private lemma sum_X_pow_coeff (N n : ℕ) (μ : Fin N →₀ ℕ) :
    ((∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n).coeff μ =
      ((Finset.univ.filter
        fun f : Fin n → Fin N => RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f = μ).card : ℚ) := by
  classical
  rw [sum_X_pow_eq_sum_monomial, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  rw [Finset.sum_boole, Nat.cast_inj]

omit [CharZero k] in
private theorem tensorStdBasis_repr_eq_zero_of_ne_weight
    (N n : ℕ) (μ : Fin N →₀ ℕ)
    (v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n)
    (hv : v ∈ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n)) (fun i => μ i))
    (f : Fin n → Fin N) (hne : RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f ≠ μ) :
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n).repr v f = 0 := by

  obtain ⟨i, hi⟩ : ∃ i, (RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f) i ≠ μ i := by
    by_contra h
    push Not at h
    exact hne (Finsupp.ext h)

  obtain ⟨t, ht⟩ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.exists_unit_pow_ne_pow k hi

  have hmem : v ∈ LinearMap.ker
      ((FDRep.of (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n)).ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t)
        - ((t : k) ^ μ i) • LinearMap.id) := by
    simp only [RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace, Submodule.mem_iInf] at hv
    exact hv i t
  rw [LinearMap.mem_ker] at hmem

  have hmem' : (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t)) v - ((t : k) ^ μ i) • v = 0 := hmem

  have hcoord := congr_arg (fun w => (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n).repr w f) hmem'
  simp only [map_sub, Finsupp.sub_apply, map_zero, Finsupp.zero_apply, sub_eq_zero,
    map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord

  rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.repr_tensorPowerRepresentation_diagonalUnit k N n i t f v] at hcoord

  have hcoord' : ((t : k) ^ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f) i - (t : k) ^ μ i) *
      (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n).repr v f = 0 := by
    have hcw : (Finset.univ.filter (fun j : Fin n => f j = i)).card =
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f) i := rfl
    rw [hcw] at hcoord
    linear_combination hcoord
  rcases mul_eq_zero.mp hcoord' with hd | hr
  · exact absurd (sub_eq_zero.mp hd) ht
  · exact hr

omit [CharZero k] in
private theorem glWeightSpace_glTensorRep_eq_span (N n : ℕ) (μ : Fin N →₀ ℕ) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n)) (fun i => μ i) =
      Submodule.span k
        (Set.range (fun fh : {f : Fin n → Fin N // RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f = μ} =>
          RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n fh.val)) := by
  classical
  apply le_antisymm
  ·
    intro v hv
    have hv_eq : v =
        ((RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n).repr v).sum
          (fun f c => c • RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n f) := by
      conv_lhs => rw [← (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n).linearCombination_repr v]
      rw [Finsupp.linearCombination_apply]
    rw [hv_eq, Finsupp.sum]
    refine Submodule.sum_mem _ (fun f _ => ?_)
    by_cases htw : RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f = μ
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨⟨f, htw⟩, rfl⟩
    · rw [tensorStdBasis_repr_eq_zero_of_ne_weight k N n μ v hv f htw, zero_smul]
      exact Submodule.zero_mem _
  ·
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨f, hf⟩, rfl⟩
    have hmem := tensorStdBasis_mem_glWeightSpace k N n f

    have heq : (fun i => (RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f) i) = (fun i => μ i) := by
      funext i; rw [hf]
    rwa [heq] at hmem

omit [CharZero k] in
/-- The auxiliary weight spaces of the displayed representation jointly span the whole module. -/
theorem auxiliaryRepresentation_iSupWeightSpace_eq_top (N n : ℕ) :
    ⨆ (μ : Fin N →₀ ℕ),
        RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n)) (fun i => μ i) = ⊤ := by
  classical
  rw [eq_top_iff, ← (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n).span_eq, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact Submodule.mem_iSup_of_mem (RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f)
    (tensorStdBasis_mem_glWeightSpace k N n f)

omit [CharZero k] in
private theorem finrank_glWeightSpace_glTensorRep (N n : ℕ) (μ : Fin N →₀ ℕ) :
    Module.finrank k
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n)) (fun i => μ i)) =
      Fintype.card {f : Fin n → Fin N // RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f = μ} := by
  classical
  rw [glWeightSpace_glTensorRep_eq_span]

  have hf_lin : LinearIndependent k
      (fun fh : {f : Fin n → Fin N // RepresentationTheory.GeneralLinearGroup.WeightCharacter.fiberCount N f = μ} =>
        RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n fh.val) :=
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n).linearIndependent.comp _ Subtype.val_injective
  exact finrank_span_eq_card hf_lin

omit [CharZero k] in
/-- The polynomial attached to the auxiliary representation is a power of the sum of the variables. -/
theorem auxiliaryRepresentation_polynomial_eq_sum_X_pow (N n : ℕ) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (FDRep.of (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n)) =
      (∑ i : Fin N, MvPolynomial.X i) ^ n := by
  classical
  ext μ
  rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter, sum_X_pow_coeff, finrank_glWeightSpace_glTensorRep,
    Fintype.card_subtype]

omit [CharZero k] in
/-- The auxiliary representation polynomial is the displayed finite sum with coefficients given by auxiliary finranks over `Complex`. -/
theorem auxiliaryRepresentation_polynomial_eq_sum_auxiliaryFinrank_smul (N n : ℕ) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (FDRep.of (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n)) =
      ∑ lam : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n,
        (Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n
          (lam.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam.parts)) : ℚ) •
        RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam.parts := by
  rw [auxiliaryRepresentation_polynomial_eq_sum_X_pow, RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.sum_variables_pow_eq_sum_finrank_smul]

end RepresentationTheory.AuxiliaryCharacter
