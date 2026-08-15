/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.MvPolynomial.Vanishing
import RepresentationTheory.GeneralLinearGroup.Auxiliary
import RepresentationTheory.UnitTupleActions



open MvPolynomial

namespace RepresentationTheory.GeneralLinearGroup.DiagonalAction




/-- An auxiliary property of a family of linear endomorphisms indexed by a general linear group. -/
def IsAuxiliaryEndomorphismFamily
    {k : Type*} [Field k] (N : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) k Y)
    (P : Fin m → Fin m → MvPolynomial (Fin N × Fin N) k),
    ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (a c : Fin m),
      b.repr (ρ g (b c)) a =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c)


/-- This auxiliary endomorphism-family property implies the specified dependent condition. -/
theorem IsAuxiliaryEndomorphismFamily.toAuxiliaryCondition
    {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    (h : IsAuxiliaryEndomorphismFamily N ρ) : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N ρ := by
  obtain ⟨m, b, P, hP⟩ := h
  refine ⟨m, b, fun a c => MvPolynomial.rename Sum.inl (P a c), fun g a c => ?_⟩
  rw [hP g a c, RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation, MvPolynomial.eval_rename]
  rfl




/-- A multivariate polynomial over an infinite field is zero if it vanishes whenever every coordinate is nonzero. -/
theorem MvPolynomial.eq_zero_of_eval_eq_zero_on_nonzero
    {N : ℕ} {k : Type*} [Field k] [Infinite k] (p : MvPolynomial (Fin N) k)
    (h : ∀ t : Fin N → k, (∀ i, t i ≠ 0) → MvPolynomial.eval t p = 0) : p = 0 := by
  apply RepresentationTheory.MvPolynomial.Vanishing.eq_zero_of_eval_eq_zero_off_zero_locus (Q := ∏ i, X i)
  · intro hc
    rw [Finset.prod_eq_zero_iff] at hc
    obtain ⟨i, -, hi⟩ := hc
    exact MvPolynomial.X_ne_zero i hi
  · intro x hx
    apply h
    intro i hxi
    apply hx
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [MvPolynomial.eval_X, hxi])


/-- Finitely supported matrix coefficients are zero if their monomial sum vanishes at every tuple with nonzero coordinates. -/
theorem matrixCoefficients_eq_zero_of_eval_eq_zero_on_nonzero {N m : ℕ} {k : Type*} [Field k] [Infinite k]
    (S : Finset (Fin N →₀ ℕ)) (C : (Fin N →₀ ℕ) → Matrix (Fin m) (Fin m) k)
    (hsupp : ∀ μ ∉ S, C μ = 0)
    (h : ∀ t : Fin N → k, (∀ i, t i ≠ 0) →
       ∑ μ ∈ S, (∏ i, t i ^ μ i) • C μ = 0) :
    ∀ μ, C μ = 0 := by
  intro μ₀
  ext a c
  set p : MvPolynomial (Fin N) k := ∑ μ ∈ S, MvPolynomial.monomial μ (C μ a c) with hp
  have hpzero : p = 0 := by
    apply RepresentationTheory.GeneralLinearGroup.DiagonalAction.MvPolynomial.eq_zero_of_eval_eq_zero_on_nonzero
    intro t ht
    rw [hp, map_sum]
    have hsum : ∑ μ ∈ S, MvPolynomial.eval t (MvPolynomial.monomial μ (C μ a c))
         = ∑ μ ∈ S, (∏ i, t i ^ μ i) * (C μ a c) := by
      apply Finset.sum_congr rfl
      intro μ _
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp), mul_comm]
    rw [hsum]
    have hh := h t ht
    have hac := congrFun (congrFun hh a) c
    rw [Matrix.sum_apply, Matrix.zero_apply] at hac
    rw [← hac]
    apply Finset.sum_congr rfl
    intro μ _
    rw [Matrix.smul_apply, smul_eq_mul]
  have hcoeff : MvPolynomial.coeff μ₀ p = C μ₀ a c := by
    rw [hp, MvPolynomial.coeff_sum, Finset.sum_eq_single μ₀]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro μ _ hne
      rw [MvPolynomial.coeff_monomial, if_neg hne]
    · intro hμ
      rw [hsupp μ₀ hμ]; simp
  rw [hpzero, MvPolynomial.coeff_zero] at hcoeff
  rw [Matrix.zero_apply, ← hcoeff]


/-- Finitely supported matrix coefficients are zero if their monomial sum vanishes at every tuple of units. -/
theorem matrixCoefficients_eq_zero_of_eval_eq_zero_on_units {N m : ℕ} {k : Type*} [Field k] [Infinite k]
    (S : Finset (Fin N →₀ ℕ)) (C : (Fin N →₀ ℕ) → Matrix (Fin m) (Fin m) k)
    (hsupp : ∀ μ ∉ S, C μ = 0)
    (h : ∀ t : Fin N → kˣ,
       ∑ μ ∈ S, (∏ i, (t i : k) ^ μ i) • C μ = 0) :
    ∀ μ, C μ = 0 := by
  apply matrixCoefficients_eq_zero_of_eval_eq_zero_on_nonzero S C hsupp
  intro t ht
  have hu := h (fun i => Units.mk0 (t i) (ht i))
  simpa using hu



variable {k : Type*} [Field k]


/-- The underlying matrix of the diagonal unit matrix has the given units along its diagonal. -/
theorem coe_diagonalUnitMatrix {N : ℕ} (t : Fin N → kˣ) :
    (RepresentationTheory.UnitTupleActions.unitTupleElement k N t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => (t i : k)) := rfl

/-- The diagonal unit matrix associated to a pointwise product is the product of the associated diagonal unit matrices. -/
theorem diagonalUnitMatrix_mul {N : ℕ} (t s : Fin N → kˣ) :
    RepresentationTheory.UnitTupleActions.unitTupleElement k N (t * s) = RepresentationTheory.UnitTupleActions.unitTupleElement k N t * RepresentationTheory.UnitTupleActions.unitTupleElement k N s := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul]
  change Matrix.diagonal (fun i => ((t i * s i : kˣ) : k)) =
    Matrix.diagonal (fun i => (t i : k)) * Matrix.diagonal (fun i => (s i : k))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1

/-- The diagonal unit matrix associated to the constant-one function is one. -/
theorem diagonalUnitMatrix_one {N : ℕ} : RepresentationTheory.UnitTupleActions.unitTupleElement k N (1 : Fin N → kˣ) = 1 := by
  apply Units.ext
  change Matrix.diagonal (fun i => ((1 : Fin N → kˣ) i : k)) = (1 : Matrix (Fin N) (Fin N) k)
  rw [← Matrix.diagonal_one]; congr 1


/-- The unit associated to one coordinate equals the diagonal unit matrix obtained by updating that coordinate of the constant-one function. -/
theorem coordinateUnit_eq_diagonalUnitMatrix_update {N : ℕ} (i : Fin N) (t : kˣ) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t = RepresentationTheory.UnitTupleActions.unitTupleElement k N (Function.update (1 : Fin N → kˣ) i t) := by
  apply Units.ext
  change Matrix.diagonal (Function.update (1 : Fin N → k) i (t : k)) =
    Matrix.diagonal (fun j => ((Function.update (1 : Fin N → kˣ) i t) j : k))
  congr 1; funext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]; simp

end RepresentationTheory.GeneralLinearGroup.DiagonalAction



namespace RepresentationTheory.GeneralLinearGroup.DiagonalAction.MvPolynomial

/-- Evaluating after polynomial substitution equals evaluation at the values obtained by evaluating each substituted polynomial. -/
theorem eval_aeval {k : Type*} [CommSemiring k] {σ τ : Type*}
    (f : σ → MvPolynomial τ k) (x : τ → k) (p : MvPolynomial σ k) :
    eval x (aeval f p) = eval (fun i => eval x (f i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, eval_X]

end RepresentationTheory.GeneralLinearGroup.DiagonalAction.MvPolynomial



namespace RepresentationTheory.GeneralLinearGroup.DiagonalAction

open scoped BigOperators

variable {k : Type*} [Field k] [IsAlgClosed k]

set_option maxHeartbeats 6400000 in
-- Heavy: the orthogonal-idempotent extraction runs two matrix-density passes and
-- transports between `toMatrix`/`toLin` over the FDRep carrier; raise the heartbeat budget.

/-- If the general-linear-group-indexed endomorphism family of a finite-dimensional representation satisfies the auxiliary property, the supremum of the specified naturally indexed family is top. -/
theorem iSup_indexedFamily_eq_top_of_isAuxiliaryEndomorphismFamily {N : ℕ}
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hpoly : IsAuxiliaryEndomorphismFamily N M.ρ) :
    ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤ := by
  classical
  haveI : Infinite k := inferInstance
  obtain ⟨m, b, P, hP⟩ := hpoly
  -- The diagonal restriction of the coefficient polynomials: `Xᵢⱼ ↦ if i=j then Xᵢ else 0`.
  set Q : Fin m → Fin m → MvPolynomial (Fin N) k :=
    fun a c => aeval (fun ij : Fin N × Fin N => if ij.1 = ij.2 then X ij.1 else 0) (P a c)
    with hQ
  -- Evaluating `Q` at a torus point reproduces the matrix coefficient of `T(t)`.
  have hQeval : ∀ (t : Fin N → kˣ) (a c : Fin m),
      b.repr (M.ρ (RepresentationTheory.UnitTupleActions.unitTupleElement k N t) (b c)) a = eval (fun i => (t i : k)) (Q a c) := by
    intro t a c
    have hpt : (fun ij : Fin N × Fin N => (RepresentationTheory.UnitTupleActions.unitTupleElement k N t : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
        = (fun ij : Fin N × Fin N =>
            eval (fun i => (t i : k)) (if ij.1 = ij.2 then X ij.1 else 0)) := by
      funext ij
      rw [coe_diagonalUnitMatrix, Matrix.diagonal_apply]
      by_cases hij : ij.1 = ij.2 <;> simp [hij]
    rw [hP (RepresentationTheory.UnitTupleActions.unitTupleElement k N t) a c, hQ,
      RepresentationTheory.GeneralLinearGroup.DiagonalAction.MvPolynomial.eval_aeval, hpt]
  -- The coefficient matrices.
  set Cmat : (Fin N →₀ ℕ) → Matrix (Fin m) (Fin m) k :=
    fun μ a c => coeff μ (Q a c) with hCmat
  have hCmat_apply : ∀ μ a c, Cmat μ a c = coeff μ (Q a c) := fun _ _ _ => rfl
  -- Finite support.
  set S : Finset (Fin N →₀ ℕ) :=
    Finset.univ.biUnion (fun ac : Fin m × Fin m => (Q ac.1 ac.2).support) with hS
  have hSsupp : ∀ μ ∉ S, Cmat μ = 0 := by
    intro μ hμ
    ext a c
    rw [hCmat_apply, Matrix.zero_apply]
    by_contra hne
    apply hμ
    rw [hS, Finset.mem_biUnion]
    exact ⟨(a, c), Finset.mem_univ _, MvPolynomial.mem_support_iff.mpr hne⟩
  have hsub : ∀ a c : Fin m, (Q a c).support ⊆ S := by
    intro a c μ hμ
    rw [hS, Finset.mem_biUnion]
    exact ⟨(a, c), Finset.mem_univ _, hμ⟩
  -- The weight monomial.
  set w : (Fin N → kˣ) → (Fin N →₀ ℕ) → k := fun t μ => ∏ i, (t i : k) ^ μ i with hw
  have hw_apply : ∀ t μ, w t μ = ∏ i, (t i : k) ^ μ i := fun _ _ => rfl
  -- `T(t)` in matrix form: `toMatrix (M.ρ (RepresentationTheory.UnitTupleActions.unitTupleElement k N t)) = ∑_{μ∈S} w t μ • Cmat μ`.
  have hTmat : ∀ t : Fin N → kˣ,
      LinearMap.toMatrix b b (M.ρ (RepresentationTheory.UnitTupleActions.unitTupleElement k N t)) = ∑ μ ∈ S, w t μ • Cmat μ := by
    intro t
    ext a c
    rw [LinearMap.toMatrix_apply, hQeval t a c, MvPolynomial.eval_eq', Matrix.sum_apply,
      ← Finset.sum_subset (hsub a c)]
    · apply Finset.sum_congr rfl
      intro μ _
      rw [Matrix.smul_apply, smul_eq_mul, hCmat_apply, hw_apply, mul_comm]
    · intro μ _ hμ
      simp only [MvPolynomial.mem_support_iff, ne_eq, not_not] at hμ
      rw [Matrix.smul_apply, smul_eq_mul, hCmat_apply, hμ, mul_zero]
  -- multiplicativity of the weight monomial
  have hw_mul : ∀ (t s : Fin N → kˣ) μ, w (t * s) μ = w t μ * w s μ := by
    intro t s μ
    simp only [hw_apply, Pi.mul_apply, Units.val_mul, mul_pow]
    rw [Finset.prod_mul_distrib]
  -- The operators.
  set Cop : (Fin N →₀ ℕ) → (M →ₗ[k] M) := fun μ => Matrix.toLin b b (Cmat μ) with hCop
  have hCop_apply : ∀ μ, Cop μ = Matrix.toLin b b (Cmat μ) := fun _ => rfl
  -- `∑_{μ∈S} Cmat μ = 1`.
  have hCmat_sum : ∑ μ ∈ S, Cmat μ = 1 := by
    have h1 := hTmat 1
    rw [diagonalUnitMatrix_one, map_one, LinearMap.toMatrix_one] at h1
    rw [h1]
    apply Finset.sum_congr rfl
    intro μ _
    have hw1 : w 1 μ = 1 := by rw [hw_apply]; simp
    rw [hw1, one_smul]
  -- master identity:
  --   `∑_μ (w t μ * w s μ) • Cmat μ = ∑_{μ,ν} (w t μ * w s ν) • (Cmat μ * Cmat ν)`.
  have hmaster : ∀ t s : Fin N → kˣ,
      ∑ μ ∈ S, (w t μ * w s μ) • Cmat μ =
        ∑ μ ∈ S, ∑ ν ∈ S, (w t μ * w s ν) • (Cmat μ * Cmat ν) := by
    intro t s
    have hlhs : ∑ μ ∈ S, (w t μ * w s μ) • Cmat μ =
        LinearMap.toMatrix b b (M.ρ (RepresentationTheory.UnitTupleActions.unitTupleElement k N (t * s))) := by
      rw [hTmat (t * s)]
      apply Finset.sum_congr rfl
      intro μ _
      rw [hw_mul]
    rw [hlhs, diagonalUnitMatrix_mul, map_mul, LinearMap.toMatrix_mul, hTmat t, hTmat s,
      Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    rw [smul_mul_smul_comm]
  -- Step 1 density (in `t`): `∀ μ s, w s μ • Cmat μ = ∑_{ν∈S} w s ν • (Cmat μ * Cmat ν)`.
  have hstep1 : ∀ (s : Fin N → kˣ) (μ : Fin N →₀ ℕ),
      w s μ • Cmat μ = ∑ ν ∈ S, w s ν • (Cmat μ * Cmat ν) := by
    intro s
    have hD : ∀ μ, w s μ • Cmat μ - ∑ ν ∈ S, w s ν • (Cmat μ * Cmat ν) = 0 := by
      apply matrixCoefficients_eq_zero_of_eval_eq_zero_on_units S
        (fun μ => w s μ • Cmat μ - ∑ ν ∈ S, w s ν • (Cmat μ * Cmat ν))
      · intro μ hμ
        simp [hSsupp μ hμ]
      · intro t
        have hkey : ∑ μ ∈ S, (∏ i, (t i : k) ^ μ i) •
              (w s μ • Cmat μ - ∑ ν ∈ S, w s ν • (Cmat μ * Cmat ν)) =
            (∑ μ ∈ S, (w t μ * w s μ) • Cmat μ) -
              (∑ μ ∈ S, ∑ ν ∈ S, (w t μ * w s ν) • (Cmat μ * Cmat ν)) := by
          simp_rw [smul_sub]
          rw [Finset.sum_sub_distrib]
          congr 1
          · apply Finset.sum_congr rfl
            intro μ _
            rw [smul_smul, ← hw_apply t μ]
          · apply Finset.sum_congr rfl
            intro μ _
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro ν _
            rw [smul_smul, ← hw_apply t μ]
        rw [hkey, hmaster t s, sub_self]
    intro μ
    have := hD μ
    rw [sub_eq_zero] at this
    exact this
  -- Step 2 density (in `s`): orthogonal idempotents.
  have horth_mat : ∀ μ ν, Cmat μ * Cmat ν = if ν = μ then Cmat μ else 0 := by
    intro μ
    have hE : ∀ ν, Cmat μ * Cmat ν - (if ν = μ then Cmat μ else 0) = 0 := by
      apply matrixCoefficients_eq_zero_of_eval_eq_zero_on_units S
        (fun ν => Cmat μ * Cmat ν - (if ν = μ then Cmat μ else 0))
      · intro ν hν
        by_cases hνμ : ν = μ
        · subst hνμ
          simp [hSsupp ν hν]
        · rw [if_neg hνμ, hSsupp ν hν, Matrix.mul_zero, sub_zero]
      · intro s
        change ∑ ν ∈ S, (∏ i, (s i : k) ^ ν i) •
            (Cmat μ * Cmat ν - if ν = μ then Cmat μ else 0) = 0
        simp_rw [← hw_apply s, smul_sub]
        rw [Finset.sum_sub_distrib]
        have hfirst : ∑ ν ∈ S, w s ν • (Cmat μ * Cmat ν) = w s μ • Cmat μ := (hstep1 s μ).symm
        rw [hfirst]
        have hsecond : ∑ ν ∈ S, w s ν • (if ν = μ then Cmat μ else 0) =
            if μ ∈ S then w s μ • Cmat μ else 0 := by
          rw [← Finset.sum_ite_eq' S μ (fun ν => w s ν • Cmat μ)]
          apply Finset.sum_congr rfl
          intro ν _
          rw [smul_ite, smul_zero]
        rw [hsecond]
        by_cases hμS : μ ∈ S
        · rw [if_pos hμS, sub_self]
        · rw [if_neg hμS, hSsupp μ hμS]; simp
    intro ν
    have := hE ν
    rw [sub_eq_zero] at this
    exact this
  -- Transfer to operators.
  have horth_op : ∀ μ ν, Cop μ ∘ₗ Cop ν = if ν = μ then Cop μ else 0 := by
    intro μ ν
    rw [hCop_apply μ, hCop_apply ν, ← Matrix.toLin_mul b b b, horth_mat]
    by_cases hνμ : ν = μ
    · rw [if_pos hνμ, if_pos hνμ, ← hCop_apply]
    · rw [if_neg hνμ, if_neg hνμ, map_zero]
  have hsum_op : ∑ μ ∈ S, Cop μ = LinearMap.id := by
    simp_rw [hCop_apply]
    rw [← map_sum, hCmat_sum, Matrix.toLin_one]
  -- `T(s)` in operator form.
  have hTop : ∀ s : Fin N → kˣ, M.ρ (RepresentationTheory.UnitTupleActions.unitTupleElement k N s) = ∑ μ ∈ S, w s μ • Cop μ := by
    intro s
    have heq := congrArg (Matrix.toLin b b) (hTmat s)
    rw [Matrix.toLin_toMatrix, map_sum] at heq
    rw [heq]
    apply Finset.sum_congr rfl
    intro μ _
    rw [map_smul, hCop_apply]
  -- range Cop μ ≤ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace μ.
  have hrange : ∀ μ : Fin N →₀ ℕ,
      LinearMap.range (Cop μ) ≤ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) := by
    intro μ x hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
    rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace, Submodule.mem_iInf]
    intro i
    rw [Submodule.mem_iInf]
    intro t
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
    rw [coordinateUnit_eq_diagonalUnitMatrix_update, hTop, LinearMap.sum_apply]
    have hcollapse : ∑ ν ∈ S, (w (Function.update (1 : Fin N → kˣ) i t) ν • Cop ν) (Cop μ v)
        = if μ ∈ S then
            w (Function.update (1 : Fin N → kˣ) i t) μ • Cop μ v
          else 0 := by
      rw [← Finset.sum_ite_eq' S μ
        (fun ν => w (Function.update (1 : Fin N → kˣ) i t) ν • Cop μ v)]
      apply Finset.sum_congr rfl
      intro ν _
      rw [LinearMap.smul_apply, ← LinearMap.comp_apply, horth_op]
      by_cases hνμ : ν = μ
      · subst hνμ; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hνμ, if_neg (by simpa [eq_comm] using hνμ), LinearMap.zero_apply, smul_zero]
    rw [hcollapse]
    have hwval : w (Function.update (1 : Fin N → kˣ) i t) μ = (t : k) ^ μ i := by
      rw [hw_apply, Finset.prod_eq_single i]
      · rw [Function.update_self]
      · intro j _ hj
        rw [Function.update_of_ne hj]; simp
      · intro hi; exact absurd (Finset.mem_univ i) hi
    by_cases hμS : μ ∈ S
    · rw [if_pos hμS, hwval]
    · rw [if_neg hμS, hCop_apply, hSsupp μ hμS, map_zero, LinearMap.zero_apply, smul_zero]
  -- Conclude saturation.
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ μ ∈ S, Cop μ v := by
    have heq := congrArg (fun f => f v) hsum_op
    rw [LinearMap.sum_apply, LinearMap.id_apply] at heq
    exact heq.symm
  rw [hv]
  apply Submodule.sum_mem
  intro μ _
  exact Submodule.mem_iSup_of_mem μ (hrange μ ⟨v, rfl⟩)

end RepresentationTheory.GeneralLinearGroup.DiagonalAction
