/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute



open MvPolynomial Finset

noncomputable section

namespace RepresentationTheory.SymmetricPolynomials.Alternant




/-- The multivariate-polynomial matrix associated with a finite exponent tuple. -/
@[source_ref "Chapter5/Discussion_Schur_polynomials" (role := supporting)]
def alternantMatrix (N : ℕ) (e : Fin N → ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) ℚ) :=
  Matrix.of fun i j => (MvPolynomial.X i) ^ (e j)


/-- The natural-number exponent tuple indexed by a finite ordered type that supplies the staircase shift. -/
@[source_ref "Chapter5/Discussion_Schur_polynomials" (role := supporting)]
def staircaseExponents (N : ℕ) : Fin N → ℕ := fun j => N - 1 - j


/-- Associates a finite exponent tuple with another tuple indexed by the same finite type. -/
@[source_ref "Chapter5/Discussion_Schur_polynomials" (role := supporting)]
def addStaircase (N : ℕ) (lam : Fin N → ℕ) : Fin N → ℕ :=
  fun j => lam j + (N - 1 - j)




private noncomputable def substMap (N : ℕ) (i j : Fin N) :
    MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  MvPolynomial.aeval (fun k => if k = i then MvPolynomial.X j else MvPolynomial.X k)


private theorem alternant_subst_zero (N : ℕ) (e : Fin N → ℕ) {i j : Fin N} (hij : i ≠ j) :
    substMap N i j (alternantMatrix N e).det = 0 := by
  rw [AlgHom.map_det]
  apply Matrix.det_zero_of_row_eq hij
  funext col
  simp only [substMap, AlgHom.mapMatrix_apply, Matrix.map_apply, alternantMatrix, Matrix.of_apply,
    map_pow, MvPolynomial.aeval_X, ite_true, if_neg (Ne.symm hij)]


private theorem X_zero_sub_dvd {n : ℕ} (k : Fin n)
    (p : MvPolynomial (Fin (n + 1)) ℚ)
    (hp : MvPolynomial.aeval (fun m : Fin (n + 1) =>
      if m = (0 : Fin (n + 1)) then (MvPolynomial.X k.succ : MvPolynomial (Fin (n + 1)) ℚ)
      else MvPolynomial.X m) p = 0) :
    (MvPolynomial.X 0 - MvPolynomial.X k.succ : MvPolynomial (Fin (n + 1)) ℚ) ∣ p := by

  have hcomp : (MvPolynomial.aeval (fun m : Fin (n + 1) =>
      if m = (0 : Fin (n + 1)) then (MvPolynomial.X k.succ : MvPolynomial (Fin (n + 1)) ℚ)
      else MvPolynomial.X m) : MvPolynomial (Fin (n + 1)) ℚ →ₐ[ℚ] _) =
    ((MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1))).comp
      (((Polynomial.aeval (MvPolynomial.X k : MvPolynomial (Fin n) ℚ)).restrictScalars ℚ).comp
        (MvPolynomial.finSuccEquiv ℚ n).toAlgHom)) := by
    ext m : 1
    refine Fin.cases ?_ (fun m => ?_) m
    · simp [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        MvPolynomial.finSuccEquiv_X_zero, Polynomial.aeval_X, MvPolynomial.rename_X]
    · simp [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        MvPolynomial.finSuccEquiv_X_succ, Polynomial.aeval_C, MvPolynomial.rename_X,
        Fin.succ_ne_zero]

  have heval : Polynomial.aeval (MvPolynomial.X k : MvPolynomial (Fin n) ℚ)
      (MvPolynomial.finSuccEquiv ℚ n p) = 0 := by
    have : (MvPolynomial.aeval (fun m : Fin (n + 1) =>
        if m = (0 : Fin (n + 1)) then (MvPolynomial.X k.succ : MvPolynomial (Fin (n + 1)) ℚ)
        else MvPolynomial.X m)) p = _ := congr_fun (congr_arg DFunLike.coe hcomp) p
    rw [hp] at this
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
    exact MvPolynomial.rename_injective _ (Fin.succ_injective n)
      (this.symm.trans (map_zero _).symm)

  have hdvd_poly : (Polynomial.X - Polynomial.C (MvPolynomial.X k)) ∣
      MvPolynomial.finSuccEquiv ℚ n p :=
    Polynomial.dvd_iff_isRoot.mpr heval

  obtain ⟨q, hq⟩ := hdvd_poly
  exact ⟨(MvPolynomial.finSuccEquiv ℚ n).symm q, (MvPolynomial.finSuccEquiv ℚ n).injective <| by
    rw [map_mul, AlgEquiv.apply_symm_apply,
      show MvPolynomial.finSuccEquiv ℚ n (MvPolynomial.X 0 - MvPolynomial.X k.succ) =
        Polynomial.X - Polynomial.C (MvPolynomial.X k) from by
          simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]]
    exact hq⟩


private theorem X_sub_X_dvd {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (p : MvPolynomial (Fin N) ℚ)
    (hp : substMap N i j p = 0) :
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin N) ℚ) ∣ p := by

  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩

  set σ := Equiv.swap i (0 : Fin (n + 1))

  suffices h : (MvPolynomial.X (0 : Fin (n + 1)) -
      MvPolynomial.X (σ j) : MvPolynomial (Fin (n + 1)) ℚ) ∣
      MvPolynomial.rename σ p by

    obtain ⟨q, hq⟩ := h
    refine ⟨MvPolynomial.rename σ.symm q, ?_⟩
    apply (MvPolynomial.rename_injective _ σ.injective)
    rw [map_mul, MvPolynomial.rename_rename, Equiv.self_comp_symm]
    simp only [MvPolynomial.rename_id, AlgHom.id_apply]
    rw [show MvPolynomial.rename σ (MvPolynomial.X i - MvPolynomial.X j) =
        MvPolynomial.X (0 : Fin (n + 1)) - MvPolynomial.X (σ j) from by
      simp only [map_sub, MvPolynomial.rename_X, σ, Equiv.swap_apply_left]]
    exact hq

  have hσj : σ j ≠ 0 := by
    change Equiv.swap i 0 j ≠ 0
    rcases eq_or_ne j i with rfl | hji
    · exact absurd rfl hij
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [Equiv.swap_apply_right]; exact fun h => hij (h ▸ rfl)
    · rw [Equiv.swap_apply_of_ne_of_ne hji hj0]; exact hj0

  obtain ⟨k, hk⟩ : ∃ k : Fin n, k.succ = σ j :=
    ⟨(σ j).pred hσj, Fin.succ_pred _ _⟩
  rw [← hk]

  apply X_zero_sub_dvd


  have hcomp : ((substMap (n + 1) 0 (σ j)).comp (MvPolynomial.rename σ) :
      MvPolynomial (Fin (n + 1)) ℚ →ₐ[ℚ] _) =
    (MvPolynomial.rename σ).comp (substMap (n + 1) i j) := by
    ext m : 1
    simp only [AlgHom.comp_apply, substMap, MvPolynomial.aeval_X, MvPolynomial.rename_X]
    simp only [σ, Equiv.swap_apply_def]
    split_ifs with h1 h2 h3 <;> simp_all [Equiv.swap_apply_of_ne_of_ne]

  change (substMap (n + 1) 0 k.succ) (MvPolynomial.rename σ p) = 0
  rw [show substMap (n + 1) 0 k.succ = substMap (n + 1) 0 (σ j) from by rw [← hk],
    show (substMap (n + 1) 0 (σ j)) (MvPolynomial.rename σ p) =
      ((substMap (n + 1) 0 (σ j)).comp (MvPolynomial.rename σ)) p from rfl,
    hcomp, show ((MvPolynomial.rename σ).comp (substMap (n + 1) i j)) p =
      MvPolynomial.rename σ (substMap (n + 1) i j p) from rfl, hp, map_zero]


private theorem X_sub_X_prime {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    Prime (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin N) ℚ) := by
  let φ := MvPolynomial.aeval (R := ℚ) (fun k : Fin N =>
    if k = i then (MvPolynomial.X i : MvPolynomial (Fin N) ℚ) - MvPolynomial.X j
    else MvPolynomial.X k)
  let ψ := MvPolynomial.aeval (R := ℚ) (fun k : Fin N =>
    if k = i then (MvPolynomial.X i : MvPolynomial (Fin N) ℚ) + MvPolynomial.X j
    else MvPolynomial.X k)
  have hφψ : φ.comp ψ = AlgHom.id ℚ _ := by
    ext k : 1; simp only [φ, ψ, AlgHom.comp_apply, MvPolynomial.aeval_X]
    split_ifs with h <;> simp_all [hij.symm]
  have hψφ : ψ.comp φ = AlgHom.id ℚ _ := by
    ext k : 1; simp only [φ, ψ, AlgHom.comp_apply, MvPolynomial.aeval_X]
    split_ifs with h <;> simp_all [hij.symm]
  let e : MvPolynomial (Fin N) ℚ ≃ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
    AlgEquiv.ofAlgHom φ ψ hφψ hψφ
  rw [show (MvPolynomial.X i : MvPolynomial (Fin N) ℚ) - MvPolynomial.X j = e (MvPolynomial.X i)
    from by change _ = φ (MvPolynomial.X i); simp [φ]]
  exact (MulEquiv.prime_iff e.toMulEquiv).mpr (MvPolynomial.X_prime (i := i))


private theorem X_sub_X_not_associated {N : ℕ} {i₁ j₁ i₂ j₂ : Fin N}
    (h₁ : i₁ < j₁) (h₂ : i₂ < j₂) (hne : (i₁, j₁) ≠ (i₂, j₂)) :
    ¬Associated (MvPolynomial.X j₁ - MvPolynomial.X i₁ : MvPolynomial (Fin N) ℚ)
      (MvPolynomial.X j₂ - MvPolynomial.X i₂) := by
  intro ⟨u, hu⟩

  have hev₁ := congr_arg
    (MvPolynomial.eval (fun k : Fin N => if k = j₁ then (1 : ℚ) else 0)) hu
  simp only [map_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X, ite_true,
    if_neg h₁.ne, sub_zero] at hev₁

  have hev₂ := congr_arg
    (MvPolynomial.eval (fun k : Fin N => if k = i₁ then (1 : ℚ) else 0)) hu
  simp only [map_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X, ite_true,
    if_neg h₁.ne', zero_sub] at hev₂

  have hu₁ : (MvPolynomial.eval (fun k : Fin N => if k = j₁ then (1 : ℚ) else 0)) ↑u ≠ 0 :=
    (Units.map (MvPolynomial.eval (R := ℚ)
      (fun k : Fin N => if k = j₁ then 1 else 0)).toMonoidHom u).isUnit.ne_zero
  have hu₂ : (MvPolynomial.eval (fun k : Fin N => if k = i₁ then (1 : ℚ) else 0)) ↑u ≠ 0 :=
    (Units.map (MvPolynomial.eval (R := ℚ)
      (fun k : Fin N => if k = i₁ then 1 else 0)).toMonoidHom u).isUnit.ne_zero
  rw [one_mul] at hev₁
  rw [neg_one_mul] at hev₂
  by_cases hj : j₂ = j₁
  · subst hj; simp only [if_neg h₂.ne, sub_zero] at hev₁
    by_cases hi : i₂ = i₁; · subst hi; exact hne rfl
    · simp only [if_neg h₁.ne', if_neg hi, sub_zero] at hev₂
      exact hu₂ (neg_eq_zero.mp hev₂)
  · by_cases hi₂j₁ : i₂ = j₁
    · subst hi₂j₁; simp only [if_neg hj, zero_sub] at hev₁
      by_cases hj₂i₁ : j₂ = i₁; · subst hj₂i₁; exact absurd h₂ (by omega)
      · simp only [if_neg hj₂i₁, if_neg h₁.ne'] at hev₂
        simp only [sub_zero] at hev₂; exact hu₂ (neg_eq_zero.mp hev₂)
    · simp only [if_neg hj, if_neg hi₂j₁, sub_zero] at hev₁; exact hu₁ hev₁


private theorem X_sub_X_isRelPrime {N : ℕ} {i₁ j₁ i₂ j₂ : Fin N}
    (h₁ : i₁ < j₁) (h₂ : i₂ < j₂) (hne : (i₁, j₁) ≠ (i₂, j₂)) :
    IsRelPrime (MvPolynomial.X j₁ - MvPolynomial.X i₁ : MvPolynomial (Fin N) ℚ)
      (MvPolynomial.X j₂ - MvPolynomial.X i₂) := by
  letI : GCDMonoid (MvPolynomial (Fin N) ℚ) :=
    UniqueFactorizationMonoid.toGCDMonoid _
  exact (X_sub_X_prime h₁.ne').irreducible.isRelPrime_iff_not_dvd.mpr
    fun hdvd => X_sub_X_not_associated h₁ h₂ hne
      ((X_sub_X_prime h₁.ne').associated_of_dvd (X_sub_X_prime h₂.ne') hdvd)

set_option maxHeartbeats 8000000 in


private theorem prod_dvd_alternant (N : ℕ) (e : Fin N → ℕ) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ∣
      (alternantMatrix N e).det := by
  letI : DecompositionMonoid (MvPolynomial (Fin N) ℚ) :=
    UniqueFactorizationMonoid.instDecompositionMonoid
  apply Fintype.prod_dvd_of_isRelPrime
  ·
    intro i₁ i₂ hi
    apply IsRelPrime.prod_left_iff.mpr; intro j₁ hj₁
    apply IsRelPrime.prod_right_iff.mpr; intro j₂ hj₂
    simp only [Finset.mem_Ioi] at hj₁ hj₂
    exact X_sub_X_isRelPrime hj₁ hj₂ (by intro h; exact hi (Prod.mk.inj h).1)
  ·
    intro i
    apply Finset.prod_dvd_of_isRelPrime
    · intro j₁ hj₁ j₂ hj₂ hjne
      simp only [Finset.coe_Ioi, Set.mem_Ioi] at hj₁ hj₂
      rw [Function.onFun]
      exact X_sub_X_isRelPrime hj₁ hj₂ (by intro h; exact hjne (Prod.mk.inj h).2)
    · intro j hj
      simp only [Finset.mem_Ioi] at hj
      exact X_sub_X_dvd (Fin.ne_of_gt hj) _ (alternant_subst_zero N e (Fin.ne_of_gt hj))


private theorem alternant_det_associated_prod (N : ℕ) :
    Associated (alternantMatrix N (staircaseExponents N)).det
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) := by
  have h1 : alternantMatrix N (staircaseExponents N) =
      (Matrix.vandermonde (MvPolynomial.X : Fin N → MvPolynomial (Fin N) ℚ)).submatrix
        id (@Fin.revPerm N) := by
    ext i j
    simp only [alternantMatrix, Matrix.vandermonde, staircaseExponents, Matrix.of_apply,
      Matrix.submatrix_apply, id, Fin.revPerm_apply]
    congr 2
    simp only [Fin.rev, Fin.val_mk]
    omega
  rw [h1, Matrix.det_permute', Matrix.det_vandermonde]
  have hu : IsUnit (↑↑(@Fin.revPerm N).sign : MvPolynomial (Fin N) ℚ) :=
    (Units.map (algebraMap ℤ (MvPolynomial (Fin N) ℚ)).toMonoidHom
      (@Fin.revPerm N).sign).isUnit
  exact (associated_isUnit_mul_left_iff hu).mpr (Associated.refl _)


private theorem vandermonde_dvd_alternant (N : ℕ) (e : Fin N → ℕ) :
    (alternantMatrix N (staircaseExponents N)).det ∣ (alternantMatrix N e).det :=
  (alternant_det_associated_prod N).dvd_iff_dvd_left.mpr (prod_dvd_alternant N e)


/-- The multivariate rational polynomial associated with a finite tuple of natural numbers. -/
@[source_ref "Chapter5/Discussion_Schur_polynomials" (role := supporting)]
noncomputable def partitionPolynomial (N : ℕ) (lam : Fin N → ℕ) :
    MvPolynomial (Fin N) ℚ :=
  (vandermonde_dvd_alternant N (addStaircase N lam)).choose


/-- Multiplying a partition polynomial by the staircase alternant determinant gives the alternant determinant for the staircase-shifted exponents. -/
@[source_ref "Chapter5/Discussion_Schur_polynomials" (role := primary)]
theorem partitionPolynomial_mul_det_staircase (N : ℕ) (lam : Fin N → ℕ) :
    partitionPolynomial N lam * (alternantMatrix N (staircaseExponents N)).det =
      (alternantMatrix N (addStaircase N lam)).det := by
  have h := (vandermonde_dvd_alternant N (addStaircase N lam)).choose_spec

  rw [partitionPolynomial, mul_comm]
  exact h.symm


/-- Antitone tuples of natural numbers indexed by `Fin N` with prescribed total `n`. -/
structure FinPartition (N n : ℕ) where
  
  /-- Returns the entry of a finite partition tuple at a given finite index. -/
  parts : Fin N → ℕ
  
  /-- The entries of a finite partition tuple are antitone. -/
  parts_antitone : Antitone parts
  
  /-- The sum of all entries of a finite partition tuple is its prescribed total. -/
  sum_parts : ∑ i, parts i = n


/-- The rational coefficient assigned to a finite partition tuple and a natural-number partition. -/
@[source_ref "Chapter5/Discussion_hook_length_derivation" (role := supporting)]
noncomputable def partitionExpansionCoeff {n : ℕ} (N : ℕ) (lam : FinPartition N n)
    (μ : n.Partition) : ℚ :=
  MvPolynomial.coeff
    (Finsupp.equivFunOnFinite.symm (addStaircase N lam.parts))
    ((alternantMatrix N (staircaseExponents N)).det * MvPolynomial.psumPart (Fin N) ℚ μ)




/-- Provides decidable equality for finite partition tuples. -/
instance instDecidableEqFinPartition {N n : ℕ} : DecidableEq (FinPartition N n) :=
  fun a b => decidable_of_iff (a.parts = b.parts) ⟨
    fun h => by cases a; cases b; simp_all,
    fun h => by subst h; rfl⟩


/-- Provides a finite type structure on finite partition tuples with fixed bounds and total. -/
noncomputable instance instFintypeFinPartition {N n : ℕ} :
    Fintype (FinPartition N n) := by
  classical
  exact Fintype.ofInjective
    (fun p : FinPartition N n => fun i =>
      (⟨p.parts i, Nat.lt_succ_of_le (le_trans
        (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
        (le_of_eq p.sum_parts))⟩ : Fin (n + 1)))
    (fun a b h => by
      cases a; cases b; simp only [FinPartition.mk.injEq]
      funext i; exact congrArg Fin.val (congrFun h i))


/-- Renaming the variables of an alternant determinant by a permutation multiplies it by the permutation sign. -/
theorem rename_det_alternantMatrix {N : ℕ} (e : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) :
    (MvPolynomial.rename σ) (alternantMatrix N e).det =
      Equiv.Perm.sign σ • (alternantMatrix N e).det := by
  rw [AlgHom.map_det]
  have hmat : (MvPolynomial.rename σ).mapMatrix (alternantMatrix N e) =
      (alternantMatrix N e).submatrix σ id := by
    apply Matrix.ext; intro i j
    change (MvPolynomial.rename σ) ((alternantMatrix N e) i j) =
      (alternantMatrix N e) (σ i) j
    simp [alternantMatrix, Matrix.of_apply, map_pow, MvPolynomial.rename_X]
  rw [hmat, Matrix.det_permute]
  simp [Units.smul_def]






private lemma coeff_sign_smul {N : ℕ} (σ : Equiv.Perm (Fin N)) (m : Fin N →₀ ℕ)
    (p : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.coeff m (Equiv.Perm.sign σ • p)
      = (Equiv.Perm.sign σ : ℤ) • MvPolynomial.coeff m p := by
  rw [Units.smul_def]
  exact map_zsmul (MvPolynomial.lcoeff ℚ m) _ p


private lemma sign_smul_sub {N : ℕ} (σ : Equiv.Perm (Fin N)) (a b : MvPolynomial (Fin N) ℚ) :
    Equiv.Perm.sign σ • (a - b)
      = Equiv.Perm.sign σ • a - Equiv.Perm.sign σ • b := by
  simp only [Units.smul_def]
  exact smul_sub _ a b


private lemma sign_smul_monomial {N : ℕ} (σ : Equiv.Perm (Fin N)) (d : Fin N →₀ ℕ) :
    Equiv.Perm.sign σ • MvPolynomial.monomial d (1 : ℚ)
      = MvPolynomial.monomial d ((Equiv.Perm.sign σ : ℤ) : ℚ) := by
  ext m'
  rw [coeff_sign_smul, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  split_ifs <;> simp [zsmul_eq_mul]


/-- A strictly monotone permutation of a finite ordered type is the identity permutation. -/
lemma perm_eq_one_of_strictMono {N : ℕ} {σ : Equiv.Perm (Fin N)}
    (h : StrictMono (⇑σ : Fin N → Fin N)) : σ = 1 := by
  rcases N with _ | n
  · exact Subsingleton.elim _ _
  · have hle : ∀ j : Fin (n + 1), j ≤ σ j := by
      intro j; induction j using Fin.inductionOn with
      | zero => exact Fin.zero_le _
      | succ k ih =>
          apply Fin.le_def.mpr
          have h1 : (σ k.castSucc).val < (σ k.succ).val :=
            Fin.lt_def.mp (h (by simp [Fin.lt_def]))
          have h2 := Fin.le_def.mp ih
          have h3 : k.succ.val = k.castSucc.val + 1 := rfl
          omega
    by_contra hne
    obtain ⟨i, hi⟩ := not_forall.mp
      (mt (fun heq => Equiv.ext (fun j => Eq.symm (heq j))) hne)
    linarith [Finset.sum_lt_sum (g := fun j => (σ j : ℕ)) (fun j _ => hle j)
      ⟨i, Finset.mem_univ _, Fin.lt_def.mp (lt_of_le_of_ne (hle i) hi)⟩,
      Fintype.sum_equiv σ (fun j => ((σ j) : ℕ)) (fun j => (j : ℕ)) (fun _ => rfl)]


/-- The product of the variables raised to a finite exponent tuple equals the corresponding monomial with coefficient one. -/
lemma prod_X_pow_eq_monomial {N : ℕ} (f : Fin N → ℕ) :
    ∏ i : Fin N, (X i : MvPolynomial (Fin N) ℚ) ^ f i =
    monomial (Finsupp.equivFunOnFinite.symm f) 1 := by
  set s := Finsupp.equivFunOnFinite.symm f
  rw [show ∏ i : Fin N, (X i : MvPolynomial (Fin N) ℚ) ^ f i = ∏ i, X i ^ s i from rfl,
    ← MvPolynomial.prod_X_pow_eq_monomial]; symm
  exact Finset.prod_subset (Finset.subset_univ _)
    fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, pow_zero]


/-- A partition power-sum polynomial is invariant under permutations of its variables. -/
theorem psumPart_isSymmetric {n : ℕ} (N : ℕ) (μ : n.Partition) :
    (MvPolynomial.psumPart (Fin N) ℚ μ).IsSymmetric := by
  unfold MvPolynomial.psumPart
  induction μ.parts using Multiset.induction with
  | empty => exact MvPolynomial.IsSymmetric.one
  | cons a s ih => rw [Multiset.map_cons, Multiset.prod_cons]
                   exact (MvPolynomial.psum_isSymmetric _ ℚ a).mul ih


/-- A coefficient of an alternating polynomial vanishes when its exponent assigns the same value to two distinct variables. -/
theorem coeff_eq_zero_of_alternating_of_eq {N : ℕ}
    (p : MvPolynomial (Fin N) ℚ)
    (hp : ∀ σ : Equiv.Perm (Fin N), MvPolynomial.rename σ p = Equiv.Perm.sign σ • p)
    (d : (Fin N) →₀ ℕ) {i j : Fin N} (hij : i ≠ j) (hd : d i = d j) :
    MvPolynomial.coeff d p = 0 := by
  have h1 := hp (Equiv.swap i j); rw [Equiv.Perm.sign_swap hij] at h1
  have h3 := MvPolynomial.coeff_rename_mapDomain (⇑(Equiv.swap i j))
    (Equiv.swap i j).injective p d
  rw [show Finsupp.mapDomain (⇑(Equiv.swap i j)) d = d from by
    have hsymm : (Equiv.swap i j).symm = Equiv.swap i j := Equiv.symm_swap i j
    ext k; rw [Finsupp.mapDomain_equiv_apply, hsymm, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; exact hd.symm
    · subst h2; exact hd
    · rfl,
    h1] at h3
  simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul,
    MvPolynomial.coeff_neg] at h3; linarith


/-- Adding staircase exponents to the entries of a finite partition tuple produces a strictly antitone tuple. -/
theorem addStaircase_strictAnti {N n : ℕ} (lam : FinPartition N n) :
    StrictAnti (addStaircase N lam.parts) := by
  intro i j hij; simp only [addStaircase]; have := lam.parts_antitone (le_of_lt hij); omega


/-- For strictly antitone exponent tuples, the indicated coefficient of an alternant determinant is one exactly when the tuples agree and zero otherwise. -/
theorem coeff_det_alternantMatrix_of_strictAnti {N : ℕ}
    {e e' : Fin N → ℕ} (he : StrictAnti e) (he' : StrictAnti e') :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e') (alternantMatrix N e).det =
    if e = e' then 1 else 0 := by
  rw [Matrix.det_apply]
  simp only [MvPolynomial.coeff_sum, coeff_sign_smul]
  simp_rw [show ∀ σ : Equiv.Perm (Fin N), ∏ j, alternantMatrix N e (σ j) j =
      monomial (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) 1 from fun σ => by
    rw [show ∏ j, alternantMatrix N e (σ j) j = ∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ e j
      from rfl, show ∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ e j =
        ∏ i, X i ^ (e (σ.symm i)) from Fintype.prod_equiv σ _ _ (fun _ => by simp)]
    exact prod_X_pow_eq_monomial _]
  simp only [MvPolynomial.coeff_monomial]
  have key : ∀ σ : Equiv.Perm (Fin N),
      (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm) = Finsupp.equivFunOnFinite.symm e') ↔
      (e ∘ ⇑σ.symm = e') := fun σ => Finsupp.equivFunOnFinite.symm.injective.eq_iff
  have unique : ∀ σ : Equiv.Perm (Fin N), e ∘ ⇑σ.symm = e' → e = e' ∧ σ = 1 := by
    intro σ h
    have hmono : StrictMono (⇑σ.symm : Fin N → Fin N) := by
      intro a b hab
      have hgt := (congr_fun h a) ▸ (congr_fun h b) ▸ he' hab
      by_contra h_not_lt; push Not at h_not_lt
      rcases h_not_lt.eq_or_lt with heq | hlt
      · exact absurd hgt (not_lt.mpr (le_of_eq (congr_arg e heq.symm)))
      · exact absurd hgt (not_lt.mpr (le_of_lt (he hlt)))
    exact ⟨by rw [← h]; simp [show σ.symm = 1 from perm_eq_one_of_strictMono hmono],

           by rw [← σ.symm_symm, perm_eq_one_of_strictMono hmono]; rfl⟩
  split_ifs with heq
  · rw [Finset.sum_eq_single 1]
    ·
      subst heq
      have hident : Finsupp.equivFunOnFinite.symm (e ∘ ⇑(1 : Equiv.Perm (Fin N)).symm) =
          Finsupp.equivFunOnFinite.symm e := (key 1).2 (by rfl)
      rw [if_pos hident]
      simp
    · intro σ _ hne; simp only [key]; split_ifs with h
      · exact absurd (unique σ h).2 hne
      · exact smul_zero _
    · intro h; exact absurd (Finset.mem_univ _) h
  · exact Finset.sum_eq_zero fun σ _ => by
      simp only [key]; split_ifs with h
      · exact absurd (unique σ h).1 heq
      · exact smul_zero _


/-- An alternating multivariate polynomial is zero when every coefficient at a strictly antitone exponent tuple vanishes. -/
theorem eq_zero_of_alternating_coeff_strictAnti_eq_zero {N : ℕ} (p : MvPolynomial (Fin N) ℚ)
    (hp : ∀ σ : Equiv.Perm (Fin N), MvPolynomial.rename σ p = Equiv.Perm.sign σ • p)
    (hc : ∀ e : Fin N → ℕ, StrictAnti e →
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) p = 0) :
    p = 0 := by
  ext d; simp only [MvPolynomial.coeff_zero]
  set f := Finsupp.equivFunOnFinite d
  by_cases hinj : Function.Injective f
  · obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin N), StrictAnti (f ∘ ⇑σ) :=
      ⟨Tuple.sort (OrderDual.toDual ∘ f), fun a b hab =>
        (Tuple.monotone_sort _).strictMono_of_injective
          (OrderDual.toDual.injective.comp hinj |>.comp (Tuple.sort _).injective) hab⟩
    have h1 := MvPolynomial.coeff_rename_mapDomain (⇑σ.symm) σ.symm.injective p d
    rw [show Finsupp.mapDomain (⇑σ.symm) d = Finsupp.equivFunOnFinite.symm (f ∘ ⇑σ) from by
      ext i; simp [Finsupp.mapDomain_equiv_apply, f, Finsupp.equivFunOnFinite], hp σ.symm] at h1
    rw [show MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (f ∘ ⇑σ))
          (Equiv.Perm.sign σ.symm • p) = 0 from by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h, hc _ hσ]] at h1
    exact h1.symm
  · simp only [Function.Injective] at hinj; push Not at hinj
    obtain ⟨i, j, hij_val, hij_ne⟩ := hinj
    exact coeff_eq_zero_of_alternating_of_eq p hp d hij_ne hij_val


/-- Every strictly antitone natural-valued tuple is bounded below pointwise by the descending staircase tuple. -/
theorem staircase_le_of_strictAnti {N : ℕ} {e : Fin N → ℕ} (he : StrictAnti e) (j : Fin N) :
    N - 1 - (j : ℕ) ≤ e j := by
  suffices ∀ m : ℕ, ∀ j : Fin N, m = N - 1 - (j : ℕ) → m ≤ e j by exact this _ j rfl
  intro m; induction m with
  | zero => intro j _; omega
  | succ m ih =>
    intro j hj; have hj1 : (j : ℕ) + 1 < N := by omega
    have := ih ⟨(j : ℕ) + 1, hj1⟩ (by simp; omega)
    have := he (show j < (⟨(j : ℕ) + 1, hj1⟩ : Fin N) from by simp [Fin.lt_def]); omega


private theorem strictAnti_gap {N : ℕ} {e : Fin N → ℕ} (he : StrictAnti e)
    {i j : Fin N} (hij : i ≤ j) : e j + ((j : ℕ) - (i : ℕ)) ≤ e i := by
  suffices ∀ d : ℕ, ∀ i j : Fin N, d = (j : ℕ) - (i : ℕ) → i ≤ j → e j + d ≤ e i by
    exact this _ i j rfl hij
  intro d; induction d with
  | zero => intro i j hd hij; have : i = j := Fin.ext (by omega); subst this; omega
  | succ d ih =>
    intro i j hd hij; let j' : Fin N := ⟨(j : ℕ) - 1, by omega⟩
    have := ih i j' (by simp [j']; omega) (by simp [j', Fin.le_iff_val_le_val]; omega)
    have := he (show j' < j from by simp [j', Fin.lt_def]; omega); omega


/-- The determinant of an alternant matrix is homogeneous of degree equal to the sum of its exponents. -/
theorem det_alternantMatrix_isHomogeneous {N : ℕ} (e : Fin N → ℕ) :
    (alternantMatrix N e).det.IsHomogeneous (∑ j : Fin N, e j) := by
  rw [Matrix.det_apply, show ∑ j : Fin N, e j = ∑ j : Fin N, 1 * e j by simp]
  apply MvPolynomial.IsHomogeneous.sum; intro σ _ d hd


  rw [coeff_sign_smul] at hd
  have hne : MvPolynomial.coeff d (∏ i, alternantMatrix N e (σ i) i) ≠ 0 :=
    fun hc => hd (by rw [hc, smul_zero])
  exact (MvPolynomial.IsHomogeneous.prod _ _ _ (fun j _ =>
    (MvPolynomial.isHomogeneous_X ℚ (σ j)).pow (e j))) hne


/-- The partition power-sum polynomial is homogeneous of degree equal to the partitioned natural number. -/
theorem psumPart_isHomogeneous {n : ℕ} (N : ℕ) (μ : n.Partition) :
    (MvPolynomial.psumPart (Fin N) ℚ μ).IsHomogeneous n := by
  unfold MvPolynomial.psumPart
  suffices h : (Multiset.map (psum (Fin N) ℚ) μ.parts).prod.IsHomogeneous μ.parts.sum by
    rwa [μ.parts_sum] at h
  induction μ.parts using Multiset.induction with
  | empty => simpa using MvPolynomial.isHomogeneous_one (Fin N) ℚ
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact ((show (∑ i : Fin N, X i ^ a).IsHomogeneous a from by
      apply IsHomogeneous.sum; intro i _
      convert (MvPolynomial.isHomogeneous_X ℚ i).pow a using 1; ring)).mul ih


/-- A strictly antitone exponent tuple with the required total is obtained by adding the staircase exponents to the entries of a finite partition tuple. -/
theorem exists_finPartition_addStaircase_eq {N n : ℕ}
    (e : Fin N → ℕ) (he : StrictAnti e)
    (hsum : ∑ j : Fin N, e j = (∑ j : Fin N, staircaseExponents N j) + n) :
    ∃ lam : FinPartition N n, addStaircase N lam.parts = e := by
  set parts : Fin N → ℕ := fun j => e j - (N - 1 - ↑j)
  have hge := staircase_le_of_strictAnti he
  refine ⟨⟨parts, ?_, ?_⟩, ?_⟩
  · intro i j hij; simp only [parts]; have := strictAnti_gap he hij; omega
  · have h1 : ∑ i : Fin N, (parts i + (N - 1 - ↑i)) = ∑ i : Fin N, e i :=
      Finset.sum_congr rfl fun j _ => by simp only [parts]; exact Nat.sub_add_cancel (hge j)
    rw [Finset.sum_add_distrib] at h1
    simp only [staircaseExponents] at hsum; omega
  · funext j; simp only [addStaircase, parts]; exact Nat.sub_add_cancel (hge j)


/-- Expresses a partition power-sum polynomial as a finite sum of partition polynomials weighted by expansion coefficients. -/
@[source_ref "Chapter5/Proposition5.21.1" (role := supporting)]
theorem psumPart_eq_sum_partitionPolynomial
    {n : ℕ} (N : ℕ) (μ : n.Partition) :
    (MvPolynomial.psumPart (Fin N) ℚ μ : MvPolynomial (Fin N) ℚ) =
      ∑ lam : FinPartition N n,
        (partitionExpansionCoeff N lam μ : ℚ) • partitionPolynomial N lam.parts := by

  have hΔ : (alternantMatrix N (staircaseExponents N)).det ≠ 0 := by
    obtain ⟨u, hu⟩ := alternant_det_associated_prod N
    intro h
    have hprod : ∏ i : Fin N, ∏ j ∈ Ioi i,
        (X j - X i : MvPolynomial (Fin N) ℚ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ =>
        Finset.prod_ne_zero_iff.mpr fun j hj =>
          (X_sub_X_prime (mem_Ioi.mp hj).ne').ne_zero
    exact hprod (by rw [← hu, h, zero_mul])
  apply mul_left_cancel₀ hΔ

  rw [Finset.mul_sum]
  simp_rw [Algebra.mul_smul_comm,
    mul_comm (alternantMatrix N (staircaseExponents N)).det (partitionPolynomial _ _),
    partitionPolynomial_mul_det_staircase]


  simp only [partitionExpansionCoeff]
  rw [← sub_eq_zero]
  apply eq_zero_of_alternating_coeff_strictAnti_eq_zero
  ·

    intro σ
    rw [map_sub, sign_smul_sub]
    congr 1
    · rw [map_mul, rename_det_alternantMatrix, (psumPart_isSymmetric N μ) σ, smul_mul_assoc]
    ·
      trans ∑ lam : FinPartition N n, Equiv.Perm.sign σ •
        (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (addStaircase N lam.parts))
          ((alternantMatrix N (staircaseExponents N)).det * psumPart (Fin N) ℚ μ) •
         (alternantMatrix N (addStaircase N lam.parts)).det)
      · rw [map_sum]; apply Finset.sum_congr rfl; intro lam _
        rw [AlgHom.map_smul_of_tower, rename_det_alternantMatrix, smul_comm]
      · exact (Finset.smul_sum ..).symm
  ·
    intro e he
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      smul_eq_mul, sub_eq_zero]
    simp_rw [coeff_det_alternantMatrix_of_strictAnti (addStaircase_strictAnti _) he, mul_ite, mul_one, mul_zero]
    have hsub : ∀ lam : FinPartition N n,
        (if addStaircase N lam.parts = e
         then MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (addStaircase N lam.parts))
                ((alternantMatrix N (staircaseExponents N)).det * psumPart (Fin N) ℚ μ) else 0) =
        if addStaircase N lam.parts = e
        then MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
              ((alternantMatrix N (staircaseExponents N)).det * psumPart (Fin N) ℚ μ) else 0 :=
      fun lam => by split_ifs with h <;> [rw [h]; rfl]
    simp_rw [hsub]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
    set filt := Finset.univ.filter (fun lam : FinPartition N n =>
      addStaircase N lam.parts = e)
    have hle : filt.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have : a.parts = b.parts := by
        funext j; have := congr_fun (ha'.trans hb'.symm) j; simp [addStaircase] at this; omega
      cases a; cases b; simp_all
    rcases Nat.eq_zero_or_pos filt.card with hcard | hcard
    ·
      rw [hcard, zero_nsmul]; symm
      have hne : ∀ lam : FinPartition N n, addStaircase N lam.parts ≠ e := by
        intro lam hlam
        have hmem : lam ∈ filt := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlam⟩
        rw [Finset.card_eq_zero.mp hcard] at hmem
        exact absurd hmem (by simp)
      by_contra h
      have h' : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
          ((alternantMatrix N (staircaseExponents N)).det * psumPart (Fin N) ℚ μ) ≠ 0 := by
        intro heq; exact h heq.symm
      have hF := (det_alternantMatrix_isHomogeneous (staircaseExponents N)).mul (psumPart_isHomogeneous N μ)
      have hd := hF h'
      have hweight : Finsupp.weight (1 : Fin N → ℕ) (Finsupp.equivFunOnFinite.symm e) =
          ∑ j : Fin N, e j := by
        simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      rw [hweight] at hd
      obtain ⟨lam, hlam⟩ := exists_finPartition_addStaircase_eq e he (by exact_mod_cast hd)
      exact hne lam hlam
    ·
      have : filt.card = 1 := by omega
      rw [this, one_nsmul]


/-- Gives the expansion of a partition power sum in the finite partition-polynomial family. -/
alias psumPart_expansion := psumPart_eq_sum_partitionPolynomial



section LeadingTerm

open Finsupp
open scoped MonomialOrder


/-- Permuting a strictly antitone exponent tuple by an inverse permutation does not increase its degree-lexicographic encoding. -/
theorem toDegLex_comp_perm_symm_le {N : ℕ} {e : Fin N → ℕ} (he : StrictAnti e)
    (σ : Equiv.Perm (Fin N)) :
    toDegLex (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) ≤
      toDegLex (Finsupp.equivFunOnFinite.symm e) := by
  classical
  set π : Equiv.Perm (Fin N) := σ.symm with hπ
  set a : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm (e ∘ ⇑π) with ha
  set b : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm e with hb
  have hav : ∀ i, a i = e (π i) := fun i => by rw [ha]; rfl
  have hbv : ∀ i, b i = e i := fun i => by rw [hb]; rfl
  have hdeg : a.degree = b.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    simp only [hav, hbv]
    exact Equiv.sum_comp π e
  rw [DegLex.le_iff]
  simp only [ofDegLex_toDegLex]
  refine Or.inr ⟨hdeg, ?_⟩
  by_cases hid : ∀ i, π i = i
  · have hab : a = b := by ext i; rw [hav, hbv, hid i]
    rw [hab]
  · apply le_of_lt
    have hne : (Finset.univ.filter (fun i => π i ≠ i)).Nonempty := by
      push Not at hid; obtain ⟨i, hi⟩ := hid
      exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩
    set i₀ := (Finset.univ.filter (fun i => π i ≠ i)).min' hne with hi0
    have hi0mem : i₀ ∈ Finset.univ.filter (fun i => π i ≠ i) := Finset.min'_mem _ hne
    rw [Finset.mem_filter] at hi0mem
    have hmove : π i₀ ≠ i₀ := hi0mem.2
    have hfix : ∀ j, j < i₀ → π j = j := by
      intro j hj
      by_contra hjm
      have : i₀ ≤ j :=
        Finset.min'_le _ j (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hjm)
      exact absurd hj (not_lt.mpr this)
    have hgt : i₀ < π i₀ := by
      rcases lt_trichotomy (π i₀) i₀ with h | h | h
      · exact absurd (π.injective (hfix (π i₀) h)) hmove
      · exact absurd h hmove
      · exact h
    rw [Lex.lt_iff]
    refine ⟨i₀, fun j hj => ?_, ?_⟩
    · change a j = b j
      rw [hav, hbv, hfix j hj]
    · change a i₀ < b i₀
      rw [hav, hbv]; exact he hgt


/-- For strictly antitone exponents, the degree-lexicographic degree of the alternant determinant is the corresponding finitely supported exponent. -/
theorem degLex_degree_det_alternantMatrix {N : ℕ} {e : Fin N → ℕ} (he : StrictAnti e) :
    (MonomialOrder.degLex : MonomialOrder (Fin N)).degree (alternantMatrix N e).det =
      Finsupp.equivFunOnFinite.symm e := by
  classical
  set m : MonomialOrder (Fin N) := MonomialOrder.degLex with hm

  have hmono : ∀ σ : Equiv.Perm (Fin N), (∏ j, alternantMatrix N e (σ j) j)
      = monomial (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) (1 : ℚ) := fun σ => by
    rw [show (∏ j, alternantMatrix N e (σ j) j)
          = ∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ e j from rfl,
        show (∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ e j)
          = ∏ i, X i ^ (e (σ.symm i)) from Fintype.prod_equiv σ _ _ (fun _ => by simp)]
    exact prod_X_pow_eq_monomial _
  have hdet : (alternantMatrix N e).det =
      ∑ σ : Equiv.Perm (Fin N),
        Equiv.Perm.sign σ • monomial (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) (1 : ℚ) := by
    rw [Matrix.det_apply]
    exact Finset.sum_congr rfl (fun σ _ => by rw [hmono σ])

  have hterm : ∀ σ : Equiv.Perm (Fin N),
      m.degree (Equiv.Perm.sign σ •
          monomial (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) (1 : ℚ))
        = Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm) := by
    intro σ


    have hc : (((Equiv.Perm.sign σ : ℤ) : ℚ)) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] <;> simp
    rw [sign_smul_monomial, MonomialOrder.degree_monomial, if_neg hc]

  have hlower : Finsupp.equivFunOnFinite.symm e ≼[m] m.degree (alternantMatrix N e).det := by
    apply m.le_degree
    rw [MvPolynomial.mem_support_iff, coeff_det_alternantMatrix_of_strictAnti he he, if_pos rfl]
    exact one_ne_zero

  have hupper : m.degree (alternantMatrix N e).det ≼[m] Finsupp.equivFunOnFinite.symm e := by
    rw [hdet]
    refine le_trans m.degree_sum_le (Finset.sup_le (fun σ _ => ?_))
    rw [hterm σ]
    exact toDegLex_comp_perm_symm_le he σ
  exact m.toSyn.injective (le_antisymm hupper hlower)


/-- For an antitone tuple, the coefficient of its own exponent in the associated partition polynomial is nonzero. -/
theorem coeff_partitionPolynomial_ne_zero (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    (partitionPolynomial N lam).coeff (Finsupp.equivFunOnFinite.symm lam) ≠ 0 := by
  set m : MonomialOrder (Fin N) := MonomialOrder.degLex with hm
  have hsv : StrictAnti (addStaircase N lam) := by
    intro i j hij; simp only [addStaircase]; have := hlam (le_of_lt hij); omega
  have hve : StrictAnti (staircaseExponents N) := by
    intro i j hij; simp only [staircaseExponents]; omega

  have hΔne : (alternantMatrix N (staircaseExponents N)).det ≠ 0 := by
    intro h
    have hcoeff := coeff_det_alternantMatrix_of_strictAnti hve hve
    rw [if_pos rfl, h, MvPolynomial.coeff_zero] at hcoeff
    exact one_ne_zero hcoeff.symm
  have hsne : partitionPolynomial N lam ≠ 0 := by
    intro h
    have hprod := partitionPolynomial_mul_det_staircase N lam
    rw [h, zero_mul] at hprod
    have hcoeff := coeff_det_alternantMatrix_of_strictAnti hsv hsv
    rw [if_pos rfl, ← hprod, MvPolynomial.coeff_zero] at hcoeff
    exact one_ne_zero hcoeff.symm

  have hΔdeg : m.degree (alternantMatrix N (staircaseExponents N)).det
      = Finsupp.equivFunOnFinite.symm (staircaseExponents N) :=
    degLex_degree_det_alternantMatrix hve
  have hDdeg : m.degree (alternantMatrix N (addStaircase N lam)).det
      = Finsupp.equivFunOnFinite.symm (addStaircase N lam) :=
    degLex_degree_det_alternantMatrix hsv

  have hadd : Finsupp.equivFunOnFinite.symm (addStaircase N lam)
      = Finsupp.equivFunOnFinite.symm lam
        + Finsupp.equivFunOnFinite.symm (staircaseExponents N) := by
    ext i
    simp only [Finsupp.add_apply, Finsupp.coe_equivFunOnFinite_symm, addStaircase, staircaseExponents]

  have hmul := m.degree_mul hsne hΔne
  rw [partitionPolynomial_mul_det_staircase, hDdeg, hΔdeg, hadd] at hmul
  have hdeg_schur : m.degree (partitionPolynomial N lam) = Finsupp.equivFunOnFinite.symm lam :=
    (add_right_cancel hmul).symm
  rw [← hdeg_schur]
  exact m.coeff_degree_ne_zero_iff.mpr hsne

end LeadingTerm

end RepresentationTheory.SymmetricPolynomials.Alternant
