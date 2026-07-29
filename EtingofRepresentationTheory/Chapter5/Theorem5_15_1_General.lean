import EtingofRepresentationTheory.Chapter5.Theorem5_15_1

/-!
# Theorem 5.15.1 with an independent variable count

The textbook permits any number of polynomial variables at least the number of rows of
the partition.  This file proves that stable form and retains the existing square-variable
statement as its `N = n` specialization.
-/

namespace Etingof

open scoped BigOperators

/-- The cycle-type power-sum product in an independently chosen set of `N` variables. -/
noncomputable def cycleTypePsumProductN (N n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin N) ℂ :=
  (σ.cycleType.map (MvPolynomial.psum (Fin N) ℂ)).prod *
    MvPolynomial.psum (Fin N) ℂ 1 ^ (n - σ.support.card)

/-- A partition exponent padded with zeros to an independently chosen number of variables. -/
noncomputable def Nat.Partition.toFinsuppN {n : ℕ} (N : ℕ) (la : Nat.Partition n) :
    Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => la.sortedParts.getD i 0)

/-- The exponent `λ + ρ`, written in reverse variable order.  This orientation is stable
under adjoining a new first variable: the new exponent is zero and every old exponent is
shifted by one. -/
noncomputable def frobeniusExponentRev {n : ℕ} (N : ℕ) (la : Nat.Partition n) :
    Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun i => la.sortedParts.getD (N - 1 - i.val) 0 + i.val)

/-- Set the first variable of an `(N+1)`-variable polynomial to zero and shift the
remaining variable names down by one. -/
noncomputable def dropFirstMv (N : ℕ) :
    MvPolynomial (Fin (N + 1)) ℂ →+* MvPolynomial (Fin N) ℂ :=
  (Polynomial.constantCoeff :
      Polynomial (MvPolynomial (Fin N) ℂ) →+* MvPolynomial (Fin N) ℂ).comp
    (MvPolynomial.finSuccEquiv ℂ N).toRingHom

lemma dropFirstMv_X_zero (N : ℕ) : dropFirstMv N (MvPolynomial.X 0) = 0 := by
  simp [dropFirstMv, MvPolynomial.finSuccEquiv_X_zero]

lemma dropFirstMv_X_succ (N : ℕ) (i : Fin N) :
    dropFirstMv N (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [dropFirstMv, MvPolynomial.finSuccEquiv_X_succ]

lemma dropFirstMv_psum (N m : ℕ) (hm : 0 < m) :
    dropFirstMv N (MvPolynomial.psum (Fin (N + 1)) ℂ m) =
      MvPolynomial.psum (Fin N) ℂ m := by
  simp [MvPolynomial.psum, Fin.sum_univ_succ, dropFirstMv_X_zero,
    dropFirstMv_X_succ, hm.ne']

private lemma dropFirstMv_psumProduct (N : ℕ) (s : Multiset ℕ)
    (hs : ∀ m ∈ s, 0 < m) :
    dropFirstMv N ((s.map (MvPolynomial.psum (Fin (N + 1)) ℂ)).prod) =
      (s.map (MvPolynomial.psum (Fin N) ℂ)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons m s ih =>
      have hm : 0 < m := hs m (by simp)
      have hs' : ∀ a ∈ s, 0 < a := fun a ha => hs a (by simp [ha])
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul,
        dropFirstMv_psum N m hm, ih hs']

private lemma dropFirstMv_cycleTypeProduct (N n : ℕ) (σ : Equiv.Perm (Fin n)) :
    dropFirstMv N
        ((σ.cycleType.map (MvPolynomial.psum (Fin (N + 1)) ℂ)).prod) =
      (σ.cycleType.map (MvPolynomial.psum (Fin N) ℂ)).prod := by
  apply dropFirstMv_psumProduct
  intro m hm
  exact lt_trans Nat.zero_lt_one (Equiv.Perm.one_lt_of_mem_cycleType hm)

/-- Adjoining a new first polynomial variable does not change the cycle-type power-sum
product after that variable is set to zero. -/
theorem dropFirstMv_cycleTypePsumProductN (N n : ℕ) (σ : Equiv.Perm (Fin n)) :
    dropFirstMv N (cycleTypePsumProductN (N + 1) n σ) =
      cycleTypePsumProductN N n σ := by
  simp only [cycleTypePsumProductN, map_mul, map_pow,
    dropFirstMv_cycleTypeProduct, dropFirstMv_psum N 1 Nat.zero_lt_one]

/-- Setting the new first variable to zero turns the `(N+1)`-variable Vandermonde into
the `N`-variable Vandermonde times one copy of every remaining variable. -/
theorem dropFirstMv_vandermondePoly (N : ℕ) :
    dropFirstMv N (vandermondePoly (N + 1)) =
      (∏ i : Fin N, MvPolynomial.X i) * vandermondePoly N := by
  simp [vandermondePoly, Fin.prod_univ_succ,
    Fin.prod_Ioi_succ, dropFirstMv_X_zero, dropFirstMv_X_succ]

/-- The exponent vector with one in every variable. -/
noncomputable def allOnesFinsupp (N : ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

lemma frobeniusExponentRev_succ {n N : ℕ} (la : Nat.Partition n)
    (hlen : la.sortedParts.length ≤ N) :
    frobeniusExponentRev (N + 1) la =
      (frobeniusExponentRev N la + allOnesFinsupp N).cons 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change la.sortedParts.getD N 0 = 0
    exact List.getD_eq_default la.sortedParts 0 hlen
  · simp only [Finsupp.cons_succ, Finsupp.coe_add, Pi.add_apply]
    have hidx : N - (j.val + 1) = N - 1 - j.val := by omega
    change la.sortedParts.getD (N - (j.val + 1)) 0 + (j.val + 1) =
      la.sortedParts.getD (N - 1 - j.val) 0 + j.val + 1
    rw [hidx]
    omega

lemma monomial_allOnesFinsupp (N : ℕ) :
    MvPolynomial.monomial (allOnesFinsupp N) (1 : ℂ) =
      ∏ i : Fin N, MvPolynomial.X i := by
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
    Finsupp.prod_fintype]
  · simp [allOnesFinsupp]
  · intro i
    simp

/-- In reverse variable order, the Frobenius coefficient is unchanged when a new
zero row / first polynomial variable is adjoined. -/
theorem frobeniusCoefficientRev_succ {n N : ℕ} (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hlen : la.sortedParts.length ≤ N) :
    MvPolynomial.coeff (frobeniusExponentRev (N + 1) la)
        (vandermondePoly (N + 1) * cycleTypePsumProductN (N + 1) n σ) =
      MvPolynomial.coeff (frobeniusExponentRev N la)
        (vandermondePoly N * cycleTypePsumProductN N n σ) := by
  rw [frobeniusExponentRev_succ la hlen]
  rw [← MvPolynomial.finSuccEquiv_coeff_coeff
    (frobeniusExponentRev N la + allOnesFinsupp N)
    (vandermondePoly (N + 1) * cycleTypePsumProductN (N + 1) n σ) 0]
  change MvPolynomial.coeff (frobeniusExponentRev N la + allOnesFinsupp N)
      (dropFirstMv N
        (vandermondePoly (N + 1) * cycleTypePsumProductN (N + 1) n σ)) = _
  rw [map_mul, dropFirstMv_vandermondePoly,
    dropFirstMv_cycleTypePsumProductN, mul_assoc]
  rw [← monomial_allOnesFinsupp]
  simpa using coeff_monomial_mul_shift (allOnesFinsupp N)
    (frobeniusExponentRev N la) 1
    (vandermondePoly N * cycleTypePsumProductN N n σ)

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

lemma rename_cycleTypePsumProductN (N n : ℕ) (σ : Equiv.Perm (Fin n))
    (e : Equiv.Perm (Fin N)) :
    MvPolynomial.rename e (cycleTypePsumProductN N n σ) =
      cycleTypePsumProductN N n σ := by
  simp only [cycleTypePsumProductN, map_mul, map_pow,
    rename_psumProduct, MvPolynomial.rename_psum]

lemma rename_vandermondePoly (N : ℕ) (e : Equiv.Perm (Fin N)) :
    MvPolynomial.rename e (vandermondePoly N) =
      (Equiv.Perm.sign e : ℤ) • vandermondePoly N := by
  unfold vandermondePoly
  simp only [map_prod, map_sub, MvPolynomial.rename_X]
  rw [e.prod_Ioi_comp_eq_sign_mul_prod
    (f := fun i j => MvPolynomial.X j - MvPolynomial.X i)]
  · simp [zsmul_eq_mul]
  · intro i j
    ring

lemma frobeniusExponentRev_eq_mapDomain {n N : ℕ} (la : Nat.Partition n) :
    frobeniusExponentRev N la =
      (Nat.Partition.toFinsuppN N la + rhoShift N).mapDomain
        (Fin.revPerm (n := N)) := by
  ext i
  have hidx : N - (i.val + 1) = N - 1 - i.val := by omega
  rw [show i = Fin.revPerm (Fin.revPerm i) by simp [Fin.revPerm]]
  rw [Finsupp.mapDomain_apply (Fin.revPerm (n := N)).injective]
  simp [frobeniusExponentRev, Nat.Partition.toFinsuppN, rhoShift, Fin.revPerm, hidx]
  omega

lemma Nat.Partition.toFinsuppN_self {n : ℕ} (la : Nat.Partition n) :
    Nat.Partition.toFinsuppN n la = Nat.Partition.toFinsupp la := rfl

lemma cycleTypePsumProductN_self (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    cycleTypePsumProductN n n σ = cycleTypePsumProduct n σ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The existing `n`-variable Frobenius formula, rewritten in the stable reverse-variable
orientation.  In this orientation the Vandermonde sign disappears. -/
theorem frobeniusCoefficientRev_self (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.coeff (frobeniusExponentRev n la)
        (vandermondePoly n * cycleTypePsumProductN n n σ) =
      spechtModuleCharacter n la σ := by
  let e := Fin.revPerm (n := n)
  let α := Nat.Partition.toFinsupp la + rhoShift n
  let F := vandermondePoly n * cycleTypePsumProduct n σ
  have hrename := MvPolynomial.coeff_rename_mapDomain e e.injective F α
  have hexp : frobeniusExponentRev n la = α.mapDomain e := by
    simpa [α, e, Nat.Partition.toFinsuppN_self] using
      (frobeniusExponentRev_eq_mapDomain (N := n) la)
  have hrename' :
      (Equiv.Perm.sign e : ℤ) •
          MvPolynomial.coeff (frobeniusExponentRev n la) F =
        MvPolynomial.coeff α F := by
    rw [← hexp] at hrename
    have hp : MvPolynomial.rename e (cycleTypePsumProduct n σ) =
        cycleTypePsumProduct n σ := by
      simpa only [cycleTypePsumProductN_self] using
        (rename_cycleTypePsumProductN n n σ e)
    rw [map_mul, rename_vandermondePoly, hp] at hrename
    rw [smul_mul_assoc, MvPolynomial.coeff_smul] at hrename
    simpa only [F] using hrename
  have hmain := Theorem5_15_1 n la σ
  change (Equiv.Perm.sign e : ℤ) • spechtModuleCharacter n la σ =
    MvPolynomial.coeff α F at hmain
  rw [← hmain] at hrename'
  rcases Int.isUnit_iff.mp (Units.isUnit (Equiv.Perm.sign e)) with hs | hs
  · simpa only [cycleTypePsumProductN_self, F, hs, one_zsmul] using hrename'
  · simpa only [cycleTypePsumProductN_self, F, hs, neg_zsmul, one_zsmul, neg_inj]
      using hrename'

private theorem frobeniusCoefficientRev_add {n N : ℕ} (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hlen : la.sortedParts.length ≤ N) (k : ℕ) :
    MvPolynomial.coeff (frobeniusExponentRev (N + k) la)
        (vandermondePoly (N + k) * cycleTypePsumProductN (N + k) n σ) =
      MvPolynomial.coeff (frobeniusExponentRev N la)
        (vandermondePoly N * cycleTypePsumProductN N n σ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hlen' : la.sortedParts.length ≤ N + k :=
        le_trans hlen (Nat.le_add_right N k)
      exact (frobeniusCoefficientRev_succ la σ hlen').trans ih

/-- Stable reverse-variable Frobenius formula for every variable count containing all rows. -/
theorem frobeniusCoefficientRev_general {n N : ℕ} (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hlen : la.sortedParts.length ≤ N) :
    MvPolynomial.coeff (frobeniusExponentRev N la)
        (vandermondePoly N * cycleTypePsumProductN N n σ) =
      spechtModuleCharacter n la σ := by
  let L := la.sortedParts.length
  have hLn : L ≤ n := by
    change la.sortedParts.length ≤ n
    have hsum : la.sortedParts.sum = n := by
      unfold Nat.Partition.sortedParts
      have h := congrArg Multiset.sum (Multiset.sort_eq la.parts (· ≥ ·))
      rw [Multiset.sum_coe] at h
      linarith [la.parts_sum]
    calc
      la.sortedParts.length ≤ la.sortedParts.sum :=
        List.length_le_sum_of_one_le _ (fun i hi => by
          have := sortedParts_pos la i hi
          omega)
      _ = n := hsum
  have hN := frobeniusCoefficientRev_add la σ (N := L) (le_refl L) (N - L)
  have hn := frobeniusCoefficientRev_add la σ (N := L) (le_refl L) (n - L)
  rw [Nat.add_sub_of_le hlen] at hN
  rw [Nat.add_sub_of_le hLn] at hn
  exact hN.trans (hn.symm.trans (frobeniusCoefficientRev_self n la σ))

set_option backward.isDefEq.respectTransparency false in
/-- **Theorem 5.15.1, stable form.** Let `λ` partition `n`, and choose any independent
number `N` of polynomial variables containing all rows of `λ`.  The Specht character is
the coefficient of `x^(λ+ρ_N)` in the `N`-variable Vandermonde times the cycle-type
power-sum product.  The sign records this project's `∏_{i<j}(x_j-x_i)` convention.

Taking `N = n` recovers `Etingof.Theorem5_15_1`; unlike that convenient specialization,
this theorem exposes the variable count quantified in the book. -/
theorem Theorem5_15_1_general {n N : ℕ} (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hlen : la.sortedParts.length ≤ N) :
    (Equiv.Perm.sign (Fin.revPerm (n := N)) : ℤ) •
        spechtModuleCharacter n la σ =
      MvPolynomial.coeff (Nat.Partition.toFinsuppN N la + rhoShift N)
        (vandermondePoly N * cycleTypePsumProductN N n σ) := by
  let e := Fin.revPerm (n := N)
  let α := Nat.Partition.toFinsuppN N la + rhoShift N
  let F := vandermondePoly N * cycleTypePsumProductN N n σ
  have hrename := MvPolynomial.coeff_rename_mapDomain e e.injective F α
  have hexp : frobeniusExponentRev N la = α.mapDomain e := by
    simpa [α, e] using frobeniusExponentRev_eq_mapDomain (N := N) la
  rw [← hexp] at hrename
  rw [map_mul, rename_vandermondePoly,
    rename_cycleTypePsumProductN N n σ e] at hrename
  rw [smul_mul_assoc, MvPolynomial.coeff_smul] at hrename
  rw [frobeniusCoefficientRev_general la σ hlen] at hrename
  simpa only [e, α, F] using hrename

end Etingof
