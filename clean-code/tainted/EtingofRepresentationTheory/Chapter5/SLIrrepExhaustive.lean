import EtingofRepresentationTheory.Chapter5.Remark5_23_3
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLExhaustive

/-!
# Exhaustiveness bridge for algebraic `SL_N` representations

This file supplies the formal bridge from the landed `GL_N` highest-weight classification to
`SL_N`.  It defines intrinsic regularity of matrix coefficients on `SL_N`, proves that restriction
of an algebraic `GL_N` representation is algebraic, constructs an algebraic `GL_N` extension of
every intrinsically algebraic simple `SL_N` representation, and proves unconditional
exhaustiveness by the restrictions of the `GL_N` highest-weight modules.
-/

noncomputable section

namespace Etingof

/-- Matrix-coefficient regularity for a family of endomorphisms indexed by `SL_n(k)`.  The
coefficients are restrictions of polynomials in the standard `GL_n` coordinate variables; on
`SL_n`, the inverse-determinant coordinate evaluates to `1`. -/
def IsAlgebraicSLCoefficientFamily
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Matrix.SpecialLinearGroup (Fin n) k → Y →ₗ[k] Y) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) k Y)
    (P : Fin m → Fin m → MvPolynomial (GLCoordVars n) k),
    ∀ (g : Matrix.SpecialLinearGroup (Fin n) k) (a c : Fin m),
      b.repr (σ g (b c)) a = evalAtGL (Matrix.SpecialLinearGroup.toGL g) (P a c)

/-- A bundled `SL_n` representation is algebraic when its coefficient family is algebraic. -/
def IsAlgebraicSLRepresentation
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) : Prop :=
  IsAlgebraicSLCoefficientFamily n σ

/-- Restricting an algebraic `GL_n` coefficient family to `SL_n` preserves algebraicity. -/
theorem IsAlgebraicCoefficientFamily.slRestrict
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y}
    (hρ : IsAlgebraicCoefficientFamily n ρ) :
    IsAlgebraicSLCoefficientFamily n (slRestrict ρ) := by
  obtain ⟨m, b, P, hP⟩ := hρ
  exact ⟨m, b, P, fun g a c => hP (Matrix.SpecialLinearGroup.toGL g) a c⟩

/-- An `SL_n` representation has an algebraic `GL_n` extension if its action is obtained by
restriction from an algebraic `GL_n` representation on the same vector space. -/
def HasAlgebraicGLExtension
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) : Prop :=
  ∃ ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y,
    IsAlgebraicCoefficientFamily n ρ ∧ slRestrict ρ = σ

/-- An abstract `GL_n` extension, without yet asserting regularity of its matrix coefficients. -/
def HasGLExtension
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) : Prop :=
  ∃ ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y, slRestrict ρ = σ

/-- A central group element acts by a scalar in a finite-dimensional simple representation over
an algebraically closed field.  This is the form of Schur's lemma used for the scalar roots of
unity in `SL_n`. -/
private theorem exists_scalar_action_of_central
    {k G Y : Type*} [Field k] [IsAlgClosed k] [Group G]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (σ : Representation k G Y)
    [hsimp : IsSimpleModule (MonoidAlgebra k G) σ.asModule]
    (z : G) (hz : ∀ g : G, z * g = g * z) :
    ∃ c : k, σ z = c • LinearMap.id := by
  letI : Nontrivial Y := IsSimpleModule.nontrivial (MonoidAlgebra k G) σ.asModule
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (σ z)
  let S : Subrepresentation σ :=
    { toSubmodule := Module.End.eigenspace (σ z) c
      apply_mem_toSubmodule := fun g v hv => by
        rw [Module.End.mem_eigenspace_iff] at hv ⊢
        calc
          σ z (σ g v) = σ (z * g) v := by rw [map_mul, Module.End.mul_apply]
          _ = σ (g * z) v := by rw [hz]
          _ = σ g (σ z v) := by rw [map_mul, Module.End.mul_apply]
          _ = σ g (c • v) := by rw [hv]
          _ = c • σ g v := by rw [map_smul] }
  have hS_ne : S ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
    intro hbot
    have : v ∈ (⊥ : Subrepresentation σ) := hbot ▸ hv
    change v ∈ (⊥ : Submodule k Y) at this
    exact hv0 ((Submodule.mem_bot k).mp this)
  have hirr : Representation.IsIrreducible σ :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).2 hsimp
  have hS : S = ⊤ := (hirr.eq_bot_or_eq_top S).resolve_left hS_ne
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  have hv : v ∈ S := by rw [hS]; trivial
  change v ∈ Module.End.eigenspace (σ z) c at hv
  rw [Module.End.mem_eigenspace_iff] at hv
  simpa only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] using hv

/-- Scalar matrices, bundled as a homomorphism.  `Remark5_23_3.scalarGL` is deliberately
defined elementwise there, so we package the elementary multiplicativity needed for descent. -/
private def scalarGLHom {k : Type*} [Field k] (n : ℕ) :
    kˣ →* Matrix.GeneralLinearGroup (Fin n) k where
  toFun := scalarGL k n
  map_one' := by
    apply Units.ext
    simp [scalarGL]
  map_mul' s t := by
    apply Units.ext
    simp [scalarGL, smul_smul, mul_comm]

@[simp] private theorem scalarGLHom_apply
    {k : Type*} [Field k] {n : ℕ} (s : kˣ) :
    scalarGLHom n s = scalarGL k n s := rfl

private theorem scalarGL_comm
    {k : Type*} [Field k] {n : ℕ} (s : kˣ)
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    scalarGL k n s * g = g * scalarGL k n s := by
  apply Units.ext
  change ((s : k) • 1) * (g : Matrix (Fin n) (Fin n) k) =
    (g : Matrix (Fin n) (Fin n) k) * ((s : k) • 1)
  simp

/-- The central-product map `kˣ × SL_n(k) → GL_n(k)`. -/
private def scalarSpecialMul {k : Type*} [Field k] (n : ℕ) :
    kˣ × Matrix.SpecialLinearGroup (Fin n) k →*
      Matrix.GeneralLinearGroup (Fin n) k where
  toFun p := scalarGL k n p.1 * Matrix.SpecialLinearGroup.toGL p.2
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one]
    change scalarGL k n 1 * 1 = 1
    rw [show scalarGL k n 1 = 1 by exact (scalarGLHom n).map_one, one_mul]
  map_mul' p q := by
    change scalarGL k n (p.1 * q.1) * Matrix.SpecialLinearGroup.toGL (p.2 * q.2) =
      (scalarGL k n p.1 * Matrix.SpecialLinearGroup.toGL p.2) *
        (scalarGL k n q.1 * Matrix.SpecialLinearGroup.toGL q.2)
    rw [show scalarGL k n (p.1 * q.1) = scalarGL k n p.1 * scalarGL k n q.1 by
      exact (scalarGLHom n).map_mul p.1 q.1]
    rw [map_mul]
    calc
      (scalarGL k n p.1 * scalarGL k n q.1) *
          (Matrix.SpecialLinearGroup.toGL p.2 * Matrix.SpecialLinearGroup.toGL q.2) =
        scalarGL k n p.1 *
          (scalarGL k n q.1 * Matrix.SpecialLinearGroup.toGL p.2) *
            Matrix.SpecialLinearGroup.toGL q.2 := by simp only [mul_assoc]
      _ = scalarGL k n p.1 *
          (Matrix.SpecialLinearGroup.toGL p.2 * scalarGL k n q.1) *
            Matrix.SpecialLinearGroup.toGL q.2 := by
        rw [scalarGL_comm q.1 (Matrix.SpecialLinearGroup.toGL p.2)]
      _ = (scalarGL k n p.1 * Matrix.SpecialLinearGroup.toGL p.2) *
          (scalarGL k n q.1 * Matrix.SpecialLinearGroup.toGL q.2) := by
        simp only [mul_assoc]

private theorem scalarSpecialMul_surjective
    {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (scalarSpecialMul (k := k) n) := by
  intro g
  obtain ⟨s, h, rfl⟩ := specialLinearFactor hn g
  exact ⟨(s, h), rfl⟩

/-- In a simple `SL_n` representation, scalar `n`-th roots of unity act through one power
character.  This is the compatibility needed to descend from the central product. -/
private theorem exists_scalar_weight
    {k Y : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ} (hn : n ≠ 0)
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    ∃ d : ℕ, d < n ∧ ∀ (s : kˣ) (hs : (s : k) ^ n = 1),
      sigma (scalarSL s hs) = ((s : k) ^ d) • LinearMap.id := by
  letI : NeZero n := ⟨hn⟩
  obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  let u : kˣ := (hzeta.isUnit hn).unit
  have hu : (u : k) = zeta := IsUnit.unit_spec _
  have hun : (u : k) ^ n = 1 := by rw [hu]; exact hzeta.pow_eq_one
  let z : Matrix.SpecialLinearGroup (Fin n) k := scalarSL u hun
  have hzcentral : ∀ g : Matrix.SpecialLinearGroup (Fin n) k, z * g = g * z := by
    intro g
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, show Matrix.SpecialLinearGroup.toGL z = scalarGL k n u by
      simp [z]]
    exact scalarGL_comm u _
  obtain ⟨c, hc⟩ := exists_scalar_action_of_central sigma z hzcentral
  have hupow : u ^ n = 1 := Units.ext hun
  have hzpow : z ^ n = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, show Matrix.SpecialLinearGroup.toGL z = scalarGL k n u by simp [z]]
    change (scalarGLHom n u) ^ n = _
    rw [← map_pow, hupow, map_one, map_one]
  have hpow_smul_id (a : k) (m : ℕ) :
      (a • LinearMap.id : Module.End k Y) ^ m = (a ^ m) • LinearMap.id := by
    induction m with
    | zero => ext v; simp
    | succ m ih =>
      rw [pow_succ, ih]
      ext v
      simp [pow_succ, mul_smul, mul_comm]
  have hcpowEnd : (c ^ n) • LinearMap.id =
      (1 : Module.End k Y) := by
    calc
      (c ^ n) • LinearMap.id = (c • LinearMap.id) ^ n := (hpow_smul_id c n).symm
      _ = (sigma z) ^ n := congrArg (fun T : Module.End k Y => T ^ n) hc.symm
      _ = sigma (z ^ n) := by rw [map_pow]
      _ = 1 := by rw [hzpow, map_one]
  letI : Nontrivial Y :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : Y)
  have hcpow : c ^ n = 1 := by
    apply smul_left_injective k hv
    have h := LinearMap.congr_fun hcpowEnd v
    simpa using h
  obtain ⟨d, hdlt, hcd⟩ := hzeta.eq_pow_of_pow_eq_one hcpow
  refine ⟨d, hdlt, fun s hs => ?_⟩
  obtain ⟨m, hmlt, hsm⟩ := hzeta.eq_pow_of_pow_eq_one hs
  have hsu : s = u ^ m := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu, hsm]
  have hscalarSL : scalarSL s hs = z ^ m := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, toGL_scalarSL]
    rw [show Matrix.SpecialLinearGroup.toGL z = scalarGL k n u by simp [z]]
    change scalarGL k n s = (scalarGLHom n u) ^ m
    rw [← map_pow, hsu]
    rfl
  rw [hscalarSL, map_pow, hc]
  rw [hpow_smul_id]
  ext v
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  rw [← hcd, ← hu]
  have hsval : (s : k) = (u : k) ^ m := congrArg Units.val hsu
  rw [hsval]
  rw [← pow_mul, mul_comm d m, pow_mul]

/-! ### Homogeneous normalization of intrinsic `SL_n` coefficients -/

/-- The roots-of-unity filter for ordinary total degrees. -/
private lemma root_average
    {k : Type*} [Field k] [CharZero k]
    {n d e : ℕ} (hd : d < n)
    {zeta : k} (hzeta : IsPrimitiveRoot zeta n) :
    ∑ j ∈ Finset.range n, zeta ^ (j * (n - d + e)) =
      if e ≡ d [MOD n] then (n : k) else 0 := by
  split_ifs with he
  · have hdvd : n ∣ n - d + e := by
      rw [← Nat.modEq_zero_iff_dvd]
      have h := he.add_left (n - d)
      have h' : n - d + e ≡ n [MOD n] := by
        convert h using 1
        all_goals omega
      have hzero : n ≡ 0 [MOD n] := Nat.modEq_zero_iff_dvd.2 (dvd_refl n)
      exact h'.trans hzero
    have hzpow : zeta ^ (n - d + e) = 1 :=
      (hzeta.pow_eq_one_iff_dvd _).2 hdvd
    calc
      ∑ j ∈ Finset.range n, zeta ^ (j * (n - d + e)) =
          ∑ j ∈ Finset.range n, (zeta ^ (n - d + e)) ^ j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [mul_comm, pow_mul]
      _ = (n : k) := by simp [hzpow]
  · have hndvd : ¬ n ∣ n - d + e := by
      intro hdvd
      apply he
      have h := (Nat.modEq_zero_iff_dvd.2 hdvd).add_right d
      have heq : n - d + e + d = n + e := by omega
      rw [heq] at h
      simpa using h
    have hzne : zeta ^ (n - d + e) ≠ 1 :=
      mt (hzeta.pow_eq_one_iff_dvd _).1 hndvd
    have hzpow : (zeta ^ (n - d + e)) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]
    have hmul := geom_sum_mul (zeta ^ (n - d + e)) n
    rw [hzpow, sub_self] at hmul
    have hsum : ∑ j ∈ Finset.range n, (zeta ^ (n - d + e)) ^ j = 0 :=
      (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hzne)
    calc
      ∑ j ∈ Finset.range n, zeta ^ (j * (n - d + e)) =
          ∑ j ∈ Finset.range n, (zeta ^ (n - d + e)) ^ j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [mul_comm, pow_mul]
      _ = 0 := hsum

/-- On `SL_n`, replace the formal determinant-inverse coordinate by `1`. -/
private def slEntryPolynomial {k : Type*} [Field k] (n : ℕ)
    (P : MvPolynomial (GLCoordVars n) k) :
    MvPolynomial (Fin n × Fin n) k :=
  MvPolynomial.bind₁ (Sum.elim MvPolynomial.X (fun _ => 1)) P

private lemma eval_slEntryPolynomial {k : Type*} [Field k] {n : ℕ}
    (h : Matrix.SpecialLinearGroup (Fin n) k)
    (P : MvPolynomial (GLCoordVars n) k) :
    MvPolynomial.eval
        (fun ij : Fin n × Fin n =>
          (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2)
        (slEntryPolynomial n P) =
      evalAtGL (Matrix.SpecialLinearGroup.toGL h) P := by
  unfold slEntryPolynomial Etingof.evalAtGL
  rw [MvPolynomial.hom_bind₁]
  congr 1
  apply MvPolynomial.ringHom_ext <;> intro x
  · simp
  · rcases x with ij | u
    · simp
    · simp [Matrix.SpecialLinearGroup.det_coe]

private lemma eval_mul_pow_of_isHomogeneous
    {k : Type*} [Field k] {n i : ℕ}
    {p : MvPolynomial (Fin n × Fin n) k} (hp : p.IsHomogeneous i)
    (c : k) (x : Fin n × Fin n → k) :
    MvPolynomial.eval (fun s => c * x s) p =
      c ^ i * MvPolynomial.eval x p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [MvPolynomial.mem_support_iff] at he
  have hdeg : e.degree = i := by
    by_contra h
    exact he (hp.coeff_eq_zero h)
  have hsum : (∑ s ∈ e.support, e s) = i := by rw [← hdeg]; rfl
  rw [Finset.prod_congr rfl (fun s _ => mul_pow c (x s) (e s)),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  ring

/-- Fourier projection onto the total degrees congruent to the central weight. -/
private lemma eval_congruent_homogeneousComponents
    {k : Type*} [Field k] [CharZero k]
    {n d : ℕ} (hn : n ≠ 0) (hd : d < n)
    {zeta : k} (hzeta : IsPrimitiveRoot zeta n)
    (p : MvPolynomial (Fin n × Fin n) k)
    (x : Fin n × Fin n → k)
    (hscale : ∀ j ∈ Finset.range n,
      MvPolynomial.eval (fun ij => zeta ^ j * x ij) p =
        (zeta ^ j) ^ d * MvPolynomial.eval x p) :
    MvPolynomial.eval x
        (∑ e ∈ Finset.range (p.totalDegree + 1),
          if e ≡ d [MOD n] then MvPolynomial.homogeneousComponent e p else 0) =
      MvPolynomial.eval x p := by
  classical
  let c : ℕ → k := fun e =>
    MvPolynomial.eval x (MvPolynomial.homogeneousComponent e p)
  have hdecomp (j : ℕ) :
      MvPolynomial.eval (fun ij => zeta ^ j * x ij) p =
        ∑ e ∈ Finset.range (p.totalDegree + 1), zeta ^ (j * e) * c e := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [eval_mul_pow_of_isHomogeneous
      (MvPolynomial.homogeneousComponent_isHomogeneous e p)]
    simp only [c, pow_mul]
  have havg_cov :
      ∑ j ∈ Finset.range n,
          zeta ^ (j * (n - d)) *
            MvPolynomial.eval (fun ij => zeta ^ j * x ij) p =
        (n : k) * MvPolynomial.eval x p := by
    calc
      _ = ∑ j ∈ Finset.range n,
          zeta ^ (j * (n - d)) *
            ((zeta ^ j) ^ d * MvPolynomial.eval x p) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hscale j hj]
      _ = ∑ j ∈ Finset.range n, MvPolynomial.eval x p := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [pow_mul, ← mul_assoc, ← pow_add,
                Nat.sub_add_cancel (Nat.le_of_lt hd), ← pow_mul, mul_comm j n,
                pow_mul, hzeta.pow_eq_one, one_pow, one_mul]
      _ = (n : k) * MvPolynomial.eval x p := by simp
  have havg_fourier :
      ∑ j ∈ Finset.range n,
          zeta ^ (j * (n - d)) *
            MvPolynomial.eval (fun ij => zeta ^ j * x ij) p =
        (n : k) *
          ∑ e ∈ Finset.range (p.totalDegree + 1),
            if e ≡ d [MOD n] then c e else 0 := by
    calc
      _ = ∑ j ∈ Finset.range n,
          ∑ e ∈ Finset.range (p.totalDegree + 1),
            zeta ^ (j * (n - d + e)) * c e := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hdecomp j, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e he
              rw [← mul_assoc]
              congr 1
              rw [← pow_add]
              congr 1
              rw [Nat.mul_add]
      _ = ∑ e ∈ Finset.range (p.totalDegree + 1),
          (∑ j ∈ Finset.range n, zeta ^ (j * (n - d + e))) * c e := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro e he
              rw [Finset.sum_mul]
      _ = ∑ e ∈ Finset.range (p.totalDegree + 1),
          (if e ≡ d [MOD n] then (n : k) else 0) * c e := by
              apply Finset.sum_congr rfl
              intro e he
              rw [root_average hd hzeta]
      _ = (n : k) * ∑ e ∈ Finset.range (p.totalDegree + 1),
          if e ≡ d [MOD n] then c e else 0 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e he
              split_ifs <;> simp
  have hcancel : (n : k) *
        (∑ e ∈ Finset.range (p.totalDegree + 1),
          if e ≡ d [MOD n] then c e else 0) =
      (n : k) * MvPolynomial.eval x p := havg_fourier.symm.trans havg_cov
  have hncast : (n : k) ≠ 0 := by exact_mod_cast hn
  have hsum := mul_left_cancel₀ hncast hcancel
  rw [map_sum]
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp [c]

/-- Normalize a homogeneous component of degree congruent to `d` modulo `n` to scalar weight
`d`, using a power of `det` below degree `d` and a power of `det⁻¹` above it. -/
private def normalizeSLComponent {k : Type*} [Field k]
    (n d e : ℕ) (p : MvPolynomial (Fin n × Fin n) k) :
    MvPolynomial (GLCoordVars n) k :=
  if e ≤ d then
    detPolyGL k n ^ ((d - e) / n) * MvPolynomial.rename Sum.inl p
  else
    MvPolynomial.X (Sum.inr ()) ^ ((e - d) / n) * MvPolynomial.rename Sum.inl p

private lemma evalAtGL_rename_inl {k : Type*} [Field k] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (p : MvPolynomial (Fin n × Fin n) k) :
    evalAtGL g (MvPolynomial.rename Sum.inl p) =
      MvPolynomial.eval
        (fun ij : Fin n × Fin n =>
          (g : Matrix (Fin n) (Fin n) k) ij.1 ij.2) p := by
  unfold Etingof.evalAtGL
  rw [MvPolynomial.eval_rename]
  rfl

private lemma eval_normalizeSLComponent
    {k : Type*} [Field k] {n d e : ℕ}
    (hmod : e ≡ d [MOD n])
    (p : MvPolynomial (Fin n × Fin n) k) (hp : p.IsHomogeneous e)
    (s : kˣ) (h : Matrix.SpecialLinearGroup (Fin n) k) :
    evalAtGL (scalarGL k n s * Matrix.SpecialLinearGroup.toGL h)
        (normalizeSLComponent n d e p) =
      (s : k) ^ d *
        MvPolynomial.eval
          (fun ij : Fin n × Fin n =>
            (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2) p := by
  classical
  let g := scalarGL k n s * Matrix.SpecialLinearGroup.toGL h
  have hentries : ∀ ij : Fin n × Fin n,
      (g : Matrix (Fin n) (Fin n) k) ij.1 ij.2 =
        (s : k) * (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2 := by
    intro ij
    change (((s : k) • (1 : Matrix (Fin n) (Fin n) k)) *
      (h : Matrix (Fin n) (Fin n) k)) ij.1 ij.2 = _
    simp
  have hrename : evalAtGL g (MvPolynomial.rename Sum.inl p) =
      (s : k) ^ e *
        MvPolynomial.eval
          (fun ij : Fin n × Fin n =>
            (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2) p := by
    rw [evalAtGL_rename_inl]
    rw [show (fun ij : Fin n × Fin n =>
      (g : Matrix (Fin n) (Fin n) k) ij.1 ij.2) =
        (fun ij => (s : k) * (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2) by
          funext ij
          exact hentries ij]
    exact eval_mul_pow_of_isHomogeneous hp (s : k) _
  have hdet : (Matrix.GeneralLinearGroup.det g : k) = (s : k) ^ n := by
    change ((Etingof.KernelLemmaKPrime.detChar k n) g : k) = _
    simp [g, map_mul, detChar_toGL, detChar_scalarGL]
  change evalAtGL g (normalizeSLComponent n d e p) = _
  unfold normalizeSLComponent
  split_ifs with hed
  · have hdvd : n ∣ d - e := (Nat.modEq_iff_dvd' hed).mp hmod
    have hdegree : e + n * ((d - e) / n) = d := by
      rw [mul_comm n, Nat.div_mul_cancel hdvd, Nat.add_sub_of_le hed]
    rw [evalAtGL_mul, evalAtGL_pow, evalAtGL_detPolyGL, hdet, hrename]
    have hdegree' : n * ((d - e) / n) + e = d := by
      simpa [Nat.add_comm] using hdegree
    rw [← pow_mul, ← mul_assoc, ← pow_add, hdegree']
  · have hde : d ≤ e := Nat.le_of_not_ge hed
    have hdvd : n ∣ e - d := (Nat.modEq_iff_dvd' hde).mp hmod.symm
    have hdegree : d + n * ((e - d) / n) = e := by
      rw [mul_comm n, Nat.div_mul_cancel hdvd, Nat.add_sub_of_le hde]
    rw [evalAtGL_mul, evalAtGL_pow, evalAtGL_X_inr,
      ← Matrix.GeneralLinearGroup.val_det_apply, hdet, hrename]
    have hsne : (s : k) ^ n ≠ 0 := pow_ne_zero _ (Units.ne_zero s)
    nth_rewrite 2 [show e = d + n * ((e - d) / n) from hdegree.symm]
    rw [pow_add, pow_mul, inv_pow]
    have hqne : ((s : k) ^ n) ^ ((e - d) / n) ≠ 0 := pow_ne_zero _ hsne
    calc
      _ = (s : k) ^ d *
          ((((s : k) ^ n) ^ ((e - d) / n))⁻¹ *
            ((s : k) ^ n) ^ ((e - d) / n)) *
          MvPolynomial.eval
            (fun ij : Fin n × Fin n =>
              (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2) p := by ring
      _ = _ := by rw [inv_mul_cancel₀ hqne, mul_one]

/-- The regular `GL_n` polynomial obtained by normalizing the congruent homogeneous pieces of an
intrinsic `SL_n` coefficient. -/
private def slExtensionPolynomial {k : Type*} [Field k]
    (n d : ℕ) (P : MvPolynomial (GLCoordVars n) k) :
    MvPolynomial (GLCoordVars n) k :=
  let p := slEntryPolynomial n P
  ∑ e ∈ Finset.range (p.totalDegree + 1),
    if e ≡ d [MOD n] then
      normalizeSLComponent n d e (MvPolynomial.homogeneousComponent e p)
    else 0

private lemma eval_slExtensionPolynomial
    {k : Type*} [Field k] [CharZero k]
    {n d : ℕ} (hn : n ≠ 0) (hd : d < n)
    {zeta : k} (hzeta : IsPrimitiveRoot zeta n)
    (P : MvPolynomial (GLCoordVars n) k)
    (s : kˣ) (h : Matrix.SpecialLinearGroup (Fin n) k)
    (hscale : ∀ j ∈ Finset.range n,
      MvPolynomial.eval
          (fun ij : Fin n × Fin n =>
            zeta ^ j * (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2)
          (slEntryPolynomial n P) =
        (zeta ^ j) ^ d *
          MvPolynomial.eval
            (fun ij : Fin n × Fin n =>
              (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2)
            (slEntryPolynomial n P)) :
    evalAtGL (scalarGL k n s * Matrix.SpecialLinearGroup.toGL h)
        (slExtensionPolynomial n d P) =
      (s : k) ^ d * evalAtGL (Matrix.SpecialLinearGroup.toGL h) P := by
  classical
  let p := slEntryPolynomial n P
  let x : Fin n × Fin n → k := fun ij =>
    (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2
  have hproject :
      MvPolynomial.eval x
          (∑ e ∈ Finset.range (p.totalDegree + 1),
            if e ≡ d [MOD n] then MvPolynomial.homogeneousComponent e p else 0) =
        MvPolynomial.eval x p :=
    eval_congruent_homogeneousComponents hn hd hzeta p x hscale
  unfold slExtensionPolynomial
  dsimp only
  rw [Etingof.evalAtGL, map_sum]
  calc
    _ = ∑ e ∈ Finset.range (p.totalDegree + 1),
        if he : e ≡ d [MOD n] then
          (s : k) ^ d *
            MvPolynomial.eval x (MvPolynomial.homogeneousComponent e p)
        else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          split_ifs with hmod
          · rw [← Etingof.evalAtGL]
            exact eval_normalizeSLComponent hmod _
              (MvPolynomial.homogeneousComponent_isHomogeneous e p) s h
          · simp only [map_zero]
    _ = (s : k) ^ d *
        MvPolynomial.eval x
          (∑ e ∈ Finset.range (p.totalDegree + 1),
            if e ≡ d [MOD n] then MvPolynomial.homogeneousComponent e p else 0) := by
          rw [map_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          split_ifs <;> simp
    _ = (s : k) ^ d * MvPolynomial.eval x p := by rw [hproject]
    _ = (s : k) ^ d * evalAtGL (Matrix.SpecialLinearGroup.toGL h) P := by
      rw [eval_slEntryPolynomial]

/-- The product action before descent: the scalar factor acts by the chosen power character and
the special-linear factor acts through `sigma`. -/
private def scalarSpecialAction
    {k Y : Type*} [Field k] {n : ℕ}
    [AddCommGroup Y] [Module k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) (d : ℕ) :
    kˣ × Matrix.SpecialLinearGroup (Fin n) k →* Module.End k Y where
  toFun p := ((p.1 : k) ^ d) • sigma p.2
  map_one' := by ext v; simp
  map_mul' p q := by
    ext v
    simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, mul_pow, map_mul,
      Module.End.mul_apply, LinearMap.smul_apply, map_smul]
    rw [mul_comm, mul_smul]

private theorem scalarSpecialAction_ker_le
    {k Y : Type*} [Field k] {n : ℕ}
    [AddCommGroup Y] [Module k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) (d : ℕ)
    (hscalar : ∀ (s : kˣ) (hs : (s : k) ^ n = 1),
      sigma (scalarSL s hs) = ((s : k) ^ d) • LinearMap.id) :
    (scalarSpecialMul (k := k) n).ker ≤ (scalarSpecialAction sigma d).toHomUnits.ker := by
  rintro ⟨s, h⟩ hx
  rw [MonoidHom.mem_ker] at hx ⊢
  change scalarGL k n s * Matrix.SpecialLinearGroup.toGL h = 1 at hx
  have hdet := congrArg (KernelLemmaKPrime.detChar k n) hx
  have hsunit : s ^ n = 1 := by
    simpa [map_mul, detChar_toGL, detChar_scalarGL] using hdet
  have hs : (s : k) ^ n = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hsunit
  have hsinv : ((s⁻¹ : kˣ) : k) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hsunit, inv_one]
    rfl
  have hh : h = scalarSL s⁻¹ hsinv := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    have hto : Matrix.SpecialLinearGroup.toGL h = (scalarGL k n s)⁻¹ :=
      eq_inv_of_mul_eq_one_right hx
    rw [hto, toGL_scalarSL]
    exact ((scalarGLHom n).map_inv s).symm
  apply Units.ext
  change ((s : k) ^ d) • sigma h = (1 : Module.End k Y)
  rw [hh, hscalar]
  ext v
  simp [← Units.val_pow_eq_pow_val]

/-- The central-product construction, retaining the scalar weight needed to prove regularity. -/
private theorem exists_GLExtension_with_scalarWeight
    (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type*} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (hn : n ≠ 0)
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    ∃ (d : ℕ), d < n ∧
      ∃ rho : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y,
        slRestrict rho = sigma ∧
        ∀ s : kˣ, rho (scalarGL k n s) = ((s : k) ^ d) • LinearMap.id := by
  obtain ⟨d, hd, hscalar⟩ := exists_scalar_weight hn sigma
  let phi := scalarSpecialMul (k := k) n
  let psi := scalarSpecialAction sigma d
  have hphi : Function.Surjective phi := scalarSpecialMul_surjective hn
  have hker : phi.ker ≤ psi.toHomUnits.ker :=
    scalarSpecialAction_ker_le sigma d hscalar
  let lift : Matrix.GeneralLinearGroup (Fin n) k →* (Module.End k Y)ˣ :=
    phi.liftOfSurjective hphi ⟨psi.toHomUnits, hker⟩
  let rho : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y :=
    (Units.coeHom (Module.End k Y)).comp lift
  refine ⟨d, hd, rho, ?_, ?_⟩
  · ext h v
    have hphi1 : phi (1, h) = Matrix.SpecialLinearGroup.toGL h := by
      change scalarGL k n 1 * Matrix.SpecialLinearGroup.toGL h =
        Matrix.SpecialLinearGroup.toGL h
      rw [show scalarGL k n 1 = 1 by exact (scalarGLHom n).map_one, one_mul]
    have hlift : lift (Matrix.SpecialLinearGroup.toGL h) = psi.toHomUnits (1, h) := by
      rw [← hphi1]
      simp [lift]
    change ((lift (Matrix.SpecialLinearGroup.toGL h) : (Module.End k Y)ˣ) :
      Module.End k Y) v = sigma h v
    rw [hlift]
    change (((1 : kˣ) : k) ^ d • sigma h) v = sigma h v
    simp
  · intro s
    have hphiS : phi (s, 1) = scalarGL k n s := by
      change scalarGL k n s * Matrix.SpecialLinearGroup.toGL 1 = scalarGL k n s
      simp
    have hlift : lift (scalarGL k n s) = psi.toHomUnits (s, 1) := by
      rw [← hphiS]
      simp [lift]
    ext v
    change ((lift (scalarGL k n s) : (Module.End k Y)ˣ) : Module.End k Y) v = _
    rw [hlift]
    simp [psi, scalarSpecialAction]

/-- Every finite-dimensional simple abstract representation of `SL_n` over an algebraically
closed field of characteristic zero extends to `GL_n`.  No regularity is asserted here.  The
construction descends the compatible action of the central product `kˣ × SL_n`. -/
theorem hasGLExtension_of_isSimple
    (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type*} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    HasGLExtension n sigma := by
  rcases eq_or_ne n 0 with rfl | hn
  · let rho : Representation k (Matrix.GeneralLinearGroup (Fin 0) k) Y :=
      Representation.trivial k _ _
    refine ⟨rho, ?_⟩
    ext h v
    change v = sigma h v
    have hh : h = 1 := by
      apply Subtype.ext
      funext i
      exact Fin.elim0 i
    rw [hh, map_one]
    rfl
  · obtain ⟨_, _, rho, hres, _⟩ :=
      exists_GLExtension_with_scalarWeight n k hn sigma
    exact ⟨rho, hres⟩

/-- Every intrinsically algebraic finite-dimensional simple `SL_n` representation has an
algebraic `GL_n` extension.  The central weight chooses the congruence class of total degrees;
roots-of-unity averaging removes the other homogeneous components, and determinant powers
normalize every retained component to that scalar weight. -/
theorem hasAlgebraicGLExtension_of_isSimple
    (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type*} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    (halg : IsAlgebraicSLRepresentation n sigma)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    HasAlgebraicGLExtension n sigma := by
  rcases eq_or_ne n 0 with rfl | hn
  · let rho : Representation k (Matrix.GeneralLinearGroup (Fin 0) k) Y :=
      Representation.trivial k _ _
    have hres : slRestrict rho = sigma := by
      ext h v
      change v = sigma h v
      have hh : h = 1 := by
        apply Subtype.ext
        funext i
        exact Fin.elim0 i
      rw [hh, map_one]
      rfl
    refine ⟨rho, ?_, hres⟩
    classical
    let b := Module.finBasis k Y
    refine ⟨_, b, fun a c => MvPolynomial.C (b.repr (b c) a), ?_⟩
    intro g a c
    change b.repr (b c) a = _
    simp [Etingof.evalAtGL]
  · obtain ⟨d, hd, rho, hres, hscalar⟩ :=
      exists_GLExtension_with_scalarWeight n k hn sigma
    obtain ⟨m, b, P, hP⟩ := halg
    letI : NeZero n := ⟨hn⟩
    obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
    let u : kˣ := (hzeta.isUnit hn).unit
    have hu : (u : k) = zeta := IsUnit.unit_spec _
    have hun : (u : k) ^ n = 1 := by rw [hu]; exact hzeta.pow_eq_one
    let Q : Fin m → Fin m → MvPolynomial (GLCoordVars n) k :=
      fun a c => slExtensionPolynomial n d (P a c)
    refine ⟨rho, ⟨m, b, Q, ?_⟩, hres⟩
    intro g a c
    obtain ⟨s, h, rfl⟩ := specialLinearFactor hn g
    have hres_h : rho (Matrix.SpecialLinearGroup.toGL h) = sigma h := by
      have := DFunLike.congr_fun hres h
      exact this
    have hcoeff :
        b.repr
            (rho (scalarGL k n s * Matrix.SpecialLinearGroup.toGL h) (b c)) a =
          (s : k) ^ d * b.repr (sigma h (b c)) a := by
      rw [map_mul, hscalar s, Module.End.mul_apply, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, hres_h]
    rw [hcoeff, hP h a c]
    symm
    apply eval_slExtensionPolynomial hn hd hzeta (P a c) s h
    intro j hj
    let uj : kˣ := u ^ j
    have huj : (uj : k) = zeta ^ j := by simp [uj, hu]
    have hujn : (uj : k) ^ n = 1 := by
      rw [huj, ← pow_mul, mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]
    let z : Matrix.SpecialLinearGroup (Fin n) k := scalarSL uj hujn
    have hzentries : (fun ij : Fin n × Fin n =>
          zeta ^ j * (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2) =
        (fun ij : Fin n × Fin n =>
          (z * h : Matrix.SpecialLinearGroup (Fin n) k) ij.1 ij.2) := by
      funext ij
      change zeta ^ j * (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2 =
        (((uj : k) • (1 : Matrix (Fin n) (Fin n) k)) *
          (h : Matrix (Fin n) (Fin n) k)) ij.1 ij.2
      simp [huj]
    have hres_z : rho (Matrix.SpecialLinearGroup.toGL z) = sigma z := by
      have := DFunLike.congr_fun hres z
      exact this
    have hzaction : sigma z = ((zeta ^ j) ^ d) • LinearMap.id := by
      rw [← hres_z, show Matrix.SpecialLinearGroup.toGL z = scalarGL k n uj by
        simp [z], hscalar uj, huj]
    rw [hzentries, eval_slEntryPolynomial, eval_slEntryPolynomial,
      ← hP (z * h) a c, ← hP h a c, map_mul, hzaction, Module.End.mul_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul, Finsupp.smul_apply,
      smul_eq_mul]

/-- Liftable algebraicity implies intrinsic algebraicity on `SL_n`. -/
theorem HasAlgebraicGLExtension.isAlgebraic
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y}
    (hσ : HasAlgebraicGLExtension n σ) : IsAlgebraicSLRepresentation n σ := by
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  exact hρ.slRestrict

/-- A representation whose restriction to `SL_n` is simple is itself simple as a `GL_n`
representation: every `GL_n`-stable subspace is in particular `SL_n`-stable. -/
theorem isSimpleModule_of_slRestrict_isSimple
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    [hsl : IsSimpleModule (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k))
      (slRestrict ρ).asModule] :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have hsl' : Representation.IsIrreducible (slRestrict ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).2 hsl
  letI : Nontrivial Y :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) (slRestrict ρ).asModule
  refine
    { exists_pair_ne := ⟨⊥, ⊤, by
        intro h
        have h' := congrArg Subrepresentation.toSubmodule h
        change (⊥ : Submodule k Y) = ⊤ at h'
        exact bot_ne_top h'⟩
      eq_bot_or_eq_top := fun S => ?_ }
  let T : Subrepresentation (slRestrict ρ) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g _ hv =>
        S.apply_mem_toSubmodule (Matrix.SpecialLinearGroup.toGL g) hv }
  rcases hsl'.eq_bot_or_eq_top T with hT | hT
  · left
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊥
    have hT' := congrArg Subrepresentation.toSubmodule hT
    change T.toSubmodule = (⊥ : Submodule k Y) at hT'
    exact hT'
  · right
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    have hT' := congrArg Subrepresentation.toSubmodule hT
    change T.toSubmodule = (⊤ : Submodule k Y) at hT'
    exact hT'

/-- Every simple `SL_n` representation that admits an algebraic `GL_n` extension is isomorphic to
the restriction of `L_λ` for some dominant weight `λ`. -/
theorem exists_dominantWeight_slEquiv_of_hasAlgebraicGLExtension
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    (hσ : HasAlgebraicGLExtension n σ)
    [hsimp : IsSimpleModule (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) σ.asModule] :
    ∃ lam : DominantWeight n,
      Nonempty (Representation.Equiv σ (slRestrict (algIrrepGLRepρ n lam k))) := by
  obtain ⟨ρ, hρ, hres⟩ := hσ
  subst σ
  letI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule :=
    isSimpleModule_of_slRestrict_isSimple ρ
  obtain ⟨lam, ⟨e⟩⟩ :=
    exists_dominantWeight_asModuleEquiv_of_isSimpleModule n k ρ hρ
  let E : Representation.Equiv ρ (algIrrepGLRepρ n lam k) :=
    Representation.Equiv.mk (Representation.kEquivOfAsModuleEquiv e) (fun g => by
      ext v
      exact Representation.kEquivOfAsModuleEquiv_intertwines e g v)
  exact ⟨lam, ⟨slRestrictEquiv E⟩⟩

/-- **Exhaustiveness for algebraic `SL_n` representations.** Every intrinsically algebraic
finite-dimensional simple representation of `SL_n` over an algebraically closed field of
characteristic zero is isomorphic to the restriction of `L_λ` for some dominant weight `λ`. -/
theorem exists_dominantWeight_slEquiv_of_isAlgebraic
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    (halg : IsAlgebraicSLRepresentation n sigma)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    ∃ lam : DominantWeight n,
      Nonempty (Representation.Equiv sigma (slRestrict (algIrrepGLRepρ n lam k))) := by
  exact exists_dominantWeight_slEquiv_of_hasAlgebraicGLExtension n k sigma
    (hasAlgebraicGLExtension_of_isSimple n k sigma halg)

end Etingof
