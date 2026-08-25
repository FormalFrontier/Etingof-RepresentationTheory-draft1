/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction
import RepresentationTheory.AuxiliaryRepresentationDecompositions
import RepresentationTheory.Alignment.Attribute

/-! # Special linear representations -/

noncomputable section

namespace RepresentationTheory.Auxiliary.SpecialLinearRepresentation

namespace SpecialLinearRepresentation


/-- A property of functions from a special linear group to linear endomorphisms of a finite module. -/
def finiteLinearMapProperty
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Matrix.SpecialLinearGroup (Fin n) k → Y →ₗ[k] Y) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) k Y)
    (P : Fin m → Fin m → MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k),
    ∀ (g : Matrix.SpecialLinearGroup (Fin n) k) (a c : Fin m),
      b.repr (σ g (b c)) a = RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation (Matrix.SpecialLinearGroup.toGL g) (P a c)


/-- A primed property of finite modules carrying a representation of the special linear group. -/
def finiteProperty'
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) : Prop :=
  finiteLinearMapProperty n σ


end SpecialLinearRepresentation

end RepresentationTheory.Auxiliary.SpecialLinearRepresentation

namespace RepresentationTheory.GeneralLinearGroup.Auxiliary

/-- Turns the assumed predicate on a general-linear representation into the target predicate on the derived special-linear representation. -/
theorem HasAuxiliaryMapProperty.toFiniteLinearMapProperty
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y}
    (hρ : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n ρ) :
    RepresentationTheory.Auxiliary.SpecialLinearRepresentation.SpecialLinearRepresentation.finiteLinearMapProperty n (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.restrictToSpecialLinear ρ) := by
  obtain ⟨m, b, P, hP⟩ := hρ
  exact ⟨m, b, P, fun g a c => hP (Matrix.SpecialLinearGroup.toGL g) a c⟩


end RepresentationTheory.GeneralLinearGroup.Auxiliary

namespace RepresentationTheory.Auxiliary.SpecialLinearRepresentation

namespace SpecialLinearRepresentation

/-- A property of finite modules carrying a representation of the special linear group. -/
def finiteProperty
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) : Prop :=
  ∃ ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y,
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n ρ ∧ RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.restrictToSpecialLinear ρ = σ


/-- A property of modules carrying a representation of the special linear group. -/
def property
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) : Prop :=
  ∃ ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y, RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.restrictToSpecialLinear ρ = σ


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


private def scalarGLHom {k : Type*} [Field k] (n : ℕ) :
    kˣ →* Matrix.GeneralLinearGroup (Fin n) k where
  toFun := RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n
  map_one' := by
    apply Units.ext
    simp [RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix]
  map_mul' s t := by
    apply Units.ext
    simp [RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix, smul_smul, mul_comm]

@[simp] private theorem scalarGLHom_apply
    {k : Type*} [Field k] {n : ℕ} (s : kˣ) :
    scalarGLHom n s = RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s := rfl

private theorem scalarGL_comm
    {k : Type*} [Field k] {n : ℕ} (s : kˣ)
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s * g = g * RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s := by
  apply Units.ext
  change ((s : k) • 1) * (g : Matrix (Fin n) (Fin n) k) =
    (g : Matrix (Fin n) (Fin n) k) * ((s : k) • 1)
  simp


private def scalarSpecialMul {k : Type*} [Field k] (n : ℕ) :
    kˣ × Matrix.SpecialLinearGroup (Fin n) k →*
      Matrix.GeneralLinearGroup (Fin n) k where
  toFun p := RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n p.1 * Matrix.SpecialLinearGroup.toGL p.2
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one]
    change RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n 1 * 1 = 1
    rw [show RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n 1 = 1 by exact (scalarGLHom n).map_one, one_mul]
  map_mul' p q := by
    change RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n (p.1 * q.1) * Matrix.SpecialLinearGroup.toGL (p.2 * q.2) =
      (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n p.1 * Matrix.SpecialLinearGroup.toGL p.2) *
        (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n q.1 * Matrix.SpecialLinearGroup.toGL q.2)
    rw [show RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n (p.1 * q.1) = RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n p.1 * RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n q.1 by
      exact (scalarGLHom n).map_mul p.1 q.1]
    rw [map_mul]
    calc
      (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n p.1 * RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n q.1) *
          (Matrix.SpecialLinearGroup.toGL p.2 * Matrix.SpecialLinearGroup.toGL q.2) =
        RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n p.1 *
          (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n q.1 * Matrix.SpecialLinearGroup.toGL p.2) *
            Matrix.SpecialLinearGroup.toGL q.2 := by simp only [mul_assoc]
      _ = RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n p.1 *
          (Matrix.SpecialLinearGroup.toGL p.2 * RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n q.1) *
            Matrix.SpecialLinearGroup.toGL q.2 := by
        rw [scalarGL_comm q.1 (Matrix.SpecialLinearGroup.toGL p.2)]
      _ = (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n p.1 * Matrix.SpecialLinearGroup.toGL p.2) *
          (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n q.1 * Matrix.SpecialLinearGroup.toGL q.2) := by
        simp only [mul_assoc]

private theorem scalarSpecialMul_surjective
    {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (scalarSpecialMul (k := k) n) := by
  intro g
  obtain ⟨s, h, rfl⟩ := RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.exists_scalarMatrix_mul_specialLinear hn g
  exact ⟨(s, h), rfl⟩


private theorem exists_scalar_weight
    {k Y : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ} (hn : n ≠ 0)
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    ∃ d : ℕ, d < n ∧ ∀ (s : kˣ) (hs : (s : k) ^ n = 1),
      sigma (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarSpecialLinear s hs) = ((s : k) ^ d) • LinearMap.id := by
  letI : NeZero n := ⟨hn⟩
  obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  let u : kˣ := (hzeta.isUnit hn).unit
  have hu : (u : k) = zeta := IsUnit.unit_spec _
  have hun : (u : k) ^ n = 1 := by rw [hu]; exact hzeta.pow_eq_one
  let z : Matrix.SpecialLinearGroup (Fin n) k := RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarSpecialLinear u hun
  have hzcentral : ∀ g : Matrix.SpecialLinearGroup (Fin n) k, z * g = g * z := by
    intro g
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, show Matrix.SpecialLinearGroup.toGL z = RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n u by
      simp [z]]
    exact scalarGL_comm u _
  obtain ⟨c, hc⟩ := exists_scalar_action_of_central sigma z hzcentral
  have hupow : u ^ n = 1 := Units.ext hun
  have hzpow : z ^ n = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, show Matrix.SpecialLinearGroup.toGL z = RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n u by simp [z]]
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
  have hscalarSL : RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarSpecialLinear s hs = z ^ m := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarSpecialLinear_toGL]
    rw [show Matrix.SpecialLinearGroup.toGL z = RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n u by simp [z]]
    change RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s = (scalarGLHom n u) ^ m
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


private def slEntryPolynomial {k : Type*} [Field k] (n : ℕ)
    (P : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k) :
    MvPolynomial (Fin n × Fin n) k :=
  MvPolynomial.bind₁ (Sum.elim MvPolynomial.X (fun _ => 1)) P

private lemma eval_slEntryPolynomial {k : Type*} [Field k] {n : ℕ}
    (h : Matrix.SpecialLinearGroup (Fin n) k)
    (P : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k) :
    MvPolynomial.eval
        (fun ij : Fin n × Fin n =>
          (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2)
        (slEntryPolynomial n P) =
      RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation (Matrix.SpecialLinearGroup.toGL h) P := by
  unfold slEntryPolynomial RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation
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


private def normalizeSLComponent {k : Type*} [Field k]
    (n d e : ℕ) (p : MvPolynomial (Fin n × Fin n) k) :
    MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k :=
  if e ≤ d then
    RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.auxiliaryPolynomial k n ^ ((d - e) / n) * MvPolynomial.rename Sum.inl p
  else
    MvPolynomial.X (Sum.inr ()) ^ ((e - d) / n) * MvPolynomial.rename Sum.inl p

private lemma evalAtGL_rename_inl {k : Type*} [Field k] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (p : MvPolynomial (Fin n × Fin n) k) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (MvPolynomial.rename Sum.inl p) =
      MvPolynomial.eval
        (fun ij : Fin n × Fin n =>
          (g : Matrix (Fin n) (Fin n) k) ij.1 ij.2) p := by
  unfold RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation
  rw [MvPolynomial.eval_rename]
  rfl

private lemma eval_normalizeSLComponent
    {k : Type*} [Field k] {n d e : ℕ}
    (hmod : e ≡ d [MOD n])
    (p : MvPolynomial (Fin n × Fin n) k) (hp : p.IsHomogeneous e)
    (s : kˣ) (h : Matrix.SpecialLinearGroup (Fin n) k) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s * Matrix.SpecialLinearGroup.toGL h)
        (normalizeSLComponent n d e p) =
      (s : k) ^ d *
        MvPolynomial.eval
          (fun ij : Fin n × Fin n =>
            (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2) p := by
  classical
  let g := RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s * Matrix.SpecialLinearGroup.toGL h
  have hentries : ∀ ij : Fin n × Fin n,
      (g : Matrix (Fin n) (Fin n) k) ij.1 ij.2 =
        (s : k) * (h : Matrix (Fin n) (Fin n) k) ij.1 ij.2 := by
    intro ij
    change (((s : k) • (1 : Matrix (Fin n) (Fin n) k)) *
      (h : Matrix (Fin n) (Fin n) k)) ij.1 ij.2 = _
    simp
  have hrename : RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (MvPolynomial.rename Sum.inl p) =
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
    change ((RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n) g : k) = _
    simp [g, map_mul, RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.detCharacter_specialLinear, RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.detCharacter_scalarMatrix]
  change RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (normalizeSLComponent n d e p) = _
  unfold normalizeSLComponent
  split_ifs with hed
  · have hdvd : n ∣ d - e := (Nat.modEq_iff_dvd' hed).mp hmod
    have hdegree : e + n * ((d - e) / n) = d := by
      rw [mul_comm n, Nat.div_mul_cancel hdvd, Nat.add_sub_of_le hed]
    rw [RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_mul, RepresentationTheory.GeneralLinearGroup.TensorLocalization.auxiliaryPolynomialMap_pow, RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_auxiliaryPolynomial, hdet, hrename]
    have hdegree' : n * ((d - e) / n) + e = d := by
      simpa [Nat.add_comm] using hdegree
    rw [← pow_mul, ← mul_assoc, ← pow_add, hdegree']
  · have hde : d ≤ e := Nat.le_of_not_ge hed
    have hdvd : n ∣ e - d := (Nat.modEq_iff_dvd' hde).mp hmod.symm
    have hdegree : d + n * ((e - d) / n) = e := by
      rw [mul_comm n, Nat.div_mul_cancel hdvd, Nat.add_sub_of_le hde]
    rw [RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_mul, RepresentationTheory.GeneralLinearGroup.TensorLocalization.auxiliaryPolynomialMap_pow, RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_X_unit,
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


private def slExtensionPolynomial {k : Type*} [Field k]
    (n d : ℕ) (P : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k) :
    MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k :=
  let p := slEntryPolynomial n P
  ∑ e ∈ Finset.range (p.totalDegree + 1),
    if e ≡ d [MOD n] then
      normalizeSLComponent n d e (MvPolynomial.homogeneousComponent e p)
    else 0

private lemma eval_slExtensionPolynomial
    {k : Type*} [Field k] [CharZero k]
    {n d : ℕ} (hn : n ≠ 0) (hd : d < n)
    {zeta : k} (hzeta : IsPrimitiveRoot zeta n)
    (P : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k)
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
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s * Matrix.SpecialLinearGroup.toGL h)
        (slExtensionPolynomial n d P) =
      (s : k) ^ d * RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation (Matrix.SpecialLinearGroup.toGL h) P := by
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
  rw [RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation, map_sum]
  calc
    _ = ∑ e ∈ Finset.range (p.totalDegree + 1),
        if he : e ≡ d [MOD n] then
          (s : k) ^ d *
            MvPolynomial.eval x (MvPolynomial.homogeneousComponent e p)
        else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          split_ifs with hmod
          · rw [← RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation]
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
    _ = (s : k) ^ d * RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation (Matrix.SpecialLinearGroup.toGL h) P := by
      rw [eval_slEntryPolynomial]


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
      sigma (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarSpecialLinear s hs) = ((s : k) ^ d) • LinearMap.id) :
    (scalarSpecialMul (k := k) n).ker ≤ (scalarSpecialAction sigma d).toHomUnits.ker := by
  rintro ⟨s, h⟩ hx
  rw [MonoidHom.mem_ker] at hx ⊢
  change RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s * Matrix.SpecialLinearGroup.toGL h = 1 at hx
  have hdet := congrArg (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n) hx
  have hsunit : s ^ n = 1 := by
    simpa [map_mul, RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.detCharacter_specialLinear, RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.detCharacter_scalarMatrix] using hdet
  have hs : (s : k) ^ n = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hsunit
  have hsinv : ((s⁻¹ : kˣ) : k) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hsunit, inv_one]
    rfl
  have hh : h = RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarSpecialLinear s⁻¹ hsinv := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    have hto : Matrix.SpecialLinearGroup.toGL h = (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s)⁻¹ :=
      eq_inv_of_mul_eq_one_right hx
    rw [hto, RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarSpecialLinear_toGL]
    exact ((scalarGLHom n).map_inv s).symm
  apply Units.ext
  change ((s : k) ^ d) • sigma h = (1 : Module.End k Y)
  rw [hh, hscalar]
  ext v
  simp [← Units.val_pow_eq_pow_val]


private theorem exists_GLExtension_with_scalarWeight
    (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type*} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (hn : n ≠ 0)
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    ∃ (d : ℕ), d < n ∧
      ∃ rho : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y,
        RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.restrictToSpecialLinear rho = sigma ∧
        ∀ s : kˣ, rho (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s) = ((s : k) ^ d) • LinearMap.id := by
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
      change RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n 1 * Matrix.SpecialLinearGroup.toGL h =
        Matrix.SpecialLinearGroup.toGL h
      rw [show RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n 1 = 1 by exact (scalarGLHom n).map_one, one_mul]
    have hlift : lift (Matrix.SpecialLinearGroup.toGL h) = psi.toHomUnits (1, h) := by
      rw [← hphi1]
      simp [lift]
    change ((lift (Matrix.SpecialLinearGroup.toGL h) : (Module.End k Y)ˣ) :
      Module.End k Y) v = sigma h v
    rw [hlift]
    change (((1 : kˣ) : k) ^ d • sigma h) v = sigma h v
    simp
  · intro s
    have hphiS : phi (s, 1) = RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s := by
      change RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s * Matrix.SpecialLinearGroup.toGL 1 = RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s
      simp
    have hlift : lift (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s) = psi.toHomUnits (s, 1) := by
      rw [← hphiS]
      simp [lift]
    ext v
    change ((lift (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s) : (Module.End k Y)ˣ) : Module.End k Y) v = _
    rw [hlift]
    simp [psi, scalarSpecialAction]


/-- Establishes the property for a simple module with a special-linear-group representation. -/
theorem property_of_isSimpleModule
    (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type*} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    property n sigma := by
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


/-- Under module simplicity, derives the unprimed finite property from its primed counterpart. -/
theorem finiteProperty_of_finiteProperty'
    (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type*} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    (halg : finiteProperty' n sigma)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    finiteProperty n sigma := by
  rcases eq_or_ne n 0 with rfl | hn
  · let rho : Representation k (Matrix.GeneralLinearGroup (Fin 0) k) Y :=
      Representation.trivial k _ _
    have hres : RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.restrictToSpecialLinear rho = sigma := by
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
    simp [RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation]
  · obtain ⟨d, hd, rho, hres, hscalar⟩ :=
      exists_GLExtension_with_scalarWeight n k hn sigma
    obtain ⟨m, b, P, hP⟩ := halg
    letI : NeZero n := ⟨hn⟩
    obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
    let u : kˣ := (hzeta.isUnit hn).unit
    have hu : (u : k) = zeta := IsUnit.unit_spec _
    have hun : (u : k) ^ n = 1 := by rw [hu]; exact hzeta.pow_eq_one
    let Q : Fin m → Fin m → MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k :=
      fun a c => slExtensionPolynomial n d (P a c)
    refine ⟨rho, ⟨m, b, Q, ?_⟩, hres⟩
    intro g a c
    obtain ⟨s, h, rfl⟩ := RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.exists_scalarMatrix_mul_specialLinear hn g
    have hres_h : rho (Matrix.SpecialLinearGroup.toGL h) = sigma h := by
      have := DFunLike.congr_fun hres h
      exact this
    have hcoeff :
        b.repr
            (rho (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n s * Matrix.SpecialLinearGroup.toGL h) (b c)) a =
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
    let z : Matrix.SpecialLinearGroup (Fin n) k := RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarSpecialLinear uj hujn
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
      rw [← hres_z, show Matrix.SpecialLinearGroup.toGL z = RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.scalarMatrix k n uj by
        simp [z], hscalar uj, huj]
    rw [hzentries, eval_slEntryPolynomial, eval_slEntryPolynomial,
      ← hP (z * h) a c, ← hP h a c, map_mul, hzaction, Module.End.mul_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul, Finsupp.smul_apply,
      smul_eq_mul]


/-- Transforms this predicate into the second predicate on the same finite special-linear representation. -/
theorem finiteProperty.toFiniteProperty'
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y}
    (hσ : finiteProperty n σ) : finiteProperty' n σ := by
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  exact RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty.toFiniteLinearMapProperty hρ


/-- Transfers module simplicity from the derived special-linear representation to the general-linear representation. -/
theorem isSimpleModule_of_specialLinear
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    [hsl : IsSimpleModule (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k))
      (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.restrictToSpecialLinear ρ).asModule] :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have hsl' : Representation.IsIrreducible (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.restrictToSpecialLinear ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).2 hsl
  letI : Nontrivial Y :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.restrictToSpecialLinear ρ).asModule
  refine
    { exists_pair_ne := ⟨⊥, ⊤, by
        intro h
        have h' := congrArg Subrepresentation.toSubmodule h
        change (⊥ : Submodule k Y) = ⊤ at h'
        exact bot_ne_top h'⟩
      eq_bot_or_eq_top := fun S => ?_ }
  let T : Subrepresentation (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.restrictToSpecialLinear ρ) :=
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


/-- Under module simplicity, gives an equivalent representation from the displayed family. -/
theorem finiteProperty_exists_equiv
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    (hσ : finiteProperty n σ)
    [hsimp : IsSimpleModule (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) σ.asModule] :
    ∃ lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n,
      Nonempty (Representation.Equiv σ (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k))) := by
  obtain ⟨ρ, hρ, hres⟩ := hσ
  subst σ
  letI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule :=
    isSimpleModule_of_specialLinear ρ
  obtain ⟨lam, ⟨e⟩⟩ :=
    RepresentationTheory.AuxiliaryRepresentationDecompositions.auxiliary_exists_representationParameter_of_simple n k ρ hρ
  let E : Representation.Equiv ρ (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k) :=
    Representation.Equiv.mk (RepresentationTheory.Representation.ModuleEquivAndTraceSeparation.representationLinearEquiv e) (fun g => by
      ext v
      exact RepresentationTheory.Representation.ModuleEquivAndTraceSeparation.representationLinearEquiv_intertwines e g v)
  exact ⟨lam, ⟨RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.Equiv.restrictToSpecialLinear E⟩⟩


/-- Under module simplicity, gives an equivalent representation from the displayed family. -/
@[source_ref "Chapter5/Remark5.23.3" (role := supporting)]
theorem finiteProperty'_exists_equiv
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    (halg : finiteProperty' n sigma)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    ∃ lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n,
      Nonempty (Representation.Equiv sigma (RepresentationTheory.GeneralLinearGroup.SpecialLinearRestriction.Representation.restrictToSpecialLinear (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k))) := by
  exact finiteProperty_exists_equiv n k sigma
    (finiteProperty_of_finiteProperty' n k sigma halg)

end SpecialLinearRepresentation

end RepresentationTheory.Auxiliary.SpecialLinearRepresentation

