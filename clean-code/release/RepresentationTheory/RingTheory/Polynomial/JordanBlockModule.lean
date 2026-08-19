/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.Module.PID
import RepresentationTheory.LinearAlgebra.ModuleDecompositions

/-! # Jordan block modules -/

example (k : Type*) [Field k] : IsSimpleModule k k := inferInstance

/-- A simple vector space over its scalar field is linearly equivalent to that field. -/
@[source_ref "Chapter2/Example2.3.14" (role := primary)]
theorem RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.equiv_field_of_isSimpleModule
    (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    [IsSimpleModule k V] : Nonempty (V ≃ₗ[k] k) := by
  exact (Module.nonempty_linearEquiv_of_finrank_eq_one
    (isSimpleModule_iff_finrank_eq_one.mp (inferInstance : IsSimpleModule k V))).map
      LinearEquiv.symm

/-- An indecomposable vector space over a field is linearly equivalent to the field itself. -/
@[source_ref "Chapter2/Example2.3.14" (role := primary)]
theorem RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.equiv_field_of_isIndecomposableModule
    (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    (hV : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate k V) : Nonempty (V ≃ₗ[k] k) := by
  letI : Nontrivial V := hV.1
  haveI : IsSimpleModule k V := (isSimpleModule_iff k V).2 {
    eq_bot_or_eq_top := by
      intro W
      obtain ⟨P, hP⟩ := ComplementedLattice.exists_isCompl W
      rcases hV.2 W P hP with hW | hPbot
      · exact Or.inl hW
      · right
        have hsup : W ⊔ P = ⊤ := codisjoint_iff.mp hP.codisjoint
        simpa [hPbot] using hsup }
  exact RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.equiv_field_of_isSimpleModule k V

/-- Over an algebraically closed field, the quotient of the polynomial ring by a maximal ideal has dimension one. -/
@[source_ref "Chapter2/Example2.3.14" (role := primary)]
theorem RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.finrank_quotient_maximalIdeal (k : Type*) [Field k] [IsAlgClosed k]
    (I : Ideal (Polynomial k)) [hmax : I.IsMaximal] :
    Module.finrank k (Polynomial k ⧸ I) = 1 := by
  set p := Submodule.IsPrincipal.generator I
  have hI : I = Ideal.span {p} := by
    rw [← Ideal.submodule_span_eq]; exact (Submodule.IsPrincipal.span_singleton_generator I).symm
  rw [hI, finrank_quotient_span_eq_natDegree]
  have hne : p ≠ 0 := by
    intro h
    have hbot : I = ⊥ := by rw [hI, h, Ideal.span_singleton_eq_bot]
    rw [hbot] at hmax
    have hXtop : Ideal.span {(Polynomial.X : Polynomial k)} = ⊤ :=
      hmax.1.2 _ (bot_lt_iff_ne_bot.mpr (mt Ideal.span_singleton_eq_bot.mp
        Polynomial.X_ne_zero))
    exact (Polynomial.irreducible_X (R := k)).1 (Ideal.span_singleton_eq_top.mp hXtop)
  have hprime : (Ideal.span {p}).IsPrime := by rw [← hI]; exact hmax.isPrime
  rw [Ideal.span_singleton_prime hne] at hprime
  have hirr : Irreducible p := hprime.irreducible
  have hdeg : p.degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible (k := k) hirr
  rwa [Polynomial.degree_eq_natDegree hne, Nat.cast_eq_one] at hdeg

open Polynomial

namespace RepresentationTheory.RingTheory.Polynomial.JordanBlockModule

variable {k : Type*} [Field k]

/-- The nilpotent shift endomorphism on a finite coordinate space. -/
def jordanNilpotent (n : ℕ) : (Fin n → k) →ₗ[k] (Fin n → k) where
  toFun v i := if h : (i : ℕ) + 1 < n then v ⟨i + 1, h⟩ else 0
  map_add' u v := by funext i; dsimp; split <;> simp
  map_smul' c v := by funext i; dsimp; split <;> simp

/-- A coordinate evaluation formula for the nilpotent Jordan shift. -/
@[simp] lemma jordanNilpotent_coordinate_formula (n : ℕ) (v : Fin n → k) (i : Fin n) :
    jordanNilpotent n v i = if h : (i : ℕ) + 1 < n then v ⟨i + 1, h⟩ else 0 := rfl

/-- The linear endomorphism on finite coordinate space with a specified eigenvalue and nilpotent shift. -/
@[source_ref "Chapter2/Example2.3.14" (role := supporting)]
def jordanOperator (lam : k) (n : ℕ) : (Fin n → k) →ₗ[k] (Fin n → k) :=
  lam • LinearMap.id + jordanNilpotent n

/-- A coordinate evaluation formula for the Jordan operator. -/
@[simp, source_ref "Chapter2/Example2.3.14" (role := supporting)] lemma jordanOperator_coordinate_formula (lam : k) (n : ℕ) (v : Fin n → k) (i : Fin n) :
    jordanOperator lam n v i = lam * v i + (if h : (i : ℕ) + 1 < n then v ⟨i + 1, h⟩ else 0) := by
  simp [jordanOperator, jordanNilpotent]

/-- A boundary-coordinate formula for the nilpotent Jordan shift. -/
lemma jordanNilpotent_boundary_formula (n j : ℕ) (v : Fin n → k) (i : Fin n) :
    ((jordanNilpotent n) ^ j) v i = if h : (i : ℕ) + j < n then v ⟨i + j, h⟩ else 0 := by
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih (jordanNilpotent n v)]
    by_cases h : (i : ℕ) + (j + 1) < n
    · have h1 : (i : ℕ) + j < n := by omega
      rw [dif_pos h1]
      simp only [jordanNilpotent_coordinate_formula]
      have h2 : ((⟨(i : ℕ) + j, h1⟩ : Fin n) : ℕ) + 1 < n := by omega
      rw [dif_pos h2, dif_pos h]
      exact congrArg v (Fin.ext (by simp; omega))
    · rw [dif_neg (by omega : ¬ (i : ℕ) + (j + 1) < n)]
      by_cases h1 : (i : ℕ) + j < n
      · rw [dif_pos h1]
        simp only [jordanNilpotent_coordinate_formula]
        rw [dif_neg (show ¬ ((⟨(i : ℕ) + j, h1⟩ : Fin n) : ℕ) + 1 < n by omega)]
      · rw [dif_neg h1]

/-- The finite Jordan shift is nilpotent. -/
lemma jordanNilpotent_isNilpotent (n : ℕ) : IsNilpotent (jordanNilpotent n : (Fin n → k) →ₗ[k] (Fin n → k)) := by
  refine ⟨n, ?_⟩
  apply LinearMap.ext; intro v; funext i
  rw [jordanNilpotent_boundary_formula]
  rw [dif_neg (by omega : ¬ (i : ℕ) + n < n)]
  simp

/-- A distinguished eigenvector in a nonempty finite coordinate space. -/
def jordanEigenvector (n : ℕ) [NeZero n] : Fin n → k := Pi.single 0 1

/-- The distinguished eigenvector of a nonempty Jordan block is nonzero. -/
lemma jordanEigenvector_ne_zero (n : ℕ) [NeZero n] : (jordanEigenvector n : Fin n → k) ≠ 0 := by
  intro h
  have : (jordanEigenvector n : Fin n → k) 0 = (0 : Fin n → k) 0 := by rw [h]
  simp [jordanEigenvector, Pi.single_eq_same] at this

/-- The distinguished eigenvector has the specified eigenvalue under the Jordan operator. -/
lemma jordanOperator_jordanEigenvector (lam : k) (n : ℕ) [NeZero n] :
    jordanOperator lam n (jordanEigenvector n) = lam • (jordanEigenvector n : Fin n → k) := by
  funext i
  rw [jordanOperator_coordinate_formula]
  have hz : (if h : (i : ℕ) + 1 < n then (jordanEigenvector n : Fin n → k) ⟨i + 1, h⟩ else 0) = 0 := by
    split
    · apply Pi.single_eq_of_ne
      intro hh; rw [Fin.ext_iff] at hh; simp at hh
    · rfl
  rw [hz, add_zero]
  simp [Pi.smul_apply]

/-- The kernel of the nilpotent Jordan shift is contained in the span of the distinguished eigenvector. -/
lemma ker_jordanNilpotent_le_span_eigenvector (n : ℕ) [NeZero n] :
    LinearMap.ker (jordanNilpotent n) ≤ Submodule.span k {(jordanEigenvector n : Fin n → k)} := by
  intro v hv
  rw [LinearMap.mem_ker] at hv
  rw [Submodule.mem_span_singleton]
  refine ⟨v 0, ?_⟩
  funext j
  simp only [jordanEigenvector, Pi.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
  · have : j = 0 := Fin.ext hj
    simp [this]
  · rw [Pi.single_eq_of_ne (by intro h; rw [h] at hj; simp at hj), mul_zero]

    have hjlt : (j : ℕ) < n := j.isLt
    set i : Fin n := ⟨(j : ℕ) - 1, by omega⟩ with hi
    have hival : (i : ℕ) = (j : ℕ) - 1 := by rw [hi]
    have hlt : (i : ℕ) + 1 < n := by omega
    have hv' := congrFun hv i
    simp only [jordanNilpotent_coordinate_formula, Pi.zero_apply] at hv'
    rw [dif_pos hlt] at hv'
    have hidx : (⟨(i : ℕ) + 1, hlt⟩ : Fin n) = j := Fin.ext (by change (i : ℕ) + 1 = (j : ℕ); omega)
    rw [hidx] at hv'
    exact hv'.symm

/-- A nilpotent endomorphism of a nontrivial vector space has a nonzero vector in its kernel. -/
lemma exists_ne_zero_mem_ker_of_isNilpotent {N : Type*} [AddCommGroup N] [Module k N] [Nontrivial N]
    (g : N →ₗ[k] N) (hg : IsNilpotent g) : ∃ u : N, u ≠ 0 ∧ g u = 0 := by
  by_contra h
  rw [not_exists] at h
  simp only [not_and] at h

  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hxne
    exact h x hxne (LinearMap.mem_ker.mp hx)
  obtain ⟨m, hm⟩ := hg
  have hpow : ∀ j, Function.Injective ⇑((g ^ j : Module.End k N)) := by
    intro j
    induction j with
    | zero => intro a b hab; simpa using hab
    | succ j ih =>
      rw [pow_succ]
      intro a b hab
      exact hinj (ih (by simpa only [Module.End.mul_apply] using hab))
  have hzero := hpow m
  rw [hm] at hzero
  obtain ⟨a, b, hab⟩ := exists_pair_ne N
  exact hab (hzero (by simp))

/-- Every nonzero subspace invariant under a Jordan operator contains its distinguished eigenvector. -/
lemma jordanEigenvector_mem_of_invariant (lam : k) (n : ℕ) [NeZero n] {W : Submodule k (Fin n → k)}
    (hW : W ≠ ⊥) (hinv : ∀ m ∈ W, jordanOperator lam n m ∈ W) :
    (jordanEigenvector n : Fin n → k) ∈ W := by

  have hshift : Set.MapsTo (jordanNilpotent n) (W : Set (Fin n → k)) (W : Set (Fin n → k)) := by
    intro m hm
    have hsub : jordanNilpotent n m = jordanOperator lam n m - lam • m := by
      have : jordanOperator lam n m = lam • m + jordanNilpotent n m := by simp [jordanOperator]
      rw [this]; abel
    rw [hsub]
    exact W.sub_mem (hinv m hm) (W.smul_mem lam hm)
  have hnil : IsNilpotent ((jordanNilpotent n).restrict hshift) :=
    Module.End.isNilpotent.restrict hshift (jordanNilpotent_isNilpotent n)
  have hnontriv : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨u, hune, hu0⟩ := exists_ne_zero_mem_ker_of_isNilpotent ((jordanNilpotent n).restrict hshift) hnil

  have hu0' : jordanNilpotent n (u : Fin n → k) = 0 := by
    have := congrArg (Subtype.val) hu0
    rwa [LinearMap.restrict_apply] at this
  have huker : (u : Fin n → k) ∈ Submodule.span k {(jordanEigenvector n : Fin n → k)} :=
    ker_jordanNilpotent_le_span_eigenvector n (LinearMap.mem_ker.mpr hu0')
  rw [Submodule.mem_span_singleton] at huker
  obtain ⟨c, hc⟩ := huker
  have hcne : c ≠ 0 := by
    rintro rfl
    apply hune
    apply Subtype.ext
    simpa using hc.symm

  have : (jordanEigenvector n : Fin n → k) = c⁻¹ • (u : Fin n → k) := by
    rw [← hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  rw [this]
  exact W.smul_mem c⁻¹ u.2

/-- The polynomial module associated to a scalar parameter and a natural-number block size. -/
@[source_ref "Chapter2/Example2.3.14" (role := supporting)]
abbrev JordanBlockModule (lam : k) (n : ℕ) := Module.AEval' (jordanOperator lam n)

/-- A Jordan-block module of nonzero size is nontrivial. -/
instance jordanBlockModule_nontrivial (lam : k) (n : ℕ) [NeZero n] :
    Nontrivial (JordanBlockModule lam n) :=
  (Module.AEval'.of (jordanOperator lam n)).symm.toEquiv.nontrivial

/-- Every nonempty Jordan-block module is indecomposable. -/
@[source_ref "Chapter2/Example2.3.14" (role := primary)]
theorem jordanBlockModule_isIndecomposable (lam : k) (n : ℕ) [NeZero n] :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate (Polynomial k) (JordanBlockModule lam n) := by
  set φ := jordanOperator lam n with hφ
  set of := Module.AEval'.of φ with hof
  refine ⟨inferInstance, ?_⟩
  intro N P hcompl
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hN, hP⟩ := hcon

  have invar : ∀ Q : Submodule (Polynomial k) (JordanBlockModule lam n),
      ∀ m : Fin n → k, of m ∈ Q → φ m ∈
        ((Q.restrictScalars k).comap (of : (Fin n → k) →ₗ[k] JordanBlockModule lam n)) := by
    intro Q m hm
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
    have : (Polynomial.X : Polynomial k) • of m ∈ Q := Q.smul_mem _ hm
    rwa [Module.AEval'.X_smul_of] at this

  have e0mem : ∀ Q : Submodule (Polynomial k) (JordanBlockModule lam n), Q ≠ ⊥ →
      of (jordanEigenvector n) ∈ Q := by
    intro Q hQ
    set W : Submodule k (Fin n → k) :=
      (Q.restrictScalars k).comap (of : (Fin n → k) →ₗ[k] JordanBlockModule lam n) with hW
    have hWmem : ∀ m : Fin n → k, m ∈ W ↔ of m ∈ Q := fun m => Iff.rfl
    have hWbot : W ≠ ⊥ := by
      rw [Submodule.ne_bot_iff] at hQ ⊢
      obtain ⟨x, hxQ, hxne⟩ := hQ
      refine ⟨of.symm x, ?_, ?_⟩
      · rw [hWmem]; simpa using hxQ
      · exact (map_ne_zero_iff of.symm of.symm.injective).mpr hxne
    have hinv : ∀ m ∈ W, φ m ∈ W := by
      intro m hm
      rw [hWmem] at hm ⊢
      exact invar Q m hm
    have := jordanEigenvector_mem_of_invariant lam n hWbot hinv
    rwa [hWmem] at this
  have hNe : of (jordanEigenvector n) ∈ N := e0mem N hN
  have hPe : of (jordanEigenvector n) ∈ P := e0mem P hP
  have : of (jordanEigenvector n) ∈ N ⊓ P := Submodule.mem_inf.mpr ⟨hNe, hPe⟩
  rw [hcompl.inf_eq_bot] at this
  rw [Submodule.mem_bot] at this
  exact (map_ne_zero_iff of of.injective).mpr (jordanEigenvector_ne_zero n) this

/-- A Jordan-block module of size at least two is not simple. -/
theorem jordanBlockModule_not_isSimpleModule (lam : k) (n : ℕ) (hn : 2 ≤ n) :
    ¬ IsSimpleModule (Polynomial k) (JordanBlockModule lam n) := by
  haveI : NeZero n := ⟨by omega⟩
  set φ := jordanOperator lam n with hφ
  set of := Module.AEval'.of φ with hof
  intro hsimp
  haveI := hsimp

  set Q := Submodule.span (Polynomial k) {(of (jordanEigenvector n) : JordanBlockModule lam n)} with hQ
  have hQbot : Q ≠ ⊥ := by
    rw [hQ, Ne, Submodule.span_singleton_eq_bot]
    exact (map_ne_zero_iff of of.injective).mpr (jordanEigenvector_ne_zero n)
  have hQtop : Q = ⊤ := (eq_bot_or_eq_top Q).resolve_left hQbot

  set e1 : Fin n → k := Pi.single ⟨1, hn⟩ 1 with he1
  have he1mem : of e1 ∈ Q := hQtop ▸ Submodule.mem_top
  rw [hQ, Submodule.mem_span_singleton] at he1mem
  obtain ⟨a, ha⟩ := he1mem

  have hsmul : a • of (jordanEigenvector n) = of (a.eval lam • jordanEigenvector n) := by
    rw [← Module.AEval.of_aeval_smul]
    congr 1
    exact Module.End.aeval_apply_of_mem_apply_eq_smul (jordanOperator_jordanEigenvector lam n)
  rw [hsmul] at ha
  have hvec : a.eval lam • jordanEigenvector n = e1 := of.injective ha

  have := congrFun hvec ⟨1, hn⟩
  rw [he1, Pi.single_eq_same] at this
  simp only [jordanEigenvector, Pi.smul_apply, smul_eq_mul] at this
  rw [Pi.single_eq_of_ne (by intro h; rw [Fin.ext_iff] at h; simp at h)] at this
  simp at this

/-- The size-two Jordan block with parameter zero is indecomposable but not simple. -/
@[source_ref "Chapter2/Discussion_2.1_irreducible_indecomposable/Derived4" (role := primary),
  source_ref "Chapter2/Discussion_irreducible_vs_indecomposable/Derived2" (role := supporting),
  source_ref "Chapter2/Example2.3.14" (role := primary)]
theorem isIndecomposableModule_and_not_isSimpleModule_jordanBlock_two :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate (Polynomial k) (JordanBlockModule (0 : k) 2) ∧
      ¬ IsSimpleModule (Polynomial k) (JordanBlockModule (0 : k) 2) :=
  ⟨jordanBlockModule_isIndecomposable 0 2, jordanBlockModule_not_isSimpleModule 0 2 le_rfl⟩

/-- A distinguished cyclic vector in a nonempty finite coordinate space. -/
def jordanCyclicVector (n : ℕ) [NeZero n] : Fin n → k :=
  Pi.single ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne n)) one_pos⟩ 1

/-- A power of the nilpotent Jordan shift sends the cyclic vector to the corresponding standard basis vector. -/
lemma jordanNilpotent_pow_jordanCyclicVector (n : ℕ) [NeZero n] {j : ℕ} (hj : j < n) :
    ((jordanNilpotent n) ^ j) (jordanCyclicVector n : Fin n → k) = Pi.single ⟨n - 1 - j, by omega⟩ 1 := by
  funext i
  rw [jordanNilpotent_boundary_formula]
  by_cases h : (i : ℕ) + j < n
  · rw [dif_pos h]
    simp only [jordanCyclicVector, Pi.single_apply, Fin.ext_iff]
    have : ((i : ℕ) + j = n - 1) ↔ ((i : ℕ) = n - 1 - j) := by omega
    simp [this]
  · rw [dif_neg h]
    symm
    simp only [Pi.single_apply, Fin.ext_iff]
    rw [if_neg (by omega)]

/-- Evaluating the polynomial variable shifted by the Jordan parameter at the Jordan operator gives its nilpotent part. -/
lemma aeval_jordanOperator_sub_self (lam : k) (n : ℕ) :
    Polynomial.aeval (jordanOperator lam n) (X - C lam) = jordanNilpotent n := by
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  ext v i
  simp [jordanOperator, Module.algebraMap_end_apply]

/-- The dimension of a Jordan-block module is its size. -/
@[simp] lemma finrank_jordanBlock (lam : k) (n : ℕ) :
    Module.finrank k (JordanBlockModule lam n) = n := by
  rw [← (Module.AEval'.of (jordanOperator lam n)).finrank_eq]
  simp

/-- The polynomial-linear map obtained by evaluating at a Jordan operator and applying the result to its cyclic vector. -/
noncomputable def polynomialToJordanBlock (lam : k) (n : ℕ) [NeZero n] :
    Polynomial k →ₗ[Polynomial k] JordanBlockModule lam n :=
  LinearMap.toSpanSingleton (Polynomial k) (JordanBlockModule lam n)
    (Module.AEval'.of (jordanOperator lam n) (jordanCyclicVector n))

/-- The generator map evaluates a polynomial at the Jordan operator and applies it to the cyclic vector. -/
lemma polynomialToJordanBlock_apply (lam : k) (n : ℕ) [NeZero n] (q : Polynomial k) :
    polynomialToJordanBlock lam n q
      = Module.AEval'.of (jordanOperator lam n) (Polynomial.aeval (jordanOperator lam n) q (jordanCyclicVector n)) :=
  rfl

/-- The generator map sends a power of the shifted variable to the same power of the nilpotent part applied to the cyclic vector. -/
lemma polynomialToJordanBlock_pow_sub (lam : k) (n : ℕ) [NeZero n] (j : ℕ) :
    polynomialToJordanBlock lam n ((X - C lam) ^ j)
      = Module.AEval'.of (jordanOperator lam n) (((jordanNilpotent n) ^ j) (jordanCyclicVector n)) := by
  rw [polynomialToJordanBlock_apply, map_pow, aeval_jordanOperator_sub_self]

/-- The nilpotent Jordan shift raised to the dimension of its coordinate space is zero. -/
lemma jordanNilpotent_pow_eq_zero (n : ℕ) : ((jordanNilpotent n : (Fin n → k) →ₗ[k] (Fin n → k)) ^ n) = 0 := by
  apply LinearMap.ext; intro v; funext i
  rw [jordanNilpotent_boundary_formula, dif_neg (by omega : ¬ (i : ℕ) + n < n)]
  simp

/-- The generator map sends the defining power of the shifted variable to zero. -/
lemma polynomialToJordanBlock_pow_sub_eq_zero (lam : k) (n : ℕ) [NeZero n] :
    polynomialToJordanBlock lam n ((X - C lam) ^ n) = 0 := by
  rw [polynomialToJordanBlock_pow_sub, jordanNilpotent_pow_eq_zero]
  simp

/-- The polynomial generator map onto a nonempty Jordan block is surjective. -/
lemma polynomialToJordanBlock_surjective (lam : k) (n : ℕ) [NeZero n] :
    Function.Surjective (polynomialToJordanBlock lam n) := by
  set of := Module.AEval'.of (jordanOperator lam n) with hof

  have hbasis : ∀ i : Fin n,
      of (Pi.single i 1) ∈ LinearMap.range (polynomialToJordanBlock lam n) := by
    intro i
    have hi := i.isLt
    refine ⟨(X - C lam) ^ (n - 1 - (i : ℕ)), ?_⟩
    rw [polynomialToJordanBlock_pow_sub, jordanNilpotent_pow_jordanCyclicVector n (by omega)]
    have hidx : (⟨n - 1 - (n - 1 - (i : ℕ)), by omega⟩ : Fin n) = i :=
      Fin.ext (show n - 1 - (n - 1 - (i : ℕ)) = (i : ℕ) by omega)
    rw [hidx]

  have hspan : Submodule.span k (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → k)) = ⊤ := by
    rw [show (fun i : Fin n => (Pi.single i 1 : Fin n → k)) = ⇑(Pi.basisFun k (Fin n)) from
      funext fun i => (Pi.basisFun_apply k (Fin n) i).symm]
    exact (Pi.basisFun k (Fin n)).span_eq
  have htop : (⊤ : Submodule k (Fin n → k)) ≤
      Submodule.comap (of : (Fin n → k) →ₗ[k] JordanBlockModule lam n)
        ((LinearMap.range (polynomialToJordanBlock lam n)).restrictScalars k) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hbasis i
  intro y
  have := htop (Submodule.mem_top (x := of.symm y))
  rw [Submodule.mem_comap] at this
  simpa using this

/-- The quotient of the polynomial ring by the ideal generated by a power of a shifted variable is linearly equivalent to the associated Jordan-block module. -/
noncomputable def quotientSpanPowSubEquivJordanBlock (lam : k) (n : ℕ) [NeZero n] :
    (Polynomial k ⧸ Ideal.span {(X - C lam) ^ n}) ≃ₗ[Polynomial k] JordanBlockModule lam n := by
  haveI : Module.Finite k (Polynomial k ⧸ Ideal.span {(X - C lam) ^ n}) :=
    ((monic_X_sub_C lam).pow n).finite_quotient
  have hle : Ideal.span {(X - C lam) ^ n} ≤ LinearMap.ker (polynomialToJordanBlock lam n) := by
    rw [Ideal.span_le]
    rintro _ rfl
    exact polynomialToJordanBlock_pow_sub_eq_zero lam n
  refine LinearEquiv.ofBijective (Submodule.liftQ _ (polynomialToJordanBlock lam n) hle) ⟨?_, ?_⟩
  ·
    have hdim : Module.finrank k (Polynomial k ⧸ Ideal.span {(X - C lam) ^ n})
        = Module.finrank k (JordanBlockModule lam n) := by
      rw [finrank_quotient_span_eq_natDegree, finrank_jordanBlock]
      simp [Polynomial.natDegree_pow]
    have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := k) hdim
      (f := (Submodule.liftQ _ (polynomialToJordanBlock lam n) hle).restrictScalars k)).2
    exact this (fun y => by
      obtain ⟨q, hq⟩ := polynomialToJordanBlock_surjective lam n y
      exact ⟨Submodule.Quotient.mk q, hq⟩)
  · intro y
    obtain ⟨q, hq⟩ := polynomialToJordanBlock_surjective lam n y
    exact ⟨Submodule.Quotient.mk q, hq⟩

/-- Module indecomposability is transported across a linear equivalence. -/
lemma isIndecomposableModule_of_linearEquiv {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate R M) :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate R N := by
  haveI := h.1
  refine ⟨e.symm.toEquiv.nontrivial, fun A B hAB => ?_⟩
  set f := Submodule.orderIsoMapComap e with hf
  rcases h.2 (f.symm A) (f.symm B) (f.symm.isCompl hAB) with hbot | hbot
  · exact Or.inl (by rw [← f.apply_symm_apply A, hbot, f.map_bot])
  · exact Or.inr (by rw [← f.apply_symm_apply B, hbot, f.map_bot])

/-- An indecomposable module equivalent to a finite dependent product is equivalent to one of its components. -/
lemma equiv_component_of_isIndecomposableModule {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Finite ι] (φ : ι → Type*) [∀ i, AddCommGroup (φ i)] [∀ i, Module R (φ i)]
    (e : M ≃ₗ[R] ∀ i, φ i) (h : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate R M) :
    ∃ i, Nonempty (M ≃ₗ[R] φ i) := by
  classical
  haveI := h.1
  have hind : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate R (∀ i, φ i) := isIndecomposableModule_of_linearEquiv e h
  haveI := hind.1
  set P : ι → Submodule R (∀ i, φ i) := fun i => LinearMap.range (LinearMap.single R φ i) with hP
  have hsup : ⨆ i, P i = ⊤ := LinearMap.iSup_range_single R φ

  obtain ⟨i₀, hi₀⟩ : ∃ i, P i ≠ ⊥ := by
    by_contra hcon
    have hcon' : ∀ i, P i = ⊥ := fun i => not_not.mp fun hne => hcon ⟨i, hne⟩
    exact top_ne_bot (α := Submodule R (∀ i, φ i)) (by rw [← hsup]; simp [hcon'])

  have hcompl : IsCompl (P i₀) (⨆ i ∈ ({i₀}ᶜ : Set ι), P i) := by
    constructor
    · have hd := LinearMap.disjoint_single_single R φ {i₀} {i₀}ᶜ disjoint_compl_right
      rwa [iSup_singleton] at hd
    · rw [codisjoint_iff, eq_top_iff, ← hsup]
      refine iSup_le fun i => ?_
      by_cases hi : i = i₀
      · exact hi ▸ le_sup_left
      · exact le_sup_of_le_right (le_biSup P hi)
  rcases hind.2 _ _ hcompl with hbot | hbot
  · exact absurd hbot hi₀

  have htop : P i₀ = ⊤ := by
    have := hcompl.sup_eq_top
    rwa [hbot, sup_bot_eq] at this
  refine ⟨i₀, ⟨e.trans (LinearEquiv.ofBijective (LinearMap.single R φ i₀) ⟨?_, ?_⟩).symm⟩⟩
  · rw [← LinearMap.ker_eq_bot]; exact LinearMap.ker_single R φ i₀
  · rw [← LinearMap.range_eq_top]; exact htop

section Converse

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (Polynomial k) M]
  [IsScalarTower k (Polynomial k) M]

/-- Every finite-dimensional vector space carrying a compatible polynomial-module structure is torsion as a polynomial module. -/
lemma polynomialModule_isTorsion [FiniteDimensional k M] :
    Module.IsTorsion (Polynomial k) M := by
  intro m
  have hnotinj : ¬ Function.Injective
      ((LinearMap.toSpanSingleton (Polynomial k) M m).restrictScalars k) := fun hinj =>
    Polynomial.not_finite (Module.Finite.of_injective _ hinj)
  rw [← LinearMap.ker_eq_bot] at hnotinj
  obtain ⟨q, hq, hqne⟩ := (Submodule.ne_bot_iff _).mp hnotinj
  exact ⟨⟨q, mem_nonZeroDivisors_of_ne_zero hqne⟩, LinearMap.mem_ker.mp hq⟩

/-- A finite-dimensional polynomial module over an algebraically closed field is equivalent to a finite product of nonempty Jordan blocks. -/
@[source_ref "Chapter2/Example2.3.14" (role := primary)]
theorem exists_equiv_pi_jordanBlock [IsAlgClosed k] [FiniteDimensional k M] :
    ∃ (m : ℕ) (lam : Fin m → k) (n : Fin m → ℕ),
      (∀ i, 0 < n i) ∧
        Nonempty (M ≃ₗ[Polynomial k] ∀ i : Fin m, JordanBlockModule (lam i) (n i)) := by
  classical
  let R := Polynomial k
  haveI : Module.Finite R M := Module.Finite.of_restrictScalars_finite k R M
  obtain ⟨ι, instι, p, hp, expo, ⟨estr⟩⟩ :=
    Module.equiv_directSum_of_isTorsion (polynomialModule_isTorsion (k := k) M)
  letI : Fintype ι := instι
  let I := {i : ι // 0 < expo i}
  let Q : ι → Type _ := fun i => R ⧸ (R ∙ p i ^ expo i)

  let dropZero : (∀ i : ι, Q i) ≃ₗ[R] ∀ i : I, Q i := {
    toFun := fun f i => f i
    invFun := fun f i => if hi : 0 < expo i then f ⟨i, hi⟩ else 0
    left_inv := by
      intro f
      funext i
      by_cases hi : 0 < expo i
      · simp [hi]
      · have hzero : expo i = 0 := Nat.eq_zero_of_not_pos hi
        haveI : Subsingleton (Q i) := by
          dsimp [Q]
          rw [hzero, pow_zero, Ideal.submodule_span_eq, Ideal.span_singleton_one]
          infer_instance
        exact Subsingleton.elim _ _
    right_inv := by
      intro f
      funext i
      change (if hi : 0 < expo (i : ι) then f ⟨i, hi⟩ else 0) = f i
      rw [dif_pos i.property]
    map_add' := by intro f g; rfl
    map_smul' := by intro c f; rfl }

  have hassoc : ∀ i : I, ∃ lam : k, Associated (X - C lam) (p i) := by
    intro i
    have hdeg : (p i).degree ≠ 0 := fun hd =>
      (hp i).not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr hd)
    obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_root (p i) hdeg
    exact ⟨lam, (Polynomial.irreducible_X_sub_C lam).associated_of_dvd (hp i)
      (Polynomial.dvd_iff_isRoot.mpr hlam)⟩
  choose lam hlam using hassoc
  let blockEquiv : ∀ i : I, Q i ≃ₗ[R] JordanBlockModule (lam i) (expo i) := fun i => by
    letI : NeZero (expo i) := ⟨Nat.ne_of_gt i.property⟩
    refine (Submodule.quotEquivOfEq _ _ ?_).trans (quotientSpanPowSubEquivJordanBlock (lam i) (expo i))
    rw [Ideal.submodule_span_eq]
    exact Ideal.span_singleton_eq_span_singleton.mpr
      ((hlam i).pow_pow (n := expo i)).symm
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, lam ∘ e, fun i => expo (e i), fun i => (e i).property, ?_⟩
  exact ⟨estr.trans (DirectSum.linearEquivFunOnFintype R ι Q) |>.trans dropZero |>.trans
    (LinearEquiv.piCongrRight blockEquiv) |>.trans
    (LinearEquiv.piCongrLeft R (fun i : I => JordanBlockModule (lam i) (expo i)) e).symm⟩

/-- A finite-dimensional indecomposable polynomial module over an algebraically closed field is linearly equivalent to a nonempty Jordan block. -/
@[source_ref "Chapter2/Example2.3.14" (role := primary)]
theorem equiv_jordanBlock_of_isIndecomposableModule [IsAlgClosed k] [FiniteDimensional k M]
    (h : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate (Polynomial k) M) :
    ∃ (lam : k) (n : ℕ), 0 < n ∧ Nonempty (M ≃ₗ[Polynomial k] JordanBlockModule lam n) := by
  classical
  haveI := h.1
  haveI : Module.Finite (Polynomial k) M := Module.Finite.of_restrictScalars_finite k _ _

  obtain ⟨ι, _, p, hp, expo, ⟨estr⟩⟩ :=
    Module.equiv_directSum_of_isTorsion (polynomialModule_isTorsion (k := k) M)

  obtain ⟨i, ⟨eqi⟩⟩ := equiv_component_of_isIndecomposableModule _
    (estr.trans (DirectSum.linearEquivFunOnFintype _ _ _)) h

  have hdeg : (p i).degree ≠ 0 := fun hd =>
    (hp i).not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr hd)
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_root (p i) hdeg
  have hassoc : Associated (X - C lam) (p i) :=
    (Polynomial.irreducible_X_sub_C lam).associated_of_dvd (hp i)
      (Polynomial.dvd_iff_isRoot.mpr hlam)

  have hpos : 0 < expo i := by
    rcases Nat.eq_zero_or_pos (expo i) with h0 | h0
    · exfalso
      have : Subsingleton (Polynomial k ⧸ (Polynomial k) ∙ p i ^ expo i) := by
        rw [h0, pow_zero, Ideal.submodule_span_eq, Ideal.span_singleton_one]
        infer_instance
      exact not_subsingleton M (eqi.toEquiv.subsingleton)
    · exact h0
  haveI : NeZero (expo i) := ⟨by omega⟩
  refine ⟨lam, expo i, hpos, ⟨eqi.trans ((Submodule.quotEquivOfEq _ _ ?_).trans
    (quotientSpanPowSubEquivJordanBlock lam (expo i)))⟩⟩
  rw [Ideal.submodule_span_eq]
  exact Ideal.span_singleton_eq_span_singleton.mpr (hassoc.pow_pow (n := expo i)).symm

end Converse

/-- Evaluating a shifted polynomial variable at a Jordan operator splits into a scalar map and the nilpotent part. -/
lemma aeval_jordanOperator_sub (lam mu : k) (n : ℕ) :
    Polynomial.aeval (jordanOperator mu n) (X - C lam)
      = (mu - lam) • (1 : Module.End k (Fin n → k)) + jordanNilpotent n := by
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  ext v i
  simp [jordanOperator, Module.algebraMap_end_apply, sub_smul]
  ring

/-- The defining power of the shifted polynomial variable annihilates every vector in the corresponding Jordan-block module. -/
lemma pow_sub_smul_jordanBlock_eq_zero (lam : k) (n : ℕ) (v : JordanBlockModule lam n) :
    ((X - C lam) ^ n : Polynomial k) • v = 0 := by
  obtain ⟨w, rfl⟩ := (Module.AEval'.of (jordanOperator lam n)).surjective v
  have hsmul : ((X - C lam) ^ n : Polynomial k) • (Module.AEval'.of (jordanOperator lam n) w)
      = Module.AEval'.of (jordanOperator lam n)
        (Polynomial.aeval (jordanOperator lam n) ((X - C lam) ^ n) w) := rfl
  rw [hsmul, map_pow, aeval_jordanOperator_sub_self, jordanNilpotent_pow_eq_zero]
  simp

/-- Two nonempty Jordan-block modules are linearly equivalent exactly when their parameters and sizes agree. -/
@[source_ref "Chapter2/Example2.3.14" (role := primary)]
theorem jordanBlockModule_equiv_iff (lam mu : k) (n m : ℕ) [NeZero n] [NeZero m] :
    Nonempty (JordanBlockModule lam n ≃ₗ[Polynomial k] JordanBlockModule mu m) ↔ lam = mu ∧ n = m := by
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ ⟨LinearEquiv.refl _ _⟩⟩
  have hnm : n = m := by
    have h := (e.restrictScalars k).finrank_eq
    rwa [finrank_jordanBlock, finrank_jordanBlock] at h
  refine ⟨?_, hnm⟩
  by_contra hne

  have hop : Polynomial.aeval (jordanOperator mu m) ((X - C lam) ^ n) = 0 := by
    apply LinearMap.ext
    intro w
    have h := pow_sub_smul_jordanBlock_eq_zero lam n (e.symm (Module.AEval'.of (jordanOperator mu m) w))
    have h2 := congrArg e h
    rw [map_smul, e.apply_symm_apply, map_zero] at h2
    exact (map_eq_zero_iff _ (Module.AEval'.of (jordanOperator mu m)).injective).mp h2

  set A := Polynomial.aeval (jordanOperator mu m) (X - C lam) with hA
  have hAnil : IsNilpotent A := ⟨n, by rw [hA, ← map_pow]; exact hop⟩
  have hAeq : A = (mu - lam) • (1 : Module.End k (Fin m → k)) + jordanNilpotent m :=
    aeval_jordanOperator_sub lam mu m
  have hcomm : Commute A (jordanNilpotent m) := by
    rw [hAeq]
    exact Commute.add_left ((Commute.one_left _).smul_left _) (Commute.refl _)
  have hscal : IsNilpotent ((mu - lam) • (1 : Module.End k (Fin m → k))) := by
    have := hcomm.isNilpotent_sub hAnil (jordanNilpotent_isNilpotent m)
    rwa [hAeq, add_sub_cancel_right] at this

  obtain ⟨j, hj⟩ := hscal
  rw [smul_pow, one_pow] at hj
  have hvec : ((mu - lam) ^ j) • (jordanEigenvector m : Fin m → k) = 0 := by
    have := congrArg (fun f : Module.End k (Fin m → k) => f (jordanEigenvector m)) hj
    simpa using this
  have hpow : (mu - lam) ^ j = 0 := (smul_eq_zero.mp hvec).resolve_right (jordanEigenvector_ne_zero m)
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · rw [hj0, pow_zero] at hpow; exact one_ne_zero hpow
  · exact hne (by have := pow_eq_zero_iff (n := j) (by omega) |>.mp hpow; linear_combination -this)

attribute [nolint defsWithUnderscore]
  jordanNilpotent jordanOperator jordanEigenvector JordanBlockModule jordanCyclicVector polynomialToJordanBlock quotientSpanPowSubEquivJordanBlock

end RepresentationTheory.RingTheory.Polynomial.JordanBlockModule
