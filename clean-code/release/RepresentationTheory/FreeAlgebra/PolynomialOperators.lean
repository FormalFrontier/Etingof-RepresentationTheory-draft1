/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.CharP.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Polynomial operator algebra -/

namespace RepresentationTheory.FreeAlgebra.PolynomialOperators

variable (k : Type*) [CommRing k]

/-- An auxiliary indexing type. -/
abbrev AuxiliaryIndex := Fin 2

/-- An auxiliary element of the free algebra on the indexing type. -/
noncomputable abbrev auxiliaryFreeAlgebraElement : FreeAlgebra k AuxiliaryIndex := FreeAlgebra.ι k (0 : Fin 2)

/-- A second auxiliary element of the free algebra on the indexing type. -/
noncomputable abbrev auxiliaryFreeAlgebraElement' : FreeAlgebra k AuxiliaryIndex := FreeAlgebra.ι k (1 : Fin 2)

/-- An auxiliary binary relation on the free algebra. -/
def auxiliaryRelation : FreeAlgebra k AuxiliaryIndex → FreeAlgebra k AuxiliaryIndex → Prop :=
  fun a b => a = auxiliaryFreeAlgebraElement' k * auxiliaryFreeAlgebraElement k ∧ b = auxiliaryFreeAlgebraElement k * auxiliaryFreeAlgebraElement' k + 1

/-- An auxiliary type associated with a commutative ring. -/
@[source_ref "Chapter2/Discussion_2.7_intro" (role := supporting)]
noncomputable abbrev AuxiliaryAlgebra : Type _ := RingQuot (auxiliaryRelation k)

/-- The algebra homomorphism from the free algebra into the operator algebra. -/
noncomputable def AuxiliaryAlgebra.fromFreeAlgebra : FreeAlgebra k AuxiliaryIndex →ₐ[k] AuxiliaryAlgebra k :=
  RingQuot.mkAlgHom k (auxiliaryRelation k)

/-- The first distinguished element of the operator algebra. -/
noncomputable def AuxiliaryAlgebra.firstOperator : AuxiliaryAlgebra k := AuxiliaryAlgebra.fromFreeAlgebra k (auxiliaryFreeAlgebraElement k)

/-- The second distinguished element of the operator algebra. -/
noncomputable def AuxiliaryAlgebra.secondOperator : AuxiliaryAlgebra k := AuxiliaryAlgebra.fromFreeAlgebra k (auxiliaryFreeAlgebraElement' k)

/-- An element of the auxiliary algebra indexed by two natural numbers. -/
noncomputable def AuxiliaryAlgebra.indexedElement (i j : ℕ) : AuxiliaryAlgebra k :=
  AuxiliaryAlgebra.firstOperator k ^ i * AuxiliaryAlgebra.secondOperator k ^ j

/-- The distinguished operators satisfy the displayed commutation relation. -/
@[source_ref "Chapter2/Discussion_2.7_intro" (role := supporting)]
lemma AuxiliaryAlgebra.secondOperator_mul_firstOperator :
    AuxiliaryAlgebra.secondOperator k * AuxiliaryAlgebra.firstOperator k = AuxiliaryAlgebra.firstOperator k * AuxiliaryAlgebra.secondOperator k + 1 := by
  have h := RingQuot.mkAlgHom_rel k
    (show auxiliaryRelation k (auxiliaryFreeAlgebraElement' k * auxiliaryFreeAlgebraElement k) (auxiliaryFreeAlgebraElement k * auxiliaryFreeAlgebraElement' k + 1) from ⟨rfl, rfl⟩)
  simp only [map_mul, map_add, map_one] at h
  exact h

private noncomputable abbrev monomialSpan : Submodule k (AuxiliaryAlgebra k) :=
  Submodule.span k (Set.range (fun p : ℕ × ℕ => AuxiliaryAlgebra.indexedElement k p.1 p.2))

private lemma indexedElement_mem_span (i j : ℕ) : AuxiliaryAlgebra.indexedElement k i j ∈ monomialSpan k :=
  Submodule.subset_span ⟨(i, j), rfl⟩

private lemma firstOperator_mul_mem_span {a : AuxiliaryAlgebra k} (ha : a ∈ monomialSpan k) :
    AuxiliaryAlgebra.firstOperator k * a ∈ monomialSpan k := by
  apply Submodule.span_induction
    (p := fun a (_ : a ∈ monomialSpan k) => AuxiliaryAlgebra.firstOperator k * a ∈ monomialSpan k)
  · intro z hz
    obtain ⟨⟨i, j⟩, rfl⟩ := hz
    have : AuxiliaryAlgebra.firstOperator k * AuxiliaryAlgebra.indexedElement k i j = AuxiliaryAlgebra.indexedElement k (i + 1) j := by
      simp only [AuxiliaryAlgebra.indexedElement, pow_succ', mul_assoc]
    rw [this]; exact indexedElement_mem_span k (i + 1) j
  · rw [mul_zero]; exact (monomialSpan k).zero_mem
  · intro _ _ _ _ ha hb; rw [mul_add]; exact (monomialSpan k).add_mem ha hb
  · intro c _ _ ha; rw [mul_smul_comm]; exact (monomialSpan k).smul_mem c ha
  · exact ha

private lemma mul_secondOperator_mem_span {a : AuxiliaryAlgebra k} (ha : a ∈ monomialSpan k) :
    a * AuxiliaryAlgebra.secondOperator k ∈ monomialSpan k := by
  apply Submodule.span_induction
    (p := fun a (_ : a ∈ monomialSpan k) => a * AuxiliaryAlgebra.secondOperator k ∈ monomialSpan k)
  · intro z hz
    obtain ⟨⟨i, j⟩, rfl⟩ := hz
    have : AuxiliaryAlgebra.indexedElement k i j * AuxiliaryAlgebra.secondOperator k = AuxiliaryAlgebra.indexedElement k i (j + 1) := by
      simp only [AuxiliaryAlgebra.indexedElement, pow_succ, mul_assoc]
    rw [this]; exact indexedElement_mem_span k i (j + 1)
  · rw [zero_mul]; exact (monomialSpan k).zero_mem
  · intro _ _ _ _ ha hb; rw [add_mul]; exact (monomialSpan k).add_mem ha hb
  · intro c _ _ ha; rw [smul_mul_assoc]; exact (monomialSpan k).smul_mem c ha
  · exact ha

private lemma indexedElement_mul_firstOperator_mem_span (i j : ℕ) :
    AuxiliaryAlgebra.indexedElement k i j * AuxiliaryAlgebra.firstOperator k ∈ monomialSpan k := by
  induction j with
  | zero =>
    have : AuxiliaryAlgebra.indexedElement k i 0 * AuxiliaryAlgebra.firstOperator k = AuxiliaryAlgebra.indexedElement k (i + 1) 0 := by
      simp only [AuxiliaryAlgebra.indexedElement, pow_zero, mul_one, pow_succ]
    rw [this]; exact indexedElement_mem_span k (i + 1) 0
  | succ n ih =>

    have key : AuxiliaryAlgebra.indexedElement k i (n + 1) * AuxiliaryAlgebra.firstOperator k =
        AuxiliaryAlgebra.indexedElement k i n * AuxiliaryAlgebra.firstOperator k * AuxiliaryAlgebra.secondOperator k +
        AuxiliaryAlgebra.indexedElement k i n := by
      simp only [AuxiliaryAlgebra.indexedElement, pow_succ, mul_assoc]
      rw [AuxiliaryAlgebra.secondOperator_mul_firstOperator k, mul_add, mul_one, mul_add]
    rw [key]
    exact (monomialSpan k).add_mem (mul_secondOperator_mem_span k ih) (indexedElement_mem_span k i n)

private lemma mul_firstOperator_mem_span {a : AuxiliaryAlgebra k} (ha : a ∈ monomialSpan k) :
    a * AuxiliaryAlgebra.firstOperator k ∈ monomialSpan k := by
  apply Submodule.span_induction
    (p := fun a (_ : a ∈ monomialSpan k) => a * AuxiliaryAlgebra.firstOperator k ∈ monomialSpan k)
  · intro z hz
    obtain ⟨⟨i, j⟩, rfl⟩ := hz
    exact indexedElement_mul_firstOperator_mem_span k i j
  · rw [zero_mul]; exact (monomialSpan k).zero_mem
  · intro _ _ _ _ ha hb; rw [add_mul]; exact (monomialSpan k).add_mem ha hb
  · intro c _ _ ha; rw [smul_mul_assoc]; exact (monomialSpan k).smul_mem c ha
  · exact ha

private lemma secondOperator_mul_indexedElement_mem_span (i j : ℕ) :
    AuxiliaryAlgebra.secondOperator k * AuxiliaryAlgebra.indexedElement k i j ∈ monomialSpan k := by
  induction i with
  | zero =>
    have : AuxiliaryAlgebra.secondOperator k * AuxiliaryAlgebra.indexedElement k 0 j = AuxiliaryAlgebra.indexedElement k 0 (j + 1) := by
      simp only [AuxiliaryAlgebra.indexedElement, pow_zero, one_mul, pow_succ']
    rw [this]; exact indexedElement_mem_span k 0 (j + 1)
  | succ n ih =>

    have key : AuxiliaryAlgebra.secondOperator k * AuxiliaryAlgebra.indexedElement k (n + 1) j =
        AuxiliaryAlgebra.firstOperator k * (AuxiliaryAlgebra.secondOperator k * AuxiliaryAlgebra.indexedElement k n j) +
        AuxiliaryAlgebra.indexedElement k n j := by
      simp only [AuxiliaryAlgebra.indexedElement, pow_succ', mul_assoc]
      rw [← mul_assoc (AuxiliaryAlgebra.secondOperator k) (AuxiliaryAlgebra.firstOperator k),
          AuxiliaryAlgebra.secondOperator_mul_firstOperator k, add_mul, one_mul, mul_assoc]
    rw [key]
    exact (monomialSpan k).add_mem (firstOperator_mul_mem_span k ih) (indexedElement_mem_span k n j)

private lemma secondOperator_mul_mem_span {a : AuxiliaryAlgebra k} (ha : a ∈ monomialSpan k) :
    AuxiliaryAlgebra.secondOperator k * a ∈ monomialSpan k := by
  apply Submodule.span_induction
    (p := fun a (_ : a ∈ monomialSpan k) => AuxiliaryAlgebra.secondOperator k * a ∈ monomialSpan k)
  · intro z hz
    obtain ⟨⟨i, j⟩, rfl⟩ := hz
    exact secondOperator_mul_indexedElement_mem_span k i j
  · rw [mul_zero]; exact (monomialSpan k).zero_mem
  · intro _ _ _ _ ha hb; rw [mul_add]; exact (monomialSpan k).add_mem ha hb
  · intro c _ _ ha; rw [mul_smul_comm]; exact (monomialSpan k).smul_mem c ha
  · exact ha

private lemma mul_mem_monomialSpan {a b : AuxiliaryAlgebra k} (ha : a ∈ monomialSpan k) (hb : b ∈ monomialSpan k) :
    a * b ∈ monomialSpan k := by
  apply Submodule.span_induction
    (p := fun b (_ : b ∈ monomialSpan k) => a * b ∈ monomialSpan k)
  · intro z hz
    obtain ⟨⟨p, q⟩, rfl⟩ := hz
    simp only [AuxiliaryAlgebra.indexedElement, ← mul_assoc]

    have haxp : a * AuxiliaryAlgebra.firstOperator k ^ p ∈ monomialSpan k := by
      induction p with
      | zero => simpa [pow_zero] using ha
      | succ m ih => rw [pow_succ, ← mul_assoc]; exact mul_firstOperator_mem_span k ih

    induction q with
    | zero => simpa [pow_zero] using haxp
    | succ m ih => rw [pow_succ, ← mul_assoc]; exact mul_secondOperator_mem_span k ih
  · rw [mul_zero]; exact (monomialSpan k).zero_mem
  · intro _ _ _ _ hx hy; rw [mul_add]; exact (monomialSpan k).add_mem hx hy
  · intro c _ _ hx; rw [mul_smul_comm]; exact (monomialSpan k).smul_mem c hx
  · exact hb

/-- The family indexed by pairs of natural numbers spans the whole auxiliary algebra. -/
@[source_ref "Chapter2/Proposition2.7.1" (role := supporting)]
theorem AuxiliaryAlgebra.span_range_indexedElement :
    ⊤ ≤ Submodule.span k (Set.range (fun p : ℕ × ℕ => AuxiliaryAlgebra.indexedElement k p.1 p.2)) := by
  intro w _
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective k (auxiliaryRelation k) w
  have ha : a ∈ Algebra.adjoin k (Set.range (FreeAlgebra.ι k : AuxiliaryIndex → _)) := by
    rw [FreeAlgebra.adjoin_range_ι]; exact Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · convert indexedElement_mem_span k 1 0 using 1
      simp [AuxiliaryAlgebra.indexedElement, AuxiliaryAlgebra.firstOperator, AuxiliaryAlgebra.fromFreeAlgebra]
    · convert indexedElement_mem_span k 0 1 using 1
      simp [AuxiliaryAlgebra.indexedElement, AuxiliaryAlgebra.secondOperator, AuxiliaryAlgebra.fromFreeAlgebra]
  | algebraMap r =>
    convert (monomialSpan k).smul_mem r (indexedElement_mem_span k 0 0) using 1
    simp [AuxiliaryAlgebra.indexedElement, Algebra.algebraMap_eq_smul_one]
  | add x y _ _ ihx ihy => rw [map_add]; exact (monomialSpan k).add_mem (ihx trivial) (ihy trivial)
  | mul x y _ _ ihx ihy => rw [map_mul]; exact mul_mem_monomialSpan k (ihx trivial) (ihy trivial)

/-- The linear endomorphism of polynomials given by multiplication by the polynomial variable. -/
noncomputable def polynomialMulX : Module.End k (Polynomial k) where
  toFun p := Polynomial.X * p
  map_add' := mul_add _
  map_smul' c p := by
    simp only [RingHom.id_apply]
    exact Algebra.mul_smul_comm c Polynomial.X p

/-- The polynomial multiplication endomorphism sends a polynomial to its product with the variable. -/
lemma polynomialMulX_apply (p : Polynomial k) :
    polynomialMulX k p = Polynomial.X * p := rfl

private lemma derivative_mul_polynomialMulX :
    (Polynomial.derivative (R := k)) * polynomialMulX k =
    polynomialMulX k * Polynomial.derivative + 1 := by
  apply LinearMap.ext; intro p
  change Polynomial.derivative (polynomialMulX k p) =
    polynomialMulX k (Polynomial.derivative p) + (1 : Module.End k (Polynomial k)) p
  simp only [polynomialMulX_apply, Module.End.one_apply]
  rw [Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, add_comm]

private noncomputable def polynomialRepresentationGenerator : Fin 2 → Module.End k (Polynomial k) :=
  ![polynomialMulX k, Polynomial.derivative]

private noncomputable def freeAlgebraToPolynomialEnd :
    FreeAlgebra k (Fin 2) →ₐ[k] Module.End k (Polynomial k) :=
  FreeAlgebra.lift k (polynomialRepresentationGenerator k)

private lemma freeAlgebraToPolynomialEnd_rel :
    ∀ ⦃a b⦄, auxiliaryRelation k a b → freeAlgebraToPolynomialEnd k a = freeAlgebraToPolynomialEnd k b := by
  intro a b ⟨ha, hb⟩
  subst ha; subst hb
  simp only [freeAlgebraToPolynomialEnd, map_mul, map_add, map_one, FreeAlgebra.lift_ι_apply,
    polynomialRepresentationGenerator, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact derivative_mul_polynomialMulX k

/-- The algebra homomorphism from the operator algebra to polynomial endomorphisms. -/
noncomputable def toPolynomialEnd :
    AuxiliaryAlgebra k →ₐ[k] Module.End k (Polynomial k) :=
  RingQuot.liftAlgHom k ⟨freeAlgebraToPolynomialEnd k, freeAlgebraToPolynomialEnd_rel k⟩

/-- The first distinguished operator maps to multiplication by the polynomial variable. -/
lemma toPolynomialEnd_firstOperator :
    toPolynomialEnd k (AuxiliaryAlgebra.firstOperator k) = polynomialMulX k := by
  simp [toPolynomialEnd, AuxiliaryAlgebra.firstOperator, AuxiliaryAlgebra.fromFreeAlgebra, RingQuot.liftAlgHom_mkAlgHom_apply,
    freeAlgebraToPolynomialEnd, FreeAlgebra.lift_ι_apply, polynomialRepresentationGenerator]

/-- The second distinguished operator maps to polynomial differentiation. -/
lemma toPolynomialEnd_secondOperator :
    toPolynomialEnd k (AuxiliaryAlgebra.secondOperator k) =
    (Polynomial.derivative : Module.End k (Polynomial k)) := by
  simp [toPolynomialEnd, AuxiliaryAlgebra.secondOperator, AuxiliaryAlgebra.fromFreeAlgebra, RingQuot.liftAlgHom_mkAlgHom_apply,
    freeAlgebraToPolynomialEnd, FreeAlgebra.lift_ι_apply, polynomialRepresentationGenerator]

private lemma polynomialMulX_pow_apply (i : ℕ) (p : Polynomial k) :
    (polynomialMulX k ^ i) p = Polynomial.X ^ i * p := by
  induction i generalizing p with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, polynomialMulX_apply, ← mul_assoc, ← pow_succ]

private lemma toPolynomialEnd_indexedElement_apply (i j n : ℕ) :
    toPolynomialEnd k (AuxiliaryAlgebra.indexedElement k i j) (Polynomial.X ^ n) =
    Polynomial.C (↑(n.descFactorial j) : k) * Polynomial.X ^ (i + (n - j)) := by
  simp only [AuxiliaryAlgebra.indexedElement, map_mul, map_pow, toPolynomialEnd_firstOperator, toPolynomialEnd_secondOperator]
  rw [Module.End.mul_apply, Module.End.pow_apply (Polynomial.derivative (R := k)) j,
    Polynomial.iterate_derivative_X_pow_eq_C_mul, polynomialMulX_pow_apply]
  ring

private lemma toPolynomialEnd_indexedElement_eq_zero_of_lt (i j n : ℕ) (hjn : n < j) :
    toPolynomialEnd k (AuxiliaryAlgebra.indexedElement k i j) (Polynomial.X ^ n) = 0 := by
  rw [toPolynomialEnd_indexedElement_apply]
  simp [Nat.descFactorial_eq_zero_iff_lt.mpr hjn]

private lemma toPolynomialEnd_indexedElement_diagonal (i j : ℕ) :
    toPolynomialEnd k (AuxiliaryAlgebra.indexedElement k i j) (Polynomial.X ^ j) =
    Polynomial.C (↑(j.factorial) : k) * Polynomial.X ^ i := by
  rw [toPolynomialEnd_indexedElement_apply, Nat.descFactorial_self, Nat.sub_self, add_zero]

private lemma polynomialImages_linearIndependent [CharZero k] [NoZeroDivisors k] :
    LinearIndependent k (fun p : ℕ × ℕ => toPolynomialEnd k (AuxiliaryAlgebra.indexedElement k p.1 p.2)) := by
  rw [linearIndependent_iff']
  intro s g hg

  have hpoly : toPolynomialEnd k (∑ r ∈ s, g r • AuxiliaryAlgebra.indexedElement k r.1 r.2) = 0 := by
    rw [map_sum]; simp_rw [map_smul]; exact hg

  have hcoeff : ∀ (n m : ℕ),
      ∑ r ∈ s, g r *
        (toPolynomialEnd k (AuxiliaryAlgebra.indexedElement k r.1 r.2) (Polynomial.X ^ n)).coeff m = 0 := by
    intro n m

    have h1 : (toPolynomialEnd k (∑ r ∈ s, g r • AuxiliaryAlgebra.indexedElement k r.1 r.2)) (Polynomial.X ^ n)
        = 0 := by rw [hpoly, LinearMap.zero_apply]

    have h2 : ∀ r, toPolynomialEnd k (g r • AuxiliaryAlgebra.indexedElement k r.1 r.2) (Polynomial.X ^ n) =
        g r • (toPolynomialEnd k (AuxiliaryAlgebra.indexedElement k r.1 r.2) (Polynomial.X ^ n)) := by
      intro r
      rw [Algebra.smul_def, map_mul, AlgHom.commutes]
      simp [Module.End.mul_apply, Algebra.smul_def]
    rw [map_sum] at h1
    simp only [LinearMap.coe_sum, Finset.sum_apply] at h1
    simp_rw [h2] at h1

    have hc : (∑ r ∈ s, g r •
        (toPolynomialEnd k (AuxiliaryAlgebra.indexedElement k r.1 r.2) (Polynomial.X ^ n))).coeff m = 0 :=
      congr_arg (Polynomial.coeff · m) h1
    rw [Polynomial.finsetSum_coeff] at hc
    simp only [Polynomial.coeff_smul, smul_eq_mul] at hc
    exact hc

  suffices key : ∀ j i, (i, j) ∈ s → g (i, j) = 0 by
    intro ⟨i, j⟩ hp; exact key j i hp
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro i hij

    have hXj := hcoeff j i

    have hterm : ∀ r ∈ s, r ≠ (i, j) →
        g r * (toPolynomialEnd k (AuxiliaryAlgebra.indexedElement k r.1 r.2)
          (Polynomial.X ^ j)).coeff i = 0 := by
      intro ⟨ri, rj⟩ hr hne
      by_cases hjrj : j < rj
      · rw [toPolynomialEnd_indexedElement_eq_zero_of_lt k ri rj j hjrj, Polynomial.coeff_zero, mul_zero]
      · push Not at hjrj
        by_cases heq : rj = j
        · subst heq
          have hri : ri ≠ i := fun h => hne (Prod.ext h rfl)
          rw [toPolynomialEnd_indexedElement_diagonal, Polynomial.coeff_C_mul_X_pow,
            if_neg (Ne.symm hri), mul_zero]
        · rw [ih rj (lt_of_le_of_ne hjrj heq) ri hr, zero_mul]

    have honly : g (i, j) * (toPolynomialEnd k (AuxiliaryAlgebra.indexedElement k i j)
        (Polynomial.X ^ j)).coeff i = 0 := by
      have := Finset.sum_eq_single (i, j) (fun r hr hne => hterm r hr hne)
        (fun h => absurd hij h) |>.symm.trans hXj
      exact this
    rw [toPolynomialEnd_indexedElement_diagonal, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at honly
    exact (mul_eq_zero.mp honly).resolve_right
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))

private lemma indexedElement_linearIndependent [CharZero k] [NoZeroDivisors k] :
    LinearIndependent k (fun p : ℕ × ℕ => AuxiliaryAlgebra.indexedElement k p.1 p.2) :=
  (polynomialImages_linearIndependent k).of_comp (toPolynomialEnd k).toLinearMap

/-- The displayed homomorphism from the operator algebra to polynomial endomorphisms is injective. -/
@[source_ref "Chapter2/Discussion_faithful_example" (role := primary)]
theorem AuxiliaryAlgebra.toPolynomialEnd_injective [CharZero k] [NoZeroDivisors k] :
    Function.Injective (toPolynomialEnd k) := by
  classical
  set mono : ℕ × ℕ → AuxiliaryAlgebra k := fun p => AuxiliaryAlgebra.indexedElement k p.1 p.2 with hmono

  have hsurj : Function.Surjective (Finsupp.linearCombination k mono) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact top_le_iff.mp (AuxiliaryAlgebra.span_range_indexedElement k)

  have hli : LinearIndependent k (fun p : ℕ × ℕ => toPolynomialEnd k (mono p)) :=
    polynomialImages_linearIndependent k
  rw [injective_iff_map_eq_zero (toPolynomialEnd k)]
  intro w hw
  obtain ⟨f, rfl⟩ := hsurj w
  have h0 : Finsupp.linearCombination k (fun p => toPolynomialEnd k (mono p)) f = 0 := by
    have hap : toPolynomialEnd k (Finsupp.linearCombination k mono f)
        = Finsupp.linearCombination k (fun p => toPolynomialEnd k (mono p)) f := by
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
      simp only [map_smul]
    rw [← hap]; exact hw
  have hf : f = 0 :=
    hli.finsuppLinearCombination_injective (h0.trans (map_zero _).symm)
  rw [hf, map_zero]

/-- In prime characteristic, the indicated number of iterated polynomial derivatives is zero. -/
@[source_ref "Chapter2/Discussion_faithful_example" (role := primary)]
theorem derivative_iterate_prime_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : Polynomial k) : (Polynomial.derivative (R := k))^[p] Q = 0 := by
  ext m
  rw [Polynomial.coeff_iterate_derivative, Polynomial.coeff_zero]
  have hdvd : p ∣ (m + p).descFactorial p :=
    (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl).trans
      (Nat.factorial_dvd_descFactorial (m + p) p)
  rw [nsmul_eq_mul, (CharP.cast_eq_zero_iff k p _).mpr hdvd, zero_mul]

/-- In prime characteristic, the image of the stated power of the second operator is zero. -/
@[source_ref "Chapter2/Discussion_faithful_example" (role := supporting)]
theorem AuxiliaryAlgebra.toPolynomialEnd_power_second_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p] :
    toPolynomialEnd k (AuxiliaryAlgebra.secondOperator k ^ p) = 0 := by
  rw [map_pow, toPolynomialEnd_secondOperator]
  apply LinearMap.ext
  intro Q
  rw [Module.End.pow_apply, LinearMap.zero_apply]
  exact derivative_iterate_prime_eq_zero k p Q

/-- The family indexed by pairs of natural numbers is linearly independent and spans the ambient algebra. -/
theorem indexedElement_linearIndependent_and_span [CharZero k] [NoZeroDivisors k] :
    LinearIndependent k (fun p : ℕ × ℕ => AuxiliaryAlgebra.indexedElement k p.1 p.2) ∧
    ⊤ ≤ Submodule.span k (Set.range (fun p : ℕ × ℕ => AuxiliaryAlgebra.indexedElement k p.1 p.2)) := by
  exact ⟨indexedElement_linearIndependent k, AuxiliaryAlgebra.span_range_indexedElement k⟩

end RepresentationTheory.FreeAlgebra.PolynomialOperators
