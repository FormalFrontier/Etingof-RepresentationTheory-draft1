/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.FreeAlgebra.PolynomialOperators
import Mathlib.Algebra.Polynomial.BigOperators
import RepresentationTheory.Alignment.Attribute

/-!
# Integer-indexed polynomial operators

This file constructs a characteristic-free faithful operator representation on polynomial data
indexed by the integers.
-/

namespace RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators

open Polynomial
open RepresentationTheory.FreeAlgebra.PolynomialOperators

variable (k : Type*) [CommRing k]

/-- The module used to realize operators on polynomial data indexed by integers. -/
@[source_ref "Chapter2/Proposition2.7.1" (role := supporting)]
abbrev IntegerIndexedPolynomialModule : Type _ := ℤ →₀ Polynomial k

/-- The linear endomorphism which shifts an integer index upward. -/
noncomputable def indexShift : Module.End k (IntegerIndexedPolynomialModule k) :=
  Finsupp.lsum k (fun n => Finsupp.lsingle (n + 1))

/-- The linear endomorphism which lowers the integer index and multiplies the polynomial value by an index-dependent linear polynomial. -/
noncomputable def weightedIndexLowering : Module.End k (IntegerIndexedPolynomialModule k) :=
  Finsupp.lsum k (fun n => (Finsupp.lsingle (n - 1)).comp
    (LinearMap.mulLeft k (Polynomial.X + (n : Polynomial k))))

/-- The index shift sends a singleton at `n` to the singleton at `n + 1` without changing its polynomial value. -/
@[simp] lemma indexShift_single (n : ℤ) (c : Polynomial k) :
    indexShift k (Finsupp.single n c) = Finsupp.single (n + 1) c := by
  simp only [indexShift, Finsupp.lsum_apply, Finsupp.sum_single_index, map_zero,
    Finsupp.lsingle_apply]

/-- Weighted index lowering sends a singleton at `n` to one at `n - 1`, multiplying its value by `X + n`. -/
@[simp] lemma weightedIndexLowering_single (n : ℤ) (c : Polynomial k) :
    weightedIndexLowering k (Finsupp.single n c) =
      Finsupp.single (n - 1) ((Polynomial.X + (n : Polynomial k)) * c) := by
  simp only [weightedIndexLowering, Finsupp.lsum_apply, Finsupp.sum_single_index, map_zero,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, Finsupp.lsingle_apply]

/-- Weighted index lowering followed by shifting equals shifting followed by weighted lowering plus the identity. -/
lemma weightedIndexLowering_mul_indexShift :
    weightedIndexLowering k * indexShift k = indexShift k * weightedIndexLowering k + 1 := by
  apply Finsupp.lhom_ext
  intro n c
  simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply, indexShift_single,
    weightedIndexLowering_single]
  rw [show (n : ℤ) + 1 - 1 = n from by ring, show (n : ℤ) - 1 + 1 = n from by ring,
    ← Finsupp.single_add]
  congr 1
  push_cast
  ring

/-- A pair of distinguished linear endomorphisms of the integer-indexed polynomial module. -/
noncomputable def distinguishedEndomorphism : Fin 2 → Module.End k (IntegerIndexedPolynomialModule k) :=
  ![indexShift k, weightedIndexLowering k]

private noncomputable def weylRepFree :
    FreeAlgebra k (Fin 2) →ₐ[k] Module.End k (IntegerIndexedPolynomialModule k) :=
  FreeAlgebra.lift k (distinguishedEndomorphism k)

private lemma weylRep_rel :
    ∀ ⦃a b⦄, freeAlgebraRelation k a b → weylRepFree k a = weylRepFree k b := by
  intro a b ⟨ha, hb⟩
  subst ha; subst hb
  simp only [weylRepFree, map_mul, map_add, map_one, FreeAlgebra.lift_ι_apply,
    distinguishedEndomorphism, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact weightedIndexLowering_mul_indexShift k

/-- The algebra homomorphism realizing algebra elements as endomorphisms of the integer-indexed polynomial module. -/
@[source_ref "Chapter2/Proposition2.7.1" (role := supporting)]
noncomputable def operatorRepresentation :
    OperatorAlgebra k →ₐ[k] Module.End k (IntegerIndexedPolynomialModule k) :=
  RingQuot.liftAlgHom k ⟨weylRepFree k, weylRep_rel k⟩

/-- The representation sends the designated shift generator to the index-shift endomorphism. -/
@[simp, source_ref "Chapter2/Proposition2.7.1" (role := supporting)]
lemma operatorRepresentation_indexShiftGenerator :
    operatorRepresentation k (OperatorAlgebra.firstOperator k) = indexShift k := by
  simp [operatorRepresentation, OperatorAlgebra.firstOperator, OperatorAlgebra.fromFreeAlgebra,
    RingQuot.liftAlgHom_mkAlgHom_apply, weylRepFree, FreeAlgebra.lift_ι_apply,
    distinguishedEndomorphism]

/-- The representation sends the designated lowering generator to the weighted index-lowering endomorphism. -/
@[simp, source_ref "Chapter2/Proposition2.7.1" (role := supporting)]
lemma operatorRepresentation_weightedLoweringGenerator :
    operatorRepresentation k (OperatorAlgebra.secondOperator k) = weightedIndexLowering k := by
  simp [operatorRepresentation, OperatorAlgebra.secondOperator, OperatorAlgebra.fromFreeAlgebra,
    RingQuot.liftAlgHom_mkAlgHom_apply, weylRepFree, FreeAlgebra.lift_ι_apply,
    distinguishedEndomorphism]

/-- The polynomial family obtained by successively multiplying by `X - j`. -/
noncomputable def fallingFactorialPolynomial (j : ℕ) : Polynomial k :=
  ∏ l ∈ Finset.range j, (Polynomial.X - Polynomial.C (l : k))

/-- The zeroth falling-factorial polynomial is one. -/
@[simp] lemma fallingFactorialPolynomial_zero : fallingFactorialPolynomial k 0 = 1 := by
  simp [fallingFactorialPolynomial]

/-- The next falling-factorial polynomial is the current one multiplied by `X - j`. -/
lemma fallingFactorialPolynomial_succ (j : ℕ) :
    fallingFactorialPolynomial k (j + 1) =
      fallingFactorialPolynomial k j * (Polynomial.X - Polynomial.C (j : k)) := by
  simp [fallingFactorialPolynomial, Finset.prod_range_succ]

/-- Every falling-factorial polynomial is monic. -/
lemma fallingFactorialPolynomial_monic (j : ℕ) : (fallingFactorialPolynomial k j).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro l _
  exact Polynomial.monic_X_sub_C _

variable [Nontrivial k]

/-- Over a nontrivial commutative ring, the `j`-th falling-factorial polynomial has natural degree `j`. -/
lemma fallingFactorialPolynomial_natDegree (j : ℕ) :
    (fallingFactorialPolynomial k j).natDegree = j := by
  rw [fallingFactorialPolynomial,
    Polynomial.natDegree_prod_of_monic _ _ (fun l _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one]

/-- The coefficient in degree `j` of the `j`-th falling-factorial polynomial is one. -/
lemma fallingFactorialPolynomial_coeff_self (j : ℕ) :
    (fallingFactorialPolynomial k j).coeff j = 1 := by
  have h := (fallingFactorialPolynomial_monic k j).coeff_natDegree
  rwa [fallingFactorialPolynomial_natDegree] at h

omit [Nontrivial k] in
/-- The `i`-th power of the index shift sends a singleton at `n` to the singleton at `n + i` with the same value. -/
lemma indexShift_pow_single (i : ℕ) (n : ℤ) (c : Polynomial k) :
    (indexShift k ^ i) (Finsupp.single n c) = Finsupp.single (n + i) c := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, indexShift_single]
    congr 1
    push_cast; ring

omit [Nontrivial k] in
/-- The `j`-th power of weighted index lowering sends the unit singleton at zero to a singleton at `-j` valued in the `j`-th falling-factorial polynomial. -/
lemma weightedIndexLowering_pow_single_zero (j : ℕ) :
    (weightedIndexLowering k ^ j) (Finsupp.single 0 1) =
      Finsupp.single (-(j : ℤ)) (fallingFactorialPolynomial k j) := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, weightedIndexLowering_single,
      fallingFactorialPolynomial_succ]
    rw [show (-(n : ℤ)) - 1 = -((n + 1 : ℕ) : ℤ) from by push_cast; ring]
    congr 1
    simp only [Polynomial.C_eq_natCast]
    push_cast; ring

omit [Nontrivial k] in
/-- Applying the represented `(i,j)` operator monomial to the unit singleton gives a singleton at `i - j` valued in the `j`-th falling-factorial polynomial. -/
theorem operatorRepresentation_monomial_apply_single (i j : ℕ) :
    operatorRepresentation k (OperatorAlgebra.monomialOperator k i j) (Finsupp.single 0 1) =
      Finsupp.single ((i : ℤ) - j) (fallingFactorialPolynomial k j) := by
  simp only [OperatorAlgebra.monomialOperator, map_mul, map_pow,
    operatorRepresentation_indexShiftGenerator, operatorRepresentation_weightedLoweringGenerator,
    Module.End.mul_apply]
  rw [weightedIndexLowering_pow_single_zero, indexShift_pow_single]
  congr 1
  ring

/-- Finsupp singletons placed at the difference of their two indices and valued in the corresponding falling-factorial polynomial are linearly independent. -/
theorem single_fallingFactorialPolynomial_linearIndependent :
    LinearIndependent k
      (fun p : ℕ × ℕ =>
        Finsupp.single ((p.1 : ℤ) - p.2) (fallingFactorialPolynomial k p.2)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum p₀ hp₀
  set m₀ : ℤ := (p₀.1 : ℤ) - p₀.2 with hm₀
  have hval := congrArg (fun e : IntegerIndexedPolynomialModule k => e m₀) hsum
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
    Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply, smul_ite, smul_zero,
    ← Finset.sum_filter] at hval
  set t : Finset (ℕ × ℕ) := s.filter (fun p => (p.1 : ℤ) - p.2 = m₀) with ht
  have hp₀t : p₀ ∈ t := Finset.mem_filter.mpr ⟨hp₀, hm₀.symm⟩
  have hinj : ∀ p ∈ t, ∀ q ∈ t, p.2 = q.2 → p = q := by
    intro p hp q hq h2
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    refine Prod.ext ?_ h2
    omega
  have hall : ∀ p ∈ t, g p = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨q, hqt, hq0⟩ := hcon
    set B : Finset (ℕ × ℕ) := t.filter (fun p => g p ≠ 0) with hB
    have hqB : q ∈ B := Finset.mem_filter.mpr ⟨hqt, hq0⟩
    obtain ⟨pmax, hpmaxB, hsup⟩ := Finset.exists_mem_eq_sup' ⟨q, hqB⟩ (fun p => p.2)
    have hpmaxt : pmax ∈ t := (Finset.mem_filter.mp hpmaxB).1
    have hpmax0 : g pmax ≠ 0 := (Finset.mem_filter.mp hpmaxB).2
    have hco : (∑ p ∈ t, g p • fallingFactorialPolynomial k p.2).coeff pmax.2 = 0 := by
      rw [hval, Polynomial.coeff_zero]
    rw [Polynomial.finsetSum_coeff] at hco
    simp only [Polynomial.coeff_smul, smul_eq_mul] at hco
    rw [Finset.sum_eq_single pmax ?_ ?_] at hco
    · rw [fallingFactorialPolynomial_coeff_self, mul_one] at hco
      exact hpmax0 hco
    · intro p hpt hne
      rcases lt_trichotomy p.2 pmax.2 with hlt | heq | hgt
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (by rw [fallingFactorialPolynomial_natDegree]; exact hlt), mul_zero]
      · exact absurd (hinj p hpt pmax hpmaxt heq) hne
      · have hgp0 : g p = 0 := by
          by_contra hgp
          have hpB : p ∈ B := Finset.mem_filter.mpr ⟨hpt, hgp⟩
          have hle := (Finset.le_sup' (fun p => p.2) hpB).trans hsup.le
          omega
        rw [hgp0, zero_mul]
    · intro hpmaxnotin; exact absurd hpmaxt hpmaxnotin
  exact hall p₀ hp₀t

/-- The represented family of doubly indexed operator monomials is linearly independent. -/
theorem operatorRepresentation_monomials_linearIndependent :
    LinearIndependent k
      (fun p : ℕ × ℕ =>
        operatorRepresentation k (OperatorAlgebra.monomialOperator k p.1 p.2)) := by
  have hΦ := single_fallingFactorialPolynomial_linearIndependent k
  refine LinearIndependent.of_comp
    (LinearMap.applyₗ (Finsupp.single (0 : ℤ) (1 : Polynomial k))) ?_
  convert hΦ using 1
  funext p
  simp only [Function.comp_apply, LinearMap.applyₗ_apply_apply]
  exact operatorRepresentation_monomial_apply_single k p.1 p.2

/-- The operator representation is injective over a nontrivial commutative ring. -/
@[source_ref "Chapter2/Discussion_faithful_example" (role := primary),
  source_ref "Chapter2/Proposition2.7.1" (role := supporting)]
theorem operatorRepresentation_injective : Function.Injective (operatorRepresentation k) := by
  classical
  set mono : ℕ × ℕ → OperatorAlgebra k :=
    fun p => OperatorAlgebra.monomialOperator k p.1 p.2 with hmono
  have hsurj : Function.Surjective (Finsupp.linearCombination k mono) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact top_le_iff.mp (OperatorAlgebra.span_monomialOperator k)
  have hli : LinearIndependent k (fun p : ℕ × ℕ => operatorRepresentation k (mono p)) := by
    simpa only [hmono] using operatorRepresentation_monomials_linearIndependent k
  rw [injective_iff_map_eq_zero (operatorRepresentation k)]
  intro w hw
  obtain ⟨f, rfl⟩ := hsurj w
  have h0 : Finsupp.linearCombination k (fun p => operatorRepresentation k (mono p)) f = 0 := by
    have hap : operatorRepresentation k (Finsupp.linearCombination k mono f) =
        Finsupp.linearCombination k (fun p => operatorRepresentation k (mono p)) f := by
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
      simp only [map_smul]
    rw [← hap]; exact hw
  have hf : f = 0 :=
    hli.finsuppLinearCombination_injective (h0.trans (map_zero _).symm)
  rw [hf, map_zero]

end RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators

namespace RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra

open RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators
open RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- The family of operator monomials indexed by pairs of natural numbers is linearly independent. -/
theorem operatorMonomials_linearIndependent :
    LinearIndependent k (fun p : ℕ × ℕ => monomialOperator k p.1 p.2) :=
  (operatorRepresentation_monomials_linearIndependent k).of_comp
    (operatorRepresentation k).toLinearMap

/-- Every operator monomial indexed by a pair of natural numbers is nonzero over a nontrivial commutative ring. -/
theorem operatorMonomial_ne_zero (i j : ℕ) : monomialOperator k i j ≠ 0 :=
  (operatorMonomials_linearIndependent k).ne_zero (i, j)

/-- In prime positive characteristic, the comparison map from the algebra is not injective. -/
@[source_ref "Chapter2/Discussion_faithful_example" (role := primary)]
theorem comparisonMap_not_injective_of_charP (p : ℕ) [Fact p.Prime] [CharP k p] :
    ¬ Function.Injective (toPolynomialEnd k) := by
  intro hinj
  have hy : secondOperator k ^ p ≠ 0 := by
    rw [show secondOperator k ^ p = monomialOperator k 0 p by
      rw [monomialOperator, pow_zero, one_mul]]
    exact operatorMonomial_ne_zero k 0 p
  exact hy (hinj ((toPolynomialEnd_power_second_eq_zero k p).trans
    (map_zero (toPolynomialEnd k)).symm))

end RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra

namespace RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators

open RepresentationTheory.FreeAlgebra.PolynomialOperators

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- In prime positive characteristic, the operator representation is injective while the comparison map is not. -/
@[source_ref "Chapter2/Discussion_faithful_example" (role := supporting)]
theorem operatorRepresentation_injective_and_comparisonMap_not_injective
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    Function.Injective (operatorRepresentation k) ∧
      ¬ Function.Injective (toPolynomialEnd k) :=
  ⟨operatorRepresentation_injective k, AuxiliaryAlgebra.comparisonMap_not_injective_of_charP k p⟩

/-- The doubly indexed operator monomials are linearly independent and their range spans the whole algebra. -/
@[source_ref "Chapter2/Proposition2.7.1" (role := primary)]
theorem operatorMonomials_linearIndependent_and_span :
    LinearIndependent k (fun p : ℕ × ℕ => OperatorAlgebra.monomialOperator k p.1 p.2) ∧
    ⊤ ≤ Submodule.span k
      (Set.range (fun p : ℕ × ℕ => OperatorAlgebra.monomialOperator k p.1 p.2)) :=
  ⟨AuxiliaryAlgebra.operatorMonomials_linearIndependent k,
    OperatorAlgebra.span_monomialOperator k⟩

end RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators
