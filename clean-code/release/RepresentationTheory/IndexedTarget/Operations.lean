/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial
import RepresentationTheory.Alignment.Attribute

/-!
# Operations on an indexed target

This module defines an indexed target built from integral finitely supported exponents, embeds
multivariate polynomials into it, and establishes the resulting coefficient identities.
-/

namespace RepresentationTheory.IndexedTarget.Operations

noncomputable section

open Finset
  RepresentationTheory.PermutationPolynomialAuxiliary
  RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter

/-! ## The indexed target -/

/-- A family of types indexed by a natural number. -/
abbrev Target (n : ℕ) : Type := AddMonoidAlgebra ℂ (Fin n →₀ ℤ)

namespace Target

/-- Produces a target element from an integral exponent and a complex number. -/
def integralExponentElement {n : ℕ} (e : Fin n →₀ ℤ) (c : ℂ) : Target n :=
  AddMonoidAlgebra.single e c

/-- Assigns a complex number to an integral exponent and a target element. -/
def complexValue {n : ℕ} (e : Fin n →₀ ℤ) (f : Target n) : ℂ :=
  (AddMonoidAlgebra.coeff f) e

/-- An element of the indexed target associated with a finite index. -/
def indexedElement {n : ℕ} (i : Fin n) : Target n :=
  integralExponentElement (Finsupp.single i 1) 1

/-- A second indexed element of the target type. -/
def companionElement {n : ℕ} (i : Fin n) : Target n :=
  integralExponentElement (Finsupp.single i (-1)) 1

/-- The product of two displayed exponent elements combines their exponents by addition and their
complex inputs by multiplication. -/
@[simp] theorem integralExponentElement_mul {n : ℕ} (e f : Fin n →₀ ℤ) (c d : ℂ) :
    integralExponentElement e c * integralExponentElement f d =
      integralExponentElement (e + f) (c * d) := by
  simp only [integralExponentElement]
  exact AddMonoidAlgebra.single_mul_single (R := ℂ) (M := Fin n →₀ ℤ) e f c d

/-- The exponent element at zero with complex input one is one. -/
@[simp] theorem integralExponentElement_zero_one {n : ℕ} :
    integralExponentElement (0 : Fin n →₀ ℤ) 1 = 1 := by
  simp [integralExponentElement, AddMonoidAlgebra.one_def]

/-- The product of the indexed element and its displayed companion is one. -/
@[simp] theorem indexedElement_mul_companion_eq_one {n : ℕ} (i : Fin n) :
    indexedElement i * companionElement i = 1 := by
  rw [indexedElement, companionElement, integralExponentElement_mul]
  simp

/-- A finite product of displayed exponent elements with complex input one equals the element at
the summed exponent. -/
theorem prod_integralExponentElement_one {n : ℕ} (s : Finset (Fin n))
    (g : Fin n → (Fin n →₀ ℤ)) :
    ∏ i ∈ s, integralExponentElement (g i) (1 : ℂ) =
      integralExponentElement (∑ i ∈ s, g i) 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, integralExponentElement_mul, one_mul]

/-- Raising the exponent element with complex input one to a natural power scales its exponent. -/
theorem integralExponentElement_one_pow {n : ℕ} (e : Fin n →₀ ℤ) (k : ℕ) :
    integralExponentElement e (1 : ℂ) ^ k = integralExponentElement (k • e) 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, integralExponentElement_mul, succ_nsmul, one_mul]

/-- Evaluating the displayed product at a summed exponent equals a complex scalar times another
evaluation. -/
theorem complexValue_add_apply_mul {n : ℕ} (e a : Fin n →₀ ℤ) (c : ℂ) (f : Target n) :
    complexValue (e + a) (integralExponentElement e c * f) = c * complexValue a f := by
  rw [complexValue, complexValue, integralExponentElement,
    AddMonoidAlgebra.coeff_single_mul_apply]
  simp

end Target

/-! ## Mapping polynomials into the target -/

/-- An additive monoid homomorphism from natural-valued to integer-valued finitely supported
functions. -/
def natExponentToInt (n : ℕ) : (Fin n →₀ ℕ) →+ (Fin n →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

/-- The exponent homomorphism acts pointwise by casting each natural value to an integer. -/
@[simp] theorem natExponentToInt_apply (n : ℕ) (e : Fin n →₀ ℕ) (i : Fin n) :
    natExponentToInt n e i = (e i : ℤ) := by
  simp [natExponentToInt]

/-- The displayed exponent homomorphism is injective. -/
theorem natExponentToInt_injective (n : ℕ) : Function.Injective (natExponentToInt n) := by
  intro a b h
  ext i
  have := congrArg (fun f => f i) h
  simpa using this

/-- A ring homomorphism from complex multivariate polynomials to the indexed target. -/
def polynomialToTarget (n : ℕ) : MvPolynomial (Fin n) ℂ →+* Target n :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (natExponentToInt n)

/-- Applying the complex-valued function after the displayed polynomial map equals the
corresponding polynomial coefficient. -/
theorem complexValue_polynomialMap_eq_coeff (n : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (e : Fin n →₀ ℕ) :
    Target.complexValue (natExponentToInt n e) (polynomialToTarget n P) =
      MvPolynomial.coeff e P := by
  change Finsupp.mapDomain (natExponentToInt n) (AddMonoidAlgebra.coeff P)
      (natExponentToInt n e) = _
  rw [Finsupp.mapDomain_apply (natExponentToInt_injective n)]
  rfl

/-- The displayed ring homomorphism is injective. -/
theorem polynomialToTarget_injective (n : ℕ) : Function.Injective (polynomialToTarget n) := by
  intro P Q h
  ext e
  rw [← complexValue_polynomialMap_eq_coeff n P e,
    ← complexValue_polynomialMap_eq_coeff n Q e, h]

/-- The ring homomorphism sends a polynomial variable to the corresponding indexed element. -/
@[simp] theorem polynomialToTarget_X (n : ℕ) (i : Fin n) :
    polynomialToTarget n (MvPolynomial.X i) = Target.indexedElement i := by
  rw [MvPolynomial.X, MvPolynomial.monomial]
  change AddMonoidAlgebra.mapDomain (natExponentToInt n)
      (AddMonoidAlgebra.single (Finsupp.single i 1) (1 : ℂ)) =
    AddMonoidAlgebra.single (Finsupp.single i 1) (1 : ℂ)
  rw [AddMonoidAlgebra.mapDomain_single]
  congr 1
  ext j
  simp [natExponentToInt]

/-! ## Indexed polynomial identities -/

/-- A complex multivariate polynomial for each natural-number index. -/
def indexedPolynomial (n : ℕ) : MvPolynomial (Fin n) ℂ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (MvPolynomial.X i - MvPolynomial.X j)

/-- A target element for each natural-number index. -/
def indexedTargetElement (n : ℕ) : Target n :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
    (1 - Target.indexedElement j * Target.companionElement i)

/-- A theorem whose formal statement is unavailable because it could not be pretty printed. -/
theorem opaqueTheoremB (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm (n := n)) =
      ∏ i : Fin n, ∏ _j ∈ Finset.Ioi i, (-1 : ℤˣ) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
  have hij : i < j := Finset.mem_Ioi.mp hj
  simp only [Fin.revPerm_apply]
  rw [if_neg (asymm (Fin.rev_lt_rev.mpr hij))]

/-- A theorem whose formal statement is unavailable because it could not be pretty printed. -/
theorem opaqueTheoremA (n : ℕ) (R : Type*) [CommRing R] :
    ((Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) : R) =
      ∏ i : Fin n, ∏ _j ∈ Finset.Ioi i, (-1 : R) := by
  rw [opaqueTheoremB]
  push_cast
  simp

/-- The indexed polynomial is a scalar multiple, by the displayed permutation sign, of another
polynomial. -/
theorem indexedPolynomial_eq_sign_smul (n : ℕ) :
    indexedPolynomial n =
      (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) •
        auxiliaryPolynomial n := by
  have hprod : indexedPolynomial n =
      (∏ i : Fin n, ∏ _j ∈ Finset.Ioi i, (-1 : MvPolynomial (Fin n) ℂ)) *
        auxiliaryPolynomial n := by
    rw [indexedPolynomial, auxiliaryPolynomial, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by ring
  rw [hprod, ← opaqueTheoremA n (MvPolynomial (Fin n) ℂ), ← zsmul_eq_mul]

/-- The displayed mapped exponent equals a finite sum of singleton finitely supported functions
weighted by upper-index cardinalities. -/
theorem mappedExponent_eq_sum (n : ℕ) :
    natExponentToInt n (auxiliaryFinsupp n) =
      ∑ i : Fin n, Finsupp.single i (#(Finset.Ioi i) : ℤ) := by
  ext j
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Fin.card_Ioi,
    auxiliaryFinsupp]

/-- The displayed exponent element equals an iterated finite product of indexed elements. -/
theorem integralExponentElement_eq_prod_indexedElement (n : ℕ) :
    Target.integralExponentElement
        (natExponentToInt n (auxiliaryFinsupp n)) 1 =
      ∏ i : Fin n, ∏ _j ∈ Finset.Ioi i, Target.indexedElement i := by
  rw [mappedExponent_eq_sum, ← Target.prod_integralExponentElement_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_const, Target.indexedElement, Target.integralExponentElement_one_pow]
  congr 1
  ext j
  simp [Finsupp.single_apply]

/-- Multiplying the displayed exponent element by the indexed target element equals the image of
the indexed polynomial under the displayed map. -/
@[source_ref"Chapter5/Remark5.15.2"(role:=supporting)]
theorem integralExponentElement_mul_indexedTargetElement (n : ℕ) :
    Target.integralExponentElement
          (natExponentToInt n (auxiliaryFinsupp n)) 1 *
        indexedTargetElement n =
      polynomialToTarget n (indexedPolynomial n) := by
  rw [integralExponentElement_eq_prod_indexedElement, indexedTargetElement,
    ← Finset.prod_mul_distrib]
  rw [indexedPolynomial, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_sub, polynomialToTarget_X, polynomialToTarget_X, mul_sub, mul_one]
  congr 1
  rw [← mul_assoc, mul_comm (Target.indexedElement i) (Target.indexedElement j), mul_assoc,
    Target.indexedElement_mul_companion_eq_one, mul_one]

/-! ## Complex-value identities -/

set_option backward.isDefEq.respectTransparency false in
/-- Equates a displayed complex-valued function application with a signed
multivariate-polynomial coefficient. -/
@[source_ref"Chapter5/Remark5.15.2"(role:=supporting)]
theorem complexValue_eq_signed_coeff (n : ℕ) (e : Fin n →₀ ℕ)
    (P : MvPolynomial (Fin n) ℂ) :
    Target.complexValue (natExponentToInt n e)
        (indexedTargetElement n * polynomialToTarget n P) =
      (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) •
        MvPolynomial.coeff
          (e + auxiliaryFinsupp n)
          (auxiliaryPolynomial n * P) := by
  have hsmul : (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) •
      MvPolynomial.coeff
          (e + auxiliaryFinsupp n)
          (auxiliaryPolynomial n * P) =
      MvPolynomial.coeff
        (e + auxiliaryFinsupp n)
        (((Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) •
          auxiliaryPolynomial n) * P) := by
    rw [smul_mul_assoc, MvPolynomial.coeff_smul]
  rw [hsmul, ← indexedPolynomial_eq_sign_smul, ← complexValue_polynomialMap_eq_coeff,
    map_mul, ← integralExponentElement_mul_indexedTargetElement, map_add, mul_assoc,
    add_comm (natExponentToInt n e)
      (natExponentToInt n (auxiliaryFinsupp n)),
    Target.complexValue_add_apply_mul, one_mul]

/-- Equates the displayed partition-and-permutation expression with an application of the
complex-valued function. -/
@[source_ref"Chapter5/Remark5.15.2"(role:=primary)]
theorem partitionPermutation_eq_complexValue (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    auxiliaryPartitionPermutationValue n la σ =
      Target.complexValue (natExponentToInt n (partitionNatFinsupp la))
        (indexedTargetElement n *
          polynomialToTarget n (permutationPolynomialAuxiliary n σ)) := by
  rw [complexValue_eq_signed_coeff,
    ← auxiliarySignSmul_eq_coefficient, smul_smul]
  simp

end

end RepresentationTheory.IndexedTarget.Operations

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.IndexedTarget.Operations.Auxiliary.statement017758 := _root_.RepresentationTheory.IndexedTarget.Operations.opaqueTheoremA

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.IndexedTarget.Operations.Auxiliary.statement023150 := _root_.RepresentationTheory.IndexedTarget.Operations.opaqueTheoremB
