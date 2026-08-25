/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.NoncommutativeAlgebra.PositiveCharacteristic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Nat.Factorial.BigOperators
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels

open Finset
open scoped Fin.NatCast

section Family

variable (k : Type*) [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]

private lemma p_pos : 0 < p := (Fact.out : p.Prime).pos
/-- A prime natural number is nonzero. -/


instance prime_neZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
/-- The coefficient controlling the wraparound in the cyclic position endomorphism. -/





def cyclicPositionCoeff (α : k) (j : Fin p) : k := if j = 0 then α else 1
/-- The cyclic position endomorphism on field-valued functions on `Fin p`, with the wraparound controlled by a scalar. -/



def cyclicPositionEnd (α : k) : (Fin p → k) →ₗ[k] (Fin p → k) where
  toFun f := fun j => cyclicPositionCoeff k p α j * f (j - 1)
  map_add' f g := by funext j; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [CharP k p] in

/-- The cyclic position endomorphism evaluates by shifting the index backward and multiplying by the wraparound coefficient. -/
@[simp] theorem cyclicPositionEnd_apply (α : k) (f : Fin p → k) (j : Fin p) :
    cyclicPositionEnd k p α f j = cyclicPositionCoeff k p α j * f (j - 1) := rfl
/-- The coefficient used by the cyclic formal-derivative term at a finite index. -/






def successorCoeff (j : Fin p) : k := (((j + 1 : Fin p) : ℕ) : k)
/-- The endomorphism on finite functions given by a scalar term plus the cyclic formal-derivative term. -/


def derivativeAddScalarEnd (c : k) : (Fin p → k) →ₗ[k] (Fin p → k) where
  toFun f := fun j => c * f j + successorCoeff k p j * f (j + 1)
  map_add' f g := by funext j; simp only [Pi.add_apply]; ring
  map_smul' a f := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [CharP k p] in

/-- The derivative-plus-scalar endomorphism evaluates as the scalar multiple of the current value plus the successor coefficient times the next value. -/
@[simp] theorem derivativeAddScalarEnd_apply (c : k) (f : Fin p → k) (j : Fin p) :
    derivativeAddScalarEnd k p c f j = c * f j + successorCoeff k p j * f (j + 1) := rfl
/-- In characteristic `p`, the successor coefficient is the index cast to the field plus one. -/


theorem successorCoeff_eq_cast_add_one (j : Fin p) : successorCoeff k p j = ((j : ℕ) : k) + 1 := by
  have h1 : ((1 : Fin p) : ℕ) ≡ 1 [MOD p] := by
    rw [Fin.val_one']; exact Nat.mod_modEq 1 p
  have h : ((j + 1 : Fin p) : ℕ) ≡ (j : ℕ) + 1 [MOD p] := by
    rw [Fin.val_add]
    exact (Nat.mod_modEq _ _).trans (Nat.ModEq.add_left _ h1)
  have := (CharP.natCast_eq_natCast k p).mpr h
  rw [successorCoeff, this]; push_cast; ring

omit [CharP k p] in
/-- The successor coefficient at the preceding finite index is the cast of the current index. -/

theorem successorCoeff_pred (j : Fin p) : successorCoeff k p (j - 1) = ((j : ℕ) : k) := by
  rw [successorCoeff, sub_add_cancel]



omit [CharP k p] in
/-- The successor coefficient times the cyclic position coefficient at the next index equals the successor coefficient. -/


theorem successorCoeff_mul_cyclicPositionCoeff_succ (α : k) (j : Fin p) :
    successorCoeff k p j * cyclicPositionCoeff k p α (j + 1) = successorCoeff k p j := by
  by_cases h : j + 1 = 0
  · rw [successorCoeff, h]; simp
  · rw [cyclicPositionCoeff, if_neg h, mul_one]

omit [CharP k p] in
/-- The cyclic position coefficient times the predecessor successor coefficient equals that successor coefficient. -/


theorem cyclicPositionCoeff_mul_successorCoeff_pred (α : k) (j : Fin p) :
    cyclicPositionCoeff k p α j * successorCoeff k p (j - 1) = successorCoeff k p (j - 1) := by
  by_cases h : j = 0
  · rw [successorCoeff_pred, h]; simp
  · rw [cyclicPositionCoeff, if_neg h, one_mul]
/-- The derivative-plus-scalar and cyclic position endomorphisms satisfy the displayed commutation relation. -/



theorem derivativeAddScalarEnd_mul_cyclicPositionEnd (α c : k) :
    derivativeAddScalarEnd k p c * cyclicPositionEnd k p α = cyclicPositionEnd k p α * derivativeAddScalarEnd k p c + 1 := by
  refine LinearMap.ext fun f => ?_
  funext j
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, Pi.add_apply,
    cyclicPositionEnd_apply, derivativeAddScalarEnd_apply, add_sub_cancel_right]
  have hX : successorCoeff k p j * cyclicPositionCoeff k p α (j + 1) = successorCoeff k p j := successorCoeff_mul_cyclicPositionCoeff_succ k p α j
  have hY : cyclicPositionCoeff k p α j * successorCoeff k p (j - 1) = successorCoeff k p (j - 1) := cyclicPositionCoeff_mul_successorCoeff_pred k p α j
  have hw : successorCoeff k p j = successorCoeff k p (j - 1) + 1 := by rw [successorCoeff_eq_cast_add_one, successorCoeff_pred]
  rw [sub_add_cancel]
  linear_combination (f j) * hX - (f j) * hY + (f j) * hw




private def famRepGen (α c : k) : Fin 2 → Module.End k (Fin p → k) :=
  ![cyclicPositionEnd k p α, derivativeAddScalarEnd k p c]

private noncomputable def famRepFree (α c : k) :
    FreeAlgebra k (Fin 2) →ₐ[k] Module.End k (Fin p → k) :=
  FreeAlgebra.lift k (famRepGen k p α c)

private lemma famRep_rel (α c : k) :
    ∀ ⦃a b⦄, RepresentationTheory.FreeAlgebra.PolynomialOperators.auxiliaryRelation k a b → famRepFree k p α c a = famRepFree k p α c b := by
  intro a b ⟨ha, hb⟩
  subst ha; subst hb
  simp only [famRepFree, map_mul, map_add, map_one, FreeAlgebra.lift_ι_apply, famRepGen,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact derivativeAddScalarEnd_mul_cyclicPositionEnd k p α c
/-- The algebra representation on field-valued functions on `Fin p` determined by two scalar parameters. -/



noncomputable def modelRepresentation (α c : k) : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k →ₐ[k] Module.End k (Fin p → k) :=
  RingQuot.liftAlgHom k ⟨famRepFree k p α c, famRep_rel k p α c⟩


/-- The position generator is represented by the cyclic position endomorphism. -/
@[simp] theorem modelRepresentation_positionGenerator (α c : k) : modelRepresentation k p α c (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k) = cyclicPositionEnd k p α := by
  simp [modelRepresentation, RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator, RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.fromFreeAlgebra, RingQuot.liftAlgHom_mkAlgHom_apply, famRepFree,
    FreeAlgebra.lift_ι_apply, famRepGen]


/-- The derivative generator is represented by the derivative-plus-scalar endomorphism. -/
@[simp] theorem modelRepresentation_derivativeGenerator (α c : k) : modelRepresentation k p α c (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator k) = derivativeAddScalarEnd k p c := by
  simp [modelRepresentation, RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator, RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.fromFreeAlgebra, RingQuot.liftAlgHom_mkAlgHom_apply, famRepFree,
    FreeAlgebra.lift_ι_apply, famRepGen]



/-- The module structure of the displayed algebra on field-valued functions on `Fin p` determined by two scalar parameters. -/
@[reducible] noncomputable def modelModule (α c : k) : Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) (Fin p → k) :=
  Module.compHom (Fin p → k) (modelRepresentation k p α c).toRingHom
/-- The model-module action agrees with evaluation of the associated algebra representation. -/


theorem modelModule_smul_eq_representation_apply (α c : k) (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) (f : Fin p → k) :
    letI := modelModule k p α c
    a • f = modelRepresentation k p α c a f := rfl
/-- The base-field and algebra actions on the finite-function model form a scalar tower. -/



theorem modelModule_isScalarTower (α c : k) :
    letI := modelModule k p α c
    IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) (Fin p → k) := by
  letI := modelModule k p α c
  refine ⟨fun a b f => ?_⟩
  change modelRepresentation k p α c (a • b) f = a • (modelRepresentation k p α c b f)
  rw [map_smul, LinearMap.smul_apply]

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- The field-valued functions on `Fin p` have finrank `p`. -/
@[source_ref "Chapter2/Problem2.7.4" (role := supporting)]

theorem finrank_finFunction : Module.finrank k (Fin p → k) = p := by simp



omit [CharP k p] in
private theorem Xlin_pow_apply (α : k) (m : ℕ) (f : Fin p → k) (j : Fin p) :
    (cyclicPositionEnd k p α ^ m) f j
      = (∏ t ∈ range m, cyclicPositionCoeff k p α (j - (t : Fin p))) * f (j - ((m : ℕ) : Fin p)) := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    have hshift : ∀ t : ℕ, j - ((t + 1 : ℕ) : Fin p) = (j - 1) - (t : Fin p) := by
      intro t; rw [Nat.cast_add_one]; abel
    have hprod : ∏ t ∈ range (m + 1), cyclicPositionCoeff k p α (j - (t : Fin p))
        = cyclicPositionCoeff k p α j * ∏ t ∈ range m, cyclicPositionCoeff k p α ((j - 1) - (t : Fin p)) := by
      rw [Finset.prod_range_succ', Finset.prod_congr rfl (fun t _ => by rw [hshift t] :
        ∀ t ∈ range m, cyclicPositionCoeff k p α (j - ((t + 1 : ℕ) : Fin p))
          = cyclicPositionCoeff k p α ((j - 1) - (t : Fin p)))]
      simp only [Nat.cast_zero, sub_zero]
      ring
    rw [pow_succ', Module.End.mul_apply, cyclicPositionEnd_apply, ih (j - 1), hprod, hshift m]
    ring

omit [CharP k p] in
/-- The prime-th power of the cyclic position endomorphism is scalar multiplication by its wraparound parameter. -/

theorem cyclicPositionEnd_pow_prime (α : k) : cyclicPositionEnd k p α ^ p = α • 1 := by
  refine LinearMap.ext fun f => ?_
  funext j
  rw [Xlin_pow_apply]
  have hself : j - ((p : ℕ) : Fin p) = j := by simp
  rw [hself, LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  have hsingle : ∀ t ∈ range p, t ≠ (j : ℕ) → cyclicPositionCoeff k p α (j - (t : Fin p)) = 1 := by
    intro t ht hne
    have hlt : t < p := Finset.mem_range.mp ht
    have hne' : j - (t : Fin p) ≠ 0 := by
      intro h
      apply hne
      have hjt : (t : Fin p) = j := by rw [sub_eq_zero] at h; exact h.symm
      have := congrArg Fin.val hjt
      rwa [Fin.val_cast_of_lt hlt] at this
    rw [cyclicPositionCoeff, if_neg hne']
  rw [Finset.prod_eq_single_of_mem ((j : ℕ)) (Finset.mem_range.mpr j.isLt) hsingle,
    Fin.cast_val_eq_self, sub_self, cyclicPositionCoeff, if_pos rfl]

omit [CharP k p] in
private theorem Ylin_zero_pow_apply (m : ℕ) (f : Fin p → k) (j : Fin p) :
    (derivativeAddScalarEnd k p 0 ^ m) f j
      = (∏ t ∈ range m, successorCoeff k p (j + (t : Fin p))) * f (j + ((m : ℕ) : Fin p)) := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    have hshift : ∀ t : ℕ, j + ((t + 1 : ℕ) : Fin p) = (j + 1) + (t : Fin p) := by
      intro t; rw [Nat.cast_add_one]; abel
    have hprod : ∏ t ∈ range (m + 1), successorCoeff k p (j + (t : Fin p))
        = successorCoeff k p j * ∏ t ∈ range m, successorCoeff k p ((j + 1) + (t : Fin p)) := by
      rw [Finset.prod_range_succ', Finset.prod_congr rfl (fun t _ => by rw [hshift t] :
        ∀ t ∈ range m, successorCoeff k p (j + ((t + 1 : ℕ) : Fin p))
          = successorCoeff k p ((j + 1) + (t : Fin p)))]
      simp only [Nat.cast_zero, add_zero]
      ring
    rw [pow_succ', Module.End.mul_apply, derivativeAddScalarEnd_apply, ih (j + 1), hprod, hshift m]
    ring

omit [CharP k p] in
/-- The prime-th power of the derivative endomorphism with zero scalar term is zero. -/

theorem derivativeEnd_pow_prime : derivativeAddScalarEnd k p 0 ^ p = 0 := by
  refine LinearMap.ext fun f => ?_
  funext j
  rw [Ylin_zero_pow_apply]
  have hzero : ∏ t ∈ range p, successorCoeff k p (j + (t : Fin p)) = 0 := by
    refine Finset.prod_eq_zero (i := ((((-1 : Fin p) - j : Fin p) : ℕ)))
      (Finset.mem_range.mpr (Fin.isLt _)) ?_
    have harg : j + (((((-1 : Fin p) - j : Fin p) : ℕ) : Fin p)) + 1 = 0 := by
      rw [Fin.cast_val_eq_self]; abel
    simp only [successorCoeff, harg]
    simp
  rw [hzero]
  simp
/-- In characteristic `p`, the prime-th power of the derivative-plus-scalar endomorphism is scalar multiplication by the prime-th power of the scalar. -/


theorem derivativeAddScalarEnd_pow_prime (c : k) : derivativeAddScalarEnd k p c ^ p = (c ^ p) • 1 := by
  have hsplit : derivativeAddScalarEnd k p c = c • (1 : Module.End k (Fin p → k)) + derivativeAddScalarEnd k p 0 := by
    refine LinearMap.ext fun f => ?_
    funext j
    simp only [derivativeAddScalarEnd_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, zero_add]
  haveI : Nontrivial (Fin p → k) := by
    haveI : Nonempty (Fin p) := ⟨⟨0, p_pos p⟩⟩
    infer_instance
  haveI : CharP (Module.End k (Fin p → k)) p :=
    charP_of_injective_algebraMap (algebraMap k (Module.End k (Fin p → k))).injective p
  haveI : ExpChar (Module.End k (Fin p → k)) p := ExpChar.prime Fact.out
  have hcomm : Commute (c • (1 : Module.End k (Fin p → k))) (derivativeAddScalarEnd k p 0) :=
    (Commute.one_left (derivativeAddScalarEnd k p 0)).smul_left c
  rw [hsplit, add_pow_char_of_commute p hcomm, derivativeEnd_pow_prime, add_zero,
    smul_pow, one_pow]










omit [Fact (Nat.Prime p)] [CharP k p] in

private lemma exists_top_index (f : Fin p → k) (hf : f ≠ 0) :
    ∃ m : Fin p, f m ≠ 0 ∧ ∀ j, m < j → f j = 0 := by
  classical
  have hne : (Finset.univ.filter fun j : Fin p => f j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hf
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, by simpa using hj⟩⟩
  refine ⟨_, (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2, fun j hj => ?_⟩
  by_contra h0
  exact absurd (Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h0⟩))
    (not_le.mpr hj)

omit [Fact (Nat.Prime p)] [CharP k p] in

private lemma smul_single_one (a : k) (j : Fin p) :
    a • Pi.single j (1 : k) = Pi.single j a := by
  rw [← Pi.single_smul, smul_eq_mul, mul_one]
/-- For a function vanishing above an index, the corresponding power of the derivative endomorphism is the indexed value times the factorial and the zeroth coordinate vector. -/








theorem derivativeEnd_pow_eq_factorial_smul_single_zero (f : Fin p → k) (m : Fin p) (hmax : ∀ j, m < j → f j = 0) :
    (derivativeAddScalarEnd k p 0 ^ (m : ℕ)) f
      = ((Nat.factorial (m : ℕ) : k) * f m) • Pi.single (0 : Fin p) (1 : k) := by
  funext j
  rw [Ylin_zero_pow_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = 0
  · subst hj
    have hprod : ∏ t ∈ range (m : ℕ), successorCoeff k p ((0 : Fin p) + ((t : ℕ) : Fin p))
        = (Nat.factorial (m : ℕ) : k) := by
      have hcongr : ∀ t ∈ range (m : ℕ),
          successorCoeff k p ((0 : Fin p) + ((t : ℕ) : Fin p)) = ((t + 1 : ℕ) : k) := by
        intro t ht
        have htp : t < p := lt_trans (Finset.mem_range.mp ht) m.isLt
        rw [zero_add, successorCoeff_eq_cast_add_one, Fin.val_cast_of_lt htp]
        push_cast
        ring
      rw [Finset.prod_congr rfl hcongr, ← Nat.cast_prod,
        Finset.prod_range_add_one_eq_factorial]
    rw [hprod, Pi.single_eq_same, mul_one, zero_add, Fin.cast_val_eq_self]
  · simp only [Pi.single_apply, if_neg hj, mul_zero]
    have hjne : (j : ℕ) ≠ 0 := by
      intro h
      exact hj (by ext; simp [h])
    have hjlt : (j : ℕ) < p := j.isLt
    have hmlt : (m : ℕ) < p := m.isLt
    rcases lt_or_ge ((j : ℕ) + (m : ℕ)) p with hlt | hge
    ·
      have hval : ((j + (((m : ℕ) : ℕ) : Fin p) : Fin p) : ℕ) = (j : ℕ) + (m : ℕ) := by
        rw [Fin.val_add, Fin.val_cast_of_lt hmlt, Nat.mod_eq_of_lt hlt]
      have hgt : m < j + (((m : ℕ) : ℕ) : Fin p) := by
        rw [Fin.lt_def, hval]; omega
      rw [hmax _ hgt, mul_zero]
    ·
      set t₀ := p - 1 - (j : ℕ) with ht₀
      have ht₀m : t₀ < (m : ℕ) := by omega
      have hsum : ((j : ℕ) : Fin p) + ((t₀ : ℕ) : Fin p) + 1 = 0 := by
        have hcast : (((j : ℕ) + t₀ + 1 : ℕ) : Fin p)
            = ((j : ℕ) : Fin p) + ((t₀ : ℕ) : Fin p) + 1 := by
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
        rw [← hcast, show (j : ℕ) + t₀ + 1 = p by omega]
        simp
      rw [Fin.cast_val_eq_self] at hsum
      have hzero : successorCoeff k p (j + ((t₀ : ℕ) : Fin p)) = 0 := by rw [successorCoeff, hsum]; simp
      rw [Finset.prod_eq_zero (Finset.mem_range.mpr ht₀m) hzero, zero_mul]

omit [CharP k p] in
/-- Below the prime bound, the corresponding power of the cyclic position endomorphism sends the zeroth coordinate vector to the coordinate vector at that exponent. -/



theorem cyclicPositionEnd_pow_single_zero (α : k) (i : ℕ) (hi : i < p) :
    (cyclicPositionEnd k p α ^ i) (Pi.single (0 : Fin p) (1 : k)) = Pi.single ((i : ℕ) : Fin p) (1 : k) := by
  funext j
  rw [Xlin_pow_apply]
  by_cases hj : j = ((i : ℕ) : Fin p)
  · subst hj
    have hprod : ∏ t ∈ range i, cyclicPositionCoeff k p α (((i : ℕ) : Fin p) - ((t : ℕ) : Fin p)) = 1 := by
      refine Finset.prod_eq_one fun t ht => ?_
      have htlt : t < i := Finset.mem_range.mp ht
      have hne : ((i : ℕ) : Fin p) - ((t : ℕ) : Fin p) ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        have hv := congrArg Fin.val h
        rw [Fin.val_cast_of_lt hi, Fin.val_cast_of_lt (htlt.trans hi)] at hv
        omega
      rw [cyclicPositionCoeff, if_neg hne]
    rw [hprod, one_mul, sub_self]
    simp
  · have hsub : j - ((i : ℕ) : Fin p) ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      exact hj h
    simp [hsub, hj]
/-- Subtracting the scalar term from the derivative generator is represented by the derivative endomorphism with zero scalar term. -/



theorem modelRepresentation_derivativeGenerator_sub_scalar (α c : k) :
    modelRepresentation k p α c (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator k - c • 1) = derivativeAddScalarEnd k p 0 := by
  rw [map_sub, map_smul, map_one, modelRepresentation_derivativeGenerator]
  refine LinearMap.ext fun f => ?_
  funext j
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, derivativeAddScalarEnd_apply, zero_mul, zero_add]
  ring
/-- The base-field and algebra scalar actions on the finite-function model commute. -/



theorem modelModule_smulCommClass (α c : k) :
    letI := modelModule k p α c
    SMulCommClass k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) (Fin p → k) := by
  letI := modelModule k p α c
  refine ⟨fun a b f => ?_⟩
  change a • modelRepresentation k p α c b f = modelRepresentation k p α c b (a • f)
  rw [map_smul]
/-- The finite-function model is a simple module over the displayed algebra. -/
@[source_ref "Chapter2/Problem2.7.4" (role := supporting)]





theorem modelModule_isSimpleModule (α c : k) :
    letI := modelModule k p α c
    IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) (Fin p → k) := by
  letI := modelModule k p α c
  haveI := modelModule_isScalarTower k p α c
  haveI := modelModule_smulCommClass k p α c
  haveI : Nontrivial (Fin p → k) := by
    haveI : Nonempty (Fin p) := ⟨⟨0, p_pos p⟩⟩
    infer_instance
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, fun f hf z => ?_⟩
  obtain ⟨m, hfm, hmax⟩ := exists_top_index k p f hf

  set s : k := (Nat.factorial (m : ℕ) : k) * f m with hs
  have hs0 : s ≠ 0 := by
    rw [hs]
    refine mul_ne_zero (fun h => ?_) hfm
    have hd : p ∣ Nat.factorial (m : ℕ) := (CharP.cast_eq_zero_iff k p _).mp h
    exact absurd ((Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp hd) (not_le.mpr m.isLt)
  set y₀ : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k := RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator k - c • 1 with hy₀
  have key : (y₀ ^ (m : ℕ)) • f = s • (Pi.single (0 : Fin p) (1 : k) : Fin p → k) := by
    rw [hs, hy₀, modelModule_smul_eq_representation_apply, map_pow, modelRepresentation_derivativeGenerator_sub_scalar]
    exact derivativeEnd_pow_eq_factorial_smul_single_zero k p f m hmax
  have hx : ∀ j : Fin p,
      (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k ^ (j : ℕ)) • (Pi.single (0 : Fin p) (1 : k) : Fin p → k)
        = (Pi.single j (1 : k) : Fin p → k) := by
    intro j
    rw [modelModule_smul_eq_representation_apply, map_pow, modelRepresentation_positionGenerator, cyclicPositionEnd_pow_single_zero k p α (j : ℕ) j.isLt,
      Fin.cast_val_eq_self]
  refine ⟨∑ j : Fin p, (s⁻¹ * z j) • (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k ^ (j : ℕ) * y₀ ^ (m : ℕ)), ?_⟩
  rw [LinearMap.toSpanSingleton_apply, Finset.sum_smul]
  have step : ∀ j : Fin p,
      ((s⁻¹ * z j) • (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k ^ (j : ℕ) * y₀ ^ (m : ℕ))) • f
        = (Pi.single j (z j) : Fin p → k) := by
    intro j
    have e1 : ((s⁻¹ * z j) • (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k ^ (j : ℕ) * y₀ ^ (m : ℕ))) • f
        = (s⁻¹ * z j) • ((RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k ^ (j : ℕ) * y₀ ^ (m : ℕ)) • f) := smul_assoc _ _ _
    have e2 : (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k ^ (j : ℕ) * y₀ ^ (m : ℕ)) • f
        = (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k ^ (j : ℕ)) • ((y₀ ^ (m : ℕ)) • f) := mul_smul _ _ _
    have e3 : s • ((RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k ^ (j : ℕ)) •
          (Pi.single (0 : Fin p) (1 : k) : Fin p → k))
        = (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k ^ (j : ℕ)) • (s • (Pi.single (0 : Fin p) (1 : k) : Fin p → k)) :=
      smul_comm _ _ _
    rw [e1, e2, key, ← e3, hx j, smul_smul (s⁻¹ * z j) s,
      show s⁻¹ * z j * s = z j by
        rw [mul_comm s⁻¹ (z j), mul_assoc, inv_mul_cancel₀ hs0, mul_one],
      smul_single_one]
  rw [Finset.sum_congr rfl fun j _ => step j]
  exact Finset.univ_sum_single z
/-- Over an algebraically closed field of prime characteristic, every scalar has a unique prime-th root. -/






theorem existsUnique_pow_prime_eq [IsAlgClosed k] (β : k) : ∃! c : k, c ^ p = β := by
  haveI : ExpChar k p := ExpChar.prime Fact.out
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq β (p_pos p)
  refine ⟨c, hc, fun d hd => ?_⟩
  have : (d - c) ^ p = 0 := by
    rw [sub_pow_char, hd, hc, sub_self]
  have hdc : d - c = 0 := pow_eq_zero_iff (n := p) (Fact.out : p.Prime).ne_zero |>.mp this
  exact sub_eq_zero.mp hdc
/-- In a field of prime characteristic, equality of prime-th powers implies equality of the original scalars. -/



theorem eq_of_pow_prime_eq_pow_prime {c c' : k} (h : c ^ p = c' ^ p) : c = c' := by
  haveI : ExpChar k p := ExpChar.prime Fact.out
  have h0 : (c - c') ^ p = 0 := by rw [sub_pow_char, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := p) (Fact.out : p.Prime).ne_zero |>.mp h0)













/-- An auxiliary type parameterized by four elements of a field of prime characteristic. -/
abbrev FourScalarParameterType (α c α' c' : k) : Type _ :=
  @LinearEquiv (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) _ _
    (RingHom.id (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k)) (RingHom.id (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k)) _ _
    (Fin p → k) (Fin p → k) _ _ (modelModule k p α c) (modelModule k p α' c')

variable {k p}
/-- A map represented by the four-scalar auxiliary type intertwines the two displayed algebra actions. -/


theorem fourScalarParameterMap_intertwines_action {α c α' c' : k} (e : FourScalarParameterType k p α c α' c') (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k)
    (f : Fin p → k) : e (modelRepresentation k p α c a f) = modelRepresentation k p α' c' a (e f) :=
  map_smulₛₗ e a f
/-- A map represented by the four-scalar auxiliary type commutes with scalar multiplication by the base field. -/



theorem fourScalarParameterMap_map_smul {α c α' c' : k} (e : FourScalarParameterType k p α c α' c') (a : k)
    (f : Fin p → k) : e (a • f) = a • e f := by
  have h := fourScalarParameterMap_intertwines_action e (algebraMap k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) a) f
  simpa only [AlgHom.commutes, Module.algebraMap_end_apply] using h

variable (k p)
/-- The four-scalar auxiliary type is nonempty exactly when the first pair of parameters equals the second pair componentwise. -/
@[source_ref "Chapter2/Problem2.7.4" (role := supporting)]











theorem nonempty_fourScalarParameterType_iff (α c α' c' : k) :
    Nonempty (FourScalarParameterType k p α c α' c') ↔ α = α' ∧ c = c' := by
  constructor
  · rintro ⟨e⟩

    haveI : Nonempty (Fin p) := ⟨⟨0, p_pos p⟩⟩
    obtain ⟨g, hg⟩ := exists_ne (0 : Fin p → k)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hg
    rw [Pi.zero_apply] at hj
    obtain ⟨f, rfl⟩ : ∃ f, e f = g := ⟨e.symm g, e.apply_symm_apply g⟩

    have hx := fourScalarParameterMap_intertwines_action e (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k ^ p) f

    have hy := fourScalarParameterMap_intertwines_action e (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator k ^ p) f
    simp only [map_pow, modelRepresentation_positionGenerator, modelRepresentation_derivativeGenerator, cyclicPositionEnd_pow_prime, derivativeAddScalarEnd_pow_prime, LinearMap.smul_apply,
      Module.End.one_apply, fourScalarParameterMap_map_smul e] at hx hy
    refine ⟨?_, eq_of_pow_prime_eq_pow_prime k p ?_⟩
    · have := congrFun hx j
      simpa only [Pi.smul_apply, smul_eq_mul] using mul_right_cancel₀ hj this
    · have := congrFun hy j
      simpa only [Pi.smul_apply, smul_eq_mul] using mul_right_cancel₀ hj this
  · rintro ⟨rfl, rfl⟩
    exact ⟨@LinearEquiv.refl (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) (Fin p → k) _ _ (modelModule k p α c)⟩









omit [Fact (Nat.Prime p)] [CharP k p] in
/-- A base-linear map that intertwines the actions of both distinguished generators intertwines the action of every algebra element. -/



theorem map_smul_of_map_smul_generators {V W : Type*}
    [AddCommGroup V] [Module k V] [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V]
    [AddCommGroup W] [Module k W] [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) W] [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) W]
    (e : V →ₗ[k] W)
    (hx : ∀ z : V, e (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k • z) = RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k • e z)
    (hy : ∀ z : V, e (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator k • z) = RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator k • e z) :
    ∀ (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) (z : V), e (a • z) = a • e z := by
  intro a
  obtain ⟨a', rfl⟩ := RingQuot.mkAlgHom_surjective k (RepresentationTheory.FreeAlgebra.PolynomialOperators.auxiliaryRelation k) a
  have ha' : a' ∈ Algebra.adjoin k (Set.range (FreeAlgebra.ι k)) := by
    rw [FreeAlgebra.adjoin_range_ι]; exact Algebra.mem_top
  induction ha' using Algebra.adjoin_induction with
  | mem g hg =>
      obtain ⟨idx, rfl⟩ := hg
      intro z
      fin_cases idx
      · exact hx z
      · exact hy z
  | algebraMap r =>
      intro z
      rw [AlgHom.commutes, algebraMap_smul, algebraMap_smul, map_smul]
  | add u v _ _ ihu ihv =>
      intro z
      rw [map_add, add_smul, map_add, ihu, ihv, add_smul]
  | mul u v _ _ ihu ihv =>
      intro z
      rw [map_mul, mul_smul, ihu, ihv, mul_smul]




/-- An auxiliary type parameterized by a module over the displayed algebra and two field elements. -/
abbrev ModuleScalarParameterType (V : Type*) [AddCommGroup V] [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] (α c : k) : Type _ :=
  @LinearEquiv (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) _ _
    (RingHom.id (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k)) (RingHom.id (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k)) _ _
    V (Fin p → k) _ _ inferInstance (modelModule k p α c)
/-- For every finite-dimensional simple module over the displayed algebra, the associated auxiliary type is nonempty for some pair of field elements. -/
@[source_ref "Chapter2/Problem2.7.4" (role := supporting)]





theorem exists_nonempty_moduleScalarParameterType [IsAlgClosed k] (V : Type*) [AddCommGroup V] [Module k V]
    [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] [FiniteDimensional k V]
    [IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] :
    ∃ α c : k, Nonempty (ModuleScalarParameterType k p V α c) := by
  obtain ⟨α, c, b, hbx, hby⟩ :=
    RepresentationTheory.NoncommutativeAlgebra.PositiveCharacteristic.exists_cyclic_basis_of_simpleModule k p V
  refine ⟨α, c, ?_⟩
  letI := modelModule k p α c
  haveI := modelModule_isScalarTower k p α c

  set ψ : (Fin p → k) ≃ₗ[k] V := b.equivFun.symm
  have hψ : ∀ f : Fin p → k, ψ f = ∑ j, f j • b j := fun f => b.equivFun_symm_apply f

  have reindex : ∀ g : Fin p → V, ∑ j, g j = ∑ i : Fin p, g (i + 1) := by
    intro g
    exact (Fintype.sum_equiv (Equiv.addRight (1 : Fin p)) (fun i => g (i + 1)) g
      (fun i => by simp)).symm
  have hx : ∀ f : Fin p → k, ψ (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k • f) = RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k • ψ f := by
    intro f
    have hsm : (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator k • f : Fin p → k) = cyclicPositionEnd k p α f := by
      rw [modelModule_smul_eq_representation_apply k p α c, modelRepresentation_positionGenerator]
    rw [hsm, hψ, hψ, Finset.smul_sum, reindex fun j => cyclicPositionEnd k p α f j • b j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm, hbx i, smul_smul, cyclicPositionEnd_apply, add_sub_cancel_right, cyclicPositionCoeff, mul_comm]
  have hy : ∀ f : Fin p → k, ψ (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator k • f) = RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator k • ψ f := by
    intro f
    have hsm : (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator k • f : Fin p → k) = derivativeAddScalarEnd k p c f := by
      rw [modelModule_smul_eq_representation_apply k p α c, modelRepresentation_derivativeGenerator]

    have hR : ∑ j, RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator k • (f j • b j)
        = ∑ i : Fin p, ((c * f (i + 1)) • b (i + 1) + (successorCoeff k p i * f (i + 1)) • b i) := by
      rw [reindex fun j => RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator k • (f j • b j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, hby i, smul_add, smul_smul, smul_smul, successorCoeff_eq_cast_add_one]
      push_cast
      rw [mul_comm (f (i + 1)) c, mul_comm (f (i + 1)) (((i : ℕ) : k) + 1)]
    have hL : ∑ j, derivativeAddScalarEnd k p c f j • b j
        = ∑ j : Fin p, ((c * f j) • b j + (successorCoeff k p j * f (j + 1)) • b j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [derivativeAddScalarEnd_apply, add_smul]
    rw [hsm, hψ, hψ, Finset.smul_sum, hR, hL, Finset.sum_add_distrib, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) (reindex fun j => (c * f j) • b j) rfl
  have hlin := map_smul_of_map_smul_generators k (ψ : (Fin p → k) →ₗ[k] V) hx hy
  exact ⟨(show @LinearEquiv (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) _ _
      (RingHom.id (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k)) (RingHom.id (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k)) _ _
      (Fin p → k) V _ _ (modelModule k p α c) _ from
    { toFun := ψ, map_add' := ψ.map_add, map_smul' := hlin
      invFun := ψ.symm, left_inv := ψ.left_inv, right_inv := ψ.right_inv }).symm⟩

variable {k p}
/-- The map represented by an element of the module-and-scalars auxiliary type commutes with scalar multiplication by the base field. -/



theorem moduleScalarParameterMap_map_smul {V : Type*} [AddCommGroup V] [Module k V]
    [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] {α c : k}
    (e : ModuleScalarParameterType k p V α c) (a : k) (z : V) : e (a • z) = a • e z := by
  letI := modelModule k p α c
  have h : e (algebraMap k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) a • z) = algebraMap k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) a • e z :=
    map_smulₛₗ e _ z
  rw [algebraMap_smul] at h
  rw [h, modelModule_smul_eq_representation_apply k p α c, AlgHom.commutes, Module.algebraMap_end_apply]

variable (k p)
/-- An element of the module-and-scalars auxiliary type determines a base-field linear equivalence with the finite-function space. -/


noncomputable def moduleScalarParameterTypeToLinearEquiv {V : Type*} [AddCommGroup V] [Module k V]
    [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] {α c : k}
    (e : ModuleScalarParameterType k p V α c) : V ≃ₗ[k] (Fin p → k) :=
  letI := modelModule k p α c
  { toFun := e
    map_add' := e.map_add
    map_smul' := fun a z => moduleScalarParameterMap_map_smul e a z
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }
/-- For every finite-dimensional simple module over the displayed algebra, there is a unique pair of field elements for which the associated auxiliary type is nonempty. -/
@[source_ref "Chapter2/Problem2.7.4" (role := supporting)]












theorem existsUnique_nonempty_moduleScalarParameterType [IsAlgClosed k] (V : Type*) [AddCommGroup V] [Module k V]
    [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] [FiniteDimensional k V]
    [IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] :
    ∃! q : k × k, Nonempty (ModuleScalarParameterType k p V q.1 q.2) := by
  obtain ⟨α, c, ⟨e⟩⟩ := exists_nonempty_moduleScalarParameterType k p V
  refine ⟨(α, c), ⟨e⟩, ?_⟩
  rintro ⟨α', c'⟩ ⟨e'⟩
  obtain ⟨h1, h2⟩ := (nonempty_fourScalarParameterType_iff k p α' c' α c).mp ⟨e'.symm.trans e⟩
  exact Prod.ext h1 h2
/-- Every finite-dimensional simple module over the displayed algebra has finrank equal to the field characteristic. -/




theorem finrank_eq_prime_of_isSimpleModule [IsAlgClosed k] (V : Type*) [AddCommGroup V] [Module k V]
    [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] [FiniteDimensional k V]
    [IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra k) V] :
    Module.finrank k V = p := by
  obtain ⟨α, c, ⟨e⟩⟩ := exists_nonempty_moduleScalarParameterType k p V
  rw [(moduleScalarParameterTypeToLinearEquiv k p e).finrank_eq, finrank_finFunction k p]

end Family

end RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels



attribute [nolint defsWithUnderscore]
  RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.cyclicPositionCoeff RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.cyclicPositionEnd
  RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.successorCoeff RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.derivativeAddScalarEnd
  RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.modelRepresentation RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.modelModule
  RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.FourScalarParameterType RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.ModuleScalarParameterType
  RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.moduleScalarParameterTypeToLinearEquiv
