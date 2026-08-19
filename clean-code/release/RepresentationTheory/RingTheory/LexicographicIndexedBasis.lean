/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators
import Mathlib.Data.Prod.Lex

namespace RepresentationTheory.FreeAlgebra.PolynomialOperators

namespace AuxiliaryAlgebra

open Module
open RepresentationTheory.FreeAlgebra.PolynomialOperators
open RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators

variable (k : Type*) [CommRing k] [Nontrivial k]

@[simp] private theorem ofLex_add (p q : ℕ ×ₗ ℕ) :
    ofLex (p + q) = ofLex p + ofLex q := rfl

private theorem toLex_add (p q : ℕ × ℕ) :
    toLex (p + q) = toLex p + toLex q := rfl

@[simp] private theorem add_toLex (p q : ℕ × ℕ) :
    toLex p + toLex q = toLex (p + q) := rfl

@[simp] private theorem toLex_zero_pair :
    toLex (0, 0) = (0 : ℕ ×ₗ ℕ) := rfl


/-- A basis of the associated algebra indexed lexicographically by pairs of natural numbers. -/
noncomputable def indexedBasis :
    Basis (ℕ ×ₗ ℕ) k (AuxiliaryAlgebra k) :=
  (Basis.mk (operatorMonomials_linearIndependent_and_span k).1
    (operatorMonomials_linearIndependent_and_span k).2).reindex toLex

/-- Evaluating the indexed basis at a lexicographic pair gives the displayed auxiliary element at
its two coordinates. -/
@[simp] theorem indexedBasis_apply (p : ℕ ×ₗ ℕ) :
    AuxiliaryAlgebra.indexedBasis k p =
      AuxiliaryAlgebra.indexedElement k (ofLex p).1 (ofLex p).2 := by
  rw [AuxiliaryAlgebra.indexedBasis, Basis.reindex_apply, Basis.mk_apply]
  rfl


/-- A linear functional on the associated algebra for each lexicographic pair of natural numbers. -/
noncomputable def coordinate (p : ℕ ×ₗ ℕ) : AuxiliaryAlgebra k →ₗ[k] k :=
  (Finsupp.lapply p).comp (AuxiliaryAlgebra.indexedBasis k).repr.toLinearMap

/-- The coordinate functional evaluates on an indexed basis element as one when the indices agree
and zero otherwise. -/
@[simp] theorem coordinate_indexedBasis (p q : ℕ ×ₗ ℕ) :
    AuxiliaryAlgebra.coordinate k p (AuxiliaryAlgebra.indexedBasis k q) = if q = p then 1 else 0 := by
  change ((AuxiliaryAlgebra.indexedBasis k).repr (AuxiliaryAlgebra.indexedBasis k q)) p = _
  rw [(AuxiliaryAlgebra.indexedBasis k).repr_self]
  simp [Finsupp.single_apply, eq_comm]


/-- An auxiliary submodule of the associated algebra for each lexicographic pair of natural
numbers. -/
noncomputable def auxiliaryIndexedSubmodule (p : ℕ ×ₗ ℕ) :
    Submodule k (AuxiliaryAlgebra k) :=
  Submodule.span k ((AuxiliaryAlgebra.indexedBasis k) '' Set.Iic p)

private theorem pbwBasis_mem_filtration {p q : ℕ ×ₗ ℕ} (hqp : q ≤ p) :
    AuxiliaryAlgebra.indexedBasis k q ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p :=
  Submodule.subset_span ⟨q, hqp, rfl⟩

private theorem pbwCoeff_eq_zero_of_mem_filtration
    {a : AuxiliaryAlgebra k} {p q : ℕ ×ₗ ℕ}
    (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p) (hqp : ¬ q ≤ p) :
    AuxiliaryAlgebra.coordinate k q a = 0 := by
  apply Submodule.span_induction (R := k)
    (s := (AuxiliaryAlgebra.indexedBasis k) '' Set.Iic p)
    (p := fun a _ => AuxiliaryAlgebra.coordinate k q a = 0)
  · intro a ha
    obtain ⟨r, hrp, rfl⟩ := ha
    rw [AuxiliaryAlgebra.coordinate_indexedBasis, if_neg]
    intro hrq
    subst r
    exact hqp hrp
  · exact map_zero _
  · intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  · intro c a _ ha
    rw [map_smul, ha, smul_zero]
  · exact ha

private theorem lex_add_le_add {a b c d : ℕ ×ₗ ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d := by
  induction a using Lex.rec with | _ a =>
    induction b using Lex.rec with | _ b =>
      induction c using Lex.rec with | _ c =>
        induction d using Lex.rec with | _ d =>
          rcases a with ⟨a₁, a₂⟩
          rcases b with ⟨b₁, b₂⟩
          rcases c with ⟨c₁, c₂⟩
          rcases d with ⟨d₁, d₂⟩
          rw [Prod.Lex.toLex_le_toLex] at hab hcd
          change toLex (a₁ + c₁, a₂ + c₂) ≤ toLex (b₁ + d₁, b₂ + d₂)
          rw [Prod.Lex.toLex_le_toLex]
          rcases hab with hab | ⟨rfl, hab⟩
          · rcases hcd with hcd | ⟨rfl, hcd⟩
            · exact Or.inl (Nat.add_lt_add hab hcd)
            · exact Or.inl (Nat.add_lt_add_right hab _)
          · rcases hcd with hcd | ⟨rfl, hcd⟩
            · exact Or.inl (Nat.add_lt_add_left hcd _)
            · exact Or.inr ⟨rfl, Nat.add_le_add hab hcd⟩

private theorem lex_add_lt_add_of_lt_of_le {a b c d : ℕ ×ₗ ℕ}
    (hab : a < b) (hcd : c ≤ d) : a + c < b + d := by
  induction a using Lex.rec with | _ a =>
    induction b using Lex.rec with | _ b =>
      induction c using Lex.rec with | _ c =>
        induction d using Lex.rec with | _ d =>
          rcases a with ⟨a₁, a₂⟩
          rcases b with ⟨b₁, b₂⟩
          rcases c with ⟨c₁, c₂⟩
          rcases d with ⟨d₁, d₂⟩
          rw [Prod.Lex.toLex_lt_toLex] at hab
          rw [Prod.Lex.toLex_le_toLex] at hcd
          change toLex (a₁ + c₁, a₂ + c₂) < toLex (b₁ + d₁, b₂ + d₂)
          rw [Prod.Lex.toLex_lt_toLex]
          rcases hab with hab | ⟨rfl, hab⟩
          · rcases hcd with hcd | ⟨rfl, hcd⟩
            · exact Or.inl (Nat.add_lt_add hab hcd)
            · exact Or.inl (Nat.add_lt_add_right hab _)
          · rcases hcd with hcd | ⟨rfl, hcd⟩
            · exact Or.inl (Nat.add_lt_add_left hcd _)
            · exact Or.inr ⟨rfl, Nat.add_lt_add_of_lt_of_le hab hcd⟩

private theorem lex_add_lt_add_of_le_of_lt {a b c d : ℕ ×ₗ ℕ}
    (hab : a ≤ b) (hcd : c < d) : a + c < b + d := by
  rw [add_comm a c, add_comm b d]
  exact lex_add_lt_add_of_lt_of_le hcd hab

omit [Nontrivial k] in

private theorem y_mul_x_pow_succ (n : ℕ) :
    AuxiliaryAlgebra.secondOperator k * AuxiliaryAlgebra.firstOperator k ^ (n + 1) =
      AuxiliaryAlgebra.firstOperator k ^ (n + 1) * AuxiliaryAlgebra.secondOperator k +
        (n + 1) • AuxiliaryAlgebra.firstOperator k ^ n := by
  induction n with
  | zero => simpa using AuxiliaryAlgebra.secondOperator_mul_firstOperator k
  | succ n ih =>
      calc
        AuxiliaryAlgebra.secondOperator k * AuxiliaryAlgebra.firstOperator k ^ (n + 1 + 1) =
            AuxiliaryAlgebra.secondOperator k * AuxiliaryAlgebra.firstOperator k ^ (n + 1) * AuxiliaryAlgebra.firstOperator k := by
              rw [pow_succ, mul_assoc]
        _ = (AuxiliaryAlgebra.firstOperator k ^ (n + 1) * AuxiliaryAlgebra.secondOperator k +
              (n + 1) • AuxiliaryAlgebra.firstOperator k ^ n) * AuxiliaryAlgebra.firstOperator k := by rw [ih]
        _ = AuxiliaryAlgebra.firstOperator k ^ (n + 1) *
              (AuxiliaryAlgebra.secondOperator k * AuxiliaryAlgebra.firstOperator k) +
              (n + 1) • AuxiliaryAlgebra.firstOperator k ^ (n + 1) := by
              rw [add_mul, mul_assoc, smul_mul_assoc, ← pow_succ]
        _ = AuxiliaryAlgebra.firstOperator k ^ (n + 1) *
              (AuxiliaryAlgebra.firstOperator k * AuxiliaryAlgebra.secondOperator k + 1) +
              (n + 1) • AuxiliaryAlgebra.firstOperator k ^ (n + 1) := by
              rw [AuxiliaryAlgebra.secondOperator_mul_firstOperator]
        _ = AuxiliaryAlgebra.firstOperator k ^ (n + 1 + 1) * AuxiliaryAlgebra.secondOperator k +
              (n + 1 + 1) • AuxiliaryAlgebra.firstOperator k ^ (n + 1) := by
              rw [mul_add, mul_one, ← mul_assoc, ← pow_succ, add_assoc,
                add_comm (AuxiliaryAlgebra.firstOperator k ^ (n + 1))
                  ((n + 1) • AuxiliaryAlgebra.firstOperator k ^ (n + 1)), ← succ_nsmul]

private theorem y_mul_pbwBasis (p : ℕ ×ₗ ℕ) :
    AuxiliaryAlgebra.secondOperator k * AuxiliaryAlgebra.indexedBasis k p =
      AuxiliaryAlgebra.indexedBasis k (p + toLex (0, 1)) +
        (ofLex p).1 • AuxiliaryAlgebra.indexedBasis k
          (toLex ((ofLex p).1 - 1, (ofLex p).2)) := by
  induction p using Lex.rec with | _ p =>
    rcases p with ⟨i, j⟩
    cases i with
    | zero => simp [AuxiliaryAlgebra.indexedElement, pow_succ']
    | succ i =>
        simp only [AuxiliaryAlgebra.indexedBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, add_zero]
        rw [AuxiliaryAlgebra.indexedElement, AuxiliaryAlgebra.indexedElement, AuxiliaryAlgebra.indexedElement,
          ← mul_assoc, AuxiliaryAlgebra.y_mul_x_pow_succ, add_mul, smul_mul_assoc]
        simp only [pow_succ', mul_assoc, Nat.succ_sub_one]

private theorem y_mul_filtration {a : AuxiliaryAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p) :
    AuxiliaryAlgebra.secondOperator k * a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (p + toLex (0, 1)) := by
  apply Submodule.span_induction (R := k)
    (s := (AuxiliaryAlgebra.indexedBasis k) '' Set.Iic p)
    (p := fun a _ => AuxiliaryAlgebra.secondOperator k * a ∈
      AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (p + toLex (0, 1)))
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    rw [AuxiliaryAlgebra.y_mul_pbwBasis]
    apply (AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (p + toLex (0, 1))).add_mem
    · exact AuxiliaryAlgebra.pbwBasis_mem_filtration k (lex_add_le_add hqp le_rfl)
    · apply (AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (p + toLex (0, 1))).smul_mem
      apply AuxiliaryAlgebra.pbwBasis_mem_filtration k
      induction q using Lex.rec with | _ q =>
        induction p using Lex.rec with | _ p =>
          rcases q with ⟨i, j⟩
          rcases p with ⟨u, v⟩
          simp only [ofLex_toLex]
          apply le_trans ?_ (lex_add_le_add hqp le_rfl)
          rw [show toLex (i, j) + toLex (0, 1) = toLex (i, j + 1) by rfl,
            Prod.Lex.toLex_le_toLex]
          omega
  · rw [mul_zero]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [mul_add]
    exact (AuxiliaryAlgebra.auxiliaryIndexedSubmodule k _).add_mem ha hb
  · intro c a _ ha
    rw [mul_smul_comm]
    exact (AuxiliaryAlgebra.auxiliaryIndexedSubmodule k _).smul_mem c ha
  · exact ha

private theorem pbwCoeff_y_mul {a : AuxiliaryAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p) :
    AuxiliaryAlgebra.coordinate k (p + toLex (0, 1)) (AuxiliaryAlgebra.secondOperator k * a) =
      AuxiliaryAlgebra.coordinate k p a := by
  apply Submodule.span_induction (R := k)
    (s := (AuxiliaryAlgebra.indexedBasis k) '' Set.Iic p)
    (p := fun a _ => AuxiliaryAlgebra.coordinate k (p + toLex (0, 1))
      (AuxiliaryAlgebra.secondOperator k * a) = AuxiliaryAlgebra.coordinate k p a)
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    rw [AuxiliaryAlgebra.y_mul_pbwBasis, map_add, map_nsmul,
      AuxiliaryAlgebra.coordinate_indexedBasis, AuxiliaryAlgebra.coordinate_indexedBasis,
      AuxiliaryAlgebra.coordinate_indexedBasis]
    have hcorrlt : toLex ((ofLex q).1 - 1, (ofLex q).2) < q + toLex (0, 1) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp only [ofLex_toLex]
        rw [show toLex (i, j) + toLex (0, 1) = toLex (i, j + 1) by rfl,
          Prod.Lex.toLex_lt_toLex]
        omega
    have hcorr : toLex ((ofLex q).1 - 1, (ofLex q).2) ≠ p + toLex (0, 1) :=
      ne_of_lt (lt_of_lt_of_le hcorrlt (lex_add_le_add hqp le_rfl))
    by_cases hqp' : q = p
    · subst q
      rw [if_pos rfl, if_neg hcorr, if_pos rfl]
      simp
    · have hqplt : q < p := lt_of_le_of_ne hqp hqp'
      have hadd : q + toLex (0, 1) ≠ p + toLex (0, 1) :=
        ne_of_lt (lex_add_lt_add_of_lt_of_le hqplt le_rfl)
      rw [if_neg hadd, if_neg hcorr, if_neg hqp']
      simp
  · simp
  · intro a b _ _ ha hb
    simpa [mul_add] using congrArg₂ (· + ·) ha hb
  · intro c a _ ha
    simpa [mul_smul_comm] using congrArg (fun z => c • z) ha
  · exact ha

private theorem x_mul_filtration {a : AuxiliaryAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p) :
    AuxiliaryAlgebra.firstOperator k * a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (toLex (1, 0) + p) := by
  apply Submodule.span_induction (R := k)
    (s := (AuxiliaryAlgebra.indexedBasis k) '' Set.Iic p)
    (p := fun a _ => AuxiliaryAlgebra.firstOperator k * a ∈
      AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (toLex (1, 0) + p))
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : AuxiliaryAlgebra.firstOperator k * AuxiliaryAlgebra.indexedBasis k q =
        AuxiliaryAlgebra.indexedBasis k (toLex (1, 0) + q) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp only [AuxiliaryAlgebra.indexedBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, zero_add, AuxiliaryAlgebra.indexedElement]
        rw [show 1 + i = i + 1 by omega, pow_succ', mul_assoc]
    rw [hmul]
    exact AuxiliaryAlgebra.pbwBasis_mem_filtration k (lex_add_le_add le_rfl hqp)
  · simp
  · intro a b _ _ ha hb
    simpa [mul_add] using (AuxiliaryAlgebra.auxiliaryIndexedSubmodule k _).add_mem ha hb
  · intro c a _ ha
    simpa [mul_smul_comm] using (AuxiliaryAlgebra.auxiliaryIndexedSubmodule k _).smul_mem c ha
  · exact ha

private theorem pbwCoeff_x_mul {a : AuxiliaryAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p) :
    AuxiliaryAlgebra.coordinate k (toLex (1, 0) + p) (AuxiliaryAlgebra.firstOperator k * a) =
      AuxiliaryAlgebra.coordinate k p a := by
  apply Submodule.span_induction (R := k)
    (s := (AuxiliaryAlgebra.indexedBasis k) '' Set.Iic p)
    (p := fun a _ => AuxiliaryAlgebra.coordinate k (toLex (1, 0) + p)
      (AuxiliaryAlgebra.firstOperator k * a) = AuxiliaryAlgebra.coordinate k p a)
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : AuxiliaryAlgebra.firstOperator k * AuxiliaryAlgebra.indexedBasis k q =
        AuxiliaryAlgebra.indexedBasis k (toLex (1, 0) + q) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp only [AuxiliaryAlgebra.indexedBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, zero_add, AuxiliaryAlgebra.indexedElement]
        rw [show 1 + i = i + 1 by omega, pow_succ', mul_assoc]
    rw [hmul, AuxiliaryAlgebra.coordinate_indexedBasis, AuxiliaryAlgebra.coordinate_indexedBasis]
    by_cases h : q = p
    · subst q
      simp
    · rw [if_neg h, if_neg]
      intro hadd
      exact h (add_left_cancel hadd)
  · simp
  · intro a b _ _ ha hb
    simpa [mul_add] using congrArg₂ (· + ·) ha hb
  · intro c a _ ha
    simpa [mul_smul_comm] using congrArg (fun z => c • z) ha
  · exact ha

private theorem mul_y_filtration {a : AuxiliaryAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p) :
    a * AuxiliaryAlgebra.secondOperator k ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (p + toLex (0, 1)) := by
  apply Submodule.span_induction (R := k)
    (s := (AuxiliaryAlgebra.indexedBasis k) '' Set.Iic p)
    (p := fun a _ => a * AuxiliaryAlgebra.secondOperator k ∈
      AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (p + toLex (0, 1)))
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : AuxiliaryAlgebra.indexedBasis k q * AuxiliaryAlgebra.secondOperator k =
        AuxiliaryAlgebra.indexedBasis k (q + toLex (0, 1)) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp only [AuxiliaryAlgebra.indexedBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, add_zero, AuxiliaryAlgebra.indexedElement]
        rw [pow_succ, mul_assoc]
    rw [hmul]
    exact AuxiliaryAlgebra.pbwBasis_mem_filtration k (lex_add_le_add hqp le_rfl)
  · simp
  · intro a b _ _ ha hb
    simpa [add_mul] using (AuxiliaryAlgebra.auxiliaryIndexedSubmodule k _).add_mem ha hb
  · intro c a _ ha
    simpa [smul_mul_assoc] using (AuxiliaryAlgebra.auxiliaryIndexedSubmodule k _).smul_mem c ha
  · exact ha

private theorem pbwCoeff_mul_y {a : AuxiliaryAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p) :
    AuxiliaryAlgebra.coordinate k (p + toLex (0, 1)) (a * AuxiliaryAlgebra.secondOperator k) =
      AuxiliaryAlgebra.coordinate k p a := by
  apply Submodule.span_induction (R := k)
    (s := (AuxiliaryAlgebra.indexedBasis k) '' Set.Iic p)
    (p := fun a _ => AuxiliaryAlgebra.coordinate k (p + toLex (0, 1))
      (a * AuxiliaryAlgebra.secondOperator k) = AuxiliaryAlgebra.coordinate k p a)
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : AuxiliaryAlgebra.indexedBasis k q * AuxiliaryAlgebra.secondOperator k =
        AuxiliaryAlgebra.indexedBasis k (q + toLex (0, 1)) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp [AuxiliaryAlgebra.indexedElement, pow_succ, mul_assoc]
    rw [hmul, AuxiliaryAlgebra.coordinate_indexedBasis, AuxiliaryAlgebra.coordinate_indexedBasis]
    by_cases h : q = p
    · subst q
      simp
    · rw [if_neg h, if_neg]
      intro hadd
      exact h (add_right_cancel hadd)
  · simp
  · intro a b _ _ ha hb
    simpa [add_mul] using congrArg₂ (· + ·) ha hb
  · intro c a _ ha
    simpa [smul_mul_assoc] using congrArg (fun z => c • z) ha
  · exact ha

private theorem y_pow_mul_x_pow_mem (i j : ℕ) :
    AuxiliaryAlgebra.secondOperator k ^ j * AuxiliaryAlgebra.firstOperator k ^ i ∈
      AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (toLex (i, j)) := by
  induction j with
  | zero =>
      simpa only [pow_zero, one_mul, AuxiliaryAlgebra.indexedBasis_apply, ofLex_toLex,
        AuxiliaryAlgebra.indexedElement, pow_zero, mul_one] using
        AuxiliaryAlgebra.pbwBasis_mem_filtration k (p := toLex (i, 0)) le_rfl
  | succ j ih =>
      rw [pow_succ', mul_assoc]
      simpa using AuxiliaryAlgebra.y_mul_filtration k ih

private theorem pbwCoeff_y_pow_mul_x_pow (i j : ℕ) :
    AuxiliaryAlgebra.coordinate k (toLex (i, j))
      (AuxiliaryAlgebra.secondOperator k ^ j * AuxiliaryAlgebra.firstOperator k ^ i) = 1 := by
  induction j with
  | zero =>
      rw [pow_zero, one_mul,
        ← show AuxiliaryAlgebra.indexedBasis k (toLex (i, 0)) = AuxiliaryAlgebra.firstOperator k ^ i by
          simp [AuxiliaryAlgebra.indexedElement]]
      rw [AuxiliaryAlgebra.coordinate_indexedBasis, if_pos rfl]
  | succ j ih =>
      rw [pow_succ', mul_assoc]
      have h := AuxiliaryAlgebra.pbwCoeff_y_mul k
        (AuxiliaryAlgebra.y_pow_mul_x_pow_mem k i j)
      simpa using h.trans ih

private theorem x_pow_mul_filtration {a : AuxiliaryAlgebra k} {p : ℕ ×ₗ ℕ}
    (i : ℕ) (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p) :
    AuxiliaryAlgebra.firstOperator k ^ i * a ∈
      AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (toLex (i, 0) + p) := by
  induction i with
  | zero => simpa using ha
  | succ i ih =>
      rw [pow_succ', mul_assoc]
      have h := AuxiliaryAlgebra.x_mul_filtration k ih
      have hfront : toLex (1, 0) + toLex (i, 0) = toLex (i + 1, 0) := by
        apply ofLex.injective
        change (1 + i, 0 + 0) = (i + 1, 0)
        simp [Nat.add_comm]
      have hidx : toLex (1, 0) + (toLex (i, 0) + p) = toLex (i + 1, 0) + p := by
        rw [← add_assoc, hfront]
      rwa [hidx] at h

private theorem pbwCoeff_x_pow_mul {a : AuxiliaryAlgebra k} {p : ℕ ×ₗ ℕ}
    (i : ℕ) (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p) :
    AuxiliaryAlgebra.coordinate k (toLex (i, 0) + p) (AuxiliaryAlgebra.firstOperator k ^ i * a) =
      AuxiliaryAlgebra.coordinate k p a := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ', mul_assoc]
      have h := AuxiliaryAlgebra.pbwCoeff_x_mul k
        (AuxiliaryAlgebra.x_pow_mul_filtration k i ha)
      have hfront : toLex (1, 0) + toLex (i, 0) = toLex (i + 1, 0) := by
        apply ofLex.injective
        change (1 + i, 0 + 0) = (i + 1, 0)
        simp [Nat.add_comm]
      have hidx : toLex (1, 0) + (toLex (i, 0) + p) = toLex (i + 1, 0) + p := by
        rw [← add_assoc, hfront]
      rw [hidx] at h
      exact h.trans ih

private theorem mul_y_pow_filtration {a : AuxiliaryAlgebra k} {p : ℕ ×ₗ ℕ}
    (j : ℕ) (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p) :
    a * AuxiliaryAlgebra.secondOperator k ^ j ∈
      AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (p + toLex (0, j)) := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
      rw [pow_succ, ← mul_assoc]
      simpa [add_assoc] using AuxiliaryAlgebra.mul_y_filtration k ih

private theorem pbwCoeff_mul_y_pow {a : AuxiliaryAlgebra k} {p : ℕ ×ₗ ℕ}
    (j : ℕ) (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p) :
    AuxiliaryAlgebra.coordinate k (p + toLex (0, j)) (a * AuxiliaryAlgebra.secondOperator k ^ j) =
      AuxiliaryAlgebra.coordinate k p a := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, ← mul_assoc]
      have h := AuxiliaryAlgebra.pbwCoeff_mul_y k
        (AuxiliaryAlgebra.mul_y_pow_filtration k j ha)
      simpa [add_assoc] using h.trans ih

private theorem pbwBasis_mul_mem (p q : ℕ ×ₗ ℕ) :
    AuxiliaryAlgebra.indexedBasis k p * AuxiliaryAlgebra.indexedBasis k q ∈
      AuxiliaryAlgebra.auxiliaryIndexedSubmodule k (p + q) := by
  induction p using Lex.rec with | _ p =>
    induction q using Lex.rec with | _ q =>
      rcases p with ⟨i, j⟩
      rcases q with ⟨u, v⟩
      simp only [AuxiliaryAlgebra.indexedBasis_apply, AuxiliaryAlgebra.indexedElement, ofLex_toLex]
      rw [mul_assoc (AuxiliaryAlgebra.firstOperator k ^ i) (AuxiliaryAlgebra.secondOperator k ^ j),
        ← mul_assoc (AuxiliaryAlgebra.secondOperator k ^ j) (AuxiliaryAlgebra.firstOperator k ^ u),
        ← mul_assoc (AuxiliaryAlgebra.firstOperator k ^ i)]
      have hmid := AuxiliaryAlgebra.y_pow_mul_x_pow_mem k u j
      have hleft := AuxiliaryAlgebra.x_pow_mul_filtration k i hmid
      have hright := AuxiliaryAlgebra.mul_y_pow_filtration k v hleft
      simpa [add_assoc] using hright

private theorem pbwCoeff_basis_mul (p q : ℕ ×ₗ ℕ) :
    AuxiliaryAlgebra.coordinate k (p + q)
      (AuxiliaryAlgebra.indexedBasis k p * AuxiliaryAlgebra.indexedBasis k q) = 1 := by
  induction p using Lex.rec with | _ p =>
    induction q using Lex.rec with | _ q =>
      rcases p with ⟨i, j⟩
      rcases q with ⟨u, v⟩
      simp only [AuxiliaryAlgebra.indexedBasis_apply, AuxiliaryAlgebra.indexedElement, ofLex_toLex]
      rw [mul_assoc (AuxiliaryAlgebra.firstOperator k ^ i) (AuxiliaryAlgebra.secondOperator k ^ j),
        ← mul_assoc (AuxiliaryAlgebra.secondOperator k ^ j) (AuxiliaryAlgebra.firstOperator k ^ u),
        ← mul_assoc (AuxiliaryAlgebra.firstOperator k ^ i)]
      have hmid := AuxiliaryAlgebra.y_pow_mul_x_pow_mem k u j
      have hleft := AuxiliaryAlgebra.x_pow_mul_filtration k i hmid
      have h1 := AuxiliaryAlgebra.pbwCoeff_mul_y_pow k v hleft
      have h2 := AuxiliaryAlgebra.pbwCoeff_x_pow_mul k i hmid
      have h3 := AuxiliaryAlgebra.pbwCoeff_y_pow_mul_x_pow k u j
      simpa [add_assoc] using h1.trans (h2.trans h3)

private theorem pbwCoeff_basis_mul_of_le
    {p q r s : ℕ ×ₗ ℕ} (hrp : r ≤ p) (hsq : s ≤ q) :
    AuxiliaryAlgebra.coordinate k (p + q)
      (AuxiliaryAlgebra.indexedBasis k r * AuxiliaryAlgebra.indexedBasis k s) =
        AuxiliaryAlgebra.coordinate k p (AuxiliaryAlgebra.indexedBasis k r) *
          AuxiliaryAlgebra.coordinate k q (AuxiliaryAlgebra.indexedBasis k s) := by
  by_cases hr : r = p
  · subst r
    by_cases hs : s = q
    · subst s
      rw [AuxiliaryAlgebra.pbwCoeff_basis_mul, AuxiliaryAlgebra.coordinate_indexedBasis,
        AuxiliaryAlgebra.coordinate_indexedBasis, if_pos rfl, if_pos rfl, mul_one]
    · have hslt : s < q := lt_of_le_of_ne hsq hs
      have hlt : p + s < p + q := lex_add_lt_add_of_le_of_lt le_rfl hslt
      rw [AuxiliaryAlgebra.coordinate_indexedBasis, AuxiliaryAlgebra.coordinate_indexedBasis, if_pos rfl, if_neg hs,
        mul_zero]
      exact AuxiliaryAlgebra.pbwCoeff_eq_zero_of_mem_filtration k
        (AuxiliaryAlgebra.pbwBasis_mul_mem k p s) (not_le_of_gt hlt)
  · have hrlt : r < p := lt_of_le_of_ne hrp hr
    have hlt : r + s < p + q := lex_add_lt_add_of_lt_of_le hrlt hsq
    rw [AuxiliaryAlgebra.coordinate_indexedBasis, if_neg hr, zero_mul]
    exact AuxiliaryAlgebra.pbwCoeff_eq_zero_of_mem_filtration k
      (AuxiliaryAlgebra.pbwBasis_mul_mem k r s) (not_le_of_gt hlt)


/-- For elements in the displayed indexed submodules, the coordinate of their product at the sum
index is the product of the corresponding coordinates. -/
theorem coordinate_mul
    {a b : AuxiliaryAlgebra k} {p q : ℕ ×ₗ ℕ}
    (ha : a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p)
    (hb : b ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k q) :
    AuxiliaryAlgebra.coordinate k (p + q) (a * b) =
      AuxiliaryAlgebra.coordinate k p a * AuxiliaryAlgebra.coordinate k q b := by
  apply Submodule.span_induction (R := k)
    (s := (AuxiliaryAlgebra.indexedBasis k) '' Set.Iic p)
    (p := fun a _ => AuxiliaryAlgebra.coordinate k (p + q) (a * b) =
      AuxiliaryAlgebra.coordinate k p a * AuxiliaryAlgebra.coordinate k q b)
  · intro a ha
    obtain ⟨r, hrp, rfl⟩ := ha
    apply Submodule.span_induction (R := k)
      (s := (AuxiliaryAlgebra.indexedBasis k) '' Set.Iic q)
      (p := fun b _ => AuxiliaryAlgebra.coordinate k (p + q)
        (AuxiliaryAlgebra.indexedBasis k r * b) =
          AuxiliaryAlgebra.coordinate k p (AuxiliaryAlgebra.indexedBasis k r) *
            AuxiliaryAlgebra.coordinate k q b)
    · intro b hb
      obtain ⟨s, hsq, rfl⟩ := hb
      exact AuxiliaryAlgebra.pbwCoeff_basis_mul_of_le k hrp hsq
    · simp
    · intro x y _ _ hx hy
      simpa [mul_add, mul_add] using congrArg₂ (· + ·) hx hy
    · intro c x _ hx
      simpa [mul_smul_comm, mul_assoc, mul_comm, mul_left_comm] using
        congrArg (fun z => c • z) hx
    · exact hb
  · simp
  · intro x y _ _ hx hy
    simpa [add_mul, add_mul] using congrArg₂ (· + ·) hx hy
  · intro c x _ hx
    simpa [smul_mul_assoc, mul_assoc] using congrArg (fun z => c • z) hx
  · exact ha

private theorem exists_leading
    {a : AuxiliaryAlgebra k} (ha : a ≠ 0) :
    ∃ p : ℕ ×ₗ ℕ, a ∈ AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p ∧
      AuxiliaryAlgebra.coordinate k p a ≠ 0 := by
  classical
  set f := (AuxiliaryAlgebra.indexedBasis k).repr a
  have hf : f ≠ 0 := fun hf => ha ((AuxiliaryAlgebra.indexedBasis k).repr.injective
    (hf.trans (map_zero _).symm))
  have hsupport : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  let p := f.support.max' hsupport
  refine ⟨p, ?_, ?_⟩
  · have heq : (Finsupp.linearCombination k (AuxiliaryAlgebra.indexedBasis k)) f = a := by
      simp [f]
    rw [← heq, Finsupp.linearCombination_apply]
    apply Submodule.sum_mem
    intro q hq
    exact (AuxiliaryAlgebra.auxiliaryIndexedSubmodule k p).smul_mem _
      (AuxiliaryAlgebra.pbwBasis_mem_filtration k (Finset.le_max' f.support q hq))
  · change f p ≠ 0
    exact Finsupp.mem_support_iff.mp (Finset.max'_mem f.support hsupport)



/-- The product of two nonzero elements of the associated algebra is nonzero when the coefficient ring has no zero divisors. -/
theorem mul_ne_zero [NoZeroDivisors k]
    {a b : AuxiliaryAlgebra k} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  classical
  obtain ⟨p, haF, hap⟩ := AuxiliaryAlgebra.exists_leading k ha
  obtain ⟨q, hbF, hbq⟩ := AuxiliaryAlgebra.exists_leading k hb
  intro hab
  have hcoeff := AuxiliaryAlgebra.coordinate_mul k haF hbF
  rw [hab, map_zero] at hcoeff
  exact (_root_.mul_ne_zero hap hbq) hcoeff.symm

end AuxiliaryAlgebra

end RepresentationTheory.FreeAlgebra.PolynomialOperators

namespace RepresentationTheory.RingTheory.LexicographicIndexedBasis

open RepresentationTheory.FreeAlgebra.PolynomialOperators

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- The associated algebra has no zero divisors when its coefficient ring does. -/
noncomputable instance noZeroDivisors [NoZeroDivisors k] : NoZeroDivisors (AuxiliaryAlgebra k) :=
  noZeroDivisors_iff (AuxiliaryAlgebra k) |>.2 fun {a b} hab => by
    by_contra h
    push Not at h
    exact AuxiliaryAlgebra.mul_ne_zero k h.1 h.2 hab

end RepresentationTheory.RingTheory.LexicographicIndexedBasis
