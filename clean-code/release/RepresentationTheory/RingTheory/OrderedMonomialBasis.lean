/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators
import Mathlib.Data.Prod.Lex

/-! # Ordered monomial basis -/

namespace RepresentationTheory

open Module

variable (k : Type*) [CommRing k] [Nontrivial k]

@[simp] private theorem ofLex_add (p q : ℕ ×ₗ ℕ) :
    ofLex (p + q) = ofLex p + ofLex q := rfl

private theorem toLex_add (p q : ℕ × ℕ) :
    toLex (p + q) = toLex p + toLex q := rfl

@[simp] private theorem add_toLex (p q : ℕ × ℕ) :
    toLex p + toLex q = toLex (p + q) := rfl

@[simp] private theorem toLex_zero_pair :
    toLex (0, 0) = (0 : ℕ ×ₗ ℕ) := rfl

/-- The lexicographically indexed monomials form a basis over the coefficient ring. -/
noncomputable def FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis :
    Basis (ℕ ×ₗ ℕ) k (FreeAlgebra.PolynomialOperators.OperatorAlgebra k) :=
  (Basis.mk (Algebra.IntegerIndexedPolynomialOperators.operatorMonomials_linearIndependent_and_span k).1
    (Algebra.IntegerIndexedPolynomialOperators.operatorMonomials_linearIndependent_and_span k).2).reindex toLex

/-- Evaluating the monomial basis at an index gives the monomial with the two corresponding exponents. -/
@[simp] theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis_apply (p : ℕ ×ₗ ℕ) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k p =
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k (ofLex p).1 (ofLex p).2 := by
  rw [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis, Basis.reindex_apply, Basis.mk_apply]
  rfl

/-- The linear functional extracting the coefficient of a lexicographically indexed monomial. -/
noncomputable def FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff (p : ℕ ×ₗ ℕ) : FreeAlgebra.PolynomialOperators.OperatorAlgebra k →ₗ[k] k :=
  (Finsupp.lapply p).comp (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k).repr.toLinearMap

/-- A monomial coefficient functional evaluates on a basis monomial as the corresponding Kronecker delta. -/
@[simp] theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis (p q : ℕ ×ₗ ℕ) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k q) = if q = p then 1 else 0 := by
  change ((FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k).repr (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k q)) p = _
  rw [(FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k).repr_self]
  simp [Finsupp.single_apply, eq_comm]

/-- The submodule spanned up to a lexicographic monomial index. -/
noncomputable def FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration (p : ℕ ×ₗ ℕ) :
    Submodule k (FreeAlgebra.PolynomialOperators.OperatorAlgebra k) :=
  Submodule.span k ((FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k) '' Set.Iic p)

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwBasis_mem_filtration {p q : ℕ ×ₗ ℕ} (hqp : q ≤ p) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k q ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p :=
  Submodule.subset_span ⟨q, hqp, rfl⟩

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_eq_zero_of_mem_filtration
    {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p q : ℕ ×ₗ ℕ}
    (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p) (hqp : ¬ q ≤ p) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k q a = 0 := by
  apply Submodule.span_induction (R := k)
    (s := (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k) '' Set.Iic p)
    (p := fun a _ => FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k q a = 0)
  · intro a ha
    obtain ⟨r, hrp, rfl⟩ := ha
    rw [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis, if_neg]
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
private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.y_mul_x_pow_succ (n : ℕ) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) =
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k +
        (n + 1) • FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ n := by
  induction n with
  | zero => simpa using FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator_mul_firstOperator k
  | succ n ih =>
      calc
        FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1 + 1) =
            FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) * FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k := by
              rw [pow_succ, mul_assoc]
        _ = (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k +
              (n + 1) • FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ n) * FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k := by rw [ih]
        _ = FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) *
              (FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k) +
              (n + 1) • FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) := by
              rw [add_mul, mul_assoc, smul_mul_assoc, ← pow_succ]
        _ = FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) *
              (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k + 1) +
              (n + 1) • FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) := by
              rw [FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator_mul_firstOperator]
        _ = FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1 + 1) * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k +
              (n + 1 + 1) • FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) := by
              rw [mul_add, mul_one, ← mul_assoc, ← pow_succ, add_assoc,
                add_comm (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1))
                  ((n + 1) • FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1)), ← succ_nsmul]

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.y_mul_pbwBasis (p : ℕ ×ₗ ℕ) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k p =
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k (p + toLex (0, 1)) +
        (ofLex p).1 • FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k
          (toLex ((ofLex p).1 - 1, (ofLex p).2)) := by
  induction p using Lex.rec with | _ p =>
    rcases p with ⟨i, j⟩
    cases i with
    | zero => simp [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator, pow_succ']
    | succ i =>
        simp only [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, add_zero]
        rw [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator,
          ← mul_assoc, FreeAlgebra.PolynomialOperators.OperatorAlgebra.y_mul_x_pow_succ, add_mul, smul_mul_assoc]
        simp only [pow_succ', mul_assoc, Nat.succ_sub_one]

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.y_mul_filtration {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (p + toLex (0, 1)) := by
  apply Submodule.span_induction (R := k)
    (s := (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k) '' Set.Iic p)
    (p := fun a _ => FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * a ∈
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (p + toLex (0, 1)))
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    rw [FreeAlgebra.PolynomialOperators.OperatorAlgebra.y_mul_pbwBasis]
    apply (FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (p + toLex (0, 1))).add_mem
    · exact FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwBasis_mem_filtration k (lex_add_le_add hqp le_rfl)
    · apply (FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (p + toLex (0, 1))).smul_mem
      apply FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwBasis_mem_filtration k
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
    exact (FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k _).add_mem ha hb
  · intro c a _ ha
    rw [mul_smul_comm]
    exact (FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k _).smul_mem c ha
  · exact ha

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_y_mul {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (p + toLex (0, 1)) (FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * a) =
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p a := by
  apply Submodule.span_induction (R := k)
    (s := (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k) '' Set.Iic p)
    (p := fun a _ => FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (p + toLex (0, 1))
      (FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * a) = FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p a)
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    rw [FreeAlgebra.PolynomialOperators.OperatorAlgebra.y_mul_pbwBasis, map_add, map_nsmul,
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis,
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis]
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

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.x_mul_filtration {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (toLex (1, 0) + p) := by
  apply Submodule.span_induction (R := k)
    (s := (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k) '' Set.Iic p)
    (p := fun a _ => FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * a ∈
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (toLex (1, 0) + p))
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k q =
        FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k (toLex (1, 0) + q) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp only [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, zero_add, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator]
        rw [show 1 + i = i + 1 by omega, pow_succ', mul_assoc]
    rw [hmul]
    exact FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwBasis_mem_filtration k (lex_add_le_add le_rfl hqp)
  · simp
  · intro a b _ _ ha hb
    simpa [mul_add] using (FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k _).add_mem ha hb
  · intro c a _ ha
    simpa [mul_smul_comm] using (FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k _).smul_mem c ha
  · exact ha

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_x_mul {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (toLex (1, 0) + p) (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * a) =
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p a := by
  apply Submodule.span_induction (R := k)
    (s := (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k) '' Set.Iic p)
    (p := fun a _ => FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (toLex (1, 0) + p)
      (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * a) = FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p a)
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k q =
        FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k (toLex (1, 0) + q) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp only [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, zero_add, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator]
        rw [show 1 + i = i + 1 by omega, pow_succ', mul_assoc]
    rw [hmul, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis]
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

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.mul_y_filtration {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p) :
    a * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (p + toLex (0, 1)) := by
  apply Submodule.span_induction (R := k)
    (s := (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k) '' Set.Iic p)
    (p := fun a _ => a * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ∈
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (p + toLex (0, 1)))
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k q * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k =
        FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k (q + toLex (0, 1)) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp only [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, add_zero, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator]
        rw [pow_succ, mul_assoc]
    rw [hmul]
    exact FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwBasis_mem_filtration k (lex_add_le_add hqp le_rfl)
  · simp
  · intro a b _ _ ha hb
    simpa [add_mul] using (FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k _).add_mem ha hb
  · intro c a _ ha
    simpa [smul_mul_assoc] using (FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k _).smul_mem c ha
  · exact ha

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_mul_y {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (p + toLex (0, 1)) (a * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k) =
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p a := by
  apply Submodule.span_induction (R := k)
    (s := (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k) '' Set.Iic p)
    (p := fun a _ => FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (p + toLex (0, 1))
      (a * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k) = FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p a)
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k q * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k =
        FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k (q + toLex (0, 1)) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator, pow_succ, mul_assoc]
    rw [hmul, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis]
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

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.y_pow_mul_x_pow_mem (i j : ℕ) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ j * FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i ∈
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (toLex (i, j)) := by
  induction j with
  | zero =>
      simpa only [pow_zero, one_mul, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis_apply, ofLex_toLex,
        FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator, pow_zero, mul_one] using
        FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwBasis_mem_filtration k (p := toLex (i, 0)) le_rfl
  | succ j ih =>
      rw [pow_succ', mul_assoc]
      simpa using FreeAlgebra.PolynomialOperators.OperatorAlgebra.y_mul_filtration k ih

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_y_pow_mul_x_pow (i j : ℕ) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (toLex (i, j))
      (FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ j * FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i) = 1 := by
  induction j with
  | zero =>
      rw [pow_zero, one_mul,
        ← show FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k (toLex (i, 0)) = FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i by
          simp [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator]]
      rw [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis, if_pos rfl]
  | succ j ih =>
      rw [pow_succ', mul_assoc]
      have h := FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_y_mul k
        (FreeAlgebra.PolynomialOperators.OperatorAlgebra.y_pow_mul_x_pow_mem k i j)
      simpa using h.trans ih

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.x_pow_mul_filtration {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p : ℕ ×ₗ ℕ}
    (i : ℕ) (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i * a ∈
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (toLex (i, 0) + p) := by
  induction i with
  | zero => simpa using ha
  | succ i ih =>
      rw [pow_succ', mul_assoc]
      have h := FreeAlgebra.PolynomialOperators.OperatorAlgebra.x_mul_filtration k ih
      have hfront : toLex (1, 0) + toLex (i, 0) = toLex (i + 1, 0) := by
        apply ofLex.injective
        change (1 + i, 0 + 0) = (i + 1, 0)
        simp [Nat.add_comm]
      have hidx : toLex (1, 0) + (toLex (i, 0) + p) = toLex (i + 1, 0) + p := by
        rw [← add_assoc, hfront]
      rwa [hidx] at h

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_x_pow_mul {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p : ℕ ×ₗ ℕ}
    (i : ℕ) (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (toLex (i, 0) + p) (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i * a) =
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p a := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ', mul_assoc]
      have h := FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_x_mul k
        (FreeAlgebra.PolynomialOperators.OperatorAlgebra.x_pow_mul_filtration k i ha)
      have hfront : toLex (1, 0) + toLex (i, 0) = toLex (i + 1, 0) := by
        apply ofLex.injective
        change (1 + i, 0 + 0) = (i + 1, 0)
        simp [Nat.add_comm]
      have hidx : toLex (1, 0) + (toLex (i, 0) + p) = toLex (i + 1, 0) + p := by
        rw [← add_assoc, hfront]
      rw [hidx] at h
      exact h.trans ih

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.mul_y_pow_filtration {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p : ℕ ×ₗ ℕ}
    (j : ℕ) (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p) :
    a * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ j ∈
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (p + toLex (0, j)) := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
      rw [pow_succ, ← mul_assoc]
      simpa [add_assoc] using FreeAlgebra.PolynomialOperators.OperatorAlgebra.mul_y_filtration k ih

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_mul_y_pow {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p : ℕ ×ₗ ℕ}
    (j : ℕ) (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (p + toLex (0, j)) (a * FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ j) =
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p a := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, ← mul_assoc]
      have h := FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_mul_y k
        (FreeAlgebra.PolynomialOperators.OperatorAlgebra.mul_y_pow_filtration k j ha)
      simpa [add_assoc] using h.trans ih

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwBasis_mul_mem (p q : ℕ ×ₗ ℕ) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k p * FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k q ∈
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k (p + q) := by
  induction p using Lex.rec with | _ p =>
    induction q using Lex.rec with | _ q =>
      rcases p with ⟨i, j⟩
      rcases q with ⟨u, v⟩
      simp only [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis_apply, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator, ofLex_toLex]
      rw [mul_assoc (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i) (FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ j),
        ← mul_assoc (FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ j) (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ u),
        ← mul_assoc (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i)]
      have hmid := FreeAlgebra.PolynomialOperators.OperatorAlgebra.y_pow_mul_x_pow_mem k u j
      have hleft := FreeAlgebra.PolynomialOperators.OperatorAlgebra.x_pow_mul_filtration k i hmid
      have hright := FreeAlgebra.PolynomialOperators.OperatorAlgebra.mul_y_pow_filtration k v hleft
      simpa [add_assoc] using hright

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_basis_mul (p q : ℕ ×ₗ ℕ) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (p + q)
      (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k p * FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k q) = 1 := by
  induction p using Lex.rec with | _ p =>
    induction q using Lex.rec with | _ q =>
      rcases p with ⟨i, j⟩
      rcases q with ⟨u, v⟩
      simp only [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis_apply, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator, ofLex_toLex]
      rw [mul_assoc (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i) (FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ j),
        ← mul_assoc (FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ j) (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ u),
        ← mul_assoc (FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i)]
      have hmid := FreeAlgebra.PolynomialOperators.OperatorAlgebra.y_pow_mul_x_pow_mem k u j
      have hleft := FreeAlgebra.PolynomialOperators.OperatorAlgebra.x_pow_mul_filtration k i hmid
      have h1 := FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_mul_y_pow k v hleft
      have h2 := FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_x_pow_mul k i hmid
      have h3 := FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_y_pow_mul_x_pow k u j
      simpa [add_assoc] using h1.trans (h2.trans h3)

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_basis_mul_of_le
    {p q r s : ℕ ×ₗ ℕ} (hrp : r ≤ p) (hsq : s ≤ q) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (p + q)
      (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k r * FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k s) =
        FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k r) *
          FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k q (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k s) := by
  by_cases hr : r = p
  · subst r
    by_cases hs : s = q
    · subst s
      rw [FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_basis_mul, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis,
        FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis, if_pos rfl, if_pos rfl, mul_one]
    · have hslt : s < q := lt_of_le_of_ne hsq hs
      have hlt : p + s < p + q := lex_add_lt_add_of_le_of_lt le_rfl hslt
      rw [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis, FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis, if_pos rfl, if_neg hs,
        mul_zero]
      exact FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_eq_zero_of_mem_filtration k
        (FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwBasis_mul_mem k p s) (not_le_of_gt hlt)
  · have hrlt : r < p := lt_of_le_of_ne hrp hr
    have hlt : r + s < p + q := lex_add_lt_add_of_lt_of_le hrlt hsq
    rw [FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_basis, if_neg hr, zero_mul]
    exact FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_eq_zero_of_mem_filtration k
      (FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwBasis_mul_mem k r s) (not_le_of_gt hlt)

/-- For elements in prescribed filtration pieces, the coefficient at the sum of their indices is the product of the leading coefficients. -/
theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_mul
    {a b : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} {p q : ℕ ×ₗ ℕ}
    (ha : a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p)
    (hb : b ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k q) :
    FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (p + q) (a * b) =
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p a * FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k q b := by
  apply Submodule.span_induction (R := k)
    (s := (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k) '' Set.Iic p)
    (p := fun a _ => FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (p + q) (a * b) =
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p a * FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k q b)
  · intro a ha
    obtain ⟨r, hrp, rfl⟩ := ha
    apply Submodule.span_induction (R := k)
      (s := (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k) '' Set.Iic q)
      (p := fun b _ => FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k (p + q)
        (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k r * b) =
          FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k r) *
            FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k q b)
    · intro b hb
      obtain ⟨s, hsq, rfl⟩ := hb
      exact FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwCoeff_basis_mul_of_le k hrp hsq
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

private theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.exists_leading
    {a : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} (ha : a ≠ 0) :
    ∃ p : ℕ ×ₗ ℕ, a ∈ FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p ∧
      FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff k p a ≠ 0 := by
  classical
  set f := (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k).repr a
  have hf : f ≠ 0 := fun hf => ha ((FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k).repr.injective
    (hf.trans (map_zero _).symm))
  have hsupport : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  let p := f.support.max' hsupport
  refine ⟨p, ?_, ?_⟩
  · have heq : (Finsupp.linearCombination k (FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialBasis k)) f = a := by
      simp [f]
    rw [← heq, Finsupp.linearCombination_apply]
    apply Submodule.sum_mem
    intro q hq
    exact (FreeAlgebra.PolynomialOperators.OperatorAlgebra.degreeFiltration k p).smul_mem _
      (FreeAlgebra.PolynomialOperators.OperatorAlgebra.pbwBasis_mem_filtration k (Finset.le_max' f.support q hq))
  · change f p ≠ 0
    exact Finsupp.mem_support_iff.mp (Finset.max'_mem f.support hsupport)

/-- The product of two nonzero elements is nonzero when the coefficient ring has no zero divisors. -/
theorem FreeAlgebra.PolynomialOperators.OperatorAlgebra.mul_ne_zero [NoZeroDivisors k]
    {a b : FreeAlgebra.PolynomialOperators.OperatorAlgebra k} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  classical
  obtain ⟨p, haF, hap⟩ := FreeAlgebra.PolynomialOperators.OperatorAlgebra.exists_leading k ha
  obtain ⟨q, hbF, hbq⟩ := FreeAlgebra.PolynomialOperators.OperatorAlgebra.exists_leading k hb
  intro hab
  have hcoeff := FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialCoeff_mul k haF hbF
  rw [hab, map_zero] at hcoeff
  exact (_root_.mul_ne_zero hap hbq) hcoeff.symm

/-- The monomial algebra has no zero divisors when its coefficient ring does. -/
noncomputable instance RingTheory.OrderedMonomialBasis.noZeroDivisors [NoZeroDivisors k] :
    NoZeroDivisors (FreeAlgebra.PolynomialOperators.OperatorAlgebra k) :=
  noZeroDivisors_iff (FreeAlgebra.PolynomialOperators.OperatorAlgebra k) |>.2 fun {a b} hab => by
    by_contra h
    push Not at h
    exact FreeAlgebra.PolynomialOperators.OperatorAlgebra.mul_ne_zero k h.1 h.2 hab

end RepresentationTheory
