/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators
import Mathlib.Data.Prod.Lex
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.RingTheory.LexicographicIndexedBasis

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


noncomputable def WeylAlgebra.pbwBasis :
    Basis (ℕ ×ₗ ℕ) k (WeylAlgebra k) :=
  (Basis.mk (Proposition_2_7_1_charFree k).1
    (Proposition_2_7_1_charFree k).2).reindex toLex

@[simp] theorem WeylAlgebra.pbwBasis_apply (p : ℕ ×ₗ ℕ) :
    WeylAlgebra.pbwBasis k p =
      WeylAlgebra.monomial k (ofLex p).1 (ofLex p).2 := by
  rw [WeylAlgebra.pbwBasis, Basis.reindex_apply, Basis.mk_apply]
  rfl


noncomputable def WeylAlgebra.pbwCoeff (p : ℕ ×ₗ ℕ) : WeylAlgebra k →ₗ[k] k :=
  (Finsupp.lapply p).comp (WeylAlgebra.pbwBasis k).repr.toLinearMap

@[simp] theorem WeylAlgebra.pbwCoeff_basis (p q : ℕ ×ₗ ℕ) :
    WeylAlgebra.pbwCoeff k p (WeylAlgebra.pbwBasis k q) = if q = p then 1 else 0 := by
  change ((WeylAlgebra.pbwBasis k).repr (WeylAlgebra.pbwBasis k q)) p = _
  rw [(WeylAlgebra.pbwBasis k).repr_self]
  simp [Finsupp.single_apply, eq_comm]


noncomputable def WeylAlgebra.pbwFiltration (p : ℕ ×ₗ ℕ) :
    Submodule k (WeylAlgebra k) :=
  Submodule.span k ((WeylAlgebra.pbwBasis k) '' Set.Iic p)

private theorem WeylAlgebra.pbwBasis_mem_filtration {p q : ℕ ×ₗ ℕ} (hqp : q ≤ p) :
    WeylAlgebra.pbwBasis k q ∈ WeylAlgebra.pbwFiltration k p :=
  Submodule.subset_span ⟨q, hqp, rfl⟩

private theorem WeylAlgebra.pbwCoeff_eq_zero_of_mem_filtration
    {a : WeylAlgebra k} {p q : ℕ ×ₗ ℕ}
    (ha : a ∈ WeylAlgebra.pbwFiltration k p) (hqp : ¬ q ≤ p) :
    WeylAlgebra.pbwCoeff k q a = 0 := by
  apply Submodule.span_induction (R := k)
    (s := (WeylAlgebra.pbwBasis k) '' Set.Iic p)
    (p := fun a _ => WeylAlgebra.pbwCoeff k q a = 0)
  · intro a ha
    obtain ⟨r, hrp, rfl⟩ := ha
    rw [WeylAlgebra.pbwCoeff_basis, if_neg]
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

private theorem WeylAlgebra.y_mul_x_pow_succ (n : ℕ) :
    WeylAlgebra.y k * WeylAlgebra.x k ^ (n + 1) =
      WeylAlgebra.x k ^ (n + 1) * WeylAlgebra.y k +
        (n + 1) • WeylAlgebra.x k ^ n := by
  induction n with
  | zero => simpa using WeylAlgebra.yx_eq k
  | succ n ih =>
      calc
        WeylAlgebra.y k * WeylAlgebra.x k ^ (n + 1 + 1) =
            WeylAlgebra.y k * WeylAlgebra.x k ^ (n + 1) * WeylAlgebra.x k := by
              rw [pow_succ, mul_assoc]
        _ = (WeylAlgebra.x k ^ (n + 1) * WeylAlgebra.y k +
              (n + 1) • WeylAlgebra.x k ^ n) * WeylAlgebra.x k := by rw [ih]
        _ = WeylAlgebra.x k ^ (n + 1) *
              (WeylAlgebra.y k * WeylAlgebra.x k) +
              (n + 1) • WeylAlgebra.x k ^ (n + 1) := by
              rw [add_mul, mul_assoc, smul_mul_assoc, ← pow_succ]
        _ = WeylAlgebra.x k ^ (n + 1) *
              (WeylAlgebra.x k * WeylAlgebra.y k + 1) +
              (n + 1) • WeylAlgebra.x k ^ (n + 1) := by
              rw [WeylAlgebra.yx_eq]
        _ = WeylAlgebra.x k ^ (n + 1 + 1) * WeylAlgebra.y k +
              (n + 1 + 1) • WeylAlgebra.x k ^ (n + 1) := by
              rw [mul_add, mul_one, ← mul_assoc, ← pow_succ, add_assoc,
                add_comm (WeylAlgebra.x k ^ (n + 1))
                  ((n + 1) • WeylAlgebra.x k ^ (n + 1)), ← succ_nsmul]

private theorem WeylAlgebra.y_mul_pbwBasis (p : ℕ ×ₗ ℕ) :
    WeylAlgebra.y k * WeylAlgebra.pbwBasis k p =
      WeylAlgebra.pbwBasis k (p + toLex (0, 1)) +
        (ofLex p).1 • WeylAlgebra.pbwBasis k
          (toLex ((ofLex p).1 - 1, (ofLex p).2)) := by
  induction p using Lex.rec with | _ p =>
    rcases p with ⟨i, j⟩
    cases i with
    | zero => simp [WeylAlgebra.monomial, pow_succ']
    | succ i =>
        simp only [WeylAlgebra.pbwBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, add_zero]
        rw [WeylAlgebra.monomial, WeylAlgebra.monomial, WeylAlgebra.monomial,
          ← mul_assoc, WeylAlgebra.y_mul_x_pow_succ, add_mul, smul_mul_assoc]
        simp only [pow_succ', mul_assoc, Nat.succ_sub_one]

private theorem WeylAlgebra.y_mul_filtration {a : WeylAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ WeylAlgebra.pbwFiltration k p) :
    WeylAlgebra.y k * a ∈ WeylAlgebra.pbwFiltration k (p + toLex (0, 1)) := by
  apply Submodule.span_induction (R := k)
    (s := (WeylAlgebra.pbwBasis k) '' Set.Iic p)
    (p := fun a _ => WeylAlgebra.y k * a ∈
      WeylAlgebra.pbwFiltration k (p + toLex (0, 1)))
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    rw [WeylAlgebra.y_mul_pbwBasis]
    apply (WeylAlgebra.pbwFiltration k (p + toLex (0, 1))).add_mem
    · exact WeylAlgebra.pbwBasis_mem_filtration k (lex_add_le_add hqp le_rfl)
    · apply (WeylAlgebra.pbwFiltration k (p + toLex (0, 1))).smul_mem
      apply WeylAlgebra.pbwBasis_mem_filtration k
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
    exact (WeylAlgebra.pbwFiltration k _).add_mem ha hb
  · intro c a _ ha
    rw [mul_smul_comm]
    exact (WeylAlgebra.pbwFiltration k _).smul_mem c ha
  · exact ha

private theorem WeylAlgebra.pbwCoeff_y_mul {a : WeylAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ WeylAlgebra.pbwFiltration k p) :
    WeylAlgebra.pbwCoeff k (p + toLex (0, 1)) (WeylAlgebra.y k * a) =
      WeylAlgebra.pbwCoeff k p a := by
  apply Submodule.span_induction (R := k)
    (s := (WeylAlgebra.pbwBasis k) '' Set.Iic p)
    (p := fun a _ => WeylAlgebra.pbwCoeff k (p + toLex (0, 1))
      (WeylAlgebra.y k * a) = WeylAlgebra.pbwCoeff k p a)
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    rw [WeylAlgebra.y_mul_pbwBasis, map_add, map_nsmul,
      WeylAlgebra.pbwCoeff_basis, WeylAlgebra.pbwCoeff_basis,
      WeylAlgebra.pbwCoeff_basis]
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

private theorem WeylAlgebra.x_mul_filtration {a : WeylAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ WeylAlgebra.pbwFiltration k p) :
    WeylAlgebra.x k * a ∈ WeylAlgebra.pbwFiltration k (toLex (1, 0) + p) := by
  apply Submodule.span_induction (R := k)
    (s := (WeylAlgebra.pbwBasis k) '' Set.Iic p)
    (p := fun a _ => WeylAlgebra.x k * a ∈
      WeylAlgebra.pbwFiltration k (toLex (1, 0) + p))
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : WeylAlgebra.x k * WeylAlgebra.pbwBasis k q =
        WeylAlgebra.pbwBasis k (toLex (1, 0) + q) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp only [WeylAlgebra.pbwBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, zero_add, WeylAlgebra.monomial]
        rw [show 1 + i = i + 1 by omega, pow_succ', mul_assoc]
    rw [hmul]
    exact WeylAlgebra.pbwBasis_mem_filtration k (lex_add_le_add le_rfl hqp)
  · simp
  · intro a b _ _ ha hb
    simpa [mul_add] using (WeylAlgebra.pbwFiltration k _).add_mem ha hb
  · intro c a _ ha
    simpa [mul_smul_comm] using (WeylAlgebra.pbwFiltration k _).smul_mem c ha
  · exact ha

private theorem WeylAlgebra.pbwCoeff_x_mul {a : WeylAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ WeylAlgebra.pbwFiltration k p) :
    WeylAlgebra.pbwCoeff k (toLex (1, 0) + p) (WeylAlgebra.x k * a) =
      WeylAlgebra.pbwCoeff k p a := by
  apply Submodule.span_induction (R := k)
    (s := (WeylAlgebra.pbwBasis k) '' Set.Iic p)
    (p := fun a _ => WeylAlgebra.pbwCoeff k (toLex (1, 0) + p)
      (WeylAlgebra.x k * a) = WeylAlgebra.pbwCoeff k p a)
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : WeylAlgebra.x k * WeylAlgebra.pbwBasis k q =
        WeylAlgebra.pbwBasis k (toLex (1, 0) + q) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp only [WeylAlgebra.pbwBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, zero_add, WeylAlgebra.monomial]
        rw [show 1 + i = i + 1 by omega, pow_succ', mul_assoc]
    rw [hmul, WeylAlgebra.pbwCoeff_basis, WeylAlgebra.pbwCoeff_basis]
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

private theorem WeylAlgebra.mul_y_filtration {a : WeylAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ WeylAlgebra.pbwFiltration k p) :
    a * WeylAlgebra.y k ∈ WeylAlgebra.pbwFiltration k (p + toLex (0, 1)) := by
  apply Submodule.span_induction (R := k)
    (s := (WeylAlgebra.pbwBasis k) '' Set.Iic p)
    (p := fun a _ => a * WeylAlgebra.y k ∈
      WeylAlgebra.pbwFiltration k (p + toLex (0, 1)))
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : WeylAlgebra.pbwBasis k q * WeylAlgebra.y k =
        WeylAlgebra.pbwBasis k (q + toLex (0, 1)) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp only [WeylAlgebra.pbwBasis_apply, ofLex_toLex, ofLex_add,
          Prod.fst_add, Prod.snd_add, add_zero, WeylAlgebra.monomial]
        rw [pow_succ, mul_assoc]
    rw [hmul]
    exact WeylAlgebra.pbwBasis_mem_filtration k (lex_add_le_add hqp le_rfl)
  · simp
  · intro a b _ _ ha hb
    simpa [add_mul] using (WeylAlgebra.pbwFiltration k _).add_mem ha hb
  · intro c a _ ha
    simpa [smul_mul_assoc] using (WeylAlgebra.pbwFiltration k _).smul_mem c ha
  · exact ha

private theorem WeylAlgebra.pbwCoeff_mul_y {a : WeylAlgebra k} {p : ℕ ×ₗ ℕ}
    (ha : a ∈ WeylAlgebra.pbwFiltration k p) :
    WeylAlgebra.pbwCoeff k (p + toLex (0, 1)) (a * WeylAlgebra.y k) =
      WeylAlgebra.pbwCoeff k p a := by
  apply Submodule.span_induction (R := k)
    (s := (WeylAlgebra.pbwBasis k) '' Set.Iic p)
    (p := fun a _ => WeylAlgebra.pbwCoeff k (p + toLex (0, 1))
      (a * WeylAlgebra.y k) = WeylAlgebra.pbwCoeff k p a)
  · intro a ha
    obtain ⟨q, hqp, rfl⟩ := ha
    have hmul : WeylAlgebra.pbwBasis k q * WeylAlgebra.y k =
        WeylAlgebra.pbwBasis k (q + toLex (0, 1)) := by
      induction q using Lex.rec with | _ q =>
        rcases q with ⟨i, j⟩
        simp [WeylAlgebra.monomial, pow_succ, mul_assoc]
    rw [hmul, WeylAlgebra.pbwCoeff_basis, WeylAlgebra.pbwCoeff_basis]
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

private theorem WeylAlgebra.y_pow_mul_x_pow_mem (i j : ℕ) :
    WeylAlgebra.y k ^ j * WeylAlgebra.x k ^ i ∈
      WeylAlgebra.pbwFiltration k (toLex (i, j)) := by
  induction j with
  | zero =>
      simpa only [pow_zero, one_mul, WeylAlgebra.pbwBasis_apply, ofLex_toLex,
        WeylAlgebra.monomial, pow_zero, mul_one] using
        WeylAlgebra.pbwBasis_mem_filtration k (p := toLex (i, 0)) le_rfl
  | succ j ih =>
      rw [pow_succ', mul_assoc]
      simpa using WeylAlgebra.y_mul_filtration k ih

private theorem WeylAlgebra.pbwCoeff_y_pow_mul_x_pow (i j : ℕ) :
    WeylAlgebra.pbwCoeff k (toLex (i, j))
      (WeylAlgebra.y k ^ j * WeylAlgebra.x k ^ i) = 1 := by
  induction j with
  | zero =>
      rw [pow_zero, one_mul,
        ← show WeylAlgebra.pbwBasis k (toLex (i, 0)) = WeylAlgebra.x k ^ i by
          simp [WeylAlgebra.monomial]]
      rw [WeylAlgebra.pbwCoeff_basis, if_pos rfl]
  | succ j ih =>
      rw [pow_succ', mul_assoc]
      have h := WeylAlgebra.pbwCoeff_y_mul k
        (WeylAlgebra.y_pow_mul_x_pow_mem k i j)
      simpa using h.trans ih

private theorem WeylAlgebra.x_pow_mul_filtration {a : WeylAlgebra k} {p : ℕ ×ₗ ℕ}
    (i : ℕ) (ha : a ∈ WeylAlgebra.pbwFiltration k p) :
    WeylAlgebra.x k ^ i * a ∈
      WeylAlgebra.pbwFiltration k (toLex (i, 0) + p) := by
  induction i with
  | zero => simpa using ha
  | succ i ih =>
      rw [pow_succ', mul_assoc]
      have h := WeylAlgebra.x_mul_filtration k ih
      have hfront : toLex (1, 0) + toLex (i, 0) = toLex (i + 1, 0) := by
        apply ofLex.injective
        change (1 + i, 0 + 0) = (i + 1, 0)
        simp [Nat.add_comm]
      have hidx : toLex (1, 0) + (toLex (i, 0) + p) = toLex (i + 1, 0) + p := by
        rw [← add_assoc, hfront]
      rwa [hidx] at h

private theorem WeylAlgebra.pbwCoeff_x_pow_mul {a : WeylAlgebra k} {p : ℕ ×ₗ ℕ}
    (i : ℕ) (ha : a ∈ WeylAlgebra.pbwFiltration k p) :
    WeylAlgebra.pbwCoeff k (toLex (i, 0) + p) (WeylAlgebra.x k ^ i * a) =
      WeylAlgebra.pbwCoeff k p a := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ', mul_assoc]
      have h := WeylAlgebra.pbwCoeff_x_mul k
        (WeylAlgebra.x_pow_mul_filtration k i ha)
      have hfront : toLex (1, 0) + toLex (i, 0) = toLex (i + 1, 0) := by
        apply ofLex.injective
        change (1 + i, 0 + 0) = (i + 1, 0)
        simp [Nat.add_comm]
      have hidx : toLex (1, 0) + (toLex (i, 0) + p) = toLex (i + 1, 0) + p := by
        rw [← add_assoc, hfront]
      rw [hidx] at h
      exact h.trans ih

private theorem WeylAlgebra.mul_y_pow_filtration {a : WeylAlgebra k} {p : ℕ ×ₗ ℕ}
    (j : ℕ) (ha : a ∈ WeylAlgebra.pbwFiltration k p) :
    a * WeylAlgebra.y k ^ j ∈
      WeylAlgebra.pbwFiltration k (p + toLex (0, j)) := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
      rw [pow_succ, ← mul_assoc]
      simpa [add_assoc] using WeylAlgebra.mul_y_filtration k ih

private theorem WeylAlgebra.pbwCoeff_mul_y_pow {a : WeylAlgebra k} {p : ℕ ×ₗ ℕ}
    (j : ℕ) (ha : a ∈ WeylAlgebra.pbwFiltration k p) :
    WeylAlgebra.pbwCoeff k (p + toLex (0, j)) (a * WeylAlgebra.y k ^ j) =
      WeylAlgebra.pbwCoeff k p a := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, ← mul_assoc]
      have h := WeylAlgebra.pbwCoeff_mul_y k
        (WeylAlgebra.mul_y_pow_filtration k j ha)
      simpa [add_assoc] using h.trans ih

private theorem WeylAlgebra.pbwBasis_mul_mem (p q : ℕ ×ₗ ℕ) :
    WeylAlgebra.pbwBasis k p * WeylAlgebra.pbwBasis k q ∈
      WeylAlgebra.pbwFiltration k (p + q) := by
  induction p using Lex.rec with | _ p =>
    induction q using Lex.rec with | _ q =>
      rcases p with ⟨i, j⟩
      rcases q with ⟨u, v⟩
      simp only [WeylAlgebra.pbwBasis_apply, WeylAlgebra.monomial, ofLex_toLex]
      rw [mul_assoc (WeylAlgebra.x k ^ i) (WeylAlgebra.y k ^ j),
        ← mul_assoc (WeylAlgebra.y k ^ j) (WeylAlgebra.x k ^ u),
        ← mul_assoc (WeylAlgebra.x k ^ i)]
      have hmid := WeylAlgebra.y_pow_mul_x_pow_mem k u j
      have hleft := WeylAlgebra.x_pow_mul_filtration k i hmid
      have hright := WeylAlgebra.mul_y_pow_filtration k v hleft
      simpa [add_assoc] using hright

private theorem WeylAlgebra.pbwCoeff_basis_mul (p q : ℕ ×ₗ ℕ) :
    WeylAlgebra.pbwCoeff k (p + q)
      (WeylAlgebra.pbwBasis k p * WeylAlgebra.pbwBasis k q) = 1 := by
  induction p using Lex.rec with | _ p =>
    induction q using Lex.rec with | _ q =>
      rcases p with ⟨i, j⟩
      rcases q with ⟨u, v⟩
      simp only [WeylAlgebra.pbwBasis_apply, WeylAlgebra.monomial, ofLex_toLex]
      rw [mul_assoc (WeylAlgebra.x k ^ i) (WeylAlgebra.y k ^ j),
        ← mul_assoc (WeylAlgebra.y k ^ j) (WeylAlgebra.x k ^ u),
        ← mul_assoc (WeylAlgebra.x k ^ i)]
      have hmid := WeylAlgebra.y_pow_mul_x_pow_mem k u j
      have hleft := WeylAlgebra.x_pow_mul_filtration k i hmid
      have h1 := WeylAlgebra.pbwCoeff_mul_y_pow k v hleft
      have h2 := WeylAlgebra.pbwCoeff_x_pow_mul k i hmid
      have h3 := WeylAlgebra.pbwCoeff_y_pow_mul_x_pow k u j
      simpa [add_assoc] using h1.trans (h2.trans h3)

private theorem WeylAlgebra.pbwCoeff_basis_mul_of_le
    {p q r s : ℕ ×ₗ ℕ} (hrp : r ≤ p) (hsq : s ≤ q) :
    WeylAlgebra.pbwCoeff k (p + q)
      (WeylAlgebra.pbwBasis k r * WeylAlgebra.pbwBasis k s) =
        WeylAlgebra.pbwCoeff k p (WeylAlgebra.pbwBasis k r) *
          WeylAlgebra.pbwCoeff k q (WeylAlgebra.pbwBasis k s) := by
  by_cases hr : r = p
  · subst r
    by_cases hs : s = q
    · subst s
      rw [WeylAlgebra.pbwCoeff_basis_mul, WeylAlgebra.pbwCoeff_basis,
        WeylAlgebra.pbwCoeff_basis, if_pos rfl, if_pos rfl, mul_one]
    · have hslt : s < q := lt_of_le_of_ne hsq hs
      have hlt : p + s < p + q := lex_add_lt_add_of_le_of_lt le_rfl hslt
      rw [WeylAlgebra.pbwCoeff_basis, WeylAlgebra.pbwCoeff_basis, if_pos rfl, if_neg hs,
        mul_zero]
      exact WeylAlgebra.pbwCoeff_eq_zero_of_mem_filtration k
        (WeylAlgebra.pbwBasis_mul_mem k p s) (not_le_of_gt hlt)
  · have hrlt : r < p := lt_of_le_of_ne hrp hr
    have hlt : r + s < p + q := lex_add_lt_add_of_lt_of_le hrlt hsq
    rw [WeylAlgebra.pbwCoeff_basis, if_neg hr, zero_mul]
    exact WeylAlgebra.pbwCoeff_eq_zero_of_mem_filtration k
      (WeylAlgebra.pbwBasis_mul_mem k r s) (not_le_of_gt hlt)


theorem WeylAlgebra.pbwCoeff_mul_of_mem_filtration
    {a b : WeylAlgebra k} {p q : ℕ ×ₗ ℕ}
    (ha : a ∈ WeylAlgebra.pbwFiltration k p)
    (hb : b ∈ WeylAlgebra.pbwFiltration k q) :
    WeylAlgebra.pbwCoeff k (p + q) (a * b) =
      WeylAlgebra.pbwCoeff k p a * WeylAlgebra.pbwCoeff k q b := by
  apply Submodule.span_induction (R := k)
    (s := (WeylAlgebra.pbwBasis k) '' Set.Iic p)
    (p := fun a _ => WeylAlgebra.pbwCoeff k (p + q) (a * b) =
      WeylAlgebra.pbwCoeff k p a * WeylAlgebra.pbwCoeff k q b)
  · intro a ha
    obtain ⟨r, hrp, rfl⟩ := ha
    apply Submodule.span_induction (R := k)
      (s := (WeylAlgebra.pbwBasis k) '' Set.Iic q)
      (p := fun b _ => WeylAlgebra.pbwCoeff k (p + q)
        (WeylAlgebra.pbwBasis k r * b) =
          WeylAlgebra.pbwCoeff k p (WeylAlgebra.pbwBasis k r) *
            WeylAlgebra.pbwCoeff k q b)
    · intro b hb
      obtain ⟨s, hsq, rfl⟩ := hb
      exact WeylAlgebra.pbwCoeff_basis_mul_of_le k hrp hsq
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

private theorem WeylAlgebra.exists_leading
    {a : WeylAlgebra k} (ha : a ≠ 0) :
    ∃ p : ℕ ×ₗ ℕ, a ∈ WeylAlgebra.pbwFiltration k p ∧
      WeylAlgebra.pbwCoeff k p a ≠ 0 := by
  classical
  set f := (WeylAlgebra.pbwBasis k).repr a
  have hf : f ≠ 0 := fun hf => ha ((WeylAlgebra.pbwBasis k).repr.injective
    (hf.trans (map_zero _).symm))
  have hsupport : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  let p := f.support.max' hsupport
  refine ⟨p, ?_, ?_⟩
  · have heq : (Finsupp.linearCombination k (WeylAlgebra.pbwBasis k)) f = a := by
      simp [f]
    rw [← heq, Finsupp.linearCombination_apply]
    apply Submodule.sum_mem
    intro q hq
    exact (WeylAlgebra.pbwFiltration k p).smul_mem _
      (WeylAlgebra.pbwBasis_mem_filtration k (Finset.le_max' f.support q hq))
  · change f p ≠ 0
    exact Finsupp.mem_support_iff.mp (Finset.max'_mem f.support hsupport)



/-- The product of two nonzero elements of the associated algebra is nonzero when the coefficient ring has no zero divisors. -/
theorem WeylAlgebra.mul_ne_zero [NoZeroDivisors k]
    {a b : WeylAlgebra k} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  classical
  obtain ⟨p, haF, hap⟩ := WeylAlgebra.exists_leading k ha
  obtain ⟨q, hbF, hbq⟩ := WeylAlgebra.exists_leading k hb
  intro hab
  have hcoeff := WeylAlgebra.pbwCoeff_mul_of_mem_filtration k haF hbF
  rw [hab, map_zero] at hcoeff
  exact (_root_.mul_ne_zero hap hbq) hcoeff.symm

noncomputable instance [NoZeroDivisors k] : NoZeroDivisors (WeylAlgebra k) :=
  noZeroDivisors_iff (WeylAlgebra k) |>.2 fun {a b} hab => by
    by_contra h
    push Not at h
    exact WeylAlgebra.mul_ne_zero k h.1 h.2 hab

end RepresentationTheory.RingTheory.LexicographicIndexedBasis
