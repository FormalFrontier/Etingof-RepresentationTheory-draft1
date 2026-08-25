/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.BracketCoefficients
import RepresentationTheory.Alignment.Attribute

/-! # Parameter Four Constructions -/

namespace RepresentationTheory.LieAlgebra.ParameterFourConstructions

attribute [local instance] LieRing.ofAssociativeRing

section DeviationAlgebra

variable {k : Type*} [Field k] [CharZero k]


private theorem deviation_eq_zero_of_recurrence
    (D E : ℕ → ℕ → k)
    (hD : ∀ a b, D a b = -D b a)
    (hE : ∀ a b, E a b = -E b a)
    (hrec : ∀ a b d,
      E (a + b) d = 2 * (D a (b + d + 1) - D (a + d + 1) b)) :
    (∀ a b, D a b = 0) ∧ ∀ a b, E a b = 0 := by
  have h2 : (2 : k) ≠ 0 := by norm_num
  have hrec' : ∀ a b d,
      E (a + b) d = 2 * (D a (b + d + 1) + D b (a + d + 1)) := by
    intro a b d
    rw [hrec, hD (a + d + 1) b]
    ring
  have hstep : ∀ a d,
      D (a + 1) (d + 1) =
        D a (d + 2) + D 1 (a + d + 1) - D 0 (a + d + 2) := by
    intro a d
    have h₁ := hrec' a 1 d
    have h₂ := hrec' 0 (a + 1) d
    simp only [zero_add] at h₂
    have h := h₁.symm.trans h₂
    norm_num [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h
    linear_combination -h
  have haffine : ∀ a d,
      D a (d + 1) = D 0 (a + d + 1) +
        (a : k) * (D 1 (a + d) - D 0 (a + d + 1)) := by
    intro a
    induction a with
    | zero =>
        intro d
        simp
    | succ a ih =>
        intro d
        rw [show a + 1 = a + 1 by rfl, hstep a d, ih (d + 1)]
        push_cast
        ring_nf
  have hlayer : ∀ q : ℕ,
      D 0 (q + 1) = 0 ∧ D 1 q - D 0 (q + 1) = 0 := by
    intro q
    let z := D 0 (q + 1)
    let r := D 1 q - z
    have haf : D q 1 = z + (q : k) * r := by
      simpa [z, r] using haffine q 0
    have hs := hD 1 q
    have hzr : 2 * z + ((q + 1 : ℕ) : k) * r = 0 := by
      dsimp [r]
      push_cast
      linear_combination hs - haf
    have he := hE 0 q
    have hleft := hrec' 0 0 q
    have hright := hrec' q 0 0
    have heq : 4 * z = -(2 * (D q 1 + z)) := by
      calc
        4 * z = E 0 q := by
          rw [hleft]
          simp only [zero_add]
          dsimp [z]
          ring
        _ = -E q 0 := he
        _ = -(2 * (D q 1 + z)) := by
          simpa [z] using congrArg Neg.neg hright
    have hertwo : 2 * (4 * z + (q : k) * r) = 0 := by
      linear_combination heq - 2 * haf
    have her : 4 * z + (q : k) * r = 0 :=
      (mul_eq_zero.mp hertwo).resolve_left h2
    have hrmul : (((q + 2 : ℕ) : k)) * r = 0 := by
      push_cast at hzr ⊢
      linear_combination 2 * hzr - her
    have hn : ((q + 2 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hr : r = 0 := (mul_eq_zero.mp hrmul).resolve_left hn
    have hzmul : 2 * z = 0 := by simpa [hr] using hzr
    have hz : z = 0 := (mul_eq_zero.mp hzmul).resolve_left h2
    exact ⟨by simpa [z] using hz, by simpa [r, z] using hr⟩
  have hDzero : ∀ a b, D a b = 0 := by
    intro a b
    obtain rfl | ha := a
    · obtain rfl | hb := b
      · have hs := hD 0 0
        have hz : 2 * D 0 0 = 0 := by linear_combination hs
        exact (mul_eq_zero.mp hz).resolve_left h2
      · exact (hlayer hb).1
    · obtain rfl | hb := b
      · rw [hD, (hlayer ha).1, neg_zero]
      · calc
          D (ha + 1) (hb + 1) =
              D 0 (ha + hb + 2) + ((ha + 1 : ℕ) : k) *
                (D 1 (ha + hb + 1) - D 0 (ha + hb + 2)) := by
            have haf := haffine (ha + 1) hb
            rw [show ha + 1 + hb + 1 = ha + hb + 2 by omega,
              show ha + 1 + hb = ha + hb + 1 by omega] at haf
            exact haf
          _ = 0 := by rw [(hlayer (ha + hb + 1)).2, (hlayer (ha + hb + 1)).1]; simp
  refine ⟨hDzero, ?_⟩
  intro a b
  have h := hrec a 0 b
  simp only [Nat.add_zero] at h
  rw [hDzero, hDzero] at h
  simpa using h

end DeviationAlgebra

section CoefficientReduction

variable {k : Type*} [Field k]

private theorem lie_loopFam_base_odd_one (a : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 1)⁆ = (2 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 0) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k 0 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 1)⁆ =
    (2 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 0)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux33, map_smul]
  rw [zero_add]

private theorem lie_loopFam_base_odd_two (a : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 2)⁆ = (-3 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 1) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k 0 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 2)⁆ =
    (-3 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 1)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux5, map_smul]
  rw [zero_add]

private theorem lie_loopFam_base_odd_three (a : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 3)⁆ = _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 2) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k 0 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 3)⁆ =
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 2)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux34]
  simp

private theorem lie_loopFam_base_odd_four (a : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 4)⁆ = -_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 3) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k 0 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4)⁆ =
    -_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 3)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux6, map_smul]
  simp

private theorem lie_loopFam_odd_one_four (a b : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 1), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 4)⁆ =
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even (a + b) 2) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 1), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * b + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4)⁆ =
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * (a + b) + 2) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17, _root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.bracket_family5_one_four]
  simp only [one_smul]
  rw [show 2 * a + 1 + (2 * b + 1) = 2 * (a + b) + 2 by omega]

private theorem lie_loopFam_odd_two_three (a b : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 2), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 3)⁆ =
      (-3 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even (a + b) 2) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 2), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * b + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 3)⁆ =
    (-3 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * (a + b) + 2) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17]
  have h : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 2, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 3⁆ = (-3 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
        Matrix.sub_apply, Matrix.smul_apply] <;> ring
  rw [h, map_smul]
  rw [show 2 * a + 1 + (2 * b + 1) = 2 * (a + b) + 2 by omega]


private theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.odd_one_three
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k} (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c) (a b : ℕ) :
    c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 1)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 3)) =
      2 * c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 0)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 4)) -
        _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c (a + b) := by
  have h := hc.cyclic_bracket (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 1))
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 4))
  rw [lie_loopFam_base_odd_one, lie_loopFam_odd_one_four,
    ← lie_skew (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 4)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base),
    lie_loopFam_base_odd_four, neg_neg, hc.smul_left] at h
  rw [hc.map_swap_eq_neg (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even (a + b) 2)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base)] at h
  rw [hc.map_swap_eq_neg (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 3)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 1))] at h
  dsimp [_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient]
  simp only [smul_eq_mul] at h
  linear_combination -h


private theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.odd_two_two_eq_deviation
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k} (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c) (a b : ℕ) :
    c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 2)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 2)) =
      6 * _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.shiftedCoefficient c a b := by
  have h := hc.cyclic_bracket (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 2))
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 3))
  rw [lie_loopFam_base_odd_two, lie_loopFam_odd_two_three,
    ← lie_skew (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 3)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base),
    lie_loopFam_base_odd_three, hc.smul_left, hc.smul_left, hc.map_neg_left] at h
  rw [hc.map_swap_eq_neg (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even (a + b) 2)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base),
    hc.map_swap_eq_neg (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 2)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 2)),
    hc.odd_one_three a b] at h
  dsimp [_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.shiftedCoefficient, _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient] at h ⊢
  simp only [neg_neg] at h
  linear_combination h

private theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.odd_deviation_skew
    [CharZero k]
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k} (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c) (a b : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.shiftedCoefficient c a b = -_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.shiftedCoefficient c b a := by
  have hab := hc.odd_two_two_eq_deviation a b
  have hba := hc.odd_two_two_eq_deviation b a
  have hs := hc.map_swap_eq_neg (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 2)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 2))
  rw [hab, hba] at hs
  have h6 : (6 : k) ≠ 0 := by norm_num
  apply (mul_left_cancel₀ h6)
  simpa [mul_neg] using hs

private theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.even_deviation_skew
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k} (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c) (a b : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.bracketCoefficient c a b = -_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.bracketCoefficient c b a := by
  rw [← hc.basisValue_eq_coefficient a b, ← hc.basisValue_eq_coefficient b a]
  exact hc.map_swap_eq_neg _ _


private theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.imaginary_deviations_eq_zero
    [CharZero k]
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k} (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c) :
    (∀ a b, _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.shiftedCoefficient c a b = 0) ∧
      ∀ a b, _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.bracketCoefficient c a b = 0 :=
  deviation_eq_zero_of_recurrence (_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.shiftedCoefficient c) (_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.bracketCoefficient c)
    hc.odd_deviation_skew hc.even_deviation_skew hc.coefficient_add_left_eq

private theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.odd_complementary
    [CharZero k]
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k} (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c)
    (a b : ℕ) (i : Fin 5) :
    c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a i)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b i.rev)) =
      _root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryCoeff5 k i * _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c (a + b) := by
  have hodd := hc.imaginary_deviations_eq_zero.1
  fin_cases i
  · change c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 0)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 4)) =
      (1 : k) * _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c (a + b)
    have h := hodd a b
    dsimp [_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.shiftedCoefficient] at h
    simpa using sub_eq_zero.mp h
  · change c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 1)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 3)) =
      (1 : k) * _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c (a + b)
    rw [hc.odd_one_three]
    have h := hodd a b
    dsimp [_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.shiftedCoefficient] at h
    rw [sub_eq_zero.mp h]
    ring
  · change c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 2)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 2)) =
      (0 : k) * _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c (a + b)
    rw [hc.odd_two_two_eq_deviation, hodd]
    ring
  · change c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 3)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 1)) =
      (-1 : k) * _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c (a + b)
    rw [hc.map_swap_eq_neg, hc.odd_one_three]
    have h := hodd b a
    dsimp [_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.shiftedCoefficient] at h
    rw [sub_eq_zero.mp h]
    rw [Nat.add_comm]
    ring
  · change c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a 4)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b 0)) =
      (-1 : k) * _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c (a + b)
    rw [hc.map_swap_eq_neg]
    have h := hodd b a
    dsimp [_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.shiftedCoefficient] at h
    rw [sub_eq_zero.mp h]
    rw [Nat.add_comm]
    ring

private theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.even_complementary
    [CharZero k]
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k} (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c)
    (a b : ℕ) (i : Fin 3) :
    c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even a i)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even b i.rev)) =
      _root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryCoeff3 k i * _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c (a + b + 1) := by
  have heven := hc.imaginary_deviations_eq_zero.2
  fin_cases i
  · change c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even a 0)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even b 2)) =
      (1 : k) * _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c (a + b + 1)
    have h := heven a b
    dsimp [_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.bracketCoefficient] at h
    simpa using sub_eq_zero.mp h
  · change c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even a 1)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even b 1)) =
      (0 : k) * _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c (a + b + 1)
    rw [hc.basisValue_eq_coefficient, heven]
    ring
  · change c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even a 2)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even b 0)) =
      (-1 : k) * _root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c (a + b + 1)
    rw [hc.map_swap_eq_neg]
    have h := heven b a
    dsimp [_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.bracketCoefficient] at h
    rw [sub_eq_zero.mp h]
    rw [show b + a + 1 = a + b + 1 by omega]
    ring

end CoefficientReduction

section Support

variable {k : Type*} [Field k]


private theorem imaginaryFunctional_eq_zero_of_lDeg
    (h2 : (2 : k) ≠ 0) (s : ℕ → k) (p : ℕ × ℕ)
    (hp : ∀ m : ℕ, p ≠ (2 * m + 2, 4 * m + 4))
    {v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k} (hv : v ∈ _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.bidegreeComponent k p) :
    _root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryLinearForm h2 s v = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨I, hI, rfl⟩ := hv
      rw [_root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryLinearForm_apply_indexedElement]
      cases I with
      | base => rfl
      | odd m i => rfl
      | even m i =>
          by_cases hi : i = 1
          · subst i
            exfalso
            apply hp m
            rw [← hI]
            simp [Fin.rev]
          · simp [_root_.RepresentationTheory.LieAlgebra.BigradedPairing.sequenceCoefficient, hi]
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]


/-- The sequence-derived bilinear map satisfies the indicated property when two, three, and five are nonzero. -/
theorem _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.sequence_has_property_of_characteristicAssumptions
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (s : ℕ → k) :
    _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.SpecialBinaryFormCondition (_root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryPairing h2 s) := by
  intro I J hIJ
  rw [_root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryPairing]
  exact imaginaryFunctional_eq_zero_of_lDeg h2 s _ hIJ
    (_root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.bracket_indexedElement_mem_bidegreeComponent_add h2 h3 h5 I J)

end Support

section Assembly

variable {k : Type*} [Field k] [CharZero k]


private noncomputable def _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.toLinearMap
    {L M : Type*} [LieRing L] [LieAlgebra k L] [AddCommGroup M] [Module k M]
    {c : L → L → M} (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c) : L →ₗ[k] L →ₗ[k] M where
  toFun a :=
    { toFun := c a
      map_add' := hc.add_right a
      map_smul' := fun r b => by simpa using hc.smul_right r a b }
  map_add' a b := LinearMap.ext fun d => hc.add_left a b d
  map_smul' r a := LinearMap.ext fun b => hc.smul_left r a b

private theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.eq_imaginaryCoboundary_loopFam
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k} (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c)
    (hw : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.SpecialBinaryFormCondition c) (I J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) :
    c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J) =
      _root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryPairing (by norm_num) (_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c)
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J) := by
  let h2 : (2 : k) ≠ 0 := by norm_num
  let h3 : (3 : k) ≠ 0 := by norm_num
  let h5 : (5 : k) ≠ 0 := by norm_num
  change c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J) =
    _root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryPairing h2 (_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J)
  by_cases hIJ : _root_.RepresentationTheory.LieAlgebra.BigradedPairing.IndexPairCompatible I J
  · rw [_root_.RepresentationTheory.LieAlgebra.BigradedPairing.indexPairCompatible_iff] at hIJ
    rcases hIJ with ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩ |
      ⟨a, b, i, j, rfl, rfl, hij⟩ | ⟨a, b, i, j, rfl, rfl, hij⟩
    · simp [_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient]
    · rw [hc.map_swap_eq_neg]
      have hcb := (_root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryPairing_property h2
        (_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c)).toIsAlternatingLieCocycle.map_swap_eq_neg
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even m 2)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base)
      rw [hcb]
      simp [_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient]
    · rw [_root_.RepresentationTheory.LieAlgebra.BigradedPairing.eq_rev_of_val_add_eq_four hij, hc.odd_complementary,
        _root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryPairing_family5 h2 _ a b i i.rev i.add_rev_cast]
    · rw [_root_.RepresentationTheory.LieAlgebra.BigradedPairing.eq_rev_of_val_add_eq_two hij, hc.even_complementary,
        _root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryPairing_family3 h2 _ a b i i.rev i.add_rev_cast]
  · rw [hw.apply_eq_zero_of_not_compatible hIJ]
    exact (_root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.SpecialBinaryFormCondition.apply_eq_zero_of_not_compatible
      (_root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.sequence_has_property_of_characteristicAssumptions h2 h3 h5 _) hIJ).symm



/-- Under the stated conditions, the bilinear map is recovered from the associated one-index coefficient data. -/
theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.eq_from_diagonalCoefficient
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k} (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c)
    (hw : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.SpecialBinaryFormCondition c) (a b : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k) :
    c a b = _root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryPairing (by norm_num)
      (_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c) a b := by
  let h2 : (2 : k) ≠ 0 := by norm_num
  let cb := _root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryPairing h2 (_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c)
  have hcb : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k cb :=
    (_root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryPairing_property h2 (_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c)).toIsAlternatingLieCocycle
  have hmaps : hc.toLinearMap = hcb.toLinearMap := by
    apply (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux2 k h2).ext
    intro I
    apply (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux2 k h2).ext
    intro J
    simpa [_root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.toLinearMap, cb, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_apply_aux6] using
      hc.eq_imaginaryCoboundary_loopFam hw I J
  change c a b = cb a b
  exact congrArg (fun F : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k →ₗ[k] _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k →ₗ[k] k => F a b) hmaps



/-- The stated structural property follows from the two displayed conditions on a bilinear map. -/
theorem _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.hasStructure_of_conditions
    (c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k) (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c)
    (hw : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.SpecialBinaryFormCondition c) : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsBinaryLieCocycle k c := by
  let h2 : (2 : k) ≠ 0 := by norm_num
  refine ⟨_root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryLinearForm h2 (_root_.RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient c), ?_⟩
  intro a b
  exact hc.eq_from_diagonalCoefficient hw a b




/-- The displayed scalar indexed by a natural number is zero. -/
@[simp] theorem _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.specifiedScalar_eq_zero (m : ℕ) : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m = 0 :=
  _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.specialFamily_eq_zero_of_cocycle_extension (by norm_num) (by norm_num) (by norm_num)
    (fun c hc hw ↦ _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.hasStructure_of_conditions c hc hw) m


/-- The two displayed objects associated with an index satisfy the specified binary property. -/
theorem _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.derivedPair_has_property (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.AuxiliaryPairCondition k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily k m) (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m) :=
  _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryPairCondition_companion_sequence (by norm_num) (by norm_num) (by norm_num) _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.specifiedScalar_eq_zero m


/-- The displayed linear map from the parameter-four module is injective. -/
theorem _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.parameterFourMap_injective : Function.Injective (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) :=
  (_root_.RepresentationTheory.LinearMap.KernelDecomposition.injective_iff_auxFamily_eq_zero (by norm_num) (by norm_num) (by norm_num)).2
    _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.specifiedScalar_eq_zero


/-- The range of the displayed map spans the parameter-four module. -/
theorem _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.span_range_parameterFourMap_eq_top :
    Submodule.span k (Set.range (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k)) = ⊤ :=
  _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.span_range_indexedFamily_eq_top_of_auxiliaryCentralFamily_eq_zero (by norm_num) (by norm_num) (by norm_num) _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.specifiedScalar_eq_zero



/-- A basis for the displayed module at parameter four. -/
@[source_ref "Chapter2/Problem2.16.3" (role := supporting)]
noncomputable def _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.parameterFourBasis : Module.Basis _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) :=
  Module.Basis.mk (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.linearIndependent_indexedFamily (by norm_num) (by norm_num))
    _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.span_range_parameterFourMap_eq_top.ge


/-- Computes the parameter-four basis vector at an index. -/
@[simp] theorem _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.parameterFourBasis_apply (I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) : _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.parameterFourBasis (k := k) I = _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k I :=
  Module.Basis.mk_apply _ _ _


/-- The displayed module at parameter four is not finite over the field. -/
theorem _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.not_moduleFinite_parameterFour : ¬ Module.Finite k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) := by
  letI : Infinite _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex := Infinite.of_injective (fun m : ℕ ↦ _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.odd m 0) <| by
    intro a b h
    cases h
    rfl
  exact Module.not_finite_of_infinite_basis (_root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.parameterFourBasis (k := k))


/-- A Lie algebra equivalence from the displayed parameter-four module to the specified subtype. -/
noncomputable def _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.parameterFourLieEquiv : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4 ≃ₗ⁅k⁆ _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k where
  toFun := _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.projectToDistinguishedSubspace k
  map_add' := map_add (_root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.projectToDistinguishedSubspace k)
  map_smul' := map_smul (_root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.projectToDistinguishedSubspace k)
  map_lie' := fun {u v} ↦ _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.projectToDistinguishedSubspace_bracket u v
  invFun := _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.liftFromDistinguishedSubspace (by norm_num)
  left_inv u := by
    apply _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.parameterFourMap_injective (k := k)
    rw [_root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.ambientMap_comp_lift (by norm_num) (by norm_num), _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.projectedSubtypeMap_val]
  right_inv := _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.projectToDistinguishedSubspace_comp_lift (by norm_num) (by norm_num)


/-- Computes the parameter-four Lie equivalence on an element. -/
@[simp] theorem _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.parameterFourLieEquiv_apply (u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) :
    _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.parameterFourLieEquiv (k := k) u = _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.projectToDistinguishedSubspace k u := by
  change _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.projectToDistinguishedSubspace k u = _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.projectToDistinguishedSubspace k u
  rfl

end Assembly

end RepresentationTheory.LieAlgebra.ParameterFourConstructions


attribute [nolint defsWithUnderscore]
  _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.parameterFourBasis
  _root_.RepresentationTheory.LieAlgebra.ParameterFourConstructions.parameterFourLieEquiv
