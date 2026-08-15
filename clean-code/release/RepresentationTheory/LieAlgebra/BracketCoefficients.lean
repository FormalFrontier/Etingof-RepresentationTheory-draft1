/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.BigradedPairing
import RepresentationTheory.Alignment.Attribute

/-! # Bracket Coefficients -/

namespace RepresentationTheory.LieAlgebra.BracketCoefficients

attribute [local instance] LieRing.ofAssociativeRing

section Alternating

variable {k L M : Type*} [CommRing k] [LieRing L] [LieAlgebra k L]
  [AddCommGroup M] [Module k M]

/-- A bilinear Lie-compatible map changes sign when its two inputs are swapped. -/
theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.map_swap_eq_neg
    {c : L → L → M}
    (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c)
    (a b : L) : c a b = -c b a := by
  have h := hc.self_eq_zero (a + b)
  rw [hc.add_left, hc.add_right, hc.add_right, hc.self_eq_zero, hc.self_eq_zero, zero_add,
    add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- A bilinear Lie-compatible map is negated when its left input is negated. -/
theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.map_neg_left
    {c : L → L → M}
    (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c)
    (a b : L) : c (-a) b = -c a b := by
  rw [show -a = (-1 : k) • a by simp, hc.smul_left]
  simp

end Alternating

section Coefficients

variable {k : Type*} [Field k]

/-- The scalar coefficient indexed by one natural number for the displayed bilinear map. -/
noncomputable def diagonalCoefficient
    (c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k →
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k)
    (m : ℕ) : k :=
  c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base)
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.even m 2))

/-- A second two-index scalar coefficient associated with the displayed bilinear map. -/
noncomputable def shiftedCoefficient
    (c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k →
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k)
    (a b : ℕ) : k :=
  c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.odd a 0))
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.odd b 4)) - diagonalCoefficient c (a + b)

/-- The scalar coefficient indexed by two natural numbers for the displayed bilinear map. -/
noncomputable def bracketCoefficient
    (c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k →
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k)
    (a b : ℕ) : k :=
  c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.even a 0))
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.even b 2)) - diagonalCoefficient c (a + b + 1)

private theorem lie_loopFam_even_one_odd_four (b d : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.odd b 4),
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even d 1)⁆ =
      (2 : k) •
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
          (.odd (b + d + 1) 4) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * b + 1)
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4),
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * d + 2)
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1)⁆ =
      (2 : k) •
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k
          (2 * (b + d + 1) + 1)
          (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17,
    ← lie_skew
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4)
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1),
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux8, neg_smul,
    neg_neg, map_smul]
  rw [show 2 * b + 1 + (2 * d + 2) = 2 * (b + d + 1) + 1 by omega]

private theorem lie_loopFam_even_one_odd_zero (a d : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even d 1),
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.odd a 0)⁆ =
      (2 : k) •
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
          (.odd (a + d + 1) 0) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * d + 2)
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1),
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1)
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 0)⁆ =
      (2 : k) •
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k
          (2 * (a + d + 1) + 1)
          (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 0)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17,
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux35, map_smul]
  rw [show 2 * d + 2 + (2 * a + 1) = 2 * (a + d + 1) + 1 by omega]

private theorem lie_loopFam_base_even_one (a : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base,
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even a 1)⁆ =
      -_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even a 0) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k 0
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0),
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 2)
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1)⁆ =
      -_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 2)
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17]
  have h :
      ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0,
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1⁆ =
        (-1 : k) •
          _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11,
        LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single, Matrix.sub_apply,
        Matrix.smul_apply]
  rw [h, map_smul]
  simp

private theorem lie_loopFam_even_one_even_two (a b : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even a 1),
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even b 2)⁆ =
      -_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even (a + b + 1) 2) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 2)
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1),
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * b + 2)
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2)⁆ =
      -_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k
        (2 * (a + b + 1) + 2)
        (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17]
  have h :
      ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1,
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2⁆ =
        (-1 : k) •
          _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11,
        LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single, Matrix.sub_apply,
        Matrix.smul_apply]
  rw [h, map_smul]
  rw [show 2 * a + 2 + (2 * b + 2) = 2 * (a + b + 1) + 2 by omega]
  simp

private theorem lie_loopFam_even_two_base (b : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even b 2),
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        .base⁆ =
      -_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even b 1) := by
  rw [← lie_skew
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even b 2))
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        .base),
    _root_.RepresentationTheory.LieAlgebra.BigradedPairing.bracket_base_familyTwo]

/-- Evaluating the bilinear map on the displayed basis elements equals its indexed coefficient. -/
theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.basisValue_eq_coefficient
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k →
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k}
    (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c)
    (a b : ℕ) :
    c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even a 1))
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
        (.even b 1)) = bracketCoefficient c a b := by
  have h := hc.cyclic_bracket
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      .base)
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.even a 1))
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.even b 2))
  rw [lie_loopFam_base_even_one, lie_loopFam_even_one_even_two,
    lie_loopFam_even_two_base, hc.map_neg_left, hc.map_neg_left, hc.map_neg_left] at h
  rw [hc.map_swap_eq_neg
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.even (a + b + 1) 2))
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      .base)] at h
  rw [hc.map_swap_eq_neg
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.even b 1))
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.even a 1))] at h
  simp only [neg_neg] at h
  dsimp [bracketCoefficient, diagonalCoefficient]
  linear_combination h

/-- Relates a coefficient with summed left index to two shifted coefficients. -/
theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle.coefficient_add_left_eq
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k →
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k}
    (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsAlternatingLieCocycle k c)
    (a b d : ℕ) :
    bracketCoefficient c (a + b) d =
      2 * (shiftedCoefficient c a (b + d + 1) -
        shiftedCoefficient c (a + d + 1) b) := by
  have h := hc.cyclic_bracket
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.odd a 0))
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.odd b 4))
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.even d 1))
  have hodd :
      ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
          (.odd a 0),
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
          (.odd b 4)⁆ =
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
          (.even (a + b) 1) := by
    simpa [Fin.rev, _root_.RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryCoeff5] using
      (_root_.RepresentationTheory.LieAlgebra.BigradedPairing.bracket_family5_rev_index
        (k := k) a b (0 : Fin 5))
  rw [hodd, lie_loopFam_even_one_odd_four, lie_loopFam_even_one_odd_zero, hc.smul_left,
    hc.smul_left] at h
  simp only [smul_eq_mul] at h
  rw [hc.basisValue_eq_coefficient (a + b) d] at h
  rw [hc.map_swap_eq_neg
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.odd (b + d + 1) 4))
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k
      (.odd a 0))] at h
  dsimp [shiftedCoefficient, diagonalCoefficient]
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  linear_combination h

end Coefficients

end RepresentationTheory.LieAlgebra.BracketCoefficients

attribute [nolint defsWithUnderscore]
  RepresentationTheory.LieAlgebra.BracketCoefficients.diagonalCoefficient
  RepresentationTheory.LieAlgebra.BracketCoefficients.shiftedCoefficient
  RepresentationTheory.LieAlgebra.BracketCoefficients.bracketCoefficient
