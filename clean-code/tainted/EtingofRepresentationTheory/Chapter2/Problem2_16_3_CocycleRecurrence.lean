import EtingofRepresentationTheory.Chapter2.Problem2_16_3_CocycleCombinatorics


/-!
# Problem 2.16.3(b): the scalar Jacobi recurrence

This file isolates the uniform recurrence left after the imaginary-support enumeration in
`Problem2_16_3_CocycleCombinatorics.lean`.

For a cocycle `c`, subtract its value on the base/even pair from the extreme odd/odd and
even/even coefficients.  Jacobi on the triple

`(odd a 0, odd b 4, even d 1)`

then gives

`evenDeviation (a+b) d = 2 * (oddDeviation a (b+d+1) - oddDeviation (a+d+1) b)`.

This is the layer-splitting recurrence underlying the remaining cohomology computation.  In
characteristic zero it combines with skew-symmetry and the base-generator recurrences to kill
all deviations.  Over positive characteristic it also exposes why a uniform theorem with only
the assumptions `2 ≠ 0`, `3 ≠ 0`, `5 ≠ 0` needs additional care: closing the recurrence at
imaginary layer `m` eventually requires cancellation of the scalar `m + 1`.
-/

namespace Etingof.Problem2_16_3

attribute [local instance] LieRing.ofAssociativeRing

section Alternating

variable {k L M : Type*} [CommRing k] [LieRing L] [LieAlgebra k L]
  [AddCommGroup M] [Module k M]

/-- An alternating bilinear two-cocycle is skew-symmetric. -/
theorem IsTwoCocycle.skew {c : L → L → M} (hc : IsTwoCocycle k c) (a b : L) :
    c a b = -c b a := by
  have h := hc.self (a + b)
  rw [hc.add_left, hc.add_right, hc.add_right, hc.self, hc.self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Negating the first input negates a bilinear cocycle value. -/
theorem IsTwoCocycle.neg_left {c : L → L → M} (hc : IsTwoCocycle k c) (a b : L) :
    c (-a) b = -c a b := by
  rw [show -a = (-1 : k) • a by simp, hc.smul_left]
  simp

end Alternating

section Coefficients

variable {k : Type*} [Field k]

/-- The coefficient on the base/even supporting pair in imaginary layer `m`. -/
noncomputable def imaginaryBaseValue (c : loopPos k → loopPos k → k) (m : ℕ) : k :=
  c (loopFam k .base) (loopFam k (.even m 2))

/-- The extreme odd/odd coefficient after subtracting the normal-form base value. -/
noncomputable def oddImaginaryDeviation (c : loopPos k → loopPos k → k) (a b : ℕ) : k :=
  c (loopFam k (.odd a 0)) (loopFam k (.odd b 4)) - imaginaryBaseValue c (a + b)

/-- The extreme even/even coefficient after subtracting the normal-form base value. -/
noncomputable def evenImaginaryDeviation (c : loopPos k → loopPos k → k) (a b : ℕ) : k :=
  c (loopFam k (.even a 0)) (loopFam k (.even b 2)) -
    imaginaryBaseValue c (a + b + 1)

private theorem lie_loopFam_even_one_odd_four (b d : ℕ) :
    ⁅loopFam k (.odd b 4), loopFam k (.even d 1)⁆ =
      (2 : k) • loopFam k (.odd (b + d + 1) 4) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k (2 * b + 1) (gone k 4), emb k (2 * d + 2) (gzero k 1)⁆ =
    (2 : k) • emb k (2 * (b + d + 1) + 1) (gone k 4)
  rw [emb_lie, ← lie_skew (gone k 4) (gzero k 1), lie_gzero1_gone4,
    neg_smul, neg_neg, map_smul]
  rw [show 2 * b + 1 + (2 * d + 2) = 2 * (b + d + 1) + 1 by omega]

private theorem lie_loopFam_even_one_odd_zero (a d : ℕ) :
    ⁅loopFam k (.even d 1), loopFam k (.odd a 0)⁆ =
      (2 : k) • loopFam k (.odd (a + d + 1) 0) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k (2 * d + 2) (gzero k 1), emb k (2 * a + 1) (gone k 0)⁆ =
    (2 : k) • emb k (2 * (a + d + 1) + 1) (gone k 0)
  rw [emb_lie, lie_gzero1_gone0, map_smul]
  rw [show 2 * d + 2 + (2 * a + 1) = 2 * (a + d + 1) + 1 by omega]

private theorem lie_loopFam_base_even_one (a : ℕ) :
    ⁅loopFam k .base, loopFam k (.even a 1)⁆ = -loopFam k (.even a 0) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k 0 (gzero k 0), emb k (2 * a + 2) (gzero k 1)⁆ =
    -emb k (2 * a + 2) (gzero k 0)
  rw [emb_lie]
  have h : ⁅gzero k 0, gzero k 1⁆ = (-1 : k) • gzero k 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gzero, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
        Matrix.sub_apply, Matrix.smul_apply]
  rw [h, map_smul]
  simp

private theorem lie_loopFam_even_one_even_two (a b : ℕ) :
    ⁅loopFam k (.even a 1), loopFam k (.even b 2)⁆ =
      -loopFam k (.even (a + b + 1) 2) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k (2 * a + 2) (gzero k 1), emb k (2 * b + 2) (gzero k 2)⁆ =
    -emb k (2 * (a + b + 1) + 2) (gzero k 2)
  rw [emb_lie]
  have h : ⁅gzero k 1, gzero k 2⁆ = (-1 : k) • gzero k 2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gzero, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
        Matrix.sub_apply, Matrix.smul_apply]
  rw [h, map_smul]
  rw [show 2 * a + 2 + (2 * b + 2) = 2 * (a + b + 1) + 2 by omega]
  simp

private theorem lie_loopFam_even_two_base (b : ℕ) :
    ⁅loopFam k (.even b 2), loopFam k .base⁆ = -loopFam k (.even b 1) := by
  rw [← lie_skew (loopFam k (.even b 2)) (loopFam k .base),
    lie_loopFam_base_even_last]

/-- Jacobi with the base generator expresses the middle even/even coefficient as its extreme
coefficient minus the base/even normal-form value. -/
theorem IsTwoCocycle.even_middle_eq_deviation
    {c : loopPos k → loopPos k → k} (hc : IsTwoCocycle k c) (a b : ℕ) :
    c (loopFam k (.even a 1)) (loopFam k (.even b 1)) =
      evenImaginaryDeviation c a b := by
  have h := hc.jacobi (loopFam k .base) (loopFam k (.even a 1))
    (loopFam k (.even b 2))
  rw [lie_loopFam_base_even_one, lie_loopFam_even_one_even_two,
    lie_loopFam_even_two_base, hc.neg_left, hc.neg_left, hc.neg_left] at h
  rw [hc.skew (loopFam k (.even (a + b + 1) 2)) (loopFam k .base)] at h
  rw [hc.skew (loopFam k (.even b 1)) (loopFam k (.even a 1))] at h
  simp only [neg_neg] at h
  dsimp [evenImaginaryDeviation, imaginaryBaseValue]
  linear_combination h

/-- **The uniform scalar Jacobi recurrence.** This is the remaining layer-splitting equation
after subtracting the canonical coboundary value from the two extreme supporting families. -/
theorem IsTwoCocycle.imaginary_deviation_recurrence
    {c : loopPos k → loopPos k → k} (hc : IsTwoCocycle k c) (a b d : ℕ) :
    evenImaginaryDeviation c (a + b) d =
      2 * (oddImaginaryDeviation c a (b + d + 1) -
        oddImaginaryDeviation c (a + d + 1) b) := by
  have h := hc.jacobi (loopFam k (.odd a 0)) (loopFam k (.odd b 4))
    (loopFam k (.even d 1))
  have hodd : ⁅loopFam k (.odd a 0), loopFam k (.odd b 4)⁆ =
      loopFam k (.even (a + b) 1) := by
    simpa [Fin.rev, oddImaginaryCoeff] using
      (lie_loopFam_odd_rev (k := k) a b (0 : Fin 5))
  rw [hodd, lie_loopFam_even_one_odd_four,
    lie_loopFam_even_one_odd_zero, hc.smul_left, hc.smul_left] at h
  simp only [smul_eq_mul] at h
  rw [hc.even_middle_eq_deviation (a + b) d] at h
  rw [hc.skew (loopFam k (.odd (b + d + 1) 4)) (loopFam k (.odd a 0))] at h
  dsimp [oddImaginaryDeviation, imaginaryBaseValue]
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  linear_combination h

end Coefficients

end Etingof.Problem2_16_3

-- The source-numbered exercise namespace and established API contain intentional underscores.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_16_3.imaginaryBaseValue
  Etingof.Problem2_16_3.oddImaginaryDeviation
  Etingof.Problem2_16_3.evenImaginaryDeviation
