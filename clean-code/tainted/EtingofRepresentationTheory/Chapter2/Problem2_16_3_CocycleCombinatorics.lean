import EtingofRepresentationTheory.Chapter2.Problem2_16_3_Cocycle


/-!
# Problem 2.16.3(b): combinatorics of imaginary-weight cocycles

This file carries out the first uniform step in the cocycle computation isolated in
`Problem2_16_3_Cocycle.lean`: it classifies all pairs of graded basis vectors whose pulled-back
bidegrees add to an imaginary bidegree `(2m+2, 4m+4)`.

There are exactly four ordered families:

* `base, even m 2`;
* `even m 2, base`;
* `odd a i, odd b j` with `i + j = 4`;
* `even a i, even b j` with `i + j = 2`.

In particular, mixed odd/even pairs never contribute.  The file also identifies every occupied
pulled-back bidegree component with the span of its unique basis vector and specializes this at
the imaginary bidegrees.  Thus every bracket attached to one of the pairs above lands in the
single line spanned by `loopFam k (.even m 1)`.  These are the finite families on which the
remaining cocycle recurrence has to be solved.
-/

namespace Etingof.Problem2_16_3

attribute [local instance] LieRing.ofAssociativeRing

/-- Two loop-basis indices form an imaginary pair if their pulled-back bidegrees add to some
`(2m+2, 4m+4)`. -/
def IsImaginaryPair (I J : LoopIdx) : Prop :=
  ∃ m : ℕ, I.lbideg + J.lbideg = (2 * m + 2, 4 * m + 4)

/-- **Uniform enumeration of imaginary pairs.** This removes the unbounded bidegree arithmetic
from the subsequent cocycle computation: only four index shapes can support an imaginary-weight
cochain. -/
theorem isImaginaryPair_iff (I J : LoopIdx) :
    IsImaginaryPair I J ↔
      (∃ m : ℕ, I = .base ∧ J = .even m 2) ∨
      (∃ m : ℕ, I = .even m 2 ∧ J = .base) ∨
      (∃ (a b : ℕ) (i j : Fin 5),
        I = .odd a i ∧ J = .odd b j ∧ (i : ℕ) + (j : ℕ) = 4) ∨
      ∃ (a b : ℕ) (i j : Fin 3),
        I = .even a i ∧ J = .even b j ∧ (i : ℕ) + (j : ℕ) = 2 := by
  cases I with
  | base =>
      cases J with
      | base => simp [IsImaginaryPair]
      | odd b j => simp [IsImaginaryPair]; omega
      | even b j =>
          fin_cases j <;> simp [IsImaginaryPair, Fin.rev] <;> omega
  | odd a i =>
      cases J with
      | base => simp [IsImaginaryPair]; omega
      | odd b j =>
          fin_cases i <;> fin_cases j <;> simp [IsImaginaryPair, Fin.rev] <;> try omega
          all_goals exact ⟨a + b, by omega⟩
      | even b j => simp [IsImaginaryPair]; omega
  | even a i =>
      cases J with
      | base =>
          fin_cases i <;> simp [IsImaginaryPair, Fin.rev]
      | odd b j => simp [IsImaginaryPair]; omega
      | even b j =>
          fin_cases i <;> fin_cases j <;> simp [IsImaginaryPair, Fin.rev] <;> try omega
          all_goals exact ⟨a + b + 1, by omega⟩

/-- A pair is outside imaginary weight exactly when it is outside the four families enumerated
by `isImaginaryPair_iff`. -/
theorem not_isImaginaryPair_iff (I J : LoopIdx) :
    (∀ m : ℕ, I.lbideg + J.lbideg ≠ (2 * m + 2, 4 * m + 4)) ↔
      ¬ IsImaginaryPair I J := by
  simp [IsImaginaryPair]

/-! ## Structure constants on the imaginary pairs -/

/-- Structure constants for brackets of complementary odd-layer basis vectors. -/
def oddImaginaryCoeff (k : Type*) [Ring k] : Fin 5 → k :=
  ![1, 1, 0, -1, -1]

/-- Structure constants for brackets of complementary even-layer basis vectors. -/
def evenImaginaryCoeff (k : Type*) [Ring k] : Fin 3 → k :=
  ![1, 0, -1]

/-- Complementarity in `Fin 5` expressed by the ordinary-index sum used in
`isImaginaryPair_iff`. -/
theorem fin5_eq_rev_of_add_eq_four {i j : Fin 5}
    (hij : (i : ℕ) + (j : ℕ) = 4) : j = i.rev := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.rev]

/-- Complementarity in `Fin 3` expressed by the ordinary-index sum used in
`isImaginaryPair_iff`. -/
theorem fin3_eq_rev_of_add_eq_two {i j : Fin 3}
    (hij : (i : ℕ) + (j : ℕ) = 2) : j = i.rev := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.rev]

/-- The five complementary brackets in the odd constant-matrix layer all land on the diagonal
vector `gzero 1`, with coefficients `1, 1, 0, -1, -1`. -/
private theorem lie_gone1_gone3_imaginary {k : Type*} [CommRing k] :
    ⁅gone k 1, gone k 3⁆ = gzero k 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gone, gzero, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply]

/-- The bracket with the reversed degree-one generator. -/
theorem lie_gone_rev {k : Type*} [CommRing k] (i : Fin 5) :
    ⁅gone k i, gone k i.rev⁆ = oddImaginaryCoeff k i • gzero k 1 := by
  fin_cases i
  · change ⁅gone k (0 : Fin 5), gone k (4 : Fin 5)⁆ = (1 : k) • gzero k 1
    rw [← lie_skew (gone k 0) (gone k 4), lie_gone4_gone0]
    simp
  · change ⁅gone k (1 : Fin 5), gone k (3 : Fin 5)⁆ = (1 : k) • gzero k 1
    simpa using lie_gone1_gone3_imaginary (k := k)
  · change ⁅gone k (2 : Fin 5), gone k (2 : Fin 5)⁆ = (0 : k) • gzero k 1
    simp
  · change ⁅gone k (3 : Fin 5), gone k (1 : Fin 5)⁆ = (-1 : k) • gzero k 1
    rw [← lie_skew (gone k 3) (gone k 1), lie_gone1_gone3_imaginary]
    simp
  · change ⁅gone k (4 : Fin 5), gone k (0 : Fin 5)⁆ = (-1 : k) • gzero k 1
    simpa using lie_gone4_gone0 (k := k)

/-- The three complementary brackets in the even constant-matrix layer have coefficients
`1, 0, -1` on `gzero 1`. -/
private theorem lie_gzero0_gzero2_imaginary {k : Type*} [CommRing k] :
    ⁅gzero k 0, gzero k 2⁆ = gzero k 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gzero, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply]

/-- The bracket with the reversed degree-zero generator. -/
theorem lie_gzero_rev {k : Type*} [CommRing k] (i : Fin 3) :
    ⁅gzero k i, gzero k i.rev⁆ = evenImaginaryCoeff k i • gzero k 1 := by
  fin_cases i
  · change ⁅gzero k (0 : Fin 3), gzero k (2 : Fin 3)⁆ = (1 : k) • gzero k 1
    simpa using lie_gzero0_gzero2_imaginary (k := k)
  · change ⁅gzero k (1 : Fin 3), gzero k (1 : Fin 3)⁆ = (0 : k) • gzero k 1
    simp
  · change ⁅gzero k (2 : Fin 3), gzero k (0 : Fin 3)⁆ = (-1 : k) • gzero k 1
    rw [← lie_skew (gzero k 2) (gzero k 0), lie_gzero0_gzero2_imaginary]
    simp

/-- Complementary odd loop-basis vectors bracket to the unique imaginary basis vector in their
total bidegree, with a coefficient independent of the layer numbers. -/
theorem lie_loopFam_odd_rev
    {k : Type*} [Field k] (a b : ℕ) (i : Fin 5) :
    ⁅loopFam k (.odd a i), loopFam k (.odd b i.rev)⁆ =
      oddImaginaryCoeff k i • loopFam k (.even (a + b) 1) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k (2 * a + 1) (gone k i), emb k (2 * b + 1) (gone k i.rev)⁆ =
    oddImaginaryCoeff k i • emb k (2 * (a + b) + 2) (gzero k 1)
  rw [emb_lie, lie_gone_rev, map_smul]
  rw [show 2 * a + 1 + (2 * b + 1) = 2 * (a + b) + 2 by omega]

/-- The odd/odd bracket formula in the ordinary-index form returned by the imaginary-pair
enumeration. -/
theorem lie_loopFam_odd_of_add_eq_four
    {k : Type*} [Field k] (a b : ℕ) (i j : Fin 5)
    (hij : (i : ℕ) + (j : ℕ) = 4) :
    ⁅loopFam k (.odd a i), loopFam k (.odd b j)⁆ =
      oddImaginaryCoeff k i • loopFam k (.even (a + b) 1) := by
  rw [fin5_eq_rev_of_add_eq_four hij]
  exact lie_loopFam_odd_rev a b i

/-- Complementary even loop-basis vectors bracket to the unique imaginary basis vector in their
total bidegree, with a coefficient independent of the layer numbers. -/
theorem lie_loopFam_even_rev
    {k : Type*} [Field k] (a b : ℕ) (i : Fin 3) :
    ⁅loopFam k (.even a i), loopFam k (.even b i.rev)⁆ =
      evenImaginaryCoeff k i • loopFam k (.even (a + b + 1) 1) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k (2 * a + 2) (gzero k i), emb k (2 * b + 2) (gzero k i.rev)⁆ =
    evenImaginaryCoeff k i • emb k (2 * (a + b + 1) + 2) (gzero k 1)
  rw [emb_lie, lie_gzero_rev, map_smul]
  rw [show 2 * a + 2 + (2 * b + 2) = 2 * (a + b + 1) + 2 by omega]

/-- The even/even bracket formula in the ordinary-index form returned by the imaginary-pair
enumeration. -/
theorem lie_loopFam_even_of_add_eq_two
    {k : Type*} [Field k] (a b : ℕ) (i j : Fin 3)
    (hij : (i : ℕ) + (j : ℕ) = 2) :
    ⁅loopFam k (.even a i), loopFam k (.even b j)⁆ =
      evenImaginaryCoeff k i • loopFam k (.even (a + b + 1) 1) := by
  rw [fin3_eq_rev_of_add_eq_two hij]
  exact lie_loopFam_even_rev a b i

/-- The remaining base/even imaginary bracket also has coefficient one on the target line. -/
theorem lie_loopFam_base_even_last
    {k : Type*} [Field k] (m : ℕ) :
    ⁅loopFam k .base, loopFam k (.even m 2)⁆ = loopFam k (.even m 1) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅emb k 0 (gzero k 0), emb k (2 * m + 2) (gzero k 2)⁆ =
    emb k (2 * m + 2) (gzero k 1)
  rw [emb_lie]
  have h : ⁅gzero k 0, gzero k 2⁆ = gzero k 1 := by
    simpa [evenImaginaryCoeff] using lie_gzero_rev (k := k) (0 : Fin 3)
  rw [h]
  rw [show 0 + (2 * m + 2) = 2 * m + 2 by omega]

/-- The reverse ordering of the base/even imaginary bracket. -/
theorem lie_loopFam_even_last_base
    {k : Type*} [Field k] (m : ℕ) :
    ⁅loopFam k (.even m 2), loopFam k .base⁆ = -loopFam k (.even m 1) := by
  rw [← lie_skew (loopFam k (.even m 2)) (loopFam k .base),
    lie_loopFam_base_even_last]

/-! ## Normal form for the desired coboundaries -/

/-- A scalar sequence on the imaginary degrees, extended by zero to all loop-basis indices. -/
def imaginaryBasisValue
    {k : Type*} [Zero k] (s : ℕ → k) : LoopIdx → k
  | .base => 0
  | .odd _ _ => 0
  | .even m i => if i = 1 then s m else 0

/-- The linear functional on the loop model supported on the unique basis vector in every
imaginary bidegree. -/
noncomputable def imaginaryFunctional
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k) :
    loopPos k →ₗ[k] k :=
  (loopBasis k h2).constr k (imaginaryBasisValue s)

/-- The imaginary functional on a loop-family vector. -/
@[simp] theorem imaginaryFunctional_loopFam
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k) (I : LoopIdx) :
    imaginaryFunctional h2 s (loopFam k I) = imaginaryBasisValue s I := by
  rw [imaginaryFunctional, ← loopBasis_apply k h2 I, Module.Basis.constr_basis]

/-- The coboundary associated to a scalar sequence on the imaginary degrees. -/
noncomputable def imaginaryCoboundary
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k) :
    loopPos k → loopPos k → k :=
  fun a b => imaginaryFunctional h2 s ⁅a, b⁆

/-- The imaginary coboundary is a two-coboundary. -/
theorem isTwoCoboundary_imaginaryCoboundary
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k) :
    IsTwoCoboundary k (imaginaryCoboundary h2 s) :=
  ⟨imaginaryFunctional h2 s, fun _ _ => rfl⟩

/-- On the base/even supporting pair, the normal-form coboundary reads off `s m`. -/
@[simp] theorem imaginaryCoboundary_base_even_last
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k) (m : ℕ) :
    imaginaryCoboundary h2 s (loopFam k .base) (loopFam k (.even m 2)) = s m := by
  rw [imaginaryCoboundary, lie_loopFam_base_even_last, imaginaryFunctional_loopFam]
  simp [imaginaryBasisValue]

/-- Values of the normal-form coboundary on every odd/odd supporting pair. -/
theorem imaginaryCoboundary_odd_of_add_eq_four
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k)
    (a b : ℕ) (i j : Fin 5) (hij : (i : ℕ) + (j : ℕ) = 4) :
    imaginaryCoboundary h2 s (loopFam k (.odd a i)) (loopFam k (.odd b j)) =
      oddImaginaryCoeff k i * s (a + b) := by
  rw [imaginaryCoboundary, lie_loopFam_odd_of_add_eq_four a b i j hij, map_smul,
    imaginaryFunctional_loopFam]
  simp [imaginaryBasisValue, smul_eq_mul]

/-- Values of the normal-form coboundary on every even/even supporting pair. -/
theorem imaginaryCoboundary_even_of_add_eq_two
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k)
    (a b : ℕ) (i j : Fin 3) (hij : (i : ℕ) + (j : ℕ) = 2) :
    imaginaryCoboundary h2 s (loopFam k (.even a i)) (loopFam k (.even b j)) =
      evenImaginaryCoeff k i * s (a + b + 1) := by
  rw [imaginaryCoboundary, lie_loopFam_even_of_add_eq_two a b i j hij, map_smul,
    imaginaryFunctional_loopFam]
  simp [imaginaryBasisValue, smul_eq_mul]

/-- An occupied pulled-back bidegree component is precisely the line through its unique basis
vector. -/
theorem lDeg_lbideg_eq_span_singleton {k : Type*} [Field k] (I : LoopIdx) :
    lDeg k I.lbideg = Submodule.span k {loopFam k I} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro v ⟨J, hJ, rfl⟩
    have hJI : J = I := lbideg_injective hJ
    subst J
    exact Submodule.subset_span rfl
  · exact Submodule.span_le.2 fun v hv => by
      rw [Set.mem_singleton_iff] at hv
      subst v
      exact loopFam_mem_lDeg I

/-- The imaginary bidegree `(2m+2, 4m+4)` is occupied by exactly
`loopFam k (.even m 1)`. -/
theorem lDeg_imaginary_eq_span_singleton {k : Type*} [Field k] (m : ℕ) :
    lDeg k (2 * m + 2, 4 * m + 4) =
      Submodule.span k {loopFam k (.even m 1)} := by
  have hdeg : (LoopIdx.even m 1).lbideg = (2 * m + 2, 4 * m + 4) := by
    simp [Fin.rev]
  rw [← hdeg, lDeg_lbideg_eq_span_singleton]

/-- The bracket of every imaginary pair lies in the unique imaginary line of the corresponding
total bidegree. -/
theorem lie_loopFam_mem_imaginary_span
    {k : Type*} [Field k]
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (I J : LoopIdx) (m : ℕ)
    (hIJ : I.lbideg + J.lbideg = (2 * m + 2, 4 * m + 4)) :
    ⁅loopFam k I, loopFam k J⁆ ∈
      Submodule.span k {loopFam k (.even m 1)} := by
  rw [← lDeg_imaginary_eq_span_singleton m, ← hIJ]
  exact lie_loopFam_mem_lDeg h2 h3 h5 I J

/-- Imaginary-weight cochains vanish on a basis pair precisely whenever the pair is not one of
the four enumerated families. -/
theorem HasImaginaryWeight.eq_zero_of_not_isImaginaryPair
    {k : Type*} [Field k] {c : loopPos k → loopPos k → k}
    (hc : HasImaginaryWeight c) {I J : LoopIdx} (hIJ : ¬ IsImaginaryPair I J) :
    c (loopFam k I) (loopFam k J) = 0 :=
  hc I J ((not_isImaginaryPair_iff I J).2 hIJ)

end Etingof.Problem2_16_3

-- The source-numbered exercise namespace and established API contain intentional underscores.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_16_3.IsImaginaryPair
  Etingof.Problem2_16_3.oddImaginaryCoeff
  Etingof.Problem2_16_3.evenImaginaryCoeff
  Etingof.Problem2_16_3.imaginaryBasisValue
  Etingof.Problem2_16_3.imaginaryFunctional
  Etingof.Problem2_16_3.imaginaryCoboundary
