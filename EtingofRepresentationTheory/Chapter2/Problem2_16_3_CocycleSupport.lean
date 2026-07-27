import EtingofRepresentationTheory.Chapter2.Problem2_16_3_Cocycle

/-!
# Imaginary-weight support in the `A₂⁽²⁾` loop model

This file performs the first combinatorial step in the scalar 2-cocycle computation left by
`Problem2_16_3_Cocycle.lean`: it classifies, uniformly in the imaginary weight, every pair of
occupied bidegrees that can support an imaginary-weight cochain.

There are exactly three kinds of pairs, up to order:

* `base` with the last vector in an even layer;
* two odd-layer vectors at reversed finite indices;
* two even-layer vectors at reversed finite indices.

The classification is exposed both as a predicate on `LoopIdx` and as support/vanishing lemmas
for `HasImaginaryWeight` cochains. It removes all impossible parity and coordinate cases before
the remaining cocycle equations are analyzed.
-/

namespace Etingof.Problem2_16_3

/-- Two loop-basis indices have total imaginary bidegree. -/
def IsImaginaryPair (I J : LoopIdx) : Prop :=
  ∃ m : ℕ, I.lbideg + J.lbideg = (2 * m + 2, 4 * m + 4)

/-- The explicit list of pairs of occupied bidegrees that can add to an imaginary bidegree.
The `Fin.rev` in the odd and even cases says that the two positions in a layer add to the last
position (`4` for `Fin 5`, respectively `2` for `Fin 3`). -/
def IsAdmissibleImaginaryPair (I J : LoopIdx) : Prop :=
  (I = .base ∧ ∃ m, J = .even m (Fin.last 2)) ∨
  (J = .base ∧ ∃ m, I = .even m (Fin.last 2)) ∨
  (∃ a b, ∃ i : Fin 5, I = .odd a i ∧ J = .odd b i.rev) ∨
  (∃ a b, ∃ i : Fin 3, I = .even a i ∧ J = .even b i.rev)

/-- The same classification with the imaginary layer `m` fixed. Besides the reversed finite
indices, the two layer numbers must add to `m` in the odd case and to `m - 1` in the even case. -/
def IsAdmissibleImaginaryPairAt (m : ℕ) (I J : LoopIdx) : Prop :=
  (I = .base ∧ J = .even m (Fin.last 2)) ∨
  (J = .base ∧ I = .even m (Fin.last 2)) ∨
  (∃ a b, ∃ i : Fin 5, a + b = m ∧ I = .odd a i ∧ J = .odd b i.rev) ∨
  (∃ a b, ∃ i : Fin 3, a + b + 1 = m ∧ I = .even a i ∧ J = .even b i.rev)

/-- Fixed-layer version of the uniform pair classification. -/
theorem lbideg_add_eq_imaginary_iff (m : ℕ) (I J : LoopIdx) :
    I.lbideg + J.lbideg = (2 * m + 2, 4 * m + 4) ↔
      IsAdmissibleImaginaryPairAt m I J := by
  constructor
  · intro hm
    cases I with
    | base =>
        cases J with
        | base => simp [LoopIdx.lbideg] at hm
        | odd b j => exfalso; simp [LoopIdx.lbideg, Prod.ext_iff] at hm; omega
        | even b j =>
            fin_cases j <;>
              simp [LoopIdx.lbideg, IsAdmissibleImaginaryPairAt, Prod.ext_iff] at hm ⊢ <;> omega
    | odd a i =>
        cases J with
        | base => exfalso; simp [LoopIdx.lbideg, Prod.ext_iff] at hm; omega
        | odd b j =>
            fin_cases i <;> fin_cases j <;>
              simp [LoopIdx.lbideg, IsAdmissibleImaginaryPairAt, Prod.ext_iff] at hm ⊢ <;> omega
        | even b j => exfalso; simp [LoopIdx.lbideg, Prod.ext_iff] at hm; omega
    | even a i =>
        cases J with
        | base =>
            fin_cases i <;>
              simp [LoopIdx.lbideg, IsAdmissibleImaginaryPairAt, Prod.ext_iff] at hm ⊢ <;> omega
        | odd b j => exfalso; simp [LoopIdx.lbideg, Prod.ext_iff] at hm; omega
        | even b j =>
            fin_cases i <;> fin_cases j <;>
              simp [LoopIdx.lbideg, IsAdmissibleImaginaryPairAt, Prod.ext_iff] at hm ⊢ <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨a, b, i, hab, rfl, rfl⟩ | ⟨a, b, i, hab, rfl, rfl⟩)
    · simp [LoopIdx.lbideg, Prod.ext_iff]
      omega
    · simp [LoopIdx.lbideg]
    · simp [LoopIdx.lbideg, Prod.ext_iff]
      omega
    · simp [LoopIdx.lbideg, Prod.ext_iff]
      omega

/-- **Uniform pair classification.** A pair of occupied loop bidegrees has imaginary total
weight if and only if it is one of the three explicit families in
`IsAdmissibleImaginaryPair`. -/
theorem isImaginaryPair_iff_isAdmissible (I J : LoopIdx) :
    IsImaginaryPair I J ↔ IsAdmissibleImaginaryPair I J := by
  constructor
  · rintro ⟨m, hm⟩
    cases I with
    | base =>
        cases J with
        | base => simp [LoopIdx.lbideg] at hm
        | odd b j => exfalso; simp [LoopIdx.lbideg, Prod.ext_iff] at hm; omega
        | even b j =>
            fin_cases j <;>
              simp [LoopIdx.lbideg, IsAdmissibleImaginaryPair, Prod.ext_iff] at hm ⊢ <;> omega
    | odd a i =>
        cases J with
        | base => exfalso; simp [LoopIdx.lbideg, Prod.ext_iff] at hm; omega
        | odd b j =>
            fin_cases i <;> fin_cases j <;>
              simp [LoopIdx.lbideg, IsAdmissibleImaginaryPair, Prod.ext_iff] at hm ⊢ <;> omega
        | even b j => exfalso; simp [LoopIdx.lbideg, Prod.ext_iff] at hm; omega
    | even a i =>
        cases J with
        | base =>
            fin_cases i <;>
              simp [LoopIdx.lbideg, IsAdmissibleImaginaryPair, Prod.ext_iff] at hm ⊢ <;> omega
        | odd b j => exfalso; simp [LoopIdx.lbideg, Prod.ext_iff] at hm; omega
        | even b j =>
            fin_cases i <;> fin_cases j <;>
              simp [LoopIdx.lbideg, IsAdmissibleImaginaryPair, Prod.ext_iff] at hm ⊢ <;> omega
  · intro h
    rcases h with ⟨rfl, m, rfl⟩ | ⟨rfl, m, rfl⟩ |
      ⟨a, b, i, rfl, rfl⟩ | ⟨a, b, i, rfl, rfl⟩
    · exact ⟨m, by simp [LoopIdx.lbideg, Prod.ext_iff]; omega⟩
    · exact ⟨m, by simp [LoopIdx.lbideg]⟩
    · refine ⟨a + b, ?_⟩
      simp [LoopIdx.lbideg, Prod.ext_iff]
      omega
    · refine ⟨a + b + 1, ?_⟩
      simp [LoopIdx.lbideg, Prod.ext_iff]
      omega

/-- The explicit admissibility predicate is symmetric. -/
theorem isAdmissibleImaginaryPair_comm (I J : LoopIdx) :
    IsAdmissibleImaginaryPair I J ↔ IsAdmissibleImaginaryPair J I := by
  rw [← isImaginaryPair_iff_isAdmissible, ← isImaginaryPair_iff_isAdmissible]
  constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨m, ?_⟩ <;>
    simpa [add_comm] using hm

/-- An imaginary-weight cochain vanishes on every pair outside the classified support. -/
theorem HasImaginaryWeight.eq_zero_of_not_admissible {k : Type*} [Field k]
    {c : loopPos k → loopPos k → k} (hc : HasImaginaryWeight c) (I J : LoopIdx)
    (hIJ : ¬ IsAdmissibleImaginaryPair I J) :
    c (loopFam k I) (loopFam k J) = 0 := by
  apply hc I J
  intro m hm
  exact hIJ ((isImaginaryPair_iff_isAdmissible I J).mp ⟨m, hm⟩)

/-- Equivalently, every nonzero coefficient of an imaginary-weight cochain belongs to one of
the three explicitly classified pair families. -/
theorem HasImaginaryWeight.admissible_of_ne_zero {k : Type*} [Field k]
    {c : loopPos k → loopPos k → k} (hc : HasImaginaryWeight c) {I J : LoopIdx}
    (h : c (loopFam k I) (loopFam k J) ≠ 0) :
    IsAdmissibleImaginaryPair I J := by
  by_contra hIJ
  exact h (hc.eq_zero_of_not_admissible I J hIJ)

/-- Layer-refined support: a nonzero coefficient determines an imaginary layer and belongs to
the corresponding fixed-layer decomposition list. -/
theorem HasImaginaryWeight.exists_admissibleAt_of_ne_zero {k : Type*} [Field k]
    {c : loopPos k → loopPos k → k} (hc : HasImaginaryWeight c) {I J : LoopIdx}
    (h : c (loopFam k I) (loopFam k J) ≠ 0) :
    ∃ m, IsAdmissibleImaginaryPairAt m I J := by
  by_contra hpair
  have hno : ∀ m : ℕ, I.lbideg + J.lbideg ≠ (2 * m + 2, 4 * m + 4) := by
    intro m hm
    exact hpair ⟨m, (lbideg_add_eq_imaginary_iff m I J).mp hm⟩
  exact h (hc I J hno)

end Etingof.Problem2_16_3
