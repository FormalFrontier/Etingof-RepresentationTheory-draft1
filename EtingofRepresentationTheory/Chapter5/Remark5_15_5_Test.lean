import EtingofRepresentationTheory.Chapter5.Remark5_15_5

/-!
# Downstream import/`#check` test for Remark 5.15.5

Pins the public signatures of the positive-root order and its consequences, and checks
that none of them depends on `sorryAx`.
-/

namespace Etingof

-- The positive-root order and the partial-order laws.
#check @Nat.Partition.RootLe
#check @Nat.Partition.RootLe.refl
#check @Nat.Partition.RootLe.trans
#check @Nat.Partition.RootLe.antisymm
#check @Etingof.rootLe_isPartialOrder

-- The book's implication `μ ≽ λ → μ ≥ λ`, its converse, and the resulting equivalence.
#check @Nat.Partition.RootLe.dominates
#check @Nat.Partition.Dominates.rootLe
#check @Nat.Partition.rootLe_iff_dominates

-- The root-order vanishing of Kostka numbers.
#check @Etingof.spechtMultiplicity_vanishing_rootOrder

-- Signature lock: the order is stated exactly as "`μ - λ` is a sum of `e i - e j`, `i < j`".
example {n : ℕ} (la mu : Nat.Partition n) :
    la.RootLe mu ↔
      ∃ L : List (ℕ × ℕ), (∀ p ∈ L, p.1 < p.2) ∧
        ∀ k : ℕ, (mu.partAt k : ℤ) = la.partAt k + (L.map (fun p => rootVec p.1 p.2 k)).sum :=
  Iff.rfl

-- The Kostka matrix, its inverse, and the character expansion.
#check @Etingof.kostkaMatrix
#check @Etingof.kostkaMatrix_diagonal
#check @Etingof.kostkaMatrix_eq_zero_of_not_rootLe
#check @Etingof.inverseKostkaMatrix
#check @Etingof.inverseKostkaMatrix_mul
#check @Etingof.mul_inverseKostkaMatrix
#check @Etingof.isUnit_kostkaMatrix
#check @Etingof.inverseKostkaMatrix_eq_zero_of_not_rootLe
#check @Etingof.spechtCharacter_eq_sum_inverseKostka
#check @Etingof.spechtCharacter_eq_sum_inverseKostka_rootLe

-- Signature lock: `K̃` really is the matrix inverse of `K`, in both directions.
example (n : ℕ) : inverseKostkaMatrix n = (kostkaMatrix n)⁻¹ := rfl

example (n : ℕ) :
    kostkaMatrix n * inverseKostkaMatrix n = 1 ∧
      inverseKostkaMatrix n * kostkaMatrix n = 1 :=
  ⟨mul_inverseKostkaMatrix, inverseKostkaMatrix_mul⟩

-- No `sorry` anywhere in the chain.
#print axioms Nat.Partition.rootLe_iff_dominates
#print axioms Etingof.spechtMultiplicity_vanishing_rootOrder
#print axioms Etingof.rootLe_isPartialOrder
#print axioms Etingof.isUnit_kostkaMatrix
#print axioms Etingof.inverseKostkaMatrix_eq_zero_of_not_rootLe
#print axioms Etingof.spechtCharacter_eq_sum_inverseKostka
#print axioms Etingof.spechtCharacter_eq_sum_inverseKostka_rootLe

end Etingof
