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

-- No `sorry` anywhere in the chain.
#print axioms Nat.Partition.rootLe_iff_dominates
#print axioms Etingof.spechtMultiplicity_vanishing_rootOrder
#print axioms Etingof.rootLe_isPartialOrder

end Etingof
