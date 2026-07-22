import Mathlib
import EtingofRepresentationTheory.Chapter5.CharValueHookFormula

/-!
# Theorem 5.17.1: Hook Length Formula

The dimension of the Specht module V_λ is given by the hook length formula:

  dim V_λ = n! / ∏_{(i,j) ∈ λ} h(i,j)

where h(i,j) = λᵢ - j + λ'ⱼ - i - 1 is the hook length at cell (i,j)
(using 0-indexed cells), and λ' is the conjugate partition.

## Proof structure

The hook length formula decomposes into two independent results:

1. **Representation → combinatorics**: dim V_λ = |SYT(λ)|, proved via the
   polytabloid basis (see `PolytabloidBasis.lean`).

2. **Frame–Robinson–Thrall (1954)**: |SYT(λ)| = n! / ∏ h(i,j). Proved by
   induction on n via the branching rule (see `FRTHelpers.lean`).
-/

namespace Etingof

noncomputable section

/-- The dimension of V_λ equals the number of standard Young tableaux of shape λ.
This is the core representation-theoretic content.

Proved via the **Frobenius character formula** (`finrank_spechtModule_eq_card_syt_general`,
`CharValueHookFormula.lean`), NOT via the polytabloid/Garnir-straightening basis —
that route (`finrank_spechtModule_eq_card_syt'`, `SpechtModuleBasis.lean`) is no
longer on the critical path for the hook length formula. -/
theorem finrank_spechtModule_eq_card_standardYoungTableau (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (SpechtModule n la) =
      Nat.card (StandardYoungTableau n la) :=
  finrank_spechtModule_eq_card_syt_general n la

/-- Hook length formula: dim V_λ = n! / ∏ h(i,j).
(Etingof Theorem 5.17.1)

The dimension of the Specht module V_λ equals n! divided by the product
of all hook lengths of the Young diagram of λ. -/
theorem Theorem5_17_1
    (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (SpechtModule n la) =
      n.factorial / la.toYoungDiagram.hookLengthProduct := by
  rw [finrank_spechtModule_eq_card_standardYoungTableau,
      card_standardYoungTableau_eq]

end

end Etingof
