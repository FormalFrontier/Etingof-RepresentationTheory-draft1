import EtingofRepresentationTheory.Chapter5.YoungRuleSemistandardDiagonal

/-!
# The Kostka-number form of Young's rule

This file packages the final output of the semistandard-tableau analysis as a
module decomposition whose copy index is the combinatorial `KostkaNumber`.
-/

namespace Etingof

noncomputable section

/-- The family of copies of `V_nu` indexed by semistandard tableaux of shape
`nu` and content `mu`. -/
noncomputable abbrev YoungRuleKostkaCopies
    (n : ℕ) (mu nu : Nat.Partition n) :=
  Fin (KostkaNumber n nu mu) → ↥(SpechtModule n nu)

/-- Convert the representation-theoretic isotypic equivalence to a
Kostka-indexed one once the two multiplicities are identified. -/
noncomputable def youngRuleKostkaIsotypicEquivOfEq (n : ℕ)
    (mu nu : Nat.Partition n)
    (h : YoungRuleMultiplicity n mu nu = KostkaNumber n nu mu) :
    ↥(YoungRuleIsotypicComponent n mu nu) ≃ₗ[SymGroupAlgebra n]
      YoungRuleKostkaCopies n mu nu :=
  (youngRuleIsotypicEquiv n mu nu).trans
    (LinearEquiv.cast (R := SymGroupAlgebra n)
      (M := fun k : ℕ => Fin k → ↥(SpechtModule n nu)) h)

/-- Convert the global Young-rule decomposition to combinatorial Kostka
multiplicities once equality is known for every shape. -/
noncomputable def youngRuleKostkaDecompositionOfEq (n : ℕ)
    (mu : Nat.Partition n)
    (h : ∀ nu : Nat.Partition n,
      YoungRuleMultiplicity n mu nu = KostkaNumber n nu mu) :
    PermutationModule n mu ≃ₗ[SymGroupAlgebra n]
      DirectSum (Nat.Partition n) (fun nu => YoungRuleKostkaCopies n mu nu) :=
  (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (fun nu : Nat.Partition n =>
        YoungRuleIsotypicComponent n mu nu))
      (permModule_isotypic_isInternal_module n mu)).symm.trans
    (DFinsupp.mapRange.linearEquiv
      (fun nu => youngRuleKostkaIsotypicEquivOfEq n mu nu (h nu)))

/-- The `nu`-isotypic component of the permutation module has one Specht copy
for every semistandard tableau of shape `nu` and content `mu`. -/
noncomputable def youngRuleKostkaIsotypicEquiv (n : ℕ)
    (mu nu : Nat.Partition n) :
    ↥(YoungRuleIsotypicComponent n mu nu) ≃ₗ[SymGroupAlgebra n]
      YoungRuleKostkaCopies n mu nu :=
  youngRuleKostkaIsotypicEquivOfEq n mu nu
    (youngRuleMultiplicity_eq_kostkaNumber n mu nu)

/-- **Young's rule in Kostka-number form.** The permutation module of content
`mu` is the direct sum, over shapes `nu`, of `KostkaNumber n nu mu` copies of
the Specht module of shape `nu`. -/
noncomputable def youngRuleKostkaDecomposition (n : ℕ)
    (mu : Nat.Partition n) :
    PermutationModule n mu ≃ₗ[SymGroupAlgebra n]
      DirectSum (Nat.Partition n) (fun nu => YoungRuleKostkaCopies n mu nu) :=
  youngRuleKostkaDecompositionOfEq n mu
    (youngRuleMultiplicity_eq_kostkaNumber n mu)

end

end Etingof
