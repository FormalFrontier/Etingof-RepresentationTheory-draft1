import EtingofRepresentationTheory.Chapter5.Theorem5_15_1

/-!
# Young's-rule module decomposition

This file packages the isotypic analysis used by the Frobenius character proof
as the global `SymGroupAlgebra n`-linear decomposition promised by Proposition
5.14.1.  The multiplicity is deliberately named `YoungRuleMultiplicity`: it is
the representation-theoretic Hom-space dimension `spechtMultiplicity` rather
than the definitionally separate tableau cardinal `KostkaNumber`; their equality
is established downstream by the semistandard-tableau basis of row invariants.
-/

namespace Etingof

/-- The representation-theoretic multiplicity in Young's rule.  This name keeps
the Hom-space dimension distinguishable from the combinatorial tableau cardinal;
`youngRuleMultiplicity_eq_kostkaNumber` identifies them downstream. -/
noncomputable abbrev YoungRuleMultiplicity
    (n : ℕ) (mu nu : Nat.Partition n) : ℕ :=
  spechtMultiplicity n mu nu

/-- The `nu`-isotypic summand of the permutation module `U_mu`, as an actual
`SymGroupAlgebra n`-submodule. -/
noncomputable abbrev YoungRuleIsotypicComponent
    (n : ℕ) (mu nu : Nat.Partition n) :=
  isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu)
    (SpechtModule n nu)

/-- The family of copies of the Specht module occurring with the Young-rule
multiplicity. -/
noncomputable abbrev YoungRuleCopies
    (n : ℕ) (mu nu : Nat.Partition n) :=
  Fin (YoungRuleMultiplicity n mu nu) → ↥(SpechtModule n nu)

/-- A chosen module-linear identification of an isotypic component with the
corresponding family of copies of its Specht module. -/
noncomputable def youngRuleIsotypicEquiv (n : ℕ) (mu nu : Nat.Partition n) :
    ↥(YoungRuleIsotypicComponent n mu nu) ≃ₗ[SymGroupAlgebra n]
      YoungRuleCopies n mu nu :=
  Classical.choice (isotypicComponent_linearEquiv_fun_module n mu nu)

/-- **Young's rule, global module form.** The permutation module `U_mu` is the
internal direct sum, over partitions `nu`, of `YoungRuleMultiplicity(mu,nu)`
copies of the Specht module `V_nu`.  The following support theorem shows that
all terms outside `nu ≥ mu` are zero, so this all-partitions direct sum is the
type-theoretically convenient form of `⊕_{nu ≥ mu}`. -/
noncomputable def youngRuleDecomposition (n : ℕ) (mu : Nat.Partition n) :
    PermutationModule n mu ≃ₗ[SymGroupAlgebra n]
      DirectSum (Nat.Partition n) (fun nu => YoungRuleCopies n mu nu) :=
  (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (fun nu : Nat.Partition n =>
        YoungRuleIsotypicComponent n mu nu))
      (permModule_isotypic_isInternal_module n mu)).symm.trans
    (DFinsupp.mapRange.linearEquiv (fun nu => youngRuleIsotypicEquiv n mu nu))

/-- Young's-rule multiplicities vanish outside the dominance cone. -/
theorem youngRuleMultiplicity_eq_zero_of_not_dominates
    (n : ℕ) (mu nu : Nat.Partition n)
    (h : ¬ Nat.Partition.Dominates nu mu) :
    YoungRuleMultiplicity n mu nu = 0 :=
  spechtMultiplicity_vanishing_general n mu nu h

/-- Consequently every direct-sum term outside `nu ≥ mu` is the zero module. -/
theorem youngRuleCopies_subsingleton_of_not_dominates
    (n : ℕ) (mu nu : Nat.Partition n)
    (h : ¬ Nat.Partition.Dominates nu mu) :
    Subsingleton (YoungRuleCopies n mu nu) := by
  change Subsingleton
    (Fin (spechtMultiplicity n mu nu) → ↥(SpechtModule n nu))
  rw [spechtMultiplicity_vanishing_general n mu nu h]
  infer_instance

/-- The diagonal Young-rule multiplicity is one. -/
theorem youngRuleMultiplicity_diagonal (n : ℕ) (mu : Nat.Partition n) :
    YoungRuleMultiplicity n mu mu = 1 :=
  spechtMultiplicity_diagonal n mu

/-- The diagonal summand is one copy of `V_mu`. -/
noncomputable def youngRuleDiagonalEquiv (n : ℕ) (mu : Nat.Partition n) :
    YoungRuleCopies n mu mu ≃ₗ[SymGroupAlgebra n] ↥(SpechtModule n mu) := by
  change (Fin (spechtMultiplicity n mu mu) → ↥(SpechtModule n mu))
    ≃ₗ[SymGroupAlgebra n] ↥(SpechtModule n mu)
  exact
    (LinearEquiv.cast (R := SymGroupAlgebra n)
      (M := fun k : ℕ => Fin k → ↥(SpechtModule n mu))
      (spechtMultiplicity_diagonal n mu)).trans
      (LinearEquiv.funUnique (Fin 1) (SymGroupAlgebra n)
        ↥(SpechtModule n mu))

end Etingof
