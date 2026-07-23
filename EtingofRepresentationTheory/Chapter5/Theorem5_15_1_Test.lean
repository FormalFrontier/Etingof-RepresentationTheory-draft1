import EtingofRepresentationTheory.Chapter5.Theorem5_15_1

/-!
# Downstream import/`#check` test for Theorem 5.15.1

This file imports `Chapter5/Theorem5_15_1.lean` and pins the public signatures of the
Frobenius character formula and the isotypic-decomposition endpoints it depends on.

Its purpose is to catch a regression in the *source* of Theorem 5.15.1 even when cached
oleans would otherwise hide it from the aggregate build: because this file `import`s the
theorem file and re-elaborates the endpoint statements, it forces a fresh check of the
public API (including the semisimplicity, `Module.Free`, scalar-tower, and
`restrictScalars` infrastructure repaired in issue #7512).

See issue #7512 (restore fresh-buildable Theorem 5.15.1).
-/

namespace Etingof

-- The public Frobenius-character endpoint must remain importable under this name.
#check @Etingof.Theorem5_15_1

-- Supporting endpoints repaired alongside the main theorem.
#check @Etingof.trace_isotypic_eq_mult_trace
#check @Etingof.trace_isotypic_eq_mult_character
#check @Etingof.spechtModules_exhaust_simples
#check @Etingof.permModuleEndomorphism_mapsTo_isotypic
#check @Etingof.isotypicComponent_linearEquiv_fun

-- Signature lock for the main theorem: the sign-twisted Specht-module character at `σ`
-- equals the `x^{λ+ρ}` coefficient of `Δ(x) · ∏ pₘ^{iₘ}`.  Re-stating the conclusion
-- forces a fresh elaboration of its shape; any drift in hypotheses or conclusion makes
-- this `example` fail to elaborate.
example (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) • spechtModuleCharacter n la σ =
      MvPolynomial.coeff (Nat.Partition.toFinsupp la + rhoShift n)
        (vandermondePoly n * cycleTypePsumProduct n σ) :=
  Theorem5_15_1 n la σ

-- The trace-on-isotypic-component endpoint: for the permutation module `U_μ`, the trace
-- of `σ` on the `V_ν`-isotypic component equals `(multiplicity) · χ_{V_ν}(σ)`.
example (n : ℕ) (mu nu : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    LinearMap.trace ℂ _ ((permModuleEndomorphism n mu σ).restrict
        (permModuleEndomorphism_mapsTo_isotypic n mu σ nu)) =
      (spechtMultiplicity n mu nu : ℂ) * spechtModuleCharacter n nu σ :=
  trace_isotypic_eq_mult_character n mu nu σ

end Etingof
