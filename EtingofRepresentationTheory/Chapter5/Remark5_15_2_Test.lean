import EtingofRepresentationTheory.Chapter5.Remark5_15_2

/-!
# Downstream import/`#check` test for Remark 5.15.2

Pins the public signatures of the Laurent-polynomial form of the Frobenius character
formula, and records that the endpoints are axiom-clean.

See issue #7405.
-/

namespace Etingof

#check @Etingof.MvLaurent
#check @Etingof.frobeniusLaurentFactor
#check @Etingof.toLaurent
#check @Etingof.Remark5_15_2
#check @Etingof.Remark5_15_2_equiv_Theorem5_15_1
#check @Etingof.rho_monomial_mul_frobeniusLaurentFactor

/-- Signature lock for the remark: the Specht-module character at `σ` is *literally* the
`x^λ` coefficient of `∏_{i<j}(1 - x_j/x_i) · ∏_m pₘ^{iₘ}`, with no sign correction. -/
example (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacter n la σ =
      MvLaurent.coeff (expEmbed n (Nat.Partition.toFinsupp la))
        (frobeniusLaurentFactor n * toLaurent n (cycleTypePsumProduct n σ)) :=
  Remark5_15_2 n la σ

/-- Signature lock for the equivalence with Theorem 5.15.1, stated for an arbitrary
polynomial factor so that it is a statement about the two coefficient extractions and
not about characters. -/
example (n : ℕ) (e : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) ℂ) :
    MvLaurent.coeff (expEmbed n e) (frobeniusLaurentFactor n * toLaurent n P) =
      (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) •
        MvPolynomial.coeff (e + rhoShift n) (vandermondePoly n * P) :=
  Remark5_15_2_equiv_Theorem5_15_1 n e P

/-- The Laurent ring is not degenerate: the variables are genuinely invertible, which is
what makes `frobeniusLaurentFactor` live outside `MvPolynomial`. -/
example (n : ℕ) (i : Fin n) : MvLaurent.X i * MvLaurent.Xinv i = 1 :=
  MvLaurent.X_mul_Xinv i

/-- `toLaurent` preserves coefficients, so the embedding loses no information. -/
example (n : ℕ) (P : MvPolynomial (Fin n) ℂ) (e : Fin n →₀ ℕ) :
    MvLaurent.coeff (expEmbed n e) (toLaurent n P) = MvPolynomial.coeff e P :=
  coeff_toLaurent n P e

/-- Non-vacuity: `MvLaurent n` is not the zero ring, and `toLaurent` is injective, so the
coefficient statements above are not trivially satisfied. -/
example (n : ℕ) : Nontrivial (MvLaurent n) := inferInstance

example (n : ℕ) : Function.Injective (toLaurent n) := toLaurent_injective n

#print axioms Etingof.Remark5_15_2
#print axioms Etingof.Remark5_15_2_equiv_Theorem5_15_1
#print axioms Etingof.rho_monomial_mul_frobeniusLaurentFactor
#print axioms Etingof.bookVandermondePoly_eq_smul

end Etingof
