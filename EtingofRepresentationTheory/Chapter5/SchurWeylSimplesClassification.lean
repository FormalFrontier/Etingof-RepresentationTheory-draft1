import EtingofRepresentationTheory.Chapter5.FormalCharacterIso

/-!
# Highest-weight classification of the Schur-Weyl simple summands

This file carves out the **conceptual crux** of Schur-Weyl #6
(`iso_of_formalCharacter_eq_schurPoly`, issue #2483): identifying the *abstract*
simple summands `L i` produced by the equivariant decomposition
`glTensorRep_equivariant_schurWeyl_decomposition`
(`Chapter5/FormalCharacterIso.lean`) of `V^{⊗n}` (`V = Fin N → k`, `n ≤ N`) with
concrete Schur modules, at the level of their formal characters.

The decomposition gives a `GL_N(k)`-equivariant iso
`V^{⊗n} ≃ₗ[k] ⨁ i, S i ⊗[k] L i` with each `L i` a simple polynomial
`GL_N(k)`-representation. The genuine mathematical content here is the
highest-weight theorem "a simple polynomial `GL_N`-rep is determined by its
character," which pins each `char(L i)` to a Schur polynomial `schurPoly N λᵢ`
for an injective partition assignment `λ`.

## Contents

* `formalCharacter_linearIndependent_of_eq_schurPoly` — the **reduction**
  (sorry-free): if the characters of a family `L` equal distinct Schur
  polynomials, they are linearly independent over `ℚ`. This is the mechanical
  half noted in the strategy ("the classification gives linear independence for
  free via `schurPoly_linearIndependent` + `schurPoly_injective`").

The former classification crux `schurWeyl_simples_formalCharacter_classification_core`
and its corollaries (`glTensorRep_schurWeyl_simples_schurPoly_classified`,
`glTensorRep_schurWeyl_simples_formalCharacter_linearIndependent`) have been
**removed** (issue #4994 / #5024): as stated they were *false* — they lacked the
nonzero-multiplicity hypothesis `hSne` (each `S i ≠ 0`), so a degenerate
decomposition with `S i₀ = 0` carried an unconstrained "ghost" simple `L i₀` whose
character need not be a Schur polynomial. The true classification is
`schurWeyl_simples_formalCharacter_classification_core_general`
(`Chapter5/SchurWeylFormalCharacterIso.lean`), which carries `hSne` and is invoked
directly by the consumers on the decomposition witnesses exposed by
`decompose_polynomial_gl_rep`.
-/

open CategoryTheory MvPolynomial

open scoped TensorProduct

namespace Etingof

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

omit [CharZero k] in
/-- **Reduction (sorry-free).** If each character `formalCharacter k N (L i)`
equals a Schur polynomial `schurPoly N (lam i)` along an *injective* assignment
`lam` of antitone partitions, then the characters are linearly independent over
`ℚ`.

This is the mechanical half of the highest-weight classification: it turns the
identification `char(L i) = schurPoly N λᵢ` (from the relocated classification core
`schurWeyl_simples_formalCharacter_classification_core_general`) into the
`LinearIndependent` statement the Schur-Weyl assembly (#2483) consumes, using
the linear independence of Schur polynomials (`schurPoly_linearIndependent`). -/
theorem formalCharacter_linearIndependent_of_eq_schurPoly
    (N : ℕ) {ι : Type*}
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (lam : ι → {l : Fin N → ℕ // Antitone l})
    (hlam : Function.Injective lam)
    (hchar : ∀ i, formalCharacter k N (L i) = schurPoly N (lam i).val) :
    LinearIndependent ℚ (fun i => formalCharacter k N (L i)) := by
  have hcomp :
      (fun i => formalCharacter k N (L i))
        = (fun p : {l : Fin N → ℕ // Antitone l} => schurPoly N p.val) ∘ lam := by
    funext i; exact hchar i
  rw [hcomp]
  exact (schurPoly_linearIndependent N).comp lam hlam

end Etingof
