import EtingofRepresentationTheory.Chapter5.PolynomialGLDecomposition
import EtingofRepresentationTheory.Chapter5.SchurWeylSimplesClassification

/-!
# Schur-Weyl #6: the formal character determines the isomorphism class

This file hosts `iso_of_formalCharacter_eq_schurPoly` (Etingof §5.22, issue
#2483): a finite-dimensional polynomial `GL_N(k)`-representation whose formal
character equals a Schur polynomial `S_λ` is isomorphic to the Schur module
`L_λ`.

## Why this lives here (not in `FormalCharacterIso`)

The theorem's essential dependency `decompose_polynomial_gl_rep`
(`PolynomialGLDecomposition`) sits **downstream** of `FormalCharacterIso`:
`PolynomialGLDecomposition` imports `FormalCharacterIso`. Proving the theorem in
`FormalCharacterIso` would therefore create an import cycle. It is relocated here,
downstream of both `PolynomialGLDecomposition` (the equivariant decomposition)
and `SchurWeylSimplesClassification` (#4698, linear independence of the abstract
simple characters). See issue #4699.

## Proof route (abstract-simple form)

Let `n := ∑ i, lam i`.

1. **`M` is homogeneous of degree `n`.** `weight_magnitude_of_formalCharacter_eq_schurPoly`
   turns `formalCharacter M = schurPoly N lam` into the `h_homog` hypothesis
   `decompose_polynomial_gl_rep` expects.
2. **Decompose `M`.** `decompose_polynomial_gl_rep` gives
   `M.asModule ≃ ⨁_{j:Fin p} (L (f j)).asModule` for abstract simples `L i`.
3. **Character match.** Push `formalCharacter` through the decomposition
   (`formalCharacter_directSum` + `formalCharacter_eq_of_rep_iso`):
   `schurPoly N lam = formalCharacter M = ∑_j formalCharacter (L (f j))`.
4. **Conclude via #4698.** The abstract simples each have `formalCharacter` a
   distinct Schur polynomial, so their characters are linearly independent
   (`SchurWeylSimplesClassification`). The single-`schurPoly` left side then
   forces `p = 1` with `f 0` the class of `L_λ`, hence
   `M ≃ L_λ` at the `asModule` level; rebuild the categorical `≅`.

## Remaining work (issue #4699 deliverable 3)

The proof is currently `sorry`. Closing it requires three ingredients that the
current upstream API does not yet expose; each is filed as a follow-up:

* **Algebraicity.** `decompose_polynomial_gl_rep` needs
  `halg : Etingof.IsAlgebraicRepresentation N M.ρ`, which is *not* implied by
  `formalCharacter M = schurPoly N lam` + `h_dim` (algebraicity is the structural
  "matrix entries are polynomials" property, not a character-level one). The
  signature must gain `halg`, and the sole consumer (`schurModule_shift_iso_detTwist`,
  `Proposition5_22_2`) must supply algebraicity of `detTwistedSchurModuleRep`.
* **`h_span` from `h_dim`.** `decompose_polynomial_gl_rep` needs
  `h_span : ⨆ μ, glWeightSpace … = ⊤`. The consumer already proves this
  (`Proposition5_22_2` `h₁_top`), so threading `h_span` through the signature is
  the clean route.
* **Character classification of the abstract simples.** `decompose_polynomial_gl_rep`
  hides the tensor-power decomposition data `(e, he)` that
  `SchurWeylSimplesClassification.glTensorRep_schurWeyl_simples_formalCharacter_linearIndependent`
  consumes. Either `decompose_polynomial_gl_rep` must additionally expose that
  its abstract simples have characters `= schurPoly` of distinct antitone
  partitions, or a bridge lemma to that effect is needed before step 4 applies.
-/

open CategoryTheory MvPolynomial

open scoped TensorProduct

noncomputable section

universe u

namespace Etingof

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- A `GL_N(k)`-representation whose formal character equals a Schur polynomial
`S_λ` and whose dimension matches the Schur module is isomorphic to `L_λ`.

The dimension hypothesis `h_dim` is necessary: without it, one could take
`M = L_λ ⊕ det⁻¹`, which has `formalCharacter M = schurPoly N lam` (since
`det⁻¹` has no `ℕ`-valued weight spaces and is invisible to `formalCharacter`),
yet `M ≇ L_λ` due to the dimension mismatch. The hypothesis ensures `M` is
"polynomial" — its `ℕ`-valued weight spaces account for all of `M`.

The proof requires GL_N-equivariant complete reducibility: every polynomial
`GL_N`-representation decomposes into a direct sum of Schur modules
(`decompose_polynomial_gl_rep`). Combined with the Weyl character formula and the
linear independence of the abstract simple characters
(`SchurWeylSimplesClassification`), this forces `M ≅ L_λ`. See the module
docstring for the remaining proof gaps (issue #4699 deliverable 3).

The downstream use is in `schurModule_shift_iso_detTwist` (Proposition 5.22.2),
where both representations are polynomial and have character equal to
`schurPoly N (λ + 1^N)`. -/
theorem iso_of_formalCharacter_eq_schurPoly (N : ℕ)
    (lam : Fin N → ℕ) (hlam : Antitone lam)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : formalCharacter k N M = schurPoly N lam)
    (h_dim : Module.finrank k M = Module.finrank k (SchurModule k N lam)) :
    Nonempty (M ≅ SchurModule k N lam) := by
  -- Proof outline (see module docstring for the precise remaining gaps):
  -- 1. From h: weight space dims match at every ℕ-valued weight; M is homogeneous
  --    of degree ∑ lam (`weight_magnitude_of_formalCharacter_eq_schurPoly`).
  -- 2. By GL_N-equivariant complete reducibility (`decompose_polynomial_gl_rep`):
  --    M.asModule ≃ ⨁_{j} (L (f j)).asModule for abstract simples L.
  -- 3. Character additivity + linear independence of the abstract simple
  --    characters (#4698): the multiset {f j} is a single class, that of L_λ.
  -- 4. Therefore M ≅ L_λ.
  sorry

end Etingof
