import Mathlib
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLRep
import EtingofRepresentationTheory.Chapter5.Proposition5_22_2
import EtingofRepresentationTheory.Chapter5.FormalCharacterIso
import EtingofRepresentationTheory.Chapter5.RepresentationAsModuleHom

/-!
# Pairwise non-isomorphism of the irreducibles `L_λ` for distinct dominant weights

For distinct dominant weights `λ ≠ μ`, the irreducible algebraic representations
`L_λ = algIrrepGLRepρ n λ k` and `L_μ` are non-isomorphic as `k[GL_n]`-modules. This
is the distinguishing-invariant input (the highest-weight / formal-character
classification) to the cross-summand orthogonality
`peterWeylSummandMap_range_iSupIndep` (issue #5556).

## Proof route (for `algIrrepGLRepρ_noniso`, currently the sole `sorry`)

A `k[GL_n]`-module isomorphism `e : L_λ.asModule ≃ₗ L_μ.asModule` restricts to a
`GL_n`-equivariant `k`-linear equivalence `f : AlgIrrepGL n λ k ≃ₗ[k] AlgIrrepGL n μ k`
(via `Representation.asModuleEquiv` and `Representation.asModuleEquiv_symm_map_rho`,
the reverse of `asModuleEquivOfIntertwiner` in `RepresentationAsModuleHom.lean`).

The same `f` intertwines the `det^M`-twists for any `M`, since
`charTwistRep c ρ g = c g • ρ g`. Choose `M = λ.shift + μ.shift` (so `M ≥ λ.shift, μ.shift`).
Using `charTwistRep_charTwistRep` (`ContragredientIdentity.lean`) and
`detChar^M * detChar^{-λ.shift} = detChar^{M - λ.shift}`,

  `charTwistRep (detChar^M) L_λ = charTwistRep (detChar^{M-λ.shift}) (schurModuleRep a)`
  (where `a = λ.toNatWeight`; an honest polynomial Schur-module twist),

an honest *polynomial* Schur module twist. Its formal character is
`schurPoly (λ.toNatWeight + (M - λ.shift)·1) = schurPoly (fun i => λ.val i + M)`
(determinant twist multiplies the character by `(∏ Xᵢ)^{M-λ.shift}`, i.e. iterates
`formalCharacter_schurModule_shift` / `schurPoly_shift`; the `p`-fold version of
`formalCharacter_detTwist_eq_shift`).

`formalCharacter_eq_of_rep_iso` applied to `f` (twisted) gives
`schurPoly (λ.val + M) = schurPoly (μ.val + M)` (both antitone, non-negative). Then
`schurPoly_injective` forces `λ.val i + M = μ.val i + M`, hence `λ.val = μ.val`, i.e.
`λ = μ`.

The genuine new ingredient is the `p`-fold determinant-twist character formula
`formalCharacter (charTwistRep (detChar^p) (schurModuleRep w)) = schurPoly (w + p·1)`
(`p : ℕ`), provable by induction on `p` from the existing `p = 1` results
(`formalCharacter_detTwist_eq_shift`, `glWeightSpace_detTwist_shift`) generalized from
`detTwistedSchurModuleRep` to an arbitrary representation, plus the determinant-twist
weight-space shift. Tracked as a sub-issue of #5556.
-/

open scoped TensorProduct

noncomputable section

namespace Etingof

/-- **Distinct dominant weights give non-isomorphic `L_λ`.** For `λ ≠ μ`,
`algIrrepGLRepρ n λ k` and `algIrrepGLRepρ n μ k` are non-isomorphic as
`k[GL_n]`-modules (the highest-weight / formal-character classification). The
distinguishing invariant is the Schur-polynomial formal character of a common
determinant twist; see the module docstring for the full route. -/
theorem algIrrepGLRepρ_noniso (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {lam mu : DominantWeight n} (hne : lam ≠ mu) :
    ¬ Nonempty ((algIrrepGLRepρ n lam k).asModule ≃ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin n) k)] (algIrrepGLRepρ n mu k).asModule) := by
  sorry

end Etingof
