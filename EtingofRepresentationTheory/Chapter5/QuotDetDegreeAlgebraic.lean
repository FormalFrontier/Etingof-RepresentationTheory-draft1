import EtingofRepresentationTheory.Chapter5.GLRepAlgebraic
import EtingofRepresentationTheory.Chapter5.CauchyDetQuotientDegree
import EtingofRepresentationTheory.Chapter5.CauchyWeightSpaceDimension

/-!
# Algebraicity of the determinant-quotient degree component `quotDetDegreeFDRep`

The final assembly of #4905
(`quotDetRep_irreducible_constituent_lastWeight_zero`) feeds the degree-`d`
component `(A/det)_d = quotDetDegreeFDRep k N d` into the part-C ingredient
`Etingof.simple_constituent_formalCharacter_eq_schurPoly_mem`, which requires the
hypothesis `Etingof.IsAlgebraicRepresentation N M.ρ`. This file supplies that
hypothesis for `quotDetDegreeFDRep`.

The route has three steps:

* `IsAlgebraicRepresentation.of_surjective_equivariant` — a general transport
  lemma: algebraicity passes along a **surjective** `GL_N`-equivariant `k`-linear
  map onto a finite-dimensional target. (The dual of
  `IsAlgebraicRepresentation.restrict`, which handles invariant *sub*modules.)
* `polyRightDegreeFDRep_isAlgebraic` — the degree-`d` component `A_d` of the
  coordinate ring under right translation is algebraic. On the monomial basis the
  right translation `R_g X_{ij} = ∑_l g_{lj} X_{il}` has matrix coefficients that
  are polynomials in the entries of `g`.
* `quotDetDegreeFDRep_isAlgebraic` — combine the two via the surjective
  equivariant quotient map `A_d → (A/det)_d`.
-/

open scoped TensorProduct
open MvPolynomial Matrix

noncomputable section

namespace Etingof

/-! ### Algebraicity transfers along a surjective equivariant map -/

/-- **Algebraicity transfers along a surjective intertwining `k`-linear map.** If
`ρ` is an algebraic `GL_N(k)`-representation on `Y` and `π : Y → Z` is a surjective
`k`-linear map onto a finite-dimensional `Z` intertwining `ρ` with `σ`
(`π (ρ g y) = σ g (π y)`), then `σ` is algebraic.

Choosing a `k`-linear section `s : Z → Y` of `π`, a basis `b'` of `Z`, and the
algebraicity basis `B` of `Y`, the new matrix coefficient `b'.repr (σ g (b' c)) a`
expands as a `k`-linear combination of `evalAtGL g (P e d)` with constant
coefficients from `B.repr (s (b' c))` and `b'.repr (π (B e))`. This mirrors
`IsAlgebraicRepresentation.restrict`, with the invariant-submodule inclusion
replaced by the section `s` and the projection replaced by `π`. -/
theorem IsAlgebraicRepresentation.of_surjective_equivariant {k : Type*} [Field k] {N : ℕ}
    {Y Z : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    [AddCommGroup Z] [Module k Z] [Module.Finite k Z]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    {σ : Matrix.GeneralLinearGroup (Fin N) k → Z →ₗ[k] Z}
    (π : Y →ₗ[k] Z) (hπ_surj : Function.Surjective π)
    (hcomm : ∀ g y, π (ρ g y) = σ g (π y))
    (h : Etingof.IsAlgebraicRepresentation N ρ) :
    Etingof.IsAlgebraicRepresentation N σ := by
  classical
  obtain ⟨M, B, P, hP⟩ := h
  -- Basis of the target, indexed by `Fin (finrank k Z)`.
  let b' : Module.Basis (Fin (Module.finrank k Z)) k Z := Module.finBasis k Z
  -- A `k`-linear section `s : Z → Y` of `π`.
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ_surj)
  have hsec : ∀ z, π (s z) = z := fun z => by
    have := LinearMap.congr_fun hs z; simpa using this
  refine ⟨Module.finrank k Z, b',
    fun a c => ∑ d, ∑ e,
      MvPolynomial.C (B.repr (s (b' c)) d) * P e d
        * MvPolynomial.C (b'.repr (π (B e)) a), fun g a c => ?_⟩
  -- `φ y = b'.repr (π y) a`, a linear functional `Y → k`.
  let φ : Y →ₗ[k] k := (Finsupp.lapply a).comp (b'.repr.toLinearMap.comp π)
  have hφ_apply : ∀ y, φ y = b'.repr (π y) a := fun _ => rfl
  -- `σ g (b' c) = π (ρ g (s (b' c)))`, from equivariance and the section property.
  have hkey : π (ρ g (s (b' c))) = σ g (b' c) := by rw [hcomm, hsec]
  -- Reduce the LHS coefficient to a double sum over the algebraicity basis `B`.
  have hlhs : b'.repr (σ g (b' c)) a
      = ∑ d, ∑ e, B.repr (s (b' c)) d
          * (Etingof.evalAtGL g (P e d) * b'.repr (π (B e)) a) := by
    rw [show b'.repr (σ g (b' c)) a = φ (ρ g (s (b' c))) from by rw [hφ_apply, hkey]]
    -- expand `s (b' c)` in the algebraicity basis `B`
    rw [show ρ g (s (b' c))
        = ∑ d, B.repr (s (b' c)) d • ρ g (B d) from by
      conv_lhs => rw [show s (b' c) = ∑ d, B.repr (s (b' c)) d • B d from
        (B.sum_repr (s (b' c))).symm]
      rw [map_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [map_smul]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smul, smul_eq_mul]
    -- compute `φ (ρ g (B d))` by expanding `ρ g (B d)` in `B`
    have hd : φ (ρ g (B d))
        = ∑ e, Etingof.evalAtGL g (P e d) * b'.repr (π (B e)) a := by
      conv_lhs => rw [show ρ g (B d) = ∑ e, B.repr (ρ g (B d)) e • B e from
        (B.sum_repr (ρ g (B d))).symm]
      rw [map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, smul_eq_mul, hP g e d, hφ_apply]
    rw [hd, Finset.mul_sum]
  rw [hlhs, evalAtGL_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [evalAtGL_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [evalAtGL_mul, evalAtGL_mul, evalAtGL_C, evalAtGL_C]
  ring

end Etingof
