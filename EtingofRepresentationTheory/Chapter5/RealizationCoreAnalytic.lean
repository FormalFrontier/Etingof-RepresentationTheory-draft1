import Mathlib
import EtingofRepresentationTheory.Chapter5.RightTranslationHullDecomp
import EtingofRepresentationTheory.Chapter5.CauchyDetQuotientDegree
import EtingofRepresentationTheory.Chapter5.CauchyDetQuotientGrading
import EtingofRepresentationTheory.Chapter5.CauchyCharacterRightAssembly
import EtingofRepresentationTheory.Chapter5.QuotDetDegreeAlgebraic
import EtingofRepresentationTheory.Chapter5.ConstituentCharacterExtraction
import EtingofRepresentationTheory.Chapter5.SchurWeylFormalCharacterIso
import EtingofRepresentationTheory.Chapter5.SchurModuleContragredientHalf
import EtingofRepresentationTheory.Chapter5.PolynomialWeightSaturation
import EtingofRepresentationTheory.Chapter5.PolynomialGLSemisimple

/-!
# Realization core, analytic half (issue #5606, steps 1–5 of #5602)

`exists_detTwistNeg_schurModule_realization_of_simple`: a simple, finite-dimensional
`localRightRep`-subrepresentation `S` of `R = Localization.Away (detPoly k n)` is, after a
`det^{-r}`-twist, equivariantly isomorphic to a Schur module `SchurModuleSubmodule k n ν`.

The proof follows the route laid out in the parent issue:

1. **Det-clearing.** `S` is finite-dimensional; clearing a common denominator `det^r` embeds the
   `det^r`-twist `M := charTwistRep (det^r) S.toRepresentation` as a `polyRightRep`-invariant
   subspace of the polynomial ring `k[Xᵢⱼ]`, hence `M` is algebraic and its `ℕ`-weight spaces
   span (`exists_detTwist_polyEmbedding_of_simple_subrep`).
2–3. **Single-degree reduction.** `M` is simple, so it embeds `GL_n`-equivariantly into a *single*
   homogeneous degree-`d` Cauchy component `polyRightDegreeFDRep k n d`
   (`exists_polyRightDegree_embedding_of_simple`), whose character is a known nonnegative
   `ℕ`-combination of distinct Schur polynomials (`polyRightDegree_char_as_antitone_sum`).
4. **Character.** Constituent extraction (`simple_constituent_formalCharacter_eq_schurPoly_mem`)
   pins `formalCharacter M = schurPoly n ν` for an antitone `ν`.
5. **Iso.** `simpleRep_iso_schurModule_of_formalCharacter_eq` gives `M ≅ SchurModule k n ν`; we
   untwist by `det^{-r}` (`Intertwines.symm`/`.charTwist`) to deliver the equivariant equivalence.
-/

open scoped TensorProduct

noncomputable section

namespace Etingof

open MvPolynomial Etingof.PolynomialGLAction Etingof.DetLocalization
  Etingof.LocalizationGLAction Etingof.PolyRightGrading Etingof.KernelLemmaKPrime
  Etingof.RightTranslationHull Etingof.CauchyDetQuotient Etingof.CauchyCharacterRight

/-! ### The character of the degree-`d` Cauchy component as an antitone Schur sum -/

/-- **Character of `A_d` as a nonnegative `ℕ`-combination of distinct Schur polynomials indexed by
antitone weights.** This is the exact input shape consumed by
`simple_constituent_formalCharacter_eq_schurPoly_mem`. Translate the Cauchy character identity
`polyRightDegreeFDRep_formalCharacter` (indexed by `BoundedPartition N d`) along the injection
`boundedToAntitone`; the multiplicities `s_ν(1,…,1)` are the nonnegative integers
`schurPoly_eval_one_isNat`. (Mirror of `quotDetDegree_char_as_antitone_sum`, without the
`0 ∈ range` constraint.) -/
theorem polyRightDegree_char_as_antitone_sum
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (N d : ℕ) :
    ∃ (S : Finset {l : Fin N → ℕ // Antitone l}) (c : {l : Fin N → ℕ // Antitone l} → ℕ),
      formalCharacter k N (polyRightDegreeFDRep k N d)
        = ∑ ν ∈ S, (c ν : ℚ) • schurPoly N ν.val := by
  classical
  have hc : ∀ ν : {l : Fin N → ℕ // Antitone l},
      ((schurPoly_eval_one_isNat k ν.val ν.property).choose : ℚ)
        = MvPolynomial.eval (fun _ => (1 : ℚ)) (schurPoly N ν.val) :=
    fun ν => ((schurPoly_eval_one_isNat k ν.val ν.property).choose_spec).symm
  refine ⟨(Finset.univ : Finset (BoundedPartition N d)).image boundedToAntitone,
    fun ν => (schurPoly_eval_one_isNat k ν.val ν.property).choose, ?_⟩
  rw [Etingof.CauchyCharacterRight.polyRightDegreeFDRep_formalCharacter k N d,
    Finset.sum_image (fun x _ y _ h => boundedToAntitone_injective h)]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  have hval : (boundedToAntitone ν).val = ν.parts := rfl
  rw [hc (boundedToAntitone ν), hval]

/-! ### Step 1 — det-clearing: the `det^r`-twist of `S` is a polynomial representation -/

/-- **Det-clearing (issue #5606, step 1).** A finite-dimensional `localRightRep`-subrepresentation
`S` of `R = Localization.Away (detPoly k n)`, after a common-denominator `det^r`-twist, embeds
`GL_n`-equivariantly into the polynomial ring `k[Xᵢⱼ]` (with its right-translation action
`polyRightRep`). Consequently the twist `M := charTwistRep (det^r) S.toRepresentation` is algebraic,
and its `ℕ`-weight spaces span. Mirror of `rightHull_isSemisimple`'s det-clearing, applied to the
subspace `S.toSubmodule` instead of a single element's hull. -/
theorem exists_detTwist_polyEmbedding_of_simple_subrep
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (S : Subrepresentation (localRightRep k n))
    [FiniteDimensional k S.toSubmodule] :
    ∃ r : ℕ,
      Etingof.IsAlgebraicRepresentation n
        ⇑(charTwistRep (detChar k n ^ r) S.toRepresentation) ∧
      (⨆ μ : Fin n →₀ ℕ,
        glWeightSpace k n
          (FDRep.of (charTwistRep (detChar k n ^ r) S.toRepresentation)) (fun i => μ i) = ⊤) ∧
      ∃ φ : S.toSubmodule →ₗ[k] MvPolynomial (Fin n × Fin n) k,
        Function.Injective φ ∧
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : S.toSubmodule),
          φ (charTwistRep (detChar k n ^ r) S.toRepresentation g v) = polyRightRep k n g (φ v) :=
  sorry

/-! ### Steps 2–3 — single-degree reduction for a simple polynomial representation -/

/-- **Single-degree reduction (issue #5606, steps 2–3).** A finite-dimensional *simple*
`GL_N`-representation `L` with a `GL_N`-equivariant injection into the polynomial ring `k[Xᵢⱼ]`
(right-translation action `polyRightRep`) embeds, for some degree `d`, `GL_N`-equivariantly into
the homogeneous degree-`d` Cauchy component `polyRightDegreeFDRep k N d`. The components
`homogeneousComponent d ∘ φ` are equivariant (`homogeneousComponent_polyRightRep`) out of the
simple `L`, hence (Schur) each is zero or injective; since `φ v = ∑_d homogeneousComponent d (φ v)`
is a finite sum and `φ` is injective, some component is injective. Mirror of
`exists_degree_embedding_of_simple` over `A` rather than `A/det`. -/
theorem exists_polyRightDegree_embedding_of_simple
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (φ : L →ₗ[k] MvPolynomial (Fin N × Fin N) k)
    (hφ_inj : Function.Injective φ)
    (hφ_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      φ (L.ρ g v) = polyRightRep k N g (φ v)) :
    ∃ (d : ℕ) (ψ : L →ₗ[k] polyRightDegreeFDRep k N d),
      Function.Injective ψ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
        ψ (L.ρ g v) = (polyRightDegreeFDRep k N d).ρ g (ψ v)) :=
  sorry

/-! ### Assembly -/

/-- **Realization core, analytic half (issue #5606).** See the file docstring. -/
theorem exists_detTwistNeg_schurModule_realization_of_simple
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (S : Subrepresentation (localRightRep k n))
    [FiniteDimensional k S.toSubmodule]
    (hSsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Subrepresentation.asSubmodule S)) :
    ∃ (r : ℕ) (ν : Fin n → ℕ) (_hν : Antitone ν),
      Nonempty { f : SchurModuleSubmodule k n ν ≃ₗ[k] S.toSubmodule //
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : SchurModuleSubmodule k n ν),
          f (charTwistRep (detChar k n ^ (-(r : ℤ))) (schurModuleRep k n ν) g v)
            = S.toRepresentation g (f v) } := by
  classical
  -- `S.asSubmodule` is `S.toRepresentation.asModule`; transport simplicity.
  haveI hSsimp' : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Representation.asModule S.toRepresentation) :=
    Etingof.isSimpleModule_toRepresentation_asModule S hSsimple
  -- Step 1: clear denominators; `M := det^r-twist of S` is algebraic and weight-spanning.
  obtain ⟨r, hMalg, hMtop, φ, hφ_inj, hφ_equiv⟩ :=
    exists_detTwist_polyEmbedding_of_simple_subrep n k S
  -- Package `M` as an `FDRep`.
  set Mrep : Representation k (Matrix.GeneralLinearGroup (Fin n) k) S.toSubmodule :=
    charTwistRep (detChar k n ^ r) S.toRepresentation with hMrep
  set L : FDRep k (Matrix.GeneralLinearGroup (Fin n) k) := FDRep.of Mrep with hL
  -- `L` is simple (a character twist of the simple `S`).
  haveI hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Representation.asModule L.ρ) := by
    have := isSimpleModule_charTwistRep (detChar k n ^ r) S.toRepresentation
    exact this
  -- Step 2–3: embed `L` into a single homogeneous degree-`d` Cauchy component.
  obtain ⟨d, ψ, hψ_inj, hψ_equiv⟩ :=
    exists_polyRightDegree_embedding_of_simple k n L hLsimp φ hφ_inj hφ_equiv
  -- The degree-`d` Cauchy component's character as a distinct Schur sum.
  obtain ⟨Sset, c, hchar⟩ := polyRightDegree_char_as_antitone_sum k n d
  -- Step 4: constituent extraction pins `formalCharacter L = schurPoly n ν`.
  obtain ⟨ν, _hνS, _hcpos, hcharL⟩ :=
    simple_constituent_formalCharacter_eq_schurPoly_mem k n d
      (polyRightDegreeFDRep k n d)
      (Etingof.polyRightDegreeFDRep_isAlgebraic k n d)
      (Etingof.CauchyDetQuotient.polyRight_iSup_glWeightSpace_eq_top d)
      (fun μ hμ => Etingof.CauchyDetQuotient.polyRight_glWeightSpace_homog d μ hμ)
      Sset c hchar L hLsimp ψ hψ_inj hψ_equiv
  -- Step 5: identify `L ≅ SchurModule k n ν`.
  obtain ⟨e⟩ := simpleRep_iso_schurModule_of_formalCharacter_eq k n ν.val ν.property
    L hLsimp hMtop hMalg hcharL
  -- The native-carrier equiv (defeq to the FDRep one — `FDRep.of` carriers reduce) is `f`; split
  -- the subtype's data and property so the equiv term stays syntactic for the intertwining proof.
  refine ⟨r, ν.val, ν.property, ⟨⟨(FDRep.isoToLinearEquiv e).symm, ?_⟩⟩⟩
  intro g v
  -- Untwist: `e` intertwines `Mrep = det^r·S.toRep` with `schurModuleRep`; transpose and
  -- twist by `det^{-r}`.
  -- `e : FDRep.of Mrep ≅ SchurModule k n ν.val = FDRep.of (schurModuleRep k n ν.val)`
  have hInt : Intertwines Mrep (schurModuleRep k n ν.val) (FDRep.isoToLinearEquiv e) :=
    intertwines_of_fdRepIso Mrep (schurModuleRep k n ν.val) e
  have hsymm : Intertwines (schurModuleRep k n ν.val) Mrep (FDRep.isoToLinearEquiv e).symm :=
    hInt.symm
  have htw := hsymm.charTwist (detChar k n ^ r)⁻¹
  -- Undo the double twist on `S`, then rewrite the twisting character `(det^r)⁻¹ = det^{-r}`.
  have hchar_inv : ((detChar k n ^ r)⁻¹ : Matrix.GeneralLinearGroup (Fin n) k →* kˣ)
      = detChar k n ^ (-(r : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
  have huntwist : charTwistRep (detChar k n ^ r)⁻¹ Mrep = S.toRepresentation := by
    rw [hMrep]
    ext g' x
    rw [charTwistRep_apply, charTwistRep_apply, smul_smul, ← Units.val_mul,
      ← MonoidHom.mul_apply, inv_mul_cancel, MonoidHom.one_apply, Units.val_one, one_smul]
  rw [huntwist, hchar_inv] at htw
  exact htw g v

end Etingof
