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

/-- **Parameterised det-clearing (issue #5606, step 1).** For any exponent `r` clearing every
denominator of a basis `B` of the finite-dimensional carrier, the `det^r`-twist
`M := charTwistRep (det^r) S.toRepresentation` is algebraic and embeds `GL_n`-equivariantly into the
polynomial ring `k[Xᵢⱼ]` (with its right-translation action `polyRightRep`). Mirror of
`rightHull_isSemisimple`'s det-clearing, applied to the subspace `S.toSubmodule` instead of a single
element's hull. -/
theorem detTwist_clearing
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (S : Subrepresentation (localRightRep k n))
    [FiniteDimensional k S.toSubmodule]
    {m : ℕ} (B : Module.Basis (Fin m) k S.toSubmodule) (r : ℕ)
    (hr_ge : ∀ i, detExp ((S.toSubmodule.subtype (B i)) : Localization.Away (detPoly k n)) ≤ r) :
      Etingof.IsAlgebraicRepresentation n
        ⇑(charTwistRep (detChar k n ^ r) S.toRepresentation) ∧
      ∃ φ : S.toSubmodule →ₗ[k] MvPolynomial (Fin n × Fin n) k,
        Function.Injective φ ∧
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : S.toSubmodule),
          φ (charTwistRep (detChar k n ^ r) S.toRepresentation g v) = polyRightRep k n g (φ v) := by
  classical
  -- Clearing: each basis vector is `det^{-r}` times an explicit polynomial.
  have hclear : ∀ i, ∃ P : MvPolynomial (Fin n × Fin n) k,
      (S.toSubmodule.subtype (B i) : Localization.Away (detPoly k n)) = numEmbed r P := by
    intro i
    obtain ⟨Q, hQ⟩ :=
      detExp_spec (S.toSubmodule.subtype (B i) : Localization.Away (detPoly k n))
    refine ⟨Q * detPoly k n ^ (r - detExp (S.toSubmodule.subtype (B i))), ?_⟩
    conv_lhs => rw [hQ]
    rw [numEmbed_apply, map_mul, map_pow, mul_assoc]
    congr 1
    -- `invSelf^e = algebraMap(detPoly)^(r - e) * invSelf^r`, where `e = detExp ↑(B i) ≤ r`.
    rw [show (IsLocalization.Away.invSelf (detPoly k n) : Localization.Away (detPoly k n)) ^ r
          = IsLocalization.Away.invSelf (detPoly k n)
              ^ (r - detExp (S.toSubmodule.subtype (B i)))
            * IsLocalization.Away.invSelf (detPoly k n)
              ^ (detExp (S.toSubmodule.subtype (B i))) from by
        rw [← pow_add, Nat.sub_add_cancel (hr_ge i)],
      ← mul_assoc, algebraMap_detPoly_pow_mul_invSelf_pow, one_mul]
  choose P hP using hclear
  -- Degree bound for the cleared numerators.
  set d : ℕ := Finset.univ.sup (fun i => (P i).totalDegree) with hd
  -- The numerator embedding restricted to bounded-degree polynomials, landing in `R`.
  set ι : (boundedSubrep k n d).toSubmodule →ₗ[k] Localization.Away (detPoly k n) :=
    (numEmbed r).comp (boundedSubrep k n d).toSubmodule.subtype with hι
  have hι_apply : ∀ w : (boundedSubrep k n d).toSubmodule,
      ι w = numEmbed r (w : MvPolynomial (Fin n × Fin n) k) := fun _ => rfl
  have hι_inj : Function.Injective ι :=
    (numEmbed_injective r).comp (Submodule.injective_subtype _)
  -- `ι` intertwines bounded right translation with the `det^r`-twisted localization action.
  have hinter : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (w : (boundedSubrep k n d).toSubmodule),
      ι ((boundedSubrep k n d).toRepresentation g w)
        = charTwistRep (detChar k n ^ r) (localRightRep k n) g (ι w) := by
    intro g w
    rw [hι_apply, boundedSubrep_toRepresentation_coe, hι_apply, numEmbed_intertwines]
  -- `S.toSubmodule` lies in the image of `ι` (clearing the basis).
  have hIII : S.toSubmodule ≤ LinearMap.range ι := by
    have hspan : S.toSubmodule
        = Submodule.span k (Set.range (fun i =>
            (S.toSubmodule.subtype (B i) : Localization.Away (detPoly k n)))) := by
      conv_lhs => rw [← Submodule.map_subtype_top S.toSubmodule, ← B.span_eq,
        Submodule.map_span]
      rw [← Set.range_comp]
      rfl
    rw [hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    refine ⟨⟨P i, ?_⟩, ?_⟩
    · show P i ∈ (boundedSubrep k n d).toSubmodule
      exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
        (Finset.le_sup (f := fun i => (P i).totalDegree) (Finset.mem_univ i))
    · rw [hι_apply]; exact (hP i).symm
  -- The preimage subspace, invariant under bounded right translation.
  set U : Submodule k (boundedSubrep k n d).toSubmodule :=
    Submodule.comap ι S.toSubmodule with hU
  have hU_inv : ∀ g, ∀ v ∈ U, (boundedSubrep k n d).toRepresentation g v ∈ U := by
    intro g v hv
    rw [hU, Submodule.mem_comap] at hv ⊢
    rw [hinter, charTwistRep_apply]
    exact Submodule.smul_mem _ _ (S.apply_mem_toSubmodule g hv)
  haveI : Module.Finite k U := inferInstance
  -- `ι` carries `U` isomorphically onto `S.toSubmodule`.
  have hmap : U.map ι = S.toSubmodule := by
    rw [hU, Submodule.map_comap_eq, inf_eq_right.mpr hIII]
  let e : U ≃ₗ[k] S.toSubmodule :=
    (Submodule.equivMapOfInjective ι hι_inj U).trans (LinearEquiv.ofEq _ _ hmap)
  have he_coe : ∀ y : U,
      (e y : Localization.Away (detPoly k n)) = ι (y : (boundedSubrep k n d).toSubmodule) := by
    intro y
    show ((LinearEquiv.ofEq _ _ hmap) (Submodule.equivMapOfInjective ι hι_inj U y) :
        Localization.Away (detPoly k n)) = _
    rw [LinearEquiv.coe_ofEq_apply, Submodule.coe_equivMapOfInjective_apply]
  have hS_coe : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (z : S.toSubmodule),
      ((S.toRepresentation g z : Localization.Away (detPoly k n)))
        = localRightRep k n g (z : Localization.Away (detPoly k n)) :=
    fun g z => LinearMap.restrict_coe_apply (localRightRep k n g)
      (S.apply_mem_toSubmodule g) z
  -- `e` intertwines the restricted bounded action with the `det^r`-twisted `S`-action.
  have hcomm : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (y : U),
      e (((boundedSubrep k n d).toRepresentation g).restrict (hU_inv g) y)
        = charTwistRep (detChar k n ^ r) S.toRepresentation g (e y) := by
    intro g y
    apply Subtype.ext
    have hL : (↑(e (((boundedSubrep k n d).toRepresentation g).restrict (hU_inv g) y)) :
        Localization.Away (detPoly k n))
        = charTwistRep (detChar k n ^ r) (localRightRep k n) g (ι (y : _)) := by
      rw [he_coe, LinearMap.restrict_coe_apply, hinter]
    have hR : (↑(charTwistRep (detChar k n ^ r) S.toRepresentation g (e y)) :
        Localization.Away (detPoly k n))
        = charTwistRep (detChar k n ^ r) (localRightRep k n) g (ι (y : _)) := by
      rw [charTwistRep_apply, Submodule.coe_smul, hS_coe, he_coe, charTwistRep_apply]
    rw [hL, hR]
  -- The twisted `S`-action is algebraic.
  have hMalg : Etingof.IsAlgebraicRepresentation n
      ⇑(charTwistRep (detChar k n ^ r) S.toRepresentation) :=
    ((boundedRightRep_isAlgebraic k n d).restrict U hU_inv).of_linearEquiv e hcomm
  -- The polynomial embedding `φ = subtype ∘ U.subtype ∘ e.symm`.
  refine ⟨hMalg,
    (boundedSubrep k n d).toSubmodule.subtype ∘ₗ U.subtype ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
  · -- injectivity
    exact (Submodule.injective_subtype _).comp
      ((Submodule.injective_subtype U).comp e.symm.injective)
  · -- equivariance
    intro g v
    show (boundedSubrep k n d).toSubmodule.subtype (U.subtype (e.symm
        (charTwistRep (detChar k n ^ r) S.toRepresentation g v)))
      = polyRightRep k n g ((boundedSubrep k n d).toSubmodule.subtype (U.subtype (e.symm v)))
    have hsymm : e.symm (charTwistRep (detChar k n ^ r) S.toRepresentation g v)
        = ((boundedSubrep k n d).toRepresentation g).restrict (hU_inv g) (e.symm v) := by
      apply e.injective
      rw [e.apply_symm_apply, hcomm, e.apply_symm_apply]
    rw [hsymm,
      show U.subtype ((((boundedSubrep k n d).toRepresentation g).restrict (hU_inv g)) (e.symm v))
          = (boundedSubrep k n d).toRepresentation g (U.subtype (e.symm v)) from
        LinearMap.restrict_coe_apply _ (hU_inv g) (e.symm v)]
    exact boundedSubrep_toRepresentation_coe d g (U.subtype (e.symm v))

/-- **Det-clearing into a polynomial representation (issue #5606, step 1).** A finite-dimensional
`localRightRep`-subrepresentation `S` of `R = Localization.Away (detPoly k n)`, after a
common-denominator `det^r`-twist with `r` chosen large enough, is a genuine **polynomial**
representation: it is algebraic, its `ℕ`-weight spaces span, and it embeds `GL_n`-equivariantly into
`k[Xᵢⱼ]`. The clearing exponent is taken `r = r₀ + s`, where `r₀` clears the basis denominators and
`s` (from `IsAlgebraicRepresentation.exists_detPow_twist_isPolynomial`) makes the twist det⁻¹-free;
weight-spanning then follows from `polynomial_rep_iSup_glWeightSpace_eq_top`. -/
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
          φ (charTwistRep (detChar k n ^ r) S.toRepresentation g v) = polyRightRep k n g (φ v) := by
  classical
  haveI : Module.Finite k S.toSubmodule := ‹FiniteDimensional k S.toSubmodule›
  let B : Module.Basis (Fin (Module.finrank k S.toSubmodule)) k S.toSubmodule :=
    Module.finBasis k S.toSubmodule
  -- The basis-clearing exponent `r₀`.
  set r₀ : ℕ := Finset.univ.sup
    (fun i => detExp ((S.toSubmodule.subtype (B i)) : Localization.Away (detPoly k n))) with hr₀def
  have hr₀ : ∀ i, detExp ((S.toSubmodule.subtype (B i)) : Localization.Away (detPoly k n)) ≤ r₀ :=
    fun i => Finset.le_sup
      (f := fun i => detExp ((S.toSubmodule.subtype (B i)) : Localization.Away (detPoly k n)))
      (Finset.mem_univ i)
  -- Algebraicity of the `det^{r₀}`-twist, then a polynomial exponent `s` on top of it.
  obtain ⟨hMalg₀, -⟩ := detTwist_clearing n k S B r₀ hr₀
  obtain ⟨s, hPoly₀⟩ := hMalg₀.exists_detPow_twist_isPolynomial
  -- Clear at the *polynomial* exponent `r := r₀ + s`.
  have hr : ∀ i, detExp ((S.toSubmodule.subtype (B i)) : Localization.Away (detPoly k n)) ≤ r₀ + s :=
    fun i => le_trans (hr₀ i) (Nat.le_add_right r₀ s)
  obtain ⟨hMalg, φ, hφ_inj, hφ_equiv⟩ := detTwist_clearing n k S B (r₀ + s) hr
  refine ⟨r₀ + s, hMalg, ?_, φ, hφ_inj, hφ_equiv⟩
  -- The `det^{r₀+s}`-twist is `det^s • (det^{r₀}·S)`, hence polynomial, hence weight-spanning.
  have hfun : (fun g => (Matrix.GeneralLinearGroup.det g : k) ^ s •
        (charTwistRep (detChar k n ^ r₀) S.toRepresentation) g)
      = ⇑(charTwistRep (detChar k n ^ (r₀ + s)) S.toRepresentation) := by
    funext g
    ext x
    rw [LinearMap.smul_apply, charTwistRep_apply, charTwistRep_apply, smul_smul]
    congr 1
    have hd : (Matrix.GeneralLinearGroup.det g : k) = (detChar k n g : k) := rfl
    rw [hd, MonoidHom.pow_apply, MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, pow_add]
    ring
  have hPoly : IsPolynomialRepresentation n
      ⇑(charTwistRep (detChar k n ^ (r₀ + s)) S.toRepresentation) := hfun ▸ hPoly₀
  exact polynomial_rep_iSup_glWeightSpace_eq_top
    (FDRep.of (charTwistRep (detChar k n ^ (r₀ + s)) S.toRepresentation)) hPoly

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
        ψ (L.ρ g v) = (polyRightDegreeFDRep k N d).ρ g (ψ v)) := by
  classical
  haveI := hLsimp
  -- For each degree `d`, the equivariant map `ψ d : L → A_d`, namely `homogeneousComponent d ∘ φ`.
  let ψ : ∀ d, L →ₗ[k] polyRightDegreeFDRep k N d := fun d =>
    LinearMap.codRestrict (polyRightHomogeneousSubrep k N d).toSubmodule
      ((MvPolynomial.homogeneousComponent d).comp φ)
      (fun v => MvPolynomial.homogeneousComponent_mem d (φ v))
  -- carrier value of `ψ d`
  have hψ_val : ∀ d (v : L),
      (polyRightHomogeneousSubrep k N d).toSubmodule.subtype (ψ d v)
        = MvPolynomial.homogeneousComponent d (φ v) := fun _ _ => rfl
  -- the carrier action of `polyRightDegreeFDRep` is `polyRightRep`
  have hρ_coe : ∀ d (g : Matrix.GeneralLinearGroup (Fin N) k)
      (z : polyRightDegreeFDRep k N d),
      (polyRightHomogeneousSubrep k N d).toSubmodule.subtype ((polyRightDegreeFDRep k N d).ρ g z)
        = polyRightRep k N g ((polyRightHomogeneousSubrep k N d).toSubmodule.subtype z) :=
    fun d g z => LinearMap.restrict_coe_apply (polyRightRep k N g)
      ((polyRightHomogeneousSubrep k N d).apply_mem_toSubmodule g) z
  -- equivariance of `ψ d`
  have hψ_equiv : ∀ d (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      ψ d (L.ρ g v) = (polyRightDegreeFDRep k N d).ρ g (ψ d v) := by
    intro d g v
    apply Submodule.injective_subtype (polyRightHomogeneousSubrep k N d).toSubmodule
    rw [hψ_val, hρ_coe, hψ_val, hφ_equiv, homogeneousComponent_polyRightRep]
  -- Schur: each `ψ d` is zero or injective
  have hschur : ∀ d, Function.Injective (ψ d) ∨ ψ d = 0 := by
    intro d
    let Ψ : Representation.asModule L.ρ
        →ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
          Representation.asModule (polyRightDegreeFDRep k N d).ρ :=
      Representation.asModuleHomOfIntertwiner (ψ d) (hψ_equiv d)
    rcases eq_bot_or_eq_top (LinearMap.ker Ψ) with hker | hker
    · exact Or.inl fun a b h => LinearMap.ker_eq_bot.1 hker h
    · refine Or.inr ?_
      have hΨ0 : Ψ = 0 := LinearMap.ker_eq_top.1 hker
      ext v
      change Ψ v = 0
      rw [hΨ0, LinearMap.zero_apply]
  -- some `ψ d` is injective
  haveI : Nontrivial L :=
    IsSimpleModule.nontrivial (R := MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (M := Representation.asModule L.ρ)
  obtain ⟨v, hv0⟩ := exists_ne (0 : L)
  have hexists : ∃ d, Function.Injective (ψ d) := by
    by_contra hcon
    push_neg at hcon
    have hzero : ∀ d, ψ d = 0 := fun d => (hschur d).resolve_left (hcon d)
    -- `φ v = ∑_d homogeneousComponent d (φ v)`, but every component vanishes
    have hdecomp : (∑ d ∈ Finset.range ((φ v).totalDegree + 1),
        MvPolynomial.homogeneousComponent d (φ v)) = φ v :=
      MvPolynomial.sum_homogeneousComponent (φ v)
    have hzeroterm : ∀ d, MvPolynomial.homogeneousComponent d (φ v) = 0 := by
      intro d
      rw [← hψ_val d v, hzero d, LinearMap.zero_apply]
      rfl
    have hφv0 : φ v = 0 := by
      rw [← hdecomp]; exact Finset.sum_eq_zero fun d _ => hzeroterm d
    exact hv0 (hφ_inj (by rw [hφv0, map_zero]))
  obtain ⟨d, hd⟩ := hexists
  exact ⟨d, ψ d, hd, hψ_equiv d⟩

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
