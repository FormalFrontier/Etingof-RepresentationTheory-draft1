import EtingofRepresentationTheory.Chapter5.CleanFormalCharacterAdditivity
import EtingofRepresentationTheory.Chapter5.GLRepAlgebraic

/-!
# Induction helpers for the DetInvElim-clean constituent-character extractor

This file provides two of the three induction helpers needed by the clean
constituent-character extractor (`clean_simple_constituent_formalCharacter_eq_schurPoly_mem`,
issue #5082, parent #5081). The third — *sub-of-spanning-is-spanning* — is the technical
crux and is developed separately (#5086).

The extractor proves `char M = ∑ (composition-factor characters)` by a `finrank` induction
that peels a simple `GL_N`-submodule `S ≤ M` off at each step and uses the short-exact-sequence
additivity `Etingof.CleanCharExtraction.formalCharacter_add_of_shortExact`. To run that
induction it needs, for an invariant submodule `S = σ.toSubmodule ≤ M`:

* the quotient `M ⧸ S` carried as a `GL_N`-representation that is **still algebraic** (so the
  induction hypothesis applies to it) — `IsAlgebraicRepresentation.quotient`;
* the packaging of `S ↪ M ↠ M ⧸ S` as an equivariant short exact sequence of `FDRep`s, so that
  `formalCharacter_add_of_shortExact` applies directly — `subFDRep`, `quotientFDRep`, the
  equivariant inclusion/projection, exactness, and the capstone
  `formalCharacter_eq_sub_add_quotient`.

Everything here imports only DetInvElim-clean files, so it introduces no build cycle with
`CauchyDetQuotient`.
-/

noncomputable section

open MvPolynomial
open scoped MonoidAlgebra

namespace Etingof

/-! ## Deliverable 2: the quotient of an algebraic representation is algebraic -/

/-- **The quotient of an algebraic representation is algebraic.** Given an algebraic
representation `ρ` on `Y` and an invariant submodule `K` (`K ≤ K.comap (ρ g)` for every `g`),
the induced action `g ↦ Submodule.mapQ K K (ρ g)` on `Y ⧸ K` is algebraic.

The proof mirrors `Etingof.IsAlgebraicRepresentation.restrict`: choose a complement `K'` of `K`,
which provides a linear *section* `s : Y ⧸ K → Y` of the quotient map `q = K.mkQ`
(`q ∘ s = id`); the quotient matrix coefficients are then the sub-block
`∑_{d,e} (B.repr (s (b' c)) d) · P e d · (b'.repr (q (B e)) a)` of the ambient polynomial
coefficients `P`, hence polynomial. -/
theorem IsAlgebraicRepresentation.quotient {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    (h : Etingof.IsAlgebraicRepresentation N ρ)
    (K : Submodule k Y) (hK : ∀ g, K ≤ K.comap (ρ g)) :
    Etingof.IsAlgebraicRepresentation N (fun g => Submodule.mapQ K K (ρ g) (hK g)) := by
  classical
  haveI : Module.Finite k (Y ⧸ K) := Module.Finite.of_surjective K.mkQ K.mkQ_surjective
  obtain ⟨M, B, P, hP⟩ := h
  -- Basis of the quotient, indexed by `Fin (finrank k (Y ⧸ K))`.
  let b' : Module.Basis (Fin (Module.finrank k (Y ⧸ K))) k (Y ⧸ K) := Module.finBasis k (Y ⧸ K)
  -- A linear section `s : Y ⧸ K → Y` of `K.mkQ`, obtained from a complement of `K`.
  obtain ⟨K', hK'⟩ := K.exists_isCompl
  let e := Submodule.quotientEquivOfIsCompl K K' hK'
  let s : (Y ⧸ K) →ₗ[k] Y := K'.subtype ∘ₗ (e : (Y ⧸ K) →ₗ[k] K')
  have hsec : ∀ x : Y ⧸ K, K.mkQ (s x) = x := by
    intro x
    rw [Submodule.mkQ_apply]
    -- v4.30: the submodules are now implicit (inferred from the `IsCompl` proof).
    exact Submodule.mk_quotientEquivOfIsCompl_apply hK' x
  refine ⟨Module.finrank k (Y ⧸ K), b',
    fun a c => ∑ d, ∑ e,
      MvPolynomial.C (B.repr (s (b' c)) d) * P e d
        * MvPolynomial.C (b'.repr (K.mkQ (B e)) a), fun g a c => ?_⟩
  -- `φ y = b'.repr (K.mkQ y) a`, a linear functional `Y → k`.
  let φ : Y →ₗ[k] k := (Finsupp.lapply a).comp (b'.repr.toLinearMap.comp K.mkQ)
  have hφ_apply : ∀ y, φ y = b'.repr (K.mkQ y) a := fun _ => rfl
  -- The quotient action on `b' c` is `K.mkQ (ρ g (s (b' c)))`.
  have h1 : Submodule.mapQ K K (ρ g) (hK g) (b' c) = K.mkQ (ρ g (s (b' c))) := by
    conv_lhs => rw [← hsec (b' c)]
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, ← Submodule.mkQ_apply]
  -- Reduce the LHS coefficient to a double sum over the ambient basis.
  have hlhs : b'.repr (Submodule.mapQ K K (ρ g) (hK g) (b' c)) a
      = ∑ d, ∑ e, B.repr (s (b' c)) d
          * (Etingof.evalAtGL g (P e d) * b'.repr (K.mkQ (B e)) a) := by
    rw [show b'.repr (Submodule.mapQ K K (ρ g) (hK g) (b' c)) a = φ (ρ g (s (b' c))) from by
      rw [hφ_apply, h1]]
    -- expand `s (b' c)` in the ambient basis `B`
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
        = ∑ e, Etingof.evalAtGL g (P e d) * b'.repr (K.mkQ (B e)) a := by
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

/-! ## Deliverable 3: sub/quotient FDReps and the short-exact-sequence glue -/

namespace CleanCharExtraction

variable {k : Type*} [Field k] {N : ℕ}

/-- The sub-`FDRep` carried by a subrepresentation `σ` of an `FDRep` `M`: the restriction of
`M`'s action to the invariant submodule `σ.toSubmodule`. -/
noncomputable def subFDRep (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) : FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  haveI : Module.Finite k σ.toSubmodule := inferInstance
  FDRep.of σ.toRepresentation

/-- The quotient `FDRep` `M ⧸ σ`: the action induced by `M.ρ` on `M ⧸ σ.toSubmodule`. -/
noncomputable def quotientFDRep (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) : FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  haveI : Module.Finite k (M ⧸ σ.toSubmodule) :=
    Module.Finite.of_surjective σ.toSubmodule.mkQ σ.toSubmodule.mkQ_surjective
  FDRep.of (Representation.quotient M.ρ σ.toSubmodule (fun g => σ.apply_mem_toSubmodule g))

/-- The equivariant inclusion `subFDRep M σ → M`. -/
theorem subFDRep_subtype_equivariant (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (v : subFDRep M σ) :
    σ.toSubmodule.subtype ((subFDRep M σ).ρ g v) = M.ρ g (σ.toSubmodule.subtype v) := rfl

/-- The inclusion `subFDRep M σ → M` is injective. -/
theorem subFDRep_subtype_injective (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) :
    Function.Injective (σ.toSubmodule.subtype : subFDRep M σ →ₗ[k] M) :=
  Subtype.val_injective

/-- The equivariant projection `M → quotientFDRep M σ`. -/
theorem quotientFDRep_mkQ_equivariant (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) (g : Matrix.GeneralLinearGroup (Fin N) k) (v : M) :
    σ.toSubmodule.mkQ (M.ρ g v) = (quotientFDRep M σ).ρ g (σ.toSubmodule.mkQ v) := rfl

/-- The projection `M → quotientFDRep M σ` is surjective. -/
theorem quotientFDRep_mkQ_surjective (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) :
    Function.Surjective (σ.toSubmodule.mkQ : M →ₗ[k] quotientFDRep M σ) :=
  σ.toSubmodule.mkQ_surjective

/-- **Exactness at `M`.** The range of the inclusion `subFDRep M σ → M` equals the kernel of the
projection `M → quotientFDRep M σ`; both are `σ.toSubmodule`. -/
theorem subFDRep_range_eq_quotientFDRep_ker
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (σ : Subrepresentation M.ρ) :
    LinearMap.range (σ.toSubmodule.subtype : subFDRep M σ →ₗ[k] M)
      = LinearMap.ker (σ.toSubmodule.mkQ : M →ₗ[k] quotientFDRep M σ) := by
  rw [Submodule.range_subtype, Submodule.ker_mkQ]

/-- **The quotient `FDRep` is algebraic when `M` is.** Specializes
`IsAlgebraicRepresentation.quotient` to the quotient `FDRep`. -/
theorem quotientFDRep_isAlgebraic (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) (hM : Etingof.IsAlgebraicRepresentation N M.ρ) :
    Etingof.IsAlgebraicRepresentation N (quotientFDRep M σ).ρ :=
  hM.quotient σ.toSubmodule (fun g => σ.apply_mem_toSubmodule g)

/-- **Weight saturation passes to the quotient.** If the `ℕ`-weight spaces of `M` span `M`,
those of `quotientFDRep M σ` span it too (the projection is an equivariant surjection). -/
theorem quotientFDRep_iSup_glWeightSpace_eq_top [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (σ : Subrepresentation M.ρ)
    (hM : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N M (fun i => μ i) = ⊤) :
    ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (quotientFDRep M σ) (fun i => μ i) = ⊤ :=
  glWeightSpace_iSup_eq_top_of_equivariant_surjective N M (quotientFDRep M σ)
    σ.toSubmodule.mkQ (quotientFDRep_mkQ_equivariant M σ)
    (quotientFDRep_mkQ_surjective M σ) hM

/-- **The character of `M` splits over the subrepresentation `σ`.** Given spanning weight-space
decompositions for the sub-`FDRep` and for `M`,

  `char M = char (subFDRep M σ) + char (quotientFDRep M σ)`.

This is the direct application of `formalCharacter_add_of_shortExact` to the equivariant short
exact sequence `subFDRep M σ ↪ M ↠ quotientFDRep M σ` packaged above. The spanning hypothesis on
the sub-`FDRep` is supplied by the *sub-of-spanning-is-spanning* helper (#5086). -/
theorem formalCharacter_eq_sub_add_quotient [IsAlgClosed k] [CharZero k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (σ : Subrepresentation M.ρ)
    (hsub : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (subFDRep M σ) (fun i => μ i) = ⊤)
    (hM : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N M (fun i => μ i) = ⊤) :
    formalCharacter k N M
      = formalCharacter k N (subFDRep M σ) + formalCharacter k N (quotientFDRep M σ) :=
  formalCharacter_add_of_shortExact N (subFDRep M σ) M (quotientFDRep M σ)
    σ.toSubmodule.subtype σ.toSubmodule.mkQ
    (subFDRep_subtype_equivariant M σ) (quotientFDRep_mkQ_equivariant M σ)
    (subFDRep_subtype_injective M σ) (quotientFDRep_mkQ_surjective M σ)
    (subFDRep_range_eq_quotientFDRep_ker M σ) hsub hM

end CleanCharExtraction

end Etingof

end
