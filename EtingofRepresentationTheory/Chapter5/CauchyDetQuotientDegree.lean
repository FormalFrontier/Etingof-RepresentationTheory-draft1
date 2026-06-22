import Mathlib
import EtingofRepresentationTheory.Chapter5.CauchyCharacterRightAssembly
import EtingofRepresentationTheory.Chapter5.CauchyCharDiff
import EtingofRepresentationTheory.Chapter5.PolyRightGrading

/-!
# The determinant-quotient degree component `(A/det)_d` and its formal character

This file builds the **part-B** deliverable of issue #4905 (parent #4896, route
doc `progress/kernel-lemma-K-route.md`): the degree-`d` component of the
determinant quotient `A/det = k[Xᵢⱼ]/(det)`, packaged as a finite-dimensional
right-`GL_N`-representation `quotDetDegreeFDRep k N d`, together with the formula
for its formal character (the `0 ∈ range ν.parts`, i.e. `ν_N = 0`, constituents).

## The argument

The right-`GL_N`-equivariant per-degree short exact sequence

  `0 → A_{d-N} ⊗ χ  --mulDet-->  A_d  --mk-->  (A/det)_d → 0`

(`detSubmodule_inf_homogeneous`, `PolyRightGrading.lean`, sorry-free) gives, by
additivity of the formal character over short exact sequences
(`formalCharacter_add_of_shortExact`),

  `char (A/det)_d = char A_d − char (A_{d-N} ⊗ χ)`.

The twist character of `A_{d-N} ⊗ χ` is `(char A_{d-N}) · ∏ᵢ Xᵢ`
(`formalCharacter_twistFDRep`, the determinant character shifts every weight by
`(1,…,1)`). Substituting `polyRightDegreeFDRep_formalCharacter`
(`CauchyCharacterRightAssembly.lean`) for both degrees and applying the
combinatorial crux `cauchyMult_mul_prodX_eq_lastPart_pos` (`CauchyCharDiff.lean`)
leaves exactly the `0 ∈ range ν.parts` part.
-/

namespace Etingof.CauchyDetQuotient

open MvPolynomial Etingof Etingof.PolynomialGLAction Etingof.PolyRightGrading
  Etingof.KernelLemmaKPrime Etingof.DetShiftIso Etingof.CauchyCharacterRight
  Etingof.CauchyWeightSpaceDimension

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

/-! ### General formal-character additivity over an equivariant short exact sequence -/

/-- Membership in the `μ`-weight space, unfolded: `v` is a weight-`μ` vector iff
every diagonal torus element acts on `v` by the scalar `t ^ μ i`. -/
theorem mem_glWeightSpace_iff (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (μ : Fin N → ℕ) (v : M) :
    v ∈ glWeightSpace k N M μ ↔
      ∀ (i : Fin N) (t : kˣ), M.ρ (diagUnit k N i t) v = (t : k) ^ μ i • v := by
  simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

/-- **An equivariant linear map sends the `μ`-weight space into the `μ`-weight
space.** -/
theorem glWeightSpace_map_le (N : ℕ)
    (V W : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (f : V →ₗ[k] W) (hf : ∀ g v, f (V.ρ g v) = W.ρ g (f v)) (μ : Fin N → ℕ) :
    (glWeightSpace k N V μ).map f ≤ glWeightSpace k N W μ := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [SetLike.mem_coe, mem_glWeightSpace_iff] at hv ⊢
  intro i t
  rw [← hf, hv i t, map_smul]

/-- **The `μ`-weight space of `V` meets the range of an injective equivariant
`ι : U → V` exactly in the image of the `μ`-weight space of `U`.** -/
theorem glWeightSpace_inf_range (N : ℕ)
    (U V : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (ι : U →ₗ[k] V) (hι : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
    (hι_inj : Function.Injective ι) (μ : Fin N → ℕ) :
    glWeightSpace k N V μ ⊓ LinearMap.range ι = (glWeightSpace k N U μ).map ι := by
  apply le_antisymm
  · rintro x ⟨hxV, u, rfl⟩
    refine ⟨u, ?_, rfl⟩
    simp only [SetLike.mem_coe, mem_glWeightSpace_iff] at hxV ⊢
    intro i t
    apply hι_inj
    rw [hι, map_smul, hxV i t]
  · refine le_inf (glWeightSpace_map_le N U V ι hι μ) ?_
    rintro _ ⟨u, _, rfl⟩
    exact ⟨u, rfl⟩

/-- **Formal characters are additive over an equivariant short exact sequence.**
Given finite-dimensional `GL_N`-representations `U, V, W` with an injective
equivariant `ι : U → V`, a surjective equivariant `π : V → W`, exactness
`range ι = ker π`, and spanning weight-space decompositions for `U` and `V`,

  `char V = char U + char W`.

The proof is the termwise inequality `dim V_μ ≤ dim U_μ + dim W_μ` (left-exactness)
upgraded to equality by the global count `∑_μ dim V_μ = dim V = dim U + dim W`
(rank–nullity plus the spanning hypotheses). -/
theorem formalCharacter_add_of_shortExact (N : ℕ)
    (U V W : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (ι : U →ₗ[k] V) (π : V →ₗ[k] W)
    (hι : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
    (hπ : ∀ g v, π (V.ρ g v) = W.ρ g (π v))
    (hι_inj : Function.Injective ι)
    (hπ_surj : Function.Surjective π)
    (hexact : LinearMap.range ι = LinearMap.ker π)
    (hUtop : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N U (fun i => μ i) = ⊤)
    (hVtop : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N V (fun i => μ i) = ⊤) :
    formalCharacter k N V = formalCharacter k N U + formalCharacter k N W := by
  classical
  -- spanning for W, from spanning of V plus surjectivity of π
  have hWtop : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N W (fun i => μ i) = ⊤ := by
    have h1 : (⨆ μ : Fin N →₀ ℕ, glWeightSpace k N V (fun i => μ i)).map π
        = ⨆ μ : Fin N →₀ ℕ, (glWeightSpace k N V (fun i => μ i)).map π :=
      Submodule.map_iSup _ _
    rw [hVtop, Submodule.map_top, LinearMap.range_eq_top.mpr hπ_surj] at h1
    have h2 : (⨆ μ : Fin N →₀ ℕ, (glWeightSpace k N V (fun i => μ i)).map π)
        ≤ ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N W (fun i => μ i) :=
      iSup_mono fun μ => glWeightSpace_map_le N V W π hπ _
    exact top_le_iff.mp (h1 ▸ h2)
  -- per-weight split:  dim V_μ = dim ((V_μ).map π) + dim U_μ
  have hsplit : ∀ μ : Fin N →₀ ℕ,
      Module.finrank k (glWeightSpace k N V (fun i => μ i))
        = Module.finrank k ((glWeightSpace k N V (fun i => μ i)).map π)
          + Module.finrank k (glWeightSpace k N U (fun i => μ i)) := by
    intro μ
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (π ∘ₗ (glWeightSpace k N V (fun i => μ i)).subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype] at hrn
    have hk : Module.finrank k
          (LinearMap.ker (π ∘ₗ (glWeightSpace k N V (fun i => μ i)).subtype))
        = Module.finrank k (glWeightSpace k N U (fun i => μ i)) := by
      rw [LinearMap.ker_comp,
        (Submodule.equivMapOfInjective _
          (Submodule.injective_subtype (glWeightSpace k N V (fun i => μ i)))
          (Submodule.comap (glWeightSpace k N V (fun i => μ i)).subtype
            (LinearMap.ker π))).finrank_eq,
        Submodule.map_comap_subtype, ← hexact,
        glWeightSpace_inf_range N U V ι hι hι_inj (fun i => μ i),
        ← (Submodule.equivMapOfInjective ι hι_inj
            (glWeightSpace k N U (fun i => μ i))).finrank_eq]
    rw [hk] at hrn
    omega
  -- per-weight inequality:  dim V_μ ≤ dim U_μ + dim W_μ
  have hle : ∀ μ : Fin N →₀ ℕ,
      Module.finrank k (glWeightSpace k N V (fun i => μ i))
        ≤ Module.finrank k (glWeightSpace k N U (fun i => μ i))
          + Module.finrank k (glWeightSpace k N W (fun i => μ i)) := by
    intro μ
    rw [hsplit μ, add_comm]
    exact Nat.add_le_add_left
      (Submodule.finrank_mono (glWeightSpace_map_le N V W π hπ (fun i => μ i))) _
  -- finite supports and common index set
  set S : Finset (Fin N →₀ ℕ) :=
    (glWeightSpace_finite_support k N U).toFinset
      ∪ (glWeightSpace_finite_support k N V).toFinset
      ∪ (glWeightSpace_finite_support k N W).toFinset with hS
  have zero_of : ∀ (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (μ : Fin N →₀ ℕ),
      μ ∉ (glWeightSpace_finite_support k N M).toFinset →
      Module.finrank k (glWeightSpace k N M (fun i => μ i)) = 0 := by
    intro M μ hμ
    have : glWeightSpace k N M (fun i => μ i) = ⊥ := by
      by_contra h; exact hμ ((glWeightSpace_finite_support k N M).mem_toFinset.mpr h)
    rw [this, finrank_bot]
  -- global sums over the common index set S
  have hsumV : ∑ μ ∈ S, Module.finrank k (glWeightSpace k N V (fun i => μ i))
      = Module.finrank k V := by
    rw [finrank_eq_sum_glWeightSpace k N V hVtop]
    refine (Finset.sum_subset ?_ (fun μ _ hμ => zero_of V μ hμ)).symm
    rw [hS]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hsumU : ∑ μ ∈ S, Module.finrank k (glWeightSpace k N U (fun i => μ i))
      = Module.finrank k U := by
    rw [finrank_eq_sum_glWeightSpace k N U hUtop]
    refine (Finset.sum_subset ?_ (fun μ _ hμ => zero_of U μ hμ)).symm
    rw [hS]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hsumW : ∑ μ ∈ S, Module.finrank k (glWeightSpace k N W (fun i => μ i))
      = Module.finrank k W := by
    rw [finrank_eq_sum_glWeightSpace k N W hWtop]
    refine (Finset.sum_subset ?_ (fun μ _ hμ => zero_of W μ hμ)).symm
    rw [hS]; exact Finset.subset_union_right
  -- rank–nullity for the whole sequence:  dim V = dim U + dim W
  have hrnπ := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ_surj, finrank_top, ← hexact,
    ← (LinearEquiv.ofInjective ι hι_inj).finrank_eq] at hrnπ
  -- termwise equality on S from the equal sums and termwise inequality
  have hsumeq : ∑ μ ∈ S, Module.finrank k (glWeightSpace k N V (fun i => μ i))
      = ∑ μ ∈ S, (Module.finrank k (glWeightSpace k N U (fun i => μ i))
          + Module.finrank k (glWeightSpace k N W (fun i => μ i))) := by
    rw [Finset.sum_add_distrib, hsumU, hsumW, hsumV]; omega
  have hterm := (Finset.sum_eq_sum_iff_of_le (fun μ _ => hle μ)).mp hsumeq
  -- conclude coefficient by coefficient
  have hdim : ∀ μ : Fin N →₀ ℕ,
      Module.finrank k (glWeightSpace k N V (fun i => μ i))
        = Module.finrank k (glWeightSpace k N U (fun i => μ i))
          + Module.finrank k (glWeightSpace k N W (fun i => μ i)) := by
    intro μ
    by_cases hμS : μ ∈ S
    · exact hterm μ hμS
    · have hVμ := zero_of V μ (fun h => hμS (by
        rw [hS]; exact Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hUμ := zero_of U μ (fun h => hμS (by
        rw [hS]; exact Finset.mem_union_left _ (Finset.mem_union_left _ h)))
      have hWμ := zero_of W μ (fun h => hμS (by rw [hS]; exact Finset.mem_union_right _ h))
      rw [hVμ, hUμ, hWμ]
  ext μ
  rw [MvPolynomial.coeff_add, formalCharacter_coeff, formalCharacter_coeff,
    formalCharacter_coeff]
  rw [hdim μ]; push_cast; ring

/-! ### The determinant character on the diagonal torus -/

/-- `det (diagUnit i t) = t`: the determinant character has right-torus weight
`(1,…,1)`. -/
theorem detChar_diagUnit_val (N : ℕ) (i : Fin N) (t : kˣ) :
    ((detChar k N (diagUnit k N i t) : kˣ) : k) = (t : k) := by
  rw [detChar, Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal (Function.update (1 : Fin N → k) i (t : k))).det = (t : k)
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

/-! ### Spanning of the weight spaces of `A_d` -/

/-- **The weight spaces of `A_d` span.** Every degree-`d` monomial is a weight
vector (its weight is its column-degree vector), and the degree-`d` monomials span
`A_d`, so `⨆_μ (A_d)_μ = ⊤`. -/
theorem polyRight_iSup_glWeightSpace_eq_top {N : ℕ} (d : ℕ) :
    ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N (polyRightDegreeFDRep k N d) (fun i => μ i) = ⊤ := by
  classical
  refine Submodule.map_injective_of_injective (polyOf_injective d) ?_
  rw [Submodule.map_iSup, Submodule.map_top]
  have hrange : LinearMap.range (polyOf d)
      = MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d :=
    Submodule.range_subtype _
  rw [hrange]
  simp_rw [map_polyOf_glWeightSpace, ← Submodule.span_iUnion]
  -- the union of the `Dset`s over all weights is all degree-`d` exponents
  have hunion : (⋃ μ : Fin N →₀ ℕ,
        (fun s => MvPolynomial.monomial s (1 : k)) '' (Dset N d μ : Set _))
      = (fun s => MvPolynomial.monomial s (1 : k)) ''
          { s : (Fin N × Fin N) →₀ ℕ | ∑ p, s p = d } := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe, mem_Dset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨μ, s, ⟨hsum, _⟩, rfl⟩; exact ⟨s, hsum, rfl⟩
    · rintro ⟨s, hsum, rfl⟩
      exact ⟨Finsupp.equivFunOnFinite.symm (fun j => ∑ i, s (i, j)), s,
        ⟨hsum, fun j => by simp⟩, rfl⟩
  rw [hunion]
  -- the span of all degree-`d` monomials is `A_d`
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    exact (MvPolynomial.mem_homogeneousSubmodule d _).2
      (MvPolynomial.isHomogeneous_monomial _ (by rw [Finsupp.degree_eq_sum]; exact hs))
  · intro f hf
    rw [(f).as_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hdeg : ∑ p, s p = d := by
      have hH : f.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d _).1 hf
      have := hH (MvPolynomial.mem_support_iff.mp hs)
      rwa [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    rw [show (MvPolynomial.monomial s (MvPolynomial.coeff s f)
          : MvPolynomial (Fin N × Fin N) k)
        = MvPolynomial.coeff s f • MvPolynomial.monomial s 1 by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, hdeg, rfl⟩)

/-! ### The degree-`d` component of the determinant quotient as an `FDRep` -/

/-- **The degree-`d` component `(A/det)_d`, as a subrepresentation of `quotDetRep`.**
Its carrier is the image of `A_d` under the quotient projection `A → A/det`. -/
noncomputable def quotDetDegreeSubrep (k : Type*) [Field k] (N d : ℕ) :
    Subrepresentation (quotDetRep k N) where
  toSubmodule :=
    (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d).map (Submodule.mkQ (detSubmodule k N))
  apply_mem_toSubmodule g x hx := by
    obtain ⟨f, hf, rfl⟩ := hx
    refine ⟨polyRightRep k N g f, ?_, ?_⟩
    · exact (MvPolynomial.mem_homogeneousSubmodule d _).2
        (polyRightRep_isHomogeneous g ((MvPolynomial.mem_homogeneousSubmodule d _).1 hf))
    · rw [Submodule.mkQ_apply, Submodule.mkQ_apply, quotDetRep_mk]

/-- **The degree-`d` component `(A/det)_d` as an `FDRep`** of `GL_N(k)`: the cokernel
of `mulDet : A_{d-N} → A_d` in the per-degree short exact sequence
`0 → A_{d-N} ⊗ χ → A_d → (A/det)_d → 0`. -/
noncomputable def quotDetDegreeFDRep (k : Type*) [Field k] (N d : ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  haveI : FiniteDimensional k (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d) :=
    CauchyCharacterRight.finiteDimensional_homogeneousSubmodule d
  haveI : FiniteDimensional k (quotDetDegreeSubrep k N d).toSubmodule :=
    inferInstanceAs (FiniteDimensional k
      ((MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d).map (Submodule.mkQ (detSubmodule k N))))
  FDRep.of (quotDetDegreeSubrep k N d).toRepresentation

/-! ### The determinant-character twist `A_e ⊗ χ` and its formal character -/

/-- The degree-`e` homogeneous component `A_e` of `k[Xᵢⱼ]` twisted by the
determinant character `χ = detChar`, as an `FDRep` on the same carrier as
`polyRightDegreeFDRep k N e`. This is the left object `A_{d-N} ⊗ χ` of the
per-degree short exact sequence. -/
noncomputable def twistFDRep (k : Type*) [Field k] (N e : ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  haveI : FiniteDimensional k (polyRightHomogeneousSubrep k N e).toSubmodule :=
    finiteDimensional_homogeneousSubmodule e
  FDRep.of (charTwistRep (detChar k N) (polyRightHomogeneousSubrep k N e).toRepresentation)

/-- The action of `twistFDRep` is `detChar`-scaled `polyRightDegreeFDRep` action. -/
theorem twistFDRep_ρ_apply (e : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (v : twistFDRep k N e) :
    (twistFDRep k N e).ρ g v
      = (detChar k N g : k) • (polyRightDegreeFDRep k N e).ρ g v := by
  show (charTwistRep (detChar k N) (polyRightHomogeneousSubrep k N e).toRepresentation) g v
      = (detChar k N g : k) • (polyRightHomogeneousSubrep k N e).toRepresentation g v
  rw [charTwistRep_apply]

/-- **The twist shifts every weight up by one** (positive case): for `μ` with all
coordinates `≥ 1`, the `μ`-weight space of `A_e ⊗ χ` is the `(μ-1)`-weight space of
`A_e`. -/
theorem glWeightSpace_twistFDRep_pos (e : ℕ) (μ : Fin N → ℕ) (hμ : ∀ i, 1 ≤ μ i) :
    glWeightSpace k N (twistFDRep k N e) μ
      = glWeightSpace k N (polyRightDegreeFDRep k N e) (fun i => μ i - 1) := by
  ext v
  rw [mem_glWeightSpace_iff, mem_glWeightSpace_iff]
  refine forall_congr' fun i => forall_congr' fun t => ?_
  rw [twistFDRep_ρ_apply, detChar_diagUnit_val]
  constructor
  · intro h
    refine smul_right_injective _ (Units.ne_zero t) ?_
    show (t : k) • (polyRightDegreeFDRep k N e).ρ (diagUnit k N i t) v
        = (t : k) • ((t : k) ^ (μ i - 1) • v)
    rw [h, smul_smul, ← pow_succ', Nat.sub_add_cancel (hμ i)]
  · intro h
    rw [h, smul_smul, ← pow_succ', Nat.sub_add_cancel (hμ i)]

/-- **The twist has no weight with a zero coordinate**: if some `μ j = 0` then the
`μ`-weight space of `A_e ⊗ χ` is trivial (its weight vectors would have a negative
`A_e`-weight). -/
theorem glWeightSpace_twistFDRep_zero (e : ℕ) (μ : Fin N → ℕ) (j : Fin N) (hj : μ j = 0) :
    glWeightSpace k N (twistFDRep k N e) μ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  rw [mem_glWeightSpace_iff] at hv
  apply polyOf_injective e
  rw [map_zero]
  ext s
  rw [MvPolynomial.coeff_zero]
  by_contra hcoeff
  obtain ⟨t, ht⟩ := exists_unit_pow_ne_one k ((∑ l, s (l, j)) + 1) (by omega)
  have hkey : (t : k) • (polyRightDegreeFDRep k N e).ρ (diagUnit k N j t) v = v := by
    have := hv j t
    rwa [twistFDRep_ρ_apply, detChar_diagUnit_val, hj, pow_zero, one_smul] at this
  have hpoly := congrArg (polyOf e) hkey
  rw [map_smul, polyOf_rho] at hpoly
  have hc := congrArg (MvPolynomial.coeff s) hpoly
  rw [MvPolynomial.coeff_smul, coeff_polyRightRep_diagUnit, smul_eq_mul,
    ← mul_assoc, ← pow_succ'] at hc
  exact ht (mul_right_cancel₀ hcoeff (by rw [hc, one_mul]))

/-- All-ones exponent vector. -/
private noncomputable def allOnes (N : ℕ) : Fin N →₀ ℕ :=
  ∑ i : Fin N, Finsupp.single i 1

private theorem allOnes_apply (N : ℕ) (i : Fin N) : allOnes N i = 1 := by
  classical
  simp only [allOnes, Finsupp.finset_sum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem prod_X_eq_monomial_allOnes (N : ℕ) :
    (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ))
      = MvPolynomial.monomial (allOnes N) 1 := by
  classical
  have hsupp : (allOnes N).support = Finset.univ := by
    ext i; simp only [Finsupp.mem_support_iff, allOnes_apply, Finset.mem_univ, ne_eq,
      one_ne_zero, not_false_eq_true]
  rw [← MvPolynomial.prod_X_pow_eq_monomial, hsupp]
  exact Finset.prod_congr rfl fun i _ => by rw [allOnes_apply, pow_one]

set_option maxHeartbeats 800000 in
/-- **The formal character of the determinant-character twist** `A_e ⊗ χ` is
`(∏ᵢ Xᵢ) · char A_e`: twisting by `χ` shifts every weight by `(1,…,1)`. -/
theorem formalCharacter_twistFDRep (e : ℕ) :
    formalCharacter k N (twistFDRep k N e)
      = (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ))
          * formalCharacter k N (polyRightDegreeFDRep k N e) := by
  classical
  rw [prod_X_eq_monomial_allOnes]
  ext μ
  rw [formalCharacter_coeff, MvPolynomial.coeff_monomial_mul']
  by_cases hμ : allOnes N ≤ μ
  · have hμ1 : ∀ i, 1 ≤ μ i := fun i => by
      have := (Finsupp.le_def.mp hμ) i; rwa [allOnes_apply] at this
    have harg : (fun i => μ i - 1) = (fun i => (μ - allOnes N) i) := by
      funext i; rw [Finsupp.tsub_apply, allOnes_apply]
    rw [if_pos hμ, one_mul, formalCharacter_coeff]
    refine Nat.cast_inj.mpr ?_
    rw [glWeightSpace_twistFDRep_pos e (fun i => μ i) hμ1]
    exact congrArg
      (fun w => Module.finrank k (glWeightSpace k N (polyRightDegreeFDRep k N e) w)) harg
  · rw [if_neg hμ]
    have hj : ∃ j, μ j = 0 := by
      by_contra h; push_neg at h
      exact hμ (Finsupp.le_def.mpr fun i => by rw [allOnes_apply]; have := h i; omega)
    obtain ⟨j, hj0⟩ := hj
    rw [glWeightSpace_twistFDRep_zero e (fun i => μ i) j hj0, finrank_bot,
      Nat.cast_zero]

end Etingof.CauchyDetQuotient
