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
for its formal character

  `formalCharacter k N (quotDetDegreeFDRep k N d)
     = ∑_{ν : BoundedPartition N d, 0 ∈ range ν.parts} s_ν(1,…,1) · S_ν`,

i.e. exactly the constituents whose last highest-weight coordinate vanishes
(`ν_N = 0`).

## The argument

The right-`GL_N`-equivariant per-degree short exact sequence

  `0 → A_{d-N} ⊗ χ  --mulDet-->  A_d  --mk-->  (A/det)_d → 0`

(`detSubmodule_inf_homogeneous`, `PolyRightGrading.lean`, sorry-free; the left
map `mulDet` is injective and intertwines up to the determinant character twist
`χ` via `detShiftLinearEquiv_intertwine`, `DetShiftIso.lean`) gives, by additivity
of the formal character over short exact sequences
(`formalCharacter_add_of_shortExact`), the difference

  `char (A/det)_d = char A_d − char (A_{d-N} ⊗ χ)`.

The twist character of `A_{d-N} ⊗ χ` is `(char A_{d-N}) · ∏ᵢ Xᵢ`
(`formalCharacter_charTwistDet`, the determinant character shifts every weight by
`(1,…,1)`). Substituting `polyRightDegreeFDRep_formalCharacter`
(`CauchyCharacterRightAssembly.lean`, multiplicity form `∑_ν s_ν(1,…,1) · S_ν`)
for both degrees and applying the combinatorial crux
`cauchyMult_mul_prodX_eq_lastPart_pos` (`CauchyCharDiff.lean`) to the subtracted
term — which identifies `(char A_{d-N}) · ∏ᵢ Xᵢ` with the part of `char A_d`
supported on the `0 ∉ range ν.parts` partitions — leaves exactly the
`0 ∈ range ν.parts` part.
-/

namespace Etingof.CauchyDetQuotient

open MvPolynomial Etingof Etingof.PolynomialGLAction Etingof.PolyRightGrading
  Etingof.KernelLemmaKPrime Etingof.DetShiftIso Etingof.CauchyCharacterRight

variable {k : Type*} [Field k] [IsAlgClosed k]

/-! ### General formal-character additivity over an equivariant short exact sequence -/

/-- **An equivariant linear map sends the `μ`-weight space into the `μ`-weight
space.** If `f : V → W` intertwines the `GL_N`-actions, then `f` maps
`glWeightSpace V μ` into `glWeightSpace W μ`. -/
theorem glWeightSpace_map_le (N : ℕ)
    (V W : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (f : V →ₗ[k] W) (hf : ∀ g v, f (V.ρ g v) = W.ρ g (f v)) (μ : Fin N → ℕ) :
    (glWeightSpace k N V μ).map f ≤ glWeightSpace k N W μ := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv ⊢
  intro i t
  rw [← hf, hv i t, map_smul]

/-- **The `μ`-weight space of `V` meets the range of an injective equivariant
`ι : U → V` exactly in the image of the `μ`-weight space of `U`.** This is the
exactness statement at weight `μ` for the left half of the sequence. -/
theorem glWeightSpace_inf_range (N : ℕ)
    (U V : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (ι : U →ₗ[k] V) (hι : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
    (hι_inj : Function.Injective ι) (μ : Fin N → ℕ) :
    glWeightSpace k N V μ ⊓ LinearMap.range ι = (glWeightSpace k N U μ).map ι := by
  apply le_antisymm
  · rintro x ⟨hxV, u, rfl⟩
    refine ⟨u, ?_, rfl⟩
    simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hxV ⊢
    intro i t
    have h : ι (U.ρ (diagUnit k N i t) u) = ι (((t : k) ^ μ i) • u) := by
      rw [hι, hxV i t, map_smul]
    exact hι_inj h
  · refine le_inf (glWeightSpace_map_le N U V ι hι μ) ?_
    rintro _ ⟨u, _, rfl⟩
    exact ⟨u, rfl⟩

/-- **Formal characters are additive over an equivariant short exact sequence.**
Given finite-dimensional `GL_N`-representations `U, V, W` with an injective
equivariant `ι : U → V`, a surjective equivariant `π : V → W`, exactness
`range ι = ker π`, and spanning weight-space decompositions for `U` and `V`, the
formal character of the middle term splits:

  `char V = char U + char W`.

This is the additivity of `μ ↦ dim (weight space μ)` over the per-weight short
exact sequences `0 → U_μ → V_μ → W_μ → 0`. The proof is the termwise inequality
`dim V_μ ≤ dim U_μ + dim W_μ` (left-exactness, no semisimplicity needed) upgraded
to equality by the global dimension count `∑_μ dim V_μ = dim V = dim U + dim W =
∑_μ (dim U_μ + dim W_μ)` (rank–nullity plus the spanning hypotheses). -/
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
  -- abbreviations for the weight-space dimensions
  set dU : (Fin N →₀ ℕ) → ℕ :=
    fun μ => Module.finrank k (glWeightSpace k N U (fun i => μ i)) with hdU
  set dV : (Fin N →₀ ℕ) → ℕ :=
    fun μ => Module.finrank k (glWeightSpace k N V (fun i => μ i)) with hdV
  set dW : (Fin N →₀ ℕ) → ℕ :=
    fun μ => Module.finrank k (glWeightSpace k N W (fun i => μ i)) with hdW
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
      dV μ = Module.finrank k ((glWeightSpace k N V (fun i => μ i)).map π) + dU μ := by
    intro μ
    set S := glWeightSpace k N V (fun i => μ i)
    -- the restricted map  π ∘ S.subtype : S → W
    set f := π ∘ₗ S.subtype with hf
    have hrange : LinearMap.range f = S.map π := by
      rw [hf, LinearMap.range_comp, Submodule.range_subtype]
    have hkermap : (LinearMap.ker f).map S.subtype = S ⊓ LinearMap.ker π := by
      rw [hf, LinearMap.ker_comp, Submodule.map_comap_subtype]
    have hker_finrank : Module.finrank k (LinearMap.ker f)
        = Module.finrank k (S ⊓ LinearMap.range ι : Submodule k V) := by
      rw [← hexact, ← hkermap,
        (Submodule.equivMapOfInjective S.subtype (Submodule.injective_subtype S)
          (LinearMap.ker f)).finrank_eq]
    have hUμ : Module.finrank k (S ⊓ LinearMap.range ι : Submodule k V) = dU μ := by
      rw [glWeightSpace_inf_range N U V ι hι hι_inj (fun i => μ i),
        ← (Submodule.equivMapOfInjective ι hι_inj
            (glWeightSpace k N U (fun i => μ i))).finrank_eq]
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, hker_finrank, hUμ] at hrn
    rw [hdV]
    exact hrn.symm
  -- per-weight inequality:  dim V_μ ≤ dim U_μ + dim W_μ
  have hle : ∀ μ : Fin N →₀ ℕ, dV μ ≤ dU μ + dW μ := by
    intro μ
    rw [hsplit μ, add_comm]
    refine Nat.add_le_add_left ?_ _
    exact Submodule.finrank_mono (glWeightSpace_map_le N V W π hπ (fun i => μ i))
  -- finite supports
  set sU := (glWeightSpace_finite_support k N U).toFinset with hsU
  set sV := (glWeightSpace_finite_support k N V).toFinset with hsV
  set sW := (glWeightSpace_finite_support k N W).toFinset with hsW
  set S : Finset (Fin N →₀ ℕ) := sU ∪ sV ∪ sW with hS
  -- off-support weight spaces are trivial
  have zeroU : ∀ μ ∉ sU, dU μ = 0 := by
    intro μ hμ
    have : glWeightSpace k N U (fun i => μ i) = ⊥ := by
      by_contra h; exact hμ ((glWeightSpace_finite_support k N U).mem_toFinset.mpr h)
    rw [hdU]; simp [this]
  have zeroV : ∀ μ ∉ sV, dV μ = 0 := by
    intro μ hμ
    have : glWeightSpace k N V (fun i => μ i) = ⊥ := by
      by_contra h; exact hμ ((glWeightSpace_finite_support k N V).mem_toFinset.mpr h)
    rw [hdV]; simp [this]
  have zeroW : ∀ μ ∉ sW, dW μ = 0 := by
    intro μ hμ
    have : glWeightSpace k N W (fun i => μ i) = ⊥ := by
      by_contra h; exact hμ ((glWeightSpace_finite_support k N W).mem_toFinset.mpr h)
    rw [hdW]; simp [this]
  -- global sums over the common index set S
  have hsumV : ∑ μ ∈ S, dV μ = Module.finrank k V := by
    rw [finrank_eq_sum_glWeightSpace k N V hVtop, ← hsV,
      Finset.sum_subset (by rw [hS]; exact (Finset.subset_union_left).trans Finset.subset_union_left)
        (fun μ _ hμ => zeroV μ hμ)]
  have hsumU : ∑ μ ∈ S, dU μ = Module.finrank k U := by
    rw [finrank_eq_sum_glWeightSpace k N U hUtop, ← hsU,
      Finset.sum_subset (by rw [hS]; exact Finset.subset_union_left.trans Finset.subset_union_left)
        (fun μ _ hμ => zeroU μ hμ)]
  have hsumW : ∑ μ ∈ S, dW μ = Module.finrank k W := by
    rw [finrank_eq_sum_glWeightSpace k N W hWtop, ← hsW,
      Finset.sum_subset (by rw [hS]; exact Finset.subset_union_right)
        (fun μ _ hμ => zeroW μ hμ)]
  -- rank–nullity for the whole sequence:  dim V = dim U + dim W
  have hrnπ := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ_surj, finrank_top, ← hexact,
    ← (LinearEquiv.ofInjective ι hι_inj).finrank_eq] at hrnπ
  -- hrnπ : finrank W + finrank U = finrank V
  have hsumeq : ∑ μ ∈ S, dV μ = ∑ μ ∈ S, (dU μ + dW μ) := by
    rw [Finset.sum_add_distrib, hsumU, hsumW, hsumV]; omega
  have hterm := (Finset.sum_eq_sum_iff_of_le (fun μ _ => hle μ)).mp hsumeq
  -- assemble the formal-character identity coefficient by coefficient
  ext μ
  rw [MvPolynomial.coeff_add, formalCharacter_coeff, formalCharacter_coeff,
    formalCharacter_coeff]
  by_cases hμS : μ ∈ S
  · have := hterm μ hμS
    rw [hdU, hdV, hdW] at this
    push_cast [this]; ring
  · have hVμ := zeroV μ (fun h => hμS (by rw [hS]; exact Finset.mem_union_left _ (Finset.mem_union_right _ h)))
    have hUμ := zeroU μ (fun h => hμS (by rw [hS]; exact Finset.mem_union_left _ (Finset.mem_union_left _ h)))
    have hWμ := zeroW μ (fun h => hμS (by rw [hS]; exact Finset.mem_union_right _ h))
    rw [hdU] at hUμ; rw [hdV] at hVμ; rw [hdW] at hWμ
    rw [hVμ, hUμ, hWμ]; push_cast; ring

end Etingof.CauchyDetQuotient
