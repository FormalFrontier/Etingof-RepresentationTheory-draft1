import EtingofRepresentationTheory.Chapter5.FormalCharacterIso

/-!
# DetInvElim-clean formal-character additivity (issue #5078, parent #5075)

This file is the **DetInvElim-clean** home of the formal-character additivity engine
underlying the constituent-character extraction step of the `#4905`/`#4896` part-(a)
assembly (`clean_simple_constituent_formalCharacter_eq_schurPoly_mem`, #5078).

The additivity lemma `formalCharacter_add_of_shortExact` and its weight-space helpers
already exist (sorry-free) in `CauchyDetQuotientDegree.lean`, and the weight-saturation
transfer lemma `glWeightSpace_iSup_eq_top_of_equivariant_surjective` exists in
`SchurWeylFormalCharacterIso.lean` — but **both host files are polluted**: they
transitively import `DetInvElim` (via `PolyRightGrading` / `FormalCharacterTorusTrace`).
Because the `#4896` assembly feeds back into `DetInvElim`, using the polluted versions to
prove part-(a) is a genuine build cycle (#5072).

The statements and proofs here are clean relocations: they depend **only** on
`FormalCharacterIso` (and its clean ancestors), so the clean extractor built on top avoids
the cycle. The originals in the polluted files are left in place (their downstream
consumers there are unchanged); a successor may delete them in favour of these once the
clean extractor lands.

Relocated items (in namespace `Etingof.CleanCharExtraction`):

* `mem_glWeightSpace_iff` — membership in the `μ`-weight space, unfolded.
* `glWeightSpace_map_le` — an equivariant map sends the `μ`-weight space into the
  `μ`-weight space.
* `glWeightSpace_inf_range` — the `μ`-weight space meets the range of an injective
  equivariant map exactly in the image of the source `μ`-weight space.
* `formalCharacter_add_of_shortExact` — additivity of the formal character over an
  equivariant short exact sequence (needs weight-space spanning for the sub and total).
* `glWeightSpace_iSup_eq_top_of_equivariant_surjective` — weight saturation transfers
  along equivariant surjections.
-/

open MvPolynomial

namespace Etingof.CleanCharExtraction

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

/-! ### General formal-character additivity over an equivariant short exact sequence -/

omit [CharZero k] in
/-- Membership in the `μ`-weight space, unfolded: `v` is a weight-`μ` vector iff
every diagonal torus element acts on `v` by the scalar `t ^ μ i`. -/
theorem mem_glWeightSpace_iff (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (μ : Fin N → ℕ) (v : M) :
    v ∈ glWeightSpace k N M μ ↔
      ∀ (i : Fin N) (t : kˣ), M.ρ (diagUnit k N i t) v = (t : k) ^ μ i • v := by
  simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

omit [CharZero k] in
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

omit [CharZero k] in
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

/-! ### Weight saturation transfers along equivariant surjections -/

omit [CharZero k] in
/-- **Weight saturation transfers along equivariant surjections.** A `GL_N`-equivariant
surjection `φ : M → P` sends each `ℕ`-weight vector of `M` to an `ℕ`-weight vector of `P`
of the same weight (equivariance commutes `φ` past the torus action), so the image of a
weight space lands in the matching weight space. Hence if the `ℕ`-weight spaces of `M`
span all of `M`, those of `P` span all of `P`. -/
theorem glWeightSpace_iSup_eq_top_of_equivariant_surjective (N : ℕ)
    (M P : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (φ : M →ₗ[k] P)
    (hφ : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : M), φ (M.ρ g v) = P.ρ g (φ v))
    (hsurj : Function.Surjective φ)
    (hM : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) :
    ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N P (fun i => μ i) = ⊤ := by
  have hmap : ∀ μ : Fin N →₀ ℕ,
      Submodule.map φ (glWeightSpace k N M (fun i => μ i))
        ≤ glWeightSpace k N P (fun i => μ i) := fun μ =>
    glWeightSpace_map_le N M P φ hφ (fun i => μ i)
  rw [eq_top_iff, ← LinearMap.range_eq_top.mpr hsurj, ← Submodule.map_top, ← hM,
    Submodule.map_iSup]
  exact iSup_mono hmap

end Etingof.CleanCharExtraction
