import RepresentationTheory.AuxiliaryCharacter

set_option linter.dupNamespace false
set_option linter.style.longLine false

open MvPolynomial

namespace RepresentationTheory.GeneralLinearRepresentation.WeightSpaceMorphisms

namespace GeneralLinearRepresentation

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

omit [CharZero k] in
/-- A vector belongs to a weight space exactly when the action of each displayed group element scales it by the corresponding power of the unit. -/
theorem mem_weightSpace_iff_action_eq_smul (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (μ : Fin N → ℕ) (v : M) :
    v ∈ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M μ ↔
      ∀ (i : Fin N) (t : kˣ),
        M.ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t) v =
          (t : k) ^ μ i • v := by
  simp only [RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace,
    Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

omit [CharZero k] in
/-- An equivariant linear map sends each weight space into the corresponding target weight space. -/
theorem map_weightSpace_le_of_equivariant (N : ℕ)
    (V W : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (f : V →ₗ[k] W) (hf : ∀ g v, f (V.ρ g v) = W.ρ g (f v)) (μ : Fin N → ℕ) :
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V μ).map f ≤
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N W μ := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [SetLike.mem_coe, mem_weightSpace_iff_action_eq_smul] at hv ⊢
  intro i t
  rw [← hf, hv i t, map_smul]

omit [CharZero k] in
/-- For an injective equivariant linear map, the target weight space intersected with the range equals the image of the source weight space. -/
theorem weightSpace_inf_range_eq_map_of_injective_equivariant (N : ℕ)
    (U V : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (ι : U →ₗ[k] V) (hι : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
    (hι_inj : Function.Injective ι) (μ : Fin N → ℕ) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V μ ⊓
        LinearMap.range ι =
      (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N U μ).map ι := by
  apply le_antisymm
  · rintro x ⟨hxV, u, rfl⟩
    refine ⟨u, ?_, rfl⟩
    simp only [SetLike.mem_coe, mem_weightSpace_iff_action_eq_smul] at hxV ⊢
    intro i t
    apply hι_inj
    rw [hι, map_smul, hxV i t]
  · refine le_inf (map_weightSpace_le_of_equivariant N U V ι hι μ) ?_
    rintro _ ⟨u, _, rfl⟩
    exact ⟨u, rfl⟩

/-- For an equivariant short exact sequence whose first two representations have spanning weight spaces, the middle polynomial invariant is the sum of the outer invariants. -/
theorem weightPolynomial_eq_add_of_equivariant_exact (N : ℕ)
    (U V W : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (ι : U →ₗ[k] V) (π : V →ₗ[k] W)
    (hι : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
    (hπ : ∀ g v, π (V.ρ g v) = W.ρ g (π v))
    (hι_inj : Function.Injective ι)
    (hπ_surj : Function.Surjective π)
    (hexact : LinearMap.range ι = LinearMap.ker π)
    (hUtop : ⨆ μ : Fin N →₀ ℕ,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N U (fun i => μ i) = ⊤)
    (hVtop : ⨆ μ : Fin N →₀ ℕ,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V (fun i => μ i) = ⊤) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N V =
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N U +
        RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N W := by
  classical
  have hWtop : ⨆ μ : Fin N →₀ ℕ,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N W (fun i => μ i) = ⊤ := by
    have h1 :
        (⨆ μ : Fin N →₀ ℕ,
          RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
            (fun i => μ i)).map π =
          ⨆ μ : Fin N →₀ ℕ,
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
              (fun i => μ i)).map π :=
      Submodule.map_iSup _ _
    rw [hVtop, Submodule.map_top, LinearMap.range_eq_top.mpr hπ_surj] at h1
    have h2 :
        (⨆ μ : Fin N →₀ ℕ,
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
            (fun i => μ i)).map π) ≤
          ⨆ μ : Fin N →₀ ℕ,
            RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N W
              (fun i => μ i) :=
      iSup_mono fun μ => map_weightSpace_le_of_equivariant N V W π hπ _
    exact top_le_iff.mp (h1 ▸ h2)
  have hsplit : ∀ μ : Fin N →₀ ℕ,
      Module.finrank k
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
            (fun i => μ i)) =
        Module.finrank k
            ((RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
              (fun i => μ i)).map π) +
          Module.finrank k
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N U
              (fun i => μ i)) := by
    intro μ
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (π ∘ₗ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
        (fun i => μ i)).subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype] at hrn
    have hk : Module.finrank k
          (LinearMap.ker
            (π ∘ₗ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
              (fun i => μ i)).subtype)) =
        Module.finrank k
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N U
            (fun i => μ i)) := by
      rw [LinearMap.ker_comp,
        (Submodule.equivMapOfInjective _
          (Submodule.injective_subtype
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
              (fun i => μ i)))
          (Submodule.comap
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
              (fun i => μ i)).subtype (LinearMap.ker π))).finrank_eq,
        Submodule.map_comap_subtype, ← hexact,
        weightSpace_inf_range_eq_map_of_injective_equivariant N U V ι hι hι_inj
          (fun i => μ i),
        ← (Submodule.equivMapOfInjective ι hι_inj
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N U
              (fun i => μ i))).finrank_eq]
    rw [hk] at hrn
    omega
  have hle : ∀ μ : Fin N →₀ ℕ,
      Module.finrank k
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
            (fun i => μ i)) ≤
        Module.finrank k
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N U
              (fun i => μ i)) +
          Module.finrank k
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N W
              (fun i => μ i)) := by
    intro μ
    rw [hsplit μ, add_comm]
    exact Nat.add_le_add_left
      (Submodule.finrank_mono
        (map_weightSpace_le_of_equivariant N V W π hπ (fun i => μ i))) _
  set S : Finset (Fin N →₀ ℕ) :=
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N U).toFinset
      ∪ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N V).toFinset
      ∪ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N W).toFinset with hS
  have zero_of : ∀ (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (μ : Fin N →₀ ℕ),
      μ ∉ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N M).toFinset →
      Module.finrank k
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M
          (fun i => μ i)) = 0 := by
    intro M μ hμ
    have : RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M
        (fun i => μ i) = ⊥ := by
      by_contra h
      exact hμ
        ((RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N M).mem_toFinset.mpr h)
    rw [this, finrank_bot]
  have hsumV :
      ∑ μ ∈ S, Module.finrank k
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
          (fun i => μ i)) = Module.finrank k V := by
    rw [RepresentationTheory.AuxiliaryCharacter.finrank_eq_sum_finrank_auxiliaryWeightSpace
      k N V hVtop]
    refine (Finset.sum_subset ?_ (fun μ _ hμ => zero_of V μ hμ)).symm
    rw [hS]
    exact Finset.subset_union_right.trans Finset.subset_union_left
  have hsumU :
      ∑ μ ∈ S, Module.finrank k
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N U
          (fun i => μ i)) = Module.finrank k U := by
    rw [RepresentationTheory.AuxiliaryCharacter.finrank_eq_sum_finrank_auxiliaryWeightSpace
      k N U hUtop]
    refine (Finset.sum_subset ?_ (fun μ _ hμ => zero_of U μ hμ)).symm
    rw [hS]
    exact Finset.subset_union_left.trans Finset.subset_union_left
  have hsumW :
      ∑ μ ∈ S, Module.finrank k
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N W
          (fun i => μ i)) = Module.finrank k W := by
    rw [RepresentationTheory.AuxiliaryCharacter.finrank_eq_sum_finrank_auxiliaryWeightSpace
      k N W hWtop]
    refine (Finset.sum_subset ?_ (fun μ _ hμ => zero_of W μ hμ)).symm
    rw [hS]
    exact Finset.subset_union_right
  have hrnπ := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ_surj, finrank_top, ← hexact,
    ← (LinearEquiv.ofInjective ι hι_inj).finrank_eq] at hrnπ
  have hsumeq :
      ∑ μ ∈ S, Module.finrank k
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
            (fun i => μ i)) =
        ∑ μ ∈ S,
          (Module.finrank k
              (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N U
                (fun i => μ i)) +
            Module.finrank k
              (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N W
                (fun i => μ i))) := by
    rw [Finset.sum_add_distrib, hsumU, hsumW, hsumV]
    omega
  have hterm := (Finset.sum_eq_sum_iff_of_le (fun μ _ => hle μ)).mp hsumeq
  have hdim : ∀ μ : Fin N →₀ ℕ,
      Module.finrank k
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N V
            (fun i => μ i)) =
        Module.finrank k
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N U
              (fun i => μ i)) +
          Module.finrank k
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N W
              (fun i => μ i)) := by
    intro μ
    by_cases hμS : μ ∈ S
    · exact hterm μ hμS
    · have hVμ := zero_of V μ (fun h => hμS (by
        rw [hS]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hUμ := zero_of U μ (fun h => hμS (by
        rw [hS]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ h)))
      have hWμ := zero_of W μ (fun h => hμS (by
        rw [hS]
        exact Finset.mem_union_right _ h))
      rw [hVμ, hUμ, hWμ]
  ext μ
  rw [MvPolynomial.coeff_add,
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter,
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter,
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.coeff_weightCharacter]
  rw [hdim μ]
  push_cast
  ring

omit [CharZero k] in
/-- A surjective equivariant linear map carries the property that all weight spaces span the representation to its target. -/
theorem iSup_weightSpaces_eq_top_of_surjective_equivariant (N : ℕ)
    (M P : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (φ : M →ₗ[k] P)
    (hφ : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : M),
      φ (M.ρ g v) = P.ρ g (φ v))
    (hsurj : Function.Surjective φ)
    (hM : ⨆ (μ : Fin N →₀ ℕ),
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M
        (fun i => μ i) = ⊤) :
    ⨆ (μ : Fin N →₀ ℕ),
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N P
        (fun i => μ i) = ⊤ := by
  have hmap : ∀ μ : Fin N →₀ ℕ,
      Submodule.map φ
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M
            (fun i => μ i)) ≤
        RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N P
          (fun i => μ i) := fun μ =>
    map_weightSpace_le_of_equivariant N M P φ hφ (fun i => μ i)
  rw [eq_top_iff, ← LinearMap.range_eq_top.mpr hsurj, ← Submodule.map_top, ← hM,
    Submodule.map_iSup]
  exact iSup_mono hmap

end GeneralLinearRepresentation

end RepresentationTheory.GeneralLinearRepresentation.WeightSpaceMorphisms
