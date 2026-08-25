import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_15_1
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Classification

/-!
# From character to multiplicity for `Sₙ`-representations

The concrete Young-module setting of `Theorem5_15_1.lean` establishes the isotypic
decomposition and the character identity (Young's rule) for the permutation modules
`PermutationModule n μ`.  This file lifts that machinery to an arbitrary finite
dimensional `SymGroupAlgebra n`-module `M` (equivalently, a finite dimensional
`Sₙ`-representation).

The main results:

* `Etingof.isotypicMult n M ν`: the multiplicity of the Specht module `V_ν` in `M`,
  read off from the isotypic component.
* `Etingof.character_eq_sum_mult_spechtCharacter`: the character of `M` decomposes as
  `χ_M(σ) = Σ_ν (isotypicMult n M ν) · χ_{V_ν}(σ)`.
* `Etingof.specht_embeds_of_mult_pos`: a positive multiplicity produces an injective
  `Sₙ`-embedding `V_ν ↪ M`.
* `Etingof.factorial_mul_isotypicMult` / `Etingof.isotypicMult_eq_of_character_eq`: the
  multiplicity is recovered from the character by orthonormality of Specht characters, so
  two modules with equal character have the same multiplicities.

The `Representation`-level wrappers `Etingof.repCharacter_eq_sum_mult_spechtCharacter`
etc. specialise these to a bare `ρ : Representation ℂ (Equiv.Perm (Fin n)) V`.

The proofs mirror the `PermutationModule` template of `Theorem5_15_1.lean`; the only
`M`-specific inputs are semisimplicity of `M` (Maschke) and the classification of simple
`Sₙ`-modules (`Theorem5_12_2_classification`).
-/

namespace Etingof

universe u

variable (n : ℕ) (M : Type) [AddCommGroup M] [Module (SymGroupAlgebra n) M]
  [Module ℂ M] [IsScalarTower ℂ (SymGroupAlgebra n) M]

/-- The `ℂ`-linear endomorphism of a `SymGroupAlgebra n`-module `M` given by
multiplication by the group element `σ`, i.e. by `MonoidAlgebra.of ℂ _ σ`.  This is the
"action of `σ`" on `M`; its trace is the character value `χ_M(σ)`. -/
noncomputable def moduleEnd (σ : Equiv.Perm (Fin n)) : M →ₗ[ℂ] M where
  toFun v := (MonoidAlgebra.of ℂ _ σ : SymGroupAlgebra n) • v
  map_add' := smul_add _
  map_smul' c v := smul_comm _ c v

@[simp] lemma moduleEnd_apply (σ : Equiv.Perm (Fin n)) (v : M) :
    moduleEnd n M σ v = (MonoidAlgebra.of ℂ _ σ : SymGroupAlgebra n) • v := rfl

/-- The character of a finite dimensional `Sₙ`-module `M` at `σ`: the trace of the
`σ`-action `moduleEnd`. -/
noncomputable def moduleCharacter [Module.Finite ℂ M] (σ : Equiv.Perm (Fin n)) : ℂ :=
  LinearMap.trace ℂ M (moduleEnd n M σ)

/-- The `V_ν`-isotypic component of `M`, viewed as a `ℂ`-subspace (`restrictScalars`). -/
noncomputable def isotypicComp (ν : Nat.Partition n) : Submodule ℂ M :=
  (isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν)).restrictScalars ℂ

/-- The multiplicity of the Specht module `V_ν` in `M`: the number of copies of `V_ν`
in the isotypic component, recovered as `dim_ℂ (isotypic component) / dim_ℂ V_ν`. -/
noncomputable def isotypicMult (ν : Nat.Partition n) : ℕ :=
  Module.finrank ℂ (isotypicComp n M ν) / Module.finrank ℂ (SpechtModule n ν)

/-! ### Isotypic decomposition of a general module -/

omit [Module ℂ M] [IsScalarTower ℂ (SymGroupAlgebra n) M] in
/-- Every simple submodule of a finite dimensional `Sₙ`-module is a Specht module
(the classification, applied to submodules of `M`). -/
theorem gen_spechtModules_exhaust_simples
    (S : Submodule (SymGroupAlgebra n) M) [IsSimpleModule (SymGroupAlgebra n) S] :
    ∃ ν : Nat.Partition n, Nonempty (↥S ≃ₗ[SymGroupAlgebra n] ↥(SpechtModule n ν)) :=
  Theorem5_12_2_classification n S

omit [Module ℂ M] [IsScalarTower ℂ (SymGroupAlgebra n) M] in
/-- The isotypic components indexed by partitions span all of `M`. -/
theorem gen_iSup_isotypicComponent_eq_top :
    ⨆ ν : Nat.Partition n,
      isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν) = ⊤ := by
  rw [eq_top_iff, ← sSup_isotypicComponents (SymGroupAlgebra n) M]
  apply sSup_le
  intro c hc
  obtain ⟨S, hS_simple, rfl⟩ := hc
  haveI := hS_simple
  obtain ⟨ν, ⟨e⟩⟩ := gen_spechtModules_exhaust_simples n M S
  rw [e.isotypicComponent_eq]
  exact le_iSup (fun ν => isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν)) ν

set_option maxHeartbeats 800000 in
-- Comparing nested isotypic components requires expensive module-instance normalization.
omit [IsScalarTower ℂ (SymGroupAlgebra n) M] in
/-- The indexed family of isotypic components is `iSup`-independent. -/
theorem gen_iSupIndep_isotypicComponent [Module.Finite ℂ M] :
    iSupIndep (fun ν : Nat.Partition n =>
      isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν)) := by
  have mem_of_ne_bot : ∀ ν,
      isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν) ≠ ⊥ →
      isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν) ∈
        isotypicComponents (SymGroupAlgebra n) M := by
    intro ν hbot
    obtain ⟨S, hS_le, hS_simple⟩ :=
      (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left hbot
    haveI := hS_simple
    haveI := Theorem5_12_2_irreducible n ν
    obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν)) S hS_le
    exact ⟨S, hS_simple, e.symm.isotypicComponent_eq⟩
  rw [iSupIndep_def]
  intro ν
  by_cases hbot : isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν) = ⊥
  · simp [hbot]
  · apply (sSupIndep_isotypicComponents (SymGroupAlgebra n) M
      (mem_of_ne_bot ν hbot)).mono_right
    apply iSup₂_le
    intro ν' hne
    by_cases hbot' : isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν') = ⊥
    · simp [hbot']
    · have hne_val : isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν') ≠
          isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν) := by
        intro heq
        obtain ⟨S, hS_le, hS_simple⟩ :=
          (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left hbot
        haveI := hS_simple
        haveI := Theorem5_12_2_irreducible n ν
        haveI := Theorem5_12_2_irreducible n ν'
        obtain ⟨e₁⟩ := isIsotypicOfType_submodule_iff.mp
          (IsIsotypicOfType.isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν))
          S hS_le
        obtain ⟨e₂⟩ := isIsotypicOfType_submodule_iff.mp
          (IsIsotypicOfType.isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν'))
          S (heq ▸ hS_le)
        exact (spechtModule_noniso n ν ν' hne.symm).false (e₁.symm.trans e₂)
      exact le_sSup ⟨mem_of_ne_bot ν' hbot', hne_val⟩

/-- The `ℂ`-subspaces `isotypicComp n M ν` form an internal direct sum decomposition
of `M`.  This is the general form of `permModule_isotypic_isInternal`. -/
theorem isotypicComp_isInternal [Module.Finite ℂ M] :
    DirectSum.IsInternal (isotypicComp n M) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · have h := gen_iSupIndep_isotypicComponent n M
    rw [iSupIndep_def] at h ⊢
    intro ν
    simp only [isotypicComp]
    specialize h ν
    rw [disjoint_iff] at h ⊢
    simp only [← Submodule.restrictScalars_iSup]
    rw [← Submodule.restrictScalars_inf, Submodule.restrictScalars_eq_bot_iff]
    exact h
  · change (⨆ ν, isotypicComp n M ν) = ⊤
    simp only [isotypicComp]
    rw [← Submodule.restrictScalars_iSup,
      show (⨆ ν, isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν)) =
        (⊤ : Submodule (SymGroupAlgebra n) M) from gen_iSup_isotypicComponent_eq_top n M,
      Submodule.restrictScalars_top]

/-- `moduleEnd σ` maps each isotypic component into itself (it is `A`-multiplication by
`of σ`, and isotypic components are `A`-submodules). -/
theorem moduleEnd_mapsTo (σ : Equiv.Perm (Fin n)) (ν : Nat.Partition n) :
    Set.MapsTo (moduleEnd n M σ) ↑(isotypicComp n M ν) ↑(isotypicComp n M ν) := by
  intro v hv
  simp only [SetLike.mem_coe, isotypicComp, Submodule.restrictScalars_mem] at hv ⊢
  change (MonoidAlgebra.of ℂ _ σ : SymGroupAlgebra n) • v ∈ _
  exact Submodule.smul_mem _ _ hv

/-! ### Trace of the action on an isotypic component -/

/-- Trace of a componentwise endomorphism on `Fin m → V` equals `m · trace(f)`. -/
private theorem trace_pi_diag {m : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Module.Free ℂ V]
    (f : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ _ (LinearMap.pi (fun (i : Fin m) => f ∘ₗ LinearMap.proj i)) =
      (m : ℂ) * LinearMap.trace ℂ _ f := by
  set g := LinearMap.pi (fun (i : Fin m) => f ∘ₗ LinearMap.proj i)
  have hg_single : ∀ (i : Fin m) (v : V), g (Pi.single i v) = Pi.single i (f v) := by
    intro i v
    ext k
    simp only [g, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Pi.single_apply]
    split <;> simp [*]
  set b := Module.Free.chooseBasis ℂ V
  haveI : Fintype (Module.Free.ChooseBasisIndex ℂ V) :=
    FiniteDimensional.fintypeBasisIndex b
  set pb := Pi.basis (fun (_ : Fin m) => b)
  rw [LinearMap.trace_eq_matrix_trace ℂ pb g, LinearMap.trace_eq_matrix_trace ℂ b f]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  conv_lhs =>
    arg 2; ext p
    rw [show pb (p) = Pi.single p.1 (b p.2) from Pi.basis_apply _ p]
  simp only [hg_single]
  have hrepr : ∀ (i : Fin m) (j : Module.Free.ChooseBasisIndex ℂ V),
      (pb.repr (Pi.single i (f (b j)))) ⟨i, j⟩ = (b.repr (f (b j))) j := by
    intro i j
    simp [pb, Pi.basis_repr, Pi.single_eq_same]
  simp_rw [hrepr]
  simp_rw [Fintype.sum_sigma, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

/-- Divisibility `dim V_ν ∣ dim (isotypic component)`, witnessing that the component is a
direct sum of copies of `V_ν`. -/
private theorem finrank_spechtModule_dvd [Module.Finite ℂ M] (ν : Nat.Partition n) :
    Module.finrank ℂ (SpechtModule n ν) ∣ Module.finrank ℂ (isotypicComp n M ν) := by
  set A := SymGroupAlgebra n
  set C_R := isotypicComponent A M (SpechtModule n ν) with hCR_def
  letI : Module ℂ ↥C_R := (C_R.restrictScalars ℂ).module
  haveI : IsScalarTower ℂ A ↥C_R := ⟨fun c a m => Subtype.ext (smul_assoc c a (m : M))⟩
  haveI : IsSimpleModule A ↥(SpechtModule n ν) := Theorem5_12_2_irreducible n ν
  have hiso : IsIsotypicOfType A C_R (SpechtModule n ν) :=
    IsIsotypicOfType.isotypicComponent _ _ _
  haveI : Module.Finite ℂ ↥C_R := by
    change Module.Finite ℂ ↥(C_R.restrictScalars ℂ); infer_instance
  haveI : Module.Finite A ↥C_R := Module.Finite.of_restrictScalars_finite ℂ A ↥C_R
  obtain ⟨m', ⟨e'⟩⟩ := hiso.linearEquiv_fun
  let e'_ℂ : ↥C_R ≃ₗ[ℂ] (Fin m' → ↥(SpechtModule n ν)) := e'.restrictScalars ℂ
  refine ⟨m', ?_⟩
  have : Module.finrank ℂ (isotypicComp n M ν) = Module.finrank ℂ ↥C_R := rfl
  rw [this, LinearEquiv.finrank_eq e'_ℂ, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_fin, smul_eq_mul, mul_comm]

/-- `dim (isotypic component) = isotypicMult · dim V_ν`. -/
theorem isotypicComp_finrank [Module.Finite ℂ M] (ν : Nat.Partition n) :
    Module.finrank ℂ (isotypicComp n M ν)
      = isotypicMult n M ν * Module.finrank ℂ (SpechtModule n ν) := by
  rw [isotypicMult, Nat.div_mul_cancel (finrank_spechtModule_dvd n M ν)]

/-- The trace of `σ` on the `V_ν`-isotypic component equals
`isotypicMult · χ_{V_ν}(σ)`. -/
theorem trace_isotypicComp_eq [Module.Finite ℂ M]
    (σ : Equiv.Perm (Fin n)) (ν : Nat.Partition n) :
    LinearMap.trace ℂ _ ((moduleEnd n M σ).restrict (moduleEnd_mapsTo n M σ ν)) =
      (isotypicMult n M ν : ℂ) * spechtModuleCharacter n ν σ := by
  set A := SymGroupAlgebra n
  set C_R := isotypicComponent A M (SpechtModule n ν) with hCR_def
  letI : Module ℂ ↥C_R := (C_R.restrictScalars ℂ).module
  haveI : IsScalarTower ℂ A ↥C_R := ⟨fun c a m => Subtype.ext (smul_assoc c a (m : M))⟩
  haveI : IsSimpleModule A ↥(SpechtModule n ν) := Theorem5_12_2_irreducible n ν
  have hiso : IsIsotypicOfType A C_R (SpechtModule n ν) :=
    IsIsotypicOfType.isotypicComponent _ _ _
  haveI : Module.Finite ℂ ↥C_R := by
    change Module.Finite ℂ ↥(C_R.restrictScalars ℂ); infer_instance
  haveI : Module.Finite A ↥C_R := Module.Finite.of_restrictScalars_finite ℂ A ↥C_R
  obtain ⟨m', ⟨e'⟩⟩ := hiso.linearEquiv_fun
  let e'_ℂ : ↥C_R ≃ₗ[ℂ] (Fin m' → ↥(SpechtModule n ν)) := e'.restrictScalars ℂ
  set f := (moduleEnd n M σ).restrict (moduleEnd_mapsTo n M σ ν) with hf_def
  -- The conjugated endomorphism is componentwise `of σ` action.
  have hconj_eq : ∀ v i, (e'_ℂ.conj f v) i = (MonoidAlgebra.of ℂ _ σ : A) • v i := by
    intro v i
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    have step : e'_ℂ (f (e'_ℂ.symm v)) = (MonoidAlgebra.of ℂ _ σ : A) • v :=
      show e' (f (e'.symm v)) = _ by
        rw [show (f (e'.symm v) : ↥C_R) = (MonoidAlgebra.of ℂ _ σ : A) • (e'.symm v) from
            Subtype.ext rfl,
          e'.map_smul, LinearEquiv.apply_symm_apply]
    exact congr_fun step i
  have hact : ∀ (v : ↥(SpechtModule n ν)),
      (MonoidAlgebra.of ℂ _ σ : A) • v = spechtModuleAction n ν σ v := by
    intro ⟨m, hm⟩; rfl
  have hconj_pi : e'_ℂ.conj f =
      LinearMap.pi (fun (i : Fin m') => spechtModuleAction n ν σ ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext; intro w; funext i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply]
    rw [← hact]; exact hconj_eq w i
  have htrace : LinearMap.trace ℂ _ f =
      (m' : ℂ) * LinearMap.trace ℂ _ (spechtModuleAction n ν σ) := by
    calc LinearMap.trace ℂ _ f
        = LinearMap.trace ℂ _ (e'_ℂ.conj f) := (LinearMap.trace_conj' f e'_ℂ).symm
      _ = LinearMap.trace ℂ _ (LinearMap.pi (fun (i : Fin m') =>
            spechtModuleAction n ν σ ∘ₗ LinearMap.proj i)) := by rw [hconj_pi]
      _ = (m' : ℂ) * LinearMap.trace ℂ _ (spechtModuleAction n ν σ) := trace_pi_diag _
  rw [show spechtModuleCharacter n ν σ =
      LinearMap.trace ℂ _ (spechtModuleAction n ν σ) from rfl, htrace]
  congr 1
  -- `m' = isotypicMult` via finrank comparison.
  have hdim_e' : Module.finrank ℂ (isotypicComp n M ν) =
      m' * Module.finrank ℂ ↥(SpechtModule n ν) := by
    have : Module.finrank ℂ (isotypicComp n M ν) = Module.finrank ℂ ↥C_R := rfl
    rw [this, LinearEquiv.finrank_eq e'_ℂ, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_fin, smul_eq_mul]
  have hdim_mult := isotypicComp_finrank n M ν
  haveI : Nontrivial ↥(SpechtModule n ν) := IsSimpleModule.nontrivial (SymGroupAlgebra n) _
  have hpos : 0 < Module.finrank ℂ ↥(SpechtModule n ν) := Module.finrank_pos
  exact_mod_cast Nat.eq_of_mul_eq_mul_right hpos (hdim_e'.symm.trans hdim_mult)

/-! ### Character decomposition -/

/-- **Character-to-multiplicity decomposition.**  The character of a finite dimensional
`Sₙ`-module `M` decomposes over the Specht characters with the isotypic multiplicities:
`χ_M(σ) = Σ_ν (isotypicMult n M ν) · χ_{V_ν}(σ)`. -/
theorem character_eq_sum_mult_spechtCharacter [Module.Finite ℂ M]
    (σ : Equiv.Perm (Fin n)) :
    moduleCharacter n M σ =
      ∑ ν : Nat.Partition n, (isotypicMult n M ν : ℂ) * spechtModuleCharacter n ν σ := by
  rw [moduleCharacter, LinearMap.trace_eq_sum_trace_restrict (isotypicComp_isInternal n M)
    (moduleEnd_mapsTo n M σ)]
  congr 1; ext ν
  exact trace_isotypicComp_eq n M σ ν

/-! ### Positive multiplicity gives an embedding -/

/-- A positive multiplicity `isotypicMult n M ν ≠ 0` produces an injective
`Sₙ`-linear embedding `V_ν ↪ M`. -/
theorem specht_embeds_of_mult_pos [Module.Finite ℂ M] (ν : Nat.Partition n)
    (h : isotypicMult n M ν ≠ 0) :
    ∃ f : ↥(SpechtModule n ν) →ₗ[SymGroupAlgebra n] M, Function.Injective f := by
  -- Positive multiplicity ⇒ the isotypic component is nonzero.
  have hcomp_ne : isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν) ≠ ⊥ := by
    intro hbot
    apply h
    have hbot' : isotypicComp n M ν = ⊥ := by
      simp only [isotypicComp, hbot, Submodule.restrictScalars_bot]
    rw [isotypicMult, hbot', finrank_bot, Nat.zero_div]
  haveI := Theorem5_12_2_irreducible n ν
  -- Extract a simple submodule of the component and identify it with `V_ν`.
  obtain ⟨S, hS_le, hS_simple⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left hcomp_ne
  haveI := hS_simple
  obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent (SymGroupAlgebra n) M (SpechtModule n ν)) S hS_le
  -- `V_ν ≃ S ↪ M`.
  refine ⟨S.subtype ∘ₗ (e.symm : ↥(SpechtModule n ν) →ₗ[SymGroupAlgebra n] ↥S), ?_⟩
  exact (Submodule.injective_subtype S).comp e.symm.injective

/-! ### Multiplicities are determined by the character -/

/-- Recovery of a single multiplicity from the character via orthonormality of Specht
characters: `n! · isotypicMult n M μ = Σ_σ χ_M(σ) · χ_{V_μ}(σ⁻¹)`. -/
theorem factorial_mul_isotypicMult [Module.Finite ℂ M] (μ : Nat.Partition n) :
    (Nat.factorial n : ℂ) * (isotypicMult n M μ : ℂ) =
      ∑ σ : Equiv.Perm (Fin n),
        moduleCharacter n M σ * spechtModuleCharacter n μ σ⁻¹ := by
  simp_rw [character_eq_sum_mult_spechtCharacter n M, Finset.sum_mul]
  rw [Finset.sum_comm]
  -- inner sum over σ of (mult_ν χ_ν(σ)) χ_μ(σ⁻¹) = mult_ν · (n! δ)
  have : ∀ ν : Nat.Partition n,
      ∑ σ : Equiv.Perm (Fin n),
        (isotypicMult n M ν : ℂ) * spechtModuleCharacter n ν σ *
          spechtModuleCharacter n μ σ⁻¹ =
      (isotypicMult n M ν : ℂ) *
        ((Nat.factorial n : ℂ) * if ν = μ then 1 else 0) := by
    intro ν
    rw [← specht_char_inner n ν μ, Finset.mul_sum]
    congr 1; ext σ; ring
  simp_rw [this]
  rw [Finset.sum_eq_single μ]
  · simp [mul_comm]
  · intro ν _ hν; simp [hν]
  · intro h; exact absurd (Finset.mem_univ μ) h

/-- Two finite dimensional `Sₙ`-modules with equal character have equal multiplicities. -/
theorem isotypicMult_eq_of_character_eq {M' : Type} [AddCommGroup M']
    [Module (SymGroupAlgebra n) M'] [Module ℂ M'] [IsScalarTower ℂ (SymGroupAlgebra n) M']
    [Module.Finite ℂ M] [Module.Finite ℂ M']
    (h : ∀ σ, moduleCharacter n M σ = moduleCharacter n M' σ) (ν : Nat.Partition n) :
    isotypicMult n M ν = isotypicMult n M' ν := by
  have hfac : (Nat.factorial n : ℂ) * (isotypicMult n M ν : ℂ) =
      (Nat.factorial n : ℂ) * (isotypicMult n M' ν : ℂ) := by
    rw [factorial_mul_isotypicMult n M ν, factorial_mul_isotypicMult n M' ν]
    exact Finset.sum_congr rfl (fun σ _ => by rw [h σ])
  have hne : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  exact_mod_cast mul_left_cancel₀ hne hfac

/-! ### `Representation`-level wrappers

For a bare `ρ : Representation ℂ (Equiv.Perm (Fin n)) V` the character at `σ` is
`LinearMap.trace ℂ V (ρ σ)`, and its `ρ.asModule` is a `SymGroupAlgebra n`-module to which
all the results above apply.  `repIsotypicMult ρ ν` is the multiplicity of `V_ν` in `ρ`. -/

variable {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)

/-- Multiplicity of the Specht module `V_ν` in the representation `ρ`. -/
noncomputable def repIsotypicMult (ν : Nat.Partition n) : ℕ :=
  isotypicMult n ρ.asModule ν

/-- On `ρ.asModule`, the `σ`-action `moduleEnd` is just `ρ σ`. -/
theorem moduleEnd_asModule_eq (σ : Equiv.Perm (Fin n)) :
    moduleEnd n ρ.asModule σ = ρ σ := by
  apply LinearMap.ext; intro x
  change (MonoidAlgebra.of ℂ _ σ : SymGroupAlgebra n) • x = ρ σ x
  rw [← Representation.asAlgebraHom_of ρ σ]; rfl

/-- The character `trace(ρ σ)` equals the `ρ.asModule` character. -/
theorem repCharacter_eq_moduleCharacter [Module.Finite ℂ V] (σ : Equiv.Perm (Fin n)) :
    LinearMap.trace ℂ V (ρ σ) = moduleCharacter n ρ.asModule σ := by
  rw [moduleCharacter, moduleEnd_asModule_eq n ρ]; rfl

/-- **Character-to-multiplicity decomposition for representations.** The character of `ρ`
decomposes over the Specht characters with the isotypic multiplicities. -/
theorem repCharacter_eq_sum_mult_spechtCharacter [Module.Finite ℂ V]
    (σ : Equiv.Perm (Fin n)) :
    LinearMap.trace ℂ V (ρ σ) =
      ∑ ν : Nat.Partition n, (repIsotypicMult n ρ ν : ℂ) * spechtModuleCharacter n ν σ := by
  rw [repCharacter_eq_moduleCharacter n ρ, character_eq_sum_mult_spechtCharacter n ρ.asModule]
  rfl

/-- A positive multiplicity gives an injective `Sₙ`-embedding `V_ν ↪ ρ.asModule`. -/
theorem repSpecht_embeds_of_mult_pos [Module.Finite ℂ V] (ν : Nat.Partition n)
    (h : repIsotypicMult n ρ ν ≠ 0) :
    ∃ f : ↥(SpechtModule n ν) →ₗ[SymGroupAlgebra n] ρ.asModule, Function.Injective f :=
  specht_embeds_of_mult_pos n ρ.asModule ν h

/-- Two representations with equal character have equal multiplicities. -/
theorem repIsotypicMult_eq_of_character_eq {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ' : Representation ℂ (Equiv.Perm (Fin n)) W)
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (h : ∀ σ, LinearMap.trace ℂ V (ρ σ) = LinearMap.trace ℂ W (ρ' σ))
    (ν : Nat.Partition n) :
    repIsotypicMult n ρ ν = repIsotypicMult n ρ' ν :=
  isotypicMult_eq_of_character_eq n ρ.asModule
    (fun σ => by
      rw [← repCharacter_eq_moduleCharacter n ρ, ← repCharacter_eq_moduleCharacter n ρ', h σ]) ν

end Etingof
