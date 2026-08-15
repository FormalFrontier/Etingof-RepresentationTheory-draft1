/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial
import RepresentationTheory.SimpleModule.SubtypeRepresentation

/-!
# Partition components and traces

This module relates partition-indexed isotypic components and multiplicities to permutation
traces for finite-dimensional complex modules and representations.
-/

open RepresentationTheory.PartitionAuxiliary
open RepresentationTheory.SimpleModule.SubtypeRepresentation
open RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter

namespace RepresentationTheory.Module.PartitionComponentsAndTraces

universe u

variable (n : ℕ) (M : Type) [AddCommGroup M] [Module (natIndexedType n) M]
  [Module ℂ M] [IsScalarTower ℂ (natIndexedType n) M]

/-- The complex-linear endomorphism of a module associated with a permutation. -/
noncomputable def auxiliaryPermutationEndomorphism (σ : Equiv.Perm (Fin n)) : M →ₗ[ℂ] M where
  toFun v := (MonoidAlgebra.of ℂ _ σ : natIndexedType n) • v
  map_add' := smul_add _
  map_smul' c v := smul_comm _ c v

/-- The permutation endomorphism acts by scalar multiplication with the corresponding
monoid-algebra basis element. -/
@[simp] lemma auxiliaryPermutationEndomorphism_apply (σ : Equiv.Perm (Fin n)) (v : M) :
    auxiliaryPermutationEndomorphism n M σ v =
      (MonoidAlgebra.of ℂ _ σ : natIndexedType n) • v := rfl

/-- An auxiliary complex-valued function of permutations attached to a finite complex module. -/
noncomputable def auxiliaryPermutationTrace [Module.Finite ℂ M]
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  LinearMap.trace ℂ M (auxiliaryPermutationEndomorphism n M σ)

/-- An auxiliary complex submodule associated with a partition of `n`. -/
noncomputable def auxiliaryPartitionSubmodule (ν : Nat.Partition n) : Submodule ℂ M :=
  (isotypicComponent (natIndexedType n) M (partitionSubmodule n ν)).restrictScalars ℂ

/-- An auxiliary natural-number value attached to a module and a partition of `n`. -/
noncomputable def auxiliaryPartitionCount (ν : Nat.Partition n) : ℕ :=
  Module.finrank ℂ (auxiliaryPartitionSubmodule n M ν) /
    Module.finrank ℂ (partitionSubmodule n ν)

omit [Module ℂ M] [IsScalarTower ℂ (natIndexedType n) M] in
/-- Every simple submodule is linearly equivalent to the auxiliary subtype associated with some
partition. -/
theorem exists_partition_linearEquiv_of_simple_submodule
    (S : Submodule (natIndexedType n) M) [IsSimpleModule (natIndexedType n) S] :
    ∃ ν : Nat.Partition n,
      Nonempty (↥S ≃ₗ[natIndexedType n] ↥(partitionSubmodule n ν)) :=
  exists_linearEquiv_to_subtype n S

omit [Module ℂ M] [IsScalarTower ℂ (natIndexedType n) M] in
/-- The supremum of the partition-indexed isotypic components is the whole module. -/
theorem iSup_isotypicComponents_eq_top :
    ⨆ ν : Nat.Partition n,
      isotypicComponent (natIndexedType n) M (partitionSubmodule n ν) = ⊤ := by
  rw [eq_top_iff, ← sSup_isotypicComponents (natIndexedType n) M]
  apply sSup_le
  intro c hc
  obtain ⟨S, hS_simple, rfl⟩ := hc
  haveI := hS_simple
  obtain ⟨ν, ⟨e⟩⟩ := exists_partition_linearEquiv_of_simple_submodule n M S
  rw [e.isotypicComponent_eq]
  exact le_iSup
    (fun ν => isotypicComponent (natIndexedType n) M (partitionSubmodule n ν)) ν

set_option maxHeartbeats 800000 in
omit [IsScalarTower ℂ (natIndexedType n) M] in
/-- The isotypic components indexed by partitions form an independent indexed supremum. -/
theorem iSupIndep_isotypicComponents [Module.Finite ℂ M] :
    iSupIndep (fun ν : Nat.Partition n =>
      isotypicComponent (natIndexedType n) M (partitionSubmodule n ν)) := by
  have mem_of_ne_bot : ∀ ν,
      isotypicComponent (natIndexedType n) M (partitionSubmodule n ν) ≠ ⊥ →
      isotypicComponent (natIndexedType n) M (partitionSubmodule n ν) ∈
        isotypicComponents (natIndexedType n) M := by
    intro ν hbot
    obtain ⟨S, hS_le, hS_simple⟩ :=
      (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left hbot
    haveI := hS_simple
    haveI := partitionSubmodule_isSimpleModule n ν
    obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (natIndexedType n) M (partitionSubmodule n ν)) S
        hS_le
    exact ⟨S, hS_simple, e.symm.isotypicComponent_eq⟩
  rw [iSupIndep_def]
  intro ν
  by_cases hbot : isotypicComponent (natIndexedType n) M (partitionSubmodule n ν) = ⊥
  · simp [hbot]
  · apply (sSupIndep_isotypicComponents (natIndexedType n) M
      (mem_of_ne_bot ν hbot)).mono_right
    apply iSup₂_le
    intro ν' hne
    by_cases hbot' : isotypicComponent (natIndexedType n) M (partitionSubmodule n ν') = ⊥
    · simp [hbot']
    · have hne_val : isotypicComponent (natIndexedType n) M (partitionSubmodule n ν') ≠
          isotypicComponent (natIndexedType n) M (partitionSubmodule n ν) := by
        intro heq
        obtain ⟨S, hS_le, hS_simple⟩ :=
          (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left hbot
        haveI := hS_simple
        haveI := partitionSubmodule_isSimpleModule n ν
        haveI := partitionSubmodule_isSimpleModule n ν'
        obtain ⟨e₁⟩ := isIsotypicOfType_submodule_iff.mp
          (IsIsotypicOfType.isotypicComponent (natIndexedType n) M (partitionSubmodule n ν)) S
            hS_le
        obtain ⟨e₂⟩ := isIsotypicOfType_submodule_iff.mp
          (IsIsotypicOfType.isotypicComponent (natIndexedType n) M (partitionSubmodule n ν')) S
            (heq ▸ hS_le)
        exact (isEmpty_linearEquiv_of_ne n ν ν' hne.symm).false (e₁.symm.trans e₂)
      exact le_sSup ⟨mem_of_ne_bot ν' hbot', hne_val⟩

/-- The family of auxiliary partition submodules forms an internal direct sum. -/
theorem auxiliaryPartitionSubmodule_isInternal [Module.Finite ℂ M] :
    DirectSum.IsInternal (auxiliaryPartitionSubmodule n M) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · have h := iSupIndep_isotypicComponents n M
    rw [iSupIndep_def] at h ⊢
    intro ν
    simp only [auxiliaryPartitionSubmodule]
    specialize h ν
    rw [disjoint_iff] at h ⊢
    simp only [← Submodule.restrictScalars_iSup]
    rw [← Submodule.restrictScalars_inf, Submodule.restrictScalars_eq_bot_iff]
    exact h
  · change (⨆ ν, auxiliaryPartitionSubmodule n M ν) = ⊤
    simp only [auxiliaryPartitionSubmodule]
    rw [← Submodule.restrictScalars_iSup,
      show (⨆ ν, isotypicComponent (natIndexedType n) M (partitionSubmodule n ν)) =
        (⊤ : Submodule (natIndexedType n) M) from iSup_isotypicComponents_eq_top n M,
      Submodule.restrictScalars_top]

/-- Every auxiliary permutation endomorphism preserves each auxiliary partition submodule. -/
theorem auxiliaryPartitionSubmodule_mapsTo
    (σ : Equiv.Perm (Fin n)) (ν : Nat.Partition n) :
    Set.MapsTo (auxiliaryPermutationEndomorphism n M σ)
      ↑(auxiliaryPartitionSubmodule n M ν) ↑(auxiliaryPartitionSubmodule n M ν) := by
  intro v hv
  simp only [SetLike.mem_coe, auxiliaryPartitionSubmodule, Submodule.restrictScalars_mem] at hv ⊢
  change (MonoidAlgebra.of ℂ _ σ : natIndexedType n) • v ∈ _
  exact Submodule.smul_mem _ _ hv

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
    arg 2
    ext p
    rw [show pb p = Pi.single p.1 (b p.2) from Pi.basis_apply _ p]
  simp only [hg_single]
  have hrepr : ∀ (i : Fin m) (j : Module.Free.ChooseBasisIndex ℂ V),
      (pb.repr (Pi.single i (f (b j)))) ⟨i, j⟩ = (b.repr (f (b j))) j := by
    intro i j
    simp [pb, Pi.basis_repr, Pi.single_eq_same]
  simp_rw [hrepr]
  simp_rw [Fintype.sum_sigma, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

private theorem finrank_partitionSubmodule_dvd [Module.Finite ℂ M]
    (ν : Nat.Partition n) :
    Module.finrank ℂ (partitionSubmodule n ν) ∣
      Module.finrank ℂ (auxiliaryPartitionSubmodule n M ν) := by
  set A := natIndexedType n
  set C_R := isotypicComponent A M (partitionSubmodule n ν) with hCR_def
  letI : Module ℂ ↥C_R := (C_R.restrictScalars ℂ).module
  haveI iST : IsScalarTower ℂ A ↥C_R :=
    ⟨fun c a m => Subtype.ext (smul_assoc c a (m : M))⟩
  haveI : IsSimpleModule A ↥(partitionSubmodule n ν) := partitionSubmodule_isSimpleModule n ν
  have hiso : IsIsotypicOfType A C_R (partitionSubmodule n ν) :=
    IsIsotypicOfType.isotypicComponent _ _ _
  haveI : Module.Finite ℂ ↥C_R := by
    change Module.Finite ℂ ↥(C_R.restrictScalars ℂ)
    infer_instance
  haveI : Module.Finite A ↥C_R :=
    @Module.Finite.of_restrictScalars_finite ℂ A ↥C_R _ _ _ _ _ _ iST _
  obtain ⟨m', ⟨e'⟩⟩ := hiso.linearEquiv_fun
  let e'_ℂ : ↥C_R ≃ₗ[ℂ] (Fin m' → ↥(partitionSubmodule n ν)) :=
    { toFun := e', invFun := e'.symm, map_add' := e'.map_add,
      left_inv := e'.left_inv, right_inv := e'.right_inv,
      map_smul' := fun c x => e'.toLinearMap.map_smul_of_tower c x }
  refine ⟨m', ?_⟩
  have : Module.finrank ℂ (auxiliaryPartitionSubmodule n M ν) = Module.finrank ℂ ↥C_R := rfl
  rw [this, LinearEquiv.finrank_eq e'_ℂ, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_fin, smul_eq_mul, mul_comm]

/-- The complex finrank of an auxiliary partition submodule is its auxiliary count times the
finrank of the corresponding auxiliary subtype. -/
theorem finrank_auxiliaryPartitionSubmodule [Module.Finite ℂ M] (ν : Nat.Partition n) :
    Module.finrank ℂ (auxiliaryPartitionSubmodule n M ν) =
      auxiliaryPartitionCount n M ν * Module.finrank ℂ (partitionSubmodule n ν) := by
  rw [auxiliaryPartitionCount,
    Nat.div_mul_cancel (finrank_partitionSubmodule_dvd n M ν)]

/-- The trace of a permutation endomorphism restricted to an auxiliary partition submodule is the
auxiliary count times the associated complex value. -/
theorem auxiliary_trace_restrict_permutationEndomorphism_eq_count_mul_value
    [Module.Finite ℂ M] (σ : Equiv.Perm (Fin n)) (ν : Nat.Partition n) :
    LinearMap.trace ℂ _
        ((auxiliaryPermutationEndomorphism n M σ).restrict
          (auxiliaryPartitionSubmodule_mapsTo n M σ ν)) =
      (auxiliaryPartitionCount n M ν : ℂ) * auxiliaryPartitionPermutationValue n ν σ := by
  set A := natIndexedType n
  set C_R := isotypicComponent A M (partitionSubmodule n ν) with hCR_def
  letI : Module ℂ ↥C_R := (C_R.restrictScalars ℂ).module
  haveI iST : IsScalarTower ℂ A ↥C_R :=
    ⟨fun c a m => Subtype.ext (smul_assoc c a (m : M))⟩
  haveI : IsSimpleModule A ↥(partitionSubmodule n ν) := partitionSubmodule_isSimpleModule n ν
  have hiso : IsIsotypicOfType A C_R (partitionSubmodule n ν) :=
    IsIsotypicOfType.isotypicComponent _ _ _
  haveI : Module.Finite ℂ ↥C_R := by
    change Module.Finite ℂ ↥(C_R.restrictScalars ℂ)
    infer_instance
  haveI : Module.Finite A ↥C_R :=
    @Module.Finite.of_restrictScalars_finite ℂ A ↥C_R _ _ _ _ _ _ iST _
  obtain ⟨m', ⟨e'⟩⟩ := hiso.linearEquiv_fun
  let e'_ℂ : ↥C_R ≃ₗ[ℂ] (Fin m' → ↥(partitionSubmodule n ν)) :=
    { toFun := e', invFun := e'.symm, map_add' := e'.map_add,
      left_inv := e'.left_inv, right_inv := e'.right_inv,
      map_smul' := fun c x => e'.toLinearMap.map_smul_of_tower c x }
  set f := (auxiliaryPermutationEndomorphism n M σ).restrict
    (auxiliaryPartitionSubmodule_mapsTo n M σ ν) with hf_def
  have hconj_eq : ∀ v i, (e'_ℂ.conj f v) i = (MonoidAlgebra.of ℂ _ σ : A) • v i := by
    intro v i
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    have step : e'_ℂ (f (e'_ℂ.symm v)) = (MonoidAlgebra.of ℂ _ σ : A) • v :=
      show e' (f (e'.symm v)) = _ by
        rw [show (f (e'.symm v) : ↥C_R) =
              (MonoidAlgebra.of ℂ _ σ : A) • (e'.symm v) from Subtype.ext rfl,
          e'.map_smul, LinearEquiv.apply_symm_apply]
    exact congr_fun step i
  have hact : ∀ (v : ↥(partitionSubmodule n ν)),
      (MonoidAlgebra.of ℂ _ σ : A) • v = auxiliarySubtypePermutationEndomorphism n ν σ v := by
    intro ⟨m, hm⟩
    rfl
  have hconj_pi : e'_ℂ.conj f =
      LinearMap.pi (fun (i : Fin m') =>
        auxiliarySubtypePermutationEndomorphism n ν σ ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext
    intro w
    funext i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.proj_apply]
    rw [← hact]
    exact hconj_eq w i
  have htrace : LinearMap.trace ℂ _ f =
      (m' : ℂ) * LinearMap.trace ℂ _ (auxiliarySubtypePermutationEndomorphism n ν σ) := by
    calc
      LinearMap.trace ℂ _ f = LinearMap.trace ℂ _ (e'_ℂ.conj f) :=
        (LinearMap.trace_conj' f e'_ℂ).symm
      _ = LinearMap.trace ℂ _ (LinearMap.pi (fun (i : Fin m') =>
            auxiliarySubtypePermutationEndomorphism n ν σ ∘ₗ LinearMap.proj i)) := by
        rw [hconj_pi]
      _ = (m' : ℂ) *
          LinearMap.trace ℂ _ (auxiliarySubtypePermutationEndomorphism n ν σ) :=
        trace_pi_diag _
  rw [show auxiliaryPartitionPermutationValue n ν σ =
      LinearMap.trace ℂ _ (auxiliarySubtypePermutationEndomorphism n ν σ) from rfl, htrace]
  congr 1
  have hdim_e' : Module.finrank ℂ (auxiliaryPartitionSubmodule n M ν) =
      m' * Module.finrank ℂ ↥(partitionSubmodule n ν) := by
    have : Module.finrank ℂ (auxiliaryPartitionSubmodule n M ν) = Module.finrank ℂ ↥C_R := rfl
    rw [this, LinearEquiv.finrank_eq e'_ℂ, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_fin, smul_eq_mul]
  have hdim_mult := finrank_auxiliaryPartitionSubmodule n M ν
  haveI : Nontrivial ↥(partitionSubmodule n ν) :=
    IsSimpleModule.nontrivial (natIndexedType n) _
  have hpos : 0 < Module.finrank ℂ ↥(partitionSubmodule n ν) := Module.finrank_pos
  exact_mod_cast Nat.eq_of_mul_eq_mul_right hpos (hdim_e'.symm.trans hdim_mult)

/-- The auxiliary permutation trace is a sum over partitions of natural-number counts multiplied
by associated complex values. -/
theorem auxiliary_trace_eq_sum_partitionCounts_mul_values [Module.Finite ℂ M]
    (σ : Equiv.Perm (Fin n)) :
    auxiliaryPermutationTrace n M σ =
      ∑ ν : Nat.Partition n,
        (auxiliaryPartitionCount n M ν : ℂ) * auxiliaryPartitionPermutationValue n ν σ := by
  rw [auxiliaryPermutationTrace,
    LinearMap.trace_eq_sum_trace_restrict (auxiliaryPartitionSubmodule_isInternal n M)
      (auxiliaryPartitionSubmodule_mapsTo n M σ)]
  congr 1
  ext ν
  exact auxiliary_trace_restrict_permutationEndomorphism_eq_count_mul_value n M σ ν

/-- A nonzero auxiliary module count supplies an auxiliary map whose underlying function is
injective. -/
theorem auxiliary_exists_injective_map_of_partitionCount_ne_zero [Module.Finite ℂ M]
    (ν : Nat.Partition n) (h : auxiliaryPartitionCount n M ν ≠ 0) :
    ∃ f : ↥(partitionSubmodule n ν) →ₗ[natIndexedType n] M, Function.Injective f := by
  have hcomp_ne : isotypicComponent (natIndexedType n) M (partitionSubmodule n ν) ≠ ⊥ := by
    intro hbot
    apply h
    have hbot' : auxiliaryPartitionSubmodule n M ν = ⊥ := by
      simp only [auxiliaryPartitionSubmodule, hbot, Submodule.restrictScalars_bot]
    rw [auxiliaryPartitionCount, hbot', finrank_bot, Nat.zero_div]
  haveI := partitionSubmodule_isSimpleModule n ν
  obtain ⟨S, hS_le, hS_simple⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left hcomp_ne
  haveI := hS_simple
  obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent (natIndexedType n) M (partitionSubmodule n ν)) S
      hS_le
  refine ⟨S.subtype ∘ₗ
    (e.symm : ↥(partitionSubmodule n ν) →ₗ[natIndexedType n] ↥S), ?_⟩
  exact (Submodule.injective_subtype S).comp e.symm.injective

/-- A factorial multiple of an auxiliary partition count equals a sum of trace values weighted by
the associated value at inverse permutations. -/
theorem factorial_mul_auxiliaryPartitionCount_eq_sum_trace_mul_value_inv
    [Module.Finite ℂ M] (μ : Nat.Partition n) :
    (Nat.factorial n : ℂ) * (auxiliaryPartitionCount n M μ : ℂ) =
      ∑ σ : Equiv.Perm (Fin n),
        auxiliaryPermutationTrace n M σ * auxiliaryPartitionPermutationValue n μ σ⁻¹ := by
  simp_rw [auxiliary_trace_eq_sum_partitionCounts_mul_values n M, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ ν : Nat.Partition n,
      ∑ σ : Equiv.Perm (Fin n),
        (auxiliaryPartitionCount n M ν : ℂ) * auxiliaryPartitionPermutationValue n ν σ *
          auxiliaryPartitionPermutationValue n μ σ⁻¹ =
      (auxiliaryPartitionCount n M ν : ℂ) *
        ((Nat.factorial n : ℂ) * if ν = μ then 1 else 0) := by
    intro ν
    rw [← sum_auxiliaryPartitionPermutationValue_mul_inv n ν μ, Finset.mul_sum]
    congr 1
    ext σ
    ring
  simp_rw [this]
  rw [Finset.sum_eq_single μ]
  · simp [mul_comm]
  · intro ν _ hν
    simp [hν]
  · intro h
    exact absurd (Finset.mem_univ μ) h

/-- Finite modules with equal auxiliary permutation traces have equal auxiliary counts at every
partition. -/
theorem auxiliaryPartitionCount_eq_of_trace_eq
    {M' : Type} [AddCommGroup M'] [Module (natIndexedType n) M'] [Module ℂ M']
    [IsScalarTower ℂ (natIndexedType n) M'] [Module.Finite ℂ M] [Module.Finite ℂ M']
    (h : ∀ σ, auxiliaryPermutationTrace n M σ = auxiliaryPermutationTrace n M' σ)
    (ν : Nat.Partition n) :
    auxiliaryPartitionCount n M ν = auxiliaryPartitionCount n M' ν := by
  have hfac : (Nat.factorial n : ℂ) * (auxiliaryPartitionCount n M ν : ℂ) =
      (Nat.factorial n : ℂ) * (auxiliaryPartitionCount n M' ν : ℂ) := by
    rw [factorial_mul_auxiliaryPartitionCount_eq_sum_trace_mul_value_inv n M ν,
      factorial_mul_auxiliaryPartitionCount_eq_sum_trace_mul_value_inv n M' ν]
    exact Finset.sum_congr rfl (fun σ _ => by rw [h σ])
  have hne : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  exact_mod_cast mul_left_cancel₀ hne hfac

variable {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)

/-- An auxiliary natural-number value attached to a permutation representation and a partition. -/
noncomputable def auxiliaryRepresentationPartitionCount (ν : Nat.Partition n) : ℕ :=
  auxiliaryPartitionCount n ρ.asModule ν

/-- For the module induced by a representation, the auxiliary permutation endomorphism is
evaluation of that representation. -/
theorem auxiliaryPermutationEndomorphism_asModule (σ : Equiv.Perm (Fin n)) :
    auxiliaryPermutationEndomorphism n ρ.asModule σ = ρ σ := by
  apply LinearMap.ext
  intro x
  change (MonoidAlgebra.of ℂ _ σ : natIndexedType n) • x = ρ σ x
  rw [← Representation.asAlgebraHom_of ρ σ]
  rfl

/-- The trace of a finite-dimensional representation at a permutation equals the auxiliary trace
of its induced module. -/
theorem representation_trace_eq_auxiliaryPermutationTrace [Module.Finite ℂ V]
    (σ : Equiv.Perm (Fin n)) :
    LinearMap.trace ℂ V (ρ σ) = auxiliaryPermutationTrace n ρ.asModule σ := by
  rw [auxiliaryPermutationTrace, auxiliaryPermutationEndomorphism_asModule n ρ]
  rfl

/-- The trace of a finite-dimensional permutation representation is a partition sum of auxiliary
counts times associated values. -/
theorem representation_trace_eq_sum_partitionCounts_mul_values [Module.Finite ℂ V]
    (σ : Equiv.Perm (Fin n)) :
    LinearMap.trace ℂ V (ρ σ) =
      ∑ ν : Nat.Partition n,
        (auxiliaryRepresentationPartitionCount n ρ ν : ℂ) *
          auxiliaryPartitionPermutationValue n ν σ := by
  rw [representation_trace_eq_auxiliaryPermutationTrace n ρ,
    auxiliary_trace_eq_sum_partitionCounts_mul_values n ρ.asModule]
  rfl

/-- A nonzero auxiliary representation count supplies an auxiliary map whose underlying function
is injective. -/
theorem auxiliary_exists_injective_map_of_representationPartitionCount_ne_zero
    [Module.Finite ℂ V] (ν : Nat.Partition n)
    (h : auxiliaryRepresentationPartitionCount n ρ ν ≠ 0) :
    ∃ f : ↥(partitionSubmodule n ν) →ₗ[natIndexedType n] ρ.asModule,
      Function.Injective f :=
  auxiliary_exists_injective_map_of_partitionCount_ne_zero n ρ.asModule ν h

/-- Finite-dimensional permutation representations with identical traces have equal auxiliary
natural-number values at every partition. -/
theorem auxiliaryRepresentationPartitionCount_eq_of_trace_eq
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ' : Representation ℂ (Equiv.Perm (Fin n)) W)
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (h : ∀ σ, LinearMap.trace ℂ V (ρ σ) = LinearMap.trace ℂ W (ρ' σ))
    (ν : Nat.Partition n) :
    auxiliaryRepresentationPartitionCount n ρ ν =
      auxiliaryRepresentationPartitionCount n ρ' ν :=
  auxiliaryPartitionCount_eq_of_trace_eq n ρ.asModule
    (fun σ => by
      rw [← representation_trace_eq_auxiliaryPermutationTrace n ρ,
        ← representation_trace_eq_auxiliaryPermutationTrace n ρ', h σ]) ν

end RepresentationTheory.Module.PartitionComponentsAndTraces
