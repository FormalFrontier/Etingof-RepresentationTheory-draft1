/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import RepresentationTheory.LinearAlgebra.SubalgebraCentralizerRange
import RepresentationTheory.SymmetricGroup.SimpleModuleTrace
import RepresentationTheory.TensorPower
import RepresentationTheory.Auxiliary.MutualCentralizers
import RepresentationTheory.GeneralLinearGroup.WeightCharacter

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace RepresentationTheory.GeneralLinear.InvariantSubtype

open scoped TensorProduct

open RepresentationTheory.Auxiliary.MutualCentralizers
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.LinearAlgebra.SubalgebraCentralizerRange
open RepresentationTheory.SymmetricGroup.PartitionScalarAuxiliary
open RepresentationTheory.SymmetricGroup.SimpleModuleTrace
open RepresentationTheory.TensorPower

namespace GeneralLinear

variable (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]

noncomputable local instance (priority := high) permutationActionAlgebraRing
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (n : ℕ) :
    Ring (permutationActionAlgebra k V n) := (permutationActionAlgebra k V n).toRing

noncomputable local instance (priority := high) auxiliaryEndomorphismAlgebraRing
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (n : ℕ) :
    Ring (auxiliaryEndomorphismAlgebra k V n) :=
  (auxiliaryEndomorphismAlgebra k V n).toRing

noncomputable local instance (priority := high) centralizerRing
    {k : Type*} [Field k] {E : Type*} [AddCommGroup E] [Module k E]
    (A : Subalgebra k (Module.End k E)) :
    Ring (Subalgebra.centralizer k (A : Set (Module.End k E))) :=
  (Subalgebra.centralizer k (A : Set (Module.End k E))).toRing

noncomputable local instance (priority := high) centralizerRangeAddCommGroup
    {k : Type*} [Field k] {E : Type*} [AddCommGroup E] [Module k E]
    {A : Subalgebra k (Module.End k E)} (c : ↥A) :
    AddCommGroup (subalgebraCentralizerSubmodule c) :=
  { Module.addCommMonoidToAddCommGroup
      (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) with
    toAddCommMonoid := (subalgebraCentralizerSubmodule c).addCommMonoid }

noncomputable local instance (priority := high) invariantSubtypeAddCommGroup
    (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    AddCommGroup (schurSubmodule k N lam) :=
  { Module.addCommMonoidToAddCommGroup k with
    toAddCommMonoid := (schurSubmodule k N lam).addCommMonoid }

/-- Applying an element of the acting subtype preserves membership in the invariant subtype. -/
theorem actingSubtype_apply_mem (N : ℕ) (lam : Fin N → ℕ)
    (b : ↥(auxiliaryEndomorphismAlgebra k (Fin N → k) (∑ i, lam i)))
    {v : auxiliarySpace k (Fin N → k) (∑ i, lam i)}
    (hv : v ∈ schurSubmodule k N lam) :
    b.val v ∈ schurSubmodule k N lam := by
  obtain ⟨w, rfl⟩ := hv
  have hb := auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra
    k (Fin N → k) (∑ i, lam i) b.property
  rw [Subalgebra.mem_centralizer_iff] at hb
  have h_symmetrizer :
      (symmetrizerEndomorphism k N lam :
        Module.End k (auxiliarySpace k (Fin N → k) (∑ i, lam i))) ∈
        permutationActionAlgebra k (Fin N → k) (∑ i, lam i) :=
    (symmetrizerEndomorphismMem k N lam).property
  have h_comm := hb _ h_symmetrizer
  refine ⟨b.val w, ?_⟩
  exact LinearMap.congr_fun h_comm w

/-- The acting subtype acts by scalar multiplication on the invariant subtype. -/
noncomputable instance actingSubtypeSMul
    (N : ℕ) (lam : Fin N → ℕ) :
    SMul (↥(auxiliaryEndomorphismAlgebra k (Fin N → k) (∑ i, lam i)))
      (schurSubmodule k N lam) where
  smul b v := ⟨b.val v.val, actingSubtype_apply_mem k N lam b v.property⟩

/-- Coercing the scalar action of the acting subtype agrees with applying its underlying map. -/
@[simp]
lemma actingSubtype_smul_coe
    (N : ℕ) (lam : Fin N → ℕ)
    (b : ↥(auxiliaryEndomorphismAlgebra k (Fin N → k) (∑ i, lam i)))
    (v : schurSubmodule k N lam) :
    ((b • v : schurSubmodule k N lam) : auxiliarySpace k (Fin N → k) (∑ i, lam i)) =
      b.val v.val := rfl

/-- The invariant subtype carries a module structure over the acting subtype. -/
noncomputable instance invariantSubtypeModule
    (N : ℕ) (lam : Fin N → ℕ) :
    Module (↥(auxiliaryEndomorphismAlgebra k (Fin N → k) (∑ i, lam i)))
      (schurSubmodule k N lam) where
  one_smul v := by
    apply Subtype.ext
    change (1 : ↥(auxiliaryEndomorphismAlgebra k (Fin N → k) (∑ i, lam i))).val v.val =
      v.val
    change (1 : Module.End k _) v.val = v.val
    simp
  mul_smul a b v := by
    apply Subtype.ext
    change (a * b).val v.val = a.val (b.val v.val)
    change (a.val * b.val) v.val = a.val (b.val v.val)
    rfl
  smul_zero b := by
    apply Subtype.ext
    change b.val (0 : schurSubmodule k N lam).val = 0
    change b.val (0 : auxiliarySpace k (Fin N → k) _) = 0
    simp
  smul_add b v w := by
    apply Subtype.ext
    change b.val (v + w).val = b.val v.val + b.val w.val
    change b.val (v.val + w.val) = b.val v.val + b.val w.val
    simp
  add_smul a b v := by
    apply Subtype.ext
    change (a + b).val v.val = a.val v.val + b.val v.val
    change (a.val + b.val) v.val = a.val v.val + b.val v.val
    rfl
  zero_smul v := by
    apply Subtype.ext
    change (0 : ↥(auxiliaryEndomorphismAlgebra k (Fin N → k) _)).val v.val = 0
    change (0 : Module.End k _) v.val = 0
    simp

/-- The scalar actions on the acting and invariant subtypes form a scalar tower. -/
instance isScalarTower_actingSubtype
    (N : ℕ) (lam : Fin N → ℕ) :
    IsScalarTower k (↥(auxiliaryEndomorphismAlgebra k (Fin N → k) (∑ i, lam i)))
      (schurSubmodule k N lam) where
  smul_assoc c b v := by
    apply Subtype.ext
    change (c • b).val v.val = c • b.val v.val
    change (c • b.val) v.val = c • b.val v.val
    rfl

section CAggregation

variable (N : ℕ) (lam : Fin N → ℕ)

private lemma finrank_bound (hN : (∑ i, lam i) ≤ N) :
    (∑ i, lam i) ≤ Module.finrank ℂ (Fin N → ℂ) := by
  rw [Module.finrank_pi, Fintype.card_fin]
  exact hN

private lemma youngSymEndo_mem_restrictScalars
    (S : Submodule (permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))
      (auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i)))
    (x : auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i))
    (hx : x ∈ S.restrictScalars ℂ) :
    symmetrizerEndomorphism ℂ N lam x ∈ S.restrictScalars ℂ := by
  rw [Submodule.restrictScalars_mem] at hx ⊢
  have h := S.smul_mem (symmetrizerEndomorphismMem ℂ N lam) hx
  rwa [Subalgebra.smul_def, Module.End.smul_def, symmetrizerEndomorphismMem_val] at h

set_option maxHeartbeats 6400000 in
-- Aggregating the decomposition and centralizer-range interface needs the larger budgets.
set_option synthInstance.maxHeartbeats 3200000 in
private theorem schurBlock_imageSubmoduleB_isSimple
    (hlam : Antitone lam) (_hN : (∑ i, lam i) ≤ N) :
    IsSimpleModule
      (↥(Subalgebra.centralizer ℂ
        (permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i) :
          Set (Module.End ℂ (auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i))))))
      ↥(subalgebraCentralizerSubmodule (symmetrizerEndomorphismMem ℂ N lam)) := by
  classical
  obtain ⟨ι, _, _, S, hSimp, hDist, hSfin, _hLsimp, e, he⟩ :=
    exists_auxiliarySpace_decomposition_evaluation
      (k := ℂ) (V := Fin N → ℂ) (n := ∑ i, lam i)
  haveI : IsSemisimpleModule (permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i))
      (auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i)) :=
    IsSemisimpleRing.isSemisimpleModule
  obtain ⟨iLam, hLabel_iLam, hLabel_other⟩ :=
    existsSimpleSubmoduleWithPrescribedTraceComplex N lam hlam S hSimp hDist hSfin e he
  obtain ⟨α, hα_sq⟩ :=
    partitionSymmetrizer_sq_smul ℂ (∑ i, lam i) (partitionOfTuple N lam)
  have hc_sq : symmetrizerEndomorphismMem ℂ N lam * symmetrizerEndomorphismMem ℂ N lam =
      α • symmetrizerEndomorphismMem ℂ N lam := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_smul, symmetrizerEndomorphismMem_val]
    exact symmetrizerEndomorphism_sq ℂ N lam α hα_sq
  let f : ∀ i, ↥(S i) →ₗ[ℂ] ↥(S i) := fun i =>
    (symmetrizerEndomorphism ℂ N lam).restrict
      (p := (S i).restrictScalars ℂ) (q := (S i).restrictScalars ℂ)
      (youngSymEndo_mem_restrictScalars N lam (S i))
  have hf_block : ∀ (i : ι) (v : ↥(S i))
      (l : ↥(S i) →ₗ[permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i)]
        auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i)),
      e ((symmetrizerEndomorphismMem ℂ N lam).val
          (e.symm (DirectSum.of _ i (v ⊗ₜ[ℂ] l)))) =
        DirectSum.of _ i (f i v ⊗ₜ[ℂ] l) := by
    intro i v l
    exact map_symmetrizerEndomorphism_tmul ℂ N lam S e he i v l
  have hf_zero : ∀ i, i ≠ iLam → f i = 0 := by
    intro i hi
    obtain ⟨la', hla'_ne, hla'_trace⟩ := hLabel_other i hi
    haveI : Module.Finite ℂ ↥((S i).restrictScalars ℂ) := hSfin i
    exact restriction_eq_zero_of_partition_ne N lam (S i) la' hla'_trace hla'_ne
  haveI : Module.Finite ℂ ↥((S iLam).restrictScalars ℂ) := hSfin iLam
  obtain ⟨α', π', hα'_ne, hπ'_idem, hπ'_rank, hf_eq_raw⟩ :=
    exists_rankOneIdempotent_smul_eq_restriction N lam (S iLam) hLabel_iLam
  have hf_eq : f iLam = α' • π' := hf_eq_raw
  have hf_sq : f iLam * f iLam = α • f iLam :=
    Auxiliary.restrict_symmetrizerEndomorphism_sq N lam (S iLam) α hα_sq
  have hπ'_ne : π' ≠ 0 := by
    intro h0
    rw [h0, LinearMap.range_zero, finrank_bot] at hπ'_rank
    exact one_ne_zero hπ'_rank.symm
  have hαeq : α' = α := by
    have h1 : f iLam * f iLam = (α' * α') • π' := by
      rw [hf_eq, smul_mul_smul_comm, hπ'_idem]
    have h2 : α • f iLam = (α * α') • π' := by
      rw [hf_eq, smul_smul]
    have key : (α' * α') • π' = (α * α') • π' := by
      rw [← h1, hf_sq, h2]
    obtain ⟨x, hx⟩ : ∃ x, π' x ≠ 0 := by
      by_contra h
      push Not at h
      apply hπ'_ne
      ext x
      exact congrArg Subtype.val (h x)
    have keyx := LinearMap.congr_fun key x
    have hxval : (π' x).val ≠ 0 := by
      intro h
      exact hx (Subtype.ext h)
    have keyxval := congrArg Subtype.val keyx
    simp only [LinearMap.smul_apply, SetLike.val_smul_of_tower] at keyxval
    have hscal : α' * α' = α * α' := smul_left_injective ℂ hxval keyxval
    exact mul_right_cancel₀ hα'_ne hscal
  have hα_ne : α ≠ 0 := hαeq ▸ hα'_ne
  have hf_special : f iLam = α • π' := by
    rw [hf_eq, hαeq]
  exact isSimpleModule_subalgebraCentralizerSubmodule
    (symmetrizerEndomorphismMem ℂ N lam) α hα_ne hc_sq S e he iLam (hSimp iLam)
    f hf_block hf_zero π' hπ'_idem hπ'_rank hf_special

end CAggregation

set_option maxHeartbeats 1600000 in
-- Transporting simplicity across the subalgebra equality needs the larger budgets.
set_option synthInstance.maxHeartbeats 800000 in
/-- Under the order and size hypotheses, the complex invariant subtype is a simple module. -/
theorem isSimpleModule_invariantSubtypeComplex
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) (hN : (∑ i, lam i) ≤ N) :
    IsSimpleModule
      (↥(auxiliaryEndomorphismAlgebra ℂ (Fin N → ℂ) (∑ i, lam i)))
      (schurSubmodule ℂ N lam) := by
  classical
  have hBD : auxiliaryEndomorphismAlgebra ℂ (Fin N → ℂ) (∑ i, lam i) =
      Subalgebra.centralizer ℂ
        (permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i) :
          Set (Module.End ℂ (auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i)))) :=
    (mutual_centralizer_algebras ℂ (Fin N → ℂ) (∑ i, lam i)).2
  have h1 := schurBlock_imageSubmoduleB_isSimple N lam hlam hN
  let φ : ↥(auxiliaryEndomorphismAlgebra ℂ (Fin N → ℂ) (∑ i, lam i)) ≃+*
      ↥(Subalgebra.centralizer ℂ
        (permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i) :
          Set (Module.End ℂ (auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i))))) :=
    (Subalgebra.equivOfEq _ _ hBD).toRingEquiv
  haveI : RingHomInvPair φ.toRingHom φ.symm.toRingHom :=
    ⟨by ext x; simpa using φ.symm_apply_apply x,
      by ext x; simpa using φ.apply_symm_apply x⟩
  haveI : RingHomInvPair φ.symm.toRingHom φ.toRingHom :=
    ⟨by ext x; simpa using φ.apply_symm_apply x,
      by ext x; simpa using φ.symm_apply_apply x⟩
  let e : ↥(schurSubmodule ℂ N lam) ≃ₛₗ[φ.toRingHom]
      ↥(subalgebraCentralizerSubmodule (symmetrizerEndomorphismMem ℂ N lam)) :=
    { toFun := fun x =>
        ⟨x.val, by rw [mem_subalgebraCentralizerSubmodule_iff_mem_range]; exact x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        apply Subtype.ext
        rw [actingSubtype_smul_coe, SetLike.val_smul]
        rfl
      invFun := fun y => ⟨y.val, by
        have hy := y.property
        rw [mem_subalgebraCentralizerSubmodule_iff_mem_range] at hy
        exact hy⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hso1 : IsSimpleOrder
      (Submodule (↥(Subalgebra.centralizer ℂ
        (permutationActionAlgebra ℂ (Fin N → ℂ) (∑ i, lam i) :
          Set (Module.End ℂ (auxiliarySpace ℂ (Fin N → ℂ) (∑ i, lam i))))))
        ↥(subalgebraCentralizerSubmodule (symmetrizerEndomorphismMem ℂ N lam))) :=
    h1.toIsSimpleOrder
  have hso2 := (Submodule.orderIsoMapComap e).isSimpleOrder_iff.mpr hso1
  exact { toIsSimpleOrder := hso2 }

set_option maxHeartbeats 3200000 in
-- Elaborating the representation-module transfer needs the larger budgets.
set_option synthInstance.maxHeartbeats 1600000 in
/-- Under the stated order and size hypotheses, the displayed complex general linear
representation is simple. -/
theorem isSimpleModule_representationComplex
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) (hN : (∑ i, lam i) ≤ N) :
    IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ))
      (Representation.asModule (schurRepresentation ℂ N lam).ρ) := by
  change IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin N) ℂ))
    (schurSubmoduleRepresentation ℂ N lam).asModule
  haveI := isSimpleModule_invariantSubtypeComplex N lam hlam hN
  refine isSimpleModule_of_auxiliary_piTensorProduct_action ℂ
    (N := N) (n := ∑ i, lam i)
    (M := ↥(schurSubmodule ℂ N lam))
    (schurSubmoduleRepresentation ℂ N lam) ?_
  intro g x
  apply Subtype.ext
  rfl

set_option maxHeartbeats 6400000 in
-- Aggregating the generic decomposition and centralizer-range interface needs the larger budgets.
set_option synthInstance.maxHeartbeats 3200000 in
/-- The indicated subtype is simple under the action of the centralizing subalgebra. -/
theorem isSimpleModule_centralizerSubtypeAction
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    IsSimpleModule
      (↥(Subalgebra.centralizer k
        (permutationActionAlgebra k (Fin N → k) (∑ i, lam i) :
          Set (Module.End k (auxiliarySpace k (Fin N → k) (∑ i, lam i))))))
      ↥(subalgebraCentralizerSubmodule (symmetrizerEndomorphismMem k N lam)) := by
  classical
  obtain ⟨ι, _, _, S, hSimp, hDist, hSfin, _hLsimp, e, he⟩ :=
    exists_auxiliarySpace_decomposition_evaluation
      (k := k) (V := Fin N → k) (n := ∑ i, lam i)
  haveI : IsSemisimpleModule (permutationActionAlgebra k (Fin N → k) (∑ i, lam i))
      (auxiliarySpace k (Fin N → k) (∑ i, lam i)) :=
    IsSemisimpleRing.isSemisimpleModule
  obtain ⟨iLam, hLabel_iLam, hLabel_other⟩ :=
    existsSimpleSubmoduleWithPrescribedTrace N lam hlam S hSimp hDist hSfin e he
  obtain ⟨α, hα_sq⟩ :=
    partitionSymmetrizer_sq_smul k (∑ i, lam i) (partitionOfTuple N lam)
  have hc_sq : symmetrizerEndomorphismMem k N lam * symmetrizerEndomorphismMem k N lam =
      α • symmetrizerEndomorphismMem k N lam := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_smul, symmetrizerEndomorphismMem_val]
    exact symmetrizerEndomorphism_sq k N lam α hα_sq
  let f : ∀ i, ↥(S i) →ₗ[k] ↥(S i) := fun i =>
    (symmetrizerEndomorphism k N lam).restrict
      (p := (S i).restrictScalars k) (q := (S i).restrictScalars k)
      (fun _ hv => (S i).smul_mem (symmetrizerEndomorphismMem k N lam) hv)
  have hf_block : ∀ (i : ι) (v : ↥(S i))
      (l : ↥(S i) →ₗ[permutationActionAlgebra k (Fin N → k) (∑ i, lam i)]
        auxiliarySpace k (Fin N → k) (∑ i, lam i)),
      e ((symmetrizerEndomorphismMem k N lam).val
          (e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)))) =
        DirectSum.of _ i (f i v ⊗ₜ[k] l) := by
    intro i v l
    exact map_symmetrizerEndomorphism_tmul k N lam S e he i v l
  have hf_zero : ∀ i, i ≠ iLam → f i = 0 := by
    intro i hi
    obtain ⟨la', hla'_ne, hla'_trace⟩ := hLabel_other i hi
    haveI : Module.Finite k ↥((S i).restrictScalars k) := hSfin i
    exact restriction_eq_zero_of_partition_ne N lam (S i) la' hla'_trace hla'_ne
  haveI : Module.Finite k ↥((S iLam).restrictScalars k) := hSfin iLam
  obtain ⟨α', π', hα'_ne, hπ'_idem, hπ'_rank, hf_eq_raw⟩ :=
    exists_rankOneIdempotent_smul_eq_restriction N lam (S iLam) hLabel_iLam
  have hf_eq : f iLam = α' • π' := hf_eq_raw
  have hf_sq : f iLam * f iLam = α • f iLam :=
    Auxiliary.restrict_symmetrizerEndomorphism_sq N lam (S iLam) α hα_sq
  have hπ'_ne : π' ≠ 0 := by
    intro h0
    rw [h0, LinearMap.range_zero, finrank_bot] at hπ'_rank
    exact one_ne_zero hπ'_rank.symm
  have hαeq : α' = α := by
    have h1 : f iLam * f iLam = (α' * α') • π' := by
      rw [hf_eq, smul_mul_smul_comm, hπ'_idem]
    have h2 : α • f iLam = (α * α') • π' := by
      rw [hf_eq, smul_smul]
    have key : (α' * α') • π' = (α * α') • π' := by
      rw [← h1, hf_sq, h2]
    obtain ⟨x, hx⟩ : ∃ x, π' x ≠ 0 := by
      by_contra h
      push Not at h
      apply hπ'_ne
      ext x
      exact congrArg Subtype.val (h x)
    have keyx := LinearMap.congr_fun key x
    have hxval : (π' x).val ≠ 0 := by
      intro h
      exact hx (Subtype.ext h)
    have keyxval := congrArg Subtype.val keyx
    simp only [LinearMap.smul_apply, SetLike.val_smul_of_tower] at keyxval
    have hscal : α' * α' = α * α' := smul_left_injective k hxval keyxval
    exact mul_right_cancel₀ hα'_ne hscal
  have hα_ne : α ≠ 0 := hαeq ▸ hα'_ne
  have hf_special : f iLam = α • π' := by
    rw [hf_eq, hαeq]
  exact isSimpleModule_subalgebraCentralizerSubmodule
    (symmetrizerEndomorphismMem k N lam) α hα_ne hc_sq S e he iLam (hSimp iLam)
    f hf_block hf_zero π' hπ'_idem hπ'_rank hf_special

set_option maxHeartbeats 1600000 in
-- Transporting generic simplicity across the subalgebra equality needs the larger budgets.
set_option synthInstance.maxHeartbeats 800000 in
/-- An antitone index function makes the invariant subtype a simple module. -/
theorem isSimpleModule_invariantSubtype
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    IsSimpleModule
      (↥(auxiliaryEndomorphismAlgebra k (Fin N → k) (∑ i, lam i)))
      (schurSubmodule k N lam) := by
  classical
  have hBD : auxiliaryEndomorphismAlgebra k (Fin N → k) (∑ i, lam i) =
      Subalgebra.centralizer k
        (permutationActionAlgebra k (Fin N → k) (∑ i, lam i) :
          Set (Module.End k (auxiliarySpace k (Fin N → k) (∑ i, lam i)))) :=
    (mutual_centralizer_algebras k (Fin N → k) (∑ i, lam i)).2
  have h1 := isSimpleModule_centralizerSubtypeAction (k := k) N lam hlam
  let φ : ↥(auxiliaryEndomorphismAlgebra k (Fin N → k) (∑ i, lam i)) ≃+*
      ↥(Subalgebra.centralizer k
        (permutationActionAlgebra k (Fin N → k) (∑ i, lam i) :
          Set (Module.End k (auxiliarySpace k (Fin N → k) (∑ i, lam i))))) :=
    (Subalgebra.equivOfEq _ _ hBD).toRingEquiv
  haveI : RingHomInvPair φ.toRingHom φ.symm.toRingHom :=
    ⟨by ext x; simpa using φ.symm_apply_apply x,
      by ext x; simpa using φ.apply_symm_apply x⟩
  haveI : RingHomInvPair φ.symm.toRingHom φ.toRingHom :=
    ⟨by ext x; simpa using φ.apply_symm_apply x,
      by ext x; simpa using φ.symm_apply_apply x⟩
  let e : ↥(schurSubmodule k N lam) ≃ₛₗ[φ.toRingHom]
      ↥(subalgebraCentralizerSubmodule (symmetrizerEndomorphismMem k N lam)) :=
    { toFun := fun x =>
        ⟨x.val, by rw [mem_subalgebraCentralizerSubmodule_iff_mem_range]; exact x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        apply Subtype.ext
        rw [actingSubtype_smul_coe, SetLike.val_smul]
        rfl
      invFun := fun y => ⟨y.val, by
        have hy := y.property
        rw [mem_subalgebraCentralizerSubmodule_iff_mem_range] at hy
        exact hy⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hso1 : IsSimpleOrder
      (Submodule (↥(Subalgebra.centralizer k
        (permutationActionAlgebra k (Fin N → k) (∑ i, lam i) :
          Set (Module.End k (auxiliarySpace k (Fin N → k) (∑ i, lam i))))))
        ↥(subalgebraCentralizerSubmodule (symmetrizerEndomorphismMem k N lam))) :=
    h1.toIsSimpleOrder
  have hso2 := (Submodule.orderIsoMapComap e).isSimpleOrder_iff.mpr hso1
  exact { toIsSimpleOrder := hso2 }

end GeneralLinear

end RepresentationTheory.GeneralLinear.InvariantSubtype

end
