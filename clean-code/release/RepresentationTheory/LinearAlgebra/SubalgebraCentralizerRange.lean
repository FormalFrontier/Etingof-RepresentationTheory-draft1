/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.CentralizerDecomposition

open scoped TensorProduct

universe u v

namespace RepresentationTheory.LinearAlgebra.SubalgebraCentralizerRange

open RepresentationTheory.CentralizerDecomposition

/-- A rank-one idempotent has a nonzero fixed vector that generates its range. -/
lemma exists_fixed_generator_of_idempotent_of_finrank_range_eq_one
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (π : V →ₗ[k] V) (hπ_idem : π * π = π)
    (hπ_rank : Module.finrank k (LinearMap.range π) = 1) :
    ∃ v₀ : V, v₀ ≠ 0 ∧ π v₀ = v₀ ∧
      LinearMap.range π = Submodule.span k {v₀} := by
  classical
  haveI : Module.Finite k (LinearMap.range π) :=
    Module.finite_of_finrank_pos (by rw [hπ_rank]; exact Nat.one_pos)
  let b : Module.Basis (Fin 1) k (LinearMap.range π) :=
    Module.finBasisOfFinrankEq k _ hπ_rank
  refine ⟨(b 0 : V), ?_, ?_, ?_⟩
  · intro h
    have : (b 0 : LinearMap.range π) = 0 := Subtype.ext h
    exact b.ne_zero 0 this
  · have hv0 : (b 0 : V) ∈ LinearMap.range π := (b 0).property
    obtain ⟨w, hw⟩ := hv0
    rw [← hw]
    exact LinearMap.congr_fun hπ_idem w
  · have hb_span : (Submodule.span k ({(b 0 : LinearMap.range π)} :
        Set (LinearMap.range π))) = ⊤ := by
      rw [← b.span_eq]
      congr; ext x
      simp [Set.range_unique]
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy⟩ := hx
      have hxr : (⟨π y, ⟨y, rfl⟩⟩ : LinearMap.range π) ∈
          (Submodule.span k ({(b 0 : LinearMap.range π)} :
            Set (LinearMap.range π))) := by
        rw [hb_span]; exact Submodule.mem_top
      rw [Submodule.mem_span_singleton] at hxr
      obtain ⟨c, hc⟩ := hxr
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      have hval := congrArg ((↑) : LinearMap.range π → V) hc
      simp only [SetLike.val_smul] at hval
      rw [hval, hy]
    · rw [Submodule.span_singleton_le_iff_mem]
      exact (b 0).property

/-- If a linear map has range spanned by a vector, its tensor-product map sends every tensor to a
pure tensor with that vector as first factor. -/
lemma exists_map_eq_tmul_of_range_eq_span
    {k : Type*} [Field k] {V L : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup L] [Module k L]
    (π : V →ₗ[k] V) (v₀ : V)
    (hv₀ : LinearMap.range π = Submodule.span k {v₀})
    (ξ : V ⊗[k] L) :
    ∃ l₀ : L, (TensorProduct.map π LinearMap.id) ξ = v₀ ⊗ₜ[k] l₀ := by
  classical
  induction ξ using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul v l =>
    have hπv : π v ∈ Submodule.span k ({v₀} : Set V) := by
      rw [← hv₀]; exact LinearMap.mem_range_self π v
    rw [Submodule.mem_span_singleton] at hπv
    obtain ⟨c, hc⟩ := hπv
    refine ⟨c • l, ?_⟩
    rw [TensorProduct.map_tmul, LinearMap.id_apply, ← hc, TensorProduct.smul_tmul]
  | add ξ₁ ξ₂ ih₁ ih₂ =>
    obtain ⟨l₁, h₁⟩ := ih₁
    obtain ⟨l₂, h₂⟩ := ih₂
    refine ⟨l₁ + l₂, ?_⟩
    rw [map_add, h₁, h₂, ← TensorProduct.tmul_add]

set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
/-- If conjugating the action of c through e agrees on pure tensors in the i-th direct-sum summand
with applying f i to the first tensor factor, then the same equality holds for every tensor in that
summand. -/
lemma eq_on_directSum_summand_of_eq_on_tmul
    {k : Type u} [Field k]
    {E : Type v} [AddCommGroup E] [Module k E]
    {A : Subalgebra k (Module.End k E)}
    (c : ↥A)
    {ι : Type} [DecidableEq ι]
    (S : ι → Submodule A E)
    (e : E ≃ₗ[k] DirectSum ι (fun i =>
      ↥(S i) ⊗[k] (↥(S i) →ₗ[A] E)))
    (f : ∀ i, ↥(S i) →ₗ[k] ↥(S i))
    (hf_block : ∀ (i : ι) (v : ↥(S i)) (l : ↥(S i) →ₗ[A] E),
      e (c.val (e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)))) =
        DirectSum.of _ i (f i v ⊗ₜ[k] l))
    (i : ι) (ξ : ↥(S i) ⊗[k] (↥(S i) →ₗ[A] E)) :
    e (c.val (e.symm (DirectSum.of _ i ξ))) =
      DirectSum.of _ i (TensorProduct.map (f i) LinearMap.id ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul v l =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hf_block i v l]
  | add ξ₁ ξ₂ ih₁ ih₂ =>
    simp only [map_add, ih₁, ih₂]

variable {k : Type u} [Field k]
variable {E : Type v} [AddCommGroup E] [Module k E]
variable {A : Subalgebra k (Module.End k E)}

/-- A subalgebra element commutes with an element of the centralizer of that subalgebra. -/
lemma commute_of_mem_subalgebra_of_mem_centralizer (c : ↥A)
    (b : ↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) :
    c.val * b.val = b.val * c.val := by
  have hb := b.property
  rw [Subalgebra.mem_centralizer_iff] at hb
  exact hb _ c.property

/-- Associates to an element of a subalgebra of endomorphisms a linear endomorphism over the
centralizer of that subalgebra. -/
noncomputable def subalgebraCentralizerLinearMap (c : ↥A) :
    E →ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))] E where
  toFun := c.val
  map_add' := c.val.map_add
  map_smul' b x := by
    change c.val (b.val x) = b.val (c.val x)
    exact LinearMap.congr_fun (commute_of_mem_subalgebra_of_mem_centralizer c b) x

/-- The endomorphism over the subalgebra centralizer acts identically to the underlying subalgebra
element. -/
@[simp]
lemma subalgebraCentralizerLinearMap_apply (c : ↥A) (x : E) :
    subalgebraCentralizerLinearMap c x = c.val x := rfl

/-- The submodule over the centralizer of a subalgebra associated to an element of that
subalgebra. -/
noncomputable def subalgebraCentralizerSubmodule (c : ↥A) :
    Submodule (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) E :=
  LinearMap.range (subalgebraCentralizerLinearMap c)

/-- Membership in the subalgebra-centralizer submodule associated to an element is equivalent to
membership in the range of its underlying endomorphism. -/
@[simp]
lemma mem_subalgebraCentralizerSubmodule_iff_mem_range (c : ↥A) (x : E) :
    x ∈ subalgebraCentralizerSubmodule c ↔
      x ∈ LinearMap.range (c.val : Module.End k E) := by
  simp [subalgebraCentralizerSubmodule, LinearMap.mem_range,
    subalgebraCentralizerLinearMap]

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- Let the ambient module be finite over the field and semisimple over the subalgebra. Suppose the
direct-sum tensor decomposition is compatible with evaluation and with the action of c through f,
and that f vanishes away from a selected simple summand iLam. If c² = α • c for nonzero α and
f iLam = α • π for an idempotent π whose range has finrank one, then the centralizer submodule
associated to c is simple. -/
theorem isSimpleModule_subalgebraCentralizerSubmodule
    [Module.Finite k E]
    [IsSemisimpleModule A E]
    (c : ↥A) (α : k) (hα : α ≠ 0) (_hc_sq : c * c = α • c)
    {ι : Type} [DecidableEq ι]
    (S : ι → Submodule A E)
    (e : E ≃ₗ[k] DirectSum ι (fun i =>
      ↥(S i) ⊗[k] (↥(S i) →ₗ[A] E)))
    (he_eval : ∀ (i : ι) (v : ↥(S i)) (l : ↥(S i) →ₗ[A] E),
      e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v)
    (iLam : ι) (hSiLam_simple : IsSimpleModule A ↥(S iLam))
    (f : ∀ i, ↥(S i) →ₗ[k] ↥(S i))
    (hf_block : ∀ (i : ι) (v : ↥(S i)) (l : ↥(S i) →ₗ[A] E),
      e (c.val (e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)))) =
        DirectSum.of _ i (f i v ⊗ₜ[k] l))
    (hf_zero : ∀ i, i ≠ iLam → f i = 0)
    (π : ↥(S iLam) →ₗ[k] ↥(S iLam))
    (hπ_idem : π * π = π)
    (hπ_rank : Module.finrank k (LinearMap.range π) = 1)
    (hπ_special : f iLam = α • π) :
    IsSimpleModule
      (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      ↥(subalgebraCentralizerSubmodule c) := by
  classical
  letI : Module
      (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥(S iLam) →ₗ[A] E) :=
    centralizerModuleHom k E (A := A) (V := ↥(S iLam))
  haveI hSiLam_simple' : IsSimpleModule (↥A) ↥(S iLam) := hSiLam_simple
  haveI : IsSimpleOrder (Submodule (↥A) ↥(S iLam)) :=
    hSiLam_simple'.toIsSimpleOrder
  set β : ι → Type _ :=
    fun j => ↥(S j) ⊗[k] (↥(S j) →ₗ[A] E) with hβ
  obtain ⟨v₀, hv₀_ne, hπv₀, hrange_π⟩ :=
    exists_fixed_generator_of_idempotent_of_finrank_range_eq_one
      (k := k) (V := ↥(S iLam)) π hπ_idem hπ_rank
  let Φ : (↥(S iLam) →ₗ[A] E) →ₗ[k] E :=
    { toFun := fun l => l v₀
      map_add' := fun l₁ l₂ => by simp
      map_smul' := fun r l => by simp }
  have hΦ_equiv : ∀ b : ↥(Subalgebra.centralizer k
      (A : Set (Module.End k E))), ∀ l, Φ (b • l) = b.val (Φ l) := by
    intro b l
    change (b • l) v₀ = b.val (l v₀)
    rfl
  have hΦ_in_range : ∀ l : ↥(S iLam) →ₗ[A] E,
      Φ l ∈ subalgebraCentralizerSubmodule c := by
    intro l
    rw [mem_subalgebraCentralizerSubmodule_iff_mem_range]
    refine ⟨α⁻¹ • l v₀, ?_⟩
    rw [c.val.map_smul]
    have hlv0 : l v₀ = e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] l)) := by
      rw [he_eval]
    have hcomp : c.val (l v₀) = α • l v₀ := by
      rw [hlv0]
      have happly_e : e (c.val (e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] l)))) =
          DirectSum.of β iLam (f iLam v₀ ⊗ₜ[k] l) := hf_block iLam v₀ l
      have hα_block : e (c.val (e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] l)))) =
          α • DirectSum.of β iLam (v₀ ⊗ₜ[k] l) := by
        rw [happly_e, hπ_special, LinearMap.smul_apply, hπv₀,
          ← TensorProduct.smul_tmul', DirectSum.of_smul]
      have happly_e_symm : c.val (e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] l))) =
          α • e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] l)) := by
        have h := congrArg e.symm hα_block
        rw [LinearEquiv.symm_apply_apply,
          e.symm.map_smul α (DirectSum.of β iLam (v₀ ⊗ₜ[k] l))] at h
        exact h
      rw [happly_e_symm, ← hlv0]
    rw [hcomp, smul_smul, inv_mul_cancel₀ hα, one_smul]
    rfl
  have hΦ_surj_on_image : ∀ y : E,
      ∃ l₀ : ↥(S iLam) →ₗ[A] E, c.val y = Φ l₀ := by
    intro y
    obtain ⟨l₀_pre, hl₀_pre⟩ := exists_map_eq_tmul_of_range_eq_span π v₀ hrange_π
      ((e y) iLam)
    refine ⟨α • l₀_pre, ?_⟩
    have h_e_decomp : e y = ∑ i ∈ (e y).support,
        DirectSum.of β i ((e y) i) := by
      rw [DirectSum.sum_support_of]
    have h_apply_c : e (c.val y) =
        ∑ i ∈ (e y).support,
          e (c.val (e.symm (DirectSum.of β i ((e y) i)))) := by
      conv_lhs => rw [show y = e.symm (e y) from (e.symm_apply_apply y).symm,
        h_e_decomp]
      rw [map_sum, map_sum, map_sum]
    have h_block : ∀ i,
        e (c.val (e.symm (DirectSum.of β i ((e y) i)))) =
          DirectSum.of β i (TensorProduct.map (f i) LinearMap.id ((e y) i)) :=
      fun i => eq_on_directSum_summand_of_eq_on_tmul c S e f hf_block i ((e y) i)
    have h_block_zero : ∀ i, i ≠ iLam →
        e (c.val (e.symm (DirectSum.of β i ((e y) i)))) = 0 := by
      intro i hi
      rw [h_block, hf_zero i hi]
      simp
    have h_e_cy : e (c.val y) =
        DirectSum.of β iLam
          (TensorProduct.map (f iLam) LinearMap.id ((e y) iLam)) := by
      rw [h_apply_c]
      by_cases hsupp : iLam ∈ (e y).support
      · rw [Finset.sum_eq_single iLam ?_ ?_]
        · exact h_block iLam
        · intros j _ hj; exact h_block_zero j hj
        · intro h; exact (h hsupp).elim
      · have hzero : (e y) iLam = 0 := DFinsupp.notMem_support_iff.mp hsupp
        rw [hzero]
        simp only [map_zero]
        apply Finset.sum_eq_zero
        intros j hj
        apply h_block_zero
        intro hji; exact hsupp (hji ▸ hj)
    have h_factor : TensorProduct.map (f iLam) LinearMap.id ((e y) iLam) =
        v₀ ⊗ₜ[k] (α • l₀_pre) := by
      rw [hπ_special]
      have : TensorProduct.map (α • π) LinearMap.id ((e y) iLam) =
          α • TensorProduct.map π LinearMap.id ((e y) iLam) := by
        rw [show (α • π : ↥(S iLam) →ₗ[k] ↥(S iLam)) =
              α • (π : ↥(S iLam) →ₗ[k] ↥(S iLam)) from rfl]
        rw [TensorProduct.map_smul_left, LinearMap.smul_apply]
      rw [this, hl₀_pre]
      rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
    rw [h_factor] at h_e_cy
    have h_cy : c.val y =
        e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] (α • l₀_pre))) := by
      have h := congrArg e.symm h_e_cy
      simp only [LinearEquiv.symm_apply_apply] at h
      exact h
    rw [h_cy, he_eval]
    rfl
  have hΦ_inj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro l hl
    change (l : ↥(S iLam) →ₗ[A] E) = 0
    have hker : v₀ ∈ LinearMap.ker l := by
      change l v₀ = 0; exact hl
    rcases (eq_bot_or_eq_top (LinearMap.ker l)) with h | h
    · exfalso; apply hv₀_ne
      have : v₀ ∈ (⊥ : Submodule A ↥(S iLam)) := h ▸ hker
      simpa using this
    · ext v
      have hv : v ∈ LinearMap.ker l := h ▸ Submodule.mem_top
      change l v = 0
      simpa [LinearMap.mem_ker] using hv
  let Φ' : (↥(S iLam) →ₗ[A] E) →ₗ[↥(Subalgebra.centralizer k
      (A : Set (Module.End k E)))] ↥(subalgebraCentralizerSubmodule c) :=
    { toFun := fun l => ⟨Φ l, hΦ_in_range l⟩
      map_add' := fun l₁ l₂ => by
        ext; change Φ (l₁ + l₂) = Φ l₁ + Φ l₂; rw [map_add]
      map_smul' := fun b l => by
        ext
        change Φ (b • l) = b • (Φ l : E)
        rw [hΦ_equiv]; rfl }
  have hΦ'_surj : Function.Surjective Φ' := by
    rintro ⟨z, hz⟩
    rw [mem_subalgebraCentralizerSubmodule_iff_mem_range,
      LinearMap.mem_range] at hz
    obtain ⟨y, hy⟩ := hz
    obtain ⟨l₀, hl₀⟩ := hΦ_surj_on_image y
    refine ⟨l₀, ?_⟩
    ext
    change Φ l₀ = z
    rw [← hy]; exact hl₀.symm
  have hΦ'_inj : Function.Injective Φ' := by
    rw [injective_iff_map_eq_zero]
    intro l hl
    apply hΦ_inj
    have : (Φ' l : E) = 0 := by
      rw [hl]; rfl
    exact this
  let Ψ : (↥(S iLam) →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k
      (A : Set (Module.End k E)))] ↥(subalgebraCentralizerSubmodule c) :=
    LinearEquiv.ofBijective Φ' ⟨hΦ'_inj, hΦ'_surj⟩
  haveI hL_simp : IsSimpleModule
      (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥(S iLam) →ₗ[A] E) :=
    isSimpleModule_linearMap (k := k) (E := E) A (S iLam)
  exact IsSimpleModule.congr Ψ.symm

end RepresentationTheory.LinearAlgebra.SubalgebraCentralizerRange
