import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_ClassificationGeneral

/-!
# Schur-Weyl special-block analysis over a general field (Ch5 #4946 sub-C1)

This file lifts the two Young-symmetrizer endomorphism lemmas from
`Theorem5_22_1.lean` from `ℂ` to a general field `k` of characteristic zero:

* `youngSym_action_vanishes_off_block_general` — the Young-symmetrizer
  endomorphism `c_λ` vanishes on any simple `symGroupImage`-stable submodule
  whose Specht label `≠ weightToPartition N lam`;
* `youngSym_action_on_special_block_rank_one_scaled_proj_general` — on the
  special block it is a nonzero scalar times a rank-one idempotent projection.

The general-`k` versions live **downstream** of `Theorem5_22_1.lean`: their
off-block-vanishing input is the character-orthogonality identity
`youngSym_trace_kronecker_K`, whose proof rests on general-`k` Specht-module
simplicity (`SpechtModuleK_isSimpleModule_general`) and distinctness
(`Theorem5_12_2_distinct_general`), both of which are themselves defined in
files importing `Theorem5_22_1.lean`. Re-proving them in place would be circular,
so the lifted lemmas are collected here instead of in `Theorem5_22_1.lean`.

The two ℂ-specific helpers (`youngSym_sq_ℂ'`, `youngSymmetrizerK_complex_eq`)
disappear in the general-`k` track: working over `k` throughout, the scalar `α`
with `c_λ² = α · c_λ` comes directly from `YoungSymmetrizerK_sq_scalar k` with no
`ℚ → ℂ` base change.

The character target `spechtBlockCharacterK k n la σ` is the trace of left
multiplication by `of σ` on the Specht block `SpechtModuleK k n la`; it is
definitionally the general-`k` Specht character produced by the bridge (#4991),
so the off-block hypothesis `h_label` is the per-`σ` form of the (general-`k`)
Specht-character bridge.
-/

open MvPolynomial Finset

noncomputable section

namespace Etingof

variable {k : Type*} [Field k] [CharZero k]

private abbrev G (n : ℕ) := Equiv.Perm (Fin n)

/-! ### General-`k` Specht block action and character -/

/-- Left multiplication by `of σ` on the Specht block `SpechtModuleK k n la`,
the general-`k` analogue of `spechtModuleAction`. -/
def spechtBlockActionK (k : Type*) [Field k] (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    ↥(SpechtModuleK k n la) →ₗ[k] ↥(SpechtModuleK k n la) where
  toFun := fun ⟨m, hm⟩ => ⟨MonoidAlgebra.of k _ σ * m,
    (SpechtModuleK k n la).smul_mem (MonoidAlgebra.of k _ σ) hm⟩
  map_add' := fun ⟨a, _⟩ ⟨b, _⟩ => Subtype.ext (mul_add _ a b)
  map_smul' := fun _ ⟨m, _⟩ => Subtype.ext (Algebra.mul_smul_comm _ _ m)

/-- The general-`k` Specht character: trace of left multiplication by `of σ` on
`SpechtModuleK k n la`. Definitionally equal to the bridge's
`spechtModuleCharacterK`. -/
def spechtBlockCharacterK (k : Type*) [Field k] (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : k :=
  LinearMap.trace k _ (spechtBlockActionK k n la σ)

/-! ### Left multiplication by a group-algebra element on a Specht block -/

/-- Left multiplication by `c ∈ k[S_n]` on the Specht block `SpechtModuleK k n la`. -/
private def mulLeftBlockK (n : ℕ) (c : MonoidAlgebra k (G n)) (la : Nat.Partition n) :
    ↥(SpechtModuleK k n la) →ₗ[k] ↥(SpechtModuleK k n la) where
  toFun v := ⟨c * ↑v, (SpechtModuleK k n la).smul_mem c v.prop⟩
  map_add' a b := Subtype.ext (mul_add c ↑a ↑b)
  map_smul' r v := Subtype.ext (Algebra.mul_smul_comm r c ↑v)

omit [CharZero k] in
private lemma mulLeftBlockK_of (n : ℕ) (la : Nat.Partition n) (σ : G n) :
    mulLeftBlockK n (MonoidAlgebra.of k _ σ) la = spechtBlockActionK k n la σ := by
  ext ⟨m, hm⟩; rfl

private def mulLeftBlockKLinear (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra k (G n) →ₗ[k]
      (↥(SpechtModuleK k n la) →ₗ[k] ↥(SpechtModuleK k n la)) where
  toFun c := mulLeftBlockK n c la
  map_add' a b := by ext ⟨m, hm⟩; simp [mulLeftBlockK, add_mul]
  map_smul' r c := by ext ⟨m, hm⟩; simp [mulLeftBlockK]

omit [CharZero k] in
/-- Trace linearity: `∑_σ c(σ) · χ_{V_la}(σ) = trace of left mult by c on V_la`. -/
private lemma sum_coeff_char_eq_traceK (n : ℕ) (la : Nat.Partition n)
    (c : MonoidAlgebra k (G n)) :
    ∑ σ : G n, c σ * spechtBlockCharacterK k n la σ =
      LinearMap.trace k _ (mulLeftBlockK n c la) := by
  symm
  have key : (LinearMap.trace k _) (mulLeftBlockK n c la) =
      ∑ σ ∈ c.support, c σ * spechtBlockCharacterK k n la σ := by
    have hlin : mulLeftBlockK n c la = (mulLeftBlockKLinear n la) c := rfl
    rw [hlin]
    simp_rw [spechtBlockCharacterK, ← mulLeftBlockK_of n la]
    have hc : c = ∑ σ ∈ c.support, c σ • MonoidAlgebra.of k (G n) σ := by
      conv_lhs => rw [← Finsupp.sum_single c]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [MonoidAlgebra.of_apply, Finsupp.smul_single', mul_one]
    conv_lhs => rw [show (mulLeftBlockKLinear n la) c =
        (mulLeftBlockKLinear n la)
          (∑ σ ∈ c.support, c σ • MonoidAlgebra.of k _ σ) from by rw [← hc]]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [map_smul, LinearMap.map_smul, smul_eq_mul]; rfl
  rw [key]
  apply Finset.sum_subset (Finset.subset_univ c.support)
  intro σ _ hσ
  have : c σ = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hσ
  simp [this]

/-! ### Off-diagonal vanishing -/

/-- Off-diagonal: `c_λ` acts as `0` on `V_{la'}` when `la ≠ la'`. Uses general-`k`
Specht-module simplicity and distinctness. -/
private lemma mulLeft_youngSym_zero_of_neK (n : ℕ) (la la' : Nat.Partition n)
    (hne : la ≠ la') :
    mulLeftBlockK n (YoungSymmetrizerK k n la) la' = 0 := by
  by_contra hT
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : SpechtModuleK k n la',
      mulLeftBlockK n (YoungSymmetrizerK k n la) la' w₀ ≠ 0 := by
    by_contra hall; push_neg at hall; exact hT (LinearMap.ext hall)
  set φ : SpechtModuleK k n la →ₗ[MonoidAlgebra k (G n)] SpechtModuleK k n la' :=
    { toFun := fun v => ⟨(v : MonoidAlgebra k (G n)) * (w₀ : MonoidAlgebra k (G n)),
        (SpechtModuleK k n la').smul_mem (v : MonoidAlgebra k (G n)) w₀.prop⟩
      map_add' := fun a b => Subtype.ext (add_mul (a : MonoidAlgebra k (G n)) b w₀)
      map_smul' := fun a v => Subtype.ext (mul_assoc a (v : MonoidAlgebra k (G n)) w₀) }
  have hφ_ne : φ ≠ 0 := by
    intro h; apply hw₀
    have : φ ⟨YoungSymmetrizerK k n la, Submodule.subset_span rfl⟩ = 0 :=
      congr_fun (congr_arg DFunLike.coe h)
        ⟨YoungSymmetrizerK k n la, Submodule.subset_span rfl⟩
    simp only [mulLeftBlockK, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢; exact this
  haveI : IsSimpleModule (MonoidAlgebra k (G n)) (SpechtModuleK k n la) :=
    SpechtModuleK_isSimpleModule_general k n la
  haveI : IsSimpleModule (MonoidAlgebra k (G n)) (SpechtModuleK k n la') :=
    SpechtModuleK_isSimpleModule_general k n la'
  have hφ_bij := LinearMap.bijective_of_ne_zero hφ_ne
  exact (Theorem5_12_2_distinct_general k n la la' hne).false (LinearEquiv.ofBijective φ hφ_bij)

/-! ### Diagonal value -/

omit [CharZero k] in
/-- Identity coefficient of `c_λ` is `1`. -/
private lemma youngSymK_coeff_one (n : ℕ) (la : Nat.Partition n) :
    (YoungSymmetrizerK k n la : MonoidAlgebra k (G n)) 1 = 1 := by
  rw [YoungSymmetrizerK_eq_mapRange]
  simp [MonoidAlgebra.mapRingHom_apply, YoungSymmetrizerZ_apply_one]

omit [CharZero k] in
/-- Sandwich proportionality: `c * v = ((c * v)(1)) • c` for `v ∈ V_λ`. -/
private lemma mul_mem_specht_proportionalK (n : ℕ) (la : Nat.Partition n)
    (v : ↥(SpechtModuleK k n la)) :
    YoungSymmetrizerK k n la * v.val =
      (YoungSymmetrizerK k n la * v.val) 1 • YoungSymmetrizerK k n la := by
  classical
  set c := YoungSymmetrizerK k n la with hc
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp v.prop
  rw [smul_eq_mul] at ha
  obtain ⟨f, hf⟩ := YoungSymmetrizerK_sandwich_general k n la
  -- `c * v = c * (a * c) = c * a * c = f a • c`.
  have hcv : c * v.val = f a • c := by
    rw [← ha, ← mul_assoc, hf a]
  rw [hcv]
  congr 1
  rw [Finsupp.smul_apply, smul_eq_mul, youngSymK_coeff_one, mul_one]

omit [CharZero k] in
/-- Diagonal case: trace of `c_λ` on `V_λ` equals `α`. -/
private lemma trace_mulLeft_youngSym_eqK (n : ℕ) (la : Nat.Partition n)
    (α : k)
    (hα_sq : YoungSymmetrizerK k n la * YoungSymmetrizerK k n la =
      α • YoungSymmetrizerK k n la) :
    LinearMap.trace k _ (mulLeftBlockK n (YoungSymmetrizerK k n la) la) = α := by
  set c := YoungSymmetrizerK k n la with hc_def
  set V := SpechtModuleK k n la
  set T := mulLeftBlockK n c la
  have hc_mem : c ∈ V := Submodule.subset_span rfl
  set e : V := ⟨c, hc_mem⟩
  let ι : k →ₗ[k] V := LinearMap.lsmul k V |>.flip e
  let π : V →ₗ[k] k :=
    { toFun := fun v => (c * v.val) 1
      map_add' := fun x y => by simp [mul_add]
      map_smul' := fun r x => by
        change (c * (r • x.val)) 1 = r * (c * x.val) 1
        rw [Algebra.mul_smul_comm, Finsupp.smul_apply, smul_eq_mul] }
  have hT_eq : T = ι.comp π := by
    apply LinearMap.ext; intro ⟨v, hv⟩; apply Subtype.ext
    exact mul_mem_specht_proportionalK n la ⟨v, hv⟩
  rw [hT_eq, LinearMap.trace_comp_comm']
  have h_comp : π.comp ι = α • LinearMap.id := by
    apply LinearMap.ext; intro x
    change (c * (x • c)) 1 = α * x
    rw [Algebra.mul_smul_comm, Finsupp.smul_apply, smul_eq_mul]
    rw [hα_sq, Finsupp.smul_apply, smul_eq_mul, youngSymK_coeff_one, mul_one, mul_comm]
  rw [h_comp]; simp [map_smul, LinearMap.trace_id, Module.finrank_self]

/-! ### Character-orthogonality (Kronecker) identity over `k` -/

/-- **Young symmetrizer trace Kronecker identity over `k`.**
`∑_σ c_λ(σ) · χ_{V_{la'}}(σ) = α · δ_{la, la'}`. -/
theorem youngSym_trace_kronecker_K (n : ℕ) (la la' : Nat.Partition n)
    (α : k)
    (hα_sq : YoungSymmetrizerK k n la * YoungSymmetrizerK k n la =
      α • YoungSymmetrizerK k n la) :
    ∑ σ : G n, (YoungSymmetrizerK k n la σ) * spechtBlockCharacterK k n la' σ =
      if la = la' then α else 0 := by
  rw [sum_coeff_char_eq_traceK]
  split_ifs with h
  · subst h; exact trace_mulLeft_youngSym_eqK n la α hα_sq
  · rw [mulLeft_youngSym_zero_of_neK n la la' h, map_zero]

/-! ### A trace-zero idempotent over a characteristic-zero field is zero -/

/-- An idempotent endomorphism of a finite-dimensional vector space over a
characteristic-zero field with vanishing trace is the zero map. -/
private theorem isIdempotentElem_eq_zero_of_trace_eq_zero
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {e : V →ₗ[k] V} (he : IsIdempotentElem e)
    (htr : LinearMap.trace k V e = 0) :
    e = 0 := by
  have hproj : LinearMap.IsProj (LinearMap.range e) e :=
    LinearMap.IsIdempotentElem.isProj_range _ he
  have htr_eq : LinearMap.trace k V e = (Module.finrank k (LinearMap.range e) : k) :=
    hproj.trace
  rw [htr] at htr_eq
  have hfinrank_zero : Module.finrank k (LinearMap.range e) = 0 := by
    have h : ((Module.finrank k (LinearMap.range e) : ℕ) : k) = 0 := htr_eq.symm
    exact_mod_cast h
  rw [← LinearMap.range_eq_bot, ← Submodule.finrank_eq_zero]
  exact hfinrank_zero

/-! ### The two special-block endomorphism lemmas over `k` -/

set_option maxHeartbeats 800000 in
-- The `Module k ↥(S.restrictScalars k)` instance and `LinearMap.restrict`
-- reduction traverse the deep `Subalgebra → Subsemiring → Module → IsScalarTower`
-- synthesis chain for `symGroupImage`, which exceeds the default budgets.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Off-block vanishing (general `k`).** When the simple `symGroupImage`-stable
submodule `S ≤ V^⊗n` has Specht-module character that of `la' ≠ weightToPartition
N lam`, the Young-symmetrizer endomorphism `c_λ` vanishes on `S`. -/
theorem youngSym_action_vanishes_off_block_general
    (N : ℕ) (lam : Fin N → ℕ)
    (S : Submodule (symGroupImage k (Fin N → k) (∑ i, lam i))
      (TensorPower k (Fin N → k) (∑ i, lam i)))
    [Module.Finite k ↥(S.restrictScalars k)]
    (la' : Nat.Partition (∑ i, lam i))
    (h_label : ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace k ↥(S.restrictScalars k)
            ((symGroupAction k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
              (p := S.restrictScalars k) (q := S.restrictScalars k)
              (fun _ hv =>
                symGroupAction_mem_of_symGroupImage_submodule S σ hv)) =
          spechtBlockCharacterK k (∑ i, lam i) la' σ)
    (h_ne : la' ≠ weightToPartition N lam) :
    (youngSymEndomorphism k N lam).restrict
        (p := S.restrictScalars k) (q := S.restrictScalars k)
        (fun _ hv =>
          S.smul_mem (youngSymElement k N lam) hv) = 0 := by
  let f : ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k) :=
    (youngSymEndomorphism k N lam).restrict
      (p := S.restrictScalars k) (q := S.restrictScalars k)
      (fun _ hv => S.smul_mem (youngSymElement k N lam) hv)
  change f = 0
  obtain ⟨α, hα_sq⟩ :=
    YoungSymmetrizerK_sq_scalar k (∑ i, lam i) (weightToPartition N lam)
  have hα_ne : α ≠ 0 :=
    YoungSymmetrizerK_sq_scalar_ne_zero_general k (∑ i, lam i) (weightToPartition N lam) α hα_sq
  have h_trace_f : LinearMap.trace k _ f =
      ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam) σ) *
        LinearMap.trace k _
          ((symGroupAction k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
            (p := S.restrictScalars k) (q := S.restrictScalars k)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule S σ hv)) :=
    trace_youngSymEndomorphism_restrict_eq_sum N lam S
  have h_trace_zero : LinearMap.trace k _ f = 0 := by
    rw [h_trace_f]
    conv_lhs => arg 2; ext σ; rw [h_label σ]
    rw [youngSym_trace_kronecker_K (∑ i, lam i) (weightToPartition N lam) la' α hα_sq,
        if_neg (fun h => h_ne h.symm)]
  have hf_sq : f * f = α • f :=
    youngSymEndomorphism_restrict_sq_scalar N lam S α hα_sq
  let g : ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k) := α⁻¹ • f
  have hg_idem : IsIdempotentElem g := by
    change (α⁻¹ • f) * (α⁻¹ • f) = α⁻¹ • f
    rw [smul_mul_smul_comm, hf_sq, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]
  have hg_tr_zero : LinearMap.trace k _ g = 0 := by
    change LinearMap.trace k _ (α⁻¹ • f) = 0
    rw [LinearMap.map_smul, h_trace_zero, smul_zero]
  have hg_zero : g = 0 := isIdempotentElem_eq_zero_of_trace_eq_zero hg_idem hg_tr_zero
  have hf_eq_smul_g : f = α • g := by
    change f = α • (α⁻¹ • f)
    rw [smul_smul, mul_inv_cancel₀ hα_ne, one_smul]
  rw [hf_eq_smul_g, hg_zero, smul_zero]

set_option maxHeartbeats 800000 in
-- The `Module k ↥(S.restrictScalars k)` instance and `LinearMap.restrict`
-- reduction traverse the deep `Subalgebra → Subsemiring → Module → IsScalarTower`
-- synthesis chain for `symGroupImage`, which exceeds the default budgets.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Rank-1 scaled projection on the special block (general `k`).** On a simple
`symGroupImage`-stable submodule `S ≤ V^⊗n` whose Specht character equals that of
`weightToPartition N lam`, the restricted endomorphism `f = c_λ|_S` factors as
`α • π` for a nonzero scalar `α` and a rank-1 idempotent `π`. -/
theorem youngSym_action_on_special_block_rank_one_scaled_proj_general
    (N : ℕ) (lam : Fin N → ℕ)
    (S : Submodule (symGroupImage k (Fin N → k) (∑ i, lam i))
      (TensorPower k (Fin N → k) (∑ i, lam i)))
    [Module.Finite k ↥(S.restrictScalars k)]
    (h_label : ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
        LinearMap.trace k ↥(S.restrictScalars k)
            ((symGroupAction k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
              (p := S.restrictScalars k) (q := S.restrictScalars k)
              (fun _ hv =>
                symGroupAction_mem_of_symGroupImage_submodule S σ hv)) =
          spechtBlockCharacterK k (∑ i, lam i) (weightToPartition N lam) σ) :
    ∃ (α : k) (π : ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k)),
      α ≠ 0 ∧ π * π = π ∧
      Module.finrank k (LinearMap.range π) = 1 ∧
      (youngSymEndomorphism k N lam).restrict
          (p := S.restrictScalars k) (q := S.restrictScalars k)
          (fun _ hv =>
            S.smul_mem (youngSymElement k N lam) hv) = α • π := by
  let f : ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k) :=
    (youngSymEndomorphism k N lam).restrict
      (p := S.restrictScalars k) (q := S.restrictScalars k)
      (fun _ hv => S.smul_mem (youngSymElement k N lam) hv)
  obtain ⟨α, hα_sq⟩ :=
    YoungSymmetrizerK_sq_scalar k (∑ i, lam i) (weightToPartition N lam)
  have hα_ne : α ≠ 0 :=
    YoungSymmetrizerK_sq_scalar_ne_zero_general k (∑ i, lam i) (weightToPartition N lam) α hα_sq
  have h_trace_f : LinearMap.trace k _ f =
      ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam) σ) *
        LinearMap.trace k _
          ((symGroupAction k (Fin N → k) (∑ i, lam i) σ).toLinearMap.restrict
            (p := S.restrictScalars k) (q := S.restrictScalars k)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule S σ hv)) :=
    trace_youngSymEndomorphism_restrict_eq_sum N lam S
  have h_trace_eq_alpha : LinearMap.trace k _ f = α := by
    rw [h_trace_f]
    conv_lhs => arg 2; ext σ; rw [h_label σ]
    rw [youngSym_trace_kronecker_K (∑ i, lam i) (weightToPartition N lam)
        (weightToPartition N lam) α hα_sq, if_pos rfl]
  have hf_sq : f * f = α • f :=
    youngSymEndomorphism_restrict_sq_scalar N lam S α hα_sq
  set π : ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k) := α⁻¹ • f with hπ_def
  have hπ_idem : π * π = π := by
    rw [hπ_def, smul_mul_smul_comm, hf_sq, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]
  have hπ_proj : LinearMap.IsProj (LinearMap.range π) π :=
    { map_mem := fun x => LinearMap.mem_range_self π x
      map_id := fun x hx => by
        obtain ⟨y, rfl⟩ := hx
        exact LinearMap.congr_fun hπ_idem y }
  have hπ_trace : LinearMap.trace k _ π = 1 := by
    rw [hπ_def, LinearMap.map_smul, h_trace_eq_alpha, smul_eq_mul, inv_mul_cancel₀ hα_ne]
  have hπ_rank : Module.finrank k (LinearMap.range π) = 1 := by
    have h := hπ_proj.trace
    rw [hπ_trace] at h
    exact_mod_cast h.symm
  have hf_eq : f = α • π := by
    rw [hπ_def, smul_smul, mul_inv_cancel₀ hα_ne, one_smul]
  exact ⟨α, π, hα_ne, hπ_idem, hπ_rank, hf_eq⟩

end Etingof
