import Mathlib

/-!
# Trace of an endomorphism on the coinvariants of a finite-group representation

For a finite group `Γ` acting on a finite-dimensional module `W` over a field of
characteristic zero, and an intertwining endomorphism `Φ` of the representation `σ`, the
trace of the induced map on the coinvariants `W_Γ = Coinvariants σ` is the average over
`h ∈ Γ` of the trace of `σ(h) ∘ Φ`:

  `tr_{W_Γ}(Φ̄) = (1/|Γ|) · Σ_{h ∈ Γ} tr_W(σ(h) ∘ Φ)`.

This is the abstract heart of the Frobenius character formula (Etingof Theorem 5.9.1).

## Proof outline

Let `e = averageMap σ = (1/|Γ|) Σ_h σ(h)`, the averaging projection onto the invariants
`P = invariants σ`. Its kernel is exactly the coinvariants relation submodule
`K = Coinvariants.ker σ`, so `P` and `K` are complementary and the quotient map restricts to
a linear isomorphism `ι : Coinvariants σ ≃ P`.

* Under `ι`, the induced map `Φ̄ = Coinvariants.map σ σ Φ` is conjugate to the restriction
  `Φ_P : P → P` of `Φ` (which preserves the invariants because it commutes with `σ`); hence
  `tr(Φ̄) = tr(Φ_P)` by conjugation-invariance of the trace.
* `tr_P(Φ_P) = tr_W(e ∘ Φ)`: writing `e = j ∘ p` with `j = P.subtype` and `p` the corestriction
  of `e`, the cyclic property `tr(j ∘ (p∘Φ)) = tr((p∘Φ) ∘ j)` and `p ∘ Φ ∘ j = Φ_P` give it.
* `tr_W(e ∘ Φ) = (1/|Γ|) Σ_h tr_W(σ(h) ∘ Φ)` by linearity of the trace and `e = (1/|Γ|)Σ σ(h)`.
-/

open Representation LinearMap

namespace Etingof

variable {k : Type*} [Field k]
    {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Fintype.card Γ : k)]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    (σ : Representation k Γ W)

omit [Module.Finite k W] in
/-- The averaging projection as an explicit linear combination of the group action. -/
lemma averageMap_eq :
    averageMap σ = (Fintype.card Γ : k)⁻¹ • ∑ h : Γ, σ h := by
  simp only [averageMap, GroupAlgebra.average, map_smul, map_sum, asAlgebraHom_of, invOf_eq_inv]

omit [Module.Finite k W] in
lemma averageMap_apply (w : W) :
    averageMap σ w = (Fintype.card Γ : k)⁻¹ • ∑ h : Γ, σ h w := by
  rw [averageMap_eq]; simp

omit [Module.Finite k W] in
/-- The kernel of the averaging projection is exactly the coinvariants relation submodule. -/
lemma ker_averageMap : LinearMap.ker (averageMap σ) = Coinvariants.ker σ := by
  apply le_antisymm
  · intro w hw
    have hsub : w - averageMap σ w ∈ Coinvariants.ker σ := by
      have hne : (Fintype.card Γ : k) ≠ 0 := Invertible.ne_zero _
      have hrw : w - averageMap σ w
          = (Fintype.card Γ : k)⁻¹ • ∑ h : Γ, (w - σ h w) := by
        rw [averageMap_apply, Finset.sum_sub_distrib, smul_sub, Finset.sum_const,
          Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [hrw]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ ?_)
      intro h _
      have := Coinvariants.sub_mem_ker (ρ := σ) h w
      simpa [neg_sub] using (Submodule.neg_mem _ this)
    have : w = w - averageMap σ w := by
      rw [LinearMap.mem_ker] at hw; rw [hw, sub_zero]
    rw [this]; exact hsub
  · rw [Coinvariants.ker, Submodule.span_le]
    rintro _ ⟨⟨g, x⟩, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
    have key : averageMap σ (σ g x) = averageMap σ x := by
      rw [averageMap_apply, averageMap_apply]
      congr 1
      rw [← Equiv.sum_comp (Equiv.mulRight g) (fun h => σ h x)]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      simp only [Equiv.coe_mulRight, map_mul, Module.End.mul_apply]
    rw [key, sub_self]

omit [Invertible (Fintype.card Γ : k)] [Fintype Γ] [Module.Finite k W] in
/-- `Φ` preserves the invariants, since it commutes with the group action. -/
lemma intertwiningMap_mapsTo_invariants (Φ : IntertwiningMap σ σ) :
    ∀ x ∈ invariants σ, Φ.toLinearMap x ∈ invariants σ := by
  intro x hx
  rw [mem_invariants] at hx ⊢
  intro g
  have h : Φ.toLinearMap (σ g x) = σ g (Φ.toLinearMap x) := congr($(Φ.isIntertwining' g) x)
  rw [hx g] at h
  exact h.symm

/-- **Trace on coinvariants is the average of twisted traces.**

For a finite group `Γ` acting on a finite-dimensional char-zero module `W`, and an
intertwining endomorphism `Φ`, the trace of the induced map on `Coinvariants σ` equals
`(1/|Γ|) · Σ_{h} tr_W(σ(h) ∘ Φ)`. -/
theorem trace_coinvariantsMap (Φ : IntertwiningMap σ σ) :
    LinearMap.trace k (Coinvariants σ) (Coinvariants.map σ σ Φ)
      = (Fintype.card Γ : k)⁻¹ * ∑ h : Γ, LinearMap.trace k W (σ h ∘ₗ Φ.toLinearMap) := by
  have hΦP := intertwiningMap_mapsTo_invariants σ Φ
  -- The corestriction of the averaging projection onto the invariants.
  set p : W →ₗ[k] invariants σ :=
    (averageMap σ).codRestrict (invariants σ) (averageMap_invariant σ) with hp
  have hsubp : (invariants σ).subtype ∘ₗ p = averageMap σ :=
    LinearMap.subtype_comp_codRestrict _ _ _
  have hpid : ∀ x : invariants σ, p x = x := by
    intro x
    apply Subtype.ext
    simp only [hp, LinearMap.codRestrict_apply]
    exact averageMap_id σ x x.2
  -- `Φ` restricted to the invariants.
  set Φ_P : invariants σ →ₗ[k] invariants σ := Φ.toLinearMap.restrict hΦP with hΦ_P
  -- `P` and `K` are complementary; the quotient map restricts to an iso `Coinvariants σ ≃ P`.
  have hkerp : LinearMap.ker p = Coinvariants.ker σ := by
    rw [hp, LinearMap.ker_codRestrict, ker_averageMap]
  have hcompl : IsCompl (Coinvariants.ker σ) (invariants σ) := by
    have h1 := LinearMap.isCompl_of_proj hpid
    rw [hkerp] at h1
    exact h1.symm
  set ι : Coinvariants σ ≃ₗ[k] invariants σ :=
    Submodule.quotientEquivOfIsCompl _ _ hcompl with hι
  -- Step 1 : `tr_C(Φ̄) = tr_P(Φ_P)`.
  have hsymm : ∀ x : invariants σ, ι.symm x = Coinvariants.mk σ (x : W) := by
    intro x
    refine ι.symm_apply_eq.2 ?_
    rw [hι]
    exact (Submodule.quotientEquivOfIsCompl_apply_mk_right hcompl x).symm
  have hconj : ι.conj (Coinvariants.map σ σ Φ) = Φ_P := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.conj_apply_apply, hsymm x, Coinvariants.map_mk,
      ← IntertwiningMap.toLinearMap_apply]
    have hcoe : Φ.toLinearMap (x : W) = ((Φ_P x : invariants σ) : W) := by
      rw [hΦ_P, LinearMap.restrict_apply]
    rw [hcoe, ← hsymm (Φ_P x), ι.apply_symm_apply]
  have step1 : LinearMap.trace k (Coinvariants σ) (Coinvariants.map σ σ Φ)
      = LinearMap.trace k (invariants σ) Φ_P := by
    rw [← LinearMap.trace_conj' (Coinvariants.map σ σ Φ) ι, hconj]
  -- Step 2 : `tr_P(Φ_P) = tr_W(e ∘ Φ)`.
  have hcomp : p ∘ₗ Φ.toLinearMap ∘ₗ (invariants σ).subtype = Φ_P := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hp, LinearMap.codRestrict_apply,
      hΦ_P, LinearMap.restrict_apply]
    exact averageMap_id σ _ (hΦP x x.2)
  have step2 : LinearMap.trace k (invariants σ) Φ_P
      = LinearMap.trace k W (averageMap σ ∘ₗ Φ.toLinearMap) := by
    rw [← hcomp, ← LinearMap.comp_assoc,
      LinearMap.trace_comp_comm' ((invariants σ).subtype) (p ∘ₗ Φ.toLinearMap),
      ← hsubp, LinearMap.comp_assoc]
  -- Step 3 : `tr_W(e ∘ Φ) = (1/|Γ|) Σ_h tr_W(σ(h) ∘ Φ)`.
  have step3 : LinearMap.trace k W (averageMap σ ∘ₗ Φ.toLinearMap)
      = (Fintype.card Γ : k)⁻¹ * ∑ h : Γ, LinearMap.trace k W (σ h ∘ₗ Φ.toLinearMap) := by
    have hcomp_sum : (∑ h : Γ, σ h) ∘ₗ Φ.toLinearMap = ∑ h : Γ, (σ h ∘ₗ Φ.toLinearMap) := by
      ext w; simp [LinearMap.sum_apply]
    rw [averageMap_eq, LinearMap.smul_comp, hcomp_sum, map_smul, map_sum, smul_eq_mul]
  rw [step1, step2, step3]

section Helpers

/-- The trace of `Finsupp.lmapDomain k k φ` on the free module `ι →₀ k`, for a self-map `φ`
of a finite type, counts the fixed points of `φ`. -/
lemma trace_lmapDomain {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → ι) :
    LinearMap.trace k (ι →₀ k) (Finsupp.lmapDomain k k φ)
      = ∑ x : ι, if φ x = x then (1 : k) else 0 := by
  rw [LinearMap.trace_eq_matrix_trace k Finsupp.basisSingleOne, Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne]
  simp [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply]

/-- A sum over a subgroup `H` of an indicator on the coercion `↑h = a` picks out the unique
preimage when `a ∈ H`. -/
lemma sum_subtype_ite_coe {G : Type*} [Group G] [DecidableEq G] (H : Subgroup G) [Fintype H]
    [DecidablePred (· ∈ H)] {k : Type*} [AddCommMonoid k] (a : G) (f : H → k) :
    ∑ h : H, (if (↑h : G) = a then f h else 0) = if ha : a ∈ H then f ⟨a, ha⟩ else 0 := by
  by_cases ha : a ∈ H
  · rw [dif_pos ha]
    have hcongr : ∀ h : H, (if (↑h : G) = a then f h else 0)
        = (if h = (⟨a, ha⟩ : H) then f h else 0) := by
      intro h
      by_cases hh : h = ⟨a, ha⟩
      · subst hh; simp
      · have hne : (↑h : G) ≠ a := fun hc => hh (Subtype.ext hc)
        rw [if_neg hne, if_neg hh]
    rw [Finset.sum_congr rfl (fun h _ => hcongr h), Finset.sum_ite_eq']
    simp
  · rw [dif_neg ha]
    refine Finset.sum_eq_zero fun h _ => ?_
    rw [if_neg]
    intro hc; exact ha (hc ▸ h.2)

end Helpers

end Etingof


