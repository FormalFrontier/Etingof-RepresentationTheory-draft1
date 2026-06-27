import Mathlib
import EtingofRepresentationTheory.Chapter5.DetInvElim

/-!
# Formal character of a dual `GL_N`-representation (analytic fact (a))

Etingof §5.23. For a finite-dimensional `GL_N(k)`-representation `ρ`, the dual
representation `Representation.dual ρ` (Mathlib: `(dual ρ) g = f ∘ ρ g⁻¹`) records
`ρ`'s torus character read at *inverse* weights: the dual rep negates weights. This
is the building block (a) behind the contragredient identity `L*_λ ≅ L_λ^∨`
(#5526 / #5529).

## Main results

* `dual_diagUnit_dualBasis` (always true) — given a torus weight eigenbasis `b` of
  `ρ` with weights `wt`, the **dual basis** `b.dualBasis` is again a torus weight
  eigenbasis of `Representation.dual ρ`, with weights `-wt`. This is the precise
  sense in which the diagonal torus acts on the dual by inverse weights.

* `finrank_glWeightSpaceℤ_of_eigenbasis` (always true) — from a weight eigenbasis,
  the dimension of the integer weight space `glWeightSpaceℤ ρ ν` equals the number
  of basis vectors of weight `ν`.

* `finrank_glWeightSpaceℤ_dual_eq` (the reusable core) — combining the two, for a
  representation with a weight eigenbasis,
  `dim (glWeightSpaceℤ (dual ρ) μ) = dim (glWeightSpaceℤ ρ (-μ))`: the weight-`μ`
  space of the dual is dual to `ρ`'s weight-`(-μ)` space.

* `formalCharacter_dual_coeff_eq` (the consumer-facing form) — for a polynomial
  `GL_N`-rep `M` (spanning `ℕ`-weight spaces, `h_span`), the coefficient of `x^μ`
  in `formalCharacter (FDRep.of (dual M.ρ))` is `dim (glWeightSpaceℤ M.ρ (-μ))`:
  the `ℕ`-weight `formalCharacter (dual M.ρ)` collects exactly `M.ρ`'s non-positive
  weights, read with the sign flipped. Since `M.ρ`'s weights are `≥ 0`, the only
  weight surviving the `ℕ`-truncation is `μ = 0`.

The eigenbasis hypothesis is the honest carrier of polynomiality: `formalCharacter`
is a *truncated* invariant (it sees only `ℕ`-weights), so the statement lives at the
weight-space level, where a `det^s`-twist later brings the negative dual weights back
into range.
-/

noncomputable section

namespace Etingof

open Etingof.KernelLemmaKPrime

variable {k : Type*} [Field k] {N : ℕ}

/-! ### Torus inverse and a `ℤ`-power separation lemma -/

/-- The inverse of a diagonal torus unit is the diagonal unit at the inverse scalar. -/
theorem diagUnit_inv (k : Type*) [Field k] (N : ℕ) (i : Fin N) (t : kˣ) :
    (diagUnit k N i t)⁻¹ = diagUnit k N i t⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  exact (diagUnit k N i t).val_inv

/-- In a characteristic-zero field, distinct integer exponents give distinct power
functions of some unit: there is `t ∈ kˣ` with `t^a ≠ t^b`. (Witness: `t = 2`.) -/
theorem exists_unit_zpow_ne (k : Type*) [Field k] [CharZero k] {a b : ℤ} (hab : a ≠ b) :
    ∃ t : kˣ, ((t ^ a : kˣ) : k) ≠ ((t ^ b : kˣ) : k) := by
  refine ⟨Units.mk0 (2 : k) (by norm_num), ?_⟩
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  intro h
  apply hab
  have htrans : ∀ n : ℤ, (2 : k) ^ n = algebraMap ℚ k ((2 : ℚ) ^ n) := by
    intro n; rw [map_zpow₀, map_ofNat]
  rw [htrans a, htrans b] at h
  have hQ : (2 : ℚ) ^ a = (2 : ℚ) ^ b := (algebraMap ℚ k).injective h
  exact zpow_right_injective₀ (by norm_num) (by norm_num) hQ

/-! ### Weight-space dimension from an eigenbasis -/

/-- **Eigenbasis ⟹ weight-space dimension is a basis count.** If `b` is a basis of
torus weight eigenvectors with weights `wt`, then the integer weight space
`glWeightSpaceℤ ρ ν` is exactly the span of the eigenvectors of weight `ν`, hence its
dimension is the number of such eigenvectors. -/
theorem finrank_glWeightSpaceℤ_of_eigenbasis (k : Type*) [Field k] [CharZero k]
    (N d : ℕ) {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (b : Module.Basis (Fin d) k W) (wt : Fin d → Fin N → ℤ)
    (hb : ∀ (c : Fin d) (i : Fin N) (t : kˣ),
        σ (diagUnit k N i t) (b c) = ((t ^ wt c i : kˣ) : k) • b c)
    (ν : Fin N → ℤ) :
    Module.finrank k (glWeightSpaceℤ k N σ ν)
      = (Finset.univ.filter (fun c => wt c = ν)).card := by
  classical
  have hspan : glWeightSpaceℤ k N σ ν
      = Submodule.span k (Set.range (fun c : {c : Fin d // wt c = ν} => b c.val)) := by
    apply le_antisymm
    · -- `⊆`: any weight-`ν` vector is supported on matching eigenbasis vectors.
      intro w hw
      simp only [glWeightSpaceℤ, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero] at hw
      set r := b.repr w with hr
      have hzero : ∀ c, wt c ≠ ν → r c = 0 := by
        intro c hc
        obtain ⟨i, hi⟩ : ∃ i, wt c i ≠ ν i := by
          by_contra h; push_neg at h; exact hc (funext h)
        obtain ⟨t, ht⟩ := exists_unit_zpow_ne k hi
        have expand : σ (diagUnit k N i t) w
            = ∑ dd, (r dd * ((t ^ wt dd i : kˣ) : k)) • b dd := by
          conv_lhs => rw [show w = ∑ dd, r dd • b dd from (b.sum_repr w).symm]
          rw [map_sum]
          refine Finset.sum_congr rfl (fun dd _ => ?_)
          rw [map_smul, hb dd i t, smul_smul]
        have e1 : b.repr (σ (diagUnit k N i t) w) c = r c * ((t ^ wt c i : kˣ) : k) := by
          rw [expand, map_sum, Finsupp.finsetSum_apply]
          simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply,
            smul_eq_mul, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq' Finset.univ c
            (fun dd => r dd * ((t ^ wt dd i : kˣ) : k))]
          simp
        have e2 : b.repr (σ (diagUnit k N i t) w) c = ((t ^ ν i : kˣ) : k) * r c := by
          rw [hw i t, map_smul, Finsupp.smul_apply, smul_eq_mul]
        have key : r c * ((t ^ wt c i : kˣ) : k) = ((t ^ ν i : kˣ) : k) * r c := by
          rw [← e1, e2]
        have h0 : r c * (((t ^ wt c i : kˣ) : k) - ((t ^ ν i : kˣ) : k)) = 0 := by
          linear_combination key
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exact absurd (sub_eq_zero.1 h) ht
      rw [show w = ∑ c, r c • b c from (b.sum_repr w).symm]
      apply Submodule.sum_mem
      intro c _
      by_cases hc : wt c = ν
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hc⟩, rfl⟩)
      · rw [hzero c hc, zero_smul]; exact Submodule.zero_mem _
    · -- `⊇`: each matching eigenbasis vector lies in the weight space.
      rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      simp only [SetLike.mem_coe, glWeightSpaceℤ, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero]
      intro i t
      rw [hb c.val i t, show wt c.val i = ν i from congrFun c.property i]
  rw [hspan,
    finrank_span_eq_card
      (show LinearIndependent k (fun c : {c : Fin d // wt c = ν} => b c.val) from
        b.linearIndependent.comp Subtype.val Subtype.val_injective),
    Fintype.card_subtype]

/-! ### The dual basis is a weight eigenbasis with negated weights -/

/-- **The dual basis is a torus weight eigenbasis of the dual representation.** If
`b` is a basis of torus weight eigenvectors of `σ` with weights `wt`, then each dual
basis vector `b.dualBasis c` is a weight eigenvector of `Representation.dual σ` with
weight `-wt c`. -/
theorem dual_diagUnit_dualBasis (k : Type*) [Field k] (N d : ℕ)
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (b : Module.Basis (Fin d) k W) (wt : Fin d → Fin N → ℤ)
    (hb : ∀ (c : Fin d) (i : Fin N) (t : kˣ),
        σ (diagUnit k N i t) (b c) = ((t ^ wt c i : kˣ) : k) • b c)
    (c : Fin d) (i : Fin N) (t : kˣ) :
    (Representation.dual σ) (diagUnit k N i t) (b.dualBasis c)
      = ((t ^ (- wt c i) : kˣ) : k) • b.dualBasis c := by
  apply Module.Basis.ext b
  intro e
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    diagUnit_inv, hb e i t⁻¹, map_smul, LinearMap.smul_apply,
    Module.Basis.dualBasis_apply_self]
  by_cases h : e = c
  · subst h
    rw [if_pos rfl, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    congr 1
    rw [inv_zpow, zpow_neg]
  · rw [if_neg h, smul_zero, smul_zero]

/-! ### The dual weight space at `μ` is dual to `ρ`'s weight space at `-μ` -/

/-- **Fact (a), weight-space level.** For a representation with a torus weight
eigenbasis, the weight-`μ` space of the dual representation has the same dimension as
`ρ`'s weight-`(-μ)` space: the dual rep negates weights. -/
theorem finrank_glWeightSpaceℤ_dual_eq (k : Type*) [Field k] [CharZero k]
    (N d : ℕ) {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (b : Module.Basis (Fin d) k W) (wt : Fin d → Fin N → ℤ)
    (hb : ∀ (c : Fin d) (i : Fin N) (t : kˣ),
        σ (diagUnit k N i t) (b c) = ((t ^ wt c i : kˣ) : k) • b c)
    (μ : Fin N → ℤ) :
    Module.finrank k (glWeightSpaceℤ k N (Representation.dual σ) μ)
      = Module.finrank k (glWeightSpaceℤ k N σ (fun i => - μ i)) := by
  classical
  rw [finrank_glWeightSpaceℤ_of_eigenbasis k N d (Representation.dual σ) b.dualBasis
        (fun c i => - wt c i) (fun c i t => dual_diagUnit_dualBasis k N d σ b wt hb c i t) μ,
      finrank_glWeightSpaceℤ_of_eigenbasis k N d σ b wt hb (fun i => - μ i)]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; funext i; have := congrFun h i; omega
  · intro h; funext i; have := congrFun h i; omega

/-! ### Bridge to the `ℕ`-weight `formalCharacter` -/

/-- The `ℕ`-weight space of an `FDRep` is the corresponding integer weight space of
its underlying representation. -/
theorem glWeightSpace_eq_glWeightSpaceℤ (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (μ : Fin N → ℕ) :
    glWeightSpace k N M (fun i => μ i)
      = glWeightSpaceℤ k N M.ρ (fun i => (μ i : ℤ)) := by
  simp only [glWeightSpace, glWeightSpaceℤ]
  refine iInf_congr fun i => iInf_congr fun t => ?_
  have hs : ((t ^ (μ i : ℤ) : kˣ) : k) = (t : k) ^ μ i := by
    rw [Units.val_zpow_eq_zpow_val, zpow_natCast]
  rw [hs]

/-- **Fact (a), `formalCharacter` corollary.** For a polynomial `GL_N`-representation
`M` (spanning `ℕ`-weight spaces, `h_span`), the coefficient of `x^μ` in the formal
character of the dual `FDRep.of (dual M.ρ)` is the dimension of `M.ρ`'s integer
weight space at `-μ`. Since `M.ρ`'s weights are `≥ 0`, this vanishes unless `μ = 0`:
the `ℕ`-truncated dual character collects exactly `M.ρ`'s non-positive weights, read
with the sign flipped. -/
theorem formalCharacter_dual_coeff_eq (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N : ℕ) (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (μ : Fin N →₀ ℕ) :
    (formalCharacter k N (FDRep.of (Representation.dual M.ρ))).coeff μ
      = (Module.finrank k (glWeightSpaceℤ k N M.ρ (fun i => - (μ i : ℤ))) : ℚ) := by
  obtain ⟨d, v, wt, hv⟩ := Etingof.DetInvElim.exists_weight_eigenbasis M h_span
  have hvℤ : ∀ (c : Fin d) (i : Fin N) (t : kˣ),
      M.ρ (diagUnit k N i t) (v c) = ((t ^ (wt c i : ℤ) : kˣ) : k) • v c := by
    intro c i t
    rw [hv c i t, Units.val_zpow_eq_zpow_val, zpow_natCast]
  have hmain := finrank_glWeightSpaceℤ_dual_eq k N d M.ρ v (fun c i => (wt c i : ℤ)) hvℤ
    (fun i => (μ i : ℤ))
  rw [formalCharacter_coeff k N (FDRep.of (Representation.dual M.ρ)) μ,
    glWeightSpace_eq_glWeightSpaceℤ k N (FDRep.of (Representation.dual M.ρ)) (fun i => μ i),
    FDRep.of_ρ', hmain]

end Etingof
