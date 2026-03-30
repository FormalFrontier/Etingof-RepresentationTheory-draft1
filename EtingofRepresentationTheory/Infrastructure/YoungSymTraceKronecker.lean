import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.Theorem5_15_1
import EtingofRepresentationTheory.Infrastructure.SpechtModuleSimple

/-!
# Young Symmetrizer Trace Kronecker Identity

  `∑_σ c_λ(σ) · χ_{V_{λ'}}(σ) = α · δ_{λ,λ'}`

## Proof strategy

- **Off-diagonal (λ ≠ λ')**: Construct an A-linear map `V_λ → V_{λ'}` from
  any nonzero action of `c_λ` on `V_{λ'}`, contradicting non-isomorphism
  via Schur's lemma and `Theorem5_12_2_distinct`.
- **Diagonal (λ = λ')**: Factor `mulLeft(c)|_{V_λ}` through ℂ via the sandwich
  property (`Lemma5_13_1`) and `Submodule.mem_span_singleton`, then use
  `trace_comp_comm'` to compute `tr = α`.
- **Coefficient transfer**: Both `YoungSymmetrizerK ℚ` and `YoungSymmetrizer` (over ℂ)
  are base changes of `YoungSymmetrizerZ` (over ℤ), so their coefficients agree
  modulo the canonical maps `ℤ → ℚ → ℂ` and `ℤ → ℂ`.
-/

namespace Etingof

noncomputable section
open Classical in

/-! ### Coefficient transfer: ℚ ↔ ℂ -/

/-- The ℚ and ℂ Young symmetrizer coefficients agree under cast.
Both are images of `YoungSymmetrizerZ` (over ℤ) via base change. -/
private lemma youngSym_coeff_cast (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (YoungSymmetrizerK ℚ n la σ : ℂ) = YoungSymmetrizer n la σ := by
  sorry

/-- Transfer `c² = α·c` from ℚ to ℂ via the ℤ base change.
The scalar α is the same integer, viewed in ℚ then cast to ℂ. -/
private lemma youngSym_sq_ℂ (n : ℕ) (la : Nat.Partition n)
    (α : ℚ) (hα : YoungSymmetrizerK ℚ n la * YoungSymmetrizerK ℚ n la =
      α • YoungSymmetrizerK ℚ n la) :
    YoungSymmetrizer n la * YoungSymmetrizer n la = (α : ℂ) • YoungSymmetrizer n la := by
  sorry

/-! ### Left multiplication on Specht modules -/

private def mulLeftOnSpecht (n : ℕ) (c : SymGroupAlgebra n) (la' : Nat.Partition n) :
    ↥(SpechtModule n la') →ₗ[ℂ] ↥(SpechtModule n la') where
  toFun v := ⟨c * ↑v, (SpechtModule n la').smul_mem c v.prop⟩
  map_add' a b := Subtype.ext (mul_add c ↑a ↑b)
  map_smul' r v := Subtype.ext (Algebra.mul_smul_comm r c ↑v)

/-! ### Trace linearity -/

/-- The sum `∑_σ c(σ) · χ_{V}(σ)` equals the trace of left multiplication by `c` on `V`.
Uses the decomposition `c = ∑ c(σ) · of(σ)` and linearity of trace. -/
private lemma sum_coeff_char_eq_trace (n : ℕ) (la' : Nat.Partition n)
    (c : SymGroupAlgebra n) :
    ∑ σ : Equiv.Perm (Fin n), c σ * spechtModuleCharacter n la' σ =
      LinearMap.trace ℂ _ (mulLeftOnSpecht n c la') := by
  sorry

/-! ### Off-diagonal case -/

/-- Left multiplication by `c_λ` is zero on `V_{λ'}` when `λ ≠ λ'`.
If nonzero, right multiplication by a witness `w₀` gives an A-linear map
`V_λ → V_{λ'}`, which by Schur's lemma (both simple) is bijective,
contradicting `Theorem5_12_2_distinct`. -/
private lemma mulLeft_youngSym_zero_of_ne (n : ℕ) (la la' : Nat.Partition n) (hne : la ≠ la') :
    mulLeftOnSpecht n (YoungSymmetrizer n la) la' = 0 := by
  sorry

/-! ### Diagonal case -/

/-- The trace of left multiplication by `c_λ` on `V_λ = span({c_λ})` equals `α`.
Factor `T = ι ∘ π` where `ι : ℂ → V` and `π : V → ℂ` using the sandwich
property (`Lemma5_13_1`), then `tr(T) = tr(π ∘ ι) = α`. -/
private lemma trace_mulLeft_youngSym_eq (n : ℕ) (la : Nat.Partition n)
    (α : ℂ) (hα_ne : α ≠ 0)
    (hα_sq : YoungSymmetrizer n la * YoungSymmetrizer n la = α • YoungSymmetrizer n la) :
    LinearMap.trace ℂ _ (mulLeftOnSpecht n (YoungSymmetrizer n la) la) = α := by
  sorry

/-! ### Main theorem -/

/-- **Young symmetrizer trace Kronecker identity**:
`∑_σ c_λ(σ) · χ_{V_{λ'}}(σ) = α · δ_{λ,λ'}`. -/
theorem youngSym_trace_kronecker (n : ℕ) (la la' : Nat.Partition n)
    (α : ℚ) (hα_sq : YoungSymmetrizerK ℚ n la * YoungSymmetrizerK ℚ n la =
      α • YoungSymmetrizerK ℚ n la) :
    ∑ σ : Equiv.Perm (Fin n),
      (YoungSymmetrizerK ℚ n la σ : ℂ) * spechtModuleCharacter n la' σ =
      if la = la' then (α : ℂ) else 0 := by
  conv_lhs => arg 2; ext σ; rw [youngSym_coeff_cast]
  have hα_ℂ := youngSym_sq_ℂ n la α hα_sq
  have hα_ne : (α : ℂ) ≠ 0 := by exact_mod_cast YoungSymmetrizerK_sq_scalar_ne_zero n la α hα_sq
  rw [sum_coeff_char_eq_trace]
  split_ifs with h
  · subst h; exact trace_mulLeft_youngSym_eq n la (α : ℂ) hα_ne hα_ℂ
  · rw [mulLeft_youngSym_zero_of_ne n la la' h, map_zero]

end

end Etingof
