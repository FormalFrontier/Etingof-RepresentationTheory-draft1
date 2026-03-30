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
  rw [YoungSymmetrizerK_eq_mapRange ℚ n la, YoungSymmetrizer_eq_mapRange n la]
  simp only [MonoidAlgebra.mapRangeRingHom_apply]
  exact_mod_cast rfl

/-- Transfer `c² = α·c` from ℚ to ℂ via the ℤ base change.
The scalar α is the same integer, viewed in ℚ then cast to ℂ. -/
private lemma youngSym_sq_ℂ (n : ℕ) (la : Nat.Partition n)
    (α : ℚ) (hα : YoungSymmetrizerK ℚ n la * YoungSymmetrizerK ℚ n la =
      α • YoungSymmetrizerK ℚ n la) :
    YoungSymmetrizer n la * YoungSymmetrizer n la = (α : ℂ) • YoungSymmetrizer n la := by
  -- Key elements
  set cZ := YoungSymmetrizerZ n la
  set β : ℤ := (cZ * cZ) 1
  set φ_ℚ := MonoidAlgebra.mapRangeRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℚ)
  set φ_ℂ := MonoidAlgebra.mapRangeRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℂ)
  -- Relations to base change
  have h_ℚ : YoungSymmetrizerK ℚ n la = φ_ℚ cZ := YoungSymmetrizerK_eq_mapRange ℚ n la
  have h_ℂ : YoungSymmetrizer n la = φ_ℂ cZ := YoungSymmetrizer_eq_mapRange n la
  -- cZ(1) = 1
  have hcZ1 : cZ 1 = 1 := YoungSymmetrizerZ_apply_one n la
  -- Map hα to ℚ level: φ_ℚ(cZ * cZ) = α • φ_ℚ(cZ)
  have hmul_ℚ : φ_ℚ (cZ * cZ) = α • φ_ℚ cZ := by
    rw [map_mul]; exact h_ℚ ▸ hα
  -- Evaluating at 1: α = (β : ℚ)
  have hα_eq : α = (β : ℚ) := by
    have h1 := Finsupp.ext_iff.mp hmul_ℚ 1
    simp only [MonoidAlgebra.mapRangeRingHom_apply, MonoidAlgebra.smul_apply,
      smul_eq_mul, hcZ1, map_one, mul_one, φ_ℚ] at h1
    exact h1.symm
  -- Derive cZ * cZ = β • cZ over ℤ (by injectivity of ℤ → ℚ)
  have hZ : cZ * cZ = β • cZ := by
    ext σ
    have h1 := Finsupp.ext_iff.mp hmul_ℚ σ
    simp only [MonoidAlgebra.mapRangeRingHom_apply, MonoidAlgebra.smul_apply,
      smul_eq_mul, hα_eq, φ_ℚ] at h1
    have h2 : ((cZ * cZ) σ : ℚ) = ((β * cZ σ : ℤ) : ℚ) := by push_cast; exact h1
    have h3 : (cZ * cZ) σ = β * cZ σ := Int.cast_injective h2
    rw [MonoidAlgebra.smul_apply, smul_eq_mul, h3]
  -- Map to ℂ: c_ℂ * c_ℂ = (β : ℂ) • c_ℂ = (α : ℂ) • c_ℂ
  rw [h_ℂ, ← map_mul, hZ, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
  congr 1
  exact_mod_cast hα_eq.symm

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
  by_contra hT
  -- Find w₀ ∈ V_{la'} with T(w₀) ≠ 0, i.e., c_la * w₀ ≠ 0
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : SpechtModule n la',
      mulLeftOnSpecht n (YoungSymmetrizer n la) la' w₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hT (LinearMap.ext hall)
  -- Construct the A-linear map φ : V_la → V_{la'} by φ(v) = v * w₀
  set φ : SpechtModule n la →ₗ[SymGroupAlgebra n] SpechtModule n la' :=
    { toFun := fun v => ⟨(v : SymGroupAlgebra n) * (w₀ : SymGroupAlgebra n),
        (SpechtModule n la').smul_mem (v : SymGroupAlgebra n) w₀.prop⟩
      map_add' := fun a b => Subtype.ext (add_mul (a : SymGroupAlgebra n) b w₀)
      map_smul' := fun a v => Subtype.ext (mul_assoc a (v : SymGroupAlgebra n) w₀) }
  -- φ is nonzero: φ(c_la) = c_la * w₀ ≠ 0
  have hφ_ne : φ ≠ 0 := by
    intro h
    apply hw₀
    have : φ ⟨YoungSymmetrizer n la, Submodule.subset_span rfl⟩ = 0 :=
      congr_fun (congr_arg DFunLike.coe h) ⟨YoungSymmetrizer n la, Submodule.subset_span rfl⟩
    simp only [mulLeftOnSpecht, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢
    exact this
  -- Both modules are simple
  haveI : IsSimpleModule (SymGroupAlgebra n) (SpechtModule n la) :=
    Theorem5_12_2_irreducible n la
  haveI : IsSimpleModule (SymGroupAlgebra n) (SpechtModule n la') :=
    Theorem5_12_2_irreducible n la'
  -- By Schur's lemma, φ is bijective, giving an isomorphism V_la ≃ V_{la'}
  have hφ_bij := LinearMap.bijective_of_ne_zero hφ_ne
  exact (Theorem5_12_2_distinct n la la' hne).false (LinearEquiv.ofBijective φ hφ_bij)

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
