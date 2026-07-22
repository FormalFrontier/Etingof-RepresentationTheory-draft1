import EtingofRepresentationTheory.Infrastructure.SpechtModuleSimple

/-!
# General-`k` Specht character

This file lifts the Specht character `spechtModuleCharacter` (`Theorem5_15_1.lean`, ℂ-valued)
to a general characteristic-zero field `k`.

The ℂ character `spechtModuleCharacter n la σ` is the trace of left multiplication by `of σ`
on the left ideal `SpechtModule n la = ℂ[S_n]·c_λ`. The Schur-Weyl special-block analysis over
a general field needs a **`k`-valued** analogue, since the relevant traces over `k` land in `k`.

We define:
* `spechtModuleActionK k n la σ` — left multiplication by `of σ` on `SpechtModuleK k n la`;
* `spechtModuleCharacterK k n la σ : k` — its trace.

The key result is **field-independence**: writing `c_λ` over ℤ (`YoungSymmetrizerZ`), the
character equals `(N₀ : k)⁻¹ * (M₀ : k)` for two field-independent integers `N₀, M₀` coming from
the ℤ-coefficients of `c_λ` (`spechtModuleCharacterK_eq_intCast`). Hence
`spechtModuleCharacterK k n la σ = algebraMap ℚ k (spechtModuleCharacterK ℚ n la σ)`
(`spechtModuleCharacterK_algebraMap_rat`), and the ℂ specialisation recovers
`spechtModuleCharacter` (`spechtModuleCharacterK_complex`). From this we transfer the ℂ
injectivity (`spechtModuleCharacter_injective`) to `spechtModuleCharacterK_injective` over any
characteristic-zero field.
-/

noncomputable section

namespace Etingof

open MonoidAlgebra

variable (k : Type*) [Field k] [CharZero k]

/-- The left multiplication action of `σ ∈ S_n` on the general-`k` Specht module
`SpechtModuleK k n la = k[S_n]·c_λ`. Since `SpechtModuleK` is a left ideal, left multiplication
by `of σ` preserves it. -/
noncomputable def spechtModuleActionK (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    ↥(SpechtModuleK k n la) →ₗ[k] ↥(SpechtModuleK k n la) where
  toFun := fun m => ⟨MonoidAlgebra.of k _ σ * m.1,
    (SpechtModuleK k n la).smul_mem (MonoidAlgebra.of k _ σ) m.2⟩
  map_add' := fun a b => Subtype.ext (mul_add _ a.1 b.1)
  map_smul' := fun r a => Subtype.ext (Algebra.mul_smul_comm r _ a.1)

/-- The character of the general-`k` Specht module at `σ`: the trace of left multiplication by
`of σ` restricted to `SpechtModuleK k n la`. -/
noncomputable def spechtModuleCharacterK (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : k :=
  LinearMap.trace k _ (spechtModuleActionK k n la σ)

omit [CharZero k] in
/-- The coefficient of `c_λ` at the identity is `1`. -/
private lemma youngSymmetrizerK_apply_one (n : ℕ) (la : Nat.Partition n) :
    (YoungSymmetrizerK k n la) 1 = 1 := by
  rw [YoungSymmetrizerK_eq_mapRange k n la, MonoidAlgebra.mapRingHom_apply,
    YoungSymmetrizerZ_apply_one, map_one]

omit [CharZero k] in
/-- Trace of `x ↦ (of σ) · x · b` on `k[S_n]`, computed in the standard basis:
`trace = ∑_τ b(τ⁻¹ σ⁻¹ τ)`. -/
private lemma trace_mulLeft_of_comp_mulRight (n : ℕ) (σ : Equiv.Perm (Fin n))
    (b : MonoidAlgebra k (Equiv.Perm (Fin n))) :
    LinearMap.trace k _
        (LinearMap.mulLeft k (MonoidAlgebra.of k _ σ) ∘ₗ LinearMap.mulRight k b)
      = ∑ τ : Equiv.Perm (Fin n), b (τ⁻¹ * σ⁻¹ * τ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis (Equiv.Perm (Fin n)) k)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [LinearMap.comp_apply, MonoidAlgebra.basis_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply]
  have hrepr : ∀ (x : MonoidAlgebra k (Equiv.Perm (Fin n))) (g : Equiv.Perm (Fin n)),
      (MonoidAlgebra.basis (Equiv.Perm (Fin n)) k).repr x g = x g := fun _ _ => rfl
  rw [hrepr, MonoidAlgebra.of_apply, ← mul_assoc, MonoidAlgebra.single_mul_single, mul_one,
    MonoidAlgebra.single_mul_apply, one_mul, mul_inv_rev, mul_assoc]

/-- **Field-independence of the Specht character.** Writing `c_λ` over ℤ (`YoungSymmetrizerZ`),
the character equals `(N₀ : k)⁻¹ * (M₀ : k)` with `N₀ = (c_λ·c_λ)(1)` and
`M₀ = ∑_τ c_λ(τ⁻¹ σ⁻¹ τ)` both fixed integers, independent of `k`. -/
private lemma spechtModuleCharacterK_eq_intCast (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacterK k n la σ
      = (((YoungSymmetrizerZ n la * YoungSymmetrizerZ n la) 1 : ℤ) : k)⁻¹
        * ((∑ τ : Equiv.Perm (Fin n), (YoungSymmetrizerZ n la) (τ⁻¹ * σ⁻¹ * τ) : ℤ) : k) := by
  classical
  set c := YoungSymmetrizerK k n la with hc
  obtain ⟨α, hα⟩ := YoungSymmetrizerK_sq_scalar k n la
  have hα_ne : α ≠ 0 := YoungSymmetrizerK_sq_scalar_ne_zero_general k n la α hα
  -- Fixed-point property: every `s ∈ SpechtModuleK` is fixed by right-mult by the idempotent.
  have hfix : ∀ s ∈ SpechtModuleK k n la, s * (α⁻¹ • c) = s := by
    intro s hs
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
    rw [smul_eq_mul, mul_smul_comm, mul_assoc, hα, mul_smul_comm, smul_smul,
      inv_mul_cancel₀ hα_ne, one_smul]
  -- The composite `of σ · - · (α⁻¹ • c)` lands in `SpechtModuleK` (as a `k`-submodule).
  set F := LinearMap.mulLeft k (MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ)
      ∘ₗ LinearMap.mulRight k (α⁻¹ • c) with hFdef
  have hmem : ∀ x, F x ∈ (SpechtModuleK k n la).restrictScalars k := by
    intro x
    rw [Submodule.restrictScalars_mem, hFdef, LinearMap.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply]
    have h1 : x * (α⁻¹ • c) ∈ SpechtModuleK k n la := by
      rw [mul_smul_comm]
      exact Submodule.smul_of_tower_mem _ α⁻¹
        (Submodule.smul_mem _ x (Submodule.subset_span rfl))
    exact Submodule.smul_mem _ (MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ) h1
  -- Rewrite the character as the trace of `F` on all of `k[S_n]`, via the restriction lemma.
  have hchar : spechtModuleCharacterK k n la σ = LinearMap.trace k _ F := by
    rw [spechtModuleCharacterK,
      show spechtModuleActionK k n la σ
          = F.restrict (fun x (_ : x ∈ (SpechtModuleK k n la).restrictScalars k) => hmem x) from ?_]
    · exact LinearMap.trace_restrict_eq_of_forall_mem _ F hmem
    · apply LinearMap.ext
      intro s
      apply Subtype.ext
      change MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ * s.1 = F s.1
      rw [hFdef, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
        hfix s.1 s.2]
  -- Pull the scalar `α⁻¹` out of the trace and apply the trace formula.
  rw [hchar, hFdef]
  have hsmul : (LinearMap.mulLeft k (MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ) ∘ₗ
        LinearMap.mulRight k (α⁻¹ • c))
      = α⁻¹ • (LinearMap.mulLeft k (MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ)
        ∘ₗ LinearMap.mulRight k c) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
      LinearMap.smul_apply]
    rw [mul_smul_comm, mul_smul_comm]
  rw [hsmul, map_smul, trace_mulLeft_of_comp_mulRight, smul_eq_mul]
  -- Now identify `α⁻¹` and the sum with the integer expressions.
  have hα_int : α = (((YoungSymmetrizerZ n la * YoungSymmetrizerZ n la) 1 : ℤ) : k) := by
    have hcc : c * c =
        (MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom k))
          (YoungSymmetrizerZ n la * YoungSymmetrizerZ n la) := by
      rw [hc, YoungSymmetrizerK_eq_mapRange k n la, ← map_mul]
    have hval : (c * c) 1 = (((YoungSymmetrizerZ n la * YoungSymmetrizerZ n la) 1 : ℤ) : k) := by
      rw [hcc, MonoidAlgebra.mapRingHom_apply]; rfl
    have : (c * c) 1 = α := by
      rw [hα, Finsupp.smul_apply, smul_eq_mul, youngSymmetrizerK_apply_one k n la, mul_one]
    rw [← this, hval]
  have hsum : (∑ τ : Equiv.Perm (Fin n), c (τ⁻¹ * σ⁻¹ * τ))
      = ((∑ τ : Equiv.Perm (Fin n), (YoungSymmetrizerZ n la) (τ⁻¹ * σ⁻¹ * τ) : ℤ) : k) := by
    push_cast
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [hc, YoungSymmetrizerK_eq_mapRange k n la, MonoidAlgebra.mapRingHom_apply]
    rfl
  rw [hα_int, hsum]

/-- The Specht character is field-independent: it is the image under `algebraMap ℚ k` of the
ℚ-valued character. -/
lemma spechtModuleCharacterK_algebraMap_rat (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacterK k n la σ = algebraMap ℚ k (spechtModuleCharacterK ℚ n la σ) := by
  rw [spechtModuleCharacterK_eq_intCast k n la σ, spechtModuleCharacterK_eq_intCast ℚ n la σ,
    map_mul, map_inv₀, map_intCast, map_intCast]

/-- The ℂ specialisation of the general-`k` character recovers `spechtModuleCharacter`. -/
lemma spechtModuleCharacterK_complex (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacterK ℂ n la σ = spechtModuleCharacter n la σ := by
  have hys : YoungSymmetrizerK ℂ n la = YoungSymmetrizer n la := by
    rw [YoungSymmetrizerK_eq_mapRange ℂ n la, YoungSymmetrizer_eq_mapRange n la]
  have hmod : SpechtModuleK ℂ n la = SpechtModule n la := by
    unfold SpechtModuleK SpechtModule
    rw [hys]
  let e : ↥(SpechtModuleK ℂ n la) ≃ₗ[ℂ] ↥(SpechtModule n la) :=
    (LinearEquiv.ofEq _ _ hmod).restrictScalars ℂ
  have hint : spechtModuleAction n la σ = e.conj (spechtModuleActionK ℂ n la σ) := by
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply_apply]
    apply Subtype.ext
    rfl
  rw [spechtModuleCharacterK, spechtModuleCharacter, hint, LinearMap.trace_conj']

/-- **Specht character injectivity over a general characteristic-zero field.** Two Specht modules
whose `σ`-characters agree pointwise carry the same partition label. -/
theorem spechtModuleCharacterK_injective (n : ℕ) {μ ν : Nat.Partition n}
    (h : ∀ σ, spechtModuleCharacterK k n μ σ = spechtModuleCharacterK k n ν σ) : μ = ν := by
  apply spechtModuleCharacter_injective n
  intro σ
  have hq : spechtModuleCharacterK ℚ n μ σ = spechtModuleCharacterK ℚ n ν σ := by
    have hkσ := h σ
    rw [spechtModuleCharacterK_algebraMap_rat k n μ σ,
      spechtModuleCharacterK_algebraMap_rat k n ν σ] at hkσ
    exact (algebraMap ℚ k).injective hkσ
  rw [← spechtModuleCharacterK_complex n μ σ, ← spechtModuleCharacterK_complex n ν σ,
    spechtModuleCharacterK_algebraMap_rat ℂ n μ σ, spechtModuleCharacterK_algebraMap_rat ℂ n ν σ,
    hq]

end Etingof

end
