import EtingofRepresentationTheory.Chapter5.ContragredientIdentity
import EtingofRepresentationTheory.Chapter5.Proposition5_22_2

/-!
# The Schur-module half of the `det^s`-twisted contragredient identity

This file lands the **Schur-module half** of the analytic core
`exists_common_schurModule_model_detTwist_dual`
(`Chapter5/ContragredientIdentity.lean`, issue #5535): the easier, keystone-free
side identifying the `det^s`-twisted Schur-module contragredient with a bare Schur
module.

For `GL_n` with dominant weight `λ`, write `w₀ := λ.w0Twist`, `μ := w₀.toNatWeight`,
`sh := w₀.shift`. The contragredient `L*_λ = AlgIrrepGLDual n λ k` carries the
representation `algIrrepGLRepDualρ`, which is the bare Schur module `L_μ`
(action `schurModuleRep k n μ`) twisted by `det^{-(sh:ℤ)}`. Twisting once more by
`det^s` with `s = t + sh` collapses the stacked twists (via `charTwistRep_charTwistRep`)
to a single `det^t`-twist of `L_μ`. Iterating Proposition 5.22.2
(`schurModule_shift_iso_detTwist`) `t` times then identifies `det^t ⊗ L_μ` with the
bare Schur module `L_ν`, `ν = μ + t·1`.

The keystone `iso_of_formalCharacter_eq_schurPoly` (and hence
`schurModule_shift_iso_detTwist`) is fixed at universe `Type` (= `Type 0`), so this
file is stated at `Type 0` as well.

The main result is `schurModule_half_detTwist_contragredient`. The hard half (the
linear dual, consuming the GL char→iso keystone) is issue #5544.
-/

noncomputable section

namespace Etingof

open Etingof.KernelLemmaKPrime

/-! ## Equivariant linear equivalences and their elementary combinators

A small bundle of operations on `k`-linear equivalences that intertwine two
representations. These are pure linear-algebra glue, used to chain the per-step
identifications produced by `schurModule_shift_iso_detTwist`. -/

section Helpers

universe u

variable {k : Type u} [Field k] {G : Type u} [Monoid G]
  {V₁ V₂ V₃ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₃] [Module k V₃]

/-- `e : V₁ ≃ₗ[k] V₂` **intertwines** the representations `ρ₁` and `ρ₂`. -/
@[reducible] def Intertwines (ρ₁ : Representation k G V₁) (ρ₂ : Representation k G V₂)
    (e : V₁ ≃ₗ[k] V₂) : Prop :=
  ∀ (g : G) (v : V₁), e (ρ₁ g v) = ρ₂ g (e v)

theorem Intertwines.trans {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
    {ρ₃ : Representation k G V₃} {e : V₁ ≃ₗ[k] V₂} {f : V₂ ≃ₗ[k] V₃}
    (he : Intertwines ρ₁ ρ₂ e) (hf : Intertwines ρ₂ ρ₃ f) :
    Intertwines ρ₁ ρ₃ (e.trans f) := by
  intro g v
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he g v, hf g (e v)]

theorem Intertwines.symm {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
    {e : V₁ ≃ₗ[k] V₂} (he : Intertwines ρ₁ ρ₂ e) :
    Intertwines ρ₂ ρ₁ e.symm := by
  intro g w
  apply e.injective
  rw [e.apply_symm_apply, he g (e.symm w), e.apply_symm_apply]

/-- A character twist preserves intertwining: each side is scaled by the same
invertible scalar `c g`, and `e` is `k`-linear, so the scalar passes through. -/
theorem Intertwines.charTwist (c : G →* kˣ) {ρ₁ : Representation k G V₁}
    {ρ₂ : Representation k G V₂} {e : V₁ ≃ₗ[k] V₂} (he : Intertwines ρ₁ ρ₂ e) :
    Intertwines (charTwistRep c ρ₁) (charTwistRep c ρ₂) e := by
  intro g v
  simp only [charTwistRep_apply, map_smul, he g v]

/-- An `FDRep` isomorphism `FDRep.of ρ₁ ≅ FDRep.of ρ₂` yields an intertwining linear
equivalence, namely the underlying `FDRep.isoToLinearEquiv`. -/
theorem intertwines_of_fdRepIso [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    (ρ₁ : Representation k G V₁) (ρ₂ : Representation k G V₂)
    (f : FDRep.of ρ₁ ≅ FDRep.of ρ₂) :
    Intertwines ρ₁ ρ₂ (FDRep.isoToLinearEquiv f) := by
  intro g v
  have h := FDRep.Iso.conj_ρ f g
  change (FDRep.isoToLinearEquiv f) ((FDRep.of ρ₁).ρ g v)
    = (FDRep.of ρ₂).ρ g ((FDRep.isoToLinearEquiv f) v)
  have hconj : (FDRep.isoToLinearEquiv f).conj ((FDRep.of ρ₁).ρ g)
        ((FDRep.isoToLinearEquiv f) v)
      = (FDRep.isoToLinearEquiv f) ((FDRep.of ρ₁).ρ g v) := by
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    change (FDRep.isoToLinearEquiv f)
        (((FDRep.of ρ₁).ρ g) ((FDRep.isoToLinearEquiv f).symm ((FDRep.isoToLinearEquiv f) v)))
      = (FDRep.isoToLinearEquiv f) (((FDRep.of ρ₁).ρ g) v)
    rw [(FDRep.isoToLinearEquiv f).symm_apply_apply]
  rw [h, hconj]

/-- `charTwistRep 1 ρ = ρ`: the trivial character twist is the identity. -/
theorem charTwistRep_one (ρ : Representation k G V₁) :
    charTwistRep (1 : G →* kˣ) ρ = ρ := by
  ext g v
  simp only [charTwistRep_apply, MonoidHom.one_apply, Units.val_one, one_smul]

end Helpers

/-! ## Iterating the determinant shift -/

/-- **Iterating Proposition 5.22.2.** For an antitone weight `μ` and `t : ℕ`, the
`det^t`-twist of the Schur module `L_μ` is `GL_n`-equivariantly isomorphic to the
bare Schur module `L_{μ + t·1}`. Proved by induction on `t`: the base case is the
trivial twist `charTwistRep 1`, and each step composes the induction hypothesis
(twisted once more by `det`) with the determinant-shift isomorphism
`schurModule_shift_iso_detTwist`. -/
theorem charTwist_detPow_iso_schurShift (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (μ : Fin n → ℕ) (hμ : Antitone μ) (t : ℕ) :
    Nonempty
      { e : SchurModuleSubmodule k n μ ≃ₗ[k] SchurModuleSubmodule k n (fun i => μ i + t) //
        Intertwines (charTwistRep (detChar k n ^ t) (schurModuleRep k n μ))
          (schurModuleRep k n (fun i => μ i + t)) e } := by
  induction t with
  | zero =>
    refine ⟨⟨LinearEquiv.refl k _, ?_⟩⟩
    intro g v
    change (charTwistRep (detChar k n ^ 0) (schurModuleRep k n μ) g v)
      = schurModuleRep k n μ g v
    rw [pow_zero, charTwistRep_one]
  | succ t ih =>
    obtain ⟨e, he⟩ := ih
    have hμt : Antitone (fun i => μ i + t) := fun i j hij => Nat.add_le_add_right (hμ hij) t
    obtain ⟨iso⟩ := schurModule_shift_iso_detTwist k n (fun i => μ i + t) hμt
    -- The shift iso, read as an intertwiner between `L_{μ+(t+1)}` and `det ⊗ L_{μ+t}`.
    have hshift : Intertwines (schurModuleRep k n (fun i => μ i + (t + 1)))
        (charTwistRep (detChar k n) (schurModuleRep k n (fun i => μ i + t)))
        (FDRep.isoToLinearEquiv iso) := intertwines_of_fdRepIso _ _ iso
    -- The induction hypothesis, twisted once more by `det`.
    have he_tw : Intertwines
        (charTwistRep (detChar k n) (charTwistRep (detChar k n ^ t) (schurModuleRep k n μ)))
        (charTwistRep (detChar k n) (schurModuleRep k n (fun i => μ i + t))) e :=
      Intertwines.charTwist (detChar k n) he
    have hcomp := Intertwines.trans he_tw (Intertwines.symm hshift)
    have hsrc : charTwistRep (detChar k n) (charTwistRep (detChar k n ^ t) (schurModuleRep k n μ))
        = charTwistRep (detChar k n ^ (t + 1)) (schurModuleRep k n μ) := by
      rw [charTwistRep_charTwistRep, ← pow_succ']
    rw [hsrc] at hcomp
    exact ⟨⟨e.trans (FDRep.isoToLinearEquiv iso).symm, hcomp⟩⟩

/-! ## The Schur-module half -/

/-- **The Schur-module half of the contragredient identity.** With `w₀ := λ.w0Twist`,
`μ := w₀.toNatWeight`, `sh := w₀.shift`, for every `t : ℕ` the `det^{t+sh}`-twist of
the Schur-module contragredient `algIrrepGLRepDualρ` is `GL_n`-equivariantly
isomorphic to the bare Schur module `L_ν` with `ν = μ + t·1` (action
`schurModuleRep k n ν`).

The contragredient is `algIrrepGLRepDualρ = det^{-(sh:ℤ)} ⊗ L_μ`; twisting by
`det^{t+sh}` collapses (via `charTwistRep_charTwistRep` and
`det^{t+sh} · det^{-(sh:ℤ)} = det^t`) to the `det^t`-twist of `L_μ`, which
`charTwist_detPow_iso_schurShift` identifies with `L_ν`. This is the keystone-free
half feeding `exists_common_schurModule_model_detTwist_dual` (issue #5535); the
linear-dual half is issue #5544. -/
theorem schurModule_half_detTwist_contragredient (n : ℕ) (lam : DominantWeight n)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : ℕ) :
    Nonempty
      { e : AlgIrrepGLDual n lam k ≃ₗ[k]
            SchurModuleSubmodule k n (fun i => (lam.w0Twist).toNatWeight i + t) //
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : AlgIrrepGLDual n lam k),
          e (charTwistRep (detChar k n ^ (t + (lam.w0Twist).shift))
                (algIrrepGLRepDualρ n lam k) g v)
            = schurModuleRep k n (fun i => (lam.w0Twist).toNatWeight i + t) g (e v) } := by
  obtain ⟨e, he⟩ := charTwist_detPow_iso_schurShift k n (lam.w0Twist).toNatWeight
    (lam.w0Twist).toNatWeight_antitone t
  -- Collapse the stacked twists: `det^{t+sh} · det^{-(sh:ℤ)} = det^t`.
  have hchar : detChar k n ^ (t + (lam.w0Twist).shift)
        * detChar k n ^ (-((lam.w0Twist).shift : ℤ)) = detChar k n ^ t := by
    rw [← zpow_natCast (detChar k n) (t + (lam.w0Twist).shift), ← zpow_add,
        ← zpow_natCast (detChar k n) t]
    congr 1
    push_cast
    ring
  -- Hence the `det^{t+sh}`-twisted contragredient is the `det^t`-twist of `L_μ`.
  have hrep : charTwistRep (detChar k n ^ (t + (lam.w0Twist).shift)) (algIrrepGLRepDualρ n lam k)
      = charTwistRep (detChar k n ^ t) (schurModuleRep k n (lam.w0Twist).toNatWeight) := by
    change charTwistRep (detChar k n ^ (t + (lam.w0Twist).shift))
        (charTwistRep (detChar k n ^ (-((lam.w0Twist).shift : ℤ)))
          (schurModuleRep k n (lam.w0Twist).toNatWeight)) = _
    rw [charTwistRep_charTwistRep, hchar]
  refine ⟨e, ?_⟩
  intro g v
  rw [hrep]
  exact he g v

end Etingof
