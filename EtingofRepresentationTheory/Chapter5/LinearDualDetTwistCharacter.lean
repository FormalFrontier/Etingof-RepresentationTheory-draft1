import EtingofRepresentationTheory.Chapter5.ContragredientIdentity
import EtingofRepresentationTheory.Chapter5.DualCharTwist
import EtingofRepresentationTheory.Chapter5.FormalCharacterDual
import EtingofRepresentationTheory.Chapter5.SchurPolyInverseShift
import EtingofRepresentationTheory.Chapter5.SchurWeylFormalCharacterIso

/-!
# Formal character of the `det^s`-twisted linear dual `L_λ^∨`

This file is the **analytic heart** of the linear-dual half of the contragredient
identity for `GL_n` (Etingof §5.22-5.23, issue #5553, parent #5544 / #5535): the
formal-character identity feeding the GL char→iso keystone
`iso_of_formalCharacter_eq_schurPoly` on the `det^s`-twisted linear dual.

The deliverable (issue #5553) is

```
formalCharacter k n
    (FDRep.of (charTwistRep (detChar k n ^ s) ((algIrrepGLRepρ n lam k).dual)))
  = schurPoly n (w0ShiftWeight n lam.toNatWeight (s + lam.shift))
```

for `s` large (`hs : ∀ i, lam.toNatWeight i ≤ s + lam.shift`).

## What this file proves (the reusable representation-theoretic infrastructure)

Writing `m := s + lam.shift`, `λ' := lam.toNatWeight`, `σ := schurModuleRep k n λ'`:

* `glWeightSpaceℤ_charTwist_shift` — the integer weight space of a character twist
  whose character has torus weight `sh` shifts by `-sh`:
  `glWeightSpaceℤ (charTwistRep c ρ) w = glWeightSpaceℤ ρ (w - sh)` when
  `c (diagUnit i t) = t ^ sh i`. This is the `ℤ`-level analogue of
  `glWeightSpace_detTwist_shift` (`Proposition5_22_2.lean`).

* `detChar_zpow_diagUnit` — the determinant character power reads `t ^ z` on the
  torus: `(detChar ^ z) (diagUnit i t) = t ^ z`.

* `detTwist_dual_algIrrepρ_eq` — collapsing the stacked twists on the
  contragredient: `charTwistRep (det^s) ((algIrrepGLRepρ).dual)
  = charTwistRep (det^{(m:ℤ)}) (Representation.dual σ)`, via `dual_charTwistRep`
  (#5552) + `charTwistRep_charTwistRep`.

* `coeff_formalCharacter_detTwist_dual` (**the coefficient formula**) — combining the
  three above with fact (a) `finrank_glWeightSpaceℤ_dual_eq`
  (`FormalCharacterDual.lean`, #5533):
  `(formalCharacter k n M).coeff μ = finrank (glWeightSpaceℤ σ (m·1 - μ))`.

This reduces the deliverable to a **pure-polynomial** statement: that
`finrank (glWeightSpaceℤ σ (m·1 - μ))` (which is `(schurPoly λ').coeff (m·1 - μ)`
for `m·1 - μ ≥ 0`, else `0`) assembles to `schurPoly n (w0ShiftWeight n λ' m)` via
the inverted-variable Schur identity fact (b) `schurPoly_inverseShift`
(`SchurPolyInverseShift.lean`, #5534). That coeff↔alternant bridge is the residual
work (tracked as a sub-issue).
-/

noncomputable section

namespace Etingof

open Etingof.KernelLemmaKPrime

/-! ## The integer weight space of a character twist -/

section TwistShift

variable {k : Type*} [Field k] {N : ℕ} {V : Type*} [AddCommGroup V] [Module k V]

/-- **The `ℤ`-level twist-shift lemma.** If the twisting character `c` has torus
weight `sh` (i.e. `c (diagUnit i t) = t ^ sh i`), then twisting `ρ` by `c` shifts
every integer weight space by `sh`:
`glWeightSpaceℤ (charTwistRep c ρ) w = glWeightSpaceℤ ρ (w - sh)`.

This mirrors `glWeightSpace_detTwist_shift` (`Proposition5_22_2.lean`) at the
`ℤ`-graded level needed for the negative dual weights. Each torus operator of the
twist factors as the invertible scalar `t ^ sh i` times the operator of `ρ` shifted
by `sh i`, and `ker` is invariant under nonzero scaling. -/
theorem glWeightSpaceℤ_charTwist_shift
    (c : Matrix.GeneralLinearGroup (Fin N) k →* kˣ)
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (sh : Fin N → ℤ)
    (hc : ∀ (i : Fin N) (t : kˣ), c (diagUnit k N i t) = t ^ sh i)
    (w : Fin N → ℤ) :
    glWeightSpaceℤ k N (charTwistRep c ρ) w
      = glWeightSpaceℤ k N ρ (fun i => w i - sh i) := by
  simp only [glWeightSpaceℤ]
  refine iInf_congr fun i => iInf_congr fun t => ?_
  have hCT : (charTwistRep c ρ) (diagUnit k N i t)
      = ((c (diagUnit k N i t) : kˣ) : k) • ρ (diagUnit k N i t) := rfl
  have hexp : sh i + (w i - sh i) = w i := by omega
  have hsc : (((t ^ sh i : kˣ) : k)) * (((t ^ (w i - sh i) : kˣ) : k))
      = ((t ^ w i : kˣ) : k) := by
    rw [← Units.val_mul, ← zpow_add, hexp]
  have factored : (charTwistRep c ρ) (diagUnit k N i t)
        - (((t ^ w i : kˣ) : k)) • LinearMap.id
      = ((t ^ sh i : kˣ) : k) •
          (ρ (diagUnit k N i t) - (((t ^ (w i - sh i) : kˣ) : k)) • LinearMap.id) := by
    rw [hCT, hc i t, smul_sub, smul_smul, hsc]
  rw [factored, LinearMap.ker_smul _ _ (Units.ne_zero (t ^ sh i))]

end TwistShift

/-! ## The determinant character power on the torus -/

/-- The `z`-th power of the determinant character reads `t ^ z` on the torus element
`diagUnit i t` (whose determinant is `t`). -/
theorem detChar_zpow_diagUnit (k : Type*) [Field k] (N : ℕ) (z : ℤ) (i : Fin N) (t : kˣ) :
    (detChar k N ^ z) (diagUnit k N i t) = t ^ z := by
  rw [MonoidHom.zpow_apply]
  congr 1
  -- `detChar (diagUnit i t) = t`: the determinant of the diagonal torus unit is `t`.
  apply Units.ext
  change Matrix.det (diagUnit k N i t).val = (t : k)
  simp only [diagUnit, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i),
    Pi.one_apply]
  simp [Finset.prod_eq_one (fun j _ => rfl)]

/-! ## Collapsing the stacked twists on the contragredient -/

/-- **The collapsed twisting character.** The character `det^s · (det^{-(lam.shift:ℤ)})⁻¹`
produced by dualizing then re-twisting `algIrrepGLRepρ = det^{-(lam.shift:ℤ)} ⊗ σ`
collapses to a single `det^{(s+lam.shift:ℤ)}`. -/
theorem detChar_pow_mul_inv_neg_zpow (n : ℕ) (lam : DominantWeight n) (k : Type*)
    [Field k] [IsAlgClosed k] (s : ℕ) :
    (detChar k n ^ s) * (detChar k n ^ (-(lam.shift : ℤ)))⁻¹
      = detChar k n ^ ((s + lam.shift : ℕ) : ℤ) := by
  rw [show (detChar k n ^ (-(lam.shift : ℤ)))⁻¹ = detChar k n ^ (lam.shift : ℤ) from by
        rw [zpow_neg, inv_inv],
    ← zpow_natCast (detChar k n) s, ← zpow_add, Nat.cast_add]

/-! ## The coefficient formula -/

/-- **The coefficient formula (reduction to pure polynomials).** Writing
`m := s + lam.shift`, `σ := schurModuleRep k n lam.toNatWeight`, the coefficient of
`x^μ` in the formal character of the `det^s`-twisted linear dual is the dimension of
`σ`'s integer weight space at the complemented weight `m·1 - μ`:

```
(formalCharacter k n (FDRep.of (charTwistRep (det^s) ((algIrrepGLRepρ).dual)))).coeff μ
  = finrank (glWeightSpaceℤ σ (fun i => (m:ℤ) - μ i)).
```

Proof chain: `formalCharacter_coeff` →
`glWeightSpace_eq_glWeightSpaceℤ` → `detTwist_dual_algIrrepρ_eq` (collapse) →
`glWeightSpaceℤ_charTwist_shift` (the `det^m` twist shifts the weight by `m`) →
`finrank_glWeightSpaceℤ_dual_eq` (the dual negates weights, #5533), using the weight
eigenbasis of the Schur module (`exists_weight_eigenbasis` +
`glWeightSpace_schurModule_iSup_eq_top`). -/
theorem coeff_formalCharacter_detTwist_dual (n : ℕ) (lam : DominantWeight n)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (s : ℕ) (μ : Fin n →₀ ℕ) :
    (formalCharacter k n
        (FDRep.of (charTwistRep (detChar k n ^ s)
          ((algIrrepGLRepρ n lam k).dual)))).coeff μ
      = (Module.finrank k (glWeightSpaceℤ k n (schurModuleRep k n lam.toNatWeight)
          (fun i => ((s + lam.shift : ℕ) : ℤ) - (μ i : ℤ))) : ℚ) := by
  -- Unfold `algIrrepGLRepρ = det^{-(lam.shift:ℤ)} ⊗ σ` so every carrier is `σ`'s
  -- (`AlgIrrepGL n lam k` is definitionally `↥(SchurModuleSubmodule k n λ')`).
  change (formalCharacter k n
      (FDRep.of (charTwistRep (detChar k n ^ s)
        (Representation.dual (charTwistRep (detChar k n ^ (-(lam.shift : ℤ)))
          (schurModuleRep k n lam.toNatWeight)))))).coeff μ = _
  -- A torus weight eigenbasis of the Schur module `L_{λ'}` (carrier of `σ`).
  obtain ⟨d, v, wt, hv⟩ := DetInvElim.exists_weight_eigenbasis
    (SchurModule k n lam.toNatWeight)
    (glWeightSpace_schurModule_iSup_eq_top k n lam.toNatWeight)
  -- Convert the eigenbasis equation to `schurModuleRep` and integer exponents.
  have hvℤ : ∀ (c : Fin d) (i : Fin n) (t : kˣ),
      (schurModuleRep k n lam.toNatWeight) (diagUnit k n i t) (v c)
        = ((t ^ (wt c i : ℤ) : kˣ) : k) • v c := by
    intro c i t
    rw [Units.val_zpow_eq_zpow_val, zpow_natCast]
    exact hv c i t
  rw [formalCharacter_coeff,
    glWeightSpace_eq_glWeightSpaceℤ k n _ (fun i => μ i),
    FDRep.of_ρ', dual_charTwistRep, charTwistRep_charTwistRep,
    detChar_pow_mul_inv_neg_zpow,
    glWeightSpaceℤ_charTwist_shift _ _ (fun _ => ((s + lam.shift : ℕ) : ℤ))
      (fun i t => detChar_zpow_diagUnit k n _ i t),
    finrank_glWeightSpaceℤ_dual_eq k n d (schurModuleRep k n lam.toNatWeight) v
      (fun c i => (wt c i : ℤ)) hvℤ (fun i => (μ i : ℤ) - ((s + lam.shift : ℕ) : ℤ))]
  -- Match the two weight functions: `-((μ i) - m) = m - μ i` (a `Fin n → ℤ` equality,
  -- so the weight-space type is unchanged and `rw` carries through `finrank`).
  rw [show (fun i => -((μ i : ℤ) - ((s + lam.shift : ℕ) : ℤ)))
        = (fun i : Fin n => ((s + lam.shift : ℕ) : ℤ) - (μ i : ℤ)) from by funext i; omega]

end Etingof
