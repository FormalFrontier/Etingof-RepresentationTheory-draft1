import Mathlib
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLRep
import EtingofRepresentationTheory.Chapter5.SchurModuleContragredientHalf
import EtingofRepresentationTheory.Chapter5.LinearDualContragredientHalf

/-!
# The contragredient identity `L*_λ ≅ L_λ^∨` for `GL_n`

Etingof §5.23 identifies, for `GL_n`, the contragredient `L*_λ` with `L_{-w₀λ}`.
The repo carries **two** concrete models of this contragredient:

* the **Schur-module realization** `AlgIrrepGLDual n lam k`
  (`= AlgIrrepGL n lam.w0Twist k`, `Theorem5_23_2Core.lean`) carrying
  `algIrrepGLRepDualρ n lam k` (`AlgIrrepGLRep.lean`);
* the **linear dual** `Module.Dual k (AlgIrrepGL n lam k)` carrying the
  contragredient representation `(algIrrepGLRepρ n lam k).dual`
  (`Representation.dual`, Mathlib).

These are two realizations of the same abstract simple, so they are isomorphic as
`GL_n`-representations. This file lands that isomorphism as
`algIrrepGLDual_iso_linearDual`, the input needed to retype the canonical
evaluation pairing `contractLeft` (`Chapter5/ContragredientPairing.lean`, #5515)
onto `AlgIrrepGLDual ⊗ AlgIrrepGL`.

## Proof architecture

The genuine obstruction is that the linear dual `L_λ^∨` has *negative* weights (its
character is `s_λ(x⁻¹)`), so it falls outside the polynomial `formalCharacter`
framework and the GL char→iso keystone `iso_of_formalCharacter_eq_schurPoly`
(`SchurWeylFormalCharacterIso.lean`) does not apply directly. The standard fix is a
`det^s`-twist: for `s` large both `L_λ^∨ ⊗ det^s` and `L_{w₀λ} ⊗ det^s` are
polynomial with Schur-polynomial character, so the keystone applies to each and
their isomorphism transfers.

The two pieces are factored cleanly:

* `isEquivariant_of_charTwist` (**proven here, no sorry**) — the *untwist* step.
  An equivariant linear equivalence between `charTwistRep c ρ₁` and
  `charTwistRep c ρ₂` is, after cancelling the invertible scalar `c g`, an
  equivariant equivalence between `ρ₁` and `ρ₂`. This is the reusable glue that
  removes the `det^s` twist once the twisted models are matched.
* `exists_detTwist_equivariantEquiv_dual` (**now sorry-free**, assembled from the two
  halves #5543/#5544) — for a large enough `det^s`-twist, the Schur-module
  contragredient and the linear dual are equivariantly isomorphic, via
  `iso_of_formalCharacter_eq_schurPoly` applied to both polynomial models. This is
  where the two analytic facts live: (a) `formalCharacter (ρ.dual)` evaluates `ρ`'s
  character at inverse weights; (b) the inverted-variable Schur identity
  `s_λ(x⁻¹)·(x₁⋯x_n)^s = s_{w₀λ+s}(x)`.
-/

noncomputable section

namespace Etingof

open Etingof.KernelLemmaKPrime
open scoped TensorProduct

/-! ## The untwist step (the reusable glue, sorry-free) -/

section Untwist

variable {k G W₁ W₂ : Type*} [Field k] [Monoid G]
  [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]

/-- **Cancelling a common character twist preserves equivariance.** A `k`-linear
equivalence `e : W₁ ≃ₗ[k] W₂` intertwining the `det`-style twists
`charTwistRep c ρ₁` and `charTwistRep c ρ₂` already intertwines the untwisted
representations `ρ₁` and `ρ₂`: each twist multiplies the action by the *same*
invertible scalar `c g`, and `e` is `k`-linear, so the scalar cancels.

This is the elementary "untwist" used to strip the `det^s`-twist after the two
polynomial models have been matched by `iso_of_formalCharacter_eq_schurPoly`. -/
theorem isEquivariant_of_charTwist (c : G →* kˣ)
    (ρ₁ : Representation k G W₁) (ρ₂ : Representation k G W₂)
    (e : W₁ ≃ₗ[k] W₂)
    (he : ∀ (g : G) (v : W₁),
      e (charTwistRep c ρ₁ g v) = charTwistRep c ρ₂ g (e v)) :
    ∀ (g : G) (v : W₁), e (ρ₁ g v) = ρ₂ g (e v) := by
  intro g v
  have h := he g v
  rw [charTwistRep_apply, charTwistRep_apply, map_smul] at h
  exact smul_right_injective W₂ (Units.ne_zero (c g)) h

end Untwist

/-! ## The contragredient identity -/

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

/-- **Both `det^s`-twisted contragredient models land on a common Schur module
(analytic core).** For a large enough determinant twist `det^s`, there is a single
non-negative weight `ν` such that *both* twisted models are `GL_n`-equivariantly
isomorphic to the bare Schur module `SchurModuleSubmodule k n ν` (action
`schurModuleRep k n ν`):

* the Schur-module contragredient `L_{w₀λ}` twisted by `det^s` (carrier
  `AlgIrrepGLDual n lam k`, action `charTwistRep (det^s) algIrrepGLRepDualρ`), and
* the linear dual `L_λ^∨` twisted by `det^s` (carrier
  `Module.Dual k (AlgIrrepGL n lam k)`, action `charTwistRep (det^s) (ρ.dual)`).

This bundles the entire analytic content of the contragredient identity. The
intended route applies the GL char→iso keystone `iso_of_formalCharacter_eq_schurPoly`
(`SchurWeylFormalCharacterIso.lean`) to each twisted model: both are polynomial
(algebraic, with spanning `ℕ`-weight spaces) with formal character `schurPoly N ν`,
so each is identified with the *same* Schur module `SchurModuleSubmodule k n ν`.

Two facts feed the character computation (each warrants its own sub-issue):

* (a) `formalCharacter (ρ.dual)` is `formalCharacter ρ` read at inverse torus weights
  (the dual rep negates weights);
* (b) the inverted-variable Schur identity `s_λ(x⁻¹)·(x₁⋯x_n)^s = s_{w₀λ+s}(x)`, which
  makes the `det^s`-twisted dual character a genuine Schur polynomial.

The `det^s`-twisted Schur-module side is the easier half: for `s ≥ (lam.w0Twist).shift`
it is the determinant-shift of a Schur module, identified with a Schur module by
iterating Proposition 5.22.2 (`schurModule_shift_iso_detTwist`). The hard half is the
linear-dual side, which needs (a) and (b).

Once this common model is available, the equivariant equivalence
`AlgIrrepGLDual ≃ₗ Module.Dual` is obtained by composing the two identifications
(`exists_detTwist_equivariantEquiv_dual`, sorry-free below).

**Status / decomposition (now sorry-free).** Facts (a) and (b) are closed:
(a) `formalCharacter_dual_coeff_eq` (`FormalCharacterDual.lean`, #5533) and
(b) `schurPoly_inverseShift` (`SchurPolyInverseShift.lean`, #5534). The reusable glue
`charTwistRep_charTwistRep` (`KernelLemmaKPrime.lean`, sorry-free) collapses the stacked
`det^s ∘ det^{-(shift:ℤ)}` twists into a single `det`-power twist. The two halves are:

* the Schur-module half `schurModule_half_detTwist_contragredient`
  (`SchurModuleContragredientHalf.lean`, keystone-free; iterate Prop 5.22.2) — issue #5543;
* the linear-dual half `linearDual_half_detTwist_contragredient`
  (`LinearDualContragredientHalf.lean`, keystone `iso_of_formalCharacter_eq_schurPoly`
  consuming (a)+(b)) — issue #5544.

**The shared-`ν` crux (resolved below).** The two halves must land on the *same* `ν`.
The Schur half (parameter `t`) yields `ν_Schur = (lam.w0Twist).toNatWeight + t`
(with `s = t + (lam.w0Twist).shift`), while the dual half (parameter `s`) yields
`ν_dual = w0ShiftWeight n lam.toNatWeight (s + lam.shift)`. Taking `t = 0` fixes
`s = (lam.w0Twist).shift` and `ν = (lam.w0Twist).toNatWeight`; the arithmetic identity
`hνeq : w0ShiftWeight n lam.toNatWeight ((lam.w0Twist).shift + lam.shift)
= (lam.w0Twist).toNatWeight` (each side `(lam.w0Twist).shift - lam_{rev j}` over `ℤ`,
the `lam.shift` columns cancelling) reconciles the dual half onto the shared `ν`.

Assembled from the two halves (#5543, #5544); the keystone forces `k : Type`. Tracked in
https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1/issues/5526. -/
theorem exists_common_schurModule_model_detTwist_dual (n : ℕ) (lam : DominantWeight n)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    ∃ (s : ℕ) (ν : Fin n → ℕ),
      Nonempty
        { e : AlgIrrepGLDual n lam k ≃ₗ[k] SchurModuleSubmodule k n ν //
          ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : AlgIrrepGLDual n lam k),
            e (charTwistRep (detChar k n ^ s) (algIrrepGLRepDualρ n lam k) g v)
              = schurModuleRep k n ν g (e v) }
      ∧ Nonempty
        { e : Module.Dual k (AlgIrrepGL n lam k) ≃ₗ[k] SchurModuleSubmodule k n ν //
          ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : Module.Dual k (AlgIrrepGL n lam k)),
            e (charTwistRep (detChar k n ^ s) ((algIrrepGLRepρ n lam k).dual) g v)
              = schurModuleRep k n ν g (e v) } := by
  -- The two halves are coupled through a shared weight `ν`. Take the Schur half's
  -- parameter `t = 0`, so the common twist is `s = (lam.w0Twist).shift` and the common
  -- weight is `ν = (lam.w0Twist).toNatWeight`. The Schur half lands there by construction;
  -- the dual half lands on `w0ShiftWeight n lam.toNatWeight (s + lam.shift)`, which the
  -- arithmetic below (`hνeq`) reconciles with `(lam.w0Twist).toNatWeight`.
  -- The torus shift normalizing a dominant weight is large enough: `λ_i + shift ≥ 0`.
  have hnonneg : ∀ (lz : DominantWeight n) (i : Fin n), 0 ≤ lz.val i + (lz.shift : ℤ) := by
    intro lz i
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
    have hlast : lz.val (Fin.last m) ≤ lz.val i := lz.property (Fin.le_last i)
    change 0 ≤ lz.val i + (((-(lz.val (Fin.last m))).toNat : ℕ) : ℤ)
    omega
  -- `λ.toNatWeight` recovers `λ`: `(λ.toNatWeight i : ℤ) = λ_i + shift`.
  have hcast : ∀ (lz : DominantWeight n) (i : Fin n),
      (lz.toNatWeight i : ℤ) = lz.val i + (lz.shift : ℤ) := by
    intro lz i
    change (((lz.val i + (lz.shift : ℤ)).toNat : ℕ) : ℤ) = lz.val i + (lz.shift : ℤ)
    rw [Int.toNat_of_nonneg (hnonneg lz i)]
  -- The bound feeding the dual half: `λ.toNatWeight i ≤ (lam.w0Twist).shift + lam.shift`.
  have hs : ∀ i, lam.toNatWeight i ≤ (lam.w0Twist).shift + lam.shift := by
    intro i
    have h1 : (lam.toNatWeight i : ℤ) = lam.val i + (lam.shift : ℤ) := hcast lam i
    have h2 : 0 ≤ (lam.w0Twist).val (Fin.rev i) + ((lam.w0Twist).shift : ℤ) :=
      hnonneg (lam.w0Twist) (Fin.rev i)
    have h3 : (lam.w0Twist).val (Fin.rev i) = -lam.val i := by
      change -lam.val (Fin.rev (Fin.rev i)) = -lam.val i
      rw [Fin.rev_rev]
    omega
  -- The shared-weight reconciliation: both halves land on `(lam.w0Twist).toNatWeight`.
  have hνeq : w0ShiftWeight n lam.toNatWeight ((lam.w0Twist).shift + lam.shift)
      = (lam.w0Twist).toNatWeight := by
    funext j
    have hA : (lam.toNatWeight (Fin.rev j) : ℤ) = lam.val (Fin.rev j) + (lam.shift : ℤ) :=
      hcast lam (Fin.rev j)
    have hB : ((lam.w0Twist).toNatWeight j : ℤ)
        = (lam.w0Twist).val j + ((lam.w0Twist).shift : ℤ) := hcast (lam.w0Twist) j
    have hw0 : (lam.w0Twist).val j = -lam.val (Fin.rev j) := rfl
    change ((lam.w0Twist).shift + lam.shift) - lam.toNatWeight (Fin.rev j)
      = (lam.w0Twist).toNatWeight j
    omega
  refine ⟨(lam.w0Twist).shift, (lam.w0Twist).toNatWeight, ?_, ?_⟩
  · -- Schur half with `t = 0`: twist power `0 + (lam.w0Twist).shift`, weight defeq to `ν`.
    rw [show (lam.w0Twist).shift = 0 + (lam.w0Twist).shift from (Nat.zero_add _).symm]
    exact schurModule_half_detTwist_contragredient n lam k 0
  · -- Dual half with `s = (lam.w0Twist).shift`; `hνeq` matches its weight to `ν`.
    rw [← hνeq]
    exact linearDual_half_detTwist_contragredient n lam k (lam.w0Twist).shift hs

/-- **The `det^s`-twisted models of the contragredient agree (character input).**
For a large enough determinant twist `det^s`, the Schur-module contragredient
`L_{w₀λ}` (carrier `AlgIrrepGLDual n lam k`, action `algIrrepGLRepDualρ`) and the
linear dual `L_λ^∨` (carrier `Module.Dual k (AlgIrrepGL n lam k)`, action
`(algIrrepGLRepρ n lam k).dual`) become `GL_n`-equivariantly isomorphic.

This is the analytic heart of the contragredient identity. Both twisted models are
polynomial with Schur-polynomial formal character, so each is identified with the
same Schur module by `iso_of_formalCharacter_eq_schurPoly`
(`SchurWeylFormalCharacterIso.lean`); composing the two identifications gives the
equivariant equivalence. Two facts feed the character computation:

* `formalCharacter (ρ.dual)` is `formalCharacter ρ` read at inverse torus weights
  (the dual rep negates weights);
* the inverted-variable Schur identity `s_λ(x⁻¹)·(x₁⋯x_n)^s = s_{w₀λ+s}(x)`, which
  makes the `det^s`-twisted dual character a genuine Schur polynomial.

Now sorry-free via `exists_common_schurModule_model_detTwist_dual`; tracked in
https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1/issues/5526. -/
theorem exists_detTwist_equivariantEquiv_dual (n : ℕ) (lam : DominantWeight n)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    ∃ s : ℕ, Nonempty
      { e : AlgIrrepGLDual n lam k ≃ₗ[k] Module.Dual k (AlgIrrepGL n lam k) //
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : AlgIrrepGLDual n lam k),
          e (charTwistRep (detChar k n ^ s) (algIrrepGLRepDualρ n lam k) g v)
            = charTwistRep (detChar k n ^ s) ((algIrrepGLRepρ n lam k).dual) g (e v) } := by
  -- Both twisted models land on the same bare Schur module `L_ν` (action
  -- `schurModuleRep k n ν`), via the analytic core. Compose the two identifications:
  -- `AlgIrrepGLDual --eA--> L_ν --eB.symm--> Module.Dual`.
  obtain ⟨s, ν, ⟨eA, heA⟩, ⟨eB, heB⟩⟩ :=
    exists_common_schurModule_model_detTwist_dual n lam k
  refine ⟨s, ⟨eA.trans eB.symm, ?_⟩⟩
  intro g v
  -- `eB` is injective, so it suffices to compare after applying `eB`.
  apply eB.injective
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, eB.apply_symm_apply,
    heA g v, heB g (eB.symm (eA v)), eB.apply_symm_apply]

/-- **The contragredient identity `L*_λ ≅ L_λ^∨` for `GL_n`.** A `GL_n`-equivariant
`k`-linear isomorphism identifying the Schur-module realization of the
contragredient `AlgIrrepGLDual n lam k` (`= L_{w₀λ}`, action
`algIrrepGLRepDualρ`) with the genuine linear dual `Module.Dual k (AlgIrrepGL n lam k)`
(action `(algIrrepGLRepρ n lam k).dual`).

The proof matches the two models after a common `det^s`-twist
(`exists_detTwist_equivariantEquiv_dual`) and cancels the twist with the
elementary `isEquivariant_of_charTwist`. With this in hand the canonical evaluation
pairing `contractLeft` (`Chapter5/ContragredientPairing.lean`) retypes onto
`AlgIrrepGLDual ⊗ AlgIrrepGL`. -/
theorem algIrrepGLDual_iso_linearDual (n : ℕ) (lam : DominantWeight n) (k : Type)
    [Field k] [IsAlgClosed k] [CharZero k] :
    Nonempty
      { e : AlgIrrepGLDual n lam k ≃ₗ[k] Module.Dual k (AlgIrrepGL n lam k) //
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : AlgIrrepGLDual n lam k),
          e (algIrrepGLRepDualρ n lam k g v) = (algIrrepGLRepρ n lam k).dual g (e v) } := by
  obtain ⟨s, ⟨e, he⟩⟩ := exists_detTwist_equivariantEquiv_dual n lam k
  exact ⟨⟨e, isEquivariant_of_charTwist (detChar k n ^ s)
    (algIrrepGLRepDualρ n lam k) ((algIrrepGLRepρ n lam k).dual) e he⟩⟩

end Etingof
