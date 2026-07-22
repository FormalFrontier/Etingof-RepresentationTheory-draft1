import EtingofRepresentationTheory.Chapter5.LinearDualDetTwistCharacter
import EtingofRepresentationTheory.Chapter5.SchurModuleContragredientHalf
import EtingofRepresentationTheory.Chapter5.GLRepAlgebraic
import EtingofRepresentationTheory.Chapter5.DetInvElim

/-!
# The linear-dual half of the `det^s`-twisted contragredient identity

This file lands the **linear-dual half** of the analytic core
`exists_common_schurModule_model_detTwist_dual`
(`Chapter5/ContragredientIdentity.lean`, parent issue #5535): the hard, keystone-
consuming side identifying the `det^s`-twisted linear dual `L_λ^∨` with a bare Schur
module.

For `GL_n` with dominant weight `λ`, write `λ' := λ.toNatWeight`,
`σ := schurModuleRep k n λ'`, `m := s + λ.shift`. The linear dual carries the
contragredient representation `(algIrrepGLRepρ n λ k).dual` on
`Module.Dual k (AlgIrrepGL n λ k)`. Twisting by `det^s` and collapsing the stacked
twists (via `dual_charTwistRep`, `charTwistRep_charTwistRep`,
`detChar_pow_mul_inv_neg_zpow`) gives
`M.ρ = charTwistRep (det^m) (Representation.dual σ)`.

Under the largeness hypothesis `hs : ∀ i, λ' i ≤ m` every weight of `M` is `≥ 0`, so
`M` is polynomial: a torus weight eigenbasis is the dual basis `v.dualBasis` of a
weight eigenbasis `v` of `σ`, carrying weight `m·1 - wt c` (the dual negates weights,
the `det^m` twist shifts them up). The weight bound `wt c i ≤ m` comes from
`schurPoly_coeff_le` applied to the Schur polynomial. The spanning `ℕ`-weight spaces
let the GL char→iso keystone `iso_of_formalCharacter_eq_schurPoly`
(`SchurWeylFormalCharacterIso.lean`) apply: with formal character
`schurPoly n (w0ShiftWeight n λ' m)` (`formalCharacter_detTwist_linearDual_eq_schurPoly`,
issue #5553) and the matching `finrank`, `M` is identified with the bare Schur module
`L_ν`, `ν = w0ShiftWeight n λ' m`.

The keystone `iso_of_formalCharacter_eq_schurPoly` is fixed at universe `Type`
(= `Type 0`), so this file is stated at `Type 0` as well, mirroring
`SchurModuleContragredientHalf.lean`.

The main result is `linearDual_half_detTwist_contragredient`. It consumes the closed
prerequisites #5552 (dual & det-twist algebraicity, `GLRepAlgebraic`/`DualCharTwist`)
and #5553 (the det^s-twisted dual character, `LinearDualDetTwistCharacter`). The
keystone-free Schur-module half is issue #5543
(`schurModule_half_detTwist_contragredient`). The shared-`ν` reconciliation between
the two halves belongs to the #5535 assembler.
-/

noncomputable section

namespace Etingof

open Etingof.KernelLemmaKPrime

/-! ## Spanning from a weight eigenbasis -/

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

omit [CharZero k] in
/-- **A torus weight eigenbasis saturates the `ℕ`-weight spaces.** If a finite-
dimensional `GL_n`-representation `M` has a basis of torus weight eigenvectors with
`ℕ`-valued weights `wt`, then its `ℕ`-indexed weight spaces span everything: each
basis vector lies in the weight space at its (finitely-supported) weight. This is the
converse direction to `exists_weight_eigenbasis`, packaging the spanning hypothesis
needed by the GL char→iso keystone. -/
theorem iSup_glWeightSpace_eq_top_of_eigenbasis (n d : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin n) k))
    (b : Module.Basis (Fin d) k M) (wt : Fin d → Fin n → ℕ)
    (hb : ∀ (c : Fin d) (i : Fin n) (t : kˣ),
        M.ρ (diagUnit k n i t) (b c) = ((t : k) ^ wt c i) • b c) :
    ⨆ (μ : Fin n →₀ ℕ), glWeightSpace k n M (fun i => μ i) = ⊤ := by
  classical
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  set μc : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (wt c) with hμc
  have hμc_apply : ∀ i, μc i = wt c i := fun i => rfl
  have hmem : b c ∈ glWeightSpace k n M (fun i => μc i) := by
    simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero]
    intro i t
    rw [hb c i t, hμc_apply]
  exact SetLike.mem_coe.mpr (Submodule.mem_iSup_of_mem μc hmem)

/-! ## Algebraicity of a determinant-power twist -/

omit [IsAlgClosed k] [CharZero k] in
/-- **A `det^m`-power twist preserves algebraicity.** Twisting an algebraic
`GL_n`-representation by the `m`-th power of the determinant character (for `m : ℕ`)
keeps it algebraic, by iterating `IsAlgebraicRepresentation.detTwist`. -/
theorem isAlgebraic_charTwist_detChar_natPow {Y : Type} [AddCommGroup Y] [Module k Y]
    [Module.Finite k Y] (n m : ℕ)
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (h : Etingof.IsAlgebraicRepresentation n ρ) :
    Etingof.IsAlgebraicRepresentation n
      (charTwistRep (detChar k n ^ ((m : ℕ) : ℤ)) ρ) := by
  induction m with
  | zero =>
    have heq : charTwistRep (detChar k n ^ ((0 : ℕ) : ℤ)) ρ = ρ := by
      rw [Nat.cast_zero, zpow_zero, charTwistRep_one]
    rw [heq]; exact h
  | succ m ih =>
    have hfun : (charTwistRep (detChar k n ^ (((m + 1 : ℕ)) : ℤ)) ρ :
          Matrix.GeneralLinearGroup (Fin n) k → Y →ₗ[k] Y)
        = fun g => ((detChar k n) g : k)
            • (charTwistRep (detChar k n ^ ((m : ℕ) : ℤ)) ρ) g := by
      funext g
      ext v
      simp only [charTwistRep_apply, LinearMap.smul_apply]
      rw [show (((m + 1 : ℕ)) : ℤ) = ((m : ℕ) : ℤ) + 1 by push_cast; ring,
        zpow_add_one, MonoidHom.mul_apply, Units.val_mul, mul_comm, mul_smul]
    rw [hfun]
    exact ih.detTwist

/-! ## The linear-dual half -/

/-- **The linear-dual half of the contragredient identity.** With `λ' := λ.toNatWeight`
and `m := s + λ.shift`, under the largeness hypothesis `hs : ∀ i, λ' i ≤ m`, the
`det^s`-twist of the linear-dual contragredient `(algIrrepGLRepρ n λ k).dual` is
`GL_n`-equivariantly isomorphic to the bare Schur module `L_ν` with
`ν = w0ShiftWeight n λ' m` (action `schurModuleRep k n ν`).

This is the keystone-consuming half feeding
`exists_common_schurModule_model_detTwist_dual` (parent issue #5535). The proof applies
the GL char→iso keystone `iso_of_formalCharacter_eq_schurPoly` to
`M := FDRep.of (charTwistRep (det^s) ((algIrrepGLRepρ n λ k).dual))`: it is algebraic
(prereq #5552), its `ℕ`-weight spaces span (a `det^m`-shifted dual weight eigenbasis,
nonnegative by `hs`), and its formal character is `schurPoly n ν`
(`formalCharacter_detTwist_linearDual_eq_schurPoly`, prereq #5553). The keystone-free
Schur-module half is `schurModule_half_detTwist_contragredient` (issue #5543). -/
theorem linearDual_half_detTwist_contragredient (n : ℕ) (lam : DominantWeight n)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (s : ℕ)
    (hs : ∀ i, lam.toNatWeight i ≤ s + lam.shift) :
    Nonempty
      { e : Module.Dual k (AlgIrrepGL n lam k) ≃ₗ[k]
            SchurModuleSubmodule k n (w0ShiftWeight n lam.toNatWeight (s + lam.shift)) //
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : Module.Dual k (AlgIrrepGL n lam k)),
          e (charTwistRep (detChar k n ^ s) ((algIrrepGLRepρ n lam k).dual) g v)
            = schurModuleRep k n (w0ShiftWeight n lam.toNatWeight (s + lam.shift)) g (e v) } := by
  classical
  set lz := lam.toNatWeight with hlz_def
  have hlz : Antitone lz := lam.toNatWeight_antitone
  set m : ℕ := s + lam.shift with hm_def
  set ν : Fin n → ℕ := w0ShiftWeight n lz m with hν_def
  have hν : Antitone ν := w0ShiftWeight_antitone n lz hlz m
  -- The det^s-twisted linear dual, as an `FDRep`.
  set M : FDRep k (Matrix.GeneralLinearGroup (Fin n) k) :=
    FDRep.of (charTwistRep (detChar k n ^ s) ((algIrrepGLRepρ n lam k).dual)) with hM_def
  -- A torus weight eigenbasis of the Schur module `L_{λ'}` (carrier of `σ`).
  obtain ⟨d, v, wt, hv⟩ := DetInvElim.exists_weight_eigenbasis
    (SchurModule k n lz) (glWeightSpace_schurModule_iSup_eq_top k n lz)
  -- The eigenbasis equation in integer-exponent form, kept on the *FDRep* instances of
  -- `(SchurModule k n lz)` (matching `v`) to avoid the native/`ModuleCat` carrier diamond.
  have hvℤ : ∀ (c : Fin d) (i : Fin n) (t : kˣ),
      ((SchurModule k n lz).ρ) (diagUnit k n i t) (v c)
        = ((t ^ (wt c i : ℤ) : kˣ) : k) • v c := by
    intro c i t
    rw [Units.val_zpow_eq_zpow_val, zpow_natCast]
    exact hv c i t
  -- The eigenbasis weights are bounded by `m` (no negative weights after the twist).
  have hbound : ∀ (c : Fin d) (i : Fin n), wt c i ≤ m := by
    intro c i
    set μc : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (wt c) with hμc
    have hμc_apply : ∀ j, μc j = wt c j := fun j => rfl
    have hmem : v c ∈ glWeightSpace k n (SchurModule k n lz) (fun j => μc j) := by
      simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero]
      intro j t
      rw [hv c j t, hμc_apply]
    have hne : glWeightSpace k n (SchurModule k n lz) (fun j => μc j) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hmem
      exact v.ne_zero c (by rwa [Submodule.mem_bot] at hmem)
    have hfr : 0 < Module.finrank k
        (glWeightSpace k n (SchurModule k n lz) (fun j => μc j)) :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne)
    have hcoeff : (schurPoly n lz).coeff μc ≠ 0 := by
      rw [← schurModule_weight_eq_schurPoly_coeff k n lz hlz μc]
      exact_mod_cast hfr.ne'
    have hle := schurPoly_coeff_le n lz m hs hcoeff i
    rwa [hμc_apply] at hle
  -- The dual basis `v.dualBasis` is a weight eigenbasis of `M`, weight `m·1 - wt c`.
  have hMeigen : ∀ (c : Fin d) (i : Fin n) (t : kˣ),
      M.ρ (diagUnit k n i t) (v.dualBasis c)
        = ((t : k) ^ (m - wt c i)) • v.dualBasis c := by
    intro c i t
    -- Unfold `M.ρ` to the concrete nested twist phrased through `(SchurModule k n lz).ρ`
    -- (defeq to `schurModuleRep`, but carrying the *same FDRep instances as `v`*), via
    -- `show` not `rw`, reconciling the carrier-alias instance paths by defeq (skill #5553).
    -- Then ordinary same-carrier rewrites collapse the twists.
    change (charTwistRep (detChar k n ^ s)
        (Representation.dual (charTwistRep (detChar k n ^ (-(lam.shift : ℤ)))
          ((SchurModule k n lz).ρ)))) (diagUnit k n i t) (v.dualBasis c)
      = ((t : k) ^ (m - wt c i)) • v.dualBasis c
    rw [dual_charTwistRep, charTwistRep_charTwistRep, detChar_pow_mul_inv_neg_zpow,
      charTwistRep_apply, detChar_zpow_diagUnit k n _ i t,
      dual_diagUnit_dualBasis k n d ((SchurModule k n lz).ρ) v (fun c i => (wt c i : ℤ)) hvℤ c i t,
      smul_smul, ← Units.val_mul, ← zpow_add]
    congr 1
    rw [show ((m : ℕ) : ℤ) + -(wt c i : ℤ) = (((m - wt c i : ℕ)) : ℤ) by
          have := hbound c i; omega,
      Units.val_zpow_eq_zpow_val, zpow_natCast]
  -- Spanning: the dual basis is an `ℕ`-weight eigenbasis.
  have h_span : ⨆ (μ : Fin n →₀ ℕ), glWeightSpace k n M (fun i => μ i) = ⊤ :=
    iSup_glWeightSpace_eq_top_of_eigenbasis n d M v.dualBasis
      (fun c i => m - wt c i) hMeigen
  -- Algebraicity of `M.ρ = charTwistRep (det^m) (dual σ)`.
  have hσalg : Etingof.IsAlgebraicRepresentation n (schurModuleRep k n lz) :=
    schurModule_isAlgebraic (k := k) n lz
  have halg : Etingof.IsAlgebraicRepresentation n M.ρ := by
    -- Unfold `M.ρ` to the native nested twist (`show`), collapse it, then iterate the
    -- determinant-power twist closure on the algebraic dual of the Schur module.
    change Etingof.IsAlgebraicRepresentation n
      (charTwistRep (detChar k n ^ s)
        (Representation.dual (charTwistRep (detChar k n ^ (-(lam.shift : ℤ)))
          (schurModuleRep k n lz))))
    rw [dual_charTwistRep, charTwistRep_charTwistRep, detChar_pow_mul_inv_neg_zpow]
    exact isAlgebraic_charTwist_detChar_natPow n m _
      (IsAlgebraicRepresentation.dual (schurModuleRep k n lz) hσalg)
  -- Formal character of `M` is `schurPoly n ν` (prereq #5553).
  have h_char : formalCharacter k n M = schurPoly n ν := by
    rw [hM_def]
    exact formalCharacter_detTwist_linearDual_eq_schurPoly n lam k s hs
  -- Dimension match against the bare Schur module `L_ν`.
  have h_dim : Module.finrank k M = Module.finrank k (SchurModule k n ν) := by
    have h₂_top : ⨆ (μ : Fin n →₀ ℕ),
        glWeightSpace k n (SchurModule k n ν) (fun i => μ i) = ⊤ :=
      glWeightSpace_schurModule_iSup_eq_top k n ν
    have h_char_eq : formalCharacter k n M = formalCharacter k n (SchurModule k n ν) :=
      h_char.trans (Theorem5_22_1 k n ν hν).symm
    exact finrank_eq_of_formalCharacter_eq k n M (SchurModule k n ν) h_span h₂_top h_char_eq
  -- Apply the GL char→iso keystone.
  obtain ⟨iso⟩ := iso_of_formalCharacter_eq_schurPoly k n ν hν M halg h_span h_char h_dim
  -- Convert the FDRep iso into the bundled intertwining linear equivalence.
  exact ⟨FDRep.isoToLinearEquiv iso,
    intertwines_of_fdRepIso (charTwistRep (detChar k n ^ s) ((algIrrepGLRepρ n lam k).dual))
      (schurModuleRep k n ν) iso⟩

end Etingof
