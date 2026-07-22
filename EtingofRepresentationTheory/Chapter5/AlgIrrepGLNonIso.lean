import Mathlib
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLRep
import EtingofRepresentationTheory.Chapter5.Proposition5_22_2
import EtingofRepresentationTheory.Chapter5.FormalCharacterIso
import EtingofRepresentationTheory.Chapter5.RepresentationAsModuleHom
import EtingofRepresentationTheory.Chapter5.LinearDualDetTwistCharacter
import EtingofRepresentationTheory.Chapter5.SchurPolyShift
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Pairwise non-isomorphism of the irreducibles `L_λ` for distinct dominant weights

For distinct dominant weights `λ ≠ μ`, the irreducible algebraic representations
`L_λ = algIrrepGLRepρ n λ k` and `L_μ` are non-isomorphic as `k[GL_n]`-modules. This
is the distinguishing-invariant input (the highest-weight / formal-character
classification) to the cross-summand orthogonality
`peterWeylSummandMap_range_iSupIndep` (issue #5556).

## Proof route (`algIrrepGLRepρ_noniso`)

A `k[GL_n]`-module isomorphism `e : L_λ.asModule ≃ₗ L_μ.asModule` restricts to a
`GL_n`-equivariant `k`-linear equivalence `f : AlgIrrepGL n λ k ≃ₗ[k] AlgIrrepGL n μ k`
(via `Representation.asModuleEquiv` and `Representation.asModuleEquiv_symm_map_rho`,
the reverse of `asModuleEquivOfIntertwiner` in `RepresentationAsModuleHom.lean`).

The same `f` intertwines the `det^M`-twists for any `M`, since
`charTwistRep c ρ g = c g • ρ g`. Choose `M = λ.shift + μ.shift` (so `M ≥ λ.shift, μ.shift`).
Using `charTwistRep_charTwistRep` (`ContragredientIdentity.lean`) and
`detChar^M * detChar^{-λ.shift} = detChar^{M - λ.shift}`,

  `charTwistRep (detChar^M) L_λ = charTwistRep (detChar^{M-λ.shift}) (schurModuleRep a)`

(where `a = λ.toNatWeight`), an honest *polynomial* Schur-module twist, whose formal
character is `schurPoly (a + (M - λ.shift)·1) = schurPoly (fun i => a i + μ.shift)`
(`M - λ.shift = μ.shift`), computed by `formalCharacter_charTwist_detChar_pow` below.

`formalCharacter_eq_of_rep_iso` applied to `f` (twisted) thus gives
`schurPoly (fun i => λ.toNatWeight i + μ.shift) = schurPoly (fun i => μ.toNatWeight i + λ.shift)`
(both antitone, non-negative). `schurPoly_injective` and the recovery
`(λ.toNatWeight i : ℤ) = λ.val i + λ.shift` then force `λ.val = μ.val`, i.e. `λ = μ`.

The genuine new ingredient is the `p`-fold determinant-twist character formula
`formalCharacter_charTwist_detChar_pow` below
(`formalCharacter (charTwistRep (detChar^p) (schurModuleRep w)) = schurPoly (w + p·1)`,
`p : ℕ`), proved by induction on `p` from `formalCharacter_shift_of_weightSpace_finrank`
(one `∏ Xᵢ` factor per twist) and `schurPoly_shift`, with the per-step weight-space
bookkeeping done at the integer-graded level (`glWeightSpaceℤ_charTwist_shift`,
`finrank_glWeightSpaceℤ_schurModule_neg`).
-/

open scoped TensorProduct

noncomputable section

namespace Etingof

open Etingof.KernelLemmaKPrime

/-- Equal submodules have equal finrank (as a `congrArg`, avoiding dependent
`rw` under `Module.finrank`). -/
private theorem finrank_submodule_congr' {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {S T : Submodule K W} (h : S = T) : Module.finrank K S = Module.finrank K T :=
  congrArg (fun U : Submodule K W => Module.finrank K U) h

/-- **`p`-fold determinant-twist character formula.** Twisting the Schur module
`L_w` by `det^p` (`p : ℕ`) shifts the highest weight up by `p` in every coordinate:
its formal character is `schurPoly (w + p·1)`. Proved by induction on `p` from
`formalCharacter_shift_of_weightSpace_finrank` (one `∏ Xᵢ` factor per twist) and
`schurPoly_shift`; the weight-space bookkeeping at each step is done at the integer-
graded level (`glWeightSpaceℤ_charTwist_shift`, `finrank_glWeightSpaceℤ_schurModule_neg`). -/
theorem formalCharacter_charTwist_detChar_pow (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (n : ℕ) (w : Fin n → ℕ) (hw : Antitone w) (p : ℕ) :
    formalCharacter k n
        (FDRep.of (charTwistRep (detChar k n ^ (p : ℤ)) (schurModuleRep k n w)))
      = schurPoly n (fun i => w i + p) := by
  induction p with
  | zero =>
    have hct : charTwistRep (detChar k n ^ (0 : ℤ)) (schurModuleRep k n w)
        = schurModuleRep k n w := by
      ext g v; simp [charTwistRep_apply]
    rw [Nat.cast_zero, hct]
    have hw0 : (fun i => w i + 0) = w := by funext i; omega
    rw [hw0]
    exact formalCharacter_schurModule_eq_schurPoly k n w hw
  | succ p ih =>
    have hshift : ∀ ν : Fin n → ℕ,
        Module.finrank k (glWeightSpace k n
            (FDRep.of (charTwistRep (detChar k n ^ ((p + 1 : ℕ) : ℤ)) (schurModuleRep k n w)))
            (fun i => ν i + 1))
          = Module.finrank k (glWeightSpace k n
            (FDRep.of (charTwistRep (detChar k n ^ ((p : ℕ) : ℤ)) (schurModuleRep k n w))) ν) := by
      intro ν
      refine finrank_submodule_congr' ?_
      rw [glWeightSpace_eq_glWeightSpaceℤ k n _ (fun i => ν i + 1),
          glWeightSpace_eq_glWeightSpaceℤ k n _ ν]
      simp only [FDRep.of_ρ']
      rw [glWeightSpaceℤ_charTwist_shift (detChar k n ^ ((p + 1 : ℕ) : ℤ))
            (schurModuleRep k n w) (fun _ => ((p + 1 : ℕ) : ℤ))
            (fun i t => detChar_zpow_diagUnit k n _ i t) (fun i => ((ν i + 1 : ℕ) : ℤ)),
          glWeightSpaceℤ_charTwist_shift (detChar k n ^ ((p : ℕ) : ℤ))
            (schurModuleRep k n w) (fun _ => ((p : ℕ) : ℤ))
            (fun i t => detChar_zpow_diagUnit k n _ i t) (fun i => ((ν i : ℕ) : ℤ))]
      have hAB : (fun i => ((ν i + 1 : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ))
          = (fun i => ((ν i : ℕ) : ℤ) - ((p : ℕ) : ℤ)) := by
        funext i; push_cast; ring
      simp only [hAB]
    have hvanish : ∀ μ : Fin n → ℕ, (∃ i, μ i = 0) →
        Module.finrank k (glWeightSpace k n
          (FDRep.of (charTwistRep (detChar k n ^ ((p + 1 : ℕ) : ℤ)) (schurModuleRep k n w)))
          μ) = 0 := by
      rintro μ ⟨i₀, hi₀⟩
      have hsub : glWeightSpace k n
            (FDRep.of (charTwistRep (detChar k n ^ ((p + 1 : ℕ) : ℤ)) (schurModuleRep k n w))) μ
          = glWeightSpaceℤ k n (schurModuleRep k n w)
              (fun i => ((μ i : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ)) := by
        rw [glWeightSpace_eq_glWeightSpaceℤ k n _ μ]
        simp only [FDRep.of_ρ']
        rw [glWeightSpaceℤ_charTwist_shift (detChar k n ^ ((p + 1 : ℕ) : ℤ))
              (schurModuleRep k n w) (fun _ => ((p + 1 : ℕ) : ℤ))
              (fun i t => detChar_zpow_diagUnit k n _ i t) (fun i => ((μ i : ℕ) : ℤ))]
      rw [finrank_submodule_congr' hsub]
      refine finrank_glWeightSpaceℤ_schurModule_neg k n w
        (fun i => ((μ i : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ)) i₀ ?_
      rw [hi₀]; push_cast; omega
    have hidx : (fun i => w i + (p + 1)) = (fun i => (w i + p) + 1) := by funext i; omega
    have hsp : schurPoly n (fun i => w i + (p + 1))
        = (∏ i : Fin n, MvPolynomial.X i) * schurPoly n (fun i => w i + p) := by
      rw [hidx, schurPoly_shift]
    rw [formalCharacter_shift_of_weightSpace_finrank k n _ _ hshift hvanish, ih, hsp]

/-- The torus-shift normalizing a dominant weight is large enough: `λ_i + shift ≥ 0`. -/
private theorem dominantWeight_shift_nonneg {n : ℕ} (lz : DominantWeight n) (i : Fin n) :
    0 ≤ lz.val i + (lz.shift : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
  have hlast : lz.val (Fin.last m) ≤ lz.val i := lz.property (Fin.le_last i)
  show 0 ≤ lz.val i + (((-(lz.val (Fin.last m))).toNat : ℕ) : ℤ)
  omega

/-- The non-negative weight `λ.toNatWeight` recovers `λ`: `(λ.toNatWeight i : ℤ) = λ_i + shift`. -/
private theorem dominantWeight_toNatWeight_cast {n : ℕ} (lz : DominantWeight n) (i : Fin n) :
    (lz.toNatWeight i : ℤ) = lz.val i + (lz.shift : ℤ) := by
  show (((lz.val i + (lz.shift : ℤ)).toNat : ℕ) : ℤ) = lz.val i + (lz.shift : ℤ)
  rw [Int.toNat_of_nonneg (dominantWeight_shift_nonneg lz i)]

/-- **Distinct dominant weights give non-isomorphic `L_λ`.** For `λ ≠ μ`,
`algIrrepGLRepρ n λ k` and `algIrrepGLRepρ n μ k` are non-isomorphic as
`k[GL_n]`-modules (the highest-weight / formal-character classification). The
distinguishing invariant is the Schur-polynomial formal character of a common
determinant twist; see the module docstring for the full route. -/
theorem algIrrepGLRepρ_noniso (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {lam mu : DominantWeight n} (hne : lam ≠ mu) :
    ¬ Nonempty ((algIrrepGLRepρ n lam k).asModule ≃ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin n) k)] (algIrrepGLRepρ n mu k).asModule) := by
  rintro ⟨e⟩
  apply hne
  -- An equivariant `k[GL]`-module equiv restricts to a `GL`-intertwining `k`-linear equiv.
  set f : AlgIrrepGL n lam k ≃ₗ[k] AlgIrrepGL n mu k :=
    (((algIrrepGLRepρ n lam k).asModuleEquiv).symm.trans (e.restrictScalars k)).trans
      ((algIrrepGLRepρ n mu k).asModuleEquiv) with hf
  have hf_int : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : AlgIrrepGL n lam k),
      f (algIrrepGLRepρ n lam k g v) = algIrrepGLRepρ n mu k g (f v) := by
    intro g v
    simp only [hf, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      Representation.asModuleEquiv_symm_map_rho, map_smul,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
  -- The same `f` intertwines the `det^M`-twists, for any character `c`.
  have hf_twist : ∀ (c : Matrix.GeneralLinearGroup (Fin n) k →* kˣ)
      (g : Matrix.GeneralLinearGroup (Fin n) k) (v : AlgIrrepGL n lam k),
      f (charTwistRep c (algIrrepGLRepρ n lam k) g v)
        = charTwistRep c (algIrrepGLRepρ n mu k) g (f v) := by
    intro c g v
    rw [charTwistRep_apply, map_smul, hf_int, charTwistRep_apply]
  -- Twisting by `det^M`, `M = λ.shift + μ.shift`, clears both determinant shifts to honest
  -- polynomial Schur modules.
  have hclear : ∀ (lz : DominantWeight n), lz.shift ≤ lam.shift + mu.shift →
      charTwistRep (detChar k n ^ ((lam.shift + mu.shift : ℕ) : ℤ)) (algIrrepGLRepρ n lz k)
        = charTwistRep (detChar k n ^ (((lam.shift + mu.shift) - lz.shift : ℕ) : ℤ))
            (schurModuleRep k n lz.toNatWeight) := by
    intro lz hle
    unfold algIrrepGLRepρ
    rw [charTwistRep_charTwistRep, ← zpow_add]
    congr 2
    omega
  -- Equal formal characters of the common twist (via `f`).
  have hchar := formalCharacter_eq_of_rep_iso k n
    (charTwistRep (detChar k n ^ ((lam.shift + mu.shift : ℕ) : ℤ)) (algIrrepGLRepρ n lam k))
    (charTwistRep (detChar k n ^ ((lam.shift + mu.shift : ℕ) : ℤ)) (algIrrepGLRepρ n mu k))
    f (hf_twist _)
  rw [hclear lam (by omega), hclear mu (by omega),
      formalCharacter_charTwist_detChar_pow k n lam.toNatWeight lam.toNatWeight_antitone _,
      formalCharacter_charTwist_detChar_pow k n mu.toNatWeight mu.toNatWeight_antitone _] at hchar
  -- Equal Schur polynomials ⟹ equal weights ⟹ `λ = μ`.
  have hweq := schurPoly_injective n _ _
    (fun i j hij => Nat.add_le_add_right (lam.toNatWeight_antitone hij) _)
    (fun i j hij => Nat.add_le_add_right (mu.toNatWeight_antitone hij) _) hchar
  apply Subtype.ext
  funext i
  have hi := congrFun hweq i
  have hcl := dominantWeight_toNatWeight_cast lam i
  have hcm := dominantWeight_toNatWeight_cast mu i
  have : (lam.toNatWeight i : ℤ) + ((lam.shift + mu.shift) - lam.shift : ℕ)
      = (mu.toNatWeight i : ℤ) + ((lam.shift + mu.shift) - mu.shift : ℕ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hi
  omega

/-- **Uniqueness of the highest weight (the complete-invariant classification).**
The dominant integer weight `λ` is a complete invariant of the irreducible algebraic
representation `L_λ = algIrrepGLRepρ n λ k`: two of these irreducibles are isomorphic
as `k[GL_n]`-modules **iff** their highest weights coincide. This is the faithful
Lean rendering of the book's assertion (Discussion after Definition 5.23.1) that to
every weakly-decreasing integer sequence `λ₁ ≥ ⋯ ≥ λ_N` there is attached a *unique*
irreducible algebraic representation `L_λ`, whose highest weight is `λ`. The forward
direction is `algIrrepGLRepρ_noniso`; the reverse is the identity isomorphism. -/
theorem algIrrepGLRepρ_iso_iff_eq (n : ℕ) (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] {lam mu : DominantWeight n} :
    Nonempty ((algIrrepGLRepρ n lam k).asModule ≃ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin n) k)] (algIrrepGLRepρ n mu k).asModule) ↔
      lam = mu := by
  constructor
  · intro h
    by_contra hne
    exact algIrrepGLRepρ_noniso n k hne h
  · rintro rfl
    exact ⟨LinearEquiv.refl _ _⟩

end Etingof
