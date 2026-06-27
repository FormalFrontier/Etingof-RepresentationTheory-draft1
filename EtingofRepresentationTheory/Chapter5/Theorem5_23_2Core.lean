import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_23_1
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Theorem 5.23.2: core definitions

The dominant-weight and irreducible-algebraic-representation definitions
(`DominantWeight`, `AlgIrrepGL`, `AlgIrrepGLDual`) together with the nonvanishing
lemma `schurModuleSubmodule_ne_bot`, factored out of `Theorem5_23_2.lean`.

These are the only names the downstream GL-representation machinery
(`AlgIrrepGLRep`, `CauchyDetQuotient`, `SchurModuleSpecialBlock`) needs from
Theorem 5.23.2. Keeping them in a base file lets `Theorem5_23_2.lean` import the
complete-reducibility infrastructure (`PolynomialGLSemisimple`, `DetClearing`)
to discharge part (i) without forming an import cycle.
-/

open CategoryTheory
open scoped TensorProduct

noncomputable section

namespace Etingof

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

/-- A dominant weight for `GL_n` is a weakly decreasing sequence of integers
`(λ₁ ≥ λ₂ ≥ ⋯ ≥ λ_n)`. -/
def DominantWeight (n : ℕ) := { lam : Fin n → ℤ // Antitone lam }

/-- Shift amount to normalize a dominant weight to non-negative entries.
For an antitone (decreasing) weight, the minimum entry is at `Fin.last`. -/
def DominantWeight.shift : {n : ℕ} → DominantWeight n → ℕ
  | 0, _ => 0
  | _ + 1, lam => (-(lam.val (Fin.last _))).toNat

/-- Convert a dominant weight (integer-valued) to a natural-number weight by shifting
all entries by `shift` so that the minimum becomes 0. -/
def DominantWeight.toNatWeight {n : ℕ} (lam : DominantWeight n) : Fin n → ℕ :=
  fun i => (lam.val i + lam.shift).toNat

/-- The w₀-twist (longest element of Sₙ) of a dominant weight: reverses and negates.
`(w₀λ)ᵢ = -λ_{n-1-i}`. This maps dominant weights to dominant weights. -/
def DominantWeight.w0Twist {n : ℕ} (lam : DominantWeight n) : DominantWeight n :=
  ⟨fun i => -lam.val (Fin.rev i), fun i j hij => by
    simp only [neg_le_neg_iff]
    exact lam.property (Fin.rev_anti hij)⟩

/-- The irreducible algebraic representation of `GL_n(k)` with highest weight `λ`,
extended from `SchurModule` to integer weights via twisting by powers of the
determinant character. Returns the underlying `k`-module.

For a dominant weight `λ = (λ₁ ≥ ⋯ ≥ λ_n)`, we shift by `m = max(0, -λ_n)` to get
a non-negative weight `μ = λ + m·1ⁿ`, then define `L_λ = L_μ ⊗ det^{-m}`.
As a `k`-module (ignoring the GL-action), the tensor with the 1-dimensional det
representation does not change the underlying vector space, so the carrier type
is just `SchurModuleSubmodule k n μ`.
(See discussion after Definition 5.23.1.) -/
noncomputable def AlgIrrepGL (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Type _ :=
  ↥(SchurModuleSubmodule k n lam.toNatWeight)

noncomputable instance AlgIrrepGL.addCommGroup (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : AddCommGroup (AlgIrrepGL n lam k) :=
  show AddCommGroup ↥(SchurModuleSubmodule k n lam.toNatWeight) from inferInstance

noncomputable instance AlgIrrepGL.module (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module k (AlgIrrepGL n lam k) :=
  show Module k ↥(SchurModuleSubmodule k n lam.toNatWeight) from inferInstance

noncomputable instance AlgIrrepGL.finite (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module.Finite k (AlgIrrepGL n lam k) :=
  show Module.Finite k ↥(SchurModuleSubmodule k n lam.toNatWeight) from inferInstance

/-- The contragredient (dual) representation `L*_λ`.
For `GL_n`, the contragredient of `L_λ` is `L_{-w₀λ}` where `w₀` is the longest
element of `S_n` (the permutation that reverses order). -/
noncomputable def AlgIrrepGLDual (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Type _ :=
  AlgIrrepGL n lam.w0Twist k

noncomputable instance AlgIrrepGLDual.addCommGroup (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : AddCommGroup (AlgIrrepGLDual n lam k) :=
  AlgIrrepGL.addCommGroup n lam.w0Twist k

noncomputable instance AlgIrrepGLDual.module (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module k (AlgIrrepGLDual n lam k) :=
  AlgIrrepGL.module n lam.w0Twist k

instance DominantWeight.countable (n : ℕ) : Countable (DominantWeight n) :=
  Subtype.countable

-- The Schur polynomial is nonzero for any antitone weight.
-- Proof: s_λ · Δ = D_{λ+ρ}, and D_{λ+ρ} ≠ 0 since its diagonal coefficient is 1.
private theorem schurPoly_ne_zero (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    schurPoly N lam ≠ 0 := by
  intro h
  -- From schurPoly_mul_vandermonde: s_λ · Δ = D_{λ+ρ}
  have hprod := schurPoly_mul_vandermonde N lam
  rw [h, zero_mul] at hprod
  -- So D_{λ+ρ} = 0. But its diagonal coefficient is 1.
  have hstrict : StrictAnti (shiftedExps N lam) := by
    intro i j hij; simp only [shiftedExps]; have := hlam (le_of_lt hij); omega
  have hcoeff := alternant_coeff_kronecker hstrict hstrict
  rw [if_pos rfl] at hcoeff
  -- hcoeff : coeff ... D_{λ+ρ} = 1, but D_{λ+ρ} = 0, so coeff = 0
  rw [← hprod, MvPolynomial.coeff_zero] at hcoeff
  exact one_ne_zero hcoeff.symm

-- The SchurModuleSubmodule is nonzero for any antitone weight.
-- Uses the Weyl character formula: ch(L_λ) = s_λ ≠ 0.
-- rc4: synthesising `SMulZeroClass k ↥(glWeightSpace …)` now exceeds the default
-- 20000 typeclass heartbeats; bump the synthesis budget.
set_option synthInstance.maxHeartbeats 40000 in
theorem schurModuleSubmodule_ne_bot (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    SchurModuleSubmodule k N lam ≠ ⊥ := by
  intro h
  -- If SchurModuleSubmodule = ⊥, the Schur module is zero
  -- The formal character of a zero module is 0
  have hchar : formalCharacter k N (SchurModule k N lam) = 0 := by
    unfold formalCharacter
    apply Finset.sum_eq_zero
    intro μ _
    suffices Module.finrank k (glWeightSpace k N (SchurModule k N lam) (fun i => μ i)) = 0 by
      rw [this, Nat.cast_zero, zero_smul]
    -- SchurModuleSubmodule = ⊥ means the carrier is subsingleton
    have hsub : ∀ (a b : SchurModuleSubmodule k N lam), a = b := by
      intro ⟨a, ha⟩ ⟨b, hb⟩
      ext
      rw [h] at ha hb
      simp only [Submodule.mem_bot] at ha hb
      simp [ha, hb]
    -- SchurModule has same carrier type
    have hsub' : ∀ (a b : SchurModule k N lam), a = b := hsub
    -- Weight space finrank is 0
    rw [Module.finrank_eq_zero_iff]
    intro x
    have : x = 0 := by
      have := hsub' x.val 0
      exact Subtype.ext this
    exact ⟨1, one_ne_zero, by rw [this, smul_zero]⟩
  -- But ch(L_λ) = s_λ ≠ 0
  have hne := schurPoly_ne_zero N lam hlam
  rw [formalCharacter_schurModule_eq_schurPoly k N lam hlam] at hchar
  exact hne hchar


end Etingof
