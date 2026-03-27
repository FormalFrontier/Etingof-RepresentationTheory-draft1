import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_23_1
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Theorem 5.23.2: Complete Reducibility and Peter-Weyl for GL(V)

(i) Every finite dimensional algebraic representation of GL(V) is completely
reducible and decomposes into summands Lλ (which are pairwise nonisomorphic).

(ii) (Peter-Weyl for GL(V)) The algebra R of polynomial functions on GL(V),
as a representation of GL(V) × GL(V), decomposes as:
  R ≅ ⊕_λ L*λ ⊗ Lλ

## Mathlib correspondence

Complete reducibility for semisimple groups is partially in Mathlib.
The Peter-Weyl decomposition for GL(V) is not.
-/

open CategoryTheory
open scoped TensorProduct

noncomputable section

namespace Etingof

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- **Theorem 5.23.2 (i)**: Every finite-dimensional algebraic representation of
`GL_n(k)` is completely reducible. That is, if `ρ` is an algebraic representation
of `GL_n(k)` on a finite-dimensional `k`-vector space `Y`, then `Y` is a
semisimple module under the induced action.
(Etingof Theorem 5.23.2, part i) -/
theorem Theorem5_23_2_i
    (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Matrix.GeneralLinearGroup (Fin n) k →* (Y →ₗ[k] Y))
    (halg : Etingof.IsAlgebraicRepresentation n ρ) :
    IsSemisimpleModule k Y := by
  sorry

/-- The coordinate ring of `GL_n(k)`: the polynomial ring `k[Xᵢⱼ, D]` where `D`
represents `1/det`. This models the algebra `R` of regular (polynomial) functions
on `GL_n(k)`. -/
noncomputable abbrev GLCoordinateRing (n : ℕ) (k : Type*) [Field k] :=
  MvPolynomial (GLCoordVars n) k

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

/-- **Theorem 5.23.2 (ii)** (Peter-Weyl for GL(V)): The coordinate ring `R` of
`GL_n(k)`, as a representation of `GL_n(k) × GL_n(k)` via `(g,h) · φ(x) = φ(g⁻¹xh)`,
decomposes as `R ≅ ⊕_λ L*_λ ⊗ L_λ`, where the sum ranges over all dominant weights
`λ = (λ₁ ≥ ⋯ ≥ λ_n)` with `λᵢ ∈ ℤ`, and `L*_λ` is the contragredient of `L_λ`.

Stated as a `k`-linear isomorphism between the coordinate ring and the direct sum.
The equivariance with respect to the `GL_n × GL_n`-action is part of the proof
obligation.
(Etingof Theorem 5.23.2, part ii) -/
theorem Theorem5_23_2_ii
    (n : ℕ) :
    Nonempty (GLCoordinateRing n k ≃ₗ[k]
      (DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k))) := by
  sorry

end Etingof
