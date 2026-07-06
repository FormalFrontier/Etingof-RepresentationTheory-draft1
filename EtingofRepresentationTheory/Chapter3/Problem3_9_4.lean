import EtingofRepresentationTheory.Chapter3.Problem3_9_1
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Problem 3.9.4: Formal deformations of representations

Let `A` be an algebra and `V` a representation with structure map `ρ : A → End V`. A
**formal deformation** of `V` is a formal power series
`ρ̃ = ρ₀ + tρ₁ + ⋯ + tⁿρₙ + ⋯`, where each `ρᵢ : A →ₗ End V`, `ρ₀ = ρ`, and
`ρ̃(ab) = ρ̃(a)ρ̃(b)`. If `b(t) = 1 + b₁t + b₂t² + ⋯` with `bᵢ ∈ End V`, then `b ρ̃ b⁻¹` is
an isomorphic deformation.

* **(a)** If `Ext¹(V, V) = 0` then every deformation of `ρ` is trivial (isomorphic to `ρ`).
* **(b)** Is the converse true? (Consider the dual numbers `A = k[x]/x²`.)

We encode `ρ̃` by its coefficient sequence `coeff : ℕ → (A →ₗ[k] End_k V)`. The condition
`ρ̃(ab) = ρ̃(a)ρ̃(b)` becomes, coefficient by coefficient,
`ρₙ(ab) = ∑_{i+j=n} ρᵢ(a) ∘ ρⱼ(b)` (Cauchy product). Two deformations are isomorphic when a
power series `b(t)` with `b₀ = id` intertwines them: `b ρ̃ = ρ̃' b` coefficientwise. The base
representation is `ρ₀ = ρ`, the bundled action `A →ₗ[k] End_k V`.

`Ext¹(V, V) = 0` reuses `Etingof.Problem3_9_1.Ext1`, phrased as `Subsingleton (Ext1 …)`.

Statement pass: the deformation data (`FormalDeformation`, the constant deformation, the
isomorphism relation) is genuinely constructed; proof obligations are `sorry`.
-/

namespace Etingof.Problem3_9_4

open Etingof.Problem3_9_1 (Ext1)

variable (k : Type*) (A : Type*) (V : Type*)
  [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The base representation `ρ₀ = ρ`, the action of `A` on `V` bundled as a `k`-linear map
`A →ₗ[k] End_k V`. Genuinely constructed via `Algebra.lsmul`. -/
noncomputable def baseRho : A →ₗ[k] (V →ₗ[k] V) :=
  (Algebra.lsmul k k V).toLinearMap

/-- A **formal deformation** of the representation `V`: a sequence of `k`-linear maps
`ρₙ : A →ₗ[k] End_k V` with `ρ₀` the base representation and satisfying the Cauchy-product
multiplicativity `ρₙ(ab) = ∑_{i+j=n} ρᵢ(a) ∘ ρⱼ(b)` encoding `ρ̃(ab) = ρ̃(a)ρ̃(b)`. -/
structure FormalDeformation where
  /-- The coefficient maps `ρₙ`. -/
  coeff : ℕ → (A →ₗ[k] (V →ₗ[k] V))
  /-- `ρ₀ = ρ` is the base representation. -/
  base_eq : coeff 0 = baseRho k A V
  /-- `ρ̃(ab) = ρ̃(a)ρ̃(b)`, coefficient by coefficient. -/
  isMul : ∀ (a b : A) (n : ℕ),
    coeff n (a * b)
      = ∑ p ∈ Finset.antidiagonal n, (coeff p.1 a).comp (coeff p.2 b)

/-- The **trivial (constant) deformation** `ρ̃ = ρ`: `ρ₀ = ρ` and `ρₙ = 0` for `n ≥ 1`. The
coefficient data is genuinely constructed; the multiplicativity proof obligation is left as
`sorry` (statement pass). -/
noncomputable def constDeformation : FormalDeformation k A V where
  coeff n := if n = 0 then baseRho k A V else 0
  base_eq := by simp
  isMul := by sorry

/-- Two deformations `D`, `D'` are **isomorphic** when there is a power series
`b(t) = 1 + b₁t + ⋯` with `b₀ = id` intertwining them: `b ρ̃ = ρ̃' b`, i.e.
`∑_{i+j=n} bᵢ ∘ ρⱼ(a) = ∑_{i+j=n} ρ'ᵢ(a) ∘ bⱼ` for all `a, n`. -/
def IsIsomorphic (D D' : FormalDeformation k A V) : Prop :=
  ∃ b : ℕ → (V →ₗ[k] V), b 0 = LinearMap.id ∧
    ∀ (a : A) (n : ℕ),
      ∑ p ∈ Finset.antidiagonal n, (b p.1).comp (D.coeff p.2 a)
        = ∑ p ∈ Finset.antidiagonal n, (D'.coeff p.1 a).comp (b p.2)

/-- A deformation is **trivial** if it is isomorphic to the constant deformation `ρ`. -/
def IsTrivial (D : FormalDeformation k A V) : Prop :=
  IsIsomorphic k A V D (constDeformation k A V)

/-- **Problem 3.9.4(a).** If `Ext¹(V, V) = 0`, every formal deformation of `ρ` is trivial. -/
theorem isTrivial_of_ext1_subsingleton
    (hExt : Subsingleton (Ext1 k A V V)) (D : FormalDeformation k A V) :
    IsTrivial k A V D := by
  sorry

/-- The **converse to (a)** for a fixed representation `V`: if every formal deformation of
`V` is trivial, then `Ext¹(V, V) = 0`. -/
def ConverseHolds : Prop :=
  (∀ D : FormalDeformation k A V, IsTrivial k A V D) → Subsingleton (Ext1 k A V V)

/-- **Problem 3.9.4(b).** Is the converse to (a) true? The suggested test case is the
algebra of dual numbers `A = k[x]/x²` (`DualNumber k`). This proposition is the converse
specialised to a representation `V` of the dual numbers; the exercise asks whether it holds
(the answer is expected to involve obstructions to extending first-order deformations). -/
def Problem3_9_4b (V : Type*)
    [AddCommGroup V] [Module k V] [Module (DualNumber k) V]
    [IsScalarTower k (DualNumber k) V] : Prop :=
  ConverseHolds k (DualNumber k) V

end Etingof.Problem3_9_4
