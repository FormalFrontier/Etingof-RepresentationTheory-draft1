import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import EtingofRepresentationTheory.Chapter3.Theorem3_3_1

/-!
# Problem 3.3.3: An alternative proof of Theorem 3.3.1

The problem gives an alternative route to Theorem 3.3.1 through the structure of a direct
sum of algebras.

Let `A = A₁ ⊕ ⋯ ⊕ Aₙ` (modeled as the finite product algebra `∀ i, 𝒜 i`), with unit
idempotents `1ᵢ = Pi.single i 1`.

* **(a)** A representation `V` of `A` is irreducible iff `1ᵢ V` is an irreducible
  representation of `Aᵢ` for exactly one `i`, while `1ⱼ V = 0` for all other `j`. Here
  `1ᵢ V` is the `A`-submodule `LinearMap.range (idemProj i)`, the image of the (central,
  hence `A`-linear) projection `v ↦ 1ᵢ • v`. Since the factors `Aⱼ` with `j ≠ i` act as
  `0` on `1ᵢ V`, the `A`-submodules of `1ᵢ V` are exactly its `Aᵢ`-submodules, so
  "irreducible representation of `Aᵢ`" is faithfully rendered as
  `IsSimpleModule A (1ᵢ V)`.

* **(b)** The only irreducible representation of `Matₙ(k) = Mat_d(k)` is `k^d`, and every
  finite dimensional representation of `Mat_d(k)` is a direct sum of copies of `k^d`
  (i.e. isomorphic to `(k^d)^n = Fin n → (Fin d → k)` for some `n`).

* **(c)** Theorem 3.3.1 follows; the full statement is already recorded as
  `Etingof.irreducible_reps_of_matrix_algebra` in `Theorem3_3_1`.

Statement pass: all proofs are left as `sorry`.
-/

namespace Etingof.Problem3_3_3

/-! ## Part (a): irreducibles of a direct sum of algebras

Part (a) is pure ring/module theory: it needs no base field, only the product ring
`A = ∀ i, 𝒜 i` and an `A`-module `V`. -/

section PartA

variable {r : ℕ} (𝒜 : Fin r → Type*) [∀ i, Ring (𝒜 i)]
  (V : Type*) [AddCommGroup V] [Module (∀ i, 𝒜 i) V]

/-- The unit idempotent `1ᵢ = Pi.single i 1` of the product algebra is central. -/
theorem single_one_central (i : Fin r) (a : ∀ i, 𝒜 i) :
    (Pi.single i 1 : ∀ i, 𝒜 i) * a = a * Pi.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

/-- The `A`-linear projection `v ↦ 1ᵢ • v`. It is `A`-linear because `1ᵢ` is central. Its
range is the subrepresentation `1ᵢ V`. -/
def idemProj (i : Fin r) : V →ₗ[∀ i, 𝒜 i] V where
  toFun v := (Pi.single i 1 : ∀ i, 𝒜 i) • v
  map_add' v w := smul_add _ _ _
  map_smul' a v := by
    simp only [RingHom.id_apply, smul_smul]
    rw [single_one_central 𝒜 i a]

/-- **Problem 3.3.3(a).** A representation `V` of `A = ⊕ᵢ Aᵢ` is irreducible if and only if
`1ᵢ V` is an irreducible representation of `Aᵢ` for exactly one `i`, while `1ⱼ V = 0` for
all other `j`. -/
theorem simpleModule_prod_iff :
    IsSimpleModule (∀ i, 𝒜 i) V ↔
      ∃ i, IsSimpleModule (∀ i, 𝒜 i) (LinearMap.range (idemProj 𝒜 V i)) ∧
        ∀ j, j ≠ i → LinearMap.range (idemProj 𝒜 V j) = ⊥ := by
  sorry

end PartA

/-! ## Part (b): representations of a single matrix algebra `Mat_d(k)` -/

open scoped Matrix.Module

section PartB

variable (k : Type*) [Field k] (d : ℕ) [NeZero d]

/-- **Problem 3.3.3(b), existence.** The standard representation `k^d` is an irreducible
representation of `Mat_d(k)`. -/
theorem std_isSimpleModule :
    IsSimpleModule (Matrix (Fin d) (Fin d) k) (Fin d → k) := by
  sorry

/-- **Problem 3.3.3(b), uniqueness.** Every finite dimensional irreducible representation of
`Mat_d(k)` is isomorphic to the standard representation `k^d`. -/
theorem simpleModule_iso_std (V : Type*) [AddCommGroup V] [Module k V]
    [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] [IsSimpleModule (Matrix (Fin d) (Fin d) k) V] :
    Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin d → k)) := by
  sorry

/-- **Problem 3.3.3(b), decomposition.** Every finite dimensional representation of
`Mat_d(k)` is a direct sum of copies of the standard representation `k^d`: it is isomorphic
to `(k^d)^n = Fin n → (Fin d → k)` for some `n`. -/
theorem finite_iso_std_pow (V : Type*) [AddCommGroup V] [Module k V]
    [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] :
    ∃ n : ℕ, Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin n → (Fin d → k))) := by
  sorry

end PartB

/-! ## Part (c): deducing Theorem 3.3.1

Part (c) asks to deduce Theorem 3.3.1 from (a) and (b). The full statement — for
`A = ⊕ᵢ Mat_{dᵢ}(k)`, the irreducibles are the `k^{dᵢ}` and every finite dimensional
representation is a direct sum of copies of them — is recorded (and proved) as
`Etingof.irreducible_reps_of_matrix_algebra` in `Theorem3_3_1`. -/

end Etingof.Problem3_3_3
