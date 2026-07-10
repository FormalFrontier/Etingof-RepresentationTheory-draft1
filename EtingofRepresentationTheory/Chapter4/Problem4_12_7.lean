import Mathlib

/-!
# Problem 4.12.7: `SU(2)`, the quaternions, and `SU(2) → SO(3)`

**Problem 4.12.7.** Let `G = SU(2)` (the group of unitary `2 × 2` matrices with determinant
`1`), and let `V = ℂ²` be the standard `2`-dimensional representation of `SU(2)`. We regard
`V` as a real representation, so it is `4`-dimensional.

(a) Show that `V` is irreducible (as a real representation).

(b) Let `ℍ` be the subspace of `End_ℝ(V)` consisting of endomorphisms of `V` as a real
representation. Show that `ℍ` is `4`-dimensional and closed under multiplication, and that
every nonzero element is invertible (`ℍ` is a division algebra).

(c) Find a basis `1, i, j, k` of `ℍ` with `i² = j² = k² = -1`, `ij = -ji = k`, etc. Thus
`Q₈` is a subgroup of `ℍˣ`.

(d) For `q = a + bi + cj + dk`, let `q̄ = a - bi - cj - dk` and `‖q‖² = q q̄`. Show that
`overline(q₁ q₂) = q̄₂ q̄₁` and `‖q₁ q₂‖ = ‖q₁‖ · ‖q₂‖`.

(e) Let `G` be the group of quaternions of norm `1`. Show that this group is isomorphic to
`SU(2)`.

(f) Consider the action of `G` on the space `V ⊆ ℍ` spanned by `i, j, k`, by
`x ↦ q x q⁻¹`. Since this preserves the norm, we get a homomorphism `h : SU(2) → SO(3)`.
Show that `h` is surjective and that its kernel is `{1, -1}`.

## Formalization

We model `SU(2)` by Mathlib's `Matrix.specialUnitaryGroup (Fin 2) ℂ` (unitary `2×2` complex
matrices of determinant `1`, a `Group`), `SO(3)` by `Matrix.specialOrthogonalGroup (Fin 3) ℝ`,
and the quaternions by `ℍ[ℝ] = Quaternion ℝ`. The group of unit quaternions is
`unitary ℍ[ℝ]` (`{q : star q * q = 1 = q * star q}`, i.e. `normSq q = 1`).

This is a statement pass: we give faithful signatures for parts **(a)**, **(d)**, **(e)**,
**(f)** with `sorry` proofs. Parts (b) and (c) (the commutant description of `ℍ` and the
explicit `1, i, j, k` basis) are left for a later pass.

* **(a)** `V = ℂ²` as a real representation: `Fin 2 → ℂ` is an `ℝ`-module and `SU(2)` acts
  `ℝ`-linearly by `Matrix.mulVec`. Irreducibility over `ℝ` is: every `SU(2)`-invariant
  `ℝ`-submodule is `⊥` or `⊤`.
* **(d)** conjugation reverses products (`star (q₁ q₂) = star q₂ * star q₁`) and the norm is
  multiplicative (`normSq (q₁ q₂) = normSq q₁ * normSq q₂`).
* **(e)** the group of unit quaternions is isomorphic (as a group) to `SU(2)`.
* **(f)** there is a surjective homomorphism `SU(2) → SO(3)` whose kernel consists exactly of
  `±1` (the two matrices `1` and `-1`).
-/

open scoped Quaternion
open Matrix

namespace Etingof.Problem4_12_7

/-- **Part (a).** The standard `2`-dimensional representation `V = ℂ²` of `SU(2)`, regarded as
a *real* representation (`SU(2)` acts `ℝ`-linearly on `Fin 2 → ℂ` by matrix-vector
multiplication), is irreducible: every `SU(2)`-invariant `ℝ`-subspace of `Fin 2 → ℂ` is
either `⊥` or `⊤`. -/
theorem real_irreducible
    (W : Submodule ℝ (Fin 2 → ℂ))
    (hW : ∀ A : Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ v : Fin 2 → ℂ,
      v ∈ W → (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  sorry

/-- **Part (d), conjugate of a product.** Quaternion conjugation (`star`) reverses products:
`overline(q₁ q₂) = q̄₂ q̄₁`. -/
theorem star_mul_rev (q₁ q₂ : ℍ[ℝ]) :
    star (q₁ * q₂) = star q₂ * star q₁ :=
  star_mul q₁ q₂

/-- **Part (d), multiplicativity of the norm.** The quaternion norm-square is multiplicative:
`‖q₁ q₂‖² = ‖q₁‖² · ‖q₂‖²`. -/
theorem normSq_mul (q₁ q₂ : ℍ[ℝ]) :
    Quaternion.normSq (q₁ * q₂) = Quaternion.normSq q₁ * Quaternion.normSq q₂ :=
  map_mul Quaternion.normSq q₁ q₂

/-- **Part (e).** The group of unit quaternions (`unitary ℍ[ℝ]`, i.e. quaternions of norm `1`)
is isomorphic, as a group, to `SU(2)`. -/
theorem unit_quaternions_mulEquiv_SU2 :
    Nonempty (unitary ℍ[ℝ] ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  sorry

/-- **Part (f).** There is a surjective group homomorphism `h : SU(2) → SO(3)` whose kernel is
exactly `{1, -1}`: `A ∈ ker h` iff the matrix of `A` is `1` or `-1`. -/
theorem exists_surjective_hom_to_SO3 :
    ∃ h : Matrix.specialUnitaryGroup (Fin 2) ℂ →*
        Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      Function.Surjective h ∧
      ∀ A : Matrix.specialUnitaryGroup (Fin 2) ℂ,
        A ∈ h.ker ↔
          ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
           (A : Matrix (Fin 2) (Fin 2) ℂ) = -1) := by
  sorry

end Etingof.Problem4_12_7
