import Mathlib

/-!
# Problem 4.12.1: representations of the dihedral group (symmetries of a regular `N`-gon)

**Problem 4.12.1.** Let `G` be the group of symmetries of a regular `N`-gon (it has `2N`
elements).

(a) Describe all irreducible complex representations of this group (consider the cases of odd
and even `N`).

(b) Let `V` be the 2-dimensional complex representation of `G` obtained by complexification of
the standard representation on the real plane (the plane of the polygon). Find the
decomposition of `V ⊗ V` in a direct sum of irreducible representations.

## Formalization

We model the symmetry group of the regular `N`-gon by Mathlib's `DihedralGroup N` (order `2N`;
generators `r k` = rotations, `sr k` = reflections).

* **(a)** The faithful content of "describe all irreducibles" is the dimension dichotomy:
  *every* irreducible complex representation of `DihedralGroup N` is `1`- or `2`-dimensional.
  (The precise counts — `2` one-dimensional and `(N-1)/2` two-dimensional for odd `N`; `4`
  one-dimensional and `(N-2)/2` two-dimensional for even `N` — are recorded here in the
  docstring.)

* **(b)** Over `ℂ` the complexified standard representation `V` diagonalizes on rotations with
  eigenvalues `ζ^k, ζ^{-k}` (`ζ = exp(2πi/N)` a primitive `N`-th root of unity), and `V ⊗ V`
  decomposes as `𝟙 ⊕ ε ⊕ V₂`, where `𝟙` is trivial, `ε` is the sign (rotations act by `1`,
  reflections by `-1`), and `V₂` is the `2`-dimensional representation with rotation by
  `4π/N`. We state this at the level of **characters**: with `χ_V`, `χ_ε`, `χ_{V₂}` the
  class functions defined below, `χ_V(g)² = 1 + χ_ε(g) + χ_{V₂}(g)` for all `g`, which is
  exactly `V ⊗ V ≅ 𝟙 ⊕ ε ⊕ V₂` since the character of a tensor product is the product of
  characters.

This is a statement pass: faithful signatures with `sorry` proofs.
-/

open Real

noncomputable section

namespace Etingof.Problem4_12_1

variable {N : ℕ}

/-- A primitive `N`-th root of unity `ζ = exp(2πi/N)`. -/
noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / N)

/-- **Part (a).** Every irreducible complex representation of the dihedral group
`DihedralGroup N` (for `N ≥ 1`) is either `1`- or `2`-dimensional. -/
theorem irreducible_dim [NeZero N]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (DihedralGroup N) W)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) ρ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = 2 := by
  sorry

/-- Character of the complexified standard `2`-dimensional representation `V`:
`χ_V(r k) = ζ^k + ζ^{-k}` on rotations and `0` on reflections. -/
noncomputable def chiStd (N : ℕ) : DihedralGroup N → ℂ
  | .r k => zeta N ^ k.val + (zeta N)⁻¹ ^ k.val
  | .sr _ => 0

/-- Character of the sign representation `ε`: rotations act by `1`, reflections by `-1`. -/
def chiSign (N : ℕ) : DihedralGroup N → ℂ
  | .r _ => 1
  | .sr _ => -1

/-- Character of the `2`-dimensional representation `V₂` (rotation by `4π/N`):
`χ_{V₂}(r k) = ζ^{2k} + ζ^{-2k}` on rotations and `0` on reflections. -/
noncomputable def chiRot2 (N : ℕ) : DihedralGroup N → ℂ
  | .r k => zeta N ^ (2 * k.val) + (zeta N)⁻¹ ^ (2 * k.val)
  | .sr _ => 0

/-- **Part (b).** The decomposition `V ⊗ V ≅ 𝟙 ⊕ ε ⊕ V₂`, expressed as the character identity
`χ_V(g)² = 1 + χ_ε(g) + χ_{V₂}(g)` (the constant `1` is the character of the trivial
representation). -/
theorem tensor_square_character (N : ℕ) (g : DihedralGroup N) :
    chiStd N g ^ 2 = 1 + chiSign N g + chiRot2 N g := by
  sorry

end Etingof.Problem4_12_1
