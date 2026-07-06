import Mathlib

/-!
# Exercise 2.9.5: `ℝ³` with the cross product is a special case of `𝔰𝔬(n)` (for `n = 3`)

> **Exercise 2.9.5.** Show that example (1) is a special case of example (5) (for `n = 3`).

## Which examples

The exercise refers to the *concrete* list of Lie algebras in §2.9 (blob
`blobs/Chapter2/Discussion_concrete_Lie_examples{,_continued}.md`), **not** the
abstract list of Example 2.9.2. In that concrete list:

* example (1) is `ℝ³` with `[u, v] = u × v` (the cross product), and
* example (5) is `𝔰𝔬(n)`, the skew-symmetric `n × n` matrices with `[a, b] = ab − ba`.

So the exercise asks to exhibit `(ℝ³, ×)` as `𝔰𝔬(3)`: there is a Lie algebra
isomorphism `𝔰𝔬(3) ≅ (ℝ³, ×)`. Concretely this is the classical "hat map"
`(a, b, c) ↦ ![![0, -c, b], ![c, 0, -a], ![-b, a, 0]]`, whose matrix acts on a
vector exactly by cross product with `(a, b, c)`.

## Mathlib correspondence

* `(ℝ³, ×)`: the cross product `crossProduct` (notation `⨯₃`) and the Lie ring it
  defines, `Cross.lieRing`, live in `Mathlib.LinearAlgebra.CrossProduct`. Both are
  non-instances (a bracket diamond with `LieRing.ofAssociativeRing` would otherwise
  occur), so we re-enable `Cross.lieRing` as a local instance and supply the
  matching `LieAlgebra ℝ` instance (`lie_smul` from bilinearity of `crossProduct`).
* `𝔰𝔬(3)`: `LieAlgebra.Orthogonal.so (Fin 3) ℝ`, the definite orthogonal Lie
  subalgebra of skew-symmetric matrices (`mem_so : A ∈ so n R ↔ Aᵀ = -A`).

The main statement records the isomorphism as `Nonempty (so 3 ≃ₗ⁅ℝ⁆ (ℝ³, ×))`; the
construction of the explicit hat-map equivalence is left as `sorry` (statement pass).
-/

namespace Etingof.Exercise2_9_5

open Matrix LieAlgebra

-- `Cross.lieRing` is a non-instance in Mathlib (to avoid a bracket diamond with
-- `LieRing.ofAssociativeRing`); re-enable it locally for `Fin 3 → ℝ`.
attribute [local instance] Cross.lieRing

/-- `ℝ³` with the cross product is not merely a Lie *ring* but a Lie *algebra* over `ℝ`:
the bracket `crossProduct` is `ℝ`-bilinear, so `⁅x, c • y⁆ = c • ⁅x, y⁆`. -/
noncomputable local instance crossLieAlgebra : LieAlgebra ℝ (Fin 3 → ℝ) where
  lie_smul c x y := by
    change crossProduct x (c • y) = c • crossProduct x y
    rw [map_smul]

/-- The bracket on `ℝ³` really is the cross product `u × v`. (concrete example (1)) -/
theorem bracket_eq_cross (u v : Fin 3 → ℝ) : ⁅u, v⁆ = u ⨯₃ v := rfl

/-- Membership in `𝔰𝔬(3)`: a `3 × 3` real matrix is skew-symmetric iff it lies in `so 3`.
(concrete example (5), `n = 3`) -/
theorem mem_so3 (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A ∈ Orthogonal.so (Fin 3) ℝ ↔ Aᵀ = -A :=
  Orthogonal.mem_so (n := Fin 3) (R := ℝ) A

/-- **Exercise 2.9.5.** The Lie algebra `ℝ³` with the cross product (concrete example (1))
is isomorphic to `𝔰𝔬(3)` (concrete example (5) at `n = 3`): there is a Lie algebra isomorphism
`𝔰𝔬(3) ≅ (ℝ³, ×)`, realized by the "hat map" sending a vector to the matrix whose action is
cross product with that vector. -/
theorem so3_lieEquiv_cross :
    Nonempty (Orthogonal.so (Fin 3) ℝ ≃ₗ⁅ℝ⁆ (Fin 3 → ℝ)) :=
  sorry

end Etingof.Exercise2_9_5
