import EtingofRepresentationTheory.Chapter9.PathAlgebraConsSplitting
import EtingofRepresentationTheory.Chapter9.PathAlgebraInducedGrading

/-!
# The cons-splitting degree shift for `A = PathAlgebra k Q`

Seventh layer of the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i), parent #6420). Write `A := PathAlgebra k Q`, `S := Q → k` the vertex
subalgebra, `V` the arrow bimodule (`Chapter9/PathAlgebraArrowBimodule.lean`). This file records
the length-grading behaviour of **right multiplication by an arrow** and packages the resulting
degree-`(+1)` shift of the boundary map `d` of the standard short complex
(`Chapter9/PathAlgebraStandardComplex.lean`), the noncommutative analogue of the `coeff_X_mul`
shift used by `koszulSES_shortExact` (`Chapter9/Example9_4_4.lean`).

The combinatorial core underlying the *cons-splitting isomorphism* `A_n ⊗_S V ≅ A_{n+1}` is in
`Chapter9/PathAlgebraConsSplitting.lean` (`exists_ofPath_mul_arrowElt`, `ofPath_mul_arrowElt_inj`).
Here we add the analytic companion: multiplying a homogeneous degree-`n` element on the right by an
arrow (`arrowInclusion v`, degree `1`) lands exactly in degree `n + 1`
(`lengthProj_mul_arrowInclusion`). This is the seed of both

* **`Mono (stdd M)`** — the degree-`(N+1)` component of `d(ξ)` is the cons-splitting applied to the
  top component `ξ_N` (issue #6512 deliverable 1), and
* the bundled `S`-bimodule isomorphism `A_n ⊗_S V ≅ A_{n+1}` (deliverable 2b),

both consumed by `standardResolution_shortExact` (issue #6512).
-/

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace Etingof.PathAlgebra

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]

/-! ## Right multiplication by an arrow shifts the length grading by one -/

/-- **Length projection of a basis path times an arrow.** The product `ofPath x · arrowElt y` is a
single basis path of length `pathLen x + 1` (or `0` when the two are not composable), so its
degree-`m` homogeneous component is itself exactly when `m = pathLen x + 1`. The general-arrow,
all-degrees companion of `lengthProj_ofPath_mul_arrowElt`. -/
theorem lengthProj_ofPath_mul_arrowElt_gen (m : ℕ) (x : QuiverPathIndex Q) (y : ArrowIndex Q) :
    lengthProj k Q m ((ofPath x : PathAlgebra k Q) * arrowElt y)
      = if pathLen x + 1 = m then (ofPath x : PathAlgebra k Q) * arrowElt y else 0 := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, e⟩ := y
  rw [arrowElt, ArrowIndex.toPathIndex, ofPath_mul_ofPath]
  by_cases hbc : b = c
  · subst hbc
    rw [compSingle_eq, lengthProj_single, pathLen_mk, Quiver.Path.length_comp,
      Quiver.Path.length_toPath, pathLen_mk]
  · rw [compSingle_eq_zero _ _ hbc, map_zero, ite_self]

/-- **Right multiplication by an arrow shifts the length grading by one.** For any `a ∈ A` and any
`v ∈ V`, the degree-`(n+1)` homogeneous component of `a · arrowInclusion v` is the degree-`n`
component of `a`, still multiplied by `arrowInclusion v`. This is the analytic seed of the
cons-splitting `A_n ⊗_S V ≅ A_{n+1}` and of the top-degree component of `d`. -/
theorem lengthProj_mul_arrowInclusion (n : ℕ) (a : PathAlgebra k Q) (v : ArrowIndex Q →₀ k) :
    lengthProj k Q (n + 1) (a * arrowInclusion v) = lengthProj k Q n a * arrowInclusion v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, mul_add, map_add, hv, hw, mul_add]
  | single y d =>
    rw [arrowInclusion_single]
    -- reduce to the single-arrow case `a * arrowElt y`, pulling the scalar `d` out
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [add_mul, map_add, map_add, add_mul, hf, hg]
    | single x c =>
      have hsx : (Finsupp.single x c : PathAlgebra k Q) = c • ofPath x := by
        rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsx, smul_mul, mul_smul', map_smul, map_smul,
        lengthProj_ofPath_mul_arrowElt_gen]
      simp only [add_left_inj]
      rw [map_smul, show (lengthProj k Q n) (ofPath x)
          = if pathLen x = n then (ofPath x : PathAlgebra k Q) else 0 from by
            rw [ofPath, lengthProj_single]]
      split_ifs with h
      · rw [smul_mul, mul_smul']
      · simp

end Etingof.PathAlgebra
