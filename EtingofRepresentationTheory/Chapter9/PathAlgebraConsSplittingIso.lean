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

/-- **Right multiplication by an arrow has no length-`0` component.** A product `a · arrowInclusion
v` is a combination of positive-length paths, so its degree-`0` homogeneous component vanishes. The
bottom-degree companion of `lengthProj_mul_arrowInclusion`. -/
theorem lengthProj_mul_arrowInclusion_zero (a : PathAlgebra k Q) (v : ArrowIndex Q →₀ k) :
    lengthProj k Q 0 (a * arrowInclusion v) = 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, mul_add, map_add, hv, hw, add_zero]
  | single y d =>
    rw [arrowInclusion_single]
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [add_mul, map_add, hf, hg, add_zero]
    | single x c =>
      have hsx : (Finsupp.single x c : PathAlgebra k Q) = c • ofPath x := by
        rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsx, smul_mul, mul_smul', map_smul, map_smul, lengthProj_ofPath_mul_arrowElt_gen,
        if_neg (Nat.succ_ne_zero _), smul_zero, smul_zero]

section Induced

variable [Fintype Q]

/-! ## The length-graded coordinate map on an arbitrary induced module `A ⊗_S N`

`inducedCoordMap` (`Chapter9/PathAlgebraInducedGrading.lean`) is stated for the *specific*
`S`-module `restrictObj M`. For the shift relation of `d` we also need it on the *domain*
`A ⊗_S (V ⊗_S M)`, whose `S`-module factor is `VtensObj M`, not of the form `restrictObj _`. We
package the same construction for an arbitrary `S`-module `N`. -/

variable (N : ModuleCat.{u + 1} (Q → k))

/-- **The length-graded coordinate map on `A ⊗_S N`**, for an arbitrary `S`-module `N`. The
`S`-linear map `A ⊗_S N →ₗ (ℕ →₀ A ⊗_S N)` sending `a ⊗ m` to `n ↦ (lengthProj n a) ⊗ m`. The
`N`-polymorphic version of `inducedCoordMap` (which is the `N = restrictObj M` case). -/
noncomputable def inducedCoordMapGen :
    TensorProduct (Q → k) (PathAlgebra k Q) N →ₗ[Q → k]
      (ℕ →₀ TensorProduct (Q → k) (PathAlgebra k Q) N) :=
  (TensorProduct.finsuppLeft (Q → k) (Q → k) (PathAlgebra k Q) N ℕ).toLinearMap.comp
    (TensorProduct.map (lengthGradingS k Q) LinearMap.id)

@[simp] theorem inducedCoordMapGen_tmul (a : PathAlgebra k Q) (m : N) (n : ℕ) :
    inducedCoordMapGen N (a ⊗ₜ[Q → k] m) n = (lengthProj k Q n a) ⊗ₜ[Q → k] m := by
  simp only [inducedCoordMapGen, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, lengthGradingS_apply, TensorProduct.finsuppLeft_apply_tmul_apply,
    lengthProj_apply]

/-- **Injectivity of the general coordinate map.** Inherited from the left inverse `lengthTotalizeS`
of `lengthGradingS` and the bijectivity of `TensorProduct.finsuppLeft`. The `N`-polymorphic version
of `inducedCoordMap_injective`. -/
theorem inducedCoordMapGen_injective : Function.Injective (inducedCoordMapGen N) := by
  have hleft : ∀ x : TensorProduct (Q → k) (PathAlgebra k Q) N,
      (TensorProduct.map (lengthTotalizeS k Q) (LinearMap.id (R := Q → k) (M := N)))
        (TensorProduct.map (lengthGradingS k Q) LinearMap.id x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, lengthTotalizeS_comp_lengthGradingS,
      LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
  intro x y hxy
  refine Function.LeftInverse.injective hleft ?_
  exact (TensorProduct.finsuppLeft (Q → k) (Q → k) (PathAlgebra k Q) N ℕ).injective hxy

/-! ## The degree shift of the boundary map `d`

For a pure generator `a ⊗ (v ⊗ m)` of the domain `A ⊗_S (V ⊗_S M)`, the degree-`(n+1)` component
of `d(a ⊗ v ⊗ m) = a·v ⊗ m − a ⊗ v·m` splits into the **cons-splitting** term
`(lengthProj n a · v) ⊗ m` (the top half, using `lengthProj_mul_arrowInclusion`) and the **lower**
term `−(lengthProj (n+1) a) ⊗ v·m`. This is the noncommutative analogue of the `coeff_X_mul` shift
in `koszulSES_shortExact`, and the seed of the top-degree `Mono (stdd M)` argument (issue #6512). -/

variable (M : ModuleCat.{u + 1} (PathAlgebra k Q))

/-- **The degree-`(n+1)` component of `d` on a generator.** The top half is the cons-splitting
`lengthProj n a · v` (degree `n → n+1`), the lower half is `lengthProj (n+1) a ⊗ v·m`. -/
theorem inducedCoordMap_stdd_tmul_succ (a : PathAlgebra k Q) (v : ArrowTgt k Q)
    (m : restrictObj M) (n : ℕ) :
    inducedCoordMap M ((stdd M).hom (a ⊗ₜ[Q → k] (v ⊗ₜ[Q → k] m : VtensObj M))) (n + 1)
      = (lengthProj k Q n a * arrowInclusion v) ⊗ₜ[Q → k] (m : M)
        - (lengthProj k Q (n + 1) a) ⊗ₜ[Q → k]
            (arrowInclusion v • (m : M) : restrictObj M) := by
  rw [stdd_tmul, map_sub, Finsupp.sub_apply, inducedCoordMap_tmul, inducedCoordMap_tmul,
    lengthProj_mul_arrowInclusion]

/-- **Degree `0` of `d` on a generator carries no cons-splitting term.** At the bottom degree only
the lower term survives (`lengthProj 0` of a positive-length product being handled by the shift):
`d(a ⊗ v ⊗ m)_0 = −(lengthProj 0 a) ⊗ v·m`, since `a·v` has no length-`0` component. -/
theorem inducedCoordMap_stdd_tmul_zero (a : PathAlgebra k Q) (v : ArrowTgt k Q)
    (m : restrictObj M) :
    inducedCoordMap M ((stdd M).hom (a ⊗ₜ[Q → k] (v ⊗ₜ[Q → k] m : VtensObj M))) 0
      = - (lengthProj k Q 0 a) ⊗ₜ[Q → k] (arrowInclusion v • (m : M) : restrictObj M) := by
  rw [stdd_tmul, map_sub, Finsupp.sub_apply, inducedCoordMap_tmul, inducedCoordMap_tmul,
    lengthProj_mul_arrowInclusion_zero, TensorProduct.zero_tmul, zero_sub]

end Induced

end Etingof.PathAlgebra
