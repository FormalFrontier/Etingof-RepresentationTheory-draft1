import EtingofRepresentationTheory.Chapter9.PathAlgebraLengthGrading
import EtingofRepresentationTheory.Chapter9.PathAlgebraStandardComplex
import Mathlib.LinearAlgebra.DirectSum.Finsupp

set_option backward.isDefEq.respectTransparency false

/-!
# The length grading of the induced module `A ⊗_S M`

In the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i)), write `A := PathAlgebra k Q`, `S := Q → k` the vertex
subalgebra (`f := vertexEmbedding : S →+* A`). The length grading of `A`
(`Chapter9/PathAlgebraLengthGrading.lean`) is transported to the induced module
`A ⊗_S M` (`inducedRestrictObj M`), producing a coordinate map

```
inducedCoordMap M : A ⊗_S M →ₗ[S] (ℕ →₀ A ⊗_S M)
```

injective with finite support, the noncommutative analogue of `coordMapCH`
(`Chapter9/KoszulHelpers.lean`) used by `koszulSES_shortExact`. The key point is that the
homogeneous decomposition `lengthGrading : A →ₗ (ℕ →₀ A)` is `S`-linear for the right
`S`-action `s • a = a * f s` that the tensor `A ⊗_S M` is formed over: right multiplication by
`f s` preserves path length (`lengthGrading_mul_vertexEmbedding`). Injectivity is inherited from
the left inverse `lengthTotalize` via `TensorProduct.map` and `TensorProduct.finsuppLeft`.

Template: `Chapter9/KoszulHelpers.lean` (`coordMapCH`, `coordMapCH_injective`) and its use in
`Chapter9/Example9_4_4.lean` (`koszulSES_shortExact`, `Mono d` via `finsupp_shift_eq_zero`).
-/

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace Etingof.PathAlgebra

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

/-! ## Right multiplication by a vertex idempotent preserves length -/

/-- Right multiplication of a basis path by a trivial-path idempotent `eᵢ`: the path survives when
`i` is its target, and is killed otherwise. The `ofPath`-level companion of
`compSingle_nil_right`. -/
theorem ofPath_mul_vertexIdem (i : Q) (x : QuiverPathIndex Q) :
    (ofPath x : PathAlgebra k Q) * ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q)
      = if x.2.1 = i then ofPath x else 0 := by
  obtain ⟨a, b, p⟩ := x
  rw [ofPath_mul_ofPath, compSingle_nil_right]
  split_ifs with h
  · rfl
  · rfl

/-- **Right vertex action inside `A`.** Right multiplication of a basis path by
`f s = vertexEmbedding s` scales it by the target coordinate `s (tgt)`: `p · f s = s(tgt p) • p`.
The general-path analogue of `arrowElt_mul_vertexEmbedding`. -/
theorem ofPath_mul_vertexEmbedding (x : QuiverPathIndex Q) (s : Q → k) :
    (ofPath x : PathAlgebra k Q) * vertexEmbedding k Q s = s x.2.1 • ofPath x := by
  have hsingle : ∀ i : Q, (Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) (s i)
        : PathAlgebra k Q) = s i • (ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q)) := by
    intro i; rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [vertexEmbedding_apply, Finset.sum_congr rfl fun i _ => hsingle i, Finset.mul_sum]
  have hterm : ∀ i : Q,
      (ofPath x : PathAlgebra k Q) * (s i • ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q))
        = if x.2.1 = i then s i • ofPath (k := k) x else 0 := by
    intro i
    rw [mul_smul', ofPath_mul_vertexIdem]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq Finset.univ x.2.1,
    if_pos (Finset.mem_univ _)]

/-- Right multiplication by `f s = vertexEmbedding s` scales a basis path by its target
coordinate, so the product `p · f s` stays in the same length degree. -/
theorem single_mul_vertexEmbedding (x : QuiverPathIndex Q) (c : k) (s : Q → k) :
    (@HMul.hMul (PathAlgebra k Q) (PathAlgebra k Q) (PathAlgebra k Q) _
        (Finsupp.single x c) (vertexEmbedding k Q s))
      = s x.2.1 • (Finsupp.single x c : PathAlgebra k Q) := by
  rw [show (Finsupp.single x c : PathAlgebra k Q) = c • ofPath x from by
      rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one],
    smul_mul, ofPath_mul_vertexEmbedding, smul_comm]

/-- **Right multiplication by `f s` preserves the length grading, coordinate-wise.** The degree-`n`
homogeneous component of `a · f s` is `(degree-n component of a) · f s`. -/
theorem lengthProj_mul_vertexEmbedding (n : ℕ) (a : PathAlgebra k Q) (s : Q → k) :
    lengthProj k Q n ((a * vertexEmbedding k Q s : PathAlgebra k Q))
      = lengthProj k Q n a * vertexEmbedding k Q s := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul, map_add, map_add, add_mul, hf, hg]
  | single x c =>
    rw [single_mul_vertexEmbedding, map_smul, lengthProj_single]
    split_ifs with h
    · exact (single_mul_vertexEmbedding x c s).symm
    · rw [smul_zero, zero_mul]

/-- **The length grading is `S`-linear for the right action.** Right multiplication by `f s`
preserves length degree, so `lengthGrading (a · f s)` is the pointwise right multiplication of
`lengthGrading a` by `f s` (`s • F` for the induced `S`-action on `ℕ →₀ A`). -/
theorem lengthGrading_mul_vertexEmbedding (a : PathAlgebra k Q) (s : Q → k) :
    lengthGrading k Q ((a * vertexEmbedding k Q s : PathAlgebra k Q))
      = s • lengthGrading k Q a := by
  ext n
  rw [Finsupp.smul_apply, ← lengthProj_apply, ← lengthProj_apply, vertex_smul_def,
    lengthProj_mul_vertexEmbedding]

/-! ## The `S`-linear grading and reassembly maps -/

variable (k Q) in
/-- **The length grading as an `S`-linear map** (right action `s • a = a * f s`). Same underlying
function as `lengthGrading`, upgraded to `(Q → k)`-linearity via
`lengthGrading_mul_vertexEmbedding`. This is the map tensored with `M` to build the coordinate map
on `A ⊗_S M`. -/
noncomputable def lengthGradingS : PathAlgebra k Q →ₗ[Q → k] (ℕ →₀ PathAlgebra k Q) where
  toFun := lengthGrading k Q
  map_add' := map_add _
  map_smul' s a := by
    change lengthGrading k Q (s • a) = s • lengthGrading k Q a
    rw [vertex_smul_def, lengthGrading_mul_vertexEmbedding]

@[simp] theorem lengthGradingS_apply (a : PathAlgebra k Q) :
    lengthGradingS k Q a = lengthGrading k Q a := rfl

variable (k Q) in
/-- **The reassembly map as an `S`-linear map**, left inverse of `lengthGradingS`. Same underlying
function as `lengthTotalize`. -/
noncomputable def lengthTotalizeS : (ℕ →₀ PathAlgebra k Q) →ₗ[Q → k] PathAlgebra k Q where
  toFun := lengthTotalize k Q
  map_add' := map_add _
  map_smul' s F := by
    change lengthTotalize k Q (s • F) = s • lengthTotalize k Q F
    induction F using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [smul_add, map_add, map_add, hf, hg, smul_add]
    | single n a => rw [Finsupp.smul_single, lengthTotalize_single, lengthTotalize_single]

@[simp] theorem lengthTotalizeS_apply (F : ℕ →₀ PathAlgebra k Q) :
    lengthTotalizeS k Q F = lengthTotalize k Q F := rfl

/-- `lengthTotalizeS` is a left inverse of `lengthGradingS` (the `S`-linear packaging of
`lengthTotalize_lengthGrading`). -/
theorem lengthTotalizeS_comp_lengthGradingS :
    (lengthTotalizeS k Q).comp (lengthGradingS k Q) = LinearMap.id := by
  ext a
  simp only [LinearMap.comp_apply, lengthGradingS_apply, lengthTotalizeS_apply,
    lengthTotalize_lengthGrading, LinearMap.id_coe, id_eq]

/-! ## The coordinate map on `A ⊗_S M` -/

variable (M : ModuleCat.{u + 1} (PathAlgebra k Q))

/-- Underlying carrier of the induced module `A ⊗_S M`, as the raw tensor product over `S`. This
is definitionally `↑(inducedRestrictObj M)`, but exposes the canonical `Module (Q → k)` structure
of the tensor (the ModuleCat coercion only registers the `A`-action), over which the coordinate
map is `S`-linear. -/
abbrev inducedCarrier : Type (u + 1) :=
  TensorProduct (Q → k) (PathAlgebra k Q) (restrictObj M)

/-- **The length-graded coordinate map on `A ⊗_S M`.** The `S`-linear map
`A ⊗_S M →ₗ (ℕ →₀ A ⊗_S M)` sending `a ⊗ m` to `n ↦ (lengthProj n a) ⊗ m`, obtained by tensoring
the homogeneous decomposition `lengthGradingS` with `M` and commuting the finite support past the
tensor (`TensorProduct.finsuppLeft`). The noncommutative analogue of `coordMapCH`. -/
noncomputable def inducedCoordMap :
    inducedCarrier M →ₗ[Q → k] (ℕ →₀ inducedCarrier M) :=
  (TensorProduct.finsuppLeft (Q → k) (Q → k) (PathAlgebra k Q) (restrictObj M) ℕ).toLinearMap.comp
    (TensorProduct.map (lengthGradingS k Q) LinearMap.id)

@[simp] theorem inducedCoordMap_tmul (a : PathAlgebra k Q) (m : restrictObj M) (n : ℕ) :
    inducedCoordMap M (a ⊗ₜ[Q → k] m) n
      = (lengthProj k Q n a) ⊗ₜ[Q → k] (m : M) := by
  simp only [inducedCoordMap, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, lengthGradingS_apply, TensorProduct.finsuppLeft_apply_tmul_apply,
    lengthProj_apply]

/-- **Injectivity of the coordinate map.** Inherited from the left inverse `lengthTotalizeS` of
`lengthGradingS` (preserved by `TensorProduct.map`) and the bijectivity of
`TensorProduct.finsuppLeft`. The analogue of `coordMapCH_injective`. -/
theorem inducedCoordMap_injective : Function.Injective (inducedCoordMap M) := by
  have hleft : ∀ x : inducedCarrier M,
      (TensorProduct.map (lengthTotalizeS k Q) (LinearMap.id (R := Q → k) (M := restrictObj M)))
        (TensorProduct.map (lengthGradingS k Q) LinearMap.id x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, lengthTotalizeS_comp_lengthGradingS,
      LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
  intro x y hxy
  refine Function.LeftInverse.injective hleft ?_
  exact (TensorProduct.finsuppLeft (Q → k) (Q → k) (PathAlgebra k Q) (restrictObj M) ℕ).injective
    hxy

end Etingof.PathAlgebra
