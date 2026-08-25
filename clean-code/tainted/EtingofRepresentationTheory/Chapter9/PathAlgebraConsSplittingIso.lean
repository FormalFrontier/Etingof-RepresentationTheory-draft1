import EtingofRepresentationTheory.Chapter9.PathAlgebraConsSplitting
import EtingofRepresentationTheory.Chapter9.PathAlgebraInducedGrading

set_option backward.isDefEq.respectTransparency false

/-!
# The cons-splitting degree shift for `A = PathAlgebra k Q`

In the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i)), write `A := PathAlgebra k Q`, `S := Q → k` the vertex
subalgebra, `V` the arrow bimodule (`Chapter9/PathAlgebraArrowBimodule.lean`). This file records
the length-grading behaviour of right multiplication by an arrow and packages the resulting
degree-`(+1)` shift of the boundary map `d` of the standard short complex
(`Chapter9/PathAlgebraStandardComplex.lean`), the noncommutative analogue of the `coeff_X_mul`
shift used by `koszulSES_shortExact` (`Chapter9/Example9_4_4.lean`).

The combinatorial core underlying the *cons-splitting isomorphism* `A_n ⊗_S V ≅ A_{n+1}` is in
`Chapter9/PathAlgebraConsSplitting.lean` (`exists_ofPath_mul_arrowElt`, `ofPath_mul_arrowElt_inj`).
Here we add the analytic companion: multiplying a homogeneous degree-`n` element on the right by an
arrow (`arrowInclusion v`, degree `1`) lands exactly in degree `n + 1`
(`lengthProj_mul_arrowInclusion`). This is the seed of both

* `Mono (stdd M)`: the degree-`(N+1)` component of `d(ξ)` is the cons-splitting applied to the
  top component `ξ_N`, and
* the bundled `S`-bimodule isomorphism `A_n ⊗_S V ≅ A_{n+1}`,

both consumed by `standardResolution_shortExact`.
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
of `d(a ⊗ v ⊗ m) = a·v ⊗ m − a ⊗ v·m` splits into the cons-splitting term
`(lengthProj n a · v) ⊗ m` (the top half, using `lengthProj_mul_arrowInclusion`) and the lower
term `−(lengthProj (n+1) a) ⊗ v·m`. This is the noncommutative analogue of the `coeff_X_mul` shift
in `koszulSES_shortExact`, and the seed of the top-degree `Mono (stdd M)` argument. -/

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

/-! ## The two half-maps `Φ, Ψ` of the boundary `d` and the coordinate shift relation

The boundary `d = stdd M` splits as a difference `Φ − Ψ` of `A`-linear maps
`A ⊗_S (V ⊗_S M) → A ⊗_S M`,
```
Φ (a ⊗ v ⊗ m) = (a · v) ⊗ m,      Ψ (a ⊗ v ⊗ m) = a ⊗ (v · m),
```
built exactly like `stdd` itself (`homEquivSymm` of the two halves `stdδΦ`, `stdδΨ` of `stdδ`). The
degree-`(n+1)` coordinate of `d(ξ)` then splits, for **all** `ξ` (not just pure generators), as
```
inducedCoordMap M (d ξ) (n+1) = Φ (ξ_n) − Ψ (ξ_{n+1}),
```
where `ξ_n := inducedCoordMapGen (V ⊗_S M) ξ n` is the degree-`n` graded component. This is the
noncommutative analogue of the `hshift_gen` relation in `koszulSES_shortExact`
(`Chapter9/Example9_4_4.lean`): the `Φ` term carries the length shift `n → n+1` (right
multiplication by an arrow, via `lengthProj_mul_arrowInclusion`), the `Ψ` term stays in degree
`n+1`. It is what `standardResolution_shortExact` plugs into for both `Mono (stdd M)`
(top-degree base case) and middle exactness (downward telescoping). -/

/-- The `S`-balanced additive bilinear map underlying the **top half** `Φ` of `d`:
`(v, m) ↦ v ⊗ m` (i.e. `arrowInclusion v ⊗ m`), landing in the restriction of `A ⊗_S M`. -/
noncomputable def stdδΦBilin :
    ArrowTgt k Q →+ restrictObj M →+ (restrictScalars (vertexEmbedding k Q)).obj
      (inducedRestrictObj M) where
  toFun v :=
    { toFun := fun m => arrowInclusion v ⊗ₜ[Q → k] m
      map_zero' := by simp
      map_add' := fun m m' => by rw [TensorProduct.tmul_add] }
  map_zero' := by ext m; simp
  map_add' v w := by
    ext m
    simp only [map_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk, TensorProduct.add_tmul,
      AddMonoidHom.add_apply]

theorem stdδΦBilin_apply (v : ArrowTgt k Q) (m : restrictObj M) :
    stdδΦBilin M v m = arrowInclusion v ⊗ₜ[Q → k] m := rfl

theorem stdδΦBilin_balanced (s : Q → k) (v : ArrowTgt k Q) (m : restrictObj M) :
    stdδΦBilin M (s • v) m = stdδΦBilin M v (s • m) := by
  rw [stdδΦBilin_apply, stdδΦBilin_apply]
  have hv : arrowInclusion (s • v : ArrowTgt k Q)
      = arrowInclusion v * vertexEmbedding k Q s := arrowInclusion_wSMul_tgt s v
  rw [hv, ← vertex_smul_def, TensorProduct.smul_tmul]

/-- The additive map `V ⊗_S M → restrict (A ⊗_S M)` underlying `Φ`, `v ⊗ m ↦ v ⊗ m`. -/
noncomputable def stdδΦAddHom :
    VtensCarrier M →+ (restrictScalars (vertexEmbedding k Q)).obj (inducedRestrictObj M) :=
  TensorProduct.liftAddHom (stdδΦBilin M) (stdδΦBilin_balanced M)

@[simp] theorem stdδΦAddHom_tmul (v : ArrowTgt k Q) (m : restrictObj M) :
    stdδΦAddHom M (v ⊗ₜ[Q → k] m) = arrowInclusion v ⊗ₜ[Q → k] m := rfl

/-- **The top-half boundary datum** `δΦ : V ⊗_S M → restrict (A ⊗_S M)`, `δΦ (v ⊗ m) = v ⊗ m`.
Source-`S`-linear by the same computation as the first term of `stdδ`. -/
noncomputable def stdδΦ :
    VtensObj M ⟶ (restrictScalars (vertexEmbedding k Q)).obj (inducedRestrictObj M) :=
  ModuleCat.ofHom (X := VtensObj M)
    (Y := (restrictScalars (vertexEmbedding k Q)).obj (inducedRestrictObj M))
    { toFun := fun x => stdδΦAddHom M x
      map_add' := fun x y => (stdδΦAddHom M).map_add x y
      map_smul' := fun s x => by
        change (stdδΦAddHom M (s • x) : inducedRestrictObj M)
          = vertexEmbedding k Q s • (stdδΦAddHom M x : inducedRestrictObj M)
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul v m =>
            rw [vtens_smul_def, vtens_smul_tmul, stdδΦAddHom_tmul, stdδΦAddHom_tmul]
            simp only [srcHom_apply, arrowInclusion_wSMul_src]
            rw [TensorProduct.smul_tmul', smul_eq_mul]
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add] }

@[simp] theorem stdδΦ_tmul (v : ArrowTgt k Q) (m : restrictObj M) :
    (stdδΦ M).hom (v ⊗ₜ[Q → k] m) = arrowInclusion v ⊗ₜ[Q → k] m := by
  change stdδΦAddHom M (v ⊗ₜ[Q → k] m) = _
  rw [stdδΦAddHom_tmul]

/-- The `S`-balanced additive bilinear map underlying the **lower half** `Ψ` of `d`:
`(v, m) ↦ 1 ⊗ (v · m)`, landing in the restriction of `A ⊗_S M`. -/
noncomputable def stdδΨBilin :
    ArrowTgt k Q →+ restrictObj M →+ (restrictScalars (vertexEmbedding k Q)).obj
      (inducedRestrictObj M) where
  toFun v :=
    { toFun := fun m =>
        (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (arrowInclusion v • (m : M) : restrictObj M)
      map_zero' := by simp
      map_add' := fun m m' => by simp only [smul_add, TensorProduct.tmul_add] }
  map_zero' := by ext m; simp
  map_add' v w := by
    ext m
    simp only [map_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_smul, TensorProduct.tmul_add,
      AddMonoidHom.add_apply]

theorem stdδΨBilin_apply (v : ArrowTgt k Q) (m : restrictObj M) :
    stdδΨBilin M v m
      = (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (arrowInclusion v • (m : M) : restrictObj M) := rfl

theorem stdδΨBilin_balanced (s : Q → k) (v : ArrowTgt k Q) (m : restrictObj M) :
    stdδΨBilin M (s • v) m = stdδΨBilin M v (s • m) := by
  rw [stdδΨBilin_apply, stdδΨBilin_apply]
  have hv : arrowInclusion (s • v : ArrowTgt k Q)
      = arrowInclusion v * vertexEmbedding k Q s := arrowInclusion_wSMul_tgt s v
  have e2 : (arrowInclusion v * vertexEmbedding k Q s) • (m : M)
      = arrowInclusion v • ((s : Q → k) • m : restrictObj M) := by
    rw [mul_smul]; rfl
  rw [hv, e2]

/-- The additive map `V ⊗_S M → restrict (A ⊗_S M)` underlying `Ψ`, `v ⊗ m ↦ 1 ⊗ (v · m)`. -/
noncomputable def stdδΨAddHom :
    VtensCarrier M →+ (restrictScalars (vertexEmbedding k Q)).obj (inducedRestrictObj M) :=
  TensorProduct.liftAddHom (stdδΨBilin M) (stdδΨBilin_balanced M)

@[simp] theorem stdδΨAddHom_tmul (v : ArrowTgt k Q) (m : restrictObj M) :
    stdδΨAddHom M (v ⊗ₜ[Q → k] m)
      = (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (arrowInclusion v • (m : M) : restrictObj M) := rfl

/-- **The lower-half boundary datum** `δΨ : V ⊗_S M → restrict (A ⊗_S M)`, `δΨ (v ⊗ m) = 1 ⊗ v·m`.
Source-`S`-linear by the same computation as the second term of `stdδ`. -/
noncomputable def stdδΨ :
    VtensObj M ⟶ (restrictScalars (vertexEmbedding k Q)).obj (inducedRestrictObj M) :=
  ModuleCat.ofHom (X := VtensObj M)
    (Y := (restrictScalars (vertexEmbedding k Q)).obj (inducedRestrictObj M))
    { toFun := fun x => stdδΨAddHom M x
      map_add' := fun x y => (stdδΨAddHom M).map_add x y
      map_smul' := fun s x => by
        change (stdδΨAddHom M (s • x) : inducedRestrictObj M)
          = vertexEmbedding k Q s • (stdδΨAddHom M x : inducedRestrictObj M)
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul v m =>
            rw [vtens_smul_def, vtens_smul_tmul, stdδΨAddHom_tmul, stdδΨAddHom_tmul]
            simp only [srcHom_apply, arrowInclusion_wSMul_src]
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← one_tmul_smul]
            congr 1
            exact mul_smul _ _ _
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add] }

@[simp] theorem stdδΨ_tmul (v : ArrowTgt k Q) (m : restrictObj M) :
    (stdδΨ M).hom (v ⊗ₜ[Q → k] m)
      = (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (arrowInclusion v • (m : M) : restrictObj M) := by
  change stdδΨAddHom M (v ⊗ₜ[Q → k] m) = _
  rw [stdδΨAddHom_tmul]

/-- **The top half of `d`** `Φ : A ⊗_S (V ⊗_S M) → A ⊗_S M`, `Φ (a ⊗ v ⊗ m) = (a·v) ⊗ m`, the
`A`-linear extension of `δΦ`. The cons-splitting `A_n ⊗_S V ≅ A_{n+1}` tensored with `M`. -/
noncomputable def stdΦ : inducedVtensObj M ⟶ inducedRestrictObj M :=
  homEquivSymm (stdδΦ M)

@[simp] theorem stdΦ_tmul (a : PathAlgebra k Q) (v : ArrowTgt k Q) (m : restrictObj M) :
    (stdΦ M).hom (a ⊗ₜ[Q → k] (v ⊗ₜ[Q → k] m : VtensObj M))
      = (a * arrowInclusion v) ⊗ₜ[Q → k] (m : M) := by
  rw [stdΦ, homEquivSymm_tmul, stdδΦ_tmul, TensorProduct.smul_tmul', smul_eq_mul]

/-- **The lower half of `d`** `Ψ : A ⊗_S (V ⊗_S M) → A ⊗_S M`, `Ψ (a ⊗ v ⊗ m) = a ⊗ (v·m)`, the
`A`-linear extension of `δΨ`. -/
noncomputable def stdΨ : inducedVtensObj M ⟶ inducedRestrictObj M :=
  homEquivSymm (stdδΨ M)

@[simp] theorem stdΨ_tmul (a : PathAlgebra k Q) (v : ArrowTgt k Q) (m : restrictObj M) :
    (stdΨ M).hom (a ⊗ₜ[Q → k] (v ⊗ₜ[Q → k] m : VtensObj M))
      = a ⊗ₜ[Q → k] (arrowInclusion v • (m : M) : restrictObj M) := by
  rw [stdΨ, homEquivSymm_tmul, stdδΨ_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- **`d = Φ − Ψ` pointwise.** The boundary map is the difference of its two half-maps. -/
theorem stdd_hom_eq_sub (x : inducedVtensObj M) :
    (stdd M).hom x = (stdΦ M).hom x - (stdΨ M).hom x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v m => rw [stdd_tmul, stdΦ_tmul, stdΨ_tmul]
      | add y z hy hz =>
          rw [TensorProduct.tmul_add, map_add, map_add, map_add, hy, hz]; abel
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

/-- **The coordinate shift relation for `d`, all `ξ`.** The degree-`(n+1)` component of `d(ξ)`
splits as `Φ (ξ_n) − Ψ (ξ_{n+1})`, where `ξ_j = inducedCoordMapGen (V ⊗_S M) ξ j` is the degree-`j`
graded component. The noncommutative `hshift_gen`: the `Φ` term carries the length shift `n → n+1`,
the `Ψ` term stays in degree `n+1`. Reduces on pure generators to `inducedCoordMap_stdd_tmul_succ`.
Consumed by `standardResolution_shortExact` for `Mono (stdd M)` and middle exactness. -/
theorem inducedCoordMap_stdd_shift (s : inducedVtensObj M) (n : ℕ) :
    inducedCoordMap M ((stdd M).hom s) (n + 1)
      = (stdΦ M).hom (inducedCoordMapGen (VtensObj M) s n)
        - (stdΨ M).hom (inducedCoordMapGen (VtensObj M) s (n + 1)) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v m =>
          rw [inducedCoordMap_stdd_tmul_succ, inducedCoordMapGen_tmul, inducedCoordMapGen_tmul,
            stdΦ_tmul, stdΨ_tmul]
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hy, hz]; abel
  | add s t hs ht =>
      simp only [map_add, Finsupp.add_apply, hs, ht]; abel

/-- **The degree-`0` coordinate of `d`, all `ξ`.** At the bottom degree the `Φ` term vanishes
(right multiplication by an arrow has no length-`0` component), leaving `−Ψ (ξ_0)`. The
noncommutative analogue of `hshift_zero` in `koszulSES_shortExact`. -/
theorem inducedCoordMap_stdd_shift_zero (s : inducedVtensObj M) :
    inducedCoordMap M ((stdd M).hom s) 0
      = - (stdΨ M).hom (inducedCoordMapGen (VtensObj M) s 0) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v m =>
          rw [inducedCoordMap_stdd_tmul_zero, inducedCoordMapGen_tmul, stdΨ_tmul]
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hy, hz]; abel
  | add s t hs ht =>
      simp only [map_add, Finsupp.add_apply, hs, ht]; abel

/-! ## Graded surjectivity of `Φ` (the cons-preimage of the top component)

The cons-splitting `A_n ⊗_S V ≅ A_{n+1}`, tensored with `M`, says that `Φ` restricts to an
isomorphism from the degree-`n` part of `A ⊗_S (V ⊗_S M)` onto the degree-`(n+1)` part of
`A ⊗_S M`. The surjectivity half of that graded iso is the piece consumed by
`standardResolution_shortExact`: the downward middle-exactness telescoping needs, for each
`y : A ⊗_S M` and each `n`, a degree-`n` preimage `η` of the degree-`(n+1)` component of `y` under
`Φ`. This is the noncommutative analogue of the cons-preimage `coordMapCHInv` in
`koszulSES_shortExact` (`Chapter9/Example9_4_4.lean`), built here directly from the combinatorial
core `exists_ofPath_mul_arrowElt` (`Chapter9/PathAlgebraConsSplitting.lean`) rather than from an
abstract graded-piece isomorphism.

Because `Φ (a ⊗ v ⊗ m) = (a·v) ⊗ m` raises the length degree by one
(`lengthProj_mul_arrowInclusion`), the produced `η` is homogeneous of degree `n`
(`inducedCoordMapGen (VtensObj M) η n = η` and vanishes in every other degree), so its degree-shift
coordinate `inducedCoordMap_stdd_shift` collapses to `Φ η` at degree `n+1` and to `0` above. -/

/-- **Single-path cons-preimage.** For a basis path `x` of length `n + 1` and any `m`, the pure
tensor `(x, m)` of `A ⊗_S M` is `Φ η` for an `η` homogeneous of degree `n`: split `x = p·e` into its
length-`n` initial path `p` and final arrow `e` (`exists_ofPath_mul_arrowElt`) and take
`η = (c • p) ⊗ (e ⊗ m)`. The basis-level seed of `exists_stdΦ_preimage_topDegree`. -/
theorem exists_stdΦ_preimage_single_tmul (x : QuiverPathIndex Q) (c : k) {n : ℕ}
    (hx : pathLen x = n + 1) (m : restrictObj M) :
    ∃ η : inducedVtensObj M,
      inducedCoordMapGen (VtensObj M) η n = η ∧
      (∀ j, j ≠ n → inducedCoordMapGen (VtensObj M) η j = 0) ∧
      (stdΦ M).hom η
        = ((Finsupp.single x c : PathAlgebra k Q) ⊗ₜ[Q → k] (m : M) : inducedCarrier M) := by
  obtain ⟨a, cc, q⟩ := x
  rw [pathLen_mk] at hx
  obtain ⟨b, p, e, hcomp, hlen⟩ := exists_ofPath_mul_arrowElt (k := k) q hx
  have hlp : lengthProj k Q n (ofPath (⟨a, b, p⟩ : QuiverPathIndex Q))
      = ofPath (⟨a, b, p⟩ : QuiverPathIndex Q) := by
    rw [ofPath, lengthProj_single, pathLen_mk, hlen, if_pos rfl]
  have hlp0 : ∀ j, j ≠ n →
      lengthProj k Q j (ofPath (⟨a, b, p⟩ : QuiverPathIndex Q)) = 0 := by
    intro j hj
    rw [ofPath, lengthProj_single, pathLen_mk, hlen, if_neg (fun h => hj h.symm)]
  refine ⟨(c • ofPath (⟨a, b, p⟩ : QuiverPathIndex Q)) ⊗ₜ[Q → k]
      ((Finsupp.single (⟨b, cc, e⟩ : ArrowIndex Q) 1 : ArrowTgt k Q)
        ⊗ₜ[Q → k] m : VtensObj M), ?_, ?_, ?_⟩
  · rw [inducedCoordMapGen_tmul, map_smul, hlp]
  · intro j hj
    rw [inducedCoordMapGen_tmul, map_smul, hlp0 j hj, smul_zero, TensorProduct.zero_tmul]
  · have hmul : (c • ofPath (⟨a, b, p⟩ : QuiverPathIndex Q))
        * arrowInclusion (Finsupp.single (⟨b, cc, e⟩ : ArrowIndex Q) 1 : ArrowTgt k Q)
        = (Finsupp.single (⟨a, cc, q⟩ : QuiverPathIndex Q) c : PathAlgebra k Q) := by
      rw [arrowInclusion_single, one_smul, smul_mul_assoc, ← hcomp, ofPath, Finsupp.smul_single,
        smul_eq_mul, mul_one]
    rw [stdΦ_tmul, hmul]

/-- **Graded surjectivity of `Φ` onto the top component (cons-preimage).** For every `y : A ⊗_S M`
and every `n`, the degree-`(n+1)` homogeneous component `inducedCoordMap M y (n+1)` is `Φ η` for a
degree-`n`-homogeneous `η : A ⊗_S (V ⊗_S M)`. This is the surjectivity half of the cons-splitting
`A_n ⊗_S V ≅ A_{n+1}` (tensored with `M`), used by
`standardResolution_shortExact` for the middle-exactness downward telescoping.
Reduces, via additivity, to the single-path case `exists_stdΦ_preimage_single_tmul`. -/
theorem exists_stdΦ_preimage_topDegree (y : inducedRestrictObj M) (n : ℕ) :
    ∃ η : inducedVtensObj M,
      inducedCoordMapGen (VtensObj M) η n = η ∧
      (∀ j, j ≠ n → inducedCoordMapGen (VtensObj M) η j = 0) ∧
      (stdΦ M).hom η = inducedCoordMap M y (n + 1) := by
  -- Local abbreviation for the "reachable by a degree-`n` preimage" predicate. Kept out of the
  -- proof goal (only used to type the closure lemmas) so tensor-defeq rewrites stay well-typed.
  let G : inducedCarrier M → Prop := fun z =>
    ∃ η : inducedVtensObj M,
      inducedCoordMapGen (VtensObj M) η n = η ∧
      (∀ j, j ≠ n → inducedCoordMapGen (VtensObj M) η j = 0) ∧
      (stdΦ M).hom η = z
  have hzero : G 0 := ⟨0, by simp, by simp, by simp⟩
  have hadd : ∀ z₁ z₂ : inducedCarrier M, G z₁ → G z₂ → G (z₁ + z₂) := by
    rintro z₁ z₂ ⟨η₁, h1n, h1j, h1⟩ ⟨η₂, h2n, h2j, h2⟩
    refine ⟨η₁ + η₂, ?_, ?_, ?_⟩
    · rw [map_add, Finsupp.add_apply, h1n, h2n]
    · intro j hj; rw [map_add, Finsupp.add_apply, h1j j hj, h2j j hj, add_zero]
    · rw [map_add, h1, h2]
  -- The homogeneous-degree-`(n+1)` reduction: it suffices to reach every `A_{n+1}`-pure tensor.
  suffices H : ∀ (a : PathAlgebra k Q) (m : restrictObj M),
      G (lengthProj k Q (n + 1) a ⊗ₜ[Q → k] (m : M)) by
    induction y using TensorProduct.induction_on with
    | zero =>
        have h0 : inducedCoordMap M (0 : inducedRestrictObj M) (n + 1) = 0 := by simp
        rw [h0]; exact hzero
    | tmul a m => rw [inducedCoordMap_tmul]; exact H a m
    | add y₁ y₂ hy₁ hy₂ =>
        have hsum : inducedCoordMap M (y₁ + y₂) (n + 1)
            = inducedCoordMap M y₁ (n + 1) + inducedCoordMap M y₂ (n + 1) := by
          rw [LinearMap.map_add, Finsupp.add_apply]
        rw [hsum]; exact hadd _ _ hy₁ hy₂
  intro a m
  induction a using Finsupp.induction_linear with
  | zero => rw [map_zero, TensorProduct.zero_tmul]; exact hzero
  | add f g hf hg => rw [map_add, TensorProduct.add_tmul]; exact hadd _ _ hf hg
  | single x c =>
      rw [lengthProj_single]
      split_ifs with hx
      · exact exists_stdΦ_preimage_single_tmul M x c hx m
      · rw [TensorProduct.zero_tmul]; exact hzero

end Induced

end Etingof.PathAlgebra
