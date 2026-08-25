import EtingofRepresentationTheory.Chapter9.PathAlgebraArrowBimodule
import EtingofRepresentationTheory.Chapter9.PathAlgebraInduction

set_option backward.isDefEq.respectTransparency false

/-!
# The standard short complex of a path-algebra module

Part of the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i)). Write `A := PathAlgebra k Q`, `S := Q → k` the vertex
subalgebra (embedded by `f := vertexEmbedding : S →+* A`), `V` the arrow `S`-bimodule
(`Chapter9/PathAlgebraArrowBimodule.lean`), and let `A ⊗_S -` be the induction functor
(`Chapter9/PathAlgebraInduction.lean`). This file assembles, for a left `A`-module `M`, the
standard short complex
```
A ⊗_S (V ⊗_S M) →ᵈ A ⊗_S M →ᵉ M
```
with `d (a ⊗ v ⊗ m) = a·v ⊗ m − a ⊗ (v·m)` and `ε (a ⊗ m) = a·m`, proving `d ≫ ε = 0` and
`Epi ε`. Injectivity of `d` (`Mono d`, `stdd_mono`) and middle exactness `ker ε = im d`
(`standardComplex_exact`) are proved in `Chapter9/PathAlgebraStandardResolution.lean`, where
`standardResolution_shortExact` assembles the full `ShortExact`.

## The inner tensor `V ⊗_S M`

`V = ArrowIndex Q →₀ k` carries two commuting `S`-actions (`arrowSourceModule` /
`arrowTargetModule`), realized inside `A` as left / right multiplication by vertex idempotents
(`vertexEmbedding_mul_arrowElt` / `arrowElt_mul_vertexEmbedding`). The inner tensor `V ⊗_S M`
is formed over the target action (balanced against the restricted `S`-action on `M`), and
the surviving left `S`-module structure is the source action.

Both `S`-actions live on the single carrier `ArrowIndex Q →₀ k`, and the tensor product also has
its own canonical `S`-action, so registering the surviving source action naively would create a
diamond. We break it with type synonyms: `ArrowTgt` carries the target action (used to form the
tensor), and `VtensCarrier M` carries the source action (the surviving structure) as its `S`-module
instance, defined by hand via `TensorProduct.map (srcHom s) id` rather than the canonical tensor
action.
-/

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace Etingof.PathAlgebra

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

/-! ## `wSMul` arithmetic -/

omit [DecidableEq Q] [Fintype Q] in
theorem wSMul_add (wt : ArrowIndex Q → Q) (s : Q → k) (v w : ArrowIndex Q →₀ k) :
    wSMul k Q wt s (v + w) = wSMul k Q wt s v + wSMul k Q wt s w := by
  ext i; simp only [wSMul_apply, Finsupp.add_apply]; ring

omit [DecidableEq Q] [Fintype Q] in
theorem wSMul_add_scalar (wt : ArrowIndex Q → Q) (s t : Q → k) (v : ArrowIndex Q →₀ k) :
    wSMul k Q wt (s + t) v = wSMul k Q wt s v + wSMul k Q wt t v := by
  ext i; simp only [wSMul_apply, Finsupp.add_apply, Pi.add_apply]; ring

omit [DecidableEq Q] [Fintype Q] in
theorem wSMul_zero_scalar (wt : ArrowIndex Q → Q) (v : ArrowIndex Q →₀ k) :
    wSMul k Q wt 0 v = 0 := by
  ext i; simp

omit [DecidableEq Q] [Fintype Q] in
theorem wSMul_one_scalar (wt : ArrowIndex Q → Q) (v : ArrowIndex Q →₀ k) :
    wSMul k Q wt 1 v = v := by
  ext i; simp

omit [DecidableEq Q] [Fintype Q] in
theorem wSMul_mul_scalar (wt : ArrowIndex Q → Q) (s t : Q → k) (v : ArrowIndex Q →₀ k) :
    wSMul k Q wt (s * t) v = wSMul k Q wt s (wSMul k Q wt t v) := by
  ext i; simp only [wSMul_apply, Pi.mul_apply]; ring

omit [DecidableEq Q] [Fintype Q] in
theorem wSMul_zero_vec (wt : ArrowIndex Q → Q) (s : Q → k) :
    wSMul k Q wt s (0 : ArrowIndex Q →₀ k) = 0 := by
  ext i; simp

omit [DecidableEq Q] [Fintype Q] in
theorem wSMul_single (wt : ArrowIndex Q → Q) (s : Q → k) (x : ArrowIndex Q) (c : k) :
    wSMul k Q wt s (Finsupp.single x c) = Finsupp.single x (s (wt x) * c) := by
  classical
  ext i
  rw [wSMul_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

/-! ## Source / target scaling under `arrowInclusion` -/

/-- Scaling by the source action corresponds to left multiplication by `f s` inside `A`. -/
theorem arrowInclusion_wSMul_src (s : Q → k) (v : ArrowIndex Q →₀ k) :
    arrowInclusion (wSMul k Q ArrowIndex.src s v)
      = vertexEmbedding k Q s * arrowInclusion v := by
  induction v using Finsupp.induction_linear with
  | zero => simp [wSMul_zero_vec]
  | add v w hv hw => rw [wSMul_add, map_add, map_add, mul_add, hv, hw]
  | single x c =>
      rw [wSMul_single, arrowInclusion_single, arrowInclusion_single, mul_smul_comm,
        vertexEmbedding_mul_arrowElt, smul_smul, mul_comm c]

/-- Scaling by the target action corresponds to right multiplication by `f s` inside `A`. -/
theorem arrowInclusion_wSMul_tgt (s : Q → k) (v : ArrowIndex Q →₀ k) :
    arrowInclusion (wSMul k Q ArrowIndex.tgt s v)
      = arrowInclusion v * vertexEmbedding k Q s := by
  induction v using Finsupp.induction_linear with
  | zero => simp [wSMul_zero_vec]
  | add v w hv hw => rw [wSMul_add, map_add, map_add, add_mul, hv, hw]
  | single x c =>
      rw [wSMul_single, arrowInclusion_single, arrowInclusion_single, smul_mul_assoc,
        arrowElt_mul_vertexEmbedding, smul_smul, mul_comm c]

/-! ## The target-action type synonym `ArrowTgt` -/

variable (k Q) in
/-- The arrow bimodule carrier `V = ArrowIndex Q →₀ k`, with the target `S`-action registered
as its canonical `Module (Q → k)` structure. Used to form the inner tensor `V ⊗_S M`. -/
def ArrowTgt : Type (u + 1) := ArrowIndex Q →₀ k

noncomputable instance instAddCommGroupArrowTgt : AddCommGroup (ArrowTgt k Q) :=
  inferInstanceAs (AddCommGroup (ArrowIndex Q →₀ k))

noncomputable instance instModuleKArrowTgt : Module k (ArrowTgt k Q) :=
  inferInstanceAs (Module k (ArrowIndex Q →₀ k))

/-- The target `S`-action is the canonical `Module (Q → k)`-structure on `ArrowTgt`. -/
noncomputable instance instModuleArrowTgt : Module (Q → k) (ArrowTgt k Q) :=
  arrowTargetModule k Q

/-- The source-scaling endomorphism `v ↦ s ·_src v` of `V`, as a `(Q → k)`-linear map with
respect to the target action. `(Q → k)`-linearity is exactly the bimodule commutativity
`wSMul_comm`. This is the building block of the surviving source `S`-action on `V ⊗_S M`. -/
noncomputable def srcHom (s : Q → k) : ArrowTgt k Q →ₗ[Q → k] ArrowTgt k Q where
  toFun v := wSMul k Q ArrowIndex.src s v
  map_add' v w := wSMul_add _ _ _ _
  map_smul' t v := by
    change wSMul k Q ArrowIndex.src s (wSMul k Q ArrowIndex.tgt t v)
      = wSMul k Q ArrowIndex.tgt t (wSMul k Q ArrowIndex.src s v)
    exact wSMul_comm s t v

omit [DecidableEq Q] [Fintype Q] in
@[simp] theorem srcHom_apply (s : Q → k) (v : ArrowTgt k Q) :
    srcHom s v = wSMul k Q ArrowIndex.src s v := rfl

omit [DecidableEq Q] [Fintype Q] in
theorem srcHom_one : srcHom (1 : Q → k) = LinearMap.id := by
  ext v; simp [srcHom_apply, wSMul_one_scalar]

omit [DecidableEq Q] [Fintype Q] in
theorem srcHom_mul (s t : Q → k) : srcHom (s * t) = srcHom s ∘ₗ srcHom t := by
  ext v; simp [srcHom_apply, wSMul_mul_scalar]

omit [DecidableEq Q] [Fintype Q] in
theorem srcHom_add (s t : Q → k) : srcHom (s + t) = srcHom s + srcHom t := by
  ext v; simp [srcHom_apply, wSMul_add_scalar]

omit [DecidableEq Q] [Fintype Q] in
theorem srcHom_zero : srcHom (0 : Q → k) = 0 := by
  ext v; simp [srcHom_apply, wSMul_zero_scalar]

/-! ## The inner tensor `V ⊗_S M` with the surviving source action -/

variable (M : ModuleCat.{u + 1} (PathAlgebra k Q))

/-- The `S`-module `M` restricted along `f = vertexEmbedding`, over which the inner tensor is
balanced (target action of `V` against `f`-restriction of `M`). -/
noncomputable abbrev restrictObj : ModuleCat.{u + 1} (Q → k) :=
  (restrictScalars (vertexEmbedding k Q)).obj M

/-- Underlying carrier of `V ⊗_S M`: the tensor `ArrowTgt ⊗_{Q→k} M` (target-balanced). Its
`Module (Q → k)` instance is overridden to be the surviving source action. -/
def VtensCarrier : Type (u + 1) :=
  TensorProduct (Q → k) (ArrowTgt k Q) (restrictObj M)

noncomputable instance : AddCommGroup (VtensCarrier M) :=
  inferInstanceAs (AddCommGroup (TensorProduct (Q → k) (ArrowTgt k Q) (restrictObj M)))

/-- The surviving source `S`-action on `V ⊗_S M`: `s • (v ⊗ m) = (s ·_src v) ⊗ m`,
implemented as `TensorProduct.map (srcHom s) id`. Registered by hand (not the canonical tensor
action, which is the target action). -/
noncomputable instance instSMulVtens : SMul (Q → k) (VtensCarrier M) where
  smul s x := TensorProduct.map (srcHom s) LinearMap.id x

theorem vtens_smul_def (s : Q → k) (x : VtensCarrier M) :
    s • x = TensorProduct.map (srcHom s) LinearMap.id x := rfl

theorem vtens_smul_tmul (s : Q → k) (v : ArrowTgt k Q) (m : restrictObj M) :
    TensorProduct.map (srcHom s) LinearMap.id (v ⊗ₜ[Q → k] m : VtensCarrier M)
      = srcHom s v ⊗ₜ[Q → k] m := by
  rw [TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

noncomputable instance instModuleVtens : Module (Q → k) (VtensCarrier M) where
  one_smul x := by
    rw [vtens_smul_def, srcHom_one, TensorProduct.map_id, LinearMap.id_coe, id_eq]
  mul_smul s t x := by
    change TensorProduct.map (srcHom (s * t)) LinearMap.id x
      = TensorProduct.map (srcHom s) LinearMap.id (TensorProduct.map (srcHom t) LinearMap.id x)
    rw [srcHom_mul, ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]
  smul_zero s := by rw [vtens_smul_def, map_zero]
  smul_add s x y := by rw [vtens_smul_def, vtens_smul_def, vtens_smul_def, map_add]
  add_smul s t x := by
    rw [vtens_smul_def, vtens_smul_def, vtens_smul_def, srcHom_add, TensorProduct.map_add_left,
      LinearMap.add_apply]
  zero_smul x := by
    rw [vtens_smul_def, srcHom_zero, TensorProduct.map_zero_left, LinearMap.zero_apply]

/-- `V ⊗_S M` as an object of `ModuleCat (Q → k)`, carrying the source action. -/
noncomputable def VtensObj : ModuleCat.{u + 1} (Q → k) :=
  ModuleCat.of (Q → k) (VtensCarrier M)

/-! ## The multiplication map `ε` -/

/-- `A ⊗_S M` as an object of `ModuleCat A`. -/
noncomputable abbrev inducedRestrictObj : ModuleCat.{u + 1} (PathAlgebra k Q) :=
  inducedModule.obj (restrictObj M)

/-- `A ⊗_S (V ⊗_S M)` as an object of `ModuleCat A`. -/
noncomputable abbrev inducedVtensObj : ModuleCat.{u + 1} (PathAlgebra k Q) :=
  inducedModule.obj (VtensObj M)

/-- **The multiplication map** `ε : A ⊗_S M → M`; `ε (a ⊗ m) = a · m`. This is the counit of the
induction–restriction adjunction at `M` (see `stdε_eq_counit`), written directly as
`homEquivSymm (𝟙 _)`. -/
noncomputable def stdε : inducedRestrictObj M ⟶ M :=
  homEquivSymm (𝟙 (restrictObj M))

theorem stdε_eq_counit : stdε M = inducedRestrictAdj.counit.app M := by
  rw [stdε, ← Adjunction.homEquiv_symm_id]
  simp only [inducedRestrictAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

theorem stdε_tmul (a : PathAlgebra k Q) (m : restrictObj M) :
    (stdε M).hom (a ⊗ₜ[Q → k] m) = a • (m : M) := by
  rw [stdε, homEquivSymm_tmul]
  rfl

/-! ## The boundary map `d` -/

/-- The `S`-balanced additive bilinear map underlying `d`: `(v, m) ↦ v ⊗ m − 1 ⊗ (v · m)`
landing in the restriction of `A ⊗_S M`. -/
noncomputable def stdδBilin :
    ArrowTgt k Q →+ restrictObj M →+ (restrictScalars (vertexEmbedding k Q)).obj
      (inducedRestrictObj M) where
  toFun v :=
    { toFun := fun m => arrowInclusion v ⊗ₜ[Q → k] m
        - (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (arrowInclusion v • (m : M) : restrictObj M)
      map_zero' := by simp
      map_add' := fun m m' => by
        simp only [TensorProduct.tmul_add, smul_add]
        abel }
  map_zero' := by ext m; simp
  map_add' v w := by
    ext m
    simp only [map_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_smul, TensorProduct.add_tmul,
      TensorProduct.tmul_add, AddMonoidHom.add_apply]
    abel

theorem stdδBilin_apply (v : ArrowTgt k Q) (m : restrictObj M) :
    stdδBilin M v m = arrowInclusion v ⊗ₜ[Q → k] m
      - (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (arrowInclusion v • (m : M) : restrictObj M) := rfl

theorem stdδBilin_balanced (s : Q → k) (v : ArrowTgt k Q) (m : restrictObj M) :
    stdδBilin M (s • v) m = stdδBilin M v (s • m) := by
  -- `s • v` is the target action `wSMul tgt s v`, `s • m = f s • m`.
  rw [stdδBilin_apply, stdδBilin_apply]
  have hv : arrowInclusion (s • v : ArrowTgt k Q)
      = arrowInclusion v * vertexEmbedding k Q s := arrowInclusion_wSMul_tgt s v
  rw [hv]
  -- first terms: (incl v * f s) ⊗ m = incl v ⊗ (s • m)
  have e1 : (arrowInclusion v * vertexEmbedding k Q s) ⊗ₜ[Q → k] m
      = arrowInclusion v ⊗ₜ[Q → k] ((s : Q → k) • m : restrictObj M) := by
    rw [← vertex_smul_def, TensorProduct.smul_tmul]
  -- second terms: 1 ⊗ ((incl v * f s) • m) = 1 ⊗ (incl v • (s • m))
  have e2 : (arrowInclusion v * vertexEmbedding k Q s) • (m : M)
      = arrowInclusion v • ((s : Q → k) • m : restrictObj M) := by
    rw [mul_smul]; rfl
  rw [e1, e2]

/-- The additive map `V ⊗_S M → restrict (A ⊗_S M)` underlying `d`. -/
noncomputable def stdδAddHom :
    VtensCarrier M →+ (restrictScalars (vertexEmbedding k Q)).obj (inducedRestrictObj M) :=
  TensorProduct.liftAddHom (stdδBilin M) (stdδBilin_balanced M)

@[simp] theorem stdδAddHom_tmul (v : ArrowTgt k Q) (m : restrictObj M) :
    stdδAddHom M (v ⊗ₜ[Q → k] m)
      = arrowInclusion v ⊗ₜ[Q → k] m
        - (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (arrowInclusion v • (m : M) : restrictObj M) :=
  rfl

/-- Move a vertex-embedding scalar across the tensor: `1 ⊗ (f s · y) = f s ⊗ y` in `A ⊗_S M`,
by the `S`-balancing (`f s = vertexEmbedding s` is in the image of `S`). -/
theorem one_tmul_smul (s : Q → k) (y : restrictObj M) :
    (1 : PathAlgebra k Q) ⊗ₜ[Q → k] ((vertexEmbedding k Q s • (y : M)) : restrictObj M)
      = vertexEmbedding k Q s ⊗ₜ[Q → k] y := by
  conv_rhs => rw [show vertexEmbedding k Q s = (s : Q → k) • (1 : PathAlgebra k Q) by
    rw [vertex_smul_def, one_mul]]
  rw [TensorProduct.smul_tmul]
  rfl

/-- **The `S`-linear boundary datum** `δ : V ⊗_S M → restrict (A ⊗_S M)`,
`δ (v ⊗ m) = v ⊗ m − 1 ⊗ (v · m)`. Source-`S`-linear: the source scaling of `v` corresponds to
left multiplication by `f s`, which is the `A`-action on `A ⊗_S M`. -/
noncomputable def stdδ :
    VtensObj M ⟶ (restrictScalars (vertexEmbedding k Q)).obj (inducedRestrictObj M) :=
  ModuleCat.ofHom (X := VtensObj M)
    (Y := (restrictScalars (vertexEmbedding k Q)).obj (inducedRestrictObj M))
    { toFun := fun x => stdδAddHom M x
      map_add' := fun x y => (stdδAddHom M).map_add x y
      map_smul' := fun s x => by
        change (stdδAddHom M (s • x) : inducedRestrictObj M)
          = vertexEmbedding k Q s • (stdδAddHom M x : inducedRestrictObj M)
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul v m =>
            rw [vtens_smul_def, vtens_smul_tmul, stdδAddHom_tmul, stdδAddHom_tmul]
            -- goal after: incl(s·_src v) ⊗ m − 1 ⊗ (incl(s·_src v) • m)
            --   = f s • (incl v ⊗ m − 1 ⊗ (incl v • m))
            simp only [srcHom_apply, arrowInclusion_wSMul_src]
            rw [smul_sub]
            refine congr_arg₂ (· - ·) ?_ ?_
            · -- (f s * incl v) ⊗ m = f s • (incl v ⊗ m)
              rw [TensorProduct.smul_tmul', smul_eq_mul]
            · -- 1 ⊗ ((f s * incl v) • m) = f s • (1 ⊗ (incl v • m))
              rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← one_tmul_smul]
              congr 1
              exact mul_smul _ _ _
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add] }

@[simp] theorem stdδ_tmul (v : ArrowTgt k Q) (m : restrictObj M) :
    (stdδ M).hom (v ⊗ₜ[Q → k] m)
      = arrowInclusion v ⊗ₜ[Q → k] m
        - (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (arrowInclusion v • (m : M) : restrictObj M) := by
  change stdδAddHom M (v ⊗ₜ[Q → k] m) = _
  rw [stdδAddHom_tmul]

/-- **The boundary map** `d : A ⊗_S (V ⊗_S M) → A ⊗_S M`,
`d (a ⊗ v ⊗ m) = a·v ⊗ m − a ⊗ (v · m)`, the `A`-linear extension of `δ` via the adjunction. -/
noncomputable def stdd : inducedVtensObj M ⟶ inducedRestrictObj M :=
  homEquivSymm (stdδ M)

@[simp] theorem stdd_tmul (a : PathAlgebra k Q) (v : ArrowTgt k Q) (m : restrictObj M) :
    (stdd M).hom (a ⊗ₜ[Q → k] (v ⊗ₜ[Q → k] m : VtensObj M))
      = (a * arrowInclusion v) ⊗ₜ[Q → k] m
        - a ⊗ₜ[Q → k] (arrowInclusion v • (m : M) : restrictObj M) := by
  rw [stdd, homEquivSymm_tmul, stdδ_tmul, smul_sub, TensorProduct.smul_tmul', smul_eq_mul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-! ## The short complex -/

theorem stdd_comp_stdε : stdd M ≫ stdε M = 0 := by
  apply ModuleCat.hom_ext
  ext x
  refine TensorProduct.induction_on x (by simp) (fun a y => ?_)
    (fun p q hp hq => by rw [map_add, map_add, hp, hq])
  -- pure tensor `a ⊗ y`; induct on the inner `y : V ⊗_S M`
  change (stdε M).hom ((stdd M).hom (a ⊗ₜ[Q → k] y)) = 0
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v m =>
      rw [stdd_tmul, map_sub, stdε_tmul, stdε_tmul]
      -- (a * incl v) • m − a • (incl v • m) = 0
      rw [mul_smul, sub_self]
  | add y z hy hz =>
      rw [TensorProduct.tmul_add, map_add, map_add, hy, hz, add_zero]

/-- **`ε` is an epimorphism**: `m = ε (1 ⊗ m)`. -/
theorem epi_stdε : Epi (stdε M) := by
  rw [ModuleCat.epi_iff_surjective]
  intro m
  refine ⟨(1 : PathAlgebra k Q) ⊗ₜ[Q → k] (m : restrictObj M), ?_⟩
  rw [stdε_tmul, one_smul]

/-- **The standard short complex** `A ⊗_S (V ⊗_S M) →ᵈ A ⊗_S M →ᵉ M` with `d ≫ ε = 0`.
`Epi ε` is `epi_stdε`; middle exactness `ker ε = im d` is `standardComplex_exact` and injectivity
`Mono d` is `stdd_mono` (both in `Chapter9/PathAlgebraStandardResolution.lean`). Together these
assemble the full `ShortExact` as `standardResolution_shortExact`. -/
noncomputable def standardComplex : ShortComplex (ModuleCat.{u + 1} (PathAlgebra k Q)) :=
  ShortComplex.mk (stdd M) (stdε M) (stdd_comp_stdε M)

end Etingof.PathAlgebra
