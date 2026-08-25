import EtingofRepresentationTheory.Chapter9.PathAlgebraVertexSubalgebra
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

set_option backward.isDefEq.respectTransparency false

/-!
# The noncommutative induction functor `A ⊗_S -` for a path algebra

In the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i)), write `A := PathAlgebra k Q` and `S := Q → k`, the commutative subalgebra
spanned by the trivial-path idempotents, embedded by `f := vertexEmbedding : S →+* A`.

Mathlib's `ModuleCat.extendScalars` requires commutative rings on both sides, so it does not
apply here: `A` is noncommutative and the image of `f` is not central. This file builds the
missing left adjoint of `restrictScalars f` by hand:

* `Etingof.PathAlgebra.inducedModule : ModuleCat S ⥤ ModuleCat A`, `M ↦ A ⊗_S M`, with object map,
  morphism map, `map_id`, and `map_comp`.
* `Etingof.PathAlgebra.inducedRestrictAdj : inducedModule ⊣ restrictScalars f`, the tensor–hom
  adjunction for the noncommutative ring hom `f`.
* `Etingof.PathAlgebra.projective_inducedModule_obj`: every `inducedModule.obj M` is a projective
  `A`-module, because `restrictScalars f` is exact and `S` is semisimple.

## The `S`-module structure on `A`

The tensor product `A ⊗_S M` regards `A` as a **right** `S`-module, `s • a = a * f s`
(`Etingof.PathAlgebra.instModuleVertex`). This right action is what makes left multiplication by
`A` well-defined on the tensor: `a' * (a * f s) = (a' * a) * f s`, so left multiplication commutes
with the `S`-action (`SMulCommClass S A A`), and `TensorProduct.leftModule` upgrades `A ⊗_S M` to a
left `A`-module. Note this is a different `S`-action from the one `restrictScalars f` puts on an
`A`-module (which uses left multiplication `s • n = f s • n`); the two live on different objects.
-/

universe u

open CategoryTheory TensorProduct

namespace Etingof.PathAlgebra

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

/-- The image of `vertexEmbedding` is commutative: `f s` and `f t` commute for all `s t`,
because `S = Q → k` is a commutative ring and `f` is a ring homomorphism. -/
theorem vertexEmbedding_commute (s t : Q → k) :
    Commute (vertexEmbedding k Q s) (vertexEmbedding k Q t) := by
  change vertexEmbedding k Q s * vertexEmbedding k Q t
      = vertexEmbedding k Q t * vertexEmbedding k Q s
  rw [← map_mul, ← map_mul, mul_comm]

/-- `vertexEmbedding` as a ring homomorphism into the opposite algebra `Aᵐᵒᵖ`, available because
its image is commutative. Used to give `A` the right-multiplication `S`-module structure. -/
noncomputable def vertexEmbeddingOp : (Q → k) →+* (PathAlgebra k Q)ᵐᵒᵖ :=
  (vertexEmbedding k Q).toOpposite vertexEmbedding_commute

/-- **The right-multiplication `S`-module structure on `A`.** `s • a = a * f s`. This is a valid
left `S`-module structure because `S` is commutative, and it is the structure over which the
tensor product `A ⊗_S M` is formed. -/
noncomputable instance instModuleVertex : Module (Q → k) (PathAlgebra k Q) :=
  Module.compHom (PathAlgebra k Q) (vertexEmbeddingOp (k := k) (Q := Q))

theorem vertex_smul_def (s : Q → k) (a : PathAlgebra k Q) :
    s • a = a * vertexEmbedding k Q s := rfl

/-- Left multiplication by `A` commutes with the right `S`-action `s • a = a * f s`, by
associativity. -/
instance : SMulCommClass (Q → k) (PathAlgebra k Q) (PathAlgebra k Q) where
  smul_comm s a b := by
    simp only [vertex_smul_def, smul_eq_mul, mul_assoc]

variable (k Q)

/-- The underlying left `A`-module of the induced module `A ⊗_S M`. The `A`-action is left
multiplication on the tensor's left factor, supplied by `TensorProduct.leftModule`. -/
noncomputable def inducedObj (M : ModuleCat.{u + 1} (Q → k)) :
    ModuleCat.{u + 1} (PathAlgebra k Q) :=
  ModuleCat.of (PathAlgebra k Q) (TensorProduct (Q → k) (PathAlgebra k Q) (M : Type (u + 1)))

variable {k Q}

/-- The morphism map of the induction functor: an `S`-linear `l : M ⟶ M'` induces the `A`-linear
map `a ⊗ m ↦ a ⊗ l m`, i.e. `TensorProduct.map id l`, on `A ⊗_S M`. -/
noncomputable def inducedMap {M M' : ModuleCat.{u + 1} (Q → k)} (l : M ⟶ M') :
    inducedObj k Q M ⟶ inducedObj k Q M' :=
  ModuleCat.ofHom
    { __ := TensorProduct.map (LinearMap.id (R := Q → k) (M := PathAlgebra k Q)) l.hom
      map_smul' := fun a x => by
        change TensorProduct.map (LinearMap.id (R := Q → k) (M := PathAlgebra k Q)) l.hom (a • x)
          = a • TensorProduct.map (LinearMap.id (R := Q → k) (M := PathAlgebra k Q)) l.hom x
        induction x with
        | zero => simp
        | tmul b m =>
            simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
        | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }

@[simp]
theorem inducedMap_tmul {M M' : ModuleCat.{u + 1} (Q → k)} (l : M ⟶ M') (a : PathAlgebra k Q)
    (m : M) : (inducedMap l).hom (a ⊗ₜ[Q → k] m) = a ⊗ₜ[Q → k] l.hom m := rfl

/-- **The induction functor** `A ⊗_S - : ModuleCat S ⥤ ModuleCat A`, with object map `inducedObj`,
morphism map `inducedMap`, and the functoriality laws. -/
noncomputable def inducedModule :
    ModuleCat.{u + 1} (Q → k) ⥤ ModuleCat.{u + 1} (PathAlgebra k Q) where
  obj := inducedObj k Q
  map := inducedMap
  map_id M := by
    ext x
    refine TensorProduct.induction_on x ?_ (fun a m => ?_) (fun x y hx hy => ?_)
    · simp
    · simp [inducedMap_tmul]
    · simp only [map_add, hx, hy]
  map_comp {M M' M''} l l' := by
    ext x
    refine TensorProduct.induction_on x ?_ (fun a m => ?_) (fun x y hx hy => ?_)
    · simp
    · simp [inducedMap_tmul]
    · simp only [map_add, hx, hy]

/-! ## The induction–restriction adjunction -/

section Adjunction

variable {M M' : ModuleCat.{u + 1} (Q → k)} {N N' : ModuleCat.{u + 1} (PathAlgebra k Q)}

open ModuleCat (restrictScalars)

/-- Restriction unfolds the `S`-action on `N` to the `A`-action along `f`: for `h` mapping into
`restrictScalars N`, we have `h (s • m) = f s • h m` as an equation in `N`. -/
theorem restrict_hom_smul (h : M ⟶ (restrictScalars (vertexEmbedding k Q)).obj N)
    (s : Q → k) (m : M) :
    (h.hom (s • m) : N) = vertexEmbedding k Q s • (h.hom m : N) :=
  h.hom.map_smul s m

/-- **Forward direction** of the tensor–hom adjunction: an `A`-linear map `g : A ⊗_S M → N`
restricts to the `S`-linear map `m ↦ g (1 ⊗ m)`. -/
noncomputable def homEquivFwd (g : inducedModule.obj M ⟶ N) :
    M ⟶ (restrictScalars (vertexEmbedding k Q)).obj N :=
  ModuleCat.ofHom (X := M) (Y := (restrictScalars (vertexEmbedding k Q)).obj N)
    { toFun := fun m => g.hom (1 ⊗ₜ[Q → k] m)
      map_add' := fun m m' => by rw [tmul_add, map_add]
      map_smul' := fun s m => by
        have key : (1 : PathAlgebra k Q) ⊗ₜ[Q → k] (s • (m : M))
            = vertexEmbedding k Q s • ((1 : PathAlgebra k Q) ⊗ₜ[Q → k] (m : M)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
            vertex_smul_def, one_mul]
        change (g.hom (1 ⊗ₜ[Q → k] (s • m)) : N)
          = vertexEmbedding k Q s • (g.hom (1 ⊗ₜ[Q → k] m) : N)
        rw [key, map_smul] }

/-- The `S`-balanced additive bilinear map `A × M → N`, `(a, m) ↦ a • h m`, underlying the
backward adjunction map. -/
noncomputable def symmBilin (h : M ⟶ (restrictScalars (vertexEmbedding k Q)).obj N) :
    PathAlgebra k Q →+ (M →+ N) where
  toFun a :=
    { toFun := fun m => a • (h.hom m : N)
      map_zero' := by simp
      map_add' := fun m m' => by rw [map_add, smul_add] }
  map_zero' := by ext m; simp
  map_add' a a' := by
    ext m; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_smul, AddMonoidHom.add_apply]

theorem symmBilin_apply (h : M ⟶ (restrictScalars (vertexEmbedding k Q)).obj N)
    (a : PathAlgebra k Q) (m : M) : symmBilin h a m = a • (h.hom m : N) := rfl

theorem symmBilin_balanced (h : M ⟶ (restrictScalars (vertexEmbedding k Q)).obj N)
    (s : Q → k) (a : PathAlgebra k Q) (m : M) :
    symmBilin h (s • a) m = symmBilin h a (s • m) := by
  rw [symmBilin_apply, symmBilin_apply, restrict_hom_smul, vertex_smul_def, mul_smul]

/-- **Backward direction** of the tensor–hom adjunction: an `S`-linear map `h : M → N` (viewing
`N` via `restrictScalars`) extends to the `A`-linear map `a ⊗ m ↦ a • h m`, built from
`TensorProduct.liftAddHom` and upgraded to `A`-linearity. -/
noncomputable def homEquivSymm (h : M ⟶ (restrictScalars (vertexEmbedding k Q)).obj N) :
    inducedModule.obj M ⟶ N :=
  ModuleCat.ofHom
    { toFun := TensorProduct.liftAddHom (symmBilin h) (symmBilin_balanced h)
      map_add' := map_add _
      map_smul' := fun a x => by
        change TensorProduct.liftAddHom (symmBilin h) (symmBilin_balanced h) (a • x)
          = a • TensorProduct.liftAddHom (symmBilin h) (symmBilin_balanced h) x
        induction x with
        | zero => simp
        | tmul b m =>
            rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul,
              TensorProduct.liftAddHom_tmul, symmBilin_apply, symmBilin_apply, smul_eq_mul,
              mul_smul]
        | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }

@[simp]
theorem homEquivSymm_tmul (h : M ⟶ (restrictScalars (vertexEmbedding k Q)).obj N)
    (a : PathAlgebra k Q) (m : M) :
    (homEquivSymm h).hom (a ⊗ₜ[Q → k] m) = a • (h.hom m : N) := rfl

@[simp]
theorem homEquivFwd_apply (g : inducedModule.obj M ⟶ N) (m : M) :
    (homEquivFwd g).hom m = g.hom (1 ⊗ₜ[Q → k] m) := rfl

/-- **The induction–restriction adjunction** `A ⊗_S - ⊣ restrictScalars f`, the tensor–hom
adjunction for the noncommutative ring hom `f = vertexEmbedding`. -/
noncomputable def inducedRestrictAdj :
    inducedModule (k := k) (Q := Q) ⊣ restrictScalars (vertexEmbedding k Q) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N =>
        { toFun := homEquivFwd
          invFun := homEquivSymm
          left_inv := fun g => by
            apply ModuleCat.hom_ext
            ext x
            refine TensorProduct.induction_on x ?_ (fun a m => ?_) (fun x y hx hy => ?_)
            · simp
            · rw [homEquivSymm_tmul, homEquivFwd_apply, ← g.hom.map_smul, TensorProduct.smul_tmul',
                smul_eq_mul, mul_one]
            · rw [map_add, map_add, hx, hy]
          right_inv := fun h => by
            apply ModuleCat.hom_ext
            ext m
            rw [homEquivFwd_apply, homEquivSymm_tmul, one_smul] }
      homEquiv_naturality_left_symm := fun {M' M N} f g => by
        apply ModuleCat.hom_ext
        ext x
        refine TensorProduct.induction_on x ?_ (fun a m => ?_) (fun x y hx hy => ?_)
        · simp
        · rfl
        · rw [map_add, map_add, hx, hy]
      homEquiv_naturality_right := fun {M N N'} f g => by
        apply ModuleCat.hom_ext
        ext m
        rfl }

/-- **Preservation of projectives.** Every induced module `A ⊗_S M` is a projective `A`-module:
`inducedModule` is a left adjoint whose right adjoint `restrictScalars` is exact, and every
`S`-module is projective since `S = Q → k` is semisimple. -/
theorem projective_inducedModule_obj (M : ModuleCat.{u + 1} (Q → k)) :
    CategoryTheory.Projective (inducedModule.obj M) := by
  have hSproj : CategoryTheory.Projective M := by
    have : Module.Projective (Q → k) M := Module.projective_of_isSemisimpleRing (Q → k) M
    exact M.projective_of_categoryTheory_projective
  haveI : (restrictScalars (vertexEmbedding k Q)).PreservesEpimorphisms := by
    constructor
    intro X Y φ hφ
    rw [ModuleCat.epi_iff_surjective] at hφ ⊢
    exact hφ
  haveI : (inducedModule (k := k) (Q := Q)).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (inducedRestrictAdj (k := k) (Q := Q))
  exact Functor.projective_obj_of_projective _ hSproj

end Adjunction

end Etingof.PathAlgebra
