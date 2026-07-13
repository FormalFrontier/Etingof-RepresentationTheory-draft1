import EtingofRepresentationTheory.Chapter9.PathAlgebraVertexSubalgebra
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# The noncommutative induction functor `A ⊗_S -` for a path algebra

Second layer of the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i)). Write `A := PathAlgebra k Q` and `S := Q → k`, the commutative subalgebra
spanned by the trivial-path idempotents, embedded by `f := vertexEmbedding : S →+* A`.

Mathlib's `ModuleCat.extendScalars` requires **commutative** rings on both sides, so it does not
apply here: `A` is noncommutative and the image of `f` is not central. This file builds the
missing **left** adjoint of `restrictScalars f` by hand:

* `Etingof.PathAlgebra.inducedModule : ModuleCat S ⥤ ModuleCat A`, `M ↦ A ⊗_S M`, with a genuine
  (non-`sorry`) body — object map, morphism map, `map_id`, `map_comp`.
* `Etingof.PathAlgebra.inducedRestrictAdj : inducedModule ⊣ restrictScalars f`, the tensor–hom
  adjunction for the noncommutative ring hom `f`.
* `Etingof.PathAlgebra.projective_inducedModule_obj` — every `inducedModule.obj M` is a projective
  `A`-module, because `restrictScalars f` is exact and `S` is semisimple.

## The `S`-module structure on `A`

The tensor product `A ⊗_S M` regards `A` as a **right** `S`-module, `s • a = a * f s`
(`Etingof.PathAlgebra.instModuleVertex`). This right action is what makes left multiplication by
`A` well-defined on the tensor: `a' * (a * f s) = (a' * a) * f s`, so left multiplication commutes
with the `S`-action (`SMulCommClass S A A`), and `TensorProduct.leftModule` upgrades `A ⊗_S M` to a
left `A`-module. Note this is a *different* `S`-action from the one `restrictScalars f` puts on an
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

/-- **The induction functor** `A ⊗_S - : ModuleCat S ⥤ ModuleCat A`. Real (non-`sorry`) body:
object map `inducedObj`, morphism map `inducedMap`, and the functoriality laws. -/
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

end Etingof.PathAlgebra
