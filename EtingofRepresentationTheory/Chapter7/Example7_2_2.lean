import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Ring.Pi
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Induced

/-!
# Example 7.2.2: Examples of Functors

Etingof's Example 7.2.2 collects nine illustrations of functors. We formalize
each item against Mathlib where the construction is available, and note the
genuinely advanced ones (Schur and reflection functors) that are out of scope.

1. A category with one object is a monoid; a functor between such categories is
   a monoid homomorphism.
2. Forgetful functors: Groups → Sets, Rings → AbelianGroups.
3. The opposite category C^op; V ↦ V* is a functor Vect_k → Vect_k^op.
4. Hom functors: Y ↦ Hom(X, Y) and Y ↦ Hom(Y, X).
5. X ↦ Fun(X, ℤ) is a functor Sets → Rings^op.
6. Functors from the path category of a quiver to Vect_k are quiver representations.
7. Induction and restriction functors Ind_K^G, Res_K^G.
8. Direct sum, tensor product, tensor/exterior power as functors on Vect_k; the
   symmetric-power and Schur functors are discussed as scope notes.
9. Reflection functors on quiver representation categories (scope note).
-/

open CategoryTheory
open scoped TensorProduct

namespace EtingofRepresentationTheory.Example722

/-! ### (1) One-object categories are monoids

A (locally small) category with a single object `X` is the same data as a monoid:
the monoid is `Hom(X, X)` with composition as multiplication. Mathlib packages
this as `CategoryTheory.SingleObj M`, the one-object category attached to a monoid
`M`. A functor between two such categories is exactly a monoid homomorphism, an
equivalence recorded by `SingleObj.mapHom`. -/

/-- The one-object category attached to a monoid is a category. (Etingof 7.2.2(1)) -/
example (M : Type*) [Monoid M] : Category (SingleObj M) := inferInstance

/-- Functors between one-object categories are exactly monoid homomorphisms.
(Etingof 7.2.2(1)) -/
example {M N : Type*} [Monoid M] [Monoid N] :
    (M →* N) ≃ (SingleObj M ⥤ SingleObj N) :=
  SingleObj.mapHom M N

/-! ### (2) Forgetful functors

`Groups → Sets` forgets the group structure; `Rings → AbelianGroups` keeps only
the additive group. Both are concrete-category forgetful functors in Mathlib:
`forget` lands in `Type`, while `forget₂` lands in an intermediate concrete
category (here the additive abelian group underlying a ring). -/

/-- The forgetful functor from Groups to Sets. (Etingof 7.2.2(2)) -/
example : GrpCat ⥤ Type _ := forget GrpCat

/-- The forgetful functor from Rings to AbelianGroups, recording only the
additive group structure of a ring. (Etingof 7.2.2(2)) -/
example : RingCat ⥤ AddCommGrpCat := forget₂ RingCat AddCommGrpCat

/-! ### (3) The dual functor `V ↦ V*`

Taking the dual `V* = Hom_k(V, k)` reverses arrows, so it is a (contravariant)
functor `Vect_k → Vect_k^op`. We build it from `Module.Dual` and the transpose
map `LinearMap.dualMap`; functoriality is `dualMap_id` and `dualMap_comp_dualMap`. -/

/-- The dual functor `V ↦ V*` as a functor `ModuleCat k ⥤ (ModuleCat k)ᵒᵖ`.
(Etingof 7.2.2(3)) -/
noncomputable example (k : Type*) [Field k] : ModuleCat k ⥤ (ModuleCat k)ᵒᵖ where
  obj V := Opposite.op (ModuleCat.of k (Module.Dual k V))
  map f := (ModuleCat.ofHom f.hom.dualMap).op
  map_id V := by
    apply Quiver.Hom.unop_inj
    ext φ x
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    ext φ x
    rfl

/-! ### (4) Hom functors

For a locally small category `C` and a fixed object `X`, the assignment
`Y ↦ Hom(X, Y)` is a covariant functor `C ⥤ Sets` (Mathlib's `coyoneda`), and
`Y ↦ Hom(Y, X)` is a contravariant functor `C^op ⥤ Sets` (Mathlib's `yoneda`). -/

/-- The covariant Hom functor `Y ↦ Hom(X, Y)`. (Etingof 7.2.2(4)) -/
example {C : Type*} [Category C] (X : C) : C ⥤ Type _ :=
  coyoneda.obj (Opposite.op X)

/-- The contravariant Hom functor `Y ↦ Hom(Y, X)`. (Etingof 7.2.2(4)) -/
example {C : Type*} [Category C] (X : C) : Cᵒᵖ ⥤ Type _ :=
  yoneda.obj X

/-! ### (5) The functor `X ↦ Fun(X, ℤ)`

A set `X` gives the commutative ring `X → ℤ` of integer-valued functions, with
pointwise operations. A map of sets `f : X → Y` induces, by precomposition, a
ring homomorphism `(Y → ℤ) → (X → ℤ)`, which reverses arrows. Hence
`X ↦ Fun(X, ℤ)` is a functor `Sets → Rings^op`. -/

/-- Precomposition ring homomorphism `(Y → ℤ) →+* (X → ℤ)` induced by `f : X → Y`. -/
private def funZPrecomp {X Y : Type*} (f : X → Y) : (Y → ℤ) →+* (X → ℤ) :=
  RingHom.pi fun x => Pi.evalRingHom (fun _ : Y => ℤ) (f x)

/-- The functor `X ↦ Fun(X, ℤ)` from Sets to Rings^op. (Etingof 7.2.2(5)) -/
example : Type ⥤ CommRingCatᵒᵖ where
  obj X := Opposite.op (CommRingCat.of (X → ℤ))
  map f := (CommRingCat.ofHom (funZPrecomp f)).op
  map_id X := by
    apply Quiver.Hom.unop_inj
    ext g x
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    ext h x
    rfl

/-! ### (6) Path categories of quivers

For a quiver `Q`, the path category `C(Q)` has the vertices as objects and
oriented paths as morphisms (Mathlib's `CategoryTheory.Paths Q`). A functor
`C(Q) ⥤ Vect_k` is the same as a quiver representation of `Q`: by the universal
property `Paths.lift`, it is determined by a prefunctor `Q ⥤q Vect_k`, i.e. a
vector space at each vertex and a linear map along each arrow. -/

/-- The path category of a quiver is a category. (Etingof 7.2.2(6)) -/
example (Q : Type*) [Quiver Q] : Category (Paths Q) := inferInstance

/-- A quiver representation (a prefunctor into `Vect_k`) lifts to a functor on the
path category. (Etingof 7.2.2(6)) -/
noncomputable example {Q : Type*} [Quiver Q] {k : Type*} [Field k]
    (φ : Q ⥤q ModuleCat k) : Paths Q ⥤ ModuleCat k :=
  Paths.lift φ

/-! ### (7) Induction and restriction

For an inclusion of groups `K ⊆ G`, given by a group homomorphism `f : K →* G`,
restriction `Res_K^G : Rep(G) → Rep(K)` precomposes the action with `f`, and
induction `Ind_K^G : Rep(K) → Rep(G)` is its left adjoint. Mathlib provides
`Rep.resFunctor` and `Rep.indFunctor`. -/

/-- The restriction functor `Res_K^G : Rep(G) → Rep(K)`. (Etingof 7.2.2(7)) -/
example (k : Type*) [CommRing k] {K G : Type*} [Group K] [Group G] (f : K →* G) :
    Rep k G ⥤ Rep k K :=
  Rep.resFunctor f

/-- The induction functor `Ind_K^G : Rep(K) → Rep(G)`. (Etingof 7.2.2(7)) -/
noncomputable example (k : Type*) [CommRing k] {K G : Type*} [Group K] [Group G]
    (f : K →* G) : Rep k K ⥤ Rep k G :=
  Rep.indFunctor k f

/-! ### (8) Products of categories: direct sum, tensor, and power functors

Using the Cartesian product `Vect_k × Vect_k`, direct sum and tensor product are
bifunctors `Vect_k × Vect_k ⥤ Vect_k`, and the powers `V ↦ V^{⊗n}`, `V ↦ ∧ⁿ V`
are endofunctors of `Vect_k`. We formalize each against `ModuleCat k`. The
symmetric power `Sⁿ V` and the general Schur functors are discussed in the scope
notes below. -/

/-- The direct-sum bifunctor `⊕ : Vect_k × Vect_k → Vect_k`. On modules the binary
direct sum is carried by the product `M × N`, with `LinearMap.prodMap` on arrows.
(Etingof 7.2.2(8)) -/
noncomputable example (k : Type*) [Ring k] : ModuleCat k × ModuleCat k ⥤ ModuleCat k where
  obj MN := ModuleCat.of k (MN.1 × MN.2)
  map f := ModuleCat.ofHom (f.1.hom.prodMap f.2.hom)
  map_id MN := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact LinearMap.prodMap_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact LinearMap.prodMap_comp _ _ _ _

/-- The tensor-product bifunctor `⊗ : Vect_k × Vect_k → Vect_k`, given by the
monoidal structure on `ModuleCat k`. (Etingof 7.2.2(8)) -/
noncomputable example (k : Type*) [CommRing k] : ModuleCat k × ModuleCat k ⥤ ModuleCat k :=
  MonoidalCategory.tensor (ModuleCat k)

/-- The `n`-th tensor-power functor `V ↦ V^{⊗n}` on `Vect_k`, built from
`PiTensorProduct.map`. (Etingof 7.2.2(8)) -/
noncomputable example (k : Type*) [CommRing k] (n : ℕ) : ModuleCat k ⥤ ModuleCat k where
  obj V := ModuleCat.of k (⨂[k] (_ : Fin n), V)
  map f := ModuleCat.ofHom (PiTensorProduct.map fun _ => f.hom)
  map_id V := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact PiTensorProduct.map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact PiTensorProduct.map_comp _ _

/-- The `n`-th exterior-power functor `V ↦ ∧ⁿ V` on `Vect_k`, from Mathlib's
`ModuleCat.exteriorPower.functor`. (Etingof 7.2.2(8)) -/
noncomputable example (k : Type*) [CommRing k] (n : ℕ) : ModuleCat k ⥤ ModuleCat k :=
  ModuleCat.exteriorPower.functor k n

/-! #### (8) Scope notes: symmetric power and Schur functors

**Symmetric power `V ↦ Sⁿ V`.** Mathlib has the symmetric power `Sym[k]^n V`
(`Mathlib.LinearAlgebra.TensorPower.Symmetric`, the quotient of `V^{⊗n}` by the
symmetric-group action), but its functoriality — a `map` on linear maps together
with the universal property — is not yet available (it is listed as future work
in that file). Once `SymmetricPower.map` (or the symmetric universal property)
lands upstream, `V ↦ Sⁿ V` assembles into an endofunctor of `ModuleCat k` exactly
as the exterior power does above. This is a missing-API gap, not a mathematical
obstruction.

**Schur functors `V ↦ Hom_{S_n}(π, V^{⊗n})`.** For a representation `π` of `Sₙ`,
the Schur functor sends `V` to `Hom_{S_n}(π, V^{⊗n})`; the irreducible ones are
labeled by Young diagrams. This requires the `Sₙ`-action on `V^{⊗n}` and the
`Sₙ`-equivariant Hom, neither packaged as a functor in Mathlib. It is genuinely
advanced and is deferred; the tensor-power functor above is the first ingredient. -/

/-! ### (9) Reflection functors (scope note)

The Bernstein-Gelfand-Ponomarev reflection functors `F_i^± : Rep(Q) → Rep(Q̄_i)`
reflect a quiver representation at a source/sink vertex `i` (replacing `V_i` by the
cokernel/kernel of the canonical map to/from `⊕_{i→j} V_j`). This project already
constructs the reflection functor at the level of objects: `Etingof.reflectionFunctorMinus`
(`Chapter6/Definition6_6_4.lean`) sends a representation of `Q` to a representation
of `Q̄_i` at a source, with the companion `reflectionFunctorPlus` at a sink.

Packaging these as `CategoryTheory.Functor`s between the representation categories
`Rep(Q) ⥤ Rep(Q̄_i)` additionally requires the action on morphisms of representations
plus the functor laws, which are not assembled here (BGP reflection functors are not
in Mathlib). This is deferred pending a `CategoryTheory`-level quiver-representation
category compatible with the object-level construction of Definition 6.6.4. -/

end EtingofRepresentationTheory.Example722
