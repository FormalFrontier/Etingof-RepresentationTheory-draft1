import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
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
8. Direct sum, tensor product, symmetric/exterior power as functors.
9. Reflection functors on quiver representation categories.
-/

open CategoryTheory

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

/-! ### (8) and (9): Schur and reflection functors

Item (8) (direct sum / tensor product / tensor, symmetric and exterior powers,
and the Schur functors `V ↦ Hom_{S_n}(π, V^{⊗n})`) and item (9) (the reflection
functors `F_i^±` of quiver representation theory) require infrastructure beyond
the current scope: the direct-sum and tensor-product bifunctors on `ModuleCat`,
the symmetric/exterior power functors, and the reflection-functor construction
are not assembled as packaged functors here. They are recorded for completeness. -/

end EtingofRepresentationTheory.Example722
