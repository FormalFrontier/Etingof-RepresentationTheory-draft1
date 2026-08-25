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
import EtingofRepresentationTheory.Chapter7.SymmetricPowerFunctor
import EtingofRepresentationTheory.Chapter7.SchurFunctor
import EtingofRepresentationTheory.Chapter6.Definition6_6_3_Functor
import EtingofRepresentationTheory.Chapter6.Definition6_6_4_Functor

/-!
# Example 7.2.2: Examples of Functors

Etingof's Example 7.2.2 collects nine illustrations of functors. We formalize
each item, against Mathlib where the construction is available and against
purpose-built API otherwise (the symmetric-power and Schur functors, neither of
which Mathlib carries).

1. A category with one object is a monoid; a functor between such categories is
   a monoid homomorphism.
2. Forgetful functors: Groups → Sets, Rings → AbelianGroups.
3. The opposite category C^op; V ↦ V* is a functor Vect_k → Vect_k^op.
4. Hom functors: Y ↦ Hom(X, Y) and Y ↦ Hom(Y, X).
5. X ↦ Fun(X, ℤ) is a functor Sets → Rings^op.
6. Functors from the path category of a quiver to Vect_k are quiver representations.
7. Induction and restriction functors Ind_K^G, Res_K^G.
8. Direct sum, tensor product, tensor/symmetric/exterior power as functors on Vect_k,
   and the Schur functors `V ↦ Hom_{S_n}(π, V^{⊗n})`.
9. Reflection functors `F_i^± : Rep Q ⥤ Rep Q̄_i` on quiver representation categories.
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
bifunctors `Vect_k × Vect_k ⥤ Vect_k`, and the powers `V ↦ V^{⊗n}`, `V ↦ SⁿV`,
`V ↦ ∧ⁿ V` are endofunctors of `Vect_k`, as are the Schur functors
`V ↦ Hom_{S_n}(π, V^{⊗n})`. We formalize each against `ModuleCat k`. -/

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

/-- The `n`-th symmetric-power functor `V ↦ SⁿV` on `Vect_k`. Mathlib has the
symmetric power `Sym[k]^n V` but no action on linear maps (the universal property
is listed as future work there), so `SymmetricPower.map` and the resulting functor
are supplied by `Chapter7/SymmetricPowerFunctor.lean`. (Etingof 7.2.2(8)) -/
noncomputable example (k : Type) [Field k] (n : ℕ) : ModuleCat k ⥤ ModuleCat k :=
  ModuleCat.symmetricPower k n

/-! #### (8) Schur functors

For a representation `π` of `Sₙ` on `W`, the Schur functor sends `V` to
`Hom_{S_n}(π, V^{⊗n})`, the `Sₙ`-intertwiners from `π` into the tensor power
carrying the slot-permutation action. Neither that action nor the equivariant Hom
is packaged in Mathlib, so both are built in `Chapter7/SchurFunctor.lean`. -/

/-- The Schur functor attached to an `Sₙ`-representation `π`. (Etingof 7.2.2(8)) -/
noncomputable example (k : Type) [Field k] (n : ℕ) (W : Type) [AddCommGroup W]
    [Module k W] (π : Representation k (Equiv.Perm (Fin n)) W) :
    ModuleCat k ⥤ ModuleCat k :=
  Etingof.schurFunctor π

/-- The value of the Schur functor at `V` really is the space of `Sₙ`-equivariant maps
`π → V^{⊗n}`: membership unfolds to the intertwining identity. (Etingof 7.2.2(8)) -/
example (k : Type) [Field k] (n : ℕ) {W : Type} [AddCommGroup W] [Module k W]
    (π : Representation k (Equiv.Perm (Fin n)) W)
    {V : Type} [AddCommGroup V] [Module k V] (φ : W →ₗ[k] ⨂[k] (_ : Fin n), V) :
    φ ∈ Etingof.schurObj π V ↔
      ∀ σ : Equiv.Perm (Fin n),
        (Etingof.tensorPowerPermRep k n V σ) ∘ₗ φ = φ ∘ₗ (π σ) :=
  Etingof.mem_schurObj_iff π φ

/-- Sanity check on the Schur construction: at the trivial `Sₙ`-representation it returns
the symmetric tensors `(V^{⊗n})^{Sₙ}`. (Etingof 7.2.2(8)) -/
noncomputable example (k : Type) [Field k] (n : ℕ) (V : Type) [AddCommGroup V] [Module k V] :
    Etingof.schurObj (Representation.trivial k (Equiv.Perm (Fin n)) k) V ≃ₗ[k]
      (Etingof.tensorPowerPermRep k n V).invariants :=
  Etingof.schurObjTrivialEquiv

/-! ### (9) Reflection functors

The Bernstein-Gelfand-Ponomarev reflection functors `F_i^± : Rep Q ⥤ Rep Q̄_i`
reflect a quiver representation at a sink/source vertex `i`, replacing `V_i` by the
kernel/cokernel of the canonical map to/from `⊕_{i→j} V_j` (Definitions 6.6.3 and 6.6.4).

`Rep Q` is `Etingof.QuiverRepresentation k Q` with the category structure of
`Chapter2/QuiverRepresentationCategory.lean` (objects from Definition 2.8.3, morphisms
from Definition 2.8.10). The two reflection functors are assembled in
`Chapter6/Definition6_6_3_Functor.lean` and `Chapter6/Definition6_6_4_Functor.lean`;
their object actions are the Chapter 6 constructions `Etingof.reflectionFunctorPlus`
and `Etingof.reflectionFunctorMinus`. BGP reflection functors are not in Mathlib. -/

/-- `F⁺ᵢ : Rep Q ⥤ Rep Q̄ᵢ` at a sink `i` is a functor. (Etingof 7.2.2(9)) -/
noncomputable example (k : Type) [CommSemiring k] (Q : Type) [DecidableEq Q] [Quiver Q]
    (i : Q) (hi : Etingof.IsSink Q i) :
    @CategoryTheory.Functor
      (Etingof.QuiverRepresentation k Q) Etingof.QuiverRepresentation.instCategory
      (@Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i))
      (@Etingof.QuiverRepresentation.instCategory k _ Q (Etingof.reversedAtVertex Q i)) :=
  Etingof.reflectionFunctorPlusFunctor k Q i hi

/-- `F⁻ᵢ : Rep Q ⥤ Rep Q̄ᵢ` at a source `i` is a functor. (Etingof 7.2.2(9)) -/
noncomputable example (k : Type) [CommRing k] (Q : Type) [DecidableEq Q] [Quiver Q]
    (i : Q) (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)] :
    @CategoryTheory.Functor
      (Etingof.QuiverRepresentation k Q) Etingof.QuiverRepresentation.instCategory
      (@Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i))
      (@Etingof.QuiverRepresentation.instCategory k _ Q (Etingof.reversedAtVertex Q i)) :=
  Etingof.reflectionFunctorMinusFunctor k Q i hi

end EtingofRepresentationTheory.Example722
