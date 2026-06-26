import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Example 2.3.14 (continued): Group Algebra Representations

3. The group algebra A = k[G], where G is a group. A representation of A is the same thing
   as a representation of G, i.e., a vector space V together with a group homomorphism
   ρ : G → Aut(V), where Aut(V) = GL(V) denotes the group of invertible linear maps from V
   to itself (the general linear group of V).

## Formalization

The book asserts an equality of *data*: a representation of the algebra `A = k[G]` on `V`
is "the same thing" as a representation of the group `G` on `V`, i.e. a group homomorphism
`ρ : G → GL(V)`. We make this content explicit with two bijections (`Equiv`s), bypassing the
vacuous tautology `Module k[G] V → Module k[G] V` that was here before.

* `repEquivAlgHom` : a representation `ρ : Representation k G V` is the same data as an
  algebra homomorphism `k[G] →ₐ[k] Module.End k V`. A `k`-compatible `k[G]`-module structure
  on `V` is exactly such an algebra homomorphism (a module *is* an action map into the
  endomorphism algebra), so this is precisely "a representation of `A = k[G]`".

* `repEquivGL` : a representation `ρ : Representation k G V` is the same data as a *group*
  homomorphism `G →* (V ≃ₗ[k] V)`, i.e. `ρ : G → GL(V)` into the general linear group of
  invertible linear maps. This is the book's "representation of `G`" side. Invertibility is
  automatic precisely because `G` is a group (`MonoidHom.toHomUnits`).

Chaining the two: a `k[G]`-module ↔ a representation of `G` ↔ `(V, ρ : G → GL(V))`.

## Mathlib correspondence

`MonoidAlgebra k G` is `k[G]`; `Representation k G V = (G →* (V →ₗ[k] V))`. The first
bijection is `MonoidAlgebra.lift`; the second composes `MonoidHom.toHomUnitsMulEquiv` (uses
that `G` is a group) with `LinearMap.GeneralLinearGroup.generalLinearEquiv`.
-/

namespace Etingof.Example_2_3_14_continued

open scoped MonoidAlgebra

variable (k : Type*) [CommRing k] (G : Type*) [Group G]
    (V : Type*) [AddCommGroup V] [Module k V]

/-- **A representation of the algebra `A = k[G]` is the same data as a representation of the
group `G`.** A representation `ρ : G →* (V →ₗ[k] V)` corresponds bijectively to an algebra
homomorphism `k[G] →ₐ[k] Module.End k V`; the latter is exactly a `k`-compatible `k[G]`-module
structure on `V` (the action map into the endomorphism algebra). (Etingof Example 2.3.14(3)) -/
noncomputable def repEquivAlgHom :
    Representation k G V ≃ (k[G] →ₐ[k] Module.End k V) :=
  MonoidAlgebra.lift k (Module.End k V) G

@[simp]
theorem repEquivAlgHom_apply_single (ρ : Representation k G V) (g : G) :
    repEquivAlgHom k G V ρ (MonoidAlgebra.single g 1) = ρ g := by
  simp [repEquivAlgHom]

/-- For a group `G`, a monoid homomorphism `G →* M` into any monoid `M` lands automatically in
the units `Mˣ`; this is the bijection between the two (the inverse just forgets the units). -/
def homUnitsEquiv (M : Type*) [Monoid M] : (G →* M) ≃ (G →* Mˣ) where
  toFun ρ := ρ.toHomUnits
  invFun f := (Units.coeHom M).comp f
  left_inv ρ := by ext g; rfl
  right_inv f := by ext g; rfl

/-- **A representation of `G` is the same data as a group homomorphism `ρ : G → GL(V)`.**
Here `GL(V) = V ≃ₗ[k] V` is the group of invertible `k`-linear maps `V → V`. Invertibility of
each `ρ g` is forced because `G` is a group. (Etingof Example 2.3.14(3)) -/
def repEquivGL :
    Representation k G V ≃ (G →* (V ≃ₗ[k] V)) :=
  Equiv.trans
    (homUnitsEquiv G (Module.End k V))
    (MulEquiv.monoidHomCongrRightEquiv
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V))

@[simp]
theorem repEquivGL_apply (ρ : Representation k G V) (g : G) (v : V) :
    repEquivGL k G V ρ g v = ρ g v := rfl

/-- The group homomorphism `ρ : G → GL(V)` attached to a representation acts the same way as
`ρ` itself: the data really is "the same thing", not an arbitrary relabelling. -/
theorem repEquivGL_symm_apply (f : G →* (V ≃ₗ[k] V)) (g : G) (v : V) :
    (repEquivGL k G V).symm f g v = f g v := rfl

end Etingof.Example_2_3_14_continued
