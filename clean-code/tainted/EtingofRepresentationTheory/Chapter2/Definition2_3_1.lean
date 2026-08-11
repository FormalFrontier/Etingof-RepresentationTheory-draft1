import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Algebra.Opposite

/-!
# Definition 2.3.1: Representation of an Algebra (Left A-module)

A **representation** of an algebra `A` (also called a **left `A`-module**) is a vector space `V`
together with a homomorphism of algebras `ρ : A → End V`.

Similarly, a **right `A`-module** is a space `V` equipped with an antihomomorphism
`ρ : A → End V`.

## Mathlib correspondence

A left `A`-module is `Module A V`. Mathlib uses left modules by convention. We keep the generic
`Etingof.Representation A V := Module A V` alias, which is the working definition used throughout
the project.

The book, however, phrases the definition through an **algebra homomorphism**
`ρ : A →ₐ[k] Endₖ(V)` over the base field `k`. The two presentations are equivalent, and this file
makes the round trip precise for compatible data
`[Algebra k A] [Module k V] [Module A V] [IsScalarTower k A V]`:

* `Etingof.Representation.toAlgHom : A →ₐ[k] Module.End k V` is the book's `ρ`, built from
  `Algebra.lsmul k k V`; it acts by `toAlgHom k A V a v = a • v` (`toAlgHom_apply`).
* `Etingof.Representation.ofAlgHom ρ : Module A V` reconstructs the module action from any
  `ρ : A →ₐ[k] Module.End k V`, reusing `Module.compHom V ρ.toRingHom`; it acts by
  `a • v = ρ a v` (`ofAlgHom_smul`), and the reconstructed action satisfies the scalar-tower law
  (`ofAlgHom_isScalarTower`).
* The two constructions are mutually inverse: `ofAlgHom_toAlgHom` recovers the original module
  structure, and `toAlgHom_ofAlgHom` recovers the original `ρ`.

For right modules, the antihomomorphism `A → End(V)` is equivalently a homomorphism
`Aᵐᵒᵖ → End(V)`, so the Mathlib encoding is `Module Aᵐᵒᵖ V`. The declarations below record
this convention and both associativity formulas from the source. The additional equivalence between
left and right modules when `A` is commutative belongs to Remark 2.3.2.
-/

/-- A representation of an algebra A, in the sense of Etingof Definition 2.3.1.
This is `Module A V` in Mathlib. -/
abbrev Etingof.Representation (A : Type*) (V : Type*) [Ring A] [AddCommGroup V] :=
  Module A V

/-- A right representation of `A` is a left module over the opposite ring `Aᵐᵒᵖ`. Equivalently,
its action map is an antihomomorphism `A → End(V)`. -/
abbrev Etingof.RightRepresentation (A : Type*) (V : Type*) [Ring A] [AddCommGroup V] :=
  Module Aᵐᵒᵖ V

namespace Etingof.Representation

section Associativity

variable {A V : Type*} [Ring A] [AddCommGroup V]

/-- The abbreviated left action satisfies the source's formula `(ab)v = a(bv)`. -/
theorem mul_smul_apply [Module A V] (a b : A) (v : V) :
    (a * b) • v = a • (b • v) :=
  mul_smul a b v

/-- Under the convention `v a := op(a) • v`, a right action satisfies `(va)b = v(ab)`.
The reversal in `Aᵐᵒᵖ` is exactly the antihomomorphism law from Definition 2.3.1. -/
theorem right_smul_mul_apply [Module Aᵐᵒᵖ V] (a b : A) (v : V) :
    MulOpposite.op (a * b) • v = MulOpposite.op b • (MulOpposite.op a • v) := by
  change (MulOpposite.op b * MulOpposite.op a) • v = _
  exact mul_smul _ _ _

end Associativity

/-! ### The algebra-hom presentation (forward direction)

Given a compatible module, `toAlgHom` is the algebra homomorphism `ρ : A →ₐ[k] Endₖ(V)` of the
book. It is `Algebra.lsmul`, the `k`-algebra map sending `a` to the `k`-linear endomorphism
`v ↦ a • v`. -/

section ToAlgHom

variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- **Definition 2.3.1 (algebra-hom presentation).** The book's homomorphism of algebras
`ρ : A →ₐ[k] Endₖ(V)` attached to a representation, given as left multiplication `v ↦ a • v`.
It is `Algebra.lsmul k k V`. -/
def toAlgHom : A →ₐ[k] Module.End k V :=
  Algebra.lsmul k k V

/-- The action homomorphism sends `a` to the endomorphism `v ↦ a • v`. -/
@[simp]
theorem toAlgHom_apply (a : A) (v : V) : toAlgHom k A V a v = a • v := rfl

end ToAlgHom

/-! ### Reconstructing the module from an algebra hom (reverse direction)

Conversely, an algebra homomorphism `ρ : A →ₐ[k] Endₖ(V)` induces a compatible `A`-module
structure on `V`, obtained by pulling back the tautological `Endₖ(V)`-action along `ρ`
via `Module.compHom`. -/

section OfAlgHom

variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V]

/-- **Definition 2.3.1 (module from an algebra hom).** The `A`-module structure on `V` induced by
an algebra homomorphism `ρ : A →ₐ[k] Endₖ(V)`, with action `a • v = ρ(a) v`. It reuses
`Module.compHom` along `ρ.toRingHom` and the tautological action of `Endₖ(V)` on `V`. -/
abbrev ofAlgHom (ρ : A →ₐ[k] Module.End k V) : Module A V :=
  Module.compHom V ρ.toRingHom

/-- The action induced by `ofAlgHom` is `a • v = ρ(a) v`, matching the book's `av := ρ(a)v`. -/
theorem ofAlgHom_smul (ρ : A →ₐ[k] Module.End k V) (a : A) (v : V) :
    letI := ofAlgHom k A V ρ
    a • v = ρ a v := rfl

/-- The module structure reconstructed from `ρ` satisfies the scalar-tower compatibility with the
base field `k`, so it is genuine `k`-linear representation data. The proof uses that `ρ` commutes
with the structure maps (`ρ.commutes`) together with `IsScalarTower.of_algebraMap_smul`. -/
theorem ofAlgHom_isScalarTower (ρ : A →ₐ[k] Module.End k V) :
    letI := ofAlgHom k A V ρ
    IsScalarTower k A V := by
  letI := ofAlgHom k A V ρ
  refine IsScalarTower.of_algebraMap_smul fun r x => ?_
  rw [ofAlgHom_smul k A V ρ (algebraMap k A r) x, ρ.commutes r, Module.algebraMap_end_apply]

/-- **Reverse-then-forward round trip.** Reconstructing the module from `ρ` and then reading off
the book's homomorphism returns `ρ` itself. -/
theorem toAlgHom_ofAlgHom (ρ : A →ₐ[k] Module.End k V) :
    letI := ofAlgHom k A V ρ
    letI := ofAlgHom_isScalarTower k A V ρ
    toAlgHom k A V = ρ := by
  letI := ofAlgHom k A V ρ
  letI := ofAlgHom_isScalarTower k A V ρ
  ext a v
  exact (toAlgHom_apply k A V a v).trans (ofAlgHom_smul k A V ρ a v)

end OfAlgHom

/-! ### Forward-then-reverse round trip -/

section RoundTrip

variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- **Forward-then-reverse round trip.** Reading off the book's homomorphism `ρ = toAlgHom` from a
compatible module and then reconstructing the module returns the original `A`-module structure. -/
theorem ofAlgHom_toAlgHom :
    ofAlgHom k A V (toAlgHom k A V) = (inferInstance : Module A V) := rfl

end RoundTrip

/-! ### The right-module antihomomorphism presentation -/

section RightToAlgHom

variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module Aᵐᵒᵖ V] [IsScalarTower k Aᵐᵒᵖ V]

/-- The algebra homomorphism `Aᵐᵒᵖ →ₐ[k] Endₖ(V)` corresponding to the book's
antihomomorphism `A → End(V)` for a right representation. -/
def rightToAlgHom : Aᵐᵒᵖ →ₐ[k] Module.End k V :=
  toAlgHom k Aᵐᵒᵖ V

/-- The right-action homomorphism evaluates as the abbreviated right action `v a`. -/
@[simp]
theorem rightToAlgHom_apply (a : A) (v : V) :
    rightToAlgHom k A V (MulOpposite.op a) v = MulOpposite.op a • v :=
  rfl

end RightToAlgHom

end Etingof.Representation
