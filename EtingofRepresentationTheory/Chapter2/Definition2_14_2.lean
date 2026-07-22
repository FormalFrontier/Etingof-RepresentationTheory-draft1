import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Definition 2.14.2: Dual Representation of a Lie Algebra

The **dual representation** `V*` to a representation `V` of a Lie algebra `𝔤` is the
dual space `V*` to `V` with `ρ_{V*}(x) = -ρ_V(x)*`.

## Mathlib correspondence

The carrier is `Module.Dual k V`. Its Lie-module structure is the *contragredient*
action provided by `Module.Dual.instLieRingModule` / `Module.Dual.instLieModule`
(`Mathlib.Algebra.Lie.Basic`): for `x : L` and `f : V*`,
`(x · f)(v) = -f(x · v)`, i.e. `ρ_{V*}(x) = -ρ_V(x)*`. Because
`LieDualRepresentation` is an `abbrev` for `Module.Dual k V = V →ₗ[k] k`, those
instances apply to it directly, so the alias genuinely carries the dual
*representation* structure (not merely the dual vector space).
-/

/-- The dual of a Lie algebra representation, in the sense of Etingof Definition 2.14.2.
The Lie action on `V*` is the contragredient one: `(x · f)(v) = -f(x · v)`.
It is the dual space `Module.Dual k V` equipped with the contragredient
`LieRingModule`/`LieModule` structure from `Mathlib.Algebra.Lie.Basic`. -/
abbrev Etingof.LieDualRepresentation (k : Type*) (L : Type*) (V : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V] :=
  Module.Dual k V

namespace Etingof

variable (k : Type*) (L : Type*) (V : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

/-- The dual representation is a Lie module over `L`: the contragredient action
makes `Module.Dual k V` a genuine representation of `L`. -/
example : LieRingModule L (LieDualRepresentation k L V) := inferInstance

/-- The dual representation is a Lie module over the base ring `k` as well. -/
example : LieModule k L (LieDualRepresentation k L V) := inferInstance

variable {k L V}

/-- The defining equation of Definition 2.14.2: the Lie action on the dual
representation is the contragredient action `ρ_{V*}(x) = -ρ_V(x)*`, i.e.
`(x · f)(v) = -f(x · v)`. -/
@[simp]
theorem lieDualRepresentation_lie_apply
    (x : L) (f : LieDualRepresentation k L V) (v : V) :
    (⁅x, f⁆ : LieDualRepresentation k L V) v = - f ⁅x, v⁆ :=
  Module.Dual.lie_apply x v f

end Etingof
