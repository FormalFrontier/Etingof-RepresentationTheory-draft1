import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Algebra.Defs

/-!
# Definition 3.3.2: Dual Representation

Let `V` be a representation of any algebra `A`. Then the **dual representation** `V*` is the
representation of the opposite algebra `Aᵐᵒᵖ` (or, equivalently, right `A`-module) with the
action

  `(f · a)(v) := f(a v)`.

## Mathlib correspondence

Following the project convention (see `Definition3_1_1.lean`), a representation of the
algebra `A` is modeled as an `A`-module `V` (over a base ring `k`, with the `A`- and
`k`-actions commuting, i.e. `SMulCommClass A k V`). The carrier of the dual representation
is the `k`-linear dual `Module.Dual k V = V →ₗ[k] k`.

The *defining data* of Definition 3.3.2 is the contragredient action, which makes
`Module.Dual k V` a genuine `Aᵐᵒᵖ`-module: an element `MulOpposite.op a` of `Aᵐᵒᵖ` acts on a
functional `f` by precomposition with `v ↦ a • v`, i.e. `(op a • f)(v) = f(a • v)`. This is
exactly the action `(f · a)(v) = f(a v)` of Etingof Definition 3.3.2, read as a left module
over `Aᵐᵒᵖ`. We construct this `Module Aᵐᵒᵖ` structure explicitly below — the bare
`Module.Dual k V` alone (the dual *vector space*) does not carry it.
-/

namespace Etingof

section DualRepresentation

variable (k A V : Type*)
    [CommRing k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [SMulCommClass A k V]

/-- The dual representation in the sense of Etingof Definition 3.3.2.

Given a representation `V` of the algebra `A` (an `A`-module `V` over the base ring `k`,
with commuting actions), its dual representation `V*` has carrier the `k`-linear dual
`Module.Dual k V`, equipped with the contragredient `Aᵐᵒᵖ`-action `(op a • f)(v) = f(a • v)`
constructed in `Etingof.instModuleMulOppositeDual` below. -/
abbrev DualRepresentation (k A V : Type*)
    [CommRing k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [SMulCommClass A k V] : Type _ :=
  Module.Dual k V

/-- The contragredient action of `Aᵐᵒᵖ` on the dual space: `MulOpposite.op a` sends a
functional `f` to `f` precomposed with `v ↦ a • v`, i.e. `(op a • f)(v) = f(a • v)`. This is
the action `(f · a)(v) = f(a v)` of Definition 3.3.2. -/
instance instSMulMulOppositeDual : SMul Aᵐᵒᵖ (Module.Dual k V) where
  smul a f := f.comp (DistribSMul.toLinearMap k V a.unop)

variable {k A V}

omit [Algebra k A] in
/-- The defining equation of Definition 3.3.2: the `Aᵐᵒᵖ`-action on the dual representation
is the contragredient action `(op a · f)(v) = f(a · v)`. -/
@[simp]
theorem dualRepresentation_smul_apply (a : Aᵐᵒᵖ) (f : Module.Dual k V) (v : V) :
    (a • f) v = f (a.unop • v) :=
  rfl

variable (k A V)

/-- The dual representation is a genuine left module over the opposite algebra `Aᵐᵒᵖ`,
carrying the contragredient action of Definition 3.3.2. -/
instance instModuleMulOppositeDual : Module Aᵐᵒᵖ (Module.Dual k V) where
  one_smul f := by ext v; simp
  mul_smul a b f := by ext v; simp [mul_smul]
  smul_zero a := by ext v; simp
  smul_add a f g := by ext v; simp
  add_smul a b f := by ext v; simp [add_smul]
  zero_smul f := by ext v; simp

/-- The dual representation `V*` is a representation of `Aᵐᵒᵖ`: the contragredient action
equips `Module.Dual k V` with a genuine `Aᵐᵒᵖ`-module structure (not merely the dual vector
space). -/
example : Module Aᵐᵒᵖ (DualRepresentation k A V) := inferInstance

end DualRepresentation

end Etingof
