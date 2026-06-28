import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Ring.Opposite

/-!
# Remark 2.3.2: left and right modules coincide over a commutative ring

Etingof remarks that if `A` is a **commutative** ring and `M` is a left `A`-module, then `M`
can be regarded as a right `A`-module by setting `m a := a m`, and conversely any right
`A`-module is a left `A`-module. For this reason one does not distinguish between left and
right modules over a commutative ring, and simply calls them `A`-modules.

In Mathlib the convention is that `Module A M` is a *left* module, and a *right* `A`-module is
encoded as a left module over the opposite ring, `Module Aᵐᵒᵖ M`. The remark is therefore the
statement that, over a commutative ring, the two notions are interchangeable with the scalar
action `m • op a = a • m`. We make this precise in both directions:

* `Etingof.rightModuleOfLeft`: from a left `A`-module structure, the right `A`-module structure
  (`Module Aᵐᵒᵖ M`) with action `op a • m = a • m`, witnessed by `rightModuleOfLeft_smul`.
* `Etingof.leftModuleOfRight`: from a right `A`-module structure (`Module Aᵐᵒᵖ M`), the left
  `A`-module structure with action `a • m = op a • m`, witnessed by `leftModuleOfRight_smul`.

Both directions reuse `Module.compHom` along the ring isomorphism `Aᵐᵒᵖ ≃+* A` available for a
commutative ring (built from `RingHom.fromOpposite`/`RingHom.toOpposite`, which exist precisely
because every pair of elements commutes).
-/

namespace Etingof

variable (A M : Type*) [CommRing A] [AddCommGroup M]

/-- The ring homomorphism `Aᵐᵒᵖ →+* A` sending `op a ↦ a`, available because `A` is commutative.
It is the identity of `A` viewed as a hom out of the opposite ring. -/
def unopRingHom : Aᵐᵒᵖ →+* A :=
  (RingHom.id A).fromOpposite fun x y => mul_comm x y

/-- The ring homomorphism `A →+* Aᵐᵒᵖ` sending `a ↦ op a`, available because `A` is commutative. -/
def opRingHom : A →+* Aᵐᵒᵖ :=
  (RingHom.id A).toOpposite fun x y => mul_comm x y

/-- **Remark 2.3.2 (left ⇒ right).** A left module `M` over a commutative ring `A` is canonically
a right `A`-module, encoded as a module over the opposite ring `Aᵐᵒᵖ`, with the scalar action
`m a := a m`. -/
abbrev rightModuleOfLeft [Module A M] : Module Aᵐᵒᵖ M :=
  Module.compHom M (unopRingHom A)

/-- The right action produced by `rightModuleOfLeft` is `op a • m = a • m`, i.e. `m a = a m` as
in the book. -/
theorem rightModuleOfLeft_smul [Module A M] (a : A) (m : M) :
    letI := rightModuleOfLeft A M
    (MulOpposite.op a) • m = a • m := rfl

/-- **Remark 2.3.2 (right ⇒ left).** A right module `M` over a commutative ring `A` (a module over
the opposite ring `Aᵐᵒᵖ`) is canonically a left `A`-module, with the scalar action `a m := m a`. -/
abbrev leftModuleOfRight [Module Aᵐᵒᵖ M] : Module A M :=
  Module.compHom M (opRingHom A)

/-- The left action produced by `leftModuleOfRight` is `a • m = op a • m`, i.e. `a m = m a`. -/
theorem leftModuleOfRight_smul [Module Aᵐᵒᵖ M] (a : A) (m : M) :
    letI := leftModuleOfRight A M
    a • m = (MulOpposite.op a) • m := rfl

end Etingof
