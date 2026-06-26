import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Example 8.1.7: Duality between projective and injective modules

Let `A` be an algebra and `P` be a left `A`-module. Then `P` is projective if and only if
`P*` is an injective right `A`-module.

## Formalization

The dual space `P* = Hom_k(P, k) = Module.Dual k P` carries the **contragredient** right
`A`-module structure: for `φ : P*` and `a : A`,
`(φ ⬝ a)(p) = φ(a • p)`.
We model a right `A`-module as a left `Aᵐᵒᵖ`-module, so this is the
`Module Aᵐᵒᵖ (Module.Dual k P)` instance `Etingof.Example817.contragredient` below, with
defining equation `Etingof.Example817.contragredient_smul_apply`.

The statement asserts the genuine biconditional over a general algebra `A` (not merely a
field, where every module is trivially injective). The single standing hypothesis
`[FiniteDimensional k A]` is the book's running convention that algebras are
finite dimensional, and it is *mathematically necessary*, not decorative:

* The contragredient duality `Hom_k(-, k)` is an exact contravariant functor (as `k` is a
  field), so by Lambek's theorem `P*` is injective as a right `A`-module **iff `P` is flat**
  as a left `A`-module — for an arbitrary algebra `A` and arbitrary `P`.
* A finite dimensional algebra is left (and right) perfect, and over a left perfect ring
  *every* flat left module is projective (Bass). Hence `P` projective ⟺ `P` flat ⟺ `P*`
  injective, for every left `A`-module `P`.
* Without `[FiniteDimensional k A]` the equivalence is false: it degrades to
  "`P*` injective ⟺ `P` flat", and flat does not imply projective in general.

## Proof status

The proof requires two pieces of homological infrastructure not currently in Mathlib:
Lambek's theorem for the `k`-linear dual (`P` flat ⟺ `Module.Dual k P` injective as a
right module over an injective cogenerator) and Bass's characterization of perfect rings
(over a left perfect ring, flat ⟹ projective). It is left as a `sorry` and tracked for
follow-up; the *statement* is the faithful content of Example 8.1.7.
-/

namespace Etingof.Example817

open MulOpposite

variable (k : Type*) [Field k]
variable (A : Type*) [Ring A] [Algebra k A]
variable (P : Type*) [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]

/-- The **contragredient** right `A`-action on the dual space `P* = Module.Dual k P`,
modelled as a left `Aᵐᵒᵖ`-module: `(a • φ)(p) = φ(unop a • p)`.

This is the genuine right `A`-module structure of Example 8.1.7, not merely the underlying
`k`-vector space: see `contragredient_smul_apply` for the defining equation. -/
noncomputable instance contragredient : Module Aᵐᵒᵖ (Module.Dual k P) where
  smul a φ := φ ∘ₗ Algebra.lsmul k k P a.unop
  one_smul φ := by
    ext p
    change φ ((1 : Aᵐᵒᵖ).unop • p) = φ p
    rw [MulOpposite.unop_one, one_smul]
  mul_smul a b φ := by
    ext p
    change φ ((a * b).unop • p) = φ (b.unop • a.unop • p)
    rw [MulOpposite.unop_mul, mul_smul]
  smul_zero a := by ext p; rfl
  zero_smul φ := by
    ext p
    change φ ((0 : Aᵐᵒᵖ).unop • p) = (0 : Module.Dual k P) p
    rw [MulOpposite.unop_zero, zero_smul, map_zero, LinearMap.zero_apply]
  smul_add a φ ψ := by ext p; rfl
  add_smul a b φ := by
    ext p
    change φ ((a + b).unop • p) = φ (a.unop • p) + φ (b.unop • p)
    rw [MulOpposite.unop_add, add_smul, map_add]

/-- Defining equation of the contragredient action: `(a • φ)(p) = φ(unop a • p)`. -/
@[simp]
theorem contragredient_smul_apply (a : Aᵐᵒᵖ) (φ : Module.Dual k P) (p : P) :
    (a • φ) p = φ (a.unop • p) :=
  rfl

end Etingof.Example817

/-- **Example 8.1.7.** Let `A` be an algebra and `P` be a left `A`-module. Then `P` is
projective if and only if its dual `P* = Module.Dual k P` is injective as a right `A`-module
(modelled as a left `Aᵐᵒᵖ`-module, with the contragredient action `(a • φ)(p) = φ(unop a • p)`
from `Etingof.Example817.contragredient`).

The hypothesis `[FiniteDimensional k A]` is the book's standing convention and is necessary:
without it the right-hand side characterizes flatness of `P` rather than projectivity. See the
module docstring for the mathematical content and the (deferred) proof strategy. -/
theorem Etingof.Example_8_1_7
    (k : Type*) [Field k]
    (A : Type*) [Ring A] [Algebra k A] [FiniteDimensional k A]
    (P : Type*) [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P] :
    Module.Projective A P ↔ Module.Injective Aᵐᵒᵖ (Module.Dual k P) := by
  sorry
