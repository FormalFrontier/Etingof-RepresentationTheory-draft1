import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Discussion 2.5: Well-definedness of quotient algebras and quotient representations

The prose following Definition 2.5 checks three facts that the book establishes by hand and
that Mathlib supplies through its quotient infrastructure:

* If `I ⊆ A` is a (two-sided) ideal, then `A/I` is again an algebra. The book verifies that the
  product `(a + I)(b + I) := ab + I` is well defined, using that `I` is both a left and a right
  ideal. In Mathlib this well-definedness is exactly the statement that `I.ringCon` is a ring
  congruence, and the quotient `A ⧸ I` (modelled by `I.ringCon.Quotient`) then carries a `Ring`
  and an `Algebra k` structure automatically.
* If `V` is a representation of `A` and `W ⊆ V` is a subrepresentation, then `V/W` is again a
  representation, with `ρ_{V/W}(a)(v + W) := ρ_V(a)v + W`. In Mathlib this is the `A`-module
  structure on `V ⧸ W` for a submodule `W : Submodule A V`.
* Left ideals of `A` are the subrepresentations of the regular representation, so for a left
  ideal `I ⊆ A` the quotient `A/I` is a representation of `A`.

Each of these is `inferInstance` once the objects are phrased in Mathlib's language.
-/

namespace Etingof

section QuotientAlgebra

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

/-- **`A/I` is an algebra.** For a two-sided ideal `I` of an algebra `A`, the quotient `A/I`
(modelled as `I.ringCon.Quotient`) is again a `k`-algebra. The well-definedness of the
multiplication `(a + I)(b + I) := ab + I` — checked by hand in the book using that `I` is both a
left and a right ideal — is precisely the fact that `I.ringCon` is a ring congruence, after which
the algebra structure is automatic. -/
example (I : TwoSidedIdeal A) : Algebra k I.ringCon.Quotient := inferInstance

/-- The canonical quotient map `A → A/I` is a homomorphism of `k`-algebras. -/
noncomputable example (I : TwoSidedIdeal A) : A →ₐ[k] I.ringCon.Quotient :=
  RingCon.mkₐ k I.ringCon

end QuotientAlgebra

section QuotientRepresentation

variable (A V : Type*) [Ring A] [AddCommGroup V] [Module A V]

/-- **`V/W` is a representation.** If `V` is a representation of `A` (a `Module A V`) and
`W ⊆ V` is a subrepresentation (a `Submodule A V`), then the quotient `V/W` is again a
representation of `A`, with action `a • (v + W) := a • v + W`. -/
example (W : Submodule A V) : Module A (V ⧸ W) := inferInstance

end QuotientRepresentation

section RegularQuotient

variable (A : Type*) [Ring A]

/-- **`A/I` is a representation for a left ideal `I`.** Left ideals of `A` are exactly the
subrepresentations of the regular representation (the `A`-module `A`), so for a left ideal
`I ⊆ A`, modelled as a submodule `I : Submodule A A`, the quotient `A/I` is a representation
of `A`. -/
example (I : Submodule A A) : Module A (A ⧸ I) := inferInstance

end RegularQuotient

end Etingof
