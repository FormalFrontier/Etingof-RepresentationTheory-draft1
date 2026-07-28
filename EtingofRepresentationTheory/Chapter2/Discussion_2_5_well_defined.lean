import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.TwoSidedIdeal.Basic

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

/-- The quotient algebra `A/I` of the book, implemented as the quotient by the ring congruence
associated to the two-sided ideal `I`. The congruence relation is additive-coset equality; see
`quotientAlgHom_eq_iff_sub_mem`. -/
abbrev QuotientAlgebra (I : TwoSidedIdeal A) : Type _ := I.ringCon.Quotient

/-- **`A/I` is an algebra.** For a two-sided ideal `I` of an algebra `A`, the quotient `A/I`
(modelled as `I.ringCon.Quotient`) is again a `k`-algebra. The well-definedness of the
multiplication `(a + I)(b + I) := ab + I`, checked by hand in the book using that `I` is both a
left and a right ideal, is precisely the fact that `I.ringCon` is a ring congruence, after which
the algebra structure is automatic. -/
abbrev quotientAlgebraStructure (I : TwoSidedIdeal A) : Algebra k (QuotientAlgebra A I) :=
  inferInstance

/-- The canonical quotient map `A → A/I` is a homomorphism of `k`-algebras. -/
noncomputable def quotientAlgHom (I : TwoSidedIdeal A) : A →ₐ[k] QuotientAlgebra A I :=
  RingCon.mkₐ k I.ringCon

/-- The ring-congruence quotient is exactly the book's additive-coset quotient: two images are
equal precisely when their difference lies in `I`. -/
theorem quotientAlgHom_eq_iff_sub_mem (I : TwoSidedIdeal A) (a b : A) :
    quotientAlgHom k A I a = quotientAlgHom k A I b ↔ a - b ∈ I := by
  change (a : I.ringCon.Quotient) = (b : I.ringCon.Quotient) ↔ a - b ∈ I
  rw [RingCon.eq, I.rel_iff]

/-- Multiplication on the quotient is the operation prescribed in the book:
`π(a) * π(b) = π(ab)`. -/
theorem quotientAlgHom_mul (I : TwoSidedIdeal A) (a b : A) :
    quotientAlgHom k A I a * quotientAlgHom k A I b = quotientAlgHom k A I (a * b) := by
  exact (quotientAlgHom k A I).map_mul a b

/-- The first well-definedness calculation in the book: replacing the left factor by an
additively congruent representative does not change the product. This uses right absorption of
the two-sided ideal. -/
theorem quotientAlgHom_mul_eq_of_sub_mem_left (I : TwoSidedIdeal A) (a a' b : A)
    (h : a' - a ∈ I) :
    quotientAlgHom k A I (a' * b) = quotientAlgHom k A I (a * b) := by
  rw [quotientAlgHom_eq_iff_sub_mem]
  simpa [sub_mul] using I.mul_mem_right (a' - a) b h

/-- The second well-definedness calculation in the book: replacing the right factor by an
additively congruent representative does not change the product. This uses left absorption of
the two-sided ideal. -/
theorem quotientAlgHom_mul_eq_of_sub_mem_right (I : TwoSidedIdeal A) (a b b' : A)
    (h : b' - b ∈ I) :
    quotientAlgHom k A I (a * b') = quotientAlgHom k A I (a * b) := by
  rw [quotientAlgHom_eq_iff_sub_mem]
  simpa [mul_sub] using I.mul_mem_left a (b' - b) h

end QuotientAlgebra

section QuotientRepresentation

variable (A V : Type*) [Ring A] [AddCommGroup V] [Module A V]

/-- **`V/W` is a representation.** If `V` is a representation of `A` (a `Module A V`) and
`W ⊆ V` is a subrepresentation (a `Submodule A V`), then the quotient `V/W` is again a
representation of `A`, with action `a • (v + W) := a • v + W`. -/
abbrev quotientRepresentation (W : Submodule A V) : Module A (V ⧸ W) := inferInstance

/-- The quotient action is the action prescribed in the book:
`a • π(v) = π(a • v)`. -/
theorem quotientMk_smul (W : Submodule A V) (a : A) (v : V) :
    a • (Submodule.Quotient.mk v : V ⧸ W) = Submodule.Quotient.mk (a • v) := by
  exact (Submodule.Quotient.mk_smul W a v).symm

end QuotientRepresentation

section RegularQuotient

variable (A : Type*) [Ring A]

/-- A left ideal of `A` is definitionally an `A`-submodule of the regular representation `A`.
This names the book-to-Mathlib identification used in the final paragraph. -/
abbrev RegularLeftIdeal := Submodule A A

/-- **`A/I` is a representation for a left ideal `I`.** Left ideals of `A` are exactly the
subrepresentations of the regular representation (the `A`-module `A`), so for a left ideal
`I ⊆ A`, modelled as a submodule `I : Submodule A A`, the quotient `A/I` is a representation
of `A`. -/
abbrev regularQuotientRepresentation (I : RegularLeftIdeal A) : Module A (A ⧸ I) := inferInstance

end RegularQuotient

end Etingof
