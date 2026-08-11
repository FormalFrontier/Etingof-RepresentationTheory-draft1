import EtingofRepresentationTheory.Chapter2.Definition2_2_2

/-!
# Proposition 2.2.3: Uniqueness of Unit

If a unit exists in an algebra, it is unique.

**Proof.** Let 1, 1' be two units. Then 1 = 1·1' = 1'. □

The algebra here is the potentially non-unital algebra of Definition 2.2.1, and a unit is the
two-sided-identity predicate of Definition 2.2.2. Thus the statement compares two arbitrary
elements satisfying that predicate; it does not presuppose a canonical `1`.
-/

namespace Etingof

/-- **Proposition 2.2.3.** Any two units in a possibly non-unital associative algebra are equal. -/
theorem Proposition_2_2_3 (k : Type*) {A : Type*} [Field k] [AddCommGroup A] [Module k A]
    [AssociativeAlgebra k A] {e e' : A} (he : AssociativeAlgebra.IsUnit k e)
    (he' : AssociativeAlgebra.IsUnit k e') : e = e' :=
  AssociativeAlgebra.isUnit_unique k he he'

end Etingof
