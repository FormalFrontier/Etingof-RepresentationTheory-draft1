import Mathlib.Algebra.Category.Grp.Basic

/-!
# Example 7.1.5: AbelianGroups as Full Subcategory of Groups

The category **AbelianGroups** is a full subcategory of the category **Groups**.

## Mathlib correspondence

Mathlib has `CommGrpCat` (= abelian groups) and `GrpCat`. The forgetful functor
`forget₂ CommGrpCat GrpCat` realizes the full subcategory relationship: it is
fully faithful (`Functor.Full` + `Functor.Faithful`), which is exactly the
statement that abelian groups form a full subcategory of groups.
-/

open CategoryTheory

/-- The forgetful functor from abelian groups to groups is full. (Etingof Example 7.1.5) -/
example : (forget₂ CommGrpCat GrpCat).Full := inferInstance

/-- The forgetful functor from abelian groups to groups is faithful. (Etingof Example 7.1.5) -/
example : (forget₂ CommGrpCat GrpCat).Faithful := inferInstance

/-- AbelianGroups is a full subcategory of Groups: the forgetful functor
`forget₂ CommGrpCat GrpCat` is fully faithful. (Etingof Example 7.1.5) -/
noncomputable example : (forget₂ CommGrpCat GrpCat).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _
