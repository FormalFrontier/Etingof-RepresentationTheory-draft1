import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Quotient
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Basic

/-!
# Example 7.1.3: Examples of Categories

1. The category **Sets** of sets (morphisms are arbitrary maps).
2. The categories **Groups**, **Rings** (morphisms are homomorphisms).
3. The category Vect_k of vector spaces over a field k (morphisms are linear maps).
4. The category Rep(A) of representations of an algebra A (= A-mod).
5. The category of topological spaces (morphisms are continuous maps).
6. The homotopy category of topological spaces (morphisms are homotopy classes of
   continuous maps).

## Mathlib correspondence

Items 1–5 exist in Mathlib as bundled categories (`Type*`, `GrpCat`, `RingCat`,
`ModuleCat k`, `ModuleCat A`, `TopCat`).

Item 6, the homotopy category of topological spaces, is **not** a bundled category
in Mathlib. (Mathlib's `HomotopyCategory` is the homotopy category of chain
complexes, unrelated to spaces.) We construct it here as the categorical quotient
`CategoryTheory.Quotient` of `TopCat` by the homotopy relation on morphisms:
Mathlib provides the homotopy relation `ContinuousMap.Homotopic`, proven to be an
equivalence (`Homotopic.equivalence`) compatible with composition (`Homotopic.comp`).
Those two facts make it a `CategoryTheory.Congruence`, so the quotient's morphisms
`X ⟶ Y` are exactly homotopy classes of continuous maps.
-/

open CategoryTheory

/-- The category of types (Sets). (Etingof Example 7.1.3(1)) -/
example : Category (Type*) := inferInstance

/-- The category of groups. (Etingof Example 7.1.3(2)) -/
example : Category GrpCat := inferInstance

/-- The category of rings. (Etingof Example 7.1.3(2)) -/
example : Category RingCat := inferInstance

/-- The category of k-vector spaces (= k-modules). (Etingof Example 7.1.3(3)) -/
example (k : Type*) [Field k] : Category (ModuleCat k) := inferInstance

/-- The category of left A-modules (= Rep(A)). (Etingof Example 7.1.3(4)) -/
example (A : Type*) [Ring A] : Category (ModuleCat A) := inferInstance

/-- The category of topological spaces. (Etingof Example 7.1.3(5)) -/
example : Category TopCat := inferInstance

/-- The homotopy relation on morphisms of `TopCat`: two continuous maps are related
iff they are homotopic. -/
def homotopyRel : HomRel TopCat := fun _ _ f g => ContinuousMap.Homotopic f.hom g.hom

/-- Homotopy is a congruence on `TopCat`: it is an equivalence on every hom-set and
compatible with composition on both sides. This guarantees that the morphisms of the
quotient category below are exactly homotopy classes of continuous maps. -/
instance : Congruence homotopyRel where
  equivalence :=
    { refl := fun f => ContinuousMap.Homotopic.refl f.hom
      symm := fun h => ContinuousMap.Homotopic.symm h
      trans := fun h₁ h₂ => ContinuousMap.Homotopic.trans h₁ h₂ }
  comp_left := by
    intro X Y Z f g g' h
    exact ContinuousMap.Homotopic.comp h (ContinuousMap.Homotopic.refl f.hom)
  comp_right := by
    intro X Y Z f f' g h
    exact ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl g.hom) h

/-- The homotopy category of topological spaces: the quotient of `TopCat` by the
homotopy relation. Objects are topological spaces; morphisms `X ⟶ Y` are homotopy
classes of continuous maps. (Etingof Example 7.1.3(6)) -/
abbrev HomotopyTopCat := CategoryTheory.Quotient homotopyRel

/-- The homotopy category of topological spaces is a category. (Etingof Example 7.1.3(6)) -/
example : Category HomotopyTopCat := inferInstance
