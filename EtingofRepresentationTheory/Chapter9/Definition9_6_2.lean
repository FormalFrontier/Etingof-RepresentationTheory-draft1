import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Generator.Basic

/-!
# Definition 9.6.2: Projective generator (progenerator)

An object P in an abelian category is a **projective generator** (or **progenerator**)
if P is projective and every object X in the category is a quotient of a direct sum of
copies of P.

Example: the free module A (the algebra itself) is a projective generator in the
category of finite dimensional A-modules.

## Mathlib correspondence

Mathlib has `CategoryTheory.Projective` and `CategoryTheory.IsGenerator` separately.
A progenerator would combine both conditions.
-/

/-- A projective generator (progenerator) in the sense of Etingof Definition 9.6.2.
An object that is projective and generates the category. -/
def Etingof.Progenerator : (sorry : Prop) := sorry
