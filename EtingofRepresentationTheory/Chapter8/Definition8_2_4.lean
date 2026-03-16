import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Definition 8.2.4: Ext functors

Let M be a left A-module, P• a projective resolution of M, and N a left A-module.
For i ≥ 0 we define Extⁱ_A(M, N) to be the i-th cohomology of the complex
  0 → Hom_A(P₀, N) → Hom_A(P₁, N) → Hom_A(P₂, N) → ⋯
induced by the resolution P•.

## Mathlib correspondence

This is `Abelian.Ext X Y n` in Mathlib, defined via derived categories. For the module
category `ModuleCat R`, `Abelian.Ext M N n` gives the classical Ext groups.

## Formalization note

Mathlib defines Ext in the general abelian category setting using `SmallShiftedHom` in the
derived category. The module-specific Ext is obtained by specializing to `ModuleCat R`.
-/

/-- The Ext functors, defined as derived functors of Hom, in the sense of
Etingof Definition 8.2.4. In Mathlib, this is `Abelian.Ext` for objects in an abelian
category, specialized to `ModuleCat R` for modules. -/
theorem Etingof.Definition_8_2_4 : (sorry : Prop) := sorry
