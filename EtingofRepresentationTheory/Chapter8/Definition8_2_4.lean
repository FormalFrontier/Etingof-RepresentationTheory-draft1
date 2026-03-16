import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Definition 8.2.4: Ext functors

Let M be a left A-module, P• a projective resolution of M, and N a left A-module.
For i ≥ 0 we define Extⁱ_A(M, N) to be the i-th cohomology of the complex
  0 → Hom_A(P₀, N) → Hom_A(P₁, N) → Hom_A(P₂, N) → ⋯
induced by the resolution P•.

## Mathlib correspondence

This is `CategoryTheory.Abelian.Ext X Y n` in Mathlib, defined via shifted morphisms in the
derived category. For the module category `ModuleCat R`, `Abelian.Ext M N n` gives the
classical Ext groups. The definition requires `HasExt C`, which asserts that the relevant
localized shifted hom types are small.
-/

/-- The Ext functors, defined as derived functors of Hom, in the sense of
Etingof Definition 8.2.4. In Mathlib, this is `CategoryTheory.Abelian.Ext` for objects in
an abelian category with `HasExt`, specialized to `ModuleCat R` for modules. -/
noncomputable abbrev Etingof.Ext {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] [CategoryTheory.HasExt C]
    (M N : C) (n : ℕ) : Type _ :=
  CategoryTheory.Abelian.Ext M N n
