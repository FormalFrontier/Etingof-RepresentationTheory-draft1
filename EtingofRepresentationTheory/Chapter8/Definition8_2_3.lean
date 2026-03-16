import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Definition 8.2.3: Tor functors

Let M be a right A-module, P• a projective resolution of M, and N a left A-module.
For i ≥ 0 we define Torᵢᴬ(M, N) to be the i-th homology of the complex
  ⋯ → P₂ ⊗_A N → P₁ ⊗_A N → P₀ ⊗_A N → 0
induced by the resolution P•.

## Mathlib correspondence

This is `CategoryTheory.Tor n` in Mathlib, defined as the left derived functors of the
tensor product. For the module category `ModuleCat R` over a commutative ring R,
`Tor n` gives the classical Tor functors. The definition requires the category to be
monoidal, abelian, monoidal-preadditive, and to have projective resolutions.
-/

open CategoryTheory in
/-- The Tor functors, defined as derived functors of the tensor product, in the sense of
Etingof Definition 8.2.3. In Mathlib, this is `CategoryTheory.Tor C n`, the left derived
functors of `tensoringLeft`. -/
noncomputable abbrev Etingof.Tor (C : Type*) [Category C]
    [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [HasProjectiveResolutions C]
    (n : Nat) : C ⥤ C ⥤ C :=
  CategoryTheory.Tor C n
