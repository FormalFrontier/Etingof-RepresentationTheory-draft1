import Mathlib
import EtingofRepresentationTheory.Chapter7.Definition7_8_6

/-!
# Problem 7.8.5: Long exact sequence of cohomology from a subcomplex

**Problem 7.8.5.** Let `D_•` be a complex of abelian groups with differentials `d_i`,
let `C_•` be a subcomplex of `D_•`, and let `E_• = D_•/C_•` be the quotient complex.
Define the connecting homomorphism `c_i : H^i(E) → H^{i+1}(C)` via the snake-lemma
diagram chase. (i) Show `c_i` is well defined. (ii) Show that the sequence

`… H^{i-1}(E) → H^i(C) → H^i(D) → H^i(E) → H^{i+1}(C) …`

is exact, where the connecting maps are the `c_i`, and the middle maps are induced by
`C_i → D_i → E_i`.

## Formalization

A subcomplex `C_• ⊆ D_•` with quotient `E_• = D_•/C_•` is exactly a short exact
sequence of complexes `0 → C_• → D_• → E_• → 0`, i.e. a `ShortComplex` `S` of
homological complexes with `S.ShortExact`. Part (i): the connecting homomorphism is
`S.ShortExact.δ` (built via the snake lemma), which is a well-defined morphism by
construction. Part (ii): the long exact sequence of cohomology, whose exactness at the
three positions is witnessed by `hS.homology_exact₁ / homology_exact₂ / homology_exact₃`.
-/

open CategoryTheory

/-- The connecting homomorphism `c_i : H^i(E) → H^{i+1}(C)` of Problem 7.8.5, for a
short exact sequence `0 → C → D → E → 0` of complexes of abelian groups. This is the
snake-lemma connecting map `S.ShortExact.δ`; part (i) (well-definedness) is the fact
that it is a genuine morphism. -/
noncomputable def Etingof.Problem7_8_5_connecting
    {S : ShortComplex (HomologicalComplex (ModuleCat.{0} ℤ) (ComplexShape.up ℤ))}
    (hS : S.ShortExact) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  hS.δ i j hij

/-- Problem 7.8.5(ii): the long exact sequence of cohomology of a short exact sequence
`0 → C → D → E → 0` of complexes of abelian groups is exact at the three positions
`H^j(C)`, `H^i(D)`, `H^i(E)` around indices `i` and `j = i+1`. -/
theorem Etingof.Problem7_8_5
    {S : ShortComplex (HomologicalComplex (ModuleCat.{0} ℤ) (ComplexShape.up ℤ))}
    (hS : S.ShortExact) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact ∧
    (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i)
      (by rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact ∧
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact :=
  -- The three exactness statements are exactly Mathlib's long-exact-homology-sequence
  -- lemmas for a short exact sequence of homological complexes (the snake-lemma chase).
  ⟨hS.homology_exact₁ i j hij, hS.homology_exact₂ i, hS.homology_exact₃ i j hij⟩
