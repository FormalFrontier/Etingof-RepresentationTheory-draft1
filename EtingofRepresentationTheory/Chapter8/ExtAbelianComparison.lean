import EtingofRepresentationTheory.Chapter8.HomComplexHomologyK
import EtingofRepresentationTheory.Chapter8.Definition8_2_4
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# The comparison isomorphism `Ext ≃ₗ[k] Extₖ`

Problem 8.2.8 (`Ext` half) proves a Künneth formula for the `ModuleCat k`-valued
left-derived-functor `Etingof.Extₖ`, but its top-level statement `Problem_8_2_8_ext` is phrased
with the `AddCommGroup`-
valued derived-category `Etingof.Ext = CategoryTheory.Abelian.Ext`. This file bridges the two with a
`k`-linear isomorphism

```
Etingof.extAbelianIsoExtₖ (P : ProjectiveResolution M) (n : ℕ) :
    Etingof.Ext M N n ≃ₗ[k] Etingof.Extₖ k A M N n
```

for a `k`-algebra `A` over a field `k` and left `A`-modules `M`, `N`.

## Construction

Both sides compute `Extⁿ_A(M, N)` as the cohomology of `Hom_A(P•, N)`; the bridge chains four
additive isomorphisms, then upgrades the composite to `k`-linear.

1. `P.extAddEquivCohomologyClass` — `Abelian.Ext M N n ≃+ CohomologyClass P.cochainComplex N[0] n`
   (Mathlib).
2. `(CochainComplex.HomComplex.homologyAddEquiv _ _ _).symm` — the cohomology classes are the
   degree-`n` homology of the `AddCommGrp`-valued `HomComplex` (Mathlib).
3. `Etingof.homComplexHomologyAddEquivₖ` — that homology identifies additively with the degree-`n`
   homology of the `ModuleCat k`-valued `linearYonedaObj` (the crux of #6897).
4. `(Etingof.extIsoCohomologyHomₖ …).symm` — which is `Etingof.Extₖ`
   (`ProjectiveResolution.isoExt`).

Step 4 is a `ModuleCat k` iso, hence `k`-linear; the composite's `k`-linearity is proved on
generators by tracking the scalar action, which on `Abelian.Ext` is postcomposition with `r • 𝟙 N`
(`Ext.smul_eq_comp_mk₀`) and on each `Hom(P•, N)` presentation is the same postcomposition.
-/

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace HomologicalComplex

variable {R : Type*} [Semiring R] {C : Type*} [Category C] [Preadditive C]
  [CategoryTheory.Linear R C] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

set_option backward.isDefEq.respectTransparency false in
/-- `homologyMap` is `R`-linear in the morphism: `homologyMap (r • φ) = r • homologyMap φ`. The
`R`-scalar analogue of `HomologicalComplex.homologyMap_add`, mirroring
`ShortComplex.homologyMap_smul` (Mathlib records this as a TODO in `Algebra/Homology/Linear`). -/
lemma homologyMap_smul (r : R) (φ : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    homologyMap (r • φ) i = r • homologyMap φ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_smul]
  rfl

end HomologicalComplex

namespace Etingof

universe u

variable (k : Type u) [Field k]
variable {A : Type u} [Ring A] [Algebra k A]
variable {M : ModuleCat.{u} A} (N : ModuleCat.{u} A) (P : ProjectiveResolution M)

/-- **The additive comparison `Ext ≃+ Extₖ`.** For a projective resolution `P` of `M`, the
derived-category `Ext` group `Abelian.Ext M N n` identifies additively with the left-derived-functor
`ModuleCat k`-valued `Extₖ k A M N n`, both computing the cohomology of `Hom_A(P•, N)`. The chain of
the four additive isomorphisms of the file docstring. -/
noncomputable def extAbelianAddEquivExtₖ (n : ℕ) :
    Etingof.Ext M N n ≃+ Etingof.Extₖ k A M N n :=
  (P.extAddEquivCohomologyClass.trans
    (CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) (n : ℤ)).symm).trans
    ((homComplexHomologyAddEquivₖ k N P n).trans
      (extIsoCohomologyHomₖ k A M N P n).symm.toLinearEquiv.toAddEquiv)

/-- **Fact 1 (the "clean half").** On the `ModuleCat k`-valued homology
`(P.complex.linearYonedaObj k N).homology n`, the module scalar `r • v` coincides with applying
`homologyMap` of the degreewise scalar endomorphism `r • 𝟙` of the complex. This packages the
`k`-linearity of the `linearYonedaObj` homology for the `map_smul'` proof of `extAbelianIsoExtₖ`. -/
lemma smul_homology_eq (r : k) (n : ℕ)
    (v : (P.complex.linearYonedaObj k N).homology n) :
    r • v = (HomologicalComplex.homologyMap (r • 𝟙 (P.complex.linearYonedaObj k N)) n).hom v := by
  rw [HomologicalComplex.homologyMap_smul, HomologicalComplex.homologyMap_id,
    ← ModuleCat.lsmul_eq_smul_id]
  rfl

/-- **The comparison isomorphism `Ext ≃ₗ[k] Extₖ`.** The `k`-linear upgrade of
`extAbelianAddEquivExtₖ`: for a projective resolution `P` of `M`, the derived-category `Ext` group
`Abelian.Ext M N n` is `k`-linearly isomorphic to the left-derived-functor `Extₖ k A M N n`. The
underlying additive equivalence is the sorry-free four-step chain `extAbelianAddEquivExtₖ`; this is
the version consumed by `Problem_8_2_8_ext` (#6898) to transport the `Extₖ` Künneth isomorphism to
the `Etingof.Ext` statement.

The scalar action on `Abelian.Ext M N n` is postcomposition with `r • 𝟙 N`
(`CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀`); on `Extₖ k A M N n : ModuleCat k` it is the module
scalar. Each of the four steps intertwines these actions (step 4 is a `ModuleCat k` iso, hence
`k`-linear; steps 1–3 are the `k`-linear `Hom(P•, N)` structure viewed additively), so the composite
`map_smul'` holds. Discharging it requires naturality-in-`N` of `extAddEquivCohomologyClass`,
`homologyAddEquiv`, and `homComplexHomologyAddEquivₖ` under the endomorphism `r • 𝟙 N`, tracked as
the follow-up to #6901. -/
noncomputable def extAbelianIsoExtₖ (n : ℕ) :
    Etingof.Ext M N n ≃ₗ[k] Etingof.Extₖ k A M N n where
  __ := extAbelianAddEquivExtₖ k N P n
  map_smul' := by
    intro r x
    -- Steps 1–3 of the chain, landing in the `ModuleCat k` homology of `linearYonedaObj`.
    set e123 : Etingof.Ext M N n ≃+ (P.complex.linearYonedaObj k N).homology n :=
      (P.extAddEquivCohomologyClass.trans
        (CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)
            (n : ℤ)).symm).trans
        (homComplexHomologyAddEquivₖ k N P n) with he123
    -- Step 4 as a `k`-linear equivalence `Hⁿ(Hom(P•,N)) ≃ₗ[k] Extₖ`.
    set step4 : (P.complex.linearYonedaObj k N).homology n ≃ₗ[k] Etingof.Extₖ k A M N n :=
      (extIsoCohomologyHomₖ k A M N P n).symm.toLinearEquiv with hstep4
    -- `k`-linearity of the composite reduces to `k`-linearity of `e123`, since step 4 is linear.
    -- By `smul_homology_eq` (fact 1) the target module scalar `r • e123 y` is
    -- `homologyMap (r • 𝟙) n` applied to `e123 y`, so what remains is the purely categorical
    -- naturality of `e123` in `N` under the endomorphism `r • 𝟙 N`: it must intertwine the source
    -- scalar (postcomposition with `mk₀ (r • 𝟙 N)`, `Ext.smul_eq_comp_mk₀`) with `homologyMap` of
    -- the degreewise scalar `r • 𝟙` on `linearYonedaObj`. Residual tracing through the three chain
    -- steps (`extAddEquivCohomologyClass`, `homologyAddEquiv`, `homComplexHomologyAddEquivₖ`);
    -- follow-up to #6935.
    have hnat : ∀ y, e123 (r • y)
        = (HomologicalComplex.homologyMap (r • 𝟙 (P.complex.linearYonedaObj k N)) n).hom
            (e123 y) := by
      sorry
    have key123 : ∀ y, e123 (r • y) = r • e123 y := fun y => by
      rw [hnat y, smul_homology_eq k N P r n (e123 y)]
    have hfactor : ∀ y, extAbelianAddEquivExtₖ k N P n y = step4 (e123 y) := fun _ => rfl
    change extAbelianAddEquivExtₖ k N P n (r • x) = r • extAbelianAddEquivExtₖ k N P n x
    rw [hfactor, hfactor, key123, map_smul]

end Etingof
