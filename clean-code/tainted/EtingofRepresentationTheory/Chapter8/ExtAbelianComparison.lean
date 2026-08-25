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
valued derived-category `Etingof.Ext = CategoryTheory.Abelian.Ext`. This file relates the two by a
`k`-linear isomorphism

```
Etingof.extAbelianIsoExtₖ (P : ProjectiveResolution M) (n : ℕ) :
    Etingof.Ext M N n ≃ₗ[k] Etingof.Extₖ k A M N n
```

for a `k`-algebra `A` over a field `k` and left `A`-modules `M`, `N`.

## Construction

Both sides compute `Extⁿ_A(M, N)` as the cohomology of `Hom_A(P•, N)`; the comparison composes four
additive isomorphisms, then upgrades the composite to `k`-linear.

1. `P.extAddEquivCohomologyClass`: `Abelian.Ext M N n ≃+ CohomologyClass P.cochainComplex N[0] n`
   (Mathlib).
2. `(CochainComplex.HomComplex.homologyAddEquiv _ _ _).symm`: the cohomology classes are the
   degree-`n` homology of the `AddCommGrp`-valued `HomComplex` (Mathlib).
3. `Etingof.homComplexHomologyAddEquivₖ`: that homology identifies additively with the degree-`n`
   homology of the `ModuleCat k`-valued `linearYonedaObj`.
4. `(Etingof.extIsoCohomologyHomₖ …).symm`: which is `Etingof.Extₖ`
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

/-- **Fact 1.** On the `ModuleCat k`-valued homology
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
underlying additive equivalence is the four-step chain `extAbelianAddEquivExtₖ`; this is
the version used by `Problem_8_2_8_ext` to transport the `Extₖ` Künneth isomorphism to
the `Etingof.Ext` statement.

The scalar action on `Abelian.Ext M N n` is postcomposition with `r • 𝟙 N`
(`CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀`); on `Extₖ k A M N n : ModuleCat k` it is the module
scalar. Step 4 is a `ModuleCat k` iso, hence `k`-linear, and is factored out; via `smul_homology_eq`
(fact 1) the residual `map_smul'` becomes the single purely categorical naturality statement `hnat`:
that the steps 1 to 3 composite `e123` intertwines the source scalar (postcomposition with
`mk₀ (r • 𝟙 N)`) with `homologyMap (r • 𝟙)` on the `linearYonedaObj` homology. This is proved
on generators by naturality-in-`N` of `extAddEquivCohomologyClass`
(`extEquivCohomologyClass_extMk` + `Cocycle.toSingleMk_postcomp`), of `homologyAddEquiv`
(`homologyAddEquiv_homologyMap`), and the tower naturality of `homComplexHomologyAddEquivₖ`
(`homComplexHomologyAddEquivₖ_homologyMap_postcomp`) under `r • 𝟙 N`. -/
noncomputable def extAbelianIsoExtₖ (n : ℕ) :
    Etingof.Ext M N n ≃ₗ[k] Etingof.Extₖ k A M N n where
  __ := extAbelianAddEquivExtₖ k N P n
  map_smul' := by
    intro r x
    -- Steps 1 to 3 of the chain, landing in the `ModuleCat k` homology of `linearYonedaObj`.
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
    -- the degreewise scalar `r • 𝟙` on `linearYonedaObj`. Traced through the three chain
    -- steps (`extAddEquivCohomologyClass`, `homologyAddEquiv`, `homComplexHomologyAddEquivₖ`).
    -- **Naturality on generators.** By `extMk_surjective` every element of `Ext M N n`
    -- is `P.extMk f (n+1) rfl hf` for a cocycle `f : P.complex.X n ⟶ N`. The scalar action on such
    -- a generator is `r • extMk f = extMk (r • f)` (`smul_eq_comp_mk₀` + `extMk_comp_mk₀` +
    -- `Linear.comp_smul`). The remaining content is that `e123 ∘ extMk` is `k`-homogeneous: the
    -- steps 1 to 3 composite sends the cocycle `r • f` to `r •` the class of `f`. This is the purely
    -- categorical residual traced through `extAddEquivCohomologyClass`, `homologyAddEquiv`, and the
    -- `homComplexHomologyAddEquivₖ` tower.
    have crux : ∀ (f : P.complex.X n ⟶ N) (hf : P.complex.d (n + 1) n ≫ f = 0),
        e123 (P.extMk (r • f) (n + 1) rfl
              (by rw [Linear.comp_smul, hf, smul_zero]))
          = r • e123 (P.extMk f (n + 1) rfl hf) := by
      intro f hf
      -- The scalar `r • f` is postcomposition of `f` with the endomorphism `g = r • 𝟙 N`.
      have hfg : P.complex.d (n + 1) n ≫ (f ≫ (r • 𝟙 N)) = 0 := by
        rw [← Category.assoc, hf, zero_comp]
      have hExtRw : P.extMk (r • f) (n + 1) rfl (by rw [Linear.comp_smul, hf, smul_zero])
          = P.extMk (f ≫ (r • 𝟙 N)) (n + 1) rfl hfg := by
        congr 1
      -- Step 1: on cohomology classes, `extAddEquivCohomologyClass ∘ extMk (- ≫ g)` is
      -- postcomposition `cohomologyClassPostcompHom` (via `toSingleMk_postcomp`).
      have step : P.extAddEquivCohomologyClass (P.extMk (f ≫ (r • 𝟙 N)) (n + 1) rfl hfg)
          = cohomologyClassPostcompHom N P (r • 𝟙 N) (↑n)
              (P.extAddEquivCohomologyClass (P.extMk f (n + 1) rfl hf)) := by
        rw [ProjectiveResolution.extAddEquivCohomologyClass_apply,
            ProjectiveResolution.extEquivCohomologyClass_extMk,
            ProjectiveResolution.extAddEquivCohomologyClass_apply,
            ProjectiveResolution.extEquivCohomologyClass_extMk,
            cohomologyClassPostcompHom_mk]
        congr 1
        rw [← Cocycle.toSingleMk_postcomp]
        congr 1
      -- Unfold `e123` into the three-step composite and rewrite through steps 1 to 3.
      simp only [he123, AddEquiv.trans_apply]
      rw [hExtRw, step,
        show (CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
              ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) (↑n : ℤ)).symm
              (cohomologyClassPostcompHom N P (r • 𝟙 N) (↑n)
                (P.extAddEquivCohomologyClass (P.extMk f (n + 1) rfl hf)))
            = HomologicalComplex.homologyMap (homCochainComplexPostcomp N P (r • 𝟙 N)) (↑n)
                ((CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
                  ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) (↑n : ℤ)).symm
                  (P.extAddEquivCohomologyClass (P.extMk f (n + 1) rfl hf)))
          from by rw [AddEquiv.symm_apply_eq, homologyAddEquiv_homologyMap,
            AddEquiv.apply_symm_apply],
        homComplexHomologyAddEquivₖ_homologyMap_postcomp, ← smul_homology_eq]
    have hnat : ∀ y, e123 (r • y)
        = (HomologicalComplex.homologyMap (r • 𝟙 (P.complex.linearYonedaObj k N)) n).hom
            (e123 y) := by
      intro y
      obtain ⟨f, hf, rfl⟩ := P.extMk_surjective y (n + 1) rfl
      have hrf : P.complex.d (n + 1) n ≫ (r • f) = 0 := by
        rw [Linear.comp_smul, hf, smul_zero]
      have hsmul : r • P.extMk f (n + 1) rfl hf = P.extMk (r • f) (n + 1) rfl hrf := by
        rw [Abelian.Ext.smul_eq_comp_mk₀, ProjectiveResolution.extMk_comp_mk₀]
        congr 1
      rw [hsmul, ← smul_homology_eq k N P r n (e123 (P.extMk f (n + 1) rfl hf)), crux f hf]
    have key123 : ∀ y, e123 (r • y) = r • e123 y := fun y => by
      rw [hnat y, smul_homology_eq k N P r n (e123 y)]
    have hfactor : ∀ y, extAbelianAddEquivExtₖ k N P n y = step4 (e123 y) := fun _ => rfl
    change extAbelianAddEquivExtₖ k N P n (r • x) = r • extAbelianAddEquivExtₖ k N P n x
    rw [hfactor, hfactor, key123, map_smul]

end Etingof
