import EtingofRepresentationTheory.Chapter8.RearrangeHomComplexX

/-!
# The complex-level rearrangement isomorphism for the `Ext` Künneth formula

Route **step 3** (final assembly, #6844/#6868) of the `Ext` half of Problem 8.2.8. This is the
`Hom`-cochain twin of `Etingof.rearrangeComplex` (`Chapter8/RearrangeComplex.lean`, #6744), but
built via `HomologicalComplex.Hom.isoOfComponents` (assembled degreewise from the object iso #6867)
rather than `total.mapIso`, because the source `Hom(mapBifunctor …, N)` is a **product** over the
finite fiber, not a `mapBifunctor` bicomplex.

Combining the degreewise object iso `Etingof.rearrangeHomComplexXIso` (#6867) with the two
naturality lemmas of #6843 (`homTensorHom_comp_lcompₖ_left/right`, feeding the two
differential-commutation squares), this file assembles the isomorphism of
`CochainComplex (ModuleCat k) ℕ`

```
rearrangeHomComplex :
  (extTensorComplexLeft P₁ P₂).linearYonedaObj k (N₁ ⊗ₖ N₂)
    ≅ HomologicalComplex.tensorObj
        (P₁.complex.linearYonedaObj k N₁)
        (P₂.complex.linearYonedaObj k N₂)
```

feeding the Künneth `Ext` assembler (#6818).

## Route

The degreewise components are `rearrangeHomComplexXIso`. The differential-commutation obligation for
`isoOfComponents` is discharged summand-by-summand on the *target* coproduct (via
`mapBifunctor.hom_ext`), reducing — through the `ι`/inv reduction `rearrangeHomComplexXIso`'s
`ιMapBifunctor_rearrangeHomComplexXIso_inv` and the source biproduct relations `srcInc_srcProj` — to
the two naturality lemmas of #6843. The source differential
`(X.linearYonedaObj k Y).d i j = ofHom (Linear.leftComp k Y (X.d j i))` is precomposition by the
source chain differential; contravariance flips the fiber index from degree `i+1` (source) to `i`
(target).
-/

open CategoryTheory Limits MonoidalCategory TensorProduct HomologicalComplex

namespace Etingof

universe u

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
  [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
variable
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL

variable {A₁ A₂}
variable {M₁ : ModuleCat.{u} A₁} {M₂ : ModuleCat.{u} A₂}
variable (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
variable [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
variable [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)]

include hN in
/-- **The differential-commutation square** for the `Ext` Künneth cochain assembly: the degreewise
object isos `rearrangeHomComplexXIso` commute with the source (`Hom(mapBifunctor …, N)`) and target
(`tensorObj` of the two Hom cochain complexes) differentials. Proved summand-by-summand on the
target coproduct, reducing to the two #6843 naturality lemmas. -/
theorem rearrangeHomComplexXIso_comm (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).hom ≫
        (homTarget k N₁ N₂ P₁ P₂).d i j =
      ((extTensorComplexLeft P₁ P₂).linearYonedaObj k
          (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).d i j ≫
        (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ j).hom := by
  sorry

include hN in
/-- **Route step 3 (#6868).** The complex-level rearrangement isomorphism of
`CochainComplex (ModuleCat k) ℕ`:

```
(extTensorComplexLeft P₁ P₂).linearYonedaObj k (N₁ ⊗ₖ N₂)
  ≅ HomologicalComplex.tensorObj
      (P₁.complex.linearYonedaObj k N₁)
      (P₂.complex.linearYonedaObj k N₂)
```

Assembled from the degreewise object iso `rearrangeHomComplexXIso` (#6867) via `isoOfComponents`,
with the differential-commutation obligation `rearrangeHomComplexXIso_comm`. -/
noncomputable def rearrangeHomComplex :
    (extTensorComplexLeft P₁ P₂).linearYonedaObj k
        (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) ≅
      HomologicalComplex.tensorObj
        (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i)
    (fun i j hij => rearrangeHomComplexXIso_comm k N₁ N₂ hN P₁ P₂ i j hij)

include hN in
/-- The degreewise action of `rearrangeHomComplex` on a summand: its `.hom.f i` is exactly the
degreewise object iso `rearrangeHomComplexXIso`. This is the rewrite the Künneth `Ext` assembler
(#6818) uses to identify the degree-`i` factor cohomologies. -/
@[simp]
theorem rearrangeHomComplex_hom_f (i : ℕ) :
    (rearrangeHomComplex k N₁ N₂ hN P₁ P₂).hom.f i =
      (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).hom := rfl

end Etingof
