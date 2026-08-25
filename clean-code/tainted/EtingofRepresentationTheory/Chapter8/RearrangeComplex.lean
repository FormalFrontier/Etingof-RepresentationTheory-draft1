import EtingofRepresentationTheory.Chapter8.RearrangeBifunctorNatIso
import EtingofRepresentationTheory.Chapter8.MapBifunctorPostcomp
import Mathlib.Algebra.Homology.Monoidal

set_option backward.isDefEq.respectTransparency false

/-!
# The complex-level rearrangement isomorphism for the `Tor` Künneth formula

Route **step 3** (final construction) of milestone (c) of the four-fold rearrangement of Problem 8.2.8
(`Tor`). Combining the two prior milestones,

* `Etingof.mapBifunctorPostcompIso` (`MapBifunctorPostcomp.lean`): an additive functor `G`
  commutes with the total complex `mapBifunctor`, so
  `(G.mapHomologicalComplex).obj (mapBifunctor K₁ K₂ F) ≅ mapBifunctor K₁ K₂ (F ⋙ G)`;
* `Etingof.rearrangeBifunctorNatIso` (`RearrangeBifunctorNatIso.lean`): the natural iso of
  bifunctors `extTensorRightFunctor ≅ factorTensorFunctor`, i.e.
  `(X, Y) ↦ (X ⊗ₖ Y) ⊗_{A₁⊗A₂} (N₁⊗ₖN₂)  ≅  (X ⊗_{A₁} N₁) ⊗ₖ (Y ⊗_{A₂} N₂)`,

this file assembles the isomorphism of `ChainComplex (ModuleCat k) ℕ`

```
rearrangeComplex :
  (tensorRightFunctorₖ(N₁⊗ₖN₂)).mapHC.obj (extTensorComplex P₁ P₂)
    ≅ HomologicalComplex.tensorObj
        ((tensorRightFunctorₖ N₁).mapHC.obj P₁.complex)
        ((tensorRightFunctorₖ N₂).mapHC.obj P₂.complex)
```

used by the Künneth `Tor` result.

## Route

The left-hand side is `(G.mapHC).obj (mapBifunctor P₁.complex P₂.complex (extTensorFunctor))` with
`G = tensorRightFunctorₖ (A₁⊗A₂) (N₁⊗ₖN₂)`.

1. `mapBifunctorPostcompIso` rewrites it to `mapBifunctor P₁.complex P₂.complex
   (extTensorFunctor ⋙ G) = (bicomplex of `postcompBifunctor extTensorFunctor G`).total`.
2. `rearrangeComplexBicomplexIso` is an isomorphism of the underlying **bicomplexes**, from the
   `postcompBifunctor extTensorFunctor G`-bicomplex on `(P₁, P₂)` to the `curriedTensor`-bicomplex
   on the two mapped factors `Cᵢ = (tensorRightFunctorₖ Nᵢ).mapHC.obj Pᵢ.complex`. Its bidegree
   `(i₁, i₂)` component is `rearrangeBifunctorComponentIso` (milestone (a) `rearrangeBidegree`); its
   two differential-commutation squares are exactly the two naturality squares of the bifunctor
   natural iso (`rearrangeBifunctorNatIsoApp` in the second variable, `rearrangeBifunctorNatIso` in
   the first). `HomologicalComplex₂.total.mapIso` promotes this bicomplex iso to the total complex
   iso, discharging the Koszul-signed differential automatically.

Steps 2–3 of the issue's route (apply the NatIso, then identify with `tensorObj`) fuse here into the
single bicomplex iso `rearrangeComplexBicomplexIso`, because the target bifunctor
`factorTensorFunctor` agrees **definitionally** with `curriedTensor` post-composed on each factor by
`tensorRightFunctorₖ`
(the `rfl`-lemmas `factorTensorFunctor_obj_map` / `factorTensorFunctor_map_app` of the NatIso file),
so the `factorTensorFunctor`-bicomplex on `(P₁, P₂)` and the `curriedTensor`-bicomplex on `(C₁, C₂)`
are the same object.
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
variable
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))
variable {M₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {M₂ : ModuleCat.{u} A₂ᵐᵒᵖ}
variable (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)

/-- The bicomplex-level rearrangement isomorphism. Source: the bicomplex of
`postcompBifunctor (extTensorFunctor) (tensorRightFunctorₖ (A₁⊗A₂) (N₁⊗ₖN₂))` on the resolutions
`(P₁, P₂)`. Target: the `curriedTensor (ModuleCat k)`-bicomplex on the two mapped factors
`Cᵢ = (tensorRightFunctorₖ Nᵢ).mapHC.obj Pᵢ.complex`. The bidegree `(i₁, i₂)` component is
`rearrangeBifunctorComponentIso`; the two differential-commutation squares are the two naturality
squares of the bifunctor natural iso. -/
noncomputable def rearrangeComplexBicomplexIso :
    (((postcompBifunctor (extTensorFunctor k A₁ A₂)
          (tensorRightFunctorₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).mapBifunctorHomologicalComplex
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj P₂.complex ≅
      (((curriedTensor (ModuleCat.{u} k)).mapBifunctorHomologicalComplex
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
          (((tensorRightFunctorₖ k A₁ N₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            P₁.complex)).obj
        (((tensorRightFunctorₖ k A₂ N₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P₂.complex) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i₁ => HomologicalComplex.Hom.isoOfComponents
      (fun i₂ => rearrangeBifunctorComponentIso k A₁ A₂ N₁ N₂ hN
        (P₁.complex.X i₁) (P₂.complex.X i₂))
      (fun i₂ i₂' _ =>
        ((rearrangeBifunctorNatIsoApp k A₁ A₂ N₁ N₂ hN (P₁.complex.X i₁)).hom.naturality
          (P₂.complex.d i₂ i₂')).symm))
    (fun i₁ i₁' _ => by
      apply HomologicalComplex.hom_ext
      intro i₂
      exact NatTrans.congr_app
        ((rearrangeBifunctorNatIso k A₁ A₂ N₁ N₂ hN).hom.naturality (P₁.complex.d i₁ i₁')).symm
        (P₂.complex.X i₂))

/-- **Route step 3.** The complex-level rearrangement isomorphism of
`ChainComplex (ModuleCat k) ℕ`:

```
(tensorRightFunctorₖ (N₁⊗ₖN₂)).mapHC.obj (extTensorComplex P₁ P₂)
  ≅ HomologicalComplex.tensorObj
      ((tensorRightFunctorₖ N₁).mapHC.obj P₁.complex)
      ((tensorRightFunctorₖ N₂).mapHC.obj P₂.complex)
```

built by post-composing `mapBifunctorPostcompIso` (an additive functor commutes with the total
complex) with `total.mapIso` of the bicomplex rearrangement `rearrangeComplexBicomplexIso`. -/
noncomputable def rearrangeComplex :
    ((tensorRightFunctorₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (extTensorComplex P₁ P₂) ≅
      HomologicalComplex.tensorObj
        (((tensorRightFunctorₖ k A₁ N₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₁.complex)
        (((tensorRightFunctorₖ k A₂ N₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P₂.complex) :=
  mapBifunctorPostcompIso P₁.complex P₂.complex (extTensorFunctor k A₁ A₂)
      (tensorRightFunctorₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) ≪≫
    HomologicalComplex₂.total.mapIso (rearrangeComplexBicomplexIso k A₁ A₂ N₁ N₂ hN P₁ P₂)
      (ComplexShape.down ℕ)

/-- The rearrangement iso pinned on a summand: postcomposing the `G`-image of the `(i₁, i₂)` summand
inclusion of the external tensor complex with `rearrangeComplex` lands, via milestone (a)
`rearrangeBifunctorComponentIso`, on the corresponding `(i₁, i₂)` summand of the target tensor
complex `tensorObj C₁ C₂`. This is the rewrite used by the Künneth `Tor` construction. -/
@[reassoc]
theorem rearrangeComplex_hom_f_ιMapBifunctor (i₁ i₂ j : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = j) :
    (tensorRightFunctorₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)).map
          (HomologicalComplex.ιMapBifunctor P₁.complex P₂.complex (extTensorFunctor k A₁ A₂)
            (ComplexShape.down ℕ) i₁ i₂ j h) ≫
        (rearrangeComplex k A₁ A₂ N₁ N₂ hN P₁ P₂).hom.f j =
      (rearrangeBifunctorComponentIso k A₁ A₂ N₁ N₂ hN
            (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        HomologicalComplex.ιMapBifunctor
          (((tensorRightFunctorₖ k A₁ N₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            P₁.complex)
          (((tensorRightFunctorₖ k A₂ N₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            P₂.complex)
          (curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i₁ i₂ j h := by
  rw [rearrangeComplex, Iso.trans_hom, HomologicalComplex.comp_f, ← Category.assoc]
  rw [show (mapBifunctorPostcompIso P₁.complex P₂.complex (extTensorFunctor k A₁ A₂)
        (tensorRightFunctorₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).hom.f j =
      (postcompX P₁.complex P₂.complex (extTensorFunctor k A₁ A₂)
        (tensorRightFunctorₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) j).hom from rfl,
    ιMapBifunctor_comp_postcompX_hom, HomologicalComplex₂.total.mapIso_hom,
    HomologicalComplex₂.ιTotal_map]
  rfl

end Etingof
