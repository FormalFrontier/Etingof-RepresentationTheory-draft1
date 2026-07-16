import EtingofRepresentationTheory.Chapter8.ExternalTensorComplex
import EtingofRepresentationTheory.Chapter8.ExternalTensorProjective

/-!
# The external tensor product of two projective resolutions is a projective resolution

Assembling the pieces built in `ExternalTensorComplex.lean` (the total complex
`Etingof.extTensorComplex P₁ P₂` and its augmentation `Etingof.extTensorπ P₁ P₂`) and
`ExternalTensorProjective.lean` (degreewise projectivity `Etingof.extTensor_projective`), this
file constructs the `ProjectiveResolution` of `M₁ ⊗[k] M₂` over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`:

* `Etingof.extTensorComplex_projective`: each degree `(extTensorComplex P₁ P₂).X n` is projective
  over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`. Degree `n` is the coproduct `⨁_{i₁+i₂=n} (P₁)_{i₁} ⊗[k] (P₂)_{i₂}` of the
  bidegree pieces (`GradedObject.mapObj` = `∐`), each projective by `extTensor_projective` since the
  factors `(P₁)_{i₁}`, `(P₂)_{i₂}` are projective; a coproduct of projectives is projective.
* `Etingof.extTensorProjectiveResolution`: the `ProjectiveResolution` itself, with
  `complex := extTensorComplex P₁ P₂`, `π := extTensorπ P₁ P₂`, degreewise projectivity from the
  lemma above, and the `quasiIso` obligation (exactness of the resolution).

## Status of `quasiIso`

The `quasiIso` field — exactness of `P•₁ ⊗_k P•₂` as a resolution of `M₁ ⊗_k M₂` — is currently a
`sorry` (a proof obligation *within* the definition; the resolution data itself is real). Over a
field `k` every module is flat, so the tensor of two bounded-below acyclic-augmented complexes of
`k`-vector spaces is acyclic. This is the acyclicity content of the Chapter 7 Künneth machinery
(`Etingof.Problem7_8_7_ii`: over a field, `C` acyclic ⟹ `C ⊗ D` acyclic), applied after forgetting
the `(A₁ ⊗ A₂)ᵐᵒᵖ`-structure down to `ModuleCat k` and bridging the complex shapes
(`ChainComplex … ℕ` here vs `CochainComplex … ℤ` in Chapter 7). Filling it is tracked as a separate
work item; the route is:

1. Restriction of scalars `ModuleCat (A₁ ⊗ A₂)ᵐᵒᵖ ⥤ ModuleCat k` is exact and conservative, hence
   reflects `QuasiIso`.
2. It carries `extTensorComplex P₁ P₂` to the total `k`-tensor complex of the underlying
   `k`-complexes of `P•₁`, `P•₂` (`mapBifunctor` commutes with restriction of scalars).
3. That `k`-tensor augmentation is a quasi-isomorphism by acyclicity of the tensor of the two
   acyclic augmented complexes (`Problem7_8_7_ii` + the `ℕ`/`ℤ` reindex bridge of
   `KunnethChainComplexNat.lean`).
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct MulOpposite

namespace Etingof

universe u

variable {k : Type u} [CommRing k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable {M₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {M₂ : ModuleCat.{u} A₂ᵐᵒᵖ}

-- The restriction-of-scalars `k`-module structures on `A₁ᵐᵒᵖ`- and `A₂ᵐᵒᵖ`-modules, needed to
-- form the `k`-tensor `M₁ ⊗[k] M₂` and its external `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action.
attribute [local instance] restrictModule₁ restrictModule₂ tower₁ tower₂ extModule

/-- The degree `.X n` of the external tensor complex, unfolded to the coproduct `mapObj` of its
bidegree summands. Stated as a `rfl` at the `mapObj` level (a single `total` projection), which is
cheap — unfolding all the way to `∐` forces a costly normalization of the bifunctor terms. -/
private theorem extTensorComplex_X_eq (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (n : ℕ) :
    (extTensorComplex (k := k) P₁ P₂).X n
      = (((((extTensorFunctor k A₁ A₂).mapBifunctorHomologicalComplex
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
          P₂.complex).toGradedObject.mapObj
          (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ))) n :=
  rfl

/-- Each degree of the external tensor complex is projective over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`. Degree `n` is
the coproduct of the bidegree pieces `(P₁)_{i₁} ⊗[k] (P₂)_{i₂}` over `i₁ + i₂ = n`; each is
projective by `extTensor_projective` (the factors are projective, being terms of projective
resolutions), and a coproduct of projectives is projective. The lifting property is assembled by
hand from `Sigma.desc`/`Sigma.ι` rather than via the coproduct-`Projective` instance, whose
full-transparency defeq check does not terminate on the heavy bifunctor summands. -/
theorem extTensorComplex_projective (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (n : ℕ) : Projective ((extTensorComplex (k := k) P₁ P₂).X n) := by
  rw [extTensorComplex_X_eq]
  set g := ((((extTensorFunctor k A₁ A₂).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
    P₂.complex).toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n with hg
  -- Each summand `(P₁)_{i₁} ⊗[k] (P₂)_{i₂}` is projective; the coproduct exists.
  haveI hsummand : ∀ i, Projective (g i) := by
    rw [hg]; rintro ⟨⟨i₁, i₂⟩, h⟩
    exact extTensor_projective k A₁ A₂ (P₁.complex.X i₁) (P₂.complex.X i₂)
  haveI hcop : HasCoproduct g := by rw [hg]; infer_instance
  show Projective (∐ g)
  refine ⟨fun {E X} f e he => ⟨Sigma.desc fun b => Projective.factorThru (Sigma.ι g b ≫ f) e, ?_⟩⟩
  apply Sigma.hom_ext
  intro b
  rw [Sigma.ι_desc_assoc]
  exact Projective.factorThru_comp _ e

/-- The **external tensor product of two projective resolutions** `P•₁ ⊗_k P•₂` is a projective
resolution of `M₁ ⊗[k] M₂` over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`. The complex and augmentation are the total
complex `extTensorComplex P₁ P₂` and its augmentation `extTensorπ P₁ P₂`; degreewise projectivity is
`extTensorComplex_projective`. The `quasiIso` obligation (exactness of the resolution) is currently
`sorry` — see the module docstring for the route. -/
noncomputable def extTensorProjectiveResolution
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    ProjectiveResolution (ModuleCat.of (A₁ ⊗[k] A₂)ᵐᵒᵖ (M₁ ⊗[k] M₂)) where
  complex := extTensorComplex P₁ P₂
  projective := extTensorComplex_projective P₁ P₂
  π := extTensorπ P₁ P₂
  quasiIso := sorry

end Etingof
