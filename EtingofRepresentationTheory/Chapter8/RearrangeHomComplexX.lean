import EtingofRepresentationTheory.Chapter8.RearrangeHomBifunctorNatIso
import EtingofRepresentationTheory.Chapter8.ExternalTensorComplexLeft
import EtingofRepresentationTheory.Chapter8.ExtCohomologyHomK
import EtingofRepresentationTheory.Chapter7.KunnethCochainComplexNat

/-!
# The degreewise object iso for the `Ext` Künneth cochain assembly

Substep of #6844 (the `Ext` half of Problem 8.2.8). This file constructs, for each degree `i`, the
`ModuleCat k` isomorphism

    Hom_{A₁⊗A₂}(⊕_{j+m=i} extTensorFunctorLeftObj (P₁ⱼ) (P₂ₘ), N₁⊗N₂)
      ≅ ⊕_{j+m=i} Hom_{A₁}(P₁ⱼ, N₁) ⊗ₖ Hom_{A₂}(P₂ₘ, N₂),

identifying the degree-`i` object of the source cochain complex
`(extTensorComplexLeft P₁ P₂).linearYonedaObj k (N₁⊗N₂)` with that of the target
`HomologicalComplex.tensorObj (P₁.complex.linearYonedaObj k N₁) (P₂.complex.linearYonedaObj k N₂)`.

Because the source is `Hom(mapBifunctor …, N)` — a **product** over the finite fiber via the op/unop
`linearYonedaObj`, not a `mapBifunctor` bicomplex — the `Tor`-side `total.mapIso` shortcut is
unavailable, and the complex iso (#6868) has to be assembled degreewise from this object iso.

## The per-summand bridge

The essential ingredient is `summandIso`: on a single summand `(j, m)`,
`Hom(extTensorFunctorLeftObj (P₁ⱼ)(P₂ₘ), N₁⊗N₂) ≅ Hom(P₁ⱼ,N₁) ⊗ₖ Hom(P₂ₘ,N₂)`, obtained by
bridging the categorical `Hom`s (`ModuleCat.homLinearEquiv`) to `→ₗ`-maps and applying the
component iso `Etingof.rearrangeHomComponentIso` (#6843).
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

/-- The `A₁ ⊗ A₂`-module `N₁ ⊗ₖ N₂` as an object of `ModuleCat (A₁ ⊗ A₂)`. -/
noncomputable abbrev NNobj : ModuleCat.{u} (A₁ ⊗[k] A₂) := ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL

section Summand

variable {A₁ A₂}

include hN in
/-- The per-summand bridge iso: on the `(X₁, X₂)` summand,
`Hom_{A₁⊗A₂}(extTensorFunctorLeftObj X₁ X₂, N₁⊗N₂) ≅ Hom_{A₁}(X₁, N₁) ⊗ₖ Hom_{A₂}(X₂, N₂)`, phrased
between the categorical `Hom` objects (as they appear in `linearYonedaObj`/`tensorObj`). Bridges the
categorical `Hom`s to `→ₗ`-maps via `ModuleCat.homLinearEquiv` and applies the component iso
`rearrangeHomComponentIso` (#6843). -/
noncomputable def summandIso (X₁ : ModuleCat.{u} A₁) (X₂ : ModuleCat.{u} A₂)
    [Module.Finite A₁ X₁] [Module.Projective A₁ X₁]
    [Module.Finite A₂ X₂] [Module.Projective A₂ X₂] :
    ModuleCat.of k (extTensorFunctorLeftObj k A₁ A₂ X₁ X₂ ⟶ NNobj k A₁ A₂ N₁ N₂) ≅
      (ModuleCat.of k (X₁ ⟶ ModuleCat.of A₁ N₁)) ⊗ (ModuleCat.of k (X₂ ⟶ ModuleCat.of A₂ N₂)) :=
  ModuleCat.homLinearEquiv.toModuleIso ≪≫
    rearrangeHomComponentIso k N₁ N₂ hN X₁ X₂ ≪≫
    (tensorIso
      (ModuleCat.homLinearEquiv (M := X₁) (N := ModuleCat.of A₁ N₁) (S := k)).toModuleIso
      (ModuleCat.homLinearEquiv (M := X₂) (N := ModuleCat.of A₂ N₂) (S := k)).toModuleIso).symm

end Summand

end Etingof
