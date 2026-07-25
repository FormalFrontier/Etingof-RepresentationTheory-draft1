import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import EtingofRepresentationTheory.Chapter8.Definition8_2_3
import EtingofRepresentationTheory.Chapter8.Definition8_2_4

/-!
# Additivity of `Tor` and `Ext`

Problem 8.2.7 computes `Torᵢ(M, N)` and `Extⁱ(M, N)` for finitely generated modules `M`, `N`
over a PID. The book's hint is "reduce to the case of cyclic groups using the classification
theorem": a finitely generated module over a PID is a finite direct sum of a free module and
cyclic torsion modules, and `Tor`/`Ext` are additive in each argument, so the computation
reduces to the cyclic and free building blocks proved in `Chapter8/Problem8_2_7.lean`.

This file supplies the additivity half of that reduction for `Tor`. For `Ext` nothing is needed:
`Etingof.Ext` is a reducible abbreviation for `CategoryTheory.Abelian.Ext`, and Mathlib already
proves additivity in both variables, as `Abelian.Ext.biprodAddEquiv` / `Ext.biproductAddEquiv`
(first variable) and `Abelian.Ext.addEquivBiprod` / `Ext.addEquivBiproduct` (second variable).
Those may be applied to `Etingof.Ext` directly.

## Main results

* `CategoryTheory.projectiveResolutions_additive`: taking projective resolutions is an additive
  functor `C ⥤ HomotopyCategory C (ComplexShape.down ℕ)`. Two lifts of the same map are
  homotopic, and `lift f + lift g` is a lift of `f + g`, so the two agree in the homotopy
  category. Mathlib knows the functor laws for `projectiveResolutions` but not this one.
* `CategoryTheory.Functor.leftDerived_additive`: consequently every left derived functor
  `F.leftDerived n` of an additive functor is additive, being the composite of the (now additive)
  resolution functor with `F.mapHomotopyCategory` and a homology functor. Additive functors
  preserve finite biproducts, so this is exactly what makes derived functors additive in the
  sense used by the book.
* `Etingof.torFunctor_additive`, `Etingof.torBiprodIso`, `Etingof.torBiproductIso`:
  `Torₙᴬ(-, N)` is additive, hence `Torₙᴬ(M₁ ⊕ M₂, N) ≅ Torₙᴬ(M₁, N) ⊕ Torₙᴬ(M₂, N)` and, for a
  finite index type, `Torₙᴬ(⨁ i, M i, N) ≅ ⨁ i, Torₙᴬ(M i, N)`.

Additivity of `Tor` in its *second* argument is not covered here: `Torₙᴬ(M, -)` is not the
value of a single left derived functor in the present set-up (the second argument is baked into
`Etingof.tensorRightFunctor` before deriving), so it needs a separate argument.
-/

universe u v u' v'

namespace CategoryTheory

open Limits

/-! ### The resolution functor is additive -/

section ProjectiveResolutions

variable (C : Type u) [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]

/-- **Taking projective resolutions is additive.** `ProjectiveResolution.lift f P Q` is only well
defined up to homotopy, and `lift f P Q + lift g P Q` is *a* lift of `f + g`, so it agrees with
`lift (f + g) P Q` in the homotopy category. -/
instance projectiveResolutions_additive : (projectiveResolutions C).Additive where
  map_add {X Y f g} := by
    dsimp only [projectiveResolutions]
    rw [← Functor.map_add]
    apply HomotopyCategory.eq_of_homotopy
    refine ProjectiveResolution.liftHomotopy (f + g) _ _ (by simp) ?_
    rw [Preadditive.add_comp, ProjectiveResolution.lift_commutes,
      ProjectiveResolution.lift_commutes, ← Preadditive.comp_add, ← Functor.map_add]

end ProjectiveResolutions

/-! ### Left derived functors are additive -/

section LeftDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- **A left derived functor is additive.** `F.leftDerived n` is by definition the composite
`projectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ homologyFunctor _ _ n`, and all three
factors are additive. -/
instance Functor.leftDerived_additive (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.leftDerived n).Additive := by
  dsimp only [Functor.leftDerived, Functor.leftDerivedToHomotopyCategory]
  infer_instance

end LeftDerived

end CategoryTheory

/-! ### `Tor` is additive in its first argument -/

namespace Etingof

open CategoryTheory Limits

variable (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ)

/-- `Torₙᴬ(-, N)` is an additive functor: it is a left derived functor of the additive functor
`- ⊗_A N`. -/
instance torFunctor_additive : (TorFunctor.{u} A N n).Additive := by
  dsimp only [TorFunctor]
  infer_instance

/-- **`Tor` is additive in its first argument.**
`Torₙᴬ(M₁ ⊕ M₂, N) ≅ Torₙᴬ(M₁, N) ⊕ Torₙᴬ(M₂, N)`. -/
noncomputable def torBiprodIso (M₁ M₂ : ModuleCat.{u} Aᵐᵒᵖ) :
    Tor.{u} A N (M₁ ⊞ M₂) n ≅ Tor.{u} A N M₁ n ⊞ Tor.{u} A N M₂ n :=
  letI := preservesBinaryBiproduct_of_preservesBiproduct (TorFunctor.{u} A N n) M₁ M₂
  (TorFunctor.{u} A N n).mapBiprod M₁ M₂

/-- **`Tor` commutes with finite direct sums in its first argument.**
`Torₙᴬ(⨁ i, M i, N) ≅ ⨁ i, Torₙᴬ(M i, N)` for a finite index type. This is the form in which the
reduction of Problem 8.2.7 to the cyclic and free building blocks uses additivity. -/
noncomputable def torBiproductIso {ι : Type} [Finite ι] (M : ι → ModuleCat.{u} Aᵐᵒᵖ) :
    Tor.{u} A N (⨁ M) n ≅ ⨁ ((TorFunctor.{u} A N n).obj ∘ M) :=
  (TorFunctor.{u} A N n).mapBiproduct M

end Etingof
