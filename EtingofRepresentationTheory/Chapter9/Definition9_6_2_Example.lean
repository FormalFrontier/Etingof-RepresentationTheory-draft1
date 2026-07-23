import EtingofRepresentationTheory.Chapter9.Definition9_6_2
import Mathlib.Algebra.Category.ModuleCat.Projective

universe u

/-!
# Definition 9.6.2, motivating example: the regular module is a projective generator

Etingof's Definition 9.6.2 illustrates the general notion of a projective generator with the
regular module `A` (the ring viewed as a module over itself) in the category of *all* `A`-modules:
`A` is projective (it is free of rank one), and every `A`-module `M` is a quotient of a coproduct
of copies of `A` — concretely, of the free module `A^{(M)}`. Realizing an arbitrary module this way
genuinely requires an *infinite* coproduct, which is exactly what the general
`Etingof.IsProjectiveGenerator` (unlike the finite `Etingof.IsProgenerator`) allows.

This example is kept in its own file so that the lightweight `Chapter9.Definition9_6_2` does not
depend on the module-category `Projective` instances (those instances slow generic `Projective`
typeclass search in the finite-abelian-category development downstream).
-/

open CategoryTheory CategoryTheory.Limits

/-- **Etingof's motivating example (Definition 9.6.2).** The regular module `R` (the ring viewed as
a module over itself) is a projective generator, in the general sense, of the category of all
`R`-modules: it is projective and every `R`-module is a quotient of a coproduct of copies of `R`. -/
theorem Etingof.moduleCat_regular_isProjectiveGenerator (R : Type u) [Ring R] :
    Etingof.IsProjectiveGenerator (ModuleCat.of R R) := by
  refine ⟨inferInstance, ?_⟩
  rw [isSeparator_def]
  intro X Y f g hfg
  apply ModuleCat.hom_ext
  ext x
  have h := hfg (ModuleCat.ofHom (LinearMap.toSpanSingleton R X x))
  simpa using congrArg (fun φ => ModuleCat.Hom.hom φ (1 : R)) h
