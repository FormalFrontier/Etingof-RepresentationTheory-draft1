import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Order.Lattice
import EtingofRepresentationTheory.Chapter2.Definition2_3_8

/-!
# Definition 9.2.2: Projective cover

The projective module Pᵢ (from Theorem 9.2.1) is called the **projective cover** of the
simple module Mᵢ. It is the unique indecomposable projective module with a surjection
onto Mᵢ.

## Mathlib correspondence

Projective covers are not yet formalized in Mathlib. The concept would bundle a projective
module P together with a surjection P ↠ M that is essential (minimal).

Indecomposability uses `Etingof.IsIndecomposable` from Definition 2.3.8.

## The essential (minimal) condition

A bare projective surjection `P ↠ M` is *not* a projective cover: any projective module
surjecting onto `M` would qualify, so the notion would not be minimal. The defining feature of
the projective cover `Pᵢ ↠ Mᵢ` of Theorem 9.2.1 is that the surjection is *essential*, i.e. its
kernel is a *superfluous* (small) submodule of `P`: no proper submodule of `P` already surjects
onto `M`. We encode this as

  `∀ N, N ⊔ ker π = ⊤ → N = ⊤`,

which is the standard characterization of an essential epimorphism (equivalently, `ker π ⊆ Rad P`
for finite-dimensional modules, recovering the `dim Hom(Pᵢ, Mⱼ) = δᵢⱼ` description).
-/

/-- The projective cover of a module M, in the sense of Etingof Definition 9.2.2.

A projective cover consists of:
- A module `P` that is projective and indecomposable
- a surjective `R`-linear map `π : P →ₗ[R] M` whose kernel is superfluous (essential epimorphism)

This bundles the data of the projective cover together with the surjection.
Uniqueness (up to isomorphism) is a separate theorem (part of Theorem 9.2.1). -/
structure Etingof.ProjectiveCover (R : Type*) [Ring R]
    (M : Type*) [AddCommGroup M] [Module R M] where
  /-- The carrier type of the projective cover -/
  P : Type*
  [addCommGroup : AddCommGroup P]
  [module : Module R P]
  [projective : Module.Projective R P]
  indecomposable : Etingof.IsIndecomposable R P
  /-- The surjection from the projective cover onto the module -/
  surjection : P →ₗ[R] M
  surjection_surjective : Function.Surjective surjection
  /-- The surjection is *essential*: its kernel is a superfluous (small) submodule of `P`, i.e.
  no proper submodule of `P` surjects onto `M`. This is the minimality condition distinguishing a
  projective cover from an arbitrary projective surjecting onto `M`. -/
  surjection_essential :
    ∀ N : Submodule R P, N ⊔ LinearMap.ker surjection = ⊤ → N = ⊤

attribute [instance] Etingof.ProjectiveCover.addCommGroup
  Etingof.ProjectiveCover.module
  Etingof.ProjectiveCover.projective
