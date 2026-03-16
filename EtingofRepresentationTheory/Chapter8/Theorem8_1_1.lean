import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Theorem 8.1.1: Equivalent characterizations of projective modules

The following properties of P are equivalent:

(i) If α : M → N is a surjective morphism and ν : P → N is any morphism, then there exists
a morphism μ : P → M such that α ∘ μ = ν.

(ii) Any surjective morphism α : M → P splits; i.e., there exists μ : P → M such that
α ∘ μ = id.

(iii) There exists another A-module Q such that P ⊕ Q is a free A-module.

(iv) The functor Hom_A(P, ?) on the category of A-modules is exact.

## Mathlib correspondence

`Module.Projective` captures condition (i) (the lifting property). The equivalences with
splitting, direct summand of free, and exactness of Hom are available in various forms
across Mathlib's module theory.
-/

/-- Equivalent characterizations of projective modules: the lifting property, splitting
of surjections, being a direct summand of a free module, and exactness of Hom(P, −).
(Etingof Theorem 8.1.1) -/
theorem Etingof.Theorem_8_1_1 : (sorry : Prop) := sorry
