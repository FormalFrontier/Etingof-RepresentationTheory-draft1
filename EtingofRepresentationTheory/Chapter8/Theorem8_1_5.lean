import Mathlib.Algebra.Module.Injective

/-!
# Theorem 8.1.5: Equivalent characterizations of injective modules

The following properties of I are equivalent:

(i) If α : N → M is an injective morphism and ν : N → I is any morphism, then there exists
a morphism μ : M → I such that μ ∘ α = ν.

(ii) Any injective morphism α : I → M splits; i.e., there exists μ : M → I such that
μ ∘ α = id.

(iii) The functor Hom_A(?, I) on the category of A-modules is exact.

## Mathlib correspondence

`Module.Injective` captures condition (i) (the extension property). The equivalences with
splitting of injections and exactness of Hom(−, I) are available across Mathlib.
-/

/-- Equivalent characterizations of injective modules: the extension property, splitting
of injections, and exactness of Hom(−, I).
(Etingof Theorem 8.1.5) -/
theorem Etingof.Theorem_8_1_5 : (sorry : Prop) := sorry
