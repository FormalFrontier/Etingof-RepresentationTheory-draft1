import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Discussion after Definition 7.6.1: Adjunctions as representability

The text observes that a left/right adjoint, when it exists, is unique and can be
constructed canonically. This follows from the Yoneda lemma: if `F, G` are a pair
of adjoint functors (`F ⊣ G`), then `F(X)` represents the functor
`Y ↦ Hom(X, G(Y))` and `G(Y)` represents the functor `X ↦ Hom(F(X), Y)`.

## Mathlib correspondence

Exact match. `CategoryTheory.Adjunction.corepresentableBy` says that for an
adjunction `adj : F ⊣ G` and `X : C`, the object `F.obj X` corepresents
`Y ↦ (X ⟶ G.obj Y)` (i.e. the functor `G ⋙ coyoneda.obj (op X)`).
Dually, `CategoryTheory.Adjunction.representableBy` says `G.obj Y` represents
`X ↦ (F.obj X ⟶ Y)`.
-/

open CategoryTheory Opposite

namespace Etingof

variable {C : Type*} {D : Type*} [Category C] [Category D]
variable {F : Functor C D} {G : Functor D C}

/-- Discussion after Definition 7.6.1: if `F ⊣ G`, then `F(X)` corepresents the
functor `Y ↦ Hom(X, G(Y))`. This is `Adjunction.corepresentableBy` in Mathlib. -/
noncomputable def adjunction_corepresents (adj : F ⊣ G) (X : C) :
    (G ⋙ coyoneda.obj (op X)).CorepresentableBy (F.obj X) :=
  adj.corepresentableBy X

/-- Discussion after Definition 7.6.1: if `F ⊣ G`, then `G(Y)` represents the
functor `X ↦ Hom(F(X), Y)`. This is `Adjunction.representableBy` in Mathlib. -/
noncomputable def adjunction_represents (adj : F ⊣ G) (Y : D) :
    (F.op ⋙ yoneda.obj Y).RepresentableBy (G.obj Y) :=
  adj.representableBy Y

end Etingof
