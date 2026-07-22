import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.ReflectionFunctorInfrastructure
import EtingofRepresentationTheory.Chapter2.Definition2_8_10

/-!
# Exercise 7.9.8: Reflection functors are adjoint (`F⁺ᵢ` right adjoint to `F⁻ᵢ`)

**Exercise 7.9.8.** (a) Let `Q` be a quiver and let `i ∈ Q` be a source. Let `V` be a
representation of `Q` and let `W` be a representation of `Q̄ᵢ` (the quiver obtained from
`Q` by reversing arrows at the vertex `i`). Prove that there is a natural isomorphism
between `Hom(F⁻ᵢ V, W)` and `Hom(V, F⁺ᵢ W)`. In other words, the functor `F⁺ᵢ` is right
adjoint to `F⁻ᵢ`.

(b) Deduce that the functor `F⁺ᵢ` is left exact and `F⁻ᵢ` is right exact.

## Formalization

The reflection functors are formalized in Chapter 6 as maps on
`Etingof.QuiverRepresentation` (Definition 6.6.3 for `F⁺`, requiring `i` a sink;
Definition 6.6.4 for `F⁻`, requiring `i` a source). Morphisms are
`Etingof.QuiverRepresentationHom`.

With `i` a source of `Q`, `F⁻ᵢ V := reflectionFunctorMinus Q i hi V` is a representation
of the reversed quiver `Q̄ᵢ := reversedAtVertex Q i`. In `Q̄ᵢ`, vertex `i` is a *sink*
(`Etingof.isSource_reversedAtVertex_isSink`), so `F⁺ᵢ` applies to the representation `W`
of `Q̄ᵢ` and yields a representation of the doubly-reversed quiver `(Q̄ᵢ)̄ᵢ`, which is the
original quiver by `Etingof.reversedAtVertex_twice`. We transport it back to `Q` with
`Etingof.QuiverRepresentation.transportReversedTwice`, so that
`Hom(V, F⁺ᵢ W)` is a hom-set of representations of `Q`.

Part (a), `Exercise7_9_8`, is the resulting bijection of hom-sets — the hom-set half of
the adjunction `F⁻ᵢ ⊣ F⁺ᵢ`. (The full statement "`F⁺ᵢ` is right adjoint to `F⁻ᵢ`" would
additionally package `F⁺ᵢ`/`F⁻ᵢ` as `CategoryTheory.Functor`s between the abelian
categories `Rep(Q)` and `Rep(Q̄ᵢ)` and assert naturality of this bijection; the
representation categories are not packaged as `CategoryTheory` categories in this project,
so we record the core hom-set bijection.)

Part (b) follows from (a) together with Exercise 7.9.7 (a left adjoint is right exact and a
right adjoint is left exact): once `F⁻ᵢ ⊣ F⁺ᵢ` is realized as an adjunction of additive
functors of abelian categories, `F⁻ᵢ` (the left adjoint) is right exact and `F⁺ᵢ` (the
right adjoint) is left exact. As the categorical packaging of the reflection functors is
out of scope here (see above), we do not restate (b) separately; it is `Exercise7_9_7`
applied to the adjunction of (a).
-/

open CategoryTheory

/-- Exercise 7.9.8(a): for a source `i` of a quiver `Q`, a representation `V` of `Q`, and a
representation `W` of the reversed quiver `Q̄ᵢ`, there is a natural isomorphism (here: a
bijection of hom-sets) between `Hom(F⁻ᵢ V, W)` (in `Rep(Q̄ᵢ)`) and `Hom(V, F⁺ᵢ W)` (in
`Rep(Q)`, after transporting `F⁺ᵢ W` from the doubly-reversed quiver back to `Q`). This is
the hom-set half of the adjunction `F⁻ᵢ ⊣ F⁺ᵢ`. -/
theorem Etingof.Exercise7_9_8 {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q]
    [Quiver Q] (i : Q) (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)]
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i)) :
    Nonempty
      ((@Etingof.QuiverRepresentationHom k Q _ (Etingof.reversedAtVertex Q i)
          (Etingof.reflectionFunctorMinus Q i hi V) W)
        ≃
        Etingof.QuiverRepresentationHom k Q V
          (Etingof.QuiverRepresentation.transportReversedTwice
            (@Etingof.reflectionFunctorPlus k _ Q _ (Etingof.reversedAtVertex Q i) i
              (Etingof.isSource_reversedAtVertex_isSink hi) W))) := by
  sorry
