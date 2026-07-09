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

namespace Etingof.QuiverRepresentation

/-! ## Transport accessors for `transportReversedTwice`

`transportReversedTwice X` moves a representation of the double-reversed quiver `(Q̄ᵢ)̄ᵢ`
back to `Q` along the instance equality `reversedAtVertex_twice Q i : (Q̄ᵢ)̄ᵢ = Q`. Since
the `obj` field of `QuiverRepresentation` does not mention the `Quiver` instance, transport
leaves the vertex spaces unchanged; the `mapLinear` field does mention it (through the arrow
type `v ⟶ w`), so it is transported through the arrow identification.

These lemmas expose those two facts so downstream code (e.g. the adjunction of
Exercise 7.9.8) can rewrite `(transportReversedTwice X).obj` / `.mapLinear` back in terms of
`X` without unfolding the `▸`. They are stated first for two arbitrary equal `Quiver`
instances (where `subst` discharges everything) and then specialized. -/

/-- Transport of a representation along an equality of `Quiver` instances leaves the vertex
spaces unchanged (the `obj` field is instance-independent). -/
theorem obj_transport {k : Type*} [CommSemiring k] {Q : Type*}
    {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    (X : @Etingof.QuiverRepresentation k Q _ I₁) (v : Q) :
    @Etingof.QuiverRepresentation.obj k Q _ I₂ (h ▸ X) v =
    @Etingof.QuiverRepresentation.obj k Q _ I₁ X v := by
  subst h; rfl

/-- Transport of a representation along an equality of `Quiver` instances carries the arrow
maps through the arrow identification: `(h ▸ X).mapLinear e` agrees heterogeneously with
`X.mapLinear (h.symm ▸ e)`. -/
theorem mapLinear_transport_heq {k : Type*} [CommSemiring k] {Q : Type*}
    {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    (X : @Etingof.QuiverRepresentation k Q _ I₁) (a b : Q) (e : @Quiver.Hom Q I₂ a b) :
    HEq
      (@Etingof.QuiverRepresentation.mapLinear k Q _ I₂ (h ▸ X) a b e)
      (@Etingof.QuiverRepresentation.mapLinear k Q _ I₁ X a b (h.symm ▸ e)) := by
  subst h; rfl

variable {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q] {i : Q}

/-- The vertex spaces of `transportReversedTwice X` are those of `X`. -/
theorem transportReversedTwice_obj
    (X : @Etingof.QuiverRepresentation k Q _
      (@Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i)) (v : Q) :
    @Etingof.QuiverRepresentation.obj k Q _ inst
      (Etingof.QuiverRepresentation.transportReversedTwice X) v =
    @Etingof.QuiverRepresentation.obj k Q _
      (@Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i) X v :=
  obj_transport (Etingof.reversedAtVertex_twice Q i) X v

/-- The arrow maps of `transportReversedTwice X` agree heterogeneously with those of `X`,
after transporting the arrow `e` back to the double-reversed quiver. -/
theorem transportReversedTwice_mapLinear_heq
    (X : @Etingof.QuiverRepresentation k Q _
      (@Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i))
    (a b : Q) (e : @Quiver.Hom Q inst a b) :
    HEq
      (@Etingof.QuiverRepresentation.mapLinear k Q _ inst
        (Etingof.QuiverRepresentation.transportReversedTwice X) a b e)
      (@Etingof.QuiverRepresentation.mapLinear k Q _
        (@Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i) X a b
        ((Etingof.reversedAtVertex_twice Q i).symm ▸ e)) :=
  mapLinear_transport_heq (Etingof.reversedAtVertex_twice Q i) X a b e

end Etingof.QuiverRepresentation

/-!
## Proof blueprint for `Exercise7_9_8` (the adjunction bijection)

Status: the two `transportReversedTwice` accessors above are proved sorry-free; the main
bijection below is still `sorry`. The remaining assembly is large (comparable in size to
`Proposition6_6_6`), so it is documented here for the next worker.

**Key reduction.** Write `hi' := isSource_reversedAtVertex_isSink hi` (so `i` is a sink of
`Q̄ᵢ`). Both hom-sets are equivalent to the *same* reduced data: a family
`hᵥ : V.obj v →ₗ[k] W.obj v` for every `v ≠ i` such that

* (A) for every arrow `e : a ⟶ b` of `Q` with `a ≠ i`, `b ≠ i` (these are exactly the
  arrows of `Q̄ᵢ` not touching `i`), `W.mapLinear e ∘ hₐ = h_b ∘ V.mapLinear e`; and
* (C) `∑ (a : ArrowsOutOf Q i), W.mapLinear (rev a) (h_{a.fst} (V.mapLinear a.snd x)) = 0`
  for all `x : V.obj i`, where `rev a : a.fst ⟶ i` in `Q̄ᵢ` is the reversed arrow.

*From `f : Hom(F⁻ᵢV, W)`* set `hᵥ := f.app v ∘ (reflFunctorMinus_equivAt_ne hi V v _).symm`.
Naturality of `f` on a reversed arrow `a.fst → i` (case `ne_eq`, via
`reflFunctorMinus_mapLinear_ne_eq`) forces the `a`-component of the induced map on
`coker(sourceMap_V)` to be `W.mapLinear (rev a) ∘ hₐ`; well-definedness of `f.app i` on the
cokernel is precisely (C).

*From `g : Hom(V, transportReversedTwice (F⁺ᵢW))`* set `hᵥ := (reflFunctorPlus_equivAt_ne
hi' W v _) ∘ g.app v` (using `transportReversedTwice_obj` to see `g.app v : V.obj v →
W.obj v` for `v ≠ i`). Naturality of `g` on an arrow `i → a.fst` of `Q` (case `eq_ne`, via
`reflFunctorPlus_mapLinear_eq_ne` and `transportReversedTwice_mapLinear_heq`) forces the
`a`-component of `g.app i : V.obj i → ker(sinkMap_W)` to be `hₐ ∘ V.mapLinear a.snd`; landing
in the kernel `sinkMap_W = 0` is precisely (C), which is `Φ_comp_source_eq_zero` after
reindexing `ArrowsInto (Q̄ᵢ) i ≃ ArrowsOutOf Q i` via `arrowReindexEquiv hi'`.

**Assembly.** Define `toFun`, `invFun` by extracting the reduced family and rebuilding on the
other side (kernel corestriction via `LinearMap.codRestrict` + (C); cokernel factoring via
`Submodule.liftQ` + (C)). Prove `left_inv`/`right_inv` by `QuiverRepresentationHom`
extensionality: at `v ≠ i` both sides are `hᵥ` transported; at `v = i` use uniqueness of the
cokernel map out of `mkQ` / the kernel `subtype` being injective. Reusable ingredients:
`arrowReindexEquiv`, `sinkMap_reindex_surj`, `Φ_comp_source_eq_zero`, `exact_of_dim`, the
`reversedArrow_*_twice` cast lemmas, and the `heq_apply` / `heq_linearMap_coe` toolkit.
-/

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
