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

## Decomposition (this file)

The assembly is decomposed along the blueprint's two directions through a shared reduced-data
type `Etingof.AdjReducedData hi V W`: a family `h v : V v →ₗ W v` for `v ≠ i` subject to
arrow-compatibility (A) away from `i` and the source constraint (C) at `i`. The main theorem
`Exercise7_9_8` is assembled from two hom-set equivalences, each proved separately:

* `homFMinusEquivReduced : Hom(F⁻ᵢV, W) ≃ AdjReducedData hi V W` — the cokernel side, using the
  `reflFunctorMinus_mapLinear_*` reductions and `Submodule.liftQ` (constraint (C) is exactly the
  well-definedness of the map out of the cokernel at `i`);
* `homTransportPlusEquivReduced : Hom(V, transportReversedTwice (F⁺ᵢW)) ≃ AdjReducedData hi V W`
  — the kernel side, using the `transportReversedTwice_*` accessors above together with the
  `reflFunctorPlus_mapLinear_*` reductions and `LinearMap.codRestrict` (constraint (C) is exactly
  landing in the kernel, i.e. `Φ_comp_source_eq_zero`).
-/

/-- At a source `i`, an arrow out of `i` cannot return to `i` (a loop at `i` would be an arrow
into the source). -/
theorem Etingof.arrowsOutOf_target_ne_source
    {Q : Type*} [Quiver Q] {i : Q} (hi : Etingof.IsSource Q i)
    (a : Etingof.ArrowsOutOf Q i) : a.fst ≠ i :=
  fun h => (hi i).false (cast (congrArg (i ⟶ ·) h) a.snd)

/-- The reversed arrow `a.fst ⟶ i` in `Q̄ᵢ` associated with an arrow `a : ArrowsOutOf Q i` out
of the source `i`. -/
noncomputable def Etingof.revOut
    {Q : Type*} [DecidableEq Q] [Quiver Q] {i : Q} (hi : Etingof.IsSource Q i)
    (a : Etingof.ArrowsOutOf Q i) :
    @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a.fst i :=
  cast (Etingof.ReversedAtVertexHom_ne_eq (Etingof.arrowsOutOf_target_ne_source hi a) rfl).symm
    a.snd

/-- Reduced data for the adjunction hom-set bijection of Exercise 7.9.8. Both `Hom(F⁻ᵢV, W)`
and `Hom(V, F⁺ᵢW)` are in bijection with this data:

* `h v : V v →ₗ[k] W v` for every `v ≠ i`;
* (A) `compat`: away from `i`, the family commutes with the (unchanged) arrow maps; and
* (C) `constraint`: at the source `i`, the single relation
  `∑ₐ W(rev a)(h_{a.fst}(V(a.snd) x)) = 0` for all `x : V i`.

This is the common core through which the two directions of the adjunction bijection factor. -/
structure Etingof.AdjReducedData
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)]
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i)) where
  /-- The reduced linear map at each vertex `v ≠ i`. -/
  h : ∀ v, v ≠ i → (V.obj v →ₗ[k]
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i) W v)
  /-- (A) Arrow-compatibility away from `i`. -/
  compat : ∀ {a b : Q} (ha : a ≠ i) (hb : b ≠ i)
      (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b) (x : V.obj a),
      @Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i) W a b e
          (h a ha x) =
        h b hb (V.mapLinear (Etingof.reversedArrow_ne_ne ha hb e) x)
  /-- (C) The single source constraint at `i`. -/
  constraint : ∀ (x : V.obj i),
      ∑ a : Etingof.ArrowsOutOf Q i,
        @Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i) W a.fst i
          (Etingof.revOut hi a)
          (h a.fst (Etingof.arrowsOutOf_target_ne_source hi a) (V.mapLinear a.snd x)) = 0

/-- Two pieces of reduced data are equal as soon as their linear-map families agree; the
arrow-compatibility and source-constraint fields are propositions. -/
@[ext] theorem Etingof.AdjReducedData.ext
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} {hi : Etingof.IsSource Q i} [Fintype (Etingof.ArrowsOutOf Q i)]
    {V : Etingof.QuiverRepresentation k Q}
    {W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i)}
    {r₁ r₂ : Etingof.AdjReducedData hi V W} (h : r₁.h = r₂.h) : r₁ = r₂ := by
  cases r₁; cases r₂; cases h; rfl

/-- Two representation morphisms are equal as soon as their vertex maps agree. -/
@[ext] theorem Etingof.QuiverRepresentationHom.ext
    {k : Type*} {Q : Type*} [CommSemiring k] [Quiver Q]
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    {f g : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂} (h : ∀ v, f.app v = g.app v) : f = g := by
  cases f with
  | mk fa fn => cases g with
    | mk ga gn => have : fa = ga := funext h; subst this; rfl

/-! ### Index round-trip helpers for `revOut`

`revOut hi a : a.fst ⟶_{Q̄ᵢ} i` and `reversedArrow_ne_eq ha : (a ⟶_{Q̄ᵢ} i) → (i ⟶ a)` are both
`cast`s along `ReversedAtVertexHom_ne_eq`, so composing them in either order is the identity. -/

/-- Reversing the arrow `revOut hi a` (into `i` in `Q̄ᵢ`) back to `Q` recovers `a.snd`. -/
theorem Etingof.reversedArrow_ne_eq_revOut
    {Q : Type*} [DecidableEq Q] [Quiver Q] {i : Q} (hi : Etingof.IsSource Q i)
    (a : Etingof.ArrowsOutOf Q i) :
    Etingof.reversedArrow_ne_eq (Etingof.arrowsOutOf_target_ne_source hi a)
      (Etingof.revOut hi a) = a.snd := by
  obtain ⟨j, e⟩ := a
  simp only [Etingof.revOut, Etingof.reversedArrow_ne_eq_is_cast, cast_cast, cast_eq]

/-- `revOut` of the arrow `reversedArrow_ne_eq ha e` (built from `e : a ⟶_{Q̄ᵢ} i`) recovers `e`. -/
theorem Etingof.revOut_reversedArrow_ne_eq
    {Q : Type*} [DecidableEq Q] [Quiver Q] {i a : Q} (hi : Etingof.IsSource Q i) (ha : a ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a i) :
    Etingof.revOut hi ⟨a, Etingof.reversedArrow_ne_eq ha e⟩ = e := by
  simp only [Etingof.revOut, Etingof.reversedArrow_ne_eq_is_cast, cast_cast, cast_eq]

open Classical in
/-- The quotient map `reflFunctorMinus_mkQ` on the `a`-generator `lof a u` of the direct sum is
the reversed-arrow map applied to `u`: `mkQ (lof a u) = F⁻ᵢ(V)(revOut a) (equivAt_ne⁻¹ u)`. This
is `reflFunctorMinus_mapLinear_ne_eq` read backwards, using the `reversedArrow_ne_eq_revOut`
index round-trip to collapse the reindexed generator back to `a`. -/
theorem Etingof.reflFunctorMinus_mkQ_lof
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i) (V : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (a : Etingof.ArrowsOutOf Q i) (u : V.obj a.fst) :
    Etingof.reflFunctorMinus_mkQ hi V
        (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1) a u) =
      @Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi V) a.fst i (Etingof.revOut hi a)
        ((Etingof.reflFunctorMinus_equivAt_ne hi V a.fst
          (Etingof.arrowsOutOf_target_ne_source hi a)).symm u) := by
  classical
  obtain ⟨j, e⟩ := a
  have key := Etingof.reflFunctorMinus_mapLinear_ne_eq hi V
    (Etingof.arrowsOutOf_target_ne_source hi ⟨j, e⟩) (Etingof.revOut hi ⟨j, e⟩)
    ((Etingof.reflFunctorMinus_equivAt_ne hi V (⟨j, e⟩ : Etingof.ArrowsOutOf Q i).fst
      (Etingof.arrowsOutOf_target_ne_source hi ⟨j, e⟩)).symm u)
  rw [LinearEquiv.apply_symm_apply, Etingof.reversedArrow_ne_eq_revOut hi ⟨j, e⟩] at key
  exact key.symm

set_option maxHeartbeats 3200000 in
/-- The cokernel side of the adjunction bijection: `Hom(F⁻ᵢV, W) ≃ AdjReducedData hi V W`.
At `v ≠ i` a morphism restricts to `h v` through `reflFunctorMinus_equivAt_ne`; at `i` its
value on the cokernel `coker(sourceMap_V)` is determined by the family via `Submodule.liftQ`,
with well-definedness being exactly the constraint (C). Naturality on the reversed arrows into
`i` (`reflFunctorMinus_mapLinear_ne_eq`) recovers (C), and naturality away from `i`
(`reflFunctorMinus_mapLinear_ne_ne`) recovers (A). -/
theorem Etingof.homFMinusEquivReduced
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)]
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i)) :
    Nonempty
      ((@Etingof.QuiverRepresentationHom k Q _ (Etingof.reversedAtVertex Q i)
          (Etingof.reflectionFunctorMinus Q i hi V) W)
        ≃ Etingof.AdjReducedData hi V W) := by
  classical
  letI grp_ds : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  -- `g r`: the map out of `⊕_{i→j} V_j` assembled from the reduced family, i.e. the `a`-component
  -- is `W(revOut a) ∘ r.h a.fst`.  Its factorisation through the cokernel is `f.app i`.
  let g : Etingof.AdjReducedData hi V W →
      (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1) →ₗ[k]
        @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i) W i) :=
    fun r => DirectSum.toModule k (Etingof.ArrowsOutOf Q i)
      (@Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i) W i)
      (fun a => (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i) W
          a.fst i (Etingof.revOut hi a)).comp
        (r.h a.fst (Etingof.arrowsOutOf_target_ne_source hi a)))
  -- `g r` kills the source-map image (that is exactly constraint (C)).
  have hg : ∀ (r : Etingof.AdjReducedData hi V W),
      LinearMap.range (V.sourceMap i) ≤ LinearMap.ker (g r) := by
    intro r
    rw [LinearMap.range_le_ker_iff]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    have hs : V.sourceMap i x = ∑ a : Etingof.ArrowsOutOf Q i,
        DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1) a (V.mapLinear a.snd x) := by
      simp only [Etingof.QuiverRepresentation.sourceMap, LinearMap.sum_apply, LinearMap.comp_apply]
    rw [hs, map_sum]
    simp only [g, DirectSum.toModule_lof, LinearMap.comp_apply]
    exact r.constraint x
  -- The factored-through-cokernel map `coker(sourceMap) →ₗ W.obj i`.
  let liftG : Etingof.AdjReducedData hi V W →
      ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1) ⧸
          LinearMap.range (V.sourceMap i)) →ₗ[k]
        @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i) W i) :=
    fun r =>
      letI grp_Wi : AddCommGroup (@Etingof.QuiverRepresentation.obj k Q _
        (Etingof.reversedAtVertex Q i) W i) := Etingof.addCommGroupOfRing (k := k)
      (LinearMap.range (V.sourceMap i)).liftQ
        (g r : DirectSum (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1) →ₗ[k]
          @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i) W i) (hg r)
  -- `appAtI r : F⁻ᵢ(V).obj i →ₗ W.obj i` is `liftG r ∘ equivAt_eq`.
  let appAtI : Etingof.AdjReducedData hi V W →
      (@Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
          (Etingof.reflectionFunctorMinus Q i hi V) i →ₗ[k]
        @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i) W i) :=
    fun r => (liftG r).comp (Etingof.reflFunctorMinus_equivAt_eq hi V).toLinearMap
  -- The forward map `f ↦ (v ↦ f.app v ∘ equivAt_ne⁻¹)`.
  let toFun : (@Etingof.QuiverRepresentationHom k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi V) W) → Etingof.AdjReducedData hi V W :=
    fun f => {
      h := fun v hv =>
        ((@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
              (Etingof.reflectionFunctorMinus Q i hi V) W f v).comp
            (Etingof.reflFunctorMinus_equivAt_ne hi V v hv).symm.toLinearMap :
          V.obj v →ₗ[k]
            @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i) W v)
      compat := by
        intro a b ha hb e x
        rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.coe_toLinearMap]
        rw [← @Etingof.QuiverRepresentationHom.naturality k Q _ (Etingof.reversedAtVertex Q i)
          (Etingof.reflectionFunctorMinus Q i hi V) W f a b e
          ((Etingof.reflFunctorMinus_equivAt_ne hi V a ha).symm x)]
        congr 1
        apply (Etingof.reflFunctorMinus_equivAt_ne hi V b hb).injective
        rw [Etingof.reflFunctorMinus_mapLinear_ne_ne hi V ha hb e
          ((Etingof.reflFunctorMinus_equivAt_ne hi V a ha).symm x),
          LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      constraint := by
        intro x
        have step : ∀ a : Etingof.ArrowsOutOf Q i,
            (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i) W
                a.fst i (Etingof.revOut hi a))
              (((@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
                  (Etingof.reflectionFunctorMinus Q i hi V) W f a.fst).comp
                  (Etingof.reflFunctorMinus_equivAt_ne hi V a.fst
                    (Etingof.arrowsOutOf_target_ne_source hi a)).symm.toLinearMap)
                (V.mapLinear a.snd x)) =
              (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
                  (Etingof.reflectionFunctorMinus Q i hi V) W f i)
                (Etingof.reflFunctorMinus_mkQ hi V
                (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1) a
                  (V.mapLinear a.snd x))) := by
          intro a
          rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
            Etingof.reflFunctorMinus_mkQ_lof hi V a (V.mapLinear a.snd x)]
          exact (@Etingof.QuiverRepresentationHom.naturality k Q _ (Etingof.reversedAtVertex Q i)
            (Etingof.reflectionFunctorMinus Q i hi V) W f a.fst i (Etingof.revOut hi a) _).symm
        rw [Finset.sum_congr rfl (fun a _ => step a), ← map_sum, ← map_sum,
          Etingof.reflFunctorMinus_mkQ_kills_sourceMap hi V x, map_zero] }
  -- The inverse map: `r ↦ (v ↦ r.h v ∘ equivAt_ne)` off `i`, and `appAtI r` at `i`.
  let invFun : Etingof.AdjReducedData hi V W →
      (@Etingof.QuiverRepresentationHom k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi V) W) :=
    fun r =>
      @Etingof.QuiverRepresentationHom.mk k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi V) W
        (fun v => if hv : v = i then hv ▸ appAtI r
          else (r.h v hv).comp (Etingof.reflFunctorMinus_equivAt_ne hi V v hv).toLinearMap)
        (by
          intro a b e y
          by_cases ha : a = i
          · subst ha
            exact ((Etingof.isSource_reversedAtVertex_isSink hi b).false e).elim
          · by_cases hb : b = i
            · subst b
              rw [dif_pos rfl, dif_neg ha,
                Etingof.reflFunctorMinus_mapLinear_ne_eq hi V ha e y]
              -- LHS: `appAtI r (mkQ (lof ⟨a, reversedArrow_ne_eq ha e⟩ (equivAt_ne a ha y)))`.
              -- Unfold `appAtI = liftG ∘ equivAt_eq`; `equivAt_eq ∘ mkQ = Submodule.mkQ`;
              -- `liftG ∘ Submodule.mkQ = g`; `g (lof idx u) = W(revOut idx) (r.h idx.fst u)`.
              have hmkQ : (Etingof.reflFunctorMinus_equivAt_eq hi V)
                  (Etingof.reflFunctorMinus_mkQ hi V (DirectSum.lof k (Etingof.ArrowsOutOf Q i)
                    (fun a => V.obj a.1) ⟨a, Etingof.reversedArrow_ne_eq ha e⟩
                    (Etingof.reflFunctorMinus_equivAt_ne hi V a ha y))) =
                  Submodule.mkQ (LinearMap.range (V.sourceMap i))
                    (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1)
                      ⟨a, Etingof.reversedArrow_ne_eq ha e⟩
                      (Etingof.reflFunctorMinus_equivAt_ne hi V a ha y)) := by
                unfold Etingof.reflFunctorMinus_mkQ
                rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
              show (liftG r) ((Etingof.reflFunctorMinus_equivAt_eq hi V) _) = _
              rw [hmkQ]
              show (g r) (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1)
                ⟨a, Etingof.reversedArrow_ne_eq ha e⟩
                (Etingof.reflFunctorMinus_equivAt_ne hi V a ha y)) = _
              show (DirectSum.toModule k (Etingof.ArrowsOutOf Q i) _ _) _ = _
              rw [DirectSum.toModule_lof]
              simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
              rw [Etingof.revOut_reversedArrow_ne_eq hi ha e]
            · rw [dif_neg ha, dif_neg hb]
              simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
              rw [Etingof.reflFunctorMinus_mapLinear_ne_ne hi V ha hb e y]
              exact (r.compat ha hb e (Etingof.reflFunctorMinus_equivAt_ne hi V a ha y)).symm)
  -- `reflFunctorMinus_mkQ` is surjective (a composite of two surjections).
  have hsurj : Function.Surjective (Etingof.reflFunctorMinus_mkQ hi V) := by
    intro z
    obtain ⟨w, hw⟩ := Submodule.mkQ_surjective (LinearMap.range (V.sourceMap i))
      ((Etingof.reflFunctorMinus_equivAt_eq hi V) z)
    exact ⟨w, by
      unfold Etingof.reflFunctorMinus_mkQ
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hw, LinearEquiv.symm_apply_apply]⟩
  refine ⟨⟨toFun, invFun, ?_, ?_⟩⟩
  · -- left_inv: `invFun (toFun f) = f`
    intro f
    refine @Etingof.QuiverRepresentationHom.ext k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi V) W _ _ (fun v => ?_)
    by_cases hv : v = i
    · subst v
      -- at `i`, `(invFun (toFun f)).app i = appAtI (toFun f)`; agree with `f.app i` on
      -- `mkQ`-generators, then conclude by surjectivity of `mkQ`.
      have happ : (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
          (Etingof.reflectionFunctorMinus Q i hi V) W (invFun (toFun f)) i) =
          appAtI (toFun f) :=
        LinearMap.ext fun z => by
          show (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
              (Etingof.reflectionFunctorMinus Q i hi V) W
              (@Etingof.QuiverRepresentationHom.mk k Q _ (Etingof.reversedAtVertex Q i)
                (Etingof.reflectionFunctorMinus Q i hi V) W _ _) i) z = appAtI (toFun f) z
          simp only [reduceDIte]
      refine happ.trans (LinearMap.ext fun z => ?_)
      obtain ⟨d, rfl⟩ := hsurj z
      induction d using DirectSum.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | of a u =>
        -- `DirectSum.of` is definitionally `DirectSum.lof`; restate in `lof` form.
        show appAtI (toFun f) (Etingof.reflFunctorMinus_mkQ hi V
              (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1) a u)) =
            (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
              (Etingof.reflectionFunctorMinus Q i hi V) W f i)
              (Etingof.reflFunctorMinus_mkQ hi V
                (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1) a u))
        have hmkQ : (Etingof.reflFunctorMinus_equivAt_eq hi V)
            (Etingof.reflFunctorMinus_mkQ hi V (DirectSum.lof k (Etingof.ArrowsOutOf Q i)
              (fun a => V.obj a.1) a u)) =
            Submodule.mkQ (LinearMap.range (V.sourceMap i))
              (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1) a u) := by
          unfold Etingof.reflFunctorMinus_mkQ
          rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        have hLHS : appAtI (toFun f) (Etingof.reflFunctorMinus_mkQ hi V
              (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1) a u)) =
            (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i) W
                a.fst i (Etingof.revOut hi a))
              ((toFun f).h a.fst (Etingof.arrowsOutOf_target_ne_source hi a) u) := by
          show (liftG (toFun f)) ((Etingof.reflFunctorMinus_equivAt_eq hi V) _) = _
          rw [hmkQ]
          show (g (toFun f))
            (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => V.obj a.1) a u) = _
          show (DirectSum.toModule k (Etingof.ArrowsOutOf Q i) _ _) _ = _
          rw [DirectSum.toModule_lof, LinearMap.comp_apply]
        rw [hLHS, Etingof.reflFunctorMinus_mkQ_lof hi V a u,
          @Etingof.QuiverRepresentationHom.naturality k Q _ (Etingof.reversedAtVertex Q i)
            (Etingof.reflectionFunctorMinus Q i hi V) W f a.fst i (Etingof.revOut hi a)
            ((Etingof.reflFunctorMinus_equivAt_ne hi V a.fst
              (Etingof.arrowsOutOf_target_ne_source hi a)).symm u)]
        congr 1
    · -- at `v ≠ i`, `(invFun (toFun f)).app v = (toFun f).h v hv ∘ equivAt_ne`, and
      -- `(toFun f).h v hv = f.app v ∘ equivAt_ne⁻¹`, so the equivalences cancel.
      refine LinearMap.ext fun x => ?_
      show (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
          (Etingof.reflectionFunctorMinus Q i hi V) W
          (@Etingof.QuiverRepresentationHom.mk k Q _ (Etingof.reversedAtVertex Q i)
            (Etingof.reflectionFunctorMinus Q i hi V) W _ _) v) x = _
      simp only [dif_neg hv]
      show (((@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
          (Etingof.reflectionFunctorMinus Q i hi V) W f v).comp
          (Etingof.reflFunctorMinus_equivAt_ne hi V v hv).symm.toLinearMap).comp
          (Etingof.reflFunctorMinus_equivAt_ne hi V v hv).toLinearMap) x = _
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  · -- right_inv: `toFun (invFun r) = r`
    intro r
    ext v hv x
    show ((@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi V) W
        (@Etingof.QuiverRepresentationHom.mk k Q _ (Etingof.reversedAtVertex Q i)
          (Etingof.reflectionFunctorMinus Q i hi V) W _ _) v).comp
        (Etingof.reflFunctorMinus_equivAt_ne hi V v hv).symm.toLinearMap) x = r.h v hv x
    simp only [dif_neg hv]
    show (((r.h v hv).comp (Etingof.reflFunctorMinus_equivAt_ne hi V v hv).toLinearMap).comp
        (Etingof.reflFunctorMinus_equivAt_ne hi V v hv).symm.toLinearMap) x = r.h v hv x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

/-- The kernel side of the adjunction bijection:
`Hom(V, transportReversedTwice (F⁺ᵢW)) ≃ AdjReducedData hi V W`. At `v ≠ i` a morphism gives
`h v` through `transportReversedTwice_obj` and `reflFunctorPlus_equivAt_ne`; at `i` its value
lands in `ker(sinkMap_W)` via `LinearMap.codRestrict`, the kernel condition being exactly the
constraint (C) (`Φ_comp_source_eq_zero`, after reindexing `ArrowsInto (Q̄ᵢ) i ≃ ArrowsOutOf Q i`
by `arrowReindexEquiv`). Naturality of a morphism on arrows out of `i` in `Q`
(`reflFunctorPlus_mapLinear_eq_ne`, through `transportReversedTwice_mapLinear_heq`) recovers (C),
and naturality away from `i` (`reflFunctorPlus_mapLinear_ne_ne`) recovers (A). -/
theorem Etingof.homTransportPlusEquivReduced
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)]
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i)) :
    Nonempty
      (Etingof.QuiverRepresentationHom k Q V
          (Etingof.QuiverRepresentation.transportReversedTwice
            (@Etingof.reflectionFunctorPlus k _ Q _ (Etingof.reversedAtVertex Q i) i
              (Etingof.isSource_reversedAtVertex_isSink hi) W))
        ≃ Etingof.AdjReducedData hi V W) := by
  sorry

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
  obtain ⟨eL⟩ := Etingof.homFMinusEquivReduced hi V W
  obtain ⟨eR⟩ := Etingof.homTransportPlusEquivReduced hi V W
  exact ⟨eL.trans eR.symm⟩
