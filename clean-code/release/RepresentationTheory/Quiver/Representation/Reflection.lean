/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.AuxiliaryQuiverRepresentationTransform
import RepresentationTheory.QuiverRepresentationQuotientTransform
import RepresentationTheory.Quiver.LinearAlgebra.Auxiliary
import RepresentationTheory.CategoryTheory.QuiverLinearMaps
import RepresentationTheory.Algebra.Quiver.LinearRepresentationCategory

open CategoryTheory
open RepresentationTheory.AuxiliaryQuiverRepresentationTransform
open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram
open RepresentationTheory.CategoryTheory.QuiverLinearMaps
open RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver
open RepresentationTheory.QuiverRepresentationQuotientTransform
open RepresentationTheory.QuiverVertexPredicates
open RepresentationTheory.QuiverVertexReversal

namespace RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram

/-! ## Transport accessors for `auxiliaryAt`

`auxiliaryAt X` moves a representation of the double-reversed quiver `(Q̄ᵢ)̄ᵢ`
back to `Q` along the instance equality `auxiliaryQuiver_eq Q i : (Q̄ᵢ)̄ᵢ = Q`. Since
the `obj` field of `QuiverLinearDiagram` does not mention the `Quiver` instance, transport
leaves the vertex spaces unchanged; the `mapLinear` field does mention it (through the arrow
type `v ⟶ w`), so it is transported through the arrow identification.

These lemmas expose those two facts so downstream code (e.g. the adjunction of
Exercise 7.9.8) can rewrite `(auxiliaryAt X).obj` / `.map` back in terms of
`X` without unfolding the `▸`. They are stated first for two arbitrary equal `Quiver`
instances (where `subst` discharges everything) and then specialized. -/

/-- The object assigned to each vertex is unchanged by quiver reindexing. -/
theorem reindex_object {k : Type*} [CommSemiring k] {Q : Type*}
    {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    (X : @QuiverLinearDiagram k Q _ I₁) (v : Q) :
    @QuiverLinearDiagram.obj k Q _ I₂ (h ▸ X) v =
    @QuiverLinearDiagram.obj k Q _ I₁ X v := by
  subst h; rfl

/-- Arrow maps agree heterogeneously after transporting the quiver structure. -/
theorem hom_heq_of_quiver_eq {k : Type*} [CommSemiring k] {Q : Type*}
    {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    (X : @QuiverLinearDiagram k Q _ I₁) (a b : Q) (e : @Quiver.Hom Q I₂ a b) :
    HEq
      (@QuiverLinearDiagram.map k Q _ I₂ (h ▸ X) a b e)
      (@QuiverLinearDiagram.map k Q _ I₁ X a b (h.symm ▸ e)) := by
  subst h; rfl

variable {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q] {i : Q}

/-- The reflected and original vertex objects are equal after reindexing. -/
theorem reflectAt_reindex_object
    (X : @QuiverLinearDiagram k Q _
      (@reverseAtVertex Q _ (reverseAtVertex Q i) i)) (v : Q) :
    @QuiverLinearDiagram.obj k Q _ inst
      (QuiverLinearDiagram.auxiliaryAt X) v =
    @QuiverLinearDiagram.obj k Q _
      (@reverseAtVertex Q _ (reverseAtVertex Q i) i) X v :=
  reindex_object (auxiliaryQuiver_eq Q i) X v

/-- The reflected arrow maps coincide heterogeneously after the indexing transport. -/
theorem reflectAt_reindex_hom_heq
    (X : @QuiverLinearDiagram k Q _
      (@reverseAtVertex Q _ (reverseAtVertex Q i) i))
    (a b : Q) (e : @Quiver.Hom Q inst a b) :
    HEq
      (@QuiverLinearDiagram.map k Q _ inst
        (QuiverLinearDiagram.auxiliaryAt X) a b e)
      (@QuiverLinearDiagram.map k Q _
        (@reverseAtVertex Q _ (reverseAtVertex Q i) i) X a b
        ((auxiliaryQuiver_eq Q i).symm ▸ e)) :=
  hom_heq_of_quiver_eq (auxiliaryQuiver_eq Q i) X a b e

/-! ### Transport packaged as `LinearEquiv`

The two accessors above are stated with `HEq`. For assembling the adjunction it is far more
convenient to package the transport of the vertex space as an honest `LinearEquiv` (absorbing
both the object-type transport and the transported `AddCommMonoid`/`Module` instances at once),
so that transport-compatibility of `mapLinear` becomes a plain equation rather than an `HEq`.
Both are proved by `subst`, after which the transport is literally the identity. -/

/-- Provides a vertexwise linear equivalence after reindexing a representation along equal
quivers. -/
noncomputable def reindex {k : Type*} [CommSemiring k] {Q : Type*}
    {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    (X : @QuiverLinearDiagram k Q _ I₁) (v : Q) :
    @QuiverLinearDiagram.obj k Q _ I₂ (h ▸ X) v ≃ₗ[k]
    @QuiverLinearDiagram.obj k Q _ I₁ X v :=
  match I₂, h with
  | _, rfl => LinearEquiv.refl k _

/-- The reindexing equivalences intertwine the transported arrow maps. -/
theorem reindex_naturality {k : Type*} [CommSemiring k] {Q : Type*}
    {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    (X : @QuiverLinearDiagram k Q _ I₁) (a b : Q) (e : @Quiver.Hom Q I₂ a b)
    (x : @QuiverLinearDiagram.obj k Q _ I₂ (h ▸ X) a) :
    reindex h X b
        (@QuiverLinearDiagram.map k Q _ I₂ (h ▸ X) a b e x) =
      @QuiverLinearDiagram.map k Q _ I₁ X a b (h.symm ▸ e)
        (reindex h X a x) := by
  subst h; rfl

/-- Gives the vertexwise equivalence between a reflected representation and its original
indexing. -/
noncomputable def reflectAt_reindex
    (X : @QuiverLinearDiagram k Q _
      (@reverseAtVertex Q _ (reverseAtVertex Q i) i)) (v : Q) :
    @QuiverLinearDiagram.obj k Q _ inst
      (QuiverLinearDiagram.auxiliaryAt X) v ≃ₗ[k]
    @QuiverLinearDiagram.obj k Q _
      (@reverseAtVertex Q _ (reverseAtVertex Q i) i) X v :=
  reindex (auxiliaryQuiver_eq Q i) X v

/-- The reflection reindexing equivalences commute with the corresponding arrow maps. -/
theorem reflectAt_reindex_naturality
    (X : @QuiverLinearDiagram k Q _
      (@reverseAtVertex Q _ (reverseAtVertex Q i) i))
    (a b : Q) (e : @Quiver.Hom Q inst a b)
    (x : @QuiverLinearDiagram.obj k Q _ inst
      (QuiverLinearDiagram.auxiliaryAt X) a) :
    reflectAt_reindex X b
        (@QuiverLinearDiagram.map k Q _ inst
          (QuiverLinearDiagram.auxiliaryAt X) a b e x) =
      @QuiverLinearDiagram.map k Q _
        (@reverseAtVertex Q _ (reverseAtVertex Q i) i) X a b
        ((auxiliaryQuiver_eq Q i).symm ▸ e)
        (reflectAt_reindex X a x) :=
  reindex_naturality (auxiliaryQuiver_eq Q i) X a b e x

end RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram

namespace RepresentationTheory.Quiver.Representation.Reflection

/-!
## Proof blueprint for `reflectionHomEquiv_source_target_nonempty` (the adjunction bijection)

The adjunction bijection is built from `reflectionHomEquiv_nonempty` and
`reflectionHomEquiv_dual_nonempty`, whose composite is
`reflectionHomEquiv_source_target_nonempty`. This blueprint records the structure of the
construction.

**Key reduction.** Write `hi' := auxiliaryBackward hi` (so `i` is a sink of
`Q̄ᵢ`). Both hom-sets are equivalent to the *same* reduced data: a family
`hᵥ : V.obj v →ₗ[k] W.obj v` for every `v ≠ i` such that

* (A) for every arrow `e : a ⟶ b` of `Q` with `a ≠ i`, `b ≠ i` (these are exactly the
  arrows of `Q̄ᵢ` not touching `i`), `W.map e ∘ hₐ = h_b ∘ V.map e`; and
* (C) `∑ (a : OutgoingArrow Q i), W.map (rev a) (h_{a.fst} (V.map a.snd x)) = 0`
  for all `x : V.obj i`, where `rev a : a.fst ⟶ i` in `Q̄ᵢ` is the reversed arrow.

*From `f : Hom(F⁻ᵢV, W)`* set `hᵥ := f.app v ∘ (transformedVertexEquivOfNe hi V v _).symm`.
Naturality of `f` on a reversed arrow `a.fst → i` (case `ne_eq`, via
`transformedMap_to_distinguished`) forces the `a`-component of the induced map on
`coker(outgoingDirectSumMap_V)` to be `W.map (rev a) ∘ hₐ`; well-definedness of `f.app i`
on the
cokernel is precisely (C).

*From `g : Hom(V, auxiliaryAt (F⁺ᵢW))`* set `hᵥ := (auxiliaryRepresentationLinearEquivOfNe
hi' W v _) ∘ g.app v` (using `reflectAt_reindex_object` to see `g.app v : V.obj v →
W.obj v` for `v ≠ i`). Naturality of `g` on an arrow `i → a.fst` of `Q` (case `eq_ne`, via
`auxiliary_arrow_map_from_selected` and `reflectAt_reindex_hom_heq`) forces the
`a`-component of `g.app i : V.obj i → ker(auxiliaryDirectSumMap_W)` to be
`hₐ ∘ V.map a.snd`; landing in the kernel `auxiliaryDirectSumMap_W = 0` is precisely
(C), which is `auxiliarySum_eq_zero` after
reindexing `auxiliaryTypeAt (Q̄ᵢ) i ≃ OutgoingArrow Q i` via `outgoingIncomingIndexEquiv hi'`.

**Assembly.** Define `toFun`, `invFun` by extracting the reduced family and rebuilding on the
other side (kernel corestriction via `LinearMap.codRestrict` + (C); cokernel factoring via
`Submodule.liftQ` + (C)). Prove `left_inv`/`right_inv` by `QuiverLinearHom`
extensionality: at `v ≠ i` both sides are `hᵥ` transported; at `v = i` use uniqueness of the
cokernel map out of `mkQ` / the kernel `subtype` being injective. Reusable ingredients:
`outgoingIncomingIndexEquiv`, `surjective_of_auxiliaryPreimages`, `auxiliarySum_eq_zero`,
`auxiliaryRangeEqKer`, the auxiliary-arrow cast lemmas, and the `heq_apply` /
`heq_coe_linearMap` toolkit.

## Decomposition (this file)

The construction is decomposed along the blueprint's two directions through a shared reduced-data
type `ReflectionHom hi V W`: a family `h v : V v →ₗ W v` for `v ≠ i` subject to
arrow-compatibility (A) away from `i` and the source constraint (C) at `i`. The main theorem
`reflectionHomEquiv_source_target_nonempty` is assembled from two hom-set equivalences, each
proved separately:

* `reflectionHomEquiv_nonempty : Hom(F⁻ᵢV, W) ≃ ReflectionHom hi V W`, the cokernel side,
  using the transformed-map reductions and `Submodule.liftQ` (constraint (C) is exactly the
  well-definedness of the map out of the cokernel at `i`);
* `reflectionHomEquiv_dual_nonempty : Hom(V, auxiliaryAt (F⁺ᵢW)) ≃ ReflectionHom hi V W`,
  the kernel side, using the reflection-reindexing accessors above together with the
  auxiliary-arrow-map reductions and `LinearMap.codRestrict` (constraint (C) is exactly
  landing in the kernel, i.e. `Φ_comp_source_eq_zero`).
-/

/-- The target vertex recorded by an outgoing-arrow index differs from the distinguished vertex. -/
theorem outgoingIndex_ne
    {Q : Type*} [Quiver Q] {i : Q} (hi : vertexCondition Q i)
    (a : OutgoingArrow Q i) : a.fst ≠ i :=
  fun h => (hi i).false (cast (congrArg (i ⟶ ·) h) a.snd)

/-- Extracts the incoming arrow associated with an outgoing-arrow index. -/
noncomputable def arrowTo
    {Q : Type*} [DecidableEq Q] [Quiver Q] {i : Q} (hi : vertexCondition Q i)
    (a : OutgoingArrow Q i) :
    @Quiver.Hom Q (reverseAtVertex Q i) a.fst i :=
  cast (reversedAtHom_eq_of_ne_eq (outgoingIndex_ne hi a) rfl).symm
    a.snd

/-- Morphisms between representations after reflection at a distinguished vertex. -/
structure ReflectionHom
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : vertexCondition Q i) [Fintype (OutgoingArrow Q i)]
    (V : QuiverLinearDiagram k Q)
    (W : @QuiverLinearDiagram k Q _ (reverseAtVertex Q i)) where
  /-- Returns the linear component of a reflection morphism at a non-distinguished vertex. -/
  map : ∀ v, v ≠ i → (V.obj v →ₗ[k]
    @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W v)
  /-- The component maps commute with arrows away from the distinguished vertex. -/
  comm : ∀ {a b : Q} (ha : a ≠ i) (hb : b ≠ i)
      (e : @Quiver.Hom Q (reverseAtVertex Q i) a b) (x : V.obj a),
      @QuiverLinearDiagram.map k Q _ (reverseAtVertex Q i) W a b e
          (map a ha x) =
        map b hb (V.map (auxiliaryPreserveHom ha hb e) x)
  /-- The sum of the reflected component contributions vanishes at the distinguished vertex. -/
  sum_apply_eq_zero : ∀ (x : V.obj i),
      ∑ a : OutgoingArrow Q i,
        @QuiverLinearDiagram.map k Q _ (reverseAtVertex Q i) W a.fst i
          (arrowTo hi a)
          (map a.fst (outgoingIndex_ne hi a) (V.map a.snd x)) = 0

/-- Reflection morphisms are determined by their component maps away from the distinguished
vertex. -/
@[ext] theorem ReflectionHom.ext
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} {hi : vertexCondition Q i} [Fintype (OutgoingArrow Q i)]
    {V : QuiverLinearDiagram k Q}
    {W : @QuiverLinearDiagram k Q _ (reverseAtVertex Q i)}
    {r₁ r₂ : ReflectionHom hi V W} (h : r₁.map = r₂.map) : r₁ = r₂ := by
  cases r₁; cases r₂; cases h; rfl

-- `QuiverLinearHom.ext` now lives in
-- `RepresentationTheory.Algebra.Quiver.LinearRepresentationCategory`, alongside the `Rep Q`
-- category instance.

/-! ### Index round-trip helpers for `arrowTo`

`arrowTo hi a : a.fst ⟶_{Q̄ᵢ} i` and
`reverseArrowAtVertex ha : (a ⟶_{Q̄ᵢ} i) → (i ⟶ a)` are both
`cast`s along `ReversedAtVertexHom_ne_eq`, so composing them in either order is the identity. -/

/-- Converting an extracted incoming arrow back recovers the outgoing arrow stored in the index. -/
theorem mk_arrowTo
    {Q : Type*} [DecidableEq Q] [Quiver Q] {i : Q} (hi : vertexCondition Q i)
    (a : OutgoingArrow Q i) :
  reverseArrowAtVertex (outgoingIndex_ne hi a)
      (arrowTo hi a) = a.snd := by
  obtain ⟨j, e⟩ := a
  unfold arrowTo
  rw [auxiliaryMapTo_eq_cast]
  apply eq_of_heq
  exact (cast_heq _ _).trans (cast_heq _ _)

/-- Extracting the incoming arrow from an outgoing index constructed from an incoming arrow
returns the original arrow. -/
theorem arrowTo_mk
    {Q : Type*} [DecidableEq Q] [Quiver Q] {i a : Q} (hi : vertexCondition Q i) (ha : a ≠ i)
    (e : @Quiver.Hom Q (reverseAtVertex Q i) a i) :
    arrowTo hi ⟨a, reverseArrowAtVertex ha e⟩ = e := by
  unfold arrowTo
  rw [auxiliaryMapTo_eq_cast]
  apply eq_of_heq
  exact (cast_heq _ _).trans (cast_heq _ _)

open Classical in
/-- Describes the reflected arrow map on a single direct-sum summand. -/
theorem reflectionMap_lof
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : vertexCondition Q i) (V : QuiverLinearDiagram k Q)
    [Fintype (OutgoingArrow Q i)]
    (a : OutgoingArrow Q i) (u : V.obj a.fst) :
    transformedQuotientMap hi V
        (DirectSum.lof k (OutgoingArrow Q i) (fun a => V.obj a.1) a u) =
      @QuiverLinearDiagram.map k Q _ (reverseAtVertex Q i)
        (quotientTransformedRepresentation Q i hi V) a.fst i (arrowTo hi a)
        ((transformedVertexEquivOfNe hi V a.fst
          (outgoingIndex_ne hi a)).symm u) := by
  classical
  obtain ⟨j, e⟩ := a
  have key := transformedMap_to_distinguished hi V
    (outgoingIndex_ne hi ⟨j, e⟩) (arrowTo hi ⟨j, e⟩)
    ((transformedVertexEquivOfNe hi V (⟨j, e⟩ : OutgoingArrow Q i).fst
      (outgoingIndex_ne hi ⟨j, e⟩)).symm u)
  rw [LinearEquiv.apply_symm_apply, mk_arrowTo hi ⟨j, e⟩] at key
  exact key.symm

set_option maxHeartbeats 3200000 in
/-- Constructs the equivalence between the displayed reflected morphism space and reflection
morphisms. -/
noncomputable def reflectionHomEquiv
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : vertexCondition Q i) [Fintype (OutgoingArrow Q i)]
    (V : QuiverLinearDiagram k Q)
    (W : @QuiverLinearDiagram k Q _ (reverseAtVertex Q i)) :
    (@QuiverLinearHom k Q _ (reverseAtVertex Q i)
        (quotientTransformedRepresentation Q i hi V) W)
      ≃ ReflectionHom hi V W := by
  classical
  letI grp_ds : AddCommGroup (DirectSum (OutgoingArrow Q i) (fun a => V.obj a.1)) :=
    moduleAddCommGroupOfCommRing (k := k)
  -- `g r`: the map out of `⊕_{i→j} V_j` assembled from the reduced family, i.e. the
  -- `a`-component
  -- is `W(arrowTo a) ∘ r.map a.fst`.  Its factorisation through the cokernel is `f.app i`.
  let g : ReflectionHom hi V W →
      (DirectSum (OutgoingArrow Q i) (fun a => V.obj a.1) →ₗ[k]
        @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W i) :=
    fun r => DirectSum.toModule k (OutgoingArrow Q i)
      (@QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W i)
      (fun a => (@QuiverLinearDiagram.map k Q _ (reverseAtVertex Q i) W
          a.fst i (arrowTo hi a)).comp
        (r.map a.fst (outgoingIndex_ne hi a)))
  -- `g r` kills the source-map image (that is exactly constraint (C)).
  have hg : ∀ (r : ReflectionHom hi V W),
      LinearMap.range (V.outgoingDirectSumMap i) ≤ LinearMap.ker (g r) := by
    intro r
    rw [LinearMap.range_le_ker_iff]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    have hs : V.outgoingDirectSumMap i x = ∑ a : OutgoingArrow Q i,
        DirectSum.lof k (OutgoingArrow Q i) (fun a => V.obj a.1) a (V.map a.snd x) := by
      simp only [QuiverLinearDiagram.outgoingDirectSumMap, LinearMap.sum_apply,
        LinearMap.comp_apply]
    rw [hs, map_sum]
    simp only [g, DirectSum.toModule_lof, LinearMap.comp_apply]
    exact r.sum_apply_eq_zero x
  -- The factored-through-cokernel map `coker(outgoingDirectSumMap) →ₗ W.obj i`.
  let liftG : ReflectionHom hi V W →
      ((DirectSum (OutgoingArrow Q i) (fun a => V.obj a.1) ⧸
          LinearMap.range (V.outgoingDirectSumMap i)) →ₗ[k]
        @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W i) :=
    fun r =>
      letI grp_Wi : AddCommGroup (@QuiverLinearDiagram.obj k Q _
        (reverseAtVertex Q i) W i) := moduleAddCommGroupOfCommRing (k := k)
      (LinearMap.range (V.outgoingDirectSumMap i)).liftQ
        (g r : DirectSum (OutgoingArrow Q i) (fun a => V.obj a.1) →ₗ[k]
          @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W i) (hg r)
  -- `appAtI r : F⁻ᵢ(V).obj i →ₗ W.obj i` is `liftG r ∘ equivAt_eq`.
  let appAtI : ReflectionHom hi V W →
      (@QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i)
          (quotientTransformedRepresentation Q i hi V) i →ₗ[k]
        @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W i) :=
    fun r => (liftG r).comp (transformedVertexEquivQuotient hi V).toLinearMap
  -- The forward map `f ↦ (v ↦ f.app v ∘ equivAt_ne⁻¹)`.
  let toFun : (@QuiverLinearHom k Q _ (reverseAtVertex Q i)
        (quotientTransformedRepresentation Q i hi V) W) → ReflectionHom hi V W :=
    fun f => {
      map := fun v hv =>
        ((@QuiverLinearHom.app k Q _ (reverseAtVertex Q i)
              (quotientTransformedRepresentation Q i hi V) W f v).comp
            (transformedVertexEquivOfNe hi V v hv).symm.toLinearMap :
          V.obj v →ₗ[k]
            @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W v)
      comm := by
        intro a b ha hb e x
        rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.coe_toLinearMap]
        rw [← @QuiverLinearHom.naturality k Q _ (reverseAtVertex Q i)
          (quotientTransformedRepresentation Q i hi V) W f a b e
          ((transformedVertexEquivOfNe hi V a ha).symm x)]
        congr 1
        apply (transformedVertexEquivOfNe hi V b hb).injective
        rw [transformedMap_of_ne hi V ha hb e
          ((transformedVertexEquivOfNe hi V a ha).symm x),
          LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      sum_apply_eq_zero := by
        intro x
        have step : ∀ a : OutgoingArrow Q i,
            (@QuiverLinearDiagram.map k Q _ (reverseAtVertex Q i) W
                a.fst i (arrowTo hi a))
              (((@QuiverLinearHom.app k Q _ (reverseAtVertex Q i)
                  (quotientTransformedRepresentation Q i hi V) W f a.fst).comp
                  (transformedVertexEquivOfNe hi V a.fst
                    (outgoingIndex_ne hi a)).symm.toLinearMap)
                (V.map a.snd x)) =
              (@QuiverLinearHom.app k Q _ (reverseAtVertex Q i)
                  (quotientTransformedRepresentation Q i hi V) W f i)
                (transformedQuotientMap hi V
                (DirectSum.lof k (OutgoingArrow Q i) (fun a => V.obj a.1) a
                  (V.map a.snd x))) := by
          intro a
          rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
            reflectionMap_lof hi V a (V.map a.snd x)]
          exact (@QuiverLinearHom.naturality k Q _ (reverseAtVertex Q i)
            (quotientTransformedRepresentation Q i hi V) W f a.fst i (arrowTo hi a) _).symm
        rw [Finset.sum_congr rfl (fun a _ => step a), ← map_sum, ← map_sum,
          transformedQuotientMap_sum_eq_zero hi V x, map_zero] }
  -- The inverse map: `r ↦ (v ↦ r.map v ∘ equivAt_ne)` off `i`, and `appAtI r` at `i`.
  let invFun : ReflectionHom hi V W →
      (@QuiverLinearHom k Q _ (reverseAtVertex Q i)
        (quotientTransformedRepresentation Q i hi V) W) :=
    fun r =>
      @QuiverLinearHom.mk k Q _ (reverseAtVertex Q i)
        (quotientTransformedRepresentation Q i hi V) W
        (fun v => if hv : v = i then hv ▸ appAtI r
          else (r.map v hv).comp (transformedVertexEquivOfNe hi V v hv).toLinearMap)
        (by
          intro a b e y
          by_cases ha : a = i
          · subst ha
            exact ((auxiliaryBackward hi b).false e).elim
          · by_cases hb : b = i
            · subst b
              rw [dif_pos rfl, dif_neg ha,
                transformedMap_to_distinguished hi V ha e y]
              -- LHS: `appAtI r (mkQ (lof ⟨a, reverseArrowAtVertex ha e⟩ (equivAt_ne a ha y)))`.
              -- Unfold `appAtI = liftG ∘ equivAt_eq`; `equivAt_eq ∘ mkQ = Submodule.mkQ`;
              -- `liftG ∘ Submodule.mkQ = g`; `g (lof idx u) = W(arrowTo idx) (r.map idx.fst u)`.
              have hmkQ : (transformedVertexEquivQuotient hi V)
                  (transformedQuotientMap hi V (DirectSum.lof k (OutgoingArrow Q i)
                    (fun a => V.obj a.1) ⟨a, reverseArrowAtVertex ha e⟩
                    (transformedVertexEquivOfNe hi V a ha y))) =
                  Submodule.mkQ (LinearMap.range (V.outgoingDirectSumMap i))
                    (DirectSum.lof k (OutgoingArrow Q i) (fun a => V.obj a.1)
                      ⟨a, reverseArrowAtVertex ha e⟩
                      (transformedVertexEquivOfNe hi V a ha y)) := by
                unfold transformedQuotientMap
                rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
              change (liftG r) ((transformedVertexEquivQuotient hi V) _) = _
              rw [hmkQ]
              change (g r) (DirectSum.lof k (OutgoingArrow Q i) (fun a => V.obj a.1)
                ⟨a, reverseArrowAtVertex ha e⟩
                (transformedVertexEquivOfNe hi V a ha y)) = _
              change (DirectSum.toModule k (OutgoingArrow Q i) _ _) _ = _
              rw [DirectSum.toModule_lof]
              simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
              rw [arrowTo_mk hi ha e]
            · rw [dif_neg ha, dif_neg hb]
              simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
              rw [transformedMap_of_ne hi V ha hb e y]
              exact (r.comm ha hb e (transformedVertexEquivOfNe hi V a ha y)).symm)
  -- `transformedQuotientMap` is surjective (a composite of two surjections).
  have hsurj : Function.Surjective (transformedQuotientMap hi V) := by
    intro z
    obtain ⟨w, hw⟩ := Submodule.mkQ_surjective (LinearMap.range (V.outgoingDirectSumMap i))
      ((transformedVertexEquivQuotient hi V) z)
    exact ⟨w, by
      unfold transformedQuotientMap
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hw, LinearEquiv.symm_apply_apply]⟩
  refine ⟨toFun, invFun, ?_, ?_⟩
  · -- left_inv: `invFun (toFun f) = f`
    intro f
    refine @QuiverLinearHom.ext k Q _ (reverseAtVertex Q i)
      (quotientTransformedRepresentation Q i hi V) W _ _ (fun v => ?_)
    by_cases hv : v = i
    · subst v
      -- at `i`, `(invFun (toFun f)).app i = appAtI (toFun f)`; agree with `f.app i` on
      -- `mkQ`-generators, then conclude by surjectivity of `mkQ`.
      have happ : (@QuiverLinearHom.app k Q _ (reverseAtVertex Q i)
          (quotientTransformedRepresentation Q i hi V) W (invFun (toFun f)) i) =
          appAtI (toFun f) :=
        LinearMap.ext fun z => by
          change (@QuiverLinearHom.app k Q _ (reverseAtVertex Q i)
              (quotientTransformedRepresentation Q i hi V) W
              (@QuiverLinearHom.mk k Q _ (reverseAtVertex Q i)
                (quotientTransformedRepresentation Q i hi V) W _ _) i) z = appAtI (toFun f) z
          simp only [reduceDIte]
      refine happ.trans (LinearMap.ext fun z => ?_)
      obtain ⟨d, rfl⟩ := hsurj z
      induction d using DirectSum.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | of a u =>
        -- `DirectSum.of` is definitionally `DirectSum.lof`; restate in `lof` form.
        change appAtI (toFun f) (transformedQuotientMap hi V
              (DirectSum.lof k (OutgoingArrow Q i) (fun a => V.obj a.1) a u)) =
            (@QuiverLinearHom.app k Q _ (reverseAtVertex Q i)
              (quotientTransformedRepresentation Q i hi V) W f i)
              (transformedQuotientMap hi V
                (DirectSum.lof k (OutgoingArrow Q i) (fun a => V.obj a.1) a u))
        have hmkQ : (transformedVertexEquivQuotient hi V)
            (transformedQuotientMap hi V (DirectSum.lof k (OutgoingArrow Q i)
              (fun a => V.obj a.1) a u)) =
            Submodule.mkQ (LinearMap.range (V.outgoingDirectSumMap i))
              (DirectSum.lof k (OutgoingArrow Q i) (fun a => V.obj a.1) a u) := by
          unfold transformedQuotientMap
          rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        have hLHS : appAtI (toFun f) (transformedQuotientMap hi V
              (DirectSum.lof k (OutgoingArrow Q i) (fun a => V.obj a.1) a u)) =
            (@QuiverLinearDiagram.map k Q _ (reverseAtVertex Q i) W
                a.fst i (arrowTo hi a))
              ((toFun f).map a.fst (outgoingIndex_ne hi a) u) := by
          change (liftG (toFun f)) ((transformedVertexEquivQuotient hi V) _) = _
          rw [hmkQ]
          change (g (toFun f))
            (DirectSum.lof k (OutgoingArrow Q i) (fun a => V.obj a.1) a u) = _
          change (DirectSum.toModule k (OutgoingArrow Q i) _ _) _ = _
          rw [DirectSum.toModule_lof, LinearMap.comp_apply]
        rw [hLHS, reflectionMap_lof hi V a u,
          @QuiverLinearHom.naturality k Q _ (reverseAtVertex Q i)
            (quotientTransformedRepresentation Q i hi V) W f a.fst i (arrowTo hi a)
            ((transformedVertexEquivOfNe hi V a.fst
              (outgoingIndex_ne hi a)).symm u)]
        congr 1
    · -- at `v ≠ i`, `(invFun (toFun f)).app v = (toFun f).map v hv ∘ equivAt_ne`, and
      -- `(toFun f).map v hv = f.app v ∘ equivAt_ne⁻¹`, so the equivalences cancel.
      refine LinearMap.ext fun x => ?_
      change (@QuiverLinearHom.app k Q _ (reverseAtVertex Q i)
          (quotientTransformedRepresentation Q i hi V) W
          (@QuiverLinearHom.mk k Q _ (reverseAtVertex Q i)
            (quotientTransformedRepresentation Q i hi V) W _ _) v) x = _
      simp only [dif_neg hv]
      change (((@QuiverLinearHom.app k Q _ (reverseAtVertex Q i)
          (quotientTransformedRepresentation Q i hi V) W f v).comp
          (transformedVertexEquivOfNe hi V v hv).symm.toLinearMap).comp
          (transformedVertexEquivOfNe hi V v hv).toLinearMap) x = _
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  · -- right_inv: `toFun (invFun r) = r`
    intro r
    ext v hv x
    change ((@QuiverLinearHom.app k Q _ (reverseAtVertex Q i)
        (quotientTransformedRepresentation Q i hi V) W
        (@QuiverLinearHom.mk k Q _ (reverseAtVertex Q i)
          (quotientTransformedRepresentation Q i hi V) W _ _) v).comp
        (transformedVertexEquivOfNe hi V v hv).symm.toLinearMap) x = r.map v hv x
    simp only [dif_neg hv]
    change (((r.map v hv).comp (transformedVertexEquivOfNe hi V v hv).toLinearMap).comp
        (transformedVertexEquivOfNe hi V v hv).symm.toLinearMap) x = r.map v hv x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

/-- States that the displayed reflected morphism space is equivalent to the reflection-morphism
type. -/
theorem reflectionHomEquiv_nonempty
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : vertexCondition Q i) [Fintype (OutgoingArrow Q i)]
    (V : QuiverLinearDiagram k Q)
    (W : @QuiverLinearDiagram k Q _ (reverseAtVertex Q i)) :
    Nonempty
      ((@QuiverLinearHom k Q _ (reverseAtVertex Q i)
          (quotientTransformedRepresentation Q i hi V) W)
        ≃ ReflectionHom hi V W) :=
  ⟨reflectionHomEquiv hi V W⟩

set_option maxHeartbeats 1600000 in
/-- Reflecting an arrow whose endpoints avoid the distinguished vertex twice recovers the
original arrow. -/
theorem reflectArrow_involutive
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} {a b : Q} (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (reverseAtVertex Q i) a b) :
    @auxiliaryPreserveHom Q inst_dec (reverseAtVertex Q i) i a b ha hb
        ((auxiliaryQuiver_eq Q i).symm ▸
          (@auxiliaryPreserveHom Q inst_dec inst i a b ha hb e)) = e := by
  apply eq_of_heq
  have h1 : ∀ (z : @Quiver.Hom Q
      (@reverseAtVertex Q _ (@reverseAtVertex Q _ inst i) i) a b),
      HEq (@auxiliaryPreserveHom Q inst_dec
        (@reverseAtVertex Q _ inst i) i a b ha hb z) z := by
    intro z
    rw [@auxiliaryMapAway_eq_cast Q inst_dec
      (@reverseAtVertex Q _ inst i) i a b ha hb z]
    exact cast_heq _ _
  have h2 : HEq ((auxiliaryQuiver_eq Q i).symm ▸
      (@auxiliaryPreserveHom Q inst_dec inst i a b ha hb e))
      (@auxiliaryPreserveHom Q inst_dec inst i a b ha hb e) :=
    eqRec_heq_self (motive := fun q _ => q.Hom a b) _
      (auxiliaryQuiver_eq Q i).symm
  have h3 : HEq (@auxiliaryPreserveHom Q inst_dec inst i a b ha hb e) e := by
    rw [auxiliaryMapAway_eq_cast]; exact cast_heq _ _
  exact (h1 _).trans (h2.trans h3)

/-- The extracted incoming arrow is the reflected reversal of the outgoing arrow stored in its
index. -/
theorem arrowTo_eq
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q] {i : Q} (hi : vertexCondition Q i)
    (a : OutgoingArrow Q i) :
    arrowTo hi a =
      @auxiliaryReverseHom Q inst_dec (reverseAtVertex Q i) i a.fst
        (outgoingIndex_ne hi a)
        ((auxiliaryQuiver_eq Q i).symm ▸ a.snd) := by
  apply eq_of_heq
  have hL : HEq (arrowTo hi a) a.snd := by
    unfold arrowTo; exact cast_heq _ _
  have hR : HEq
      (@auxiliaryReverseHom Q inst_dec (reverseAtVertex Q i) i a.fst
        (outgoingIndex_ne hi a)
        ((auxiliaryQuiver_eq Q i).symm ▸ a.snd)) a.snd := by
    rw [@auxiliaryMapFrom_eq_cast Q inst_dec (reverseAtVertex Q i) i a.fst
      (outgoingIndex_ne hi a)]
    refine HEq.trans (cast_heq _ _) ?_
    exact eqRec_heq_self (motive := fun q _ => q.Hom i a.fst) a.snd
      (auxiliaryQuiver_eq Q i).symm
  exact hL.trans hR.symm

/-- The source vertex recorded by an incoming-arrow index differs from the distinguished vertex. -/
theorem incomingIndex_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q] {i : Q} (hi : vertexCondition Q i)
    (b : @auxiliaryTypeAt Q (reverseAtVertex Q i) i) : b.fst ≠ i := by
  obtain ⟨j, e⟩ := b
  intro hj
  have e' : @Quiver.Hom Q (reverseAtVertex Q i) i i := hj ▸ e
  exact (hi i).false (cast (reversedAtHom_eq_of_eq_eq (i := i) rfl rfl) e')

/-- An equivalence from outgoing-arrow indices to incoming-arrow indices at the distinguished
vertex. -/
noncomputable def outgoingIncomingIndexEquiv
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : vertexCondition Q i) :
    OutgoingArrow Q i ≃ @auxiliaryTypeAt Q (reverseAtVertex Q i) i where
  toFun a := ⟨a.fst, arrowTo hi a⟩
  invFun b := ⟨b.fst, reverseArrowAtVertex (incomingIndex_ne hi b) b.snd⟩
  left_inv a := by
    refine Sigma.ext rfl ?_
    have h1 : HEq (reverseArrowAtVertex
        (incomingIndex_ne hi ⟨a.fst, arrowTo hi a⟩)
        (arrowTo hi a)) (arrowTo hi a) := by
      rw [reverseArrowAtVertex_eq_cast]; exact cast_heq _ _
    have h2 : HEq (arrowTo hi a) a.snd := by
      unfold arrowTo; exact cast_heq _ _
    exact h1.trans h2
  right_inv b := by
    refine Sigma.ext rfl ?_
    have h1 : HEq (arrowTo hi
        ⟨b.fst, reverseArrowAtVertex (incomingIndex_ne hi b) b.snd⟩)
        (reverseArrowAtVertex (incomingIndex_ne hi b) b.snd) := by
      unfold arrowTo; exact cast_heq _ _
    have h2 : HEq (reverseArrowAtVertex
        (incomingIndex_ne hi b) b.snd) b.snd := by
      rw [reverseArrowAtVertex_eq_cast]; exact cast_heq _ _
    exact h1.trans h2

/-- Applying the map from the direct sum equals the sum of its arrow-map components. -/
theorem mapFromDirectSum_eq_sum
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    (ρ : QuiverLinearDiagram k Q) (i : Q) [Fintype (auxiliaryTypeAt Q i)]
    (y : DirectSum (auxiliaryTypeAt Q i) (fun a => ρ.obj a.1)) :
    ρ.auxiliaryDirectSumMap i y =
      ∑ b : auxiliaryTypeAt Q i, ρ.map b.2
        (DirectSum.component k (auxiliaryTypeAt Q i) (fun a => ρ.obj a.1) b y) := by
  classical
  delta QuiverLinearDiagram.auxiliaryDirectSumMap
  change (DirectSum.toModule k (auxiliaryTypeAt Q i) (ρ.obj i)
    (fun a => ρ.map a.2)) y = _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero, Finset.sum_const_zero]
  | of j x =>
    erw [DirectSum.toModule_lof]
    rw [Finset.sum_eq_single j]
    · erw [DirectSum.component.lof_self]
    · intro b _ hb
      erw [DirectSum.component.of]; rw [dif_neg (Ne.symm hb), map_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  | add x y hx hy =>
    simp only [map_add, hx, hy, Finset.sum_add_distrib]

/-- Applying the map from the direct sum to one summand is its associated arrow map. -/
theorem mapFromDirectSum_lof
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    (ρ : QuiverLinearDiagram k Q) (i : Q)
    [Fintype (auxiliaryTypeAt Q i)] [DecidableEq (auxiliaryTypeAt Q i)]
    (b : auxiliaryTypeAt Q i) (v : ρ.obj b.1) :
    ρ.auxiliaryDirectSumMap i (DirectSum.lof k (auxiliaryTypeAt Q i) (fun a => ρ.obj a.1) b v) =
      ρ.map b.2 v := by
  rw [mapFromDirectSum_eq_sum ρ i
    (DirectSum.lof k (auxiliaryTypeAt Q i) (fun a => ρ.obj a.1) b v)]
  rw [Finset.sum_eq_single b]
  · rw [DirectSum.component.lof_self]
  · intro c _ hc
    rw [DirectSum.component.of, dif_neg (Ne.symm hc), map_zero]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- Constructs the dual orientation of the reflected morphism-space equivalence. -/
noncomputable def reflectionHomEquiv_dual
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : vertexCondition Q i) [Fintype (OutgoingArrow Q i)]
    (V : QuiverLinearDiagram k Q)
    (W : @QuiverLinearDiagram k Q _ (reverseAtVertex Q i)) :
    QuiverLinearHom k Q V
        (QuiverLinearDiagram.auxiliaryAt
          (@auxiliaryRepresentation k _ Q _ (reverseAtVertex Q i) i
            (auxiliaryBackward hi) W))
      ≃ ReflectionHom hi V W := by
  classical
  -- `i` is a sink of `Q̄ᵢ`; `Fplus` is the reflection of `W`, transported back to `Q` as `T`.
  set hi' := auxiliaryBackward hi with hi'_def
  set Fplus := @auxiliaryRepresentation k _ Q _ (reverseAtVertex Q i) i hi' W
    with Fplus_def
  set T := QuiverLinearDiagram.auxiliaryAt Fplus with T_def
  -- Vertex identifications: `T.obj v ≃ W.obj v` for `v ≠ i`, and
  -- `T.obj i ≃ ker(W.auxiliaryDirectSumMap i)`.
  let τ : ∀ v, v ≠ i → (T.obj v ≃ₗ[k]
      @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W v) :=
    fun v hv => (reflectAt_reindex Fplus v).trans
      (@auxiliaryRepresentationLinearEquivOfNe k _ Q _ (reverseAtVertex Q i) i hi' W v hv)
  let κ :=
    (reflectAt_reindex Fplus i).trans
      (@auxiliaryRepresentationLinearEquivAt k _ Q _ (reverseAtVertex Q i) i hi' W)
  -- Instances on the reindexed direct sum over `auxiliaryTypeAt (Q̄ᵢ) i`.
  haveI hFI : Fintype (@auxiliaryTypeAt Q (reverseAtVertex Q i) i) :=
    Fintype.ofEquiv _ (outgoingIncomingIndexEquiv hi)
  letI acmW : ∀ b : @auxiliaryTypeAt Q (reverseAtVertex Q i) i,
      AddCommMonoid (@QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W b.fst) :=
    fun b => @QuiverLinearDiagram.addCommMonoid k Q _ (reverseAtVertex Q i) W b.fst
  letI modW : ∀ b : @auxiliaryTypeAt Q (reverseAtVertex Q i) i,
      Module k (@QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W b.fst) :=
    fun b => @QuiverLinearDiagram.moduleInstance k Q _ (reverseAtVertex Q i) W b.fst
  -- The direct-sum-valued map assembled from the reduced family: the `reindex a`-component is
  -- `r.map a.fst _ ∘ V.map a.snd`.
  let sumMap : ReflectionHom hi V W → (V.obj i →ₗ[k]
      DirectSum (@auxiliaryTypeAt Q (reverseAtVertex Q i) i)
        (fun b => @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W b.1)) :=
    fun r => ∑ a : OutgoingArrow Q i,
      (DirectSum.lof k (@auxiliaryTypeAt Q (reverseAtVertex Q i) i)
        (fun b => @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W b.1)
        (outgoingIncomingIndexEquiv hi a)).comp
        ((r.map a.fst (outgoingIndex_ne hi a)).comp (V.map a.snd))
  -- `sumMap r x` lies in the kernel of `W.auxiliaryDirectSumMap i` (this is exactly
  -- constraint (C)).
  have hker : ∀ (r : ReflectionHom hi V W) (x : V.obj i),
      sumMap r x ∈ LinearMap.ker (@QuiverLinearDiagram.auxiliaryDirectSumMap k _ Q
        (reverseAtVertex Q i) W i) := by
    intro r x
    rw [LinearMap.mem_ker, LinearMap.sum_apply, map_sum]
    refine Eq.trans (Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => ?_))
      (r.sum_apply_eq_zero x)
    exact @mapFromDirectSum_lof k _ Q _ (reverseAtVertex Q i) W i _ _
      (outgoingIncomingIndexEquiv hi a)
      (r.map a.fst (outgoingIndex_ne hi a) (V.map a.snd x))
  -- The map at `i`: `V.obj i → T.obj i`, landing in
  -- `ker(W.auxiliaryDirectSumMap i)` then transported by `κ.symm`.
  let appAtI : ReflectionHom hi V W → (V.obj i →ₗ[k] T.obj i) :=
    fun r => κ.symm.toLinearMap ∘ₗ
      LinearMap.codRestrict (LinearMap.ker (@QuiverLinearDiagram.auxiliaryDirectSumMap k _ Q
        (reverseAtVertex Q i) W i)) (sumMap r) (hker r)
  -- `κ (appAtI r x)` is the kernel element with underlying direct-sum vector `sumMap r x`.
  have hκ_appAtI : ∀ (r : ReflectionHom hi V W) (x : V.obj i),
      κ (appAtI r x) = ⟨sumMap r x, hker r x⟩ := by
    intro r x
    change κ (κ.symm (LinearMap.codRestrict _ (sumMap r) (hker r) x)) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  -- Reading off the `reindex a₀`-component of `sumMap r x`.
  have hsumComp : ∀ (r : ReflectionHom hi V W) (x : V.obj i) (a₀ : OutgoingArrow Q i),
      DirectSum.component k (@auxiliaryTypeAt Q (reverseAtVertex Q i) i)
        (fun b => @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W b.1)
        (outgoingIncomingIndexEquiv hi a₀) (sumMap r x) =
        r.map a₀.fst (outgoingIndex_ne hi a₀) (V.map a₀.snd x) := by
    intro r x a₀
    have hexp : sumMap r x = ∑ a : OutgoingArrow Q i,
        DirectSum.lof k (@auxiliaryTypeAt Q (reverseAtVertex Q i) i)
          (fun b => @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W b.1)
          (outgoingIncomingIndexEquiv hi a)
          (r.map a.fst (outgoingIndex_ne hi a) (V.map a.snd x)) := by
      change (∑ a : OutgoingArrow Q i,
          (DirectSum.lof k (@auxiliaryTypeAt Q (reverseAtVertex Q i) i)
            (fun b => @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W b.1)
            (outgoingIncomingIndexEquiv hi a)).comp
            ((r.map a.fst (outgoingIndex_ne hi a)).comp (V.map a.snd))) x = _
      rw [LinearMap.sum_apply]
      rfl
    rw [hexp, map_sum, Finset.sum_eq_single a₀]
    · rw [DirectSum.component.lof_self]
    · intro b _ hb
      rw [DirectSum.component.of, dif_neg]
      exact fun hbeq => hb ((outgoingIncomingIndexEquiv hi).injective hbeq)
    · intro h; exact absurd (Finset.mem_univ a₀) h
  refine {
    toFun := fun g => {
      map := fun v hv => (τ v hv).toLinearMap ∘ₗ g.app v
      comm := ?compat
      sum_apply_eq_zero := ?constraint }
    invFun := ?invFun
    left_inv := ?li
    right_inv := ?ri }
  case compat =>
    intro a b ha hb e x
    -- `h v hv y = τ v hv (g.app v y)`; abbreviate the Q-arrow
    -- `e' := auxiliaryPreserveHom ha hb e`.
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    set e' := auxiliaryPreserveHom ha hb e with he'
    -- RHS: rewrite `g.app b ∘ V.map e'` by naturality of `g` on the Q-arrow `e'`.
    rw [g.naturality e' x]
    -- Unfold `τ b hb` through the `trans`, then push through the transport and `Fplus.map`.
    rw [show τ b hb (T.map e' (g.app a x)) =
        (@auxiliaryRepresentationLinearEquivOfNe k _ Q _ (reverseAtVertex Q i) i hi' W b hb)
          (reflectAt_reindex Fplus b
            (T.map e' (g.app a x)))
      from rfl]
    rw [reflectAt_reindex_naturality Fplus a b e' (g.app a x)]
    rw [@auxiliary_arrow_map_of_ne k _ Q _ (reverseAtVertex Q i) i hi' W
      a b ha hb ((auxiliaryQuiver_eq Q i).symm ▸ e')
      (reflectAt_reindex Fplus a (g.app a x))]
    -- Now both sides are `W.map ? (τ a ha (g.app a x))`; the arrows match by the twice lemma.
    rw [he', reflectArrow_involutive ha hb e]
    rfl
  case constraint =>
    intro x
    haveI : Fintype (@auxiliaryTypeAt Q (reverseAtVertex Q i) i) :=
      Fintype.ofEquiv _ (outgoingIncomingIndexEquiv hi)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    -- The kernel element `z` underlying `κ (g.app i x)`, and the target
    -- `auxiliaryDirectSumMap z = 0`.
    set z := (κ (g.app i x)).1 with hz
    letI acmW : ∀ b : @auxiliaryTypeAt Q (reverseAtVertex Q i) i,
        AddCommMonoid (@QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W b.fst) :=
      fun b => @QuiverLinearDiagram.addCommMonoid k Q _ (reverseAtVertex Q i) W b.fst
    letI modW : ∀ b : @auxiliaryTypeAt Q (reverseAtVertex Q i) i,
        Module k (@QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W b.fst) :=
      fun b => @QuiverLinearDiagram.moduleInstance k Q _ (reverseAtVertex Q i) W b.fst
    have hker := (κ (g.app i x)).property
    rw [LinearMap.mem_ker] at hker
    refine Eq.trans ?_ hker
    -- Expand `auxiliaryDirectSumMap z` as a sum over `auxiliaryTypeAt Q̄ᵢ i`, and
    -- reindex from `OutgoingArrow Q i`.
    rw [@mapFromDirectSum_eq_sum k _ Q _ (reverseAtVertex Q i) W i _ z]
    refine Finset.sum_equiv (outgoingIncomingIndexEquiv hi) (by simp) (fun a _ => ?_)
    -- Per-summand: `W (arrowTo a) (h_{a.fst} (V a.snd x)) = W b.snd (component b z)`
    -- for `b = reindex a`,
    -- via `g.naturality` at `i` and `auxiliary_arrow_map_from_selected`.
    have hb := outgoingIndex_ne hi a
    rw [g.naturality a.snd x]
    rw [show (τ a.fst hb) (T.map a.snd (g.app i x)) =
        (@auxiliaryRepresentationLinearEquivOfNe k _ Q _ (reverseAtVertex Q i) i hi' W
          a.fst hb)
          (reflectAt_reindex Fplus a.fst
            (T.map a.snd (g.app i x)))
      from rfl]
    rw [reflectAt_reindex_naturality Fplus i a.fst a.snd
      (g.app i x)]
    rw [@auxiliary_arrow_map_from_selected k _ Q _ (reverseAtVertex Q i) i hi' W
      a.fst hb ((auxiliaryQuiver_eq Q i).symm ▸ a.snd)
      (reflectAt_reindex Fplus i (g.app i x))]
    rw [← arrowTo_eq hi a]
    rfl
  case invFun =>
    intro r
    -- At `v ≠ i` the morphism is `(τ v _).symm ∘ r.map v _`; at `i` it is `appAtI r`.
    refine { app := fun v => if hv : v = i then hv ▸ appAtI r
        else (τ v hv).symm.toLinearMap ∘ₗ r.map v hv, naturality := ?_ }
    intro v w e x
    by_cases hw : w = i
    · -- `w = i`: no arrow enters the source `i`, so `e` is vacuous.
      exact ((hi v).false (hw ▸ e)).elim
    · by_cases hv : v = i
      · -- `v = i, w ≠ i`: the substantive source case.
        subst v
        rw [show (if hv : i = i then hv ▸ appAtI r
              else (τ i hv).symm.toLinearMap ∘ₗ r.map i hv) x = appAtI r x from by
            simp only [reduceDIte]]
        rw [show (if hv : w = i then hv ▸ appAtI r
              else (τ w hv).symm.toLinearMap ∘ₗ r.map w hv) (V.map e x)
              = (τ w hw).symm (r.map w hw (V.map e x)) from by
            simp only [dif_neg hw, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]]
        rw [LinearEquiv.symm_apply_eq]
        rw [show τ w hw (T.map e (appAtI r x)) =
            (@auxiliaryRepresentationLinearEquivOfNe k _ Q _ (reverseAtVertex Q i) i hi' W w hw)
              (reflectAt_reindex Fplus w
                (T.map e (appAtI r x)))
          from rfl]
        rw [reflectAt_reindex_naturality Fplus i w e (appAtI r x)]
        rw [@auxiliary_arrow_map_from_selected k _ Q _ (reverseAtVertex Q i) i hi' W
          w hw ((auxiliaryQuiver_eq Q i).symm ▸ e)
          (reflectAt_reindex Fplus i (appAtI r x))]
        rw [show (@auxiliaryRepresentationLinearEquivAt k _ Q _ (reverseAtVertex Q i) i hi' W)
            (reflectAt_reindex Fplus i (appAtI r x))
            = κ (appAtI r x) from rfl, hκ_appAtI r x]
        rw [show ((@QuiverLinearDiagram.auxiliaryDirectSumMap k _ Q
            (reverseAtVertex Q i) W i).ker.subtype
            ⟨sumMap r x, hker r x⟩ : _) = sumMap r x from rfl]
        -- Match the index second-component (keeping `fst = w` fixed so the motive is well-typed).
        have hsnd : arrowTo hi (⟨w, e⟩ : OutgoingArrow Q i) =
            @auxiliaryReverseHom Q _ (reverseAtVertex Q i) i w hw
              ((auxiliaryQuiver_eq Q i).symm ▸ e) :=
          arrowTo_eq hi ⟨w, e⟩
        rw [← hsnd]
        exact (hsumComp r x ⟨w, e⟩).symm
      · -- `v ≠ i, w ≠ i`: mirror `compat`, inverted through `(τ _ _).symm`.
        rw [show (if hv : w = i then hv ▸ appAtI r
              else (τ w hv).symm.toLinearMap ∘ₗ r.map w hv) (V.map e x)
              = (τ w hw).symm (r.map w hw (V.map e x)) from by
            simp only [dif_neg hw, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]]
        rw [show (if hv' : v = i then hv' ▸ appAtI r
              else (τ v hv').symm.toLinearMap ∘ₗ r.map v hv') x
              = (τ v hv).symm (r.map v hv x) from by
            simp only [dif_neg hv, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]]
        rw [LinearEquiv.symm_apply_eq]
        rw [show τ w hw (T.map e ((τ v hv).symm (r.map v hv x))) =
            (@auxiliaryRepresentationLinearEquivOfNe k _ Q _ (reverseAtVertex Q i) i hi' W w hw)
              (reflectAt_reindex Fplus w
                (T.map e ((τ v hv).symm (r.map v hv x))))
          from rfl]
        rw [reflectAt_reindex_naturality Fplus v w e
          ((τ v hv).symm (r.map v hv x))]
        rw [@auxiliary_arrow_map_of_ne k _ Q _ (reverseAtVertex Q i) i hi' W
          v w hv hw ((auxiliaryQuiver_eq Q i).symm ▸ e)
          (reflectAt_reindex Fplus v ((τ v hv).symm (r.map v hv x)))]
        rw [show (@auxiliaryRepresentationLinearEquivOfNe k _ Q _
            (reverseAtVertex Q i) i hi' W v hv)
            (reflectAt_reindex Fplus v ((τ v hv).symm (r.map v hv x)))
            = τ v hv ((τ v hv).symm (r.map v hv x)) from rfl]
        rw [LinearEquiv.apply_symm_apply]
        rw [r.comm hv hw (@auxiliaryPreserveHom Q _ (reverseAtVertex Q i) i v w hv hw
          ((auxiliaryQuiver_eq Q i).symm ▸ e)) x]
        rw [auxiliaryMapAway_involutive hv hw e]
  case li =>
    -- `invFun (toFun g) = g`.
    intro g
    refine @QuiverLinearHom.ext k Q _ _ V T _ _ (fun v => ?_)
    by_cases hv : v = i
    · subst v
      refine LinearMap.ext fun x => ?_
      simp only [reduceDIte]
      apply κ.injective
      rw [hκ_appAtI _ x]
      apply Subtype.ext
      -- Per-arrow: the `reindex a`-component of `(κ (g.app i x)).1` is
      -- `τ a.fst (g.app a.fst …)`.
      have hval : ∀ a : OutgoingArrow Q i,
          (τ a.fst (outgoingIndex_ne hi a))
              (g.app a.fst (V.map a.snd x)) =
            DirectSum.component k (@auxiliaryTypeAt Q (reverseAtVertex Q i) i)
              (fun b => @QuiverLinearDiagram.obj k Q _ (reverseAtVertex Q i) W b.1)
              (outgoingIncomingIndexEquiv hi a) (κ (g.app i x)).1 := by
        intro a
        have hb := outgoingIndex_ne hi a
        rw [g.naturality a.snd x]
        rw [show (τ a.fst hb) (T.map a.snd (g.app i x)) =
            (@auxiliaryRepresentationLinearEquivOfNe k _ Q _ (reverseAtVertex Q i) i hi' W a.fst hb)
              (reflectAt_reindex Fplus a.fst
                (T.map a.snd (g.app i x)))
          from rfl]
        rw [reflectAt_reindex_naturality Fplus i a.fst a.snd
          (g.app i x)]
        rw [@auxiliary_arrow_map_from_selected k _ Q _ (reverseAtVertex Q i) i hi' W
          a.fst hb ((auxiliaryQuiver_eq Q i).symm ▸ a.snd)
          (reflectAt_reindex Fplus i (g.app i x))]
        rw [show (@auxiliaryRepresentationLinearEquivAt k _ Q _ (reverseAtVertex Q i) i hi' W)
            (reflectAt_reindex Fplus i (g.app i x))
            = κ (g.app i x) from rfl]
        rw [show ((@QuiverLinearDiagram.auxiliaryDirectSumMap k _ Q
            (reverseAtVertex Q i) W i).ker.subtype
            (κ (g.app i x)) : _) = (κ (g.app i x)).1 from rfl]
        rw [← arrowTo_eq hi a]
        rfl
      refine DirectSum.ext_component k (fun b => ?_)
      obtain ⟨a, rfl⟩ := (outgoingIncomingIndexEquiv hi).surjective b
      rw [hsumComp _ x a]
      exact hval a
    · refine LinearMap.ext fun x => ?_
      simp only [dif_neg hv, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.symm_apply_apply]
  case ri =>
    -- `toFun (invFun r) = r`.
    intro r
    ext v hv x
    simp only [dif_neg hv, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply]

/-- States the dual orientation of the reflected morphism-space equivalence. -/
theorem reflectionHomEquiv_dual_nonempty
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : vertexCondition Q i) [Fintype (OutgoingArrow Q i)]
    (V : QuiverLinearDiagram k Q)
    (W : @QuiverLinearDiagram k Q _ (reverseAtVertex Q i)) :
    Nonempty
      (QuiverLinearHom k Q V
          (QuiverLinearDiagram.auxiliaryAt
            (@auxiliaryRepresentation k _ Q _ (reverseAtVertex Q i) i
              (auxiliaryBackward hi) W))
        ≃ ReflectionHom hi V W) :=
  ⟨reflectionHomEquiv_dual hi V W⟩

/-- The hom spaces obtained by reflecting the source and the target admit an equivalence. -/
theorem reflectionHomEquiv_source_target_nonempty
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q]
    [Quiver Q] (i : Q) (hi : vertexCondition Q i) [Fintype (OutgoingArrow Q i)]
    (V : QuiverLinearDiagram k Q)
    (W : @QuiverLinearDiagram k Q _ (reverseAtVertex Q i)) :
    Nonempty
      ((@QuiverLinearHom k Q _ (reverseAtVertex Q i)
          (quotientTransformedRepresentation Q i hi V) W)
        ≃
        QuiverLinearHom k Q V
          (QuiverLinearDiagram.auxiliaryAt
            (@auxiliaryRepresentation k _ Q _ (reverseAtVertex Q i) i
              (auxiliaryBackward hi) W))) := by
  obtain ⟨eL⟩ := reflectionHomEquiv_nonempty hi V W
  obtain ⟨eR⟩ := reflectionHomEquiv_dual_nonempty hi V W
  exact ⟨eL.trans eR.symm⟩

end RepresentationTheory.Quiver.Representation.Reflection
