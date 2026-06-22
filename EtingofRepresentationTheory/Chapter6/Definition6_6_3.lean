import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_2
import Mathlib.Algebra.DirectSum.Module

/-!
# Definition 6.6.3: Reflection Functor F⁺ᵢ (at a Sink)

Let Q be a quiver and i ∈ Q be a sink. The reflection functor
F⁺ᵢ : Rep Q → Rep Q̄ᵢ is defined by:
- F⁺ᵢ(V)_k = V_k for k ≠ i
- F⁺ᵢ(V)_i = ker(φ : ⊕_{j→i} V_j → V_i)

All maps stay the same except those now pointing out of i; these are replaced by
compositions of the inclusion of ker φ into ⊕_{j→i} V_j with the projections
⊕_{j→i} V_j → V_j.

## Mathlib correspondence

Bernstein-Gelfand-Ponomarev (BGP) reflection functors are not in Mathlib.
Needs custom definition using `LinearMap.ker`, `DirectSum`, and composition of
linear maps. The functor goes from representations of Q to representations of Q̄ᵢ.
-/

/-- The type indexing the direct sum for F⁺ᵢ: pairs (j, h) where h : j ⟶ i is an arrow
into the sink vertex i. -/
def Etingof.ArrowsInto (V : Type*) [Quiver V] (i : V) :=
  Σ (j : V), (j ⟶ i)

/-- The canonical map φ : ⊕_{j→i} V_j → V_i at a sink vertex i. -/
noncomputable def Etingof.QuiverRepresentation.sinkMap
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q) :
    DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1) →ₗ[k] ρ.obj i := by
  classical
  exact DirectSum.toModule k (Etingof.ArrowsInto Q i) (ρ.obj i) (fun a => ρ.mapLinear a.2)

/-- Heterogeneous congruence for (non-dependent) function application, given the domain
and codomain type equalities explicitly: equal (heterogeneously) functions applied to equal
(heterogeneously) arguments give equal (heterogeneously) results. -/
theorem Etingof.heq_apply
    {α α' : Sort u} {β β' : Sort v} (hα : α = α') (hβ : β = β')
    {f : α → β} {g : α' → β'} (hf : HEq f g)
    {a : α} {a' : α'} (ha : HEq a a') : HEq (f a) (g a') := by
  subst hα
  subst hβ
  cases ha
  cases hf
  rfl

/-- Heterogeneous congruence between a `LinearMap` and its coercion to a bare function,
given equalities of the domain/codomain types and heterogeneous equalities of their
`AddCommMonoid`/`Module` instances. This bridges `HEq` of two `LinearMap` *objects*
(living in different module structures) to `HEq` of their `⇑`-coerced functions, which is
what `heq_apply` consumes. -/
theorem Etingof.heq_linearMap_coe
    {k : Type*} [CommSemiring k]
    {α α' : Type u} {β β' : Type v}
    {acα : AddCommMonoid α} {acβ : AddCommMonoid β}
    {acα' : AddCommMonoid α'} {acβ' : AddCommMonoid β'}
    {mα : @Module k α _ acα} {mβ : @Module k β _ acβ}
    {mα' : @Module k α' _ acα'} {mβ' : @Module k β' _ acβ'}
    (hα : α = α') (hβ : β = β')
    (hacα : HEq acα acα') (hacβ : HEq acβ acβ')
    (hmα : HEq mα mα') (hmβ : HEq mβ mβ')
    {f : @LinearMap k k _ _ (RingHom.id k) α β acα acβ mα mβ}
    {g : @LinearMap k k _ _ (RingHom.id k) α' β' acα' acβ' mα' mβ'}
    (hf : HEq f g) :
    HEq (⇑f) (⇑g) := by
  subst hα
  subst hβ
  cases hacα
  cases hacβ
  cases hmα
  cases hmβ
  cases hf
  rfl

/-- The vertex-space type family of `reflectionFunctorPlus`, with the `Decidable`
discriminant exposed as an explicit argument `d`. At `d = .isFalse _` this is `ρ.obj v`;
at `d = .isTrue _` it is `ker(sinkMap i)`. -/
def Etingof.reflFunctorPlus_objAt
    {k : Type*} [CommSemiring k] {V : Type*} [Quiver V]
    (ρ : Etingof.QuiverRepresentation k V) (i v : V) (d : Decidable (v = i)) : Type _ :=
  @Decidable.casesOn _ (fun _ => Type _) d (fun _ => ρ.obj v) (fun _ => ↥(ρ.sinkMap i).ker)

/-- `AddCommMonoid` on `reflFunctorPlus_objAt`, with the discriminant `d` explicit. -/
noncomputable def Etingof.reflFunctorPlus_acmAt
    {k : Type*} [CommSemiring k] {V : Type*} [Quiver V]
    (ρ : Etingof.QuiverRepresentation k V) (i v : V) (d : Decidable (v = i)) :
    AddCommMonoid (Etingof.reflFunctorPlus_objAt ρ i v d) :=
  @Decidable.casesOn _ (fun d => AddCommMonoid (Etingof.reflFunctorPlus_objAt ρ i v d)) d
    (fun _ => ρ.instAddCommMonoid v) (fun _ => Submodule.addCommMonoid (ρ.sinkMap i).ker)

/-- `Module` on `reflFunctorPlus_objAt`, with the discriminant `d` explicit. -/
noncomputable def Etingof.reflFunctorPlus_modAt
    {k : Type*} [CommSemiring k] {V : Type*} [Quiver V]
    (ρ : Etingof.QuiverRepresentation k V) (i v : V) (d : Decidable (v = i)) :
    @Module k (Etingof.reflFunctorPlus_objAt ρ i v d) _ (Etingof.reflFunctorPlus_acmAt ρ i v d) :=
  @Decidable.casesOn _
    (fun d => @Module k (Etingof.reflFunctorPlus_objAt ρ i v d) _ (Etingof.reflFunctorPlus_acmAt ρ i v d)) d
    (fun _ => ρ.instModule v) (fun _ => Submodule.module (ρ.sinkMap i).ker)

/-- The arrow type of the reversed quiver, with both discriminants explicit. Definitionally
equal to `ReversedAtVertexHom V i a b` (at `da = inst a i`, `db = inst b i`). -/
def Etingof.reflFunctorPlus_arrowAt
    {V : Type*} [Quiver V] (i a b : V)
    (da : Decidable (a = i)) (db : Decidable (b = i)) : Type _ :=
  @Decidable.casesOn _ (fun _ => Type _) da
    (fun _ => @Decidable.casesOn _ (fun _ => Type _) db
      (fun _ => (a ⟶ b)) (fun _ => (i ⟶ a)))
    (fun _ => @Decidable.casesOn _ (fun _ => Type _) db
      (fun _ => (b ⟶ i)) (fun _ => (a ⟶ b)))

/-- The `mapLinear` field of `reflectionFunctorPlus`, with both discriminants explicit.
Built by the same nested `@Decidable.casesOn` (with explicit motives) as the inline
definition, so it is definitionally equal to it at `da = inst a i`, `db = inst b i`. -/
noncomputable def Etingof.reflFunctorPlus_mapAt
    {k : Type*} [CommSemiring k] {V : Type*} [Quiver V]
    (ρ : Etingof.QuiverRepresentation k V) {i : V} (hi : Etingof.IsSink V i) (a b : V)
    (da : Decidable (a = i)) (db : Decidable (b = i)) :
    letI := Etingof.reflFunctorPlus_acmAt ρ i a da
    letI := Etingof.reflFunctorPlus_acmAt ρ i b db
    letI := Etingof.reflFunctorPlus_modAt ρ i a da
    letI := Etingof.reflFunctorPlus_modAt ρ i b db
    Etingof.reflFunctorPlus_arrowAt i a b da db →
      (Etingof.reflFunctorPlus_objAt ρ i a da →ₗ[k] Etingof.reflFunctorPlus_objAt ρ i b db) :=
  @Decidable.casesOn (a = i)
    (fun da =>
      letI := Etingof.reflFunctorPlus_acmAt ρ i a da
      letI := Etingof.reflFunctorPlus_acmAt ρ i b db
      letI := Etingof.reflFunctorPlus_modAt ρ i a da
      letI := Etingof.reflFunctorPlus_modAt ρ i b db
      Etingof.reflFunctorPlus_arrowAt i a b da db →
        (Etingof.reflFunctorPlus_objAt ρ i a da →ₗ[k] Etingof.reflFunctorPlus_objAt ρ i b db))
    da
    (fun ha_ne => @Decidable.casesOn (b = i)
      (fun db =>
        letI := Etingof.reflFunctorPlus_acmAt ρ i b db
        letI := Etingof.reflFunctorPlus_modAt ρ i b db
        Etingof.reflFunctorPlus_arrowAt i a b (.isFalse ha_ne) db →
          (ρ.obj a →ₗ[k] Etingof.reflFunctorPlus_objAt ρ i b db))
      db
      (fun _hb_ne => fun e => ρ.mapLinear e)
      (fun _hb_eq => fun e => ((hi a).false e).elim))
    (fun ha_eq => @Decidable.casesOn (b = i)
      (fun db =>
        letI := Etingof.reflFunctorPlus_acmAt ρ i a (.isTrue ha_eq)
        letI := Etingof.reflFunctorPlus_acmAt ρ i b db
        letI := Etingof.reflFunctorPlus_modAt ρ i a (.isTrue ha_eq)
        letI := Etingof.reflFunctorPlus_modAt ρ i b db
        Etingof.reflFunctorPlus_arrowAt i a b (.isTrue ha_eq) db →
          (Etingof.reflFunctorPlus_objAt ρ i a (.isTrue ha_eq) →ₗ[k]
            Etingof.reflFunctorPlus_objAt ρ i b db))
      db
      (fun _hb_ne => fun e =>
        letI := Etingof.reflFunctorPlus_acmAt ρ i a (.isTrue ha_eq)
        letI := Etingof.reflFunctorPlus_modAt ρ i a (.isTrue ha_eq)
        (DirectSum.component k (Etingof.ArrowsInto V i)
          (fun x => ρ.obj x.1) ⟨b, e⟩).comp (LinearMap.ker (ρ.sinkMap i)).subtype)
      (fun hb_eq => fun e =>
        ((hi b).false (ha_eq ▸ e)).elim))

/-- The reflection functor F⁺ᵢ at a sink vertex i, sending representations of Q
to representations of Q̄ᵢ (the quiver with arrows at i reversed).

At vertex k ≠ i, F⁺ᵢ(ρ)_k = ρ_k (unchanged).
At vertex i, F⁺ᵢ(ρ)_i = ker(φ) where φ : ⊕_{j→i} ρ_j → ρ_i is the sum of
the representation maps ρ(h) for each arrow h : j → i.

The linear maps in the reversed quiver Q̄ᵢ are:
- For arrows not touching i: unchanged from ρ
- For arrows out of i in Q̄ᵢ (= reversed arrows into i in Q):
  ker(φ) ↪ ⊕_{j→i} ρ_j → ρ_j (inclusion then projection)

The vertex spaces, instances, and arrow maps are built from the
`reflFunctorPlus_objAt`/`acmAt`/`modAt`/`mapAt` helpers, which expose the shared
`Decidable` discriminant as an explicit argument (preserving instance coherence).

(Etingof Definition 6.6.3) -/
noncomputable def Etingof.reflectionFunctorPlus
    {k : Type*} [CommSemiring k]
    (V : Type*) [inst : DecidableEq V] [Quiver V]
    (i : V) (hi : Etingof.IsSink V i)
    (ρ : Etingof.QuiverRepresentation k V) :
    @Etingof.QuiverRepresentation k V _ (Etingof.reversedAtVertex V i) :=
  @Etingof.QuiverRepresentation.mk k V _ (Etingof.reversedAtVertex V i)
    (fun v => Etingof.reflFunctorPlus_objAt ρ i v (inst v i))
    (fun v => Etingof.reflFunctorPlus_acmAt ρ i v (inst v i))
    (fun v => Etingof.reflFunctorPlus_modAt ρ i v (inst v i))
    (fun {a b} (e : Etingof.ReversedAtVertexHom V i a b) =>
      Etingof.reflFunctorPlus_mapAt ρ hi a b (inst a i) (inst b i) e)

section ReflectionFunctorPlusAPI

/-! ## API for `reflectionFunctorPlus`

The reflection functor `F⁺ᵢ` is defined using `Decidable.casesOn`, making the types
at each vertex opaque. These API lemmas provide `LinearEquiv`s that reduce the
`Decidable.casesOn` once, so downstream proofs can compose them without
re-doing the case analysis. -/

/-- At a vertex v ≠ i, the type `F⁺ᵢ(ρ).obj v` is propositionally equal to `ρ.obj v`. -/
theorem Etingof.reflFunctorPlus_obj_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) v = ρ.obj v := by
  unfold Etingof.reflectionFunctorPlus Etingof.reflFunctorPlus_objAt
  simp only
  match hd : (‹DecidableEq Q› v i) with
  | .isTrue hvi => exact absurd hvi hv
  | .isFalse _ => rw [hd]

/-- At vertex i, the type `F⁺ᵢ(ρ).obj i` is propositionally equal to `ker(sinkMap i)`. -/
theorem Etingof.reflFunctorPlus_obj_eq
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) i = ↥(ρ.sinkMap i).ker := by
  unfold Etingof.reflectionFunctorPlus Etingof.reflFunctorPlus_objAt
  simp only
  match hd : (‹DecidableEq Q› i i) with
  | .isTrue _ => rw [hd]
  | .isFalse hii => exact absurd rfl hii

/-- The vertex equivalence at `v ≠ i`, with the `Decidable` discriminant exposed as an
explicit argument `d`. At `d = .isFalse _` this is the identity on `ρ.obj v`. -/
noncomputable def Etingof.reflFunctorPlus_equivAtAt_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation k Q) (v : Q) (hv : v ≠ i)
    (d : Decidable (v = i)) :
    letI := Etingof.reflFunctorPlus_acmAt ρ i v d
    letI := Etingof.reflFunctorPlus_modAt ρ i v d
    Etingof.reflFunctorPlus_objAt ρ i v d ≃ₗ[k] ρ.obj v :=
  @Decidable.casesOn (v = i)
    (fun d =>
      letI := Etingof.reflFunctorPlus_acmAt ρ i v d
      letI := Etingof.reflFunctorPlus_modAt ρ i v d
      Etingof.reflFunctorPlus_objAt ρ i v d ≃ₗ[k] ρ.obj v)
    d
    (fun _ => LinearEquiv.refl k (ρ.obj v))
    (fun hvi => absurd hvi hv)

/-- `LinearEquiv` at vertex v ≠ i: `F⁺ᵢ(ρ).obj v ≃ₗ[k] ρ.obj v`.
Defined via `reflFunctorPlus_equivAtAt_ne` at the live discriminant `inst v i`. -/
noncomputable def Etingof.reflFunctorPlus_equivAt_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) v ≃ₗ[k] ρ.obj v :=
  Etingof.reflFunctorPlus_equivAtAt_ne ρ v hv (inst v i)

/-- The vertex equivalence at `i`, with the `Decidable` discriminant exposed as an explicit
argument `d`. At `d = .isTrue _` this is the identity on `ker(sinkMap i)`. -/
noncomputable def Etingof.reflFunctorPlus_equivAtAt_eq
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation k Q) (d : Decidable (i = i)) :
    letI := Etingof.reflFunctorPlus_acmAt ρ i i d
    letI := Etingof.reflFunctorPlus_modAt ρ i i d
    Etingof.reflFunctorPlus_objAt ρ i i d ≃ₗ[k] ↥(ρ.sinkMap i).ker :=
  @Decidable.casesOn (i = i)
    (fun d =>
      letI := Etingof.reflFunctorPlus_acmAt ρ i i d
      letI := Etingof.reflFunctorPlus_modAt ρ i i d
      Etingof.reflFunctorPlus_objAt ρ i i d ≃ₗ[k] ↥(ρ.sinkMap i).ker)
    d
    (fun hii => absurd rfl hii)
    (fun _ => LinearEquiv.refl k ↥(ρ.sinkMap i).ker)

/-- `LinearEquiv` at vertex i: `F⁺ᵢ(ρ).obj i ≃ₗ[k] ker(sinkMap i)`.
This reduces the `Decidable.casesOn` in the `reflectionFunctorPlus` definition.
Defined via `reflFunctorPlus_equivAtAt_eq` at the live discriminant `inst i i`. -/
noncomputable def Etingof.reflFunctorPlus_equivAt_eq
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) i ≃ₗ[k] ↥(ρ.sinkMap i).ker :=
  Etingof.reflFunctorPlus_equivAtAt_eq ρ (inst i i)

/-- Convert a reversed-quiver arrow between non-sink vertices back to original.
For a ≠ i and b ≠ i, `ReversedAtVertexHom Q i a b = a ⟶ b`, so the arrow is unchanged. -/
def Etingof.reversedArrow_ne_ne
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i a b : Q}
    (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b) : a ⟶ b := by
  change @Etingof.ReversedAtVertexHom Q inst _ i a b at e
  unfold Etingof.ReversedAtVertexHom at e
  revert e
  exact match inst a i, inst b i with
  | .isTrue h, _ => absurd h ha
  | .isFalse _, .isTrue h => absurd h hb
  | .isFalse _, .isFalse _ => fun e => e

/-- `reversedArrow_ne_ne ha hb` is the `cast` along `ReversedAtVertexHom_ne_ne`. -/
theorem Etingof.reversedArrow_ne_ne_eq_cast
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i a b : Q}
    (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b) :
    Etingof.reversedArrow_ne_ne ha hb e =
      cast (Etingof.ReversedAtVertexHom_ne_ne ha hb) e := by
  have h_ai : inst a i = .isFalse ha := by
    cases inst a i with | isTrue h => exact absurd h ha | isFalse _ => rfl
  have h_bi : inst b i = .isFalse hb := by
    cases inst b i with | isTrue h => exact absurd h hb | isFalse _ => rfl
  revert e
  unfold Etingof.reversedArrow_ne_ne Etingof.ReversedAtVertexHom_ne_ne
    Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
  simp only []
  rw [h_ai, h_bi]
  intro e; rfl

set_option maxHeartbeats 1600000 in
-- reason: unfolding reflectionFunctorPlus + equivAt_ne + match reduction
/-- At non-sink vertices (a ≠ i, b ≠ i), the F⁺ᵢ map equals the original ρ map,
after transport through the equivAt_ne equivalences.

This is the key API lemma enabling proofs about F⁺ᵢ's behavior on arrows between
non-sink vertices without re-doing the Decidable.casesOn case analysis. -/
theorem Etingof.reflFunctorPlus_mapLinear_ne_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) {a b : Q}
    (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b)
    (w : @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) a) :
    (Etingof.reflFunctorPlus_equivAt_ne hi ρ b hb)
      (@Etingof.QuiverRepresentation.mapLinear k Q _
        (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) a b e w) =
    ρ.mapLinear (Etingof.reversedArrow_ne_ne ha hb e)
      ((Etingof.reflFunctorPlus_equivAt_ne hi ρ a ha) w) := by
  have h_da : inst a i = .isFalse ha := by
    cases inst a i with | isTrue h => exact absurd h ha | isFalse _ => rfl
  have h_db : inst b i = .isFalse hb := by
    cases inst b i with | isTrue h => exact absurd h hb | isFalse _ => rfl
  -- (1) Function-level HEq of `mapAt` at the live discriminants vs. at the literal `isFalse`
  -- branch. No element is applied, so `rw` on the discriminants is type-correct on v4.29.
  -- At `.isFalse, .isFalse` the map iota-reduces to `ρ.mapLinear`.
  have hmap : HEq
      (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) a b e)
      (ρ.mapLinear (Etingof.reversedArrow_ne_ne ha hb e)) := by
    have hf : HEq
        (Etingof.reflFunctorPlus_mapAt ρ hi a b (inst a i) (inst b i))
        (Etingof.reflFunctorPlus_mapAt ρ hi a b (.isFalse ha) (.isFalse hb)) := by
      rw [h_da, h_db]
    have he : HEq e (Etingof.reversedArrow_ne_ne ha hb e) := by
      rw [Etingof.reversedArrow_ne_ne_eq_cast ha hb]; exact (cast_heq _ _).symm
    refine Etingof.heq_apply (Etingof.ReversedAtVertexHom_ne_ne ha hb) ?_ hf he
    rw [h_da, h_db]
  -- (2) `equivAt_ne` is heterogeneously the identity (function level, via the parametrized
  -- `equivAtAt_ne` and `rw` on the discriminant — again no element applied).
  have heqv : ∀ (v : Q) (hv : v ≠ i),
      HEq (⇑(Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv)) (id : ρ.obj v → ρ.obj v) := by
    intro v hv
    have hdv : inst v i = .isFalse hv := by
      cases inst v i with | isTrue h => exact absurd h hv | isFalse _ => rfl
    show HEq (⇑(Etingof.reflFunctorPlus_equivAtAt_ne ρ v hv (inst v i))) _
    rw [hdv]
    rfl
  -- (3) Assemble via HEq congruence.
  have hwa : HEq ((Etingof.reflFunctorPlus_equivAt_ne hi ρ a ha) w) w :=
    (Etingof.heq_apply (Etingof.reflFunctorPlus_obj_ne hi ρ a ha) rfl (heqv a ha)
      (cast_heq (Etingof.reflFunctorPlus_obj_ne hi ρ a ha) w).symm).trans
      (cast_heq (Etingof.reflFunctorPlus_obj_ne hi ρ a ha) w)
  -- Instance HEqs needed to bridge `hmap` (HEq of LinearMap objects) to HEq of coercions.
  have hac_a : HEq
      (Etingof.reflFunctorPlus_acmAt ρ i a (inst a i)) (ρ.instAddCommMonoid a) := by
    rw [h_da]; rfl
  have hac_b : HEq
      (Etingof.reflFunctorPlus_acmAt ρ i b (inst b i)) (ρ.instAddCommMonoid b) := by
    rw [h_db]; rfl
  have hmo_a : HEq
      (Etingof.reflFunctorPlus_modAt ρ i a (inst a i)) (ρ.instModule a) := by
    rw [h_da]; rfl
  have hmo_b : HEq
      (Etingof.reflFunctorPlus_modAt ρ i b (inst b i)) (ρ.instModule b) := by
    rw [h_db]; rfl
  have hmapcoe : HEq
      (⇑(@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) a b e))
      (⇑(ρ.mapLinear (Etingof.reversedArrow_ne_ne ha hb e))) :=
    Etingof.heq_linearMap_coe
      (Etingof.reflFunctorPlus_obj_ne hi ρ a ha)
      (Etingof.reflFunctorPlus_obj_ne hi ρ b hb)
      hac_a hac_b hmo_a hmo_b hmap
  have hmapw : HEq
      (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) a b e w)
      (ρ.mapLinear (Etingof.reversedArrow_ne_ne ha hb e)
        ((Etingof.reflFunctorPlus_equivAt_ne hi ρ a ha) w)) :=
    Etingof.heq_apply (Etingof.reflFunctorPlus_obj_ne hi ρ a ha)
      (Etingof.reflFunctorPlus_obj_ne hi ρ b hb) hmapcoe hwa.symm
  have hfinal := Etingof.heq_apply (Etingof.reflFunctorPlus_obj_ne hi ρ b hb) rfl (heqv b hb)
    (cast_heq (Etingof.reflFunctorPlus_obj_ne hi ρ b hb)
      (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) a b e w)).symm
  -- `hfinal : HEq (equivAt_ne b hb (mapLinear e w)) (cast (obj_ne b hb) (mapLinear e w))`
  exact eq_of_heq (hfinal.trans ((cast_heq (Etingof.reflFunctorPlus_obj_ne hi ρ b hb)
    (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) a b e w)).trans hmapw))

/-- Convert a reversed-quiver arrow from i to b ≠ i back to the original b ⟶ i.
For a = i and b ≠ i, `ReversedAtVertexHom Q i i b = b ⟶ i`. -/
def Etingof.reversedArrow_eq_ne
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i b : Q}
    (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) i b) : b ⟶ i := by
  change @Etingof.ReversedAtVertexHom Q inst _ i i b at e
  unfold Etingof.ReversedAtVertexHom at e
  revert e
  exact match inst i i, inst b i with
  | .isFalse h, _ => absurd rfl h
  | .isTrue _, .isTrue h => absurd h hb
  | .isTrue _, .isFalse _ => fun e => e

/-- `reversedArrow_eq_ne hb` is the `cast` along `ReversedAtVertexHom_eq_ne`. -/
theorem Etingof.reversedArrow_eq_ne_eq_cast
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i b : Q}
    (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) i b) :
    Etingof.reversedArrow_eq_ne hb e =
      cast (Etingof.ReversedAtVertexHom_eq_ne rfl hb) e := by
  have h_ii : inst i i = .isTrue rfl := by
    cases inst i i with | isTrue _ => rfl | isFalse h => exact absurd rfl h
  have h_bi : inst b i = .isFalse hb := by
    cases inst b i with | isTrue h => exact absurd h hb | isFalse _ => rfl
  revert e
  unfold Etingof.reversedArrow_eq_ne Etingof.ReversedAtVertexHom_eq_ne
    Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
  simp only []
  rw [h_ii, h_bi]
  intro e; rfl

set_option maxHeartbeats 1600000 in
-- reason: unfolding reflectionFunctorPlus + equivAt_eq/ne + match reduction
/-- At the sink vertex going to a non-sink vertex (a = i, b ≠ i), the F⁺ᵢ map
sends an element of ker(sinkMap) to the b-component of its inclusion in ⊕V_j.

After transport through equivAt_eq and equivAt_ne, this says:
  equivAt_ne (mapLinear e w) = component ⟨b, reversedArrow_eq_ne e⟩ (subtype (equivAt_eq w))

This is the key API lemma for the case a = i, b ≠ i. -/
theorem Etingof.reflFunctorPlus_mapLinear_eq_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) {b : Q}
    (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) i b)
    (w : @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) i) :
    (Etingof.reflFunctorPlus_equivAt_ne hi ρ b hb)
      (@Etingof.QuiverRepresentation.mapLinear k Q _
        (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) i b e w) =
    (DirectSum.component k (Etingof.ArrowsInto Q i) (fun x => ρ.obj x.1)
      ⟨b, Etingof.reversedArrow_eq_ne hb e⟩)
      ((ρ.sinkMap i).ker.subtype
        ((Etingof.reflFunctorPlus_equivAt_eq hi ρ) w)) := by
  have h_da : inst i i = .isTrue rfl := by
    cases inst i i with
    | isTrue _ => rfl
    | isFalse h => exact absurd rfl h
  have h_db : inst b i = .isFalse hb := by
    cases inst b i with
    | isTrue h => exact absurd h hb
    | isFalse _ => rfl
  -- The target linear map of the F⁺ map at (a = i, b ≠ i): inclusion of `ker` then
  -- projection onto the `b`-component of the direct sum.
  set RHSmap :=
    (DirectSum.component k (Etingof.ArrowsInto Q i) (fun x => ρ.obj x.1)
      ⟨b, Etingof.reversedArrow_eq_ne hb e⟩).comp (ρ.sinkMap i).ker.subtype with hRHS
  -- (1) Function-level HEq of `mapAt` at the live discriminants vs. at the literal
  -- `(isTrue, isFalse)` branch, where the map iota-reduces to `RHSmap`.
  have hmap : HEq
      (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) i b e)
      RHSmap := by
    have hf : HEq
        (Etingof.reflFunctorPlus_mapAt ρ hi i b (inst i i) (inst b i))
        (Etingof.reflFunctorPlus_mapAt ρ hi i b (.isTrue rfl) (.isFalse hb)) := by
      rw [h_da, h_db]
    have he : HEq e (Etingof.reversedArrow_eq_ne hb e) := by
      rw [Etingof.reversedArrow_eq_ne_eq_cast hb]; exact (cast_heq _ _).symm
    refine Etingof.heq_apply (Etingof.ReversedAtVertexHom_eq_ne rfl hb) ?_ hf he
    rw [h_da, h_db]
  -- (2) `equivAt_eq` is heterogeneously the identity on `ker(sinkMap i)`.
  have heqve : HEq (⇑(Etingof.reflFunctorPlus_equivAt_eq hi ρ))
      (id : ↥(ρ.sinkMap i).ker → ↥(ρ.sinkMap i).ker) := by
    have h_ii : inst i i = .isTrue rfl := by
      cases inst i i with | isTrue _ => rfl | isFalse h => exact absurd rfl h
    show HEq (⇑(Etingof.reflFunctorPlus_equivAtAt_eq ρ (inst i i))) _
    rw [h_ii]
    rfl
  have hwe : HEq ((Etingof.reflFunctorPlus_equivAt_eq hi ρ) w) w :=
    (Etingof.heq_apply (Etingof.reflFunctorPlus_obj_eq hi ρ) rfl (heqve)
      (cast_heq (Etingof.reflFunctorPlus_obj_eq hi ρ) w).symm).trans
      (cast_heq (Etingof.reflFunctorPlus_obj_eq hi ρ) w)
  -- (3) Instance HEqs to bridge `hmap` to HEq of coercions.
  have hac_i : HEq
      (Etingof.reflFunctorPlus_acmAt ρ i i (inst i i))
      (Submodule.addCommMonoid (ρ.sinkMap i).ker) := by
    rw [h_da]; rfl
  have hac_b : HEq
      (Etingof.reflFunctorPlus_acmAt ρ i b (inst b i)) (ρ.instAddCommMonoid b) := by
    rw [h_db]; rfl
  have hmo_i : HEq
      (Etingof.reflFunctorPlus_modAt ρ i i (inst i i))
      (Submodule.module (ρ.sinkMap i).ker) := by
    rw [h_da]; rfl
  have hmo_b : HEq
      (Etingof.reflFunctorPlus_modAt ρ i b (inst b i)) (ρ.instModule b) := by
    rw [h_db]; rfl
  have hmapcoe : HEq
      (⇑(@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) i b e))
      (⇑RHSmap) :=
    Etingof.heq_linearMap_coe
      (Etingof.reflFunctorPlus_obj_eq hi ρ)
      (Etingof.reflFunctorPlus_obj_ne hi ρ b hb)
      hac_i hac_b hmo_i hmo_b hmap
  -- (4) Apply the coercion-HEq to the transported input.
  have hmapw : HEq
      (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) i b e w)
      (RHSmap ((Etingof.reflFunctorPlus_equivAt_eq hi ρ) w)) :=
    Etingof.heq_apply (Etingof.reflFunctorPlus_obj_eq hi ρ)
      (Etingof.reflFunctorPlus_obj_ne hi ρ b hb) hmapcoe hwe.symm
  -- (5) `equivAt_ne` is heterogeneously identity on `ρ.obj b`; combine.
  have heqv : ∀ (v : Q) (hv : v ≠ i),
      HEq (⇑(Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv)) (id : ρ.obj v → ρ.obj v) := by
    intro v hv
    have hdv : inst v i = .isFalse hv := by
      cases inst v i with | isTrue h => exact absurd h hv | isFalse _ => rfl
    show HEq (⇑(Etingof.reflFunctorPlus_equivAtAt_ne ρ v hv (inst v i))) _
    rw [hdv]
    rfl
  have hfinal := Etingof.heq_apply (Etingof.reflFunctorPlus_obj_ne hi ρ b hb) rfl (heqv b hb)
    (cast_heq (Etingof.reflFunctorPlus_obj_ne hi ρ b hb)
      (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) i b e w)).symm
  exact eq_of_heq (hfinal.trans ((cast_heq (Etingof.reflFunctorPlus_obj_ne hi ρ b hb)
    (@Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) i b e w)).trans hmapw))

end ReflectionFunctorPlusAPI
