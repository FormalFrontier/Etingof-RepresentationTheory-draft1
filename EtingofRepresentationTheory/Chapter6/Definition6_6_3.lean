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
@[reducible] def Etingof.ArrowsInto (V : Type*) [Quiver V] (i : V) :=
  Σ (j : V), (j ⟶ i)

/-- The canonical map φ : ⊕_{j→i} V_j → V_i at a sink vertex i. -/
noncomputable def Etingof.QuiverRepresentation.sinkMap
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q) :
    DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1) →ₗ[k] ρ.obj i := by
  classical
  exact DirectSum.toModule k (Etingof.ArrowsInto Q i) (ρ.obj i) (fun a => ρ.mapLinear a.2)

/-- The reflection functor F⁺ᵢ at a sink vertex i, sending representations of Q
to representations of Q̄ᵢ (the quiver with arrows at i reversed).

At vertex k ≠ i, F⁺ᵢ(ρ)_k = ρ_k (unchanged).
At vertex i, F⁺ᵢ(ρ)_i = ker(φ) where φ : ⊕_{j→i} ρ_j → ρ_i is the sum of
the representation maps ρ(h) for each arrow h : j → i.

The linear maps in the reversed quiver Q̄ᵢ are:
- For arrows not touching i: unchanged from ρ
- For arrows out of i in Q̄ᵢ (= reversed arrows into i in Q):
  ker(φ) ↪ ⊕_{j→i} ρ_j → ρ_j (inclusion then projection)

(Etingof Definition 6.6.3) -/
noncomputable def Etingof.reflectionFunctorPlus
    {k : Type*} [CommSemiring k]
    (V : Type*) [inst : DecidableEq V] [Quiver V]
    (i : V) (hi : Etingof.IsSink V i)
    (ρ : Etingof.QuiverRepresentation k V) :
    @Etingof.QuiverRepresentation k V _ (Etingof.reversedAtVertex V i) :=
  -- φ : ⊕_{j→i} ρ_j → ρ_i, the canonical sink map
  let φ := ρ.sinkMap i
  -- Use Decidable.casesOn with the [DecidableEq V] instance to construct
  -- obj, AddCommMonoid, and Module coherently. All three fields share the same
  -- Decidable instance, so the type-level case-split computes correctly.
  let dp : ∀ v, Decidable (v = i) := fun v => inst v i
  let objAt : ∀ v, Decidable (v = i) → Type _ :=
    fun v d => @Decidable.casesOn _ (fun _ => Type _) d (fun _ => ρ.obj v) (fun _ => ↥φ.ker)
  let acmAt : ∀ v d, AddCommMonoid (objAt v d) :=
    fun v d => @Decidable.casesOn _ (fun d => AddCommMonoid (objAt v d)) d
      (fun _ => ρ.instAddCommMonoid v) (fun _ => Submodule.addCommMonoid φ.ker)
  let modAt : ∀ v d, @Module k (objAt v d) _ (acmAt v d) :=
    fun v d => @Decidable.casesOn _ (fun d => @Module k (objAt v d) _ (acmAt v d)) d
      (fun _ => ρ.instModule v) (fun _ => Submodule.module φ.ker)
  @Etingof.QuiverRepresentation.mk k V _ (Etingof.reversedAtVertex V i)
    (fun v => objAt v (dp v))
    (fun v => acmAt v (dp v))
    (fun v => modAt v (dp v))
    (fun {a b} (e : Etingof.ReversedAtVertexHom V i a b) => by
      -- Goal: objAt a (inst a i) →ₗ[k] objAt b (inst b i)
      -- We use @Decidable.casesOn with EXPLICIT motives that parameterize
      -- both the arrow type (@ite ... da ...) and objAt by the same variable da.
      -- This ensures all ite/casesOn reduce together in each branch.
      change objAt a (inst a i) →ₗ[k] objAt b (inst b i)
      change @Etingof.ReversedAtVertexHom V inst _ i a b at e
      unfold Etingof.ReversedAtVertexHom at e
      revert e
      -- Use nested @Decidable.casesOn with explicit motives that parameterize
      -- BOTH the arrow type and objAt by the same variable (da/db).
      -- Using Decidable.casesOn (not ite) for the arrow type ensures
      -- the bound variable da appears in the compiled motive, enabling
      -- definitional reduction when the proof matches on inst a i.
      let arrowAt (da : Decidable (a = i)) (db : Decidable (b = i)) : Type _ :=
        @Decidable.casesOn _ (fun _ => Type _) da
          (fun _ => @Decidable.casesOn _ (fun _ => Type _) db
            (fun _ => (a ⟶ b)) (fun _ => (i ⟶ a)))
          (fun _ => @Decidable.casesOn _ (fun _ => Type _) db
            (fun _ => (b ⟶ i)) (fun _ => (a ⟶ b)))
      exact @Decidable.casesOn (a = i)
        (fun da => arrowAt da (inst b i) → objAt a da →ₗ[k] objAt b (inst b i))
        (inst a i)
        (fun ha_ne => @Decidable.casesOn (b = i)
          (fun db => arrowAt (.isFalse ha_ne) db → ρ.obj a →ₗ[k] objAt b db)
          (inst b i)
          (fun _hb_ne => fun e => ρ.mapLinear e)
          (fun _hb_eq => fun e => ((hi a).false e).elim))
        (fun ha_eq => @Decidable.casesOn (b = i)
          (fun db => arrowAt (.isTrue ha_eq) db → objAt a (.isTrue ha_eq) →ₗ[k] objAt b db)
          (inst b i)
          (fun _hb_ne => fun e =>
            (DirectSum.component k (Etingof.ArrowsInto V i)
              (fun x => ρ.obj x.1) ⟨b, e⟩).comp (LinearMap.ker φ).subtype)
          (fun hb_eq => fun e =>
            ((hi b).false (ha_eq ▸ e)).elim)))

section ReflectionFunctorPlusHelpers

/-! ## Field-family helpers for `reflectionFunctorPlus`

The fields of `reflectionFunctorPlus` are built from nested `Decidable.casesOn`
on the opaque instance `inst v i`. Because the discriminant is an opaque instance,
the structure projections do not reduce by `rfl` once a concrete `v` is fixed —
a `rw [Subsingleton.elim (inst v i) (.isFalse hv)]` has an ill-typed motive
(the instance is buried behind folded structure projections).

These helpers extract the field families to top-level defs whose `Decidable`
arguments are EXPLICIT parameters. The bodies are copied verbatim from the
field bodies, so the structure projections reduce to the helpers by `rfl`
(`reflFunctorPlus_obj_eq_objAt`, `reflFunctorPlus_mapLinear_eq_mapLinearAt`),
and the helpers themselves reduce by `rfl` once their explicit `Decidable`
argument is a literal `.isFalse`/`.isTrue` constructor
(`reflFunctorPlus_objAt_isFalse`, etc.). -/

/-- The object-type family of `reflectionFunctorPlus`, with the `Decidable`
instance as an explicit parameter. Copied from the local `objAt` let-binding. -/
def Etingof.reflFunctorPlus_objAt
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation k Q) (v : Q) (d : Decidable (v = i)) :
    Type _ :=
  @Decidable.casesOn _ (fun _ => Type _) d (fun _ => ρ.obj v) (fun _ => ↥(ρ.sinkMap i).ker)

/-- The `AddCommMonoid` field family of `reflectionFunctorPlus`, with the
`Decidable` instance explicit. Copied from the local `acmAt` let-binding. -/
noncomputable def Etingof.reflFunctorPlus_acmAt
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation k Q) (v : Q) (d : Decidable (v = i)) :
    AddCommMonoid (Etingof.reflFunctorPlus_objAt ρ v d) :=
  @Decidable.casesOn _ (fun d => AddCommMonoid (Etingof.reflFunctorPlus_objAt ρ v d)) d
    (fun _ => ρ.instAddCommMonoid v) (fun _ => Submodule.addCommMonoid (ρ.sinkMap i).ker)

/-- The `Module` field family of `reflectionFunctorPlus`, with the `Decidable`
instance explicit. Copied from the local `modAt` let-binding. -/
noncomputable def Etingof.reflFunctorPlus_modAt
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation k Q) (v : Q) (d : Decidable (v = i)) :
    @Module k (Etingof.reflFunctorPlus_objAt ρ v d) _ (Etingof.reflFunctorPlus_acmAt ρ v d) :=
  @Decidable.casesOn _
    (fun d => @Module k (Etingof.reflFunctorPlus_objAt ρ v d) _
      (Etingof.reflFunctorPlus_acmAt ρ v d)) d
    (fun _ => ρ.instModule v) (fun _ => Submodule.module (ρ.sinkMap i).ker)

/-- The arrow-type family of `reflectionFunctorPlus`, with the `Decidable`
instances explicit. Copied from the local `arrowAt` let-binding in the
`mapLinear` field. -/
def Etingof.reflFunctorPlus_arrowAt
    {Q : Type*} [Quiver Q] (i a b : Q)
    (da : Decidable (a = i)) (db : Decidable (b = i)) : Type _ :=
  @Decidable.casesOn _ (fun _ => Type _) da
    (fun _ => @Decidable.casesOn _ (fun _ => Type _) db
      (fun _ => (a ⟶ b)) (fun _ => (i ⟶ a)))
    (fun _ => @Decidable.casesOn _ (fun _ => Type _) db
      (fun _ => (b ⟶ i)) (fun _ => (a ⟶ b)))

/-- The `mapLinear` field family of `reflectionFunctorPlus`, with the `Decidable`
instances explicit. The body is copied verbatim from the `mapLinear` field of
`reflectionFunctorPlus` (the nested `Decidable.casesOn` term it elaborates to). -/
noncomputable def Etingof.reflFunctorPlus_mapLinearAt
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (a b : Q)
    (da : Decidable (a = i)) (db : Decidable (b = i))
    (e : Etingof.reflFunctorPlus_arrowAt i a b da db) :
    letI := (Etingof.reflFunctorPlus_acmAt ρ a da)
    letI := (Etingof.reflFunctorPlus_modAt ρ a da)
    letI := (Etingof.reflFunctorPlus_acmAt ρ b db)
    letI := (Etingof.reflFunctorPlus_modAt ρ b db)
    Etingof.reflFunctorPlus_objAt ρ a da →ₗ[k] Etingof.reflFunctorPlus_objAt ρ b db :=
  @Decidable.casesOn (a = i)
    (fun da => Etingof.reflFunctorPlus_arrowAt i a b da db →
      letI := (Etingof.reflFunctorPlus_acmAt ρ a da)
      letI := (Etingof.reflFunctorPlus_modAt ρ a da)
      letI := (Etingof.reflFunctorPlus_acmAt ρ b db)
      letI := (Etingof.reflFunctorPlus_modAt ρ b db)
      Etingof.reflFunctorPlus_objAt ρ a da →ₗ[k] Etingof.reflFunctorPlus_objAt ρ b db)
    da
    (fun ha_ne => @Decidable.casesOn (b = i)
      (fun db => Etingof.reflFunctorPlus_arrowAt i a b (.isFalse ha_ne) db →
        letI := (Etingof.reflFunctorPlus_acmAt ρ b db)
        letI := (Etingof.reflFunctorPlus_modAt ρ b db)
        ρ.obj a →ₗ[k] Etingof.reflFunctorPlus_objAt ρ b db)
      db
      (fun _hb_ne => fun e => ρ.mapLinear e)
      (fun _hb_eq => fun e => ((hi a).false e).elim))
    (fun ha_eq => @Decidable.casesOn (b = i)
      (fun db => Etingof.reflFunctorPlus_arrowAt i a b (.isTrue ha_eq) db →
        letI := (Etingof.reflFunctorPlus_acmAt ρ a (.isTrue ha_eq))
        letI := (Etingof.reflFunctorPlus_modAt ρ a (.isTrue ha_eq))
        letI := (Etingof.reflFunctorPlus_acmAt ρ b db)
        letI := (Etingof.reflFunctorPlus_modAt ρ b db)
        Etingof.reflFunctorPlus_objAt ρ a (.isTrue ha_eq) →ₗ[k]
          Etingof.reflFunctorPlus_objAt ρ b db)
      db
      (fun _hb_ne => fun e =>
        letI := (Etingof.reflFunctorPlus_acmAt ρ a (.isTrue ha_eq))
        letI := (Etingof.reflFunctorPlus_modAt ρ a (.isTrue ha_eq))
        (DirectSum.component k (Etingof.ArrowsInto Q i)
          (fun x => ρ.obj x.1) ⟨b, e⟩).comp ((ρ.sinkMap i).ker).subtype)
      (fun _hb_eq => fun e =>
        ((hi b).false (ha_eq ▸ e)).elim))
    e

/-- The `equivAt_ne` family with the `Decidable` instance explicit:
`reflFunctorPlus_objAt ρ v d ≃ₗ[k] ρ.obj v` for `v ≠ i`. Copied from the
body of `reflFunctorPlus_equivAt_ne` (the `match inst v i` term). -/
noncomputable def Etingof.reflFunctorPlus_equivAtNeFamily
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation k Q) (v : Q)
    (d : Decidable (v = i)) (hv : v ≠ i) :
    letI := (Etingof.reflFunctorPlus_acmAt ρ v d)
    letI := (Etingof.reflFunctorPlus_modAt ρ v d)
    Etingof.reflFunctorPlus_objAt ρ v d ≃ₗ[k] ρ.obj v :=
  match d with
  | .isTrue hvi => absurd hvi hv
  | .isFalse _ => LinearEquiv.refl k (ρ.obj v)

/-! ### Reduction lemmas on the explicit `Decidable` arguments

Because the `Decidable` value is now an explicit parameter of the helper (not an
opaque instance behind folded structure projections), these reduce by `rfl`. -/

/-- `reflFunctorPlus_equivAtNeFamily` on `.isFalse` reduces to `LinearEquiv.refl`. -/
theorem Etingof.reflFunctorPlus_equivAtNeFamily_isFalse
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation k Q) (v : Q)
    (hv : v = i → False) (hv' : v ≠ i) :
    Etingof.reflFunctorPlus_equivAtNeFamily ρ v (.isFalse hv) hv'
      = LinearEquiv.refl k (ρ.obj v) := rfl

/-- `reflFunctorPlus_objAt` on `.isFalse` reduces to `ρ.obj v`. -/
theorem Etingof.reflFunctorPlus_objAt_isFalse
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation k Q) (v : Q) (hv : v = i → False) :
    Etingof.reflFunctorPlus_objAt ρ v (.isFalse hv) = ρ.obj v := rfl

/-- The object of `reflectionFunctorPlus` at `v` is `reflFunctorPlus_objAt` on the
ambient instance — by `rfl`, since the field family is copied from the structure. -/
theorem Etingof.reflFunctorPlus_obj_eq_objAt
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (v : Q) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) v
      = Etingof.reflFunctorPlus_objAt ρ v (inst v i) := rfl

/-- The `mapLinear` of `reflectionFunctorPlus` equals `reflFunctorPlus_mapLinearAt`
on the ambient instances — by `rfl`, since the field is copied from the structure. -/
theorem Etingof.reflFunctorPlus_mapLinear_eq_mapLinearAt
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (a b : Q)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b) :
    @Etingof.QuiverRepresentation.mapLinear k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) a b e
      = Etingof.reflFunctorPlus_mapLinearAt hi ρ a b (inst a i) (inst b i) e := rfl

/-- `reflFunctorPlus_mapLinearAt` on `(.isFalse, .isFalse)` reduces to `ρ.mapLinear`. -/
theorem Etingof.reflFunctorPlus_mapLinearAt_isFalse_isFalse
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (a b : Q)
    (ha : a = i → False) (hb : b = i → False)
    (e : Etingof.reflFunctorPlus_arrowAt i a b (.isFalse ha) (.isFalse hb)) :
    Etingof.reflFunctorPlus_mapLinearAt hi ρ a b (.isFalse ha) (.isFalse hb) e
      = ρ.mapLinear e := rfl

/-- `reflFunctorPlus_mapLinearAt` on `(.isTrue, .isFalse)` reduces to the
component-of-inclusion map. -/
theorem Etingof.reflFunctorPlus_mapLinearAt_isTrue_isFalse
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (a b : Q)
    (ha : a = i) (hb : b = i → False)
    (e : Etingof.reflFunctorPlus_arrowAt i a b (.isTrue ha) (.isFalse hb)) :
    Etingof.reflFunctorPlus_mapLinearAt hi ρ a b (.isTrue ha) (.isFalse hb) e
      = (letI := (Etingof.reflFunctorPlus_acmAt ρ a (.isTrue ha))
         letI := (Etingof.reflFunctorPlus_modAt ρ a (.isTrue ha))
         (DirectSum.component k (Etingof.ArrowsInto Q i)
          (fun x => ρ.obj x.1) ⟨b, e⟩).comp ((ρ.sinkMap i).ker).subtype) := rfl

end ReflectionFunctorPlusHelpers

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
  unfold Etingof.reflectionFunctorPlus
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
  unfold Etingof.reflectionFunctorPlus
  simp only
  match hd : (‹DecidableEq Q› i i) with
  | .isTrue _ => rw [hd]
  | .isFalse hii => exact absurd rfl hii

/-- `LinearEquiv` at vertex v ≠ i: `F⁺ᵢ(ρ).obj v ≃ₗ[k] ρ.obj v`.
Defined as a pure term-mode match (no `by unfold` tactic block) to ensure
clean definitional reduction when composed with other match-based definitions.

The return type `(reflectionFunctorPlus ...).obj v` delta-reduces in the kernel to
`Decidable.casesOn (inst v i) (fun _ => ρ.obj v) (fun _ => ker(sinkMap))`, and the
match on `inst v i` reduces this to `ρ.obj v` in the `.isFalse` branch. -/
noncomputable def Etingof.reflFunctorPlus_equivAt_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) v ≃ₗ[k] ρ.obj v := by
  unfold Etingof.reflectionFunctorPlus
  simp only
  exact match inst v i with
  | .isTrue hvi => absurd hvi hv
  | .isFalse _ => LinearEquiv.refl k (ρ.obj v)

/-- `reflFunctorPlus_equivAt_ne` applied to an element (whose type is written in
the explicit-instance helper form `reflFunctorPlus_objAt ρ v (inst v i)`, defeq to
`(F).obj v`) equals the explicit-instance family applied to the same element. The
equation lives in the fixed type `ρ.obj v`, and `y`'s type now syntactically carries
`inst v i`, so `cases inst v i` generalizes every occurrence. -/
theorem Etingof.reflFunctorPlus_equivAt_ne_apply
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (v : Q) (hv : v ≠ i)
    (y : Etingof.reflFunctorPlus_objAt ρ v (inst v i)) :
    Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv y
      = Etingof.reflFunctorPlus_equivAtNeFamily ρ v (inst v i) hv y := rfl

/-- `LinearEquiv` at vertex i: `F⁺ᵢ(ρ).obj i ≃ₗ[k] ker(sinkMap i)`.
This reduces the `Decidable.casesOn` in the `reflectionFunctorPlus` definition.
Uses term-mode match for clean definitional reduction. -/
noncomputable def Etingof.reflFunctorPlus_equivAt_eq
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) i ≃ₗ[k] ↥(ρ.sinkMap i).ker := by
  unfold Etingof.reflectionFunctorPlus
  simp only
  exact match inst i i with
  | .isTrue _ => LinearEquiv.refl k ↥(ρ.sinkMap i).ker
  | .isFalse hii => absurd rfl hii

/-- The `equivAt_eq` family with the `Decidable` instance explicit:
`reflFunctorPlus_objAt ρ i d ≃ₗ[k] ker(sinkMap i)`. Same `match` shape as
`reflFunctorPlus_equivAt_eq`, so the apply lemma below holds by `rfl`. -/
noncomputable def Etingof.reflFunctorPlus_equivAtEqFamily
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation k Q) (d : Decidable (i = i)) :
    letI := (Etingof.reflFunctorPlus_acmAt ρ i d)
    letI := (Etingof.reflFunctorPlus_modAt ρ i d)
    Etingof.reflFunctorPlus_objAt ρ i d ≃ₗ[k] ↥(ρ.sinkMap i).ker :=
  match d with
  | .isTrue _ => LinearEquiv.refl k ↥(ρ.sinkMap i).ker
  | .isFalse hii => absurd rfl hii

/-- `reflFunctorPlus_equivAtEqFamily` on `.isTrue` reduces to `LinearEquiv.refl`. -/
theorem Etingof.reflFunctorPlus_equivAtEqFamily_isTrue
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : Etingof.QuiverRepresentation k Q) (h : i = i) :
    Etingof.reflFunctorPlus_equivAtEqFamily ρ (.isTrue h)
      = LinearEquiv.refl k ↥(ρ.sinkMap i).ker := rfl

/-- `reflFunctorPlus_equivAt_eq` applied to an element equals the explicit-instance
family applied to the same element. Holds by `rfl` (same `match inst i i`). -/
theorem Etingof.reflFunctorPlus_equivAt_eq_apply
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    (y : Etingof.reflFunctorPlus_objAt ρ i (inst i i)) :
    Etingof.reflFunctorPlus_equivAt_eq hi ρ y
      = Etingof.reflFunctorPlus_equivAtEqFamily ρ (inst i i) y := rfl

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

/-- The arrow-conversion for the `(a ≠ i, b ≠ i)` case with the `Decidable`
instances explicit. Body copied from `reversedArrow_ne_ne` so that
`reversedArrow_ne_ne ha hb e = reflFunctorPlus_arrowConvertNeNe a b (inst a i) (inst b i) e`
holds by `rfl`. -/
def Etingof.reflFunctorPlus_arrowConvertNeNe
    {Q : Type*} [Quiver Q] {i : Q} (a b : Q)
    (da : Decidable (a = i)) (db : Decidable (b = i))
    (ha : a ≠ i) (hb : b ≠ i)
    (e : Etingof.reflFunctorPlus_arrowAt i a b da db) : a ⟶ b := by
  unfold Etingof.reflFunctorPlus_arrowAt at e
  revert e
  exact match da, db with
  | .isTrue h, _ => absurd h ha
  | .isFalse _, .isTrue h => absurd h hb
  | .isFalse _, .isFalse _ => fun e => e

/-- `reversedArrow_ne_ne ha hb e = reflFunctorPlus_arrowConvertNeNe` on the
ambient instances — by `rfl`, since both unfold to the same case-split. -/
theorem Etingof.reversedArrow_ne_ne_eq_convert
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i a b : Q}
    (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b) :
    Etingof.reversedArrow_ne_ne ha hb e
      = Etingof.reflFunctorPlus_arrowConvertNeNe a b (inst a i) (inst b i) ha hb e := rfl

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
  rw [Etingof.reflFunctorPlus_equivAt_ne_apply hi ρ b hb,
    Etingof.reflFunctorPlus_equivAt_ne_apply hi ρ a ha,
    Etingof.reflFunctorPlus_mapLinear_eq_mapLinearAt]
  -- Revert `e`/`w` and restate their types in the explicit-instance helper form
  -- (defeq), so that casing on the instances generalizes every occurrence.
  revert e w
  change ∀ (e : Etingof.reflFunctorPlus_arrowAt i a b (inst a i) (inst b i))
      (w : Etingof.reflFunctorPlus_objAt ρ a (inst a i)),
    (Etingof.reflFunctorPlus_equivAtNeFamily ρ b (inst b i) hb)
      (Etingof.reflFunctorPlus_mapLinearAt hi ρ a b (inst a i) (inst b i) e w) =
    ρ.mapLinear (Etingof.reflFunctorPlus_arrowConvertNeNe a b (inst a i) (inst b i) ha hb e)
      ((Etingof.reflFunctorPlus_equivAtNeFamily ρ a (inst a i) ha) w)
  -- Every occurrence of `inst a i`/`inst b i` is now an explicit helper argument,
  -- so rewriting the whole (reverted) goal by `Subsingleton.elim` is type-correct.
  rw [Subsingleton.elim (inst a i) (Decidable.isFalse ha),
    Subsingleton.elim (inst b i) (Decidable.isFalse hb)]
  intro e w
  rfl

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

/-- The arrow-conversion for the `(a = i, b ≠ i)` case with the `Decidable`
instances explicit. Same structure as `reversedArrow_eq_ne` so that
`reversedArrow_eq_ne hb e = reflFunctorPlus_arrowConvertEqNe b (inst i i) (inst b i) hb e`
holds by `rfl`. -/
def Etingof.reflFunctorPlus_arrowConvertEqNe
    {Q : Type*} [Quiver Q] {i b : Q}
    (di : Decidable (i = i)) (db : Decidable (b = i)) (hb : b ≠ i)
    (e : Etingof.reflFunctorPlus_arrowAt i i b di db) : b ⟶ i := by
  unfold Etingof.reflFunctorPlus_arrowAt at e
  revert e
  exact match di, db with
  | .isFalse h, _ => absurd rfl h
  | .isTrue _, .isTrue h => absurd h hb
  | .isTrue _, .isFalse _ => fun e => e

/-- `reversedArrow_eq_ne hb e = reflFunctorPlus_arrowConvertEqNe` on the ambient
instances — by `rfl`. -/
theorem Etingof.reversedArrow_eq_ne_eq_convert
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i b : Q}
    (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) i b) :
    Etingof.reversedArrow_eq_ne hb e
      = Etingof.reflFunctorPlus_arrowConvertEqNe (inst i i) (inst b i) hb e := rfl

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
  rw [Etingof.reflFunctorPlus_equivAt_ne_apply hi ρ b hb,
    Etingof.reflFunctorPlus_equivAt_eq_apply hi ρ,
    Etingof.reflFunctorPlus_mapLinear_eq_mapLinearAt,
    Etingof.reversedArrow_eq_ne_eq_convert hb e]
  -- Restate `e`/`w` in the explicit-instance helper form (defeq) so that the
  -- `Subsingleton.elim` rewrite over the reverted goal is type-correct.
  revert e w
  change ∀ (e : Etingof.reflFunctorPlus_arrowAt i i b (inst i i) (inst b i))
      (w : Etingof.reflFunctorPlus_objAt ρ i (inst i i)),
    (Etingof.reflFunctorPlus_equivAtNeFamily ρ b (inst b i) hb)
      (Etingof.reflFunctorPlus_mapLinearAt hi ρ i b (inst i i) (inst b i) e w) =
    (DirectSum.component k (Etingof.ArrowsInto Q i) (fun x => ρ.obj x.1)
      ⟨b, Etingof.reflFunctorPlus_arrowConvertEqNe (inst i i) (inst b i) hb e⟩)
      ((ρ.sinkMap i).ker.subtype
        ((Etingof.reflFunctorPlus_equivAtEqFamily ρ (inst i i)) w))
  rw [Subsingleton.elim (inst i i) (Decidable.isTrue rfl),
    Subsingleton.elim (inst b i) (Decidable.isFalse hb)]
  intro e w
  rfl

end ReflectionFunctorPlusAPI
