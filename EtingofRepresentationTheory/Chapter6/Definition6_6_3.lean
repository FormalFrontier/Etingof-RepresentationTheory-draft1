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
          (fun hb_eq => fun e => ((hi a).false e).elim))
        (fun ha_eq => @Decidable.casesOn (b = i)
          (fun db => arrowAt (.isTrue ha_eq) db → objAt a (.isTrue ha_eq) →ₗ[k] objAt b db)
          (inst b i)
          (fun _hb_ne => fun e =>
            (DirectSum.component k (Etingof.ArrowsInto V i)
              (fun x => ρ.obj x.1) ⟨b, e⟩).comp (LinearMap.ker φ).subtype)
          (fun hb_eq => fun e =>
            ((hi b).false (ha_eq ▸ e)).elim)))

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
    cases inst a i with
    | isTrue h => exact absurd h ha
    | isFalse _ => rfl
  have h_db : inst b i = .isFalse hb := by
    cases inst b i with
    | isTrue h => exact absurd h hb
    | isFalse _ => rfl
  revert e w
  unfold Etingof.reflFunctorPlus_equivAt_ne Etingof.reversedArrow_ne_ne
    Etingof.reflectionFunctorPlus Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
  simp only []
  rw [h_da, h_db]
  intro e w
  rfl

end ReflectionFunctorPlusAPI
