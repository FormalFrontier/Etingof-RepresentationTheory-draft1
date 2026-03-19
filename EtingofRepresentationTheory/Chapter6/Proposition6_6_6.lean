import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Proposition 6.6.6: Inverse Relationship of Reflection Functors

(1) If φ : ⊕_{j→i} V_j → V_i is surjective, then F⁻ᵢ F⁺ᵢ V ≅ V.
(2) If ψ : V_i → ⊕_{i→j} V_j is injective, then F⁺ᵢ F⁻ᵢ V ≅ V.

The proof uses the homomorphism theorem: when φ is surjective, K = ker φ embeds
in ⊕V_j, and then (⊕V_j)/K ≅ Im φ = V_i.

## Mathlib correspondence

Requires reflection functor definitions (Definition 6.6.3 and 6.6.4) and
quiver representation isomorphism. Not in Mathlib.
-/

section Reversal

/-- A sink in Q becomes a source in the reversed quiver Q̄ᵢ.
All arrows into i in Q̄ᵢ correspond to arrows out of i in Q, which are empty
since i is a sink. -/
theorem Etingof.isSink_reversedAtVertex_isSource
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i) :
    @Etingof.IsSource Q (Etingof.reversedAtVertex Q i) i := by
  intro j
  constructor
  intro e
  change Etingof.ReversedAtVertexHom Q i j i at e
  by_cases hj : j = i
  · rw [Etingof.ReversedAtVertexHom_eq_eq hj rfl] at e
    rw [hj] at e; exact (hi i).false e
  · rw [Etingof.ReversedAtVertexHom_ne_eq hj rfl] at e
    exact (hi j).false e

/-- A source in Q becomes a sink in the reversed quiver Q̄ᵢ.
All arrows out of i in Q̄ᵢ correspond to arrows into i in Q, which are empty
since i is a source. -/
theorem Etingof.isSource_reversedAtVertex_isSink
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i) :
    @Etingof.IsSink Q (Etingof.reversedAtVertex Q i) i := by
  intro j
  constructor
  intro e
  change Etingof.ReversedAtVertexHom Q i i j at e
  by_cases hj : j = i
  · rw [Etingof.ReversedAtVertexHom_eq_eq rfl hj] at e
    rw [hj] at e; exact (hi i).false e
  · rw [Etingof.ReversedAtVertexHom_eq_ne rfl hj] at e
    exact (hi j).false e

end Reversal

section Iso

/-- An isomorphism between two quiver representations on the same quiver.
Consists of pointwise linear equivalences that commute with the representation maps. -/
structure Etingof.QuiverRepresentation.Iso
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q) : Type _ where
  /-- Pointwise linear equivalences between vertex spaces -/
  equivAt : ∀ v : Q, ρ₁.obj v ≃ₗ[k] ρ₂.obj v
  /-- Naturality: the diagram commutes -/
  naturality : ∀ {a b : Q} (e : a ⟶ b) (x : ρ₁.obj a),
    (equivAt b) (ρ₁.mapLinear e x) = ρ₂.mapLinear e ((equivAt a) x)

/-- The double reversal at vertex i recovers the original quiver instance.
This enables transporting representations from (Q̄ᵢ)̄ᵢ back to Q. -/
@[ext]
private theorem Quiver.ext' {V : Type*} {inst₁ inst₂ : Quiver V}
    (h : ∀ a b, @Quiver.Hom V inst₁ a b = @Quiver.Hom V inst₂ a b) :
    inst₁ = inst₂ := by
  cases inst₁; cases inst₂
  congr 1; funext a b; exact h a b

private theorem Etingof.reversedAtVertex_twice
    (Q : Type*) [DecidableEq Q] [inst : Quiver Q] (i : Q) :
    @Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i = inst := by
  apply Quiver.ext'
  intro a b
  change @Etingof.ReversedAtVertexHom Q _ (Etingof.reversedAtVertex Q i) i a b = (a ⟶ b)
  -- Two-layer reduction: outer ReversedAtVertexHom uses reversed quiver,
  -- inner uses original quiver. Use `trans` + `change` to bridge.
  by_cases ha : a = i <;> by_cases hb : b = i
  · -- a = i, b = i
    trans @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b
    · exact @Etingof.ReversedAtVertexHom_eq_eq Q _ (Etingof.reversedAtVertex Q i) i a b ha hb
    · change Etingof.ReversedAtVertexHom Q i a b = (a ⟶ b)
      exact Etingof.ReversedAtVertexHom_eq_eq ha hb
  · -- a = i, b ≠ i: outer gives reversed (b ⟶ i in reversed quiver)
    trans @Quiver.Hom Q (Etingof.reversedAtVertex Q i) b i
    · exact @Etingof.ReversedAtVertexHom_eq_ne Q _ (Etingof.reversedAtVertex Q i) i a b ha hb
    · change Etingof.ReversedAtVertexHom Q i b i = (a ⟶ b)
      rw [Etingof.ReversedAtVertexHom_ne_eq hb rfl]
      exact congrArg (· ⟶ b) ha.symm
  · -- a ≠ i, b = i: outer gives reversed (i ⟶ a in reversed quiver)
    trans @Quiver.Hom Q (Etingof.reversedAtVertex Q i) i a
    · exact @Etingof.ReversedAtVertexHom_ne_eq Q _ (Etingof.reversedAtVertex Q i) i a b ha hb
    · change Etingof.ReversedAtVertexHom Q i i a = (a ⟶ b)
      rw [Etingof.ReversedAtVertexHom_eq_ne rfl ha]
      exact congrArg (a ⟶ ·) hb.symm
  · -- a ≠ i, b ≠ i: outer gives unchanged (a ⟶ b in reversed quiver)
    trans @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b
    · exact @Etingof.ReversedAtVertexHom_ne_ne Q _ (Etingof.reversedAtVertex Q i) i a b ha hb
    · change Etingof.ReversedAtVertexHom Q i a b = (a ⟶ b)
      exact Etingof.ReversedAtVertexHom_ne_ne ha hb

/-- Transport a representation from the double-reversed quiver (Q̄ᵢ)̄ᵢ back to Q.

Reversing all arrows at vertex i twice recovers the original quiver. Vertex spaces
are unchanged; maps are transported through the canonical arrow identification. -/
noncomputable def Etingof.QuiverRepresentation.transportReversedTwice
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q}
    (ρ : @Etingof.QuiverRepresentation k Q _
      (@Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i)) :
    Etingof.QuiverRepresentation k Q :=
  Etingof.reversedAtVertex_twice Q i ▸ ρ

/-- If we can construct a `QuiverRepresentation.Iso` between ρ₁ and ρ₂ on
quiver instance `inst₁`, this gives an Iso between `(h ▸ ρ₁)` and `(h ▸ ρ₂)` on `inst₂`.
This is the key lemma for handling the `Eq.mpr` from `transportReversedTwice`. -/
private noncomputable def Etingof.QuiverRepresentation.transport_iso
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q]
    {inst₁ inst₂ : Quiver Q} (h : inst₁ = inst₂)
    {ρ₁ ρ₂ : @Etingof.QuiverRepresentation k Q _ inst₁}
    (iso : @Etingof.QuiverRepresentation.Iso k _ Q inst₁ ρ₁ ρ₂) :
    @Etingof.QuiverRepresentation.Iso k _ Q inst₂ (h ▸ ρ₁) (h ▸ ρ₂) := by
  subst h; exact iso

/-- Key lemma: to prove `Nonempty (Iso (h ▸ ρ₁) ρ₂)` on `inst₂`,
it suffices to prove `Nonempty (Iso ρ₁ (h.symm ▸ ρ₂))` on `inst₁`.
This allows working on a single quiver instance after `subst`. -/
private theorem Etingof.QuiverRepresentation.Iso.transport_nonempty
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q]
    {inst₁ inst₂ : Quiver Q} (h : inst₁ = inst₂)
    {ρ₁ : @Etingof.QuiverRepresentation k Q _ inst₁}
    {ρ₂ : @Etingof.QuiverRepresentation k Q _ inst₂}
    (iso : Nonempty (@Etingof.QuiverRepresentation.Iso k _ Q inst₁ ρ₁ (h.symm ▸ ρ₂))) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ Q inst₂ (h ▸ ρ₁) ρ₂) := by
  subst h; exact iso

/-- A cross-quiver isomorphism: linear equivalences at each vertex between
representations on potentially different (but equal) quiver instances.
Uses `@` notation throughout to avoid synthesis check issues.
Converts to a standard Iso via `subst`. -/
private noncomputable def Etingof.QuiverRepresentation.crossIsoToIso
    {k : Type*} [CommSemiring k] {Q : Type*}
    {inst₁ inst₂ : Quiver Q} (h : inst₁ = inst₂)
    {ρ₁ : @Etingof.QuiverRepresentation k Q _ inst₁}
    {ρ₂ : @Etingof.QuiverRepresentation k Q _ inst₂}
    (equivAt : ∀ v : Q,
      @Etingof.QuiverRepresentation.obj k Q _ inst₁ ρ₁ v ≃ₗ[k]
      @Etingof.QuiverRepresentation.obj k Q _ inst₂ ρ₂ v)
    (naturality : ∀ {a b : Q} (e : @Quiver.Hom Q inst₂ a b)
      (x : @Etingof.QuiverRepresentation.obj k Q _ inst₁ ρ₁ a),
      (equivAt b)
        (@Etingof.QuiverRepresentation.mapLinear k Q _ inst₁ ρ₁ a b (h.symm ▸ e) x) =
      @Etingof.QuiverRepresentation.mapLinear k Q _ inst₂ ρ₂ a b e ((equivAt a) x)) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ Q inst₂ (h ▸ ρ₁) ρ₂) := by
  subst h; exact ⟨⟨equivAt, naturality⟩⟩

end Iso

section Helpers

/-- The obj of a ▸-transported representation is unchanged at each vertex. -/
private theorem Etingof.QuiverRepresentation.obj_transport
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q]
    {inst₁ inst₂ : Quiver Q} (h : inst₁ = inst₂)
    (ρ : @Etingof.QuiverRepresentation k Q _ inst₁) (v : Q) :
    @Etingof.QuiverRepresentation.obj k Q _ inst₂ (h ▸ ρ) v =
    @Etingof.QuiverRepresentation.obj k Q _ inst₁ ρ v := by
  subst h; rfl

-- Note: reflFunctorPlus_obj_ne, reflFunctorPlus_obj_eq, reflFunctorMinus_obj_ne
-- are now public API in Definition6_6_3.lean and Definition6_6_4.lean.
-- The reflFunctorPlus_equivAt_ne and reflFunctorPlus_equivAt_eq LinearEquivs
-- are also available from Definition6_6_3.lean.

/-- For an arrow `i →_{Q̄ᵢ} j` in the reversed quiver (with i a sink), the target vertex
j ≠ i. This is because i is a source in Q̄ᵢ. -/
private theorem Etingof.arrowsOutReversed_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (a : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) : a.fst ≠ i := by
  obtain ⟨j, e⟩ := a
  change Etingof.ReversedAtVertexHom Q i i j at e
  by_cases hj : j = i
  · rw [Etingof.ReversedAtVertexHom_eq_eq rfl hj] at e
    rw [hj] at e; exact ((hi i).false e).elim
  · exact hj

/-- Extract the original arrow j →_Q i from a reversed arrow i →_{Q̄ᵢ} j. -/
private def Etingof.arrowsOutReversed_origArrow
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (a : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) : a.fst ⟶ i := by
  obtain ⟨j, e⟩ := a
  change Etingof.ReversedAtVertexHom Q i i j at e
  have hne := Etingof.arrowsOutReversed_ne hi ⟨j, e⟩
  rw [Etingof.ReversedAtVertexHom_eq_ne rfl hne] at e; exact e

/-- Map arrows into i in Q to arrows out of i in Q̄ᵢ.
Since i is a sink (no arrows out), any arrow j → i in Q gives a reversed
arrow i →_{Q̄ᵢ} j. The underlying arrow data is unchanged. -/
private def Etingof.arrowsInto_to_arrowsOutReversed
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i := by
  obtain ⟨j, e⟩ := b
  refine ⟨j, ?_⟩
  -- Need i →_{Q̄ᵢ} j, i.e., ReversedAtVertexHom Q i i j
  change Etingof.ReversedAtVertexHom Q i i j
  have hji : j ≠ i := by
    intro heq; rw [heq] at e; exact (hi i).false e
  rw [Etingof.ReversedAtVertexHom_eq_ne rfl hji]; exact e

/-- Round-trip: extracting the original arrow from a converted ArrowsInto
gives back the original arrow. -/
private theorem Etingof.origArrow_arrowsInto_to_arrowsOutReversed
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    Etingof.arrowsOutReversed_origArrow hi
      (Etingof.arrowsInto_to_arrowsOutReversed hi b) = b.2 := by
  obtain ⟨j, e⟩ := b
  simp only [arrowsInto_to_arrowsOutReversed, arrowsOutReversed_origArrow, id]
  -- Goal reduces to cast round-trip through ReversedAtVertexHom_eq_ne
  -- The .mp and .mpr from the Eq cast cancel
  change cast _ (cast _ e) = e
  simp [cast_cast]

/-- The component of `arrowsInto_to_arrowsOutReversed` at j gives the original arrow j ⟶ i. -/
private theorem Etingof.arrowsInto_to_arrowsOutReversed_fst
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    (Etingof.arrowsInto_to_arrowsOutReversed hi b).fst = b.fst := by
  rfl

/-- At v ≠ i, F⁻(F⁺(V)).obj v ≃ₗ[k] ρ.obj v. Both sides reduce to ρ.obj v
through the Decidable.casesOn in the reflection functor definitions. -/
private noncomputable def Etingof.equivAt_ne_sink
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i)
      (@Etingof.reflectionFunctorMinus k _ Q _
        (@Etingof.reversedAtVertex Q _ inst i) i
        (@Etingof.isSink_reversedAtVertex_isSource Q _ inst i hi)
        (@Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ) _) v ≃ₗ[k]
    @Etingof.QuiverRepresentation.obj k Q _ inst ρ v := by
  unfold Etingof.reflectionFunctorMinus
  simp only
  match hd1 : (‹DecidableEq Q› v i) with
  | .isTrue hvi => exact absurd hvi hv
  | .isFalse _ =>
    rw [hd1]; dsimp only []
    -- After reducing F⁻, goal becomes F⁺(V).obj v ≃ₗ[k] ρ.obj v
    -- Unfold F⁺ and reduce similarly
    unfold Etingof.reflectionFunctorPlus
    simp only
    match hd2 : (‹DecidableEq Q› v i) with
    | .isTrue hvi => exact absurd hvi hv
    | .isFalse _ => rw [hd2]

/-- The reindexed map Φ : ⊕_{ArrowsOutOf Q̄ᵢ i} F⁺(V).obj a.fst →ₗ ρ.obj i
is surjective when sinkMap is surjective.

Φ is essentially sinkMap after reindexing through the
ArrowsInto ↔ ArrowsOutOf correspondence and equivAt_ne.

The Φ parameter must be `DirectSum.toModule k _ _ Φ_component` where
Φ_component a = mapLinear(origArrow a) ∘ equivAt_ne. We take it as a parameter
to avoid type class synthesis issues with multiple quiver instances. -/
private theorem Etingof.sinkMap_reindex_surj
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (hsurj : Function.Surjective (ρ.sinkMap i))
    {M : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i → Type*}
    [∀ a, AddCommMonoid (M a)] [∀ a, Module k (M a)]
    (Φ : DirectSum (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) M →ₗ[k] ρ.obj i)
    (hΦ_basic : ∀ (b : @Etingof.ArrowsInto Q inst i) (v : ρ.obj b.fst),
      ∃ z, Φ z = ρ.mapLinear b.2 v) :
    Function.Surjective Φ := by
  classical
  -- Prove: sinkMap x ∈ range(Φ) for all x, hence Φ is surjective
  suffices h : ∀ x, (ρ.sinkMap i) x ∈ Set.range Φ by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    obtain ⟨z, hz⟩ := h x
    exact ⟨z, by rw [hz, hx]⟩
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, by simp [map_zero]⟩
  | of b v =>
    obtain ⟨z, hz⟩ := hΦ_basic b v
    refine ⟨z, ?_⟩
    -- Goal: sinkMap (of b v) = Φ z = mapLinear b.2 v (by hz)
    rw [hz]
    -- Goal: sinkMap (of b v) = mapLinear b.2 v
    -- sinkMap is DirectSum.toModule (after classical), so toModule_lof applies
    delta Etingof.QuiverRepresentation.sinkMap
    erw [DirectSum.toModule_lof]
  | add x₁ x₂ ih₁ ih₂ =>
    rw [map_add]
    obtain ⟨z₁, hz₁⟩ := ih₁
    obtain ⟨z₂, hz₂⟩ := ih₂
    exact ⟨z₁ + z₂, by rw [map_add, hz₁, hz₂]⟩

set_option maxHeartbeats 3200000 in
-- reason: unfolding reflectionFunctorPlus + Decidable.casesOn reduction for exactness
/-- The composition Φ ∘ source_map = 0: applying Φ after the F⁺ source map
vanishes on ker(sinkMap). This is the forward direction of exactness.

Proved by reducing everything through reflFunctorPlus_mapLinear_eq_ne and
showing the resulting sum equals sinkMap applied to a kernel element. -/
private theorem Etingof.Φ_comp_source_eq_zero
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (w : @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) i) :
    ∑ x : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i,
      (@Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ x.fst i
        (@Etingof.arrowsOutReversed_origArrow Q _ inst i hi x))
      ((@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ x.fst
        (@Etingof.arrowsOutReversed_ne Q _ inst i hi x))
      (@Etingof.QuiverRepresentation.mapLinear k Q _
        (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) i x.fst x.snd w)) = 0 := by
  -- Use the API lemma to reduce each term
  simp_rw [Etingof.reflFunctorPlus_mapLinear_eq_ne hi ρ]
  -- Goal: ∑ x, ρ.mapLinear(origArrow x) (component ⟨x.fst, revArrow x.snd⟩ (subtype (equivAt_eq w))) = 0
  -- Show this equals sinkMap(subtype(equivAt_eq w)) = 0 since equivAt_eq w ∈ ker(sinkMap)
  -- Step 1: equivAt_eq w ∈ ker(sinkMap), so sinkMap(subtype(equivAt_eq w)) = 0
  have hmem : (ρ.sinkMap i) ((ρ.sinkMap i).ker.subtype
      (Etingof.reflFunctorPlus_equivAt_eq hi ρ w)) = 0 := by
    exact (Etingof.reflFunctorPlus_equivAt_eq hi ρ w).property
  -- The sum should equal sinkMap(subtype(equivAt_eq w)) which is 0 by hmem.
  -- Proving the sum equals sinkMap requires:
  -- 1. A DirectSum.toModule decomposition lemma (toModule y = ∑_b f b (component b y))
  -- 2. A reindexing bijection ArrowsOutOf instR i ↔ ArrowsInto inst i
  -- 3. Arrow equality: origArrow x = reversedArrow_eq_ne (arrowsOutReversed_ne x) x.snd
  -- Step 3 is blocked by the same Decidable.casesOn dependent type issue.
  -- See issue #1263 for the full analysis.
  sorry

set_option maxHeartbeats 800000 in
/-- At vertex i, F⁻(F⁺(V)).obj i ≃ₗ[k] ρ.obj i when the sink map is surjective.

F⁺ᵢ(V).obj i = ker(φ) where φ = sinkMap. Then F⁻ᵢ produces the cokernel
of the source map at i, which is the inclusion ker(φ) ↪ ⊕V_j.
So F⁻(F⁺(V)).obj i = (⊕V_j) / ker(φ) ≅ V_i by the first isomorphism theorem. -/
private noncomputable def Etingof.equivAt_eq_sink
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (hsurj : Function.Surjective (ρ.sinkMap i)) :
    @Etingof.QuiverRepresentation.obj k Q _
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i)
      (@Etingof.reflectionFunctorMinus k _ Q _
        (@Etingof.reversedAtVertex Q _ inst i) i
        (@Etingof.isSink_reversedAtVertex_isSource Q _ inst i hi)
        (@Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ) _) i ≃ₗ[k]
    @Etingof.QuiverRepresentation.obj k Q _ inst ρ i := by
  -- Upgrade to AddCommGroup (needed for quotient module)
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfField (k := k)
  -- Reduce F⁻ at vertex i (isTrue branch)
  unfold Etingof.reflectionFunctorMinus
  simp only
  match hd1 : (‹DecidableEq Q› i i) with
  | .isFalse hii => exact absurd rfl hii
  | .isTrue _ =>
    -- Goal: (⊕_{a : ArrowsOutOf Q̄ᵢ i} F⁺(V)_a.fst) ⧸ range(ψ') ≃ₗ[k] V_i
    -- Strategy: Φ = sinkMap after reindexing, then first isomorphism theorem
    rw [hd1]; dsimp only []
    classical
    -- Goal: (⊕_{a : ArrowsOutOf_{Q̄ᵢ} i} F⁺(V).obj a.fst) ⧸ range(ψ') ≃ₗ[k] ρ.obj i
    -- Strategy: construct forward and inverse maps directly
    let instR := @Etingof.reversedAtVertex Q _ inst i
    let ρ' := @Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ
    -- Forward map: quotient → V_i
    -- Component maps: F⁺(V).obj a.fst → V_i via equivAt_ne then mapLinear
    let Φ_component : ∀ a : @Etingof.ArrowsOutOf Q instR i,
        @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst →ₗ[k]
        @Etingof.QuiverRepresentation.obj k Q _ inst ρ i :=
      fun a =>
        (@Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ a.fst i
          (@Etingof.arrowsOutReversed_origArrow Q _ inst i hi a)).comp
        (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst
          (@Etingof.arrowsOutReversed_ne Q _ inst i hi a)).toLinearMap
    let Φ : (DirectSum (@Etingof.ArrowsOutOf Q instR i)
        (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst)) →ₗ[k]
        @Etingof.QuiverRepresentation.obj k Q _ inst ρ i :=
      DirectSum.toModule k (@Etingof.ArrowsOutOf Q instR i)
        (@Etingof.QuiverRepresentation.obj k Q _ inst ρ i) Φ_component
    -- Provide AddCommGroup instances for quotient module construction
    letI acg_comp : ∀ a : @Etingof.ArrowsOutOf Q instR i,
        AddCommGroup (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst) :=
      fun a => @Etingof.addCommGroupOfField k _ _ (ρ'.instAddCommMonoid a.fst) (ρ'.instModule a.fst)
    letI acg_ds : AddCommGroup (DirectSum (@Etingof.ArrowsOutOf Q instR i)
        (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst)) :=
      @Etingof.addCommGroupOfField k _ _ _ _
    -- Use first isomorphism theorem: need Φ surjective and range(ψ') = ker(Φ)
    -- Step 1: Show Φ is surjective (follows from surjectivity of sinkMap φ)
    -- Construct reindexing equivalence: ArrowsOutOf Q̄ᵢ i → ArrowsInto Q i
    let reindex : @Etingof.ArrowsOutOf Q instR i → @Etingof.ArrowsInto Q inst i :=
      fun a => ⟨a.fst, @Etingof.arrowsOutReversed_origArrow Q _ inst i hi a⟩
    -- Component transport: equivAt_ne gives F⁺(V)_j ≃ V_j for j ≠ i
    -- So Φ_component a = ρ.mapLinear(origArrow) ∘ equivAt_ne
    --                   = sinkMap component at (reindex a)
    have hΦsurj : Function.Surjective Φ :=
      @Etingof.sinkMap_reindex_surj k _ Q _ inst i hi ρ _ hsurj
        (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst)
        (fun a => ρ'.instAddCommMonoid a.fst) (fun a => ρ'.instModule a.fst) Φ
        (fun b v => by
          -- Construct preimage: lof a (equivAt_ne.symm v) where a = arrowsInto_to_arrowsOutReversed b
          let a := @Etingof.arrowsInto_to_arrowsOutReversed Q _ inst i hi b
          let hne := @Etingof.arrowsOutReversed_ne Q _ inst i hi a
          let v' := (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst hne).symm v
          refine ⟨DirectSum.lof k _ _ a v', ?_⟩
          simp only [Φ, Φ_component, DirectSum.toModule_lof, LinearMap.comp_apply,
            LinearEquiv.coe_toLinearMap, v']
          -- Goal: mapLinear (origArrow a) (equivAt_ne ⋯ (equivAt_ne hne).symm v) = mapLinear b.2 v
          -- Two equivAt_ne have different proof args; apply_symm_apply still works
          have heq_proof : @Etingof.arrowsOutReversed_ne Q _ inst i hi a =
              @Etingof.arrowsOutReversed_ne Q _ inst i hi
                (@Etingof.arrowsInto_to_arrowsOutReversed Q _ inst i hi b) := rfl
          conv_lhs =>
            rw [show ∀ h, (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst h)
                ((@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst hne).symm v) = v
              from fun h => by exact LinearEquiv.apply_symm_apply _ v]
          exact congrArg (fun e => @Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ _ i e v)
            (@Etingof.origArrow_arrowsInto_to_arrowsOutReversed Q _ inst i hi b))
    -- Step 2: Show range(source map) = ker(Φ)
    have hker : (∑ a : @Etingof.ArrowsOutOf Q instR i,
        (DirectSum.lof k (@Etingof.ArrowsOutOf Q instR i)
          (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst) a).comp
          (@Etingof.QuiverRepresentation.mapLinear k Q _ instR ρ' i a.fst a.snd)).range =
        LinearMap.ker Φ := by
      -- Exactness: range(source_map) = ker(Φ)
      -- Uses Φ_comp_source_eq_zero for the forward direction (range ≤ ker),
      -- which applies reflFunctorPlus_mapLinear_eq_ne to reduce individual terms.
      -- The remaining gap is the sum reindexing (ArrowsOutOf ↔ ArrowsInto) and
      -- arrow equality (origArrow vs reversedArrow_eq_ne), both blocked by
      -- Decidable.casesOn dependent type transport issues.
      -- The reverse direction (ker ≤ range) requires constructing preimages.
      sorry
    -- Compose quotEquivOfEq with quotKerEquivOfSurjective
    exact (Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective Φ hΦsurj)

end Helpers

set_option maxHeartbeats 800000 in
/-- If φ is surjective at a sink, then applying F⁻ᵢ after F⁺ᵢ recovers V
up to isomorphism of representations.

The composition F⁻ᵢ(F⁺ᵢ(V)) lives on the double-reversed quiver (Q̄ᵢ)̄ᵢ, which is
canonically identified with Q via `transportReversedTwice`. Under this identification,
the resulting representation is isomorphic to the original.

(Etingof Proposition 6.6.6, part 1) -/
theorem Etingof.Proposition6_6_6_sink
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (hsurj : Function.Surjective (ρ.sinkMap i)) :
    Nonempty (Etingof.QuiverRepresentation.Iso
      (Etingof.QuiverRepresentation.transportReversedTwice
        (@Etingof.reflectionFunctorMinus k _ Q _
          (Etingof.reversedAtVertex Q i) i
          (Etingof.isSink_reversedAtVertex_isSource hi)
          (Etingof.reflectionFunctorPlus Q i hi ρ) _))
      ρ) := by
  -- Use crossIsoToIso: construct linear equivs at each vertex between
  -- F⁻(F⁺(V)) (on instDR) and ρ (on inst), using @ to avoid synthesis checks.
  let instR := @Etingof.reversedAtVertex Q _ inst i
  let instDR := @Etingof.reversedAtVertex Q _ instR i
  let ρ_plus := @Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ
  let ρ_dr := @Etingof.reflectionFunctorMinus k _ Q _ instR i
      (@Etingof.isSink_reversedAtVertex_isSource Q _ inst i hi) ρ_plus _
  exact Etingof.QuiverRepresentation.crossIsoToIso
    (@Etingof.reversedAtVertex_twice Q _ inst i)
    (fun v => by
      by_cases hv : v = i
      · -- v = i: first isomorphism theorem
        cases hv
        exact @Etingof.equivAt_eq_sink k _ Q _ inst i hi ρ _ _ _ hsurj
      · -- v ≠ i: both sides reduce to ρ.obj v
        exact @Etingof.equivAt_ne_sink k _ Q _ inst i hi ρ _ v hv)
    (fun {a b} e x => by
      -- Naturality: the isomorphism commutes with representation maps.
      -- Case analysis on a = i and b = i:
      -- • a ≠ i, b ≠ i: both equivs are identity, maps unchanged — trivial
      -- • a = i, b ≠ i: involves equivAt_eq_sink on the source vertex
      -- • a ≠ i, b = i: involves equivAt_eq_sink on the target vertex
      -- • a = i, b = i: self-loop at sink, vacuous
      -- BLOCKER: Same Decidable.casesOn type transport issue as equivAt_eq_sink.
      -- The representation maps of F⁻(F⁺(V)) are defined via Decidable.casesOn
      -- and don't reduce without explicit case-splitting on DecidableEq instances.
      sorry)

/-- If ψ is injective at a source, then applying F⁺ᵢ after F⁻ᵢ recovers V
up to isomorphism of representations.

The composition F⁺ᵢ(F⁻ᵢ(V)) lives on the double-reversed quiver (Q̄ᵢ)̄ᵢ, which is
canonically identified with Q via `transportReversedTwice`. Under this identification,
the resulting representation is isomorphic to the original.

(Etingof Proposition 6.6.6, part 2) -/
theorem Etingof.Proposition6_6_6_source
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (hinj : Function.Injective (ρ.sourceMap i)) :
    Nonempty (Etingof.QuiverRepresentation.Iso
      (Etingof.QuiverRepresentation.transportReversedTwice
        (@Etingof.reflectionFunctorPlus k _ Q _
          (Etingof.reversedAtVertex Q i) i
          (Etingof.isSource_reversedAtVertex_isSink hi)
          (Etingof.reflectionFunctorMinus Q i hi ρ)))
      ρ) := by
  -- Dual of the sink case:
  -- • F⁻ᵢ(V).obj i = coker(ψ) where ψ = sourceMap
  -- • F⁺ᵢ at vertex i gives ker of sink map of F⁻(V)
  -- • When ψ is injective: ker(sink map of F⁻(V)) ≅ V_i
  -- BLOCKER: Same Decidable.casesOn type transport issue as the sink case.
  -- Proving this requires the same infrastructure: direct sum reindexing
  -- between ArrowsInto Q̄ᵢ i and ArrowsOutOf Q i, plus type transport
  -- for the component types through Decidable.casesOn.
  sorry
