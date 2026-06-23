import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Reflection Functor Infrastructure

Shared infrastructure for the proof of Proposition 6.6.6 (inverse relationship of
reflection functors). This file provides:

- `QuiverRepresentation.Iso`: isomorphism between quiver representations
- `reversedAtVertex_twice`: double reversal recovers the original quiver
- `transportReversedTwice`, `crossIsoToIso`: transport through double reversal
- Arrow reindexing equivalences between reversed and original quivers
- `reversedArrow_*_is_cast` and `*_twice`: double-reversal cast lemmas
- `exact_of_dim`: first isomorphism theorem for exact sequences

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

theorem Etingof.reversedAtVertex_twice
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

/-- A cross-quiver isomorphism: linear equivalences at each vertex between
representations on potentially different (but equal) quiver instances.
Uses `@` notation throughout to avoid synthesis check issues.
Converts to a standard Iso via `subst`. -/
noncomputable def Etingof.QuiverRepresentation.crossIsoToIso
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

section MapIso

/-! ## Functoriality of F⁻ᵢ on isomorphisms

Given an isomorphism σ : ρ₁ ≅ ρ₂ of quiver representations and a source vertex i,
we construct F⁻ᵢ(σ) : F⁻ᵢ(ρ₁) ≅ F⁻ᵢ(ρ₂).

At vertices v ≠ i, the equivalence is the composition:
  F⁻(ρ₁).obj v ≃ ρ₁.obj v ≃[σ] ρ₂.obj v ≃ F⁻(ρ₂).obj v

At vertex i, both sides are cokernels of source maps ψ₁, ψ₂. The iso σ induces
a componentwise equivalence on the direct sums that maps range(ψ₁) to range(ψ₂),
hence descends to an equivalence on quotients.
-/

/-- Componentwise linear equiv on direct sums induced by linear equivs at each component.
Used to transport source maps through an isomorphism σ between representations. -/
noncomputable def Etingof.directSumMapEquiv
    {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι]
    {M₁ M₂ : ι → Type*}
    [∀ a, AddCommMonoid (M₁ a)] [∀ a, Module k (M₁ a)]
    [∀ a, AddCommMonoid (M₂ a)] [∀ a, Module k (M₂ a)]
    (e : ∀ a, M₁ a ≃ₗ[k] M₂ a) :
    DirectSum ι M₁ ≃ₗ[k] DirectSum ι M₂ :=
  DFinsupp.mapRange.linearEquiv e

theorem Etingof.directSumMapEquiv_lof
    {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι]
    {M₁ M₂ : ι → Type*}
    [∀ a, AddCommMonoid (M₁ a)] [∀ a, Module k (M₁ a)]
    [∀ a, AddCommMonoid (M₂ a)] [∀ a, Module k (M₂ a)]
    (e : ∀ a, M₁ a ≃ₗ[k] M₂ a)
    (a : ι) (v : M₁ a) :
    Etingof.directSumMapEquiv e (DirectSum.lof k ι M₁ a v) =
      DirectSum.lof k ι M₂ a (e a v) := by
  change (DFinsupp.mapRange.linearEquiv e) (DFinsupp.single a v) =
    DFinsupp.single a ((e a) v)
  ext b
  rw [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_apply,
      DFinsupp.single_apply, DFinsupp.single_apply]
  split
  · next h => subst h; rfl
  · exact map_zero _

/-- σ-induced map on direct sums sends range(ψ₁) to range(ψ₂).
This is the key compatibility needed to descend to quotients. -/
theorem Etingof.directSumMapEquiv_maps_sourceRange
    {k : Type*} [CommRing k] {Q : Type*} [Quiver Q]
    {i : Q}
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (σ : Etingof.QuiverRepresentation.Iso ρ₁ ρ₂)
    [Fintype (Etingof.ArrowsOutOf Q i)] [DecidableEq (Etingof.ArrowsOutOf Q i)]
    (ψ₁ : ρ₁.obj i →ₗ[k] DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.fst))
    (hψ₁ : ψ₁ = ∑ a : Etingof.ArrowsOutOf Q i,
        (DirectSum.lof k _ (fun a => ρ₁.obj a.fst) a).comp (ρ₁.mapLinear a.2))
    (ψ₂ : ρ₂.obj i →ₗ[k] DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.fst))
    (hψ₂ : ψ₂ = ∑ a : Etingof.ArrowsOutOf Q i,
        (DirectSum.lof k _ (fun a => ρ₂.obj a.fst) a).comp (ρ₂.mapLinear a.2))
    (F : DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.fst) ≃ₗ[k]
         DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.fst))
    (hF : ∀ (a : Etingof.ArrowsOutOf Q i) (v : ρ₁.obj a.fst),
        F (DirectSum.lof k _ _ a v) = DirectSum.lof k _ _ a (σ.equivAt a.fst v)) :
    Submodule.map F.toLinearMap (LinearMap.range ψ₁) = LinearMap.range ψ₂ := by
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_toLinearMap]
  constructor
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    refine ⟨σ.equivAt i v, ?_⟩
    rw [hψ₁, hψ₂]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    congr 1; ext1 a
    rw [hF]
    congr 1
    exact (σ.naturality a.2 v).symm
  · rintro ⟨w, rfl⟩
    refine ⟨ψ₁ ((σ.equivAt i).symm w), ⟨(σ.equivAt i).symm w, rfl⟩, ?_⟩
    rw [hψ₁, hψ₂]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    congr 1; ext1 a
    rw [hF]
    congr 1
    rw [σ.naturality a.2, LinearEquiv.apply_symm_apply]

set_option maxHeartbeats 1600000 in
/-- The vertex-i component of the map iso, with the `Decidable` discriminant `d` exposed
as an explicit argument (mirroring `reflFunctorMinus_equivAtAt_eq`). At `d = .isTrue _`
it is the descended quotient equivalence between the cokernels. Exposing `d` lets
consumer proofs reduce the `isTrue` branch via `rw` on the explicit argument, avoiding the
v4.29 "motive is not type correct" failure of rewriting an inline `match` discriminant. -/
noncomputable def Etingof.reflectionFunctorMinus_map_iso_equivAtAt_eq
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (σ : Etingof.QuiverRepresentation.Iso ρ₁ ρ₂)
    [Fintype (Etingof.ArrowsOutOf Q i)] (d : Decidable (i = i)) :
    letI := Etingof.reflFunctorMinus_acmAt ρ₁ i i d
    letI := Etingof.reflFunctorMinus_acmAt ρ₂ i i d
    letI := Etingof.reflFunctorMinus_modAt ρ₁ i i d
    letI := Etingof.reflFunctorMinus_modAt ρ₂ i i d
    Etingof.reflFunctorMinus_objAt ρ₁ i i d ≃ₗ[k]
      Etingof.reflFunctorMinus_objAt ρ₂ i i d :=
  letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  letI : DecidableEq (Etingof.ArrowsOutOf Q i) := Classical.decEq _
  @Decidable.casesOn (i = i)
    (fun d =>
      letI := Etingof.reflFunctorMinus_acmAt ρ₁ i i d
      letI := Etingof.reflFunctorMinus_acmAt ρ₂ i i d
      letI := Etingof.reflFunctorMinus_modAt ρ₁ i i d
      letI := Etingof.reflFunctorMinus_modAt ρ₂ i i d
      Etingof.reflFunctorMinus_objAt ρ₁ i i d ≃ₗ[k]
        Etingof.reflFunctorMinus_objAt ρ₂ i i d)
    d
    (fun hii => absurd rfl hii)
    (fun _ =>
      Submodule.Quotient.equiv (LinearMap.range (ρ₁.sourceMap i))
        (LinearMap.range (ρ₂.sourceMap i))
        (Etingof.directSumMapEquiv (fun a : Etingof.ArrowsOutOf Q i => σ.equivAt a.fst))
        (Etingof.directSumMapEquiv_maps_sourceRange σ _ rfl _ rfl _
          (fun a v => Etingof.directSumMapEquiv_lof
            (fun a : Etingof.ArrowsOutOf Q i => σ.equivAt a.fst) a v)))

set_option maxHeartbeats 1600000 in
-- reason: v=i case unfolds two reflectionFunctorMinus instances + match resolution + Quotient.equiv
/-- Pointwise linear equivalence for the reflection functor map at each vertex.
At v ≠ i, composes through σ.equivAt. At v = i, uses the explicit-discriminant
`map_iso_equivAtAt_eq` (quotient equiv on cokernels). -/
private noncomputable def Etingof.reflectionFunctorMinus_map_iso_equivAt
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (σ : Etingof.QuiverRepresentation.Iso ρ₁ ρ₂)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : Q) :
    @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ₁) v ≃ₗ[k]
    @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ₂) v := by
  by_cases hv : v = i
  · rw [eq_comm] at hv; subst hv
    exact Etingof.reflectionFunctorMinus_map_iso_equivAtAt_eq hi σ (inst i i)
  · exact (Etingof.reflFunctorMinus_equivAt_ne hi ρ₁ v hv).trans
      ((σ.equivAt v).trans (Etingof.reflFunctorMinus_equivAt_ne hi ρ₂ v hv).symm)

/-- `equivAt_eq` cancels the `equivAt_eq.symm` in the definition of `mkQ`, leaving the
plain cokernel quotient map. This is a Decidable-discriminant-free restatement of the
`mkQ` definition. -/
private theorem Etingof.reflFunctorMinus_equivAt_eq_mkQ
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (d : DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    Etingof.reflFunctorMinus_equivAt_eq hi ρ (Etingof.reflFunctorMinus_mkQ hi ρ d) =
      Submodule.mkQ (LinearMap.range (ρ.sourceMap i)) d := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  unfold Etingof.reflFunctorMinus_mkQ
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- Heterogeneous congruence for applying a `LinearEquiv`: from type/instance equalities,
`HEq` of two `LinearEquiv` objects, and `HEq` of inputs, conclude `HEq` of the outputs. -/
private theorem Etingof.heq_linearEquiv_apply
    {k : Type*} [CommSemiring k]
    {α α' : Type u} {β β' : Type v}
    {acα : AddCommMonoid α} {acβ : AddCommMonoid β}
    {acα' : AddCommMonoid α'} {acβ' : AddCommMonoid β'}
    {mα : @Module k α _ acα} {mβ : @Module k β _ acβ}
    {mα' : @Module k α' _ acα'} {mβ' : @Module k β' _ acβ'}
    (hα : α = α') (hβ : β = β')
    (hacα : HEq acα acα') (hacβ : HEq acβ acβ')
    (hmα : HEq mα mα') (hmβ : HEq mβ mβ')
    {e : @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k) _ _ α β acα acβ mα mβ}
    {e' : @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k) _ _ α' β' acα' acβ' mα' mβ'}
    (he : HEq e e') {a : α} {a' : α'} (ha : HEq a a') :
    HEq (e a) (e' a') := by
  subst hα; subst hβ
  cases hacα; cases hacβ; cases hmα; cases hmβ; cases he; cases ha
  rfl

open Classical in
set_option maxHeartbeats 1600000 in
/-- Factorisation of the vertex-i map iso through the `equivAt_eq` cokernel charts: in
the cokernel coordinates, the map iso sends the class of `d` to the class of the
componentwise-transported `directSumMapEquiv d`. Proven by the `HEq` technique on the
shared `inst i i` discriminant (no consumer-side match). -/
private theorem Etingof.reflectionFunctorMinus_map_iso_equivAt_factor
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (σ : Etingof.QuiverRepresentation.Iso ρ₁ ρ₂)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (d : DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :
    letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
    letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    Etingof.reflFunctorMinus_equivAt_eq hi ρ₂
        (Etingof.reflectionFunctorMinus_map_iso_equivAt hi σ i
          (Etingof.reflFunctorMinus_mkQ hi ρ₁ d)) =
      Submodule.mkQ (LinearMap.range (ρ₂.sourceMap i))
        (Etingof.directSumMapEquiv (fun a : Etingof.ArrowsOutOf Q i => σ.equivAt a.fst) d) := by
  letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  have h_di : inst i i = .isTrue rfl := by
    cases inst i i with | isTrue _ => rfl | isFalse h => exact absurd rfl h
  -- Abbreviations for the cokernel charts and the descended map.
  set ψ₁ := ρ₁.sourceMap i with hψ₁def
  set ψ₂ := ρ₂.sourceMap i with hψ₂def
  set F := Etingof.directSumMapEquiv (fun a : Etingof.ArrowsOutOf Q i => σ.equivAt a.fst)
    with hFdef
  -- Step A: the map iso at `i`, in cokernel coordinates, is the descended quotient equiv.
  -- We prove this as an `HEq` of the underlying functions, then apply.
  have hmaps : Submodule.map F.toLinearMap (LinearMap.range ψ₁) = LinearMap.range ψ₂ := by
    rw [hψ₁def, hψ₂def, hFdef]
    exact Etingof.directSumMapEquiv_maps_sourceRange σ _ rfl _ rfl _
      (fun a v => Etingof.directSumMapEquiv_lof
        (fun a : Etingof.ArrowsOutOf Q i => σ.equivAt a.fst) a v)
  -- HEq: `equivAt_eq ρ` coerces to the identity on the cokernel (it is `refl` on isTrue).
  -- Identical to `hfwd` in `reflFunctorMinus_mapLinear_ne_eq`: rephrase via the explicit
  -- discriminant of `equivAtAt_eq`, then `rw [h_di]` reduces the `isTrue` branch.
  have heq_chart₁ : HEq (⇑(Etingof.reflFunctorMinus_equivAt_eq hi ρ₁))
      (id : ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) ⧸
        LinearMap.range (ρ₁.sourceMap i)) →
        ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) ⧸
          LinearMap.range (ρ₁.sourceMap i))) := by
    show HEq (⇑(Etingof.reflFunctorMinus_equivAtAt_eq ρ₁ (inst i i))) _
    rw [h_di]
    rfl
  have heq_chart₂ : HEq (⇑(Etingof.reflFunctorMinus_equivAt_eq hi ρ₂))
      (id : ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) ⧸
        LinearMap.range (ρ₂.sourceMap i)) →
        ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) ⧸
          LinearMap.range (ρ₂.sourceMap i))) := by
    show HEq (⇑(Etingof.reflFunctorMinus_equivAtAt_eq ρ₂ (inst i i))) _
    rw [h_di]
    rfl
  -- The map iso at `i`, in cokernel coordinates, is the descended quotient equiv. We package
  -- this as `HEq` of the *same* `map_iso_equivAtAt_eq` type family (so no fixed-type clash),
  -- reducing the `isTrue` branch via the explicit discriminant.
  have hmapobj : HEq (Etingof.reflectionFunctorMinus_map_iso_equivAt hi σ i)
      (Etingof.reflectionFunctorMinus_map_iso_equivAtAt_eq hi σ (Decidable.isTrue rfl)) := by
    unfold Etingof.reflectionFunctorMinus_map_iso_equivAt
    simp only [dite_true]
    congr 1
  -- At `isTrue`, the explicit-discriminant component *is* the descended quotient equiv.
  have hAtAt : (Etingof.reflectionFunctorMinus_map_iso_equivAtAt_eq hi σ
      (Decidable.isTrue (rfl : i = i))) =
      Submodule.Quotient.equiv (LinearMap.range ψ₁) (LinearMap.range ψ₂) F hmaps := rfl
  -- Object-level HEq of the map iso with the descended quotient equiv.
  have hobj : HEq (Etingof.reflectionFunctorMinus_map_iso_equivAt hi σ i)
      (Submodule.Quotient.equiv (LinearMap.range ψ₁) (LinearMap.range ψ₂) F hmaps) :=
    hmapobj.trans (heq_of_eq hAtAt)
  -- `mkQ ρ₁ d ≅ Submodule.mkQ ψ₁.range d`: the chart `equivAt_eq ρ₁` is HEq-id and sends
  -- `mkQ ρ₁ d` to `Submodule.mkQ d` (lemma `equivAt_eq_mkQ`).
  have hz : HEq (Etingof.reflFunctorMinus_mkQ hi ρ₁ d)
      (Submodule.mkQ (LinearMap.range ψ₁) d) := by
    have h1 : HEq (Etingof.reflFunctorMinus_equivAt_eq hi ρ₁
        (Etingof.reflFunctorMinus_mkQ hi ρ₁ d)) (Etingof.reflFunctorMinus_mkQ hi ρ₁ d) :=
      Etingof.heq_apply (Etingof.reflFunctorMinus_obj_eq hi ρ₁) rfl heq_chart₁
        (cast_heq (Etingof.reflFunctorMinus_obj_eq hi ρ₁) _).symm
        |>.trans (cast_heq (Etingof.reflFunctorMinus_obj_eq hi ρ₁) _)
    rw [Etingof.reflFunctorMinus_equivAt_eq_mkQ hi ρ₁] at h1
    exact h1.symm
  -- Instance HEqs at the discriminant (domain/codomain AddCommMonoid + Module).
  have hac₁ : HEq (Etingof.reflFunctorMinus_acmAt ρ₁ i i (inst i i))
      (Submodule.Quotient.addCommGroup
        (p := LinearMap.range (ρ₁.sourceMap i))).toAddCommMonoid := by
    generalize hgen : (inst i i) = di; rw [h_di] at hgen; subst hgen; rfl
  have hac₂ : HEq (Etingof.reflFunctorMinus_acmAt ρ₂ i i (inst i i))
      (Submodule.Quotient.addCommGroup
        (p := LinearMap.range (ρ₂.sourceMap i))).toAddCommMonoid := by
    generalize hgen : (inst i i) = di; rw [h_di] at hgen; subst hgen; rfl
  have hmo₁ : HEq (Etingof.reflFunctorMinus_modAt ρ₁ i i (inst i i))
      (Submodule.Quotient.module (LinearMap.range (ρ₁.sourceMap i))) := by
    generalize hgen : (inst i i) = di; rw [h_di] at hgen; subst hgen; rfl
  have hmo₂ : HEq (Etingof.reflFunctorMinus_modAt ρ₂ i i (inst i i))
      (Submodule.Quotient.module (LinearMap.range (ρ₂.sourceMap i))) := by
    generalize hgen : (inst i i) = di; rw [h_di] at hgen; subst hgen; rfl
  -- Apply the map iso (HEq to the quotient equiv) to the input (HEq to `mkQ d`).
  have hmapw : HEq (Etingof.reflectionFunctorMinus_map_iso_equivAt hi σ i
      (Etingof.reflFunctorMinus_mkQ hi ρ₁ d))
      (Submodule.Quotient.equiv (LinearMap.range ψ₁) (LinearMap.range ψ₂) F hmaps
        (Submodule.mkQ (LinearMap.range ψ₁) d)) :=
    Etingof.heq_linearEquiv_apply (Etingof.reflFunctorMinus_obj_eq hi ρ₁)
      (Etingof.reflFunctorMinus_obj_eq hi ρ₂) hac₁ hac₂ hmo₁ hmo₂ hobj hz
  -- `equivAt_eq ρ₂` is HEq-id, so it sends `m` to the quotient-equiv value (over `coker ψ₂`).
  have hfin : Etingof.reflFunctorMinus_equivAt_eq hi ρ₂
      (Etingof.reflectionFunctorMinus_map_iso_equivAt hi σ i
        (Etingof.reflFunctorMinus_mkQ hi ρ₁ d)) =
      Submodule.Quotient.equiv (LinearMap.range ψ₁) (LinearMap.range ψ₂) F hmaps
        (Submodule.mkQ (LinearMap.range ψ₁) d) := by
    have h := Etingof.heq_apply (Etingof.reflFunctorMinus_obj_eq hi ρ₂) rfl heq_chart₂ hmapw
    -- `h : HEq (equivAt_eq ρ₂ m) (id q)`; both sides live in `coker ψ₂`, so `eq_of_heq`.
    simpa using eq_of_heq h
  rw [hfin]
  -- `Quotient.equiv` of `mkQ d` is `mkQ (F d)`.
  rw [Submodule.Quotient.equiv_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
    Submodule.mkQ_apply]
  rfl

open Classical in
set_option maxHeartbeats 1600000 in
-- reason: unfolding reflFunctorMinus_map_iso_equivAt + reflFunctorMinus_mkQ + match reduction
/-- The vertex-i map iso, evaluated on a `mkQ` class, is the `mkQ` class of the
componentwise-transported representative. This is the descent compatibility of
`map_iso_equivAt i` with the canonical quotient map, avoiding any discriminant `match`
on the consumer side. -/
private theorem Etingof.reflectionFunctorMinus_map_iso_equivAt_mkQ
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (σ : Etingof.QuiverRepresentation.Iso ρ₁ ρ₂)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (d : DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :
    Etingof.reflectionFunctorMinus_map_iso_equivAt hi σ i
        (Etingof.reflFunctorMinus_mkQ hi ρ₁ d) =
      Etingof.reflFunctorMinus_mkQ hi ρ₂
        (Etingof.directSumMapEquiv (fun a : Etingof.ArrowsOutOf Q i => σ.equivAt a.fst) d) := by
  letI : DecidableEq (Etingof.ArrowsOutOf Q i) := Classical.decEq _
  letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  -- Both `map_iso_equivAt i` and `mkQ` are built from the same `inst i i` discriminant
  -- via `equivAt_eq`. Compose with `equivAt_eq ρ₂` (whose target cokernel type has no
  -- Decidable dependency) to land in a discriminant-free goal, provable by HEq.
  apply (Etingof.reflFunctorMinus_equivAt_eq hi ρ₂).injective
  rw [Etingof.reflFunctorMinus_equivAt_eq_mkQ hi ρ₂]
  exact Etingof.reflectionFunctorMinus_map_iso_equivAt_factor hi σ d

set_option maxHeartbeats 3200000 in
-- reason: unfolding reflFunctorMinus_map_iso_equivAt + reflectionFunctorMinus + match reduction
/-- Naturality of the reflection functor map iso.
Factored out to avoid timeout in the main @Iso.mk type-check. -/
private theorem Etingof.reflectionFunctorMinus_map_iso_naturality
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (σ : Etingof.QuiverRepresentation.Iso ρ₁ ρ₂)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    {a b : Q} (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b)
    (x : @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ₁) a) :
    Etingof.reflectionFunctorMinus_map_iso_equivAt hi σ b
      (@Etingof.QuiverRepresentation.mapLinear k Q _
        (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi ρ₁) a b e x) =
    @Etingof.QuiverRepresentation.mapLinear k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ₂) a b e
      (Etingof.reflectionFunctorMinus_map_iso_equivAt hi σ a x) := by
  have hi_sink := Etingof.isSource_reversedAtVertex_isSink hi
  by_cases ha : a = i
  · subst ha; exact ((hi_sink b).false e).elim
  · by_cases hb : b = i
    · rw [eq_comm] at hb; subst hb
      letI : DecidableEq (Etingof.ArrowsOutOf Q i) := Classical.decEq _
      -- Reduce the F⁻ map at (a ≠ i, b = i) on both sides to `mkQ ∘ lof`.
      rw [Etingof.reflFunctorMinus_mapLinear_ne_eq hi ρ₁ ha e x]
      rw [Etingof.reflFunctorMinus_mapLinear_ne_eq hi ρ₂ ha e]
      -- LHS map iso at i descends through `mkQ` (helper), and `directSumMapEquiv`
      -- on a `lof` injection is `lof` of the transported representative.
      rw [Etingof.reflectionFunctorMinus_map_iso_equivAt_mkQ hi σ]
      rw [Etingof.directSumMapEquiv_lof (fun a : Etingof.ArrowsOutOf Q i => σ.equivAt a.fst)]
      -- Remaining: identify the two transported representatives in the `a`-component.
      congr 1
      -- `σ.equivAt a ∘ equivAt_ne ρ₁ a = equivAt_ne ρ₂ a ∘ (map iso at a ≠ i)`.
      simp only [Etingof.reflectionFunctorMinus_map_iso_equivAt, dif_neg ha,
        LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    · -- a ≠ i, b ≠ i: both sides reduce through equivAt_ne
      -- Unfold equivAt to see the .trans composition
      simp only [Etingof.reflectionFunctorMinus_map_iso_equivAt, dif_neg ha, dif_neg hb,
        LinearEquiv.trans_apply]
      -- Now both sides have equivAt_ne + σ.equivAt + equivAt_ne.symm pattern
      -- Use mapLinear_ne_ne to reduce F⁻ mapLinear to original ρ mapLinear
      rw [Etingof.reflFunctorMinus_mapLinear_ne_ne hi ρ₁ ha hb e x]
      -- LHS: (equivAt_ne ρ₂ b hb).symm (σ.equivAt b (ρ₁.mapLinear (reversedArrow ..) ..))
      -- RHS: (F⁻(ρ₂).mapLinear e) ((equivAt_ne ρ₂ a ha).symm (σ.equivAt a (..)))
      rw [LinearEquiv.symm_apply_eq]
      -- Now RHS has equivAt_ne ρ₂ b hb applied to F⁻(ρ₂).mapLinear
      rw [Etingof.reflFunctorMinus_mapLinear_ne_ne hi ρ₂ ha hb e]
      rw [LinearEquiv.apply_symm_apply]
      exact σ.naturality (Etingof.reversedArrow_ne_ne ha hb e)
        ((Etingof.reflFunctorMinus_equivAt_ne hi ρ₁ a ha) x)

/-- Functoriality of F⁻ᵢ: an isomorphism σ : ρ₁ ≅ ρ₂ induces an isomorphism
F⁻ᵢ(ρ₁) ≅ F⁻ᵢ(ρ₂) on the reversed quiver Q̄ᵢ.

At vertices v ≠ i, the equivalence transports through σ.equivAt v.
At vertex i, both are cokernels; σ induces a compatible map on direct sums
that descends to an equivalence on quotients.

(Functoriality of the reflection functor, implicit in Etingof Definition 6.6.4) -/
noncomputable def Etingof.reflectionFunctorMinus_map_iso
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [instQ : Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (σ : Etingof.QuiverRepresentation.Iso ρ₁ ρ₂)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    Nonempty (@Etingof.QuiverRepresentation.Iso k (inferInstanceAs (CommSemiring k))
      Q (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ₁)
      (Etingof.reflectionFunctorMinus Q i hi ρ₂)) :=
  ⟨@Etingof.QuiverRepresentation.Iso.mk k _ Q
    (Etingof.reversedAtVertex Q i)
    (Etingof.reflectionFunctorMinus Q i hi ρ₁)
    (Etingof.reflectionFunctorMinus Q i hi ρ₂)
    (Etingof.reflectionFunctorMinus_map_iso_equivAt hi σ)
    (Etingof.reflectionFunctorMinus_map_iso_naturality hi σ)⟩

end MapIso

section Helpers

/-- For an arrow `i →_{Q̄ᵢ} j` in the reversed quiver (with i a sink), the target vertex
j ≠ i. This is because i is a source in Q̄ᵢ. -/
theorem Etingof.arrowsOutReversed_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (a : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) : a.fst ≠ i := by
  obtain ⟨j, e⟩ := a
  change Etingof.ReversedAtVertexHom Q i i j at e
  by_cases hj : j = i
  · rw [Etingof.ReversedAtVertexHom_eq_eq rfl hj] at e
    rw [hj] at e; exact ((hi i).false e).elim
  · exact hj

/-- The type equality `ReversedAtVertexHom Q i i j = (j ⟶ i)` as a computable
definition (not a theorem), so that `cast`/`Eq.mpr` with it reduces properly. -/
private def Etingof.ReversedAtVertexHom_at_first_def
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i j : Q} (hj : j ≠ i) :
    Etingof.ReversedAtVertexHom Q i i j = (j ⟶ i) := by
  unfold Etingof.ReversedAtVertexHom
  cases inst i i with
  | isFalse h => exact absurd rfl h
  | isTrue _ =>
    cases inst j i with
    | isTrue h => exact absurd h hj
    | isFalse _ => rfl

/-- Extract the original arrow j →_Q i from a reversed arrow i →_{Q̄ᵢ} j.
Defined via `reversedArrow_eq_ne` to ensure definitional compatibility with the
API lemmas (e.g., `reflFunctorPlus_mapLinear_eq_ne`). -/
def Etingof.arrowsOutReversed_origArrow
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (a : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) : a.fst ⟶ i :=
  Etingof.reversedArrow_eq_ne (Etingof.arrowsOutReversed_ne hi a) a.snd

/-- Map arrows into i in Q to arrows out of i in Q̄ᵢ.
Since i is a sink (no arrows out), any arrow j → i in Q gives a reversed
arrow i →_{Q̄ᵢ} j. Uses `cast` with computable type equality. -/
def Etingof.arrowsInto_to_arrowsOutReversed
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i :=
  have hne : b.fst ≠ i := fun h =>
    (hi i).false (cast (congrArg (· ⟶ i) h) b.snd)
  ⟨b.fst, cast (Etingof.ReversedAtVertexHom_at_first_def hne).symm b.snd⟩

set_option maxHeartbeats 800000 in
-- reason: unfolding reversedArrow_eq_ne + ReversedAtVertexHom_at_first_def + proof irrelevance
/-- `reversedArrow_eq_ne` agrees with `cast` using the computable type equality. -/
private theorem Etingof.reversedArrow_eq_ne_eq_cast_def
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i j : Q} (hj : j ≠ i)
    (e : Etingof.ReversedAtVertexHom Q i i j) :
    Etingof.reversedArrow_eq_ne hj e =
    cast (Etingof.ReversedAtVertexHom_at_first_def hj) e :=
  -- `reversedArrow_eq_ne hj e` is now *defined* as `cast (ReversedAtVertexHom_eq_ne rfl hj) e`;
  -- both sides are `cast _ e`, equal by proof irrelevance of the type equalities (via `HEq`).
  eq_of_heq ((cast_heq (Etingof.ReversedAtVertexHom_eq_ne rfl hj) e).trans
    (cast_heq (Etingof.ReversedAtVertexHom_at_first_def hj) e).symm)

/-- Round-trip: extracting the original arrow from a converted ArrowsInto
gives back the original arrow. -/
theorem Etingof.origArrow_arrowsInto_to_arrowsOutReversed
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    Etingof.arrowsOutReversed_origArrow hi
      (Etingof.arrowsInto_to_arrowsOutReversed hi b) = b.2 := by
  obtain ⟨j, e⟩ := b
  have hji : j ≠ i := by intro heq; rw [heq] at e; exact (hi i).false e
  simp only [arrowsOutReversed_origArrow, arrowsInto_to_arrowsOutReversed]
  rw [reversedArrow_eq_ne_eq_cast_def]
  simp [cast_cast]

/-- The component of `arrowsInto_to_arrowsOutReversed` at j gives the original arrow j ⟶ i. -/
theorem Etingof.arrowsInto_to_arrowsOutReversed_fst
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    (Etingof.arrowsInto_to_arrowsOutReversed hi b).fst = b.fst := by
  simp [arrowsInto_to_arrowsOutReversed]

/-- Reverse round-trip: converting an arrow from ArrowsOutOf instR i to ArrowsInto
and back gives the original element. -/
theorem Etingof.arrowsInto_to_arrowsOutReversed_roundtrip
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (x : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) :
    Etingof.arrowsInto_to_arrowsOutReversed hi
      ⟨x.fst, Etingof.arrowsOutReversed_origArrow hi x⟩ = x := by
  obtain ⟨j, e⟩ := x
  have hji : j ≠ i := Etingof.arrowsOutReversed_ne hi ⟨j, e⟩
  refine Sigma.ext rfl ?_
  simp only [arrowsInto_to_arrowsOutReversed, arrowsOutReversed_origArrow]
  rw [reversedArrow_eq_ne_eq_cast_def]
  exact heq_of_eq (by simp [cast_cast])

/-- Equivalence between ArrowsOutOf in the reversed quiver and ArrowsInto in the original.
This is the key reindexing used in the round-trip proof. -/
def Etingof.arrowReindexEquiv
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i) :
    @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i ≃
    Etingof.ArrowsInto Q i where
  toFun x := ⟨x.fst, Etingof.arrowsOutReversed_origArrow hi x⟩
  invFun b := Etingof.arrowsInto_to_arrowsOutReversed hi b
  left_inv x := Etingof.arrowsInto_to_arrowsOutReversed_roundtrip hi x
  right_inv b := by
    refine Sigma.ext (Etingof.arrowsInto_to_arrowsOutReversed_fst hi b) ?_
    exact heq_of_eq (Etingof.origArrow_arrowsInto_to_arrowsOutReversed hi b)

/-- The reindexed map Φ : ⊕_{ArrowsOutOf Q̄ᵢ i} F⁺(V).obj a.fst →ₗ ρ.obj i
is surjective when sinkMap is surjective.

Φ is essentially sinkMap after reindexing through the
ArrowsInto ↔ ArrowsOutOf correspondence and equivAt_ne.

The Φ parameter must be `DirectSum.toModule k _ _ Φ_component` where
Φ_component a = mapLinear(origArrow a) ∘ equivAt_ne. We take it as a parameter
to avoid type class synthesis issues with multiple quiver instances. -/
theorem Etingof.sinkMap_reindex_surj
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (_hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Finite (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (hsurj : Function.Surjective (ρ.sinkMap i))
    {M : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i → Type*}
    [∀ a, AddCommMonoid (M a)] [∀ a, Module k (M a)]
    (Φ : DirectSum (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) M →ₗ[k] ρ.obj i)
    (hΦ_basic : ∀ (b : @Etingof.ArrowsInto Q inst i) (v : ρ.obj b.fst),
      ∃ z, Φ z = ρ.mapLinear b.2 v) :
    Function.Surjective Φ := by
  classical
  haveI := Fintype.ofFinite (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)
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
theorem Etingof.Φ_comp_source_eq_zero
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
  -- Normalize: fold reversedArrow_eq_ne back to arrowsOutReversed_origArrow
  change ∑ x : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i,
    ρ.mapLinear (Etingof.arrowsOutReversed_origArrow hi x)
      (DirectSum.component k (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1)
        ⟨x.fst, Etingof.arrowsOutReversed_origArrow hi x⟩
        ((ρ.sinkMap i).ker.subtype (Etingof.reflFunctorPlus_equivAt_eq hi ρ w))) = 0
  -- Goal: ∑ x, mapLinear(origArrow x)(component ⟨x.fst, origArrow x⟩ y) = 0
  -- Strategy: show sum = sinkMap(y) = 0 since y ∈ ker(sinkMap).
  classical
  haveI : Fintype (Etingof.ArrowsInto Q i) :=
    Fintype.ofEquiv _ (Etingof.arrowReindexEquiv hi)
  set y := (ρ.sinkMap i).ker.subtype (Etingof.reflFunctorPlus_equivAt_eq hi ρ w) with hy_def
  -- Express the sum as ∑ x, g(equiv(x)) where g b = mapLinear b.2 (component b y)
  let g : Etingof.ArrowsInto Q i → ρ.obj i :=
    fun b => ρ.mapLinear b.2 (DirectSum.component k (Etingof.ArrowsInto Q i)
      (fun a => ρ.obj a.1) b y)
  change ∑ x, g (Etingof.arrowReindexEquiv hi x) = 0
  -- Step 1: Reindex using bijection
  rw [(Etingof.arrowReindexEquiv hi).bijective.sum_comp g]
  -- Step 2: Show ∑ b, g b = sinkMap y = 0
  change ∑ b : Etingof.ArrowsInto Q i,
    ρ.mapLinear b.2 (DirectSum.component k (Etingof.ArrowsInto Q i)
      (fun a => ρ.obj a.1) b y) = 0
  -- Decompose: sinkMap y = ∑ b, mapLinear b.2 (component b y)
  rw [show ∑ b : Etingof.ArrowsInto Q i,
      ρ.mapLinear b.2 (DirectSum.component k (Etingof.ArrowsInto Q i)
        (fun a => ρ.obj a.1) b y) = (ρ.sinkMap i) y from by
    symm
    delta Etingof.QuiverRepresentation.sinkMap
    change (DirectSum.toModule k (Etingof.ArrowsInto Q i) (ρ.obj i)
      (fun a => ρ.mapLinear a.2)) y = _
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero, Finset.sum_const_zero]
    | of i x =>
      erw [DirectSum.toModule_lof]
      rw [Finset.sum_eq_single i]
      · erw [DirectSum.component.lof_self]
      · intro b _ hb
        erw [DirectSum.component.of]; rw [dif_neg (Ne.symm hb), map_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    | add x y hx hy =>
      simp only [map_add, hx, hy, Finset.sum_add_distrib]]
  -- Step 3: sinkMap y = 0 (kernel property)
  exact (Etingof.reflFunctorPlus_equivAt_eq hi ρ w).property

set_option maxHeartbeats 400000 in
-- reason: finrank arithmetic with rank-nullity for both ψ and Φ
/-- If ψ.range ≤ ker Φ, Φ is surjective, ψ is injective, and
finrank(source ψ) + finrank(target Φ) = finrank(source Φ), then ψ.range = ker Φ.
This is the "first isomorphism theorem" applied to an exact sequence. -/
theorem Etingof.exact_of_dim
    {k : Type*} [Field k]
    {A B C : Type*}
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [AddCommGroup B] [Module k B] [FiniteDimensional k B]
    [AddCommGroup C] [Module k C] [FiniteDimensional k C]
    {ψ' : A →ₗ[k] B} {Φ' : B →ₗ[k] C}
    (hfwd : ψ'.range ≤ Φ'.ker)
    (hΦ_surj : Function.Surjective Φ')
    (hψ_inj : Function.Injective ψ')
    (hdim : Module.finrank k A + Module.finrank k C = Module.finrank k B) :
    ψ'.range = Φ'.ker := by
  apply Submodule.eq_of_le_of_finrank_eq hfwd
  -- finrank(ψ'.range) = finrank(A) since ψ' is injective
  have hr : Module.finrank k ↥ψ'.range = Module.finrank k A :=
    LinearMap.finrank_range_of_inj hψ_inj
  -- finrank(Φ'.ker) + finrank(C) = finrank(B)
  have hk : Module.finrank k ↥Φ'.ker + Module.finrank k C = Module.finrank k B := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ'
    rw [LinearMap.range_eq_top.mpr hΦ_surj, finrank_top] at h1
    omega
  -- Combine: finrank(A) = finrank(B) - finrank(C) = finrank(Φ'.ker)
  omega

end Helpers

section ReversedArrowCasts

/-- `reversedArrow_ne_ne ha hb` is a cast through `ReversedAtVertexHom_ne_ne`. -/
theorem Etingof.reversedArrow_ne_ne_is_cast
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i a b : Q} (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b) :
    Etingof.reversedArrow_ne_ne ha hb e =
    cast (Etingof.ReversedAtVertexHom_ne_ne ha hb) e :=
  -- `reversedArrow_ne_ne` is now *defined* as this cast.
  rfl

set_option maxHeartbeats 1600000 in
-- reason: double-reversal cast simplification through Decidable.casesOn
theorem Etingof.reversedArrow_ne_ne_twice
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} {a b : Q} (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q inst a b) :
    @Etingof.reversedArrow_ne_ne Q inst_dec inst i a b ha hb
      (@Etingof.reversedArrow_ne_ne Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i a b ha hb
        ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e)) = e := by
  -- Convert each reversedArrow_ne_ne to cast via is_cast, then compose via HEq
  have h1 : ∀ (y : @Quiver.Hom Q (@Etingof.reversedAtVertex Q _ inst i) a b),
      HEq (@Etingof.reversedArrow_ne_ne Q inst_dec inst i a b ha hb y) y := by
    intro y; rw [Etingof.reversedArrow_ne_ne_is_cast]; exact cast_heq _ _
  have h2 : ∀ (z : @Quiver.Hom Q
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i) a b),
      HEq (@Etingof.reversedArrow_ne_ne Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i a b ha hb z) z := by
    intro z
    rw [@Etingof.reversedArrow_ne_ne_is_cast Q inst_dec
      (@Etingof.reversedAtVertex Q _ inst i) i a b ha hb z]
    exact cast_heq _ _
  -- Use eqRec_heq_self with explicit motive using field projection (avoids instance synthesis)
  have h3 : HEq ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e) e :=
    eqRec_heq_self (motive := fun q _ => q.Hom a b) e
      (@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm
  exact eq_of_heq ((h1 _).trans ((h2 _).trans h3))


/-- `reversedArrow_eq_ne hb` is a cast through `ReversedAtVertexHom_eq_ne`. -/
theorem Etingof.reversedArrow_eq_ne_is_cast
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i b : Q} (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) i b) :
    Etingof.reversedArrow_eq_ne hb e =
    cast (Etingof.ReversedAtVertexHom_eq_ne (i := i) rfl hb) e :=
  -- `reversedArrow_eq_ne` is now *defined* as this cast.
  rfl

/-- `reversedArrow_ne_eq ha` is a cast through `ReversedAtVertexHom_ne_eq`. -/
theorem Etingof.reversedArrow_ne_eq_is_cast
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i a : Q} (ha : a ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a i) :
    Etingof.reversedArrow_ne_eq ha e =
    cast (Etingof.ReversedAtVertexHom_ne_eq (i := i) ha rfl) e :=
  -- `reversedArrow_ne_eq` is now *defined* as this cast.
  rfl

set_option maxHeartbeats 1600000 in
-- reason: double-reversal cast simplification through eq_ne + ne_eq path
/-- Double reversal for the (a ≠ i, b = i) case: reversing at i twice recovers the original arrow.
This mirrors `reversedArrow_ne_ne_twice` but goes through `reversedArrow_ne_eq` then
`reversedArrow_eq_ne` instead of `reversedArrow_ne_ne` twice. -/
theorem Etingof.reversedArrow_ne_eq_eq_ne_twice
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    {a : Q} (ha : a ≠ i)
    (e : @Quiver.Hom Q inst a i) :
    Etingof.arrowsOutReversed_origArrow hi
      ⟨a, @Etingof.reversedArrow_ne_eq Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i a ha
        ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e)⟩ = e := by
  simp only [arrowsOutReversed_origArrow]
  apply eq_of_heq
  -- Step 1: reversedArrow_eq_ne is HEq to identity
  have h1 : ∀ (y : @Quiver.Hom Q (@Etingof.reversedAtVertex Q _ inst i) i a),
      HEq (@Etingof.reversedArrow_eq_ne Q inst_dec inst i a
        (Etingof.arrowsOutReversed_ne hi ⟨a, y⟩) y) y := by
    intro y
    rw [Etingof.reversedArrow_eq_ne_is_cast]
    exact cast_heq _ _
  -- Step 2: reversedArrow_ne_eq on instR is HEq to identity
  have h2 : ∀ (z : @Quiver.Hom Q
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i) a i),
      HEq (@Etingof.reversedArrow_ne_eq Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i a ha z) z := by
    intro z
    rw [@Etingof.reversedArrow_ne_eq_is_cast Q inst_dec
      (@Etingof.reversedAtVertex Q _ inst i) i a ha z]
    exact cast_heq _ _
  -- Step 3: transport is HEq to identity
  have h3 : HEq ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e) e :=
    eqRec_heq_self (motive := fun q _ => q.Hom a i) e
      (@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm
  exact (h1 _).trans ((h2 _).trans h3)

set_option maxHeartbeats 1600000 in
-- reason: double-reversal cast simplification through eq_ne + ne_eq path (source direction)
/-- Double reversal for the (a = i, b ≠ i) case: reversing at i twice recovers the original arrow.
This mirrors `reversedArrow_ne_eq_eq_ne_twice` but goes through `reversedArrow_eq_ne` then
`reversedArrow_ne_eq` (source direction: arrow from i outward). -/
theorem Etingof.reversedArrow_eq_ne_ne_eq_twice
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (_hi : Etingof.IsSource Q i)
    {b : Q} (hb : b ≠ i)
    (e : @Quiver.Hom Q inst i b) :
    @Etingof.reversedArrow_ne_eq Q inst_dec inst i b hb
      (@Etingof.reversedArrow_eq_ne Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i b hb
        ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e)) = e := by
  apply eq_of_heq
  -- Step 1: reversedArrow_ne_eq is HEq to identity
  have h1 : ∀ (y : @Quiver.Hom Q (@Etingof.reversedAtVertex Q _ inst i) b i),
      HEq (@Etingof.reversedArrow_ne_eq Q inst_dec inst i b hb y) y := by
    intro y
    rw [Etingof.reversedArrow_ne_eq_is_cast]
    exact cast_heq _ _
  -- Step 2: reversedArrow_eq_ne on instR is HEq to identity
  have h2 : ∀ (z : @Quiver.Hom Q
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i) i b),
      HEq (@Etingof.reversedArrow_eq_ne Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i b hb z) z := by
    intro z
    rw [@Etingof.reversedArrow_eq_ne_is_cast Q inst_dec
      (@Etingof.reversedAtVertex Q _ inst i) i b hb z]
    exact cast_heq _ _
  -- Step 3: transport is HEq to identity
  have h3 : HEq ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e) e :=
    eqRec_heq_self (motive := fun q _ => q.Hom i b) e
      (@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm
  exact (h1 _).trans ((h2 _).trans h3)

end ReversedArrowCasts
