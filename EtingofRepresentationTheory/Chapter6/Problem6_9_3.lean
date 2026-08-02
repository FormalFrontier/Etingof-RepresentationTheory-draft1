import Mathlib
import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Infrastructure.QuiverCompositionSeries

/-!
# Problem 6.9.3: Indecomposable representations of a Dynkin quiver

> Let `V_α` be the indecomposable representation of a Dynkin quiver `Q` which
> corresponds to a positive root `α`. For instance, if `αᵢ` is a simple root,
> then `V_{αᵢ}` has a `1`-dimensional space at `i` and is `0` everywhere else.
>
> **(a)** Show that if `i` is a **source**, then `Ext¹(V, V_{αᵢ}) = 0` for any
> representation `V` of `Q`, and if `i` is a **sink**, then `Ext¹(V_{αᵢ}, V) = 0`.
>
> **(b)** Given an orientation of the quiver, find a **Jordan–Hölder series** of
> `V_α` for that orientation.

## Computing Ext¹

For quiver representations, `Ext¹(V, W)` is computed by the standard two-term
complex
`⨁ᵢ Hom(Vᵢ, Wᵢ) → ⨁_{a : i→j} Hom(Vᵢ, Wⱼ)`,
`d(f)_a = W_a ∘ f_i - f_j ∘ V_a`, as `Ext¹(V, W) = coker d`. Hence
`Ext¹(V, W) = 0` iff `d` is surjective, which we take as the definition of
Ext-vanishing (`Ext1Vanishes`). The simple representation `S_i`
(`= V_{αᵢ}`) is `k` at vertex `i`, `0` elsewhere, with all arrow maps zero.
-/

namespace Etingof.Problem6_9_3

open Module

variable {k Q : Type*} [Field k] [Quiver Q]

/-- Over a field, each `AddCommMonoid` module carrier is an `AddCommGroup`
(negation is `(-1) • ·`). The `QuiverRepresentation.obj` carriers bundle only
`AddCommMonoid`, so this supplies the group structure needed to subtract linear
maps in the Ext differential. -/
@[reducible]
noncomputable def acg {M : Type*} [inst : AddCommMonoid M] [Module k M] :
    AddCommGroup M :=
  Module.addCommMonoidToAddCommGroup k

/-- The simple representation `S_i = V_{αᵢ}`: a `1`-dimensional space at vertex
`i`, `0` elsewhere, with all arrow maps zero. The vertex object is
`Fin (if v = i then 1 else 0) → k` (dimension `1` at `i`, `0` otherwise), which
avoids the type-level `if`/instance diamond by branching only on the
dimension.

This is `Etingof.vertexSimple` from
`Infrastructure/QuiverCompositionSeries.lean`, where the composition-series
machinery used in part (b) lives. -/
abbrev simpleRep [DecidableEq Q] (i : Q) : QuiverRepresentation k Q :=
  Etingof.vertexSimple i

/-- A vertex `i` is a **source** if no arrows point *into* it. -/
def IsSource (i : Q) : Prop := ∀ j, IsEmpty (j ⟶ i)

/-- A vertex `i` is a **sink** if no arrows point *out of* it. -/
def IsSink (i : Q) : Prop := ∀ j, IsEmpty (i ⟶ j)

/-- The Ext differential `d : ⨁ᵢ Hom(Vᵢ, Wᵢ) → ⨁_{a:i→j} Hom(Vᵢ, Wⱼ)`,
`d(f)_a = W_a ∘ f_i - f_j ∘ V_a`. Its cokernel is `Ext¹(V, W)`. -/
noncomputable def extDiff (V W : QuiverRepresentation k Q) :
    (∀ i, V.obj i →ₗ[k] W.obj i) → (∀ p : (Σ i j, (i ⟶ j)), V.obj p.1 →ₗ[k] W.obj p.2.1) :=
  fun f p =>
    -- Subtracting the two linear maps needs `AddCommGroup (W.obj p.2.1)` on the
    -- shared codomain. Supply it for this specific carrier: a `letI` of Pi type
    -- `∀ v, AddCommGroup (W.obj v)` is not a class-headed instance and so is not
    -- used by instance synthesis for the concrete `W.obj p.2.1`.
    letI : AddCommGroup (W.obj p.2.1) := acg (k := k)
    W.mapLinear p.2.2 ∘ₗ f p.1 - f p.2.1 ∘ₗ V.mapLinear p.2.2

/-- `Ext¹(V, W) = 0`: the Ext differential is surjective (its cokernel vanishes). -/
def Ext1Vanishes (V W : QuiverRepresentation k Q) : Prop :=
  Function.Surjective (extDiff V W)

/-! ## Part (a): Ext-vanishing at sources and sinks -/

/-- **(a)** If `i` is a **source**, then `Ext¹(V, S_i) = 0` for every
representation `V`. -/
theorem ext1_source [DecidableEq Q] (i : Q) (hi : IsSource i)
    (V : QuiverRepresentation k Q) : Ext1Vanishes V (simpleRep i) := by
  -- For a source `i`, every arrow `a ⟶ b` has `b ≠ i`, so its target component
  -- `(S_i)_b = Fin 0 → k` is a subsingleton. Hence the entire target of the
  -- differential is trivial and any element (e.g. `d 0`) equals the given `g`.
  intro g
  refine ⟨0, funext fun p => ?_⟩
  have hbne : p.2.1 ≠ i := by
    intro h
    exact (hi p.1).elim (h ▸ p.2.2)
  have hsub : Subsingleton ((simpleRep (k := k) i).obj p.2.1) := by
    change Subsingleton (Fin (if p.2.1 = i then 1 else 0) → k)
    rw [if_neg hbne]
    exact ⟨fun a b => funext fun x => x.elim0⟩
  exact LinearMap.ext fun x => hsub.elim _ _

/-- **(a)** If `i` is a **sink**, then `Ext¹(S_i, V) = 0` for every
representation `V`. -/
theorem ext1_sink [DecidableEq Q] (i : Q) (hi : IsSink i)
    (V : QuiverRepresentation k Q) : Ext1Vanishes (simpleRep i) V := by
  -- Dually, for a sink `i` every arrow `a ⟶ b` has `a ≠ i`, so its source
  -- component `(S_i)_a = Fin 0 → k` is a subsingleton. A linear map out of a
  -- subsingleton domain is the zero map, so the whole target of the differential
  -- is trivial and `d 0` equals the given `g`.
  intro g
  refine ⟨0, funext fun p => ?_⟩
  have hane : p.1 ≠ i := by
    intro h
    exact (hi p.2.1).elim (h ▸ p.2.2)
  have hsub : Subsingleton ((simpleRep (k := k) i).obj p.1) := by
    change Subsingleton (Fin (if p.1 = i then 1 else 0) → k)
    rw [if_neg hane]
    exact ⟨fun a b => funext fun x => x.elim0⟩
  exact LinearMap.ext fun x => by rw [hsub.elim x 0, map_zero, map_zero]

/-! ## Part (b): Jordan–Hölder series of `V_α` -/

/-- The **dimension vector** of a quiver representation (`Module.finrank` is
defined over the bundled `AddCommMonoid` carriers). -/
noncomputable def dimVec (V : QuiverRepresentation k Q) (i : Q) : ℕ :=
  finrank k (V.obj i)

/-- A basis of every vertex space computes the dimension vector. -/
theorem dimVec_eq_of_basis {Vα : QuiverRepresentation k Q} {α : Q → ℕ}
    (basis : ∀ v, Basis (Fin (α v)) k (Vα.obj v)) (v : Q) : dimVec Vα v = α v := by
  rw [dimVec, Module.finrank_eq_card_basis (basis v), Fintype.card_fin]

/-- **(b)** *Given an orientation of the quiver, find a Jordan–Hölder series of `V_α` for that
orientation.*

An orientation enters through an enumeration `order` of the vertices along which every arrow
decreases — a topological sort, which exists exactly when the quiver has no oriented cycle,
in particular for every orientation of a Dynkin diagram
(`Etingof.exists_topoSort`). Relative to such an enumeration, **any** representation `Vα`
whose vertex spaces are finite-dimensional (here: given by bases) has a genuine
Jordan–Hölder series
`0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ V_N = Vα`
of subrepresentations whose successive subquotients are the vertex simples `S i`
(`Etingof.QuiverRepCompositionSeries`, whose steps are `Etingof.IsSimpleStep` and therefore
admit no intermediate subrepresentation), with `S i` occurring exactly `dim (Vα)ᵢ = α i`
times.

The filtration itself is read off from the orientation: it fills the vertex spaces up one
basis vector at a time, in the order given by `order`. The multiset of factors is
orientation-independent; the order in which they occur is not.

For the indecomposable `V_α` attached to a positive root of a Dynkin quiver, see
`Etingof.Problem6_9_3.exists_compositionSeries_of_positiveRoot` in
`Chapter6/Problem6_9_3_JordanHolder.lean`. -/
theorem exists_jordanHolderSeries [DecidableEq Q] (Vα : QuiverRepresentation k Q)
    (n : ℕ) (order : Q ≃ Fin n)
    (horder : ∀ {v w : Q}, (v ⟶ w) → (order w : ℕ) < (order v : ℕ))
    (α : Q → ℕ) (basis : ∀ v, Basis (Fin (α v)) k (Vα.obj v)) :
    ∃ s : Etingof.QuiverRepCompositionSeries Vα,
      s.length = ∑ l : Fin n, α (order.symm l) ∧ ∀ i, s.mult i = dimVec Vα i := by
  obtain ⟨s, hlen, hmult⟩ :=
    Etingof.exists_compositionSeries Vα n order horder α basis
  exact ⟨s, hlen, fun i => (hmult i).trans (dimVec_eq_of_basis basis i).symm⟩

end Etingof.Problem6_9_3
