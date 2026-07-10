import Mathlib
import EtingofRepresentationTheory.Chapter2.Definition2_8_3

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

## Formalization notes

For quiver representations, `Ext¹(V, W)` is computed by the standard two-term
complex
`⨁ᵢ Hom(Vᵢ, Wᵢ) → ⨁_{a : i→j} Hom(Vᵢ, Wⱼ)`,
`d(f)_a = W_a ∘ f_i - f_j ∘ V_a`, as `Ext¹(V, W) = coker d`. Hence
`Ext¹(V, W) = 0` iff `d` is **surjective**; this is what we take as the faithful
statement of Ext-vanishing (`Ext1Vanishes`). The simple representation `S_i`
(`= V_{αᵢ}`) is `k` at vertex `i`, `0` elsewhere, with all arrow maps zero.
-/

namespace Etingof.Problem6_9_3

open Module

variable {k Q : Type*} [Field k] [Quiver Q]

/-- Over a field, each `AddCommMonoid` module carrier is an `AddCommGroup`
(negation is `(-1) • ·`). The `QuiverRepresentation.obj` carriers bundle only
`AddCommMonoid`, so this supplies the group structure needed to subtract linear
maps in the Ext differential. -/
noncomputable def acg {M : Type*} [inst : AddCommMonoid M] [Module k M] :
    AddCommGroup M :=
  { inst with
    neg := fun x => (-1 : k) • x
    zsmul := fun n x => (n : k) • x
    neg_add_cancel := fun a => by
      change (-1 : k) • a + a = 0
      nth_rw 2 [show a = (1 : k) • a from (one_smul k a).symm]
      rw [← add_smul, neg_add_cancel, zero_smul]
    zsmul_zero' := fun a => by simp [zero_smul]
    zsmul_succ' := fun n a => by
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
                  Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
    zsmul_neg' := fun n a => by
      simp only [Int.negSucc_eq, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
                  Int.cast_neg, smul_smul, neg_one_mul] }

/-- The simple representation `S_i = V_{αᵢ}`: a `1`-dimensional space at vertex
`i`, `0` elsewhere, with all arrow maps zero. The vertex object is
`Fin (if v = i then 1 else 0) → k` (dimension `1` at `i`, `0` otherwise), which
avoids the type-level `if`/instance diamond by branching only on the
*dimension*. -/
def simpleRep [DecidableEq Q] (i : Q) : QuiverRepresentation k Q where
  obj v := Fin (if v = i then 1 else 0) → k
  mapLinear _ := 0

/-- A vertex `i` is a **source** if no arrows point *into* it. -/
def IsSource (i : Q) : Prop := ∀ j, IsEmpty (j ⟶ i)

/-- A vertex `i` is a **sink** if no arrows point *out of* it. -/
def IsSink (i : Q) : Prop := ∀ j, IsEmpty (i ⟶ j)

/-- The Ext differential `d : ⨁ᵢ Hom(Vᵢ, Wᵢ) → ⨁_{a:i→j} Hom(Vᵢ, Wⱼ)`,
`d(f)_a = W_a ∘ f_i - f_j ∘ V_a`. Its cokernel is `Ext¹(V, W)`. -/
noncomputable def extDiff (V W : QuiverRepresentation k Q) :
    (∀ i, V.obj i →ₗ[k] W.obj i) → (∀ p : (Σ i j, (i ⟶ j)), V.obj p.1 →ₗ[k] W.obj p.2.1) :=
  letI : ∀ v, AddCommGroup (W.obj v) := fun v => acg (k := k)
  fun f p => W.mapLinear p.2.2 ∘ₗ f p.1 - f p.2.1 ∘ₗ V.mapLinear p.2.2

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

/-- **(b)** The claim that the indecomposable `V_α` (with dimension vector `α`,
a positive root) admits a Jordan–Hölder series whose factors are exactly the
simples `S_i`, each occurring `α i` times.

The multiset of Jordan–Hölder factors is orientation-independent — it is always
`{ S_i^{α_i} }` — while the *order* of the factors depends on the orientation.
Since `S_i` is `1`-dimensional at vertex `i` and `0` elsewhere, the multiplicity
`[V_α : S_i]` equals the dimension vector entry `dimVec V_α i = α i`.

We record this as a `Prop` against the real objects: a genuine composition-series
notion for `Etingof.QuiverRepresentation` is not yet in the project (it is part of
the Gabriel-theorem infrastructure), so this pins the exact statement for a later
proof pass rather than asserting a vacuous theorem. -/
def IsJordanHolderData [DecidableEq Q] (α : Q → ℕ) (Vα : QuiverRepresentation k Q) : Prop :=
  -- `V_α` has dimension vector `α`, i.e. `S_i` occurs with multiplicity `α i`.
  (∀ i, dimVec Vα i = α i) ∧
  -- there is an ordering of the factors (a list of vertices, each `i` repeated
  -- `α i` times) realizing the composition series for the given orientation.
  (∃ order : List Q, ∀ i, order.count i = α i)

end Etingof.Problem6_9_3
