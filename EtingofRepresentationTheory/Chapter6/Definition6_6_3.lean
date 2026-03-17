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
    (V : Type*) [DecidableEq V] [Quiver V]
    (i : V) (hi : Etingof.IsSink V i)
    (ρ : Etingof.QuiverRepresentation k V) :
    @Etingof.QuiverRepresentation k V _ (Etingof.reversedAtVertex V i) := by
  classical
  -- φ : ⊕_{j→i} ρ_j → ρ_i, the sum of representation maps for arrows into i
  let φ : DirectSum (Etingof.ArrowsInto V i) (fun a => ρ.obj a.1) →ₗ[k] ρ.obj i :=
    DirectSum.toModule k (Etingof.ArrowsInto V i) (ρ.obj i) (fun a => ρ.mapLinear a.2)
  refine @Etingof.QuiverRepresentation.mk k V _ (Etingof.reversedAtVertex V i)
    (fun v => if v = i then ↥(LinearMap.ker φ) else ρ.obj v)
    (fun v => by dsimp only; split <;> infer_instance)
    (fun v => by exact sorry)
    (fun {a b} (e : Etingof.ReversedAtVertexHom V i a b) => by
      change Etingof.ReversedAtVertexHom V i a b at e
      unfold Etingof.ReversedAtVertexHom at e
      by_cases ha : a = i
      · by_cases hb : b = i
        · -- a = i, b = i: self-loop; vacuous since i is a sink
          simp only [ha, hb] at e; exact ((hi i).false e).elim
        · -- a = i, b ≠ i: reversed arrow, ker φ ↪ ⊕ → proj_b
          simp only [ha, hb, ite_true, ite_false] at e
          exact Eq.mpr sorry
            ((DirectSum.component k (Etingof.ArrowsInto V i)
              (fun x => ρ.obj x.1) ⟨b, e⟩).comp
              (LinearMap.ker φ).subtype)
      · by_cases hb : b = i
        · -- a ≠ i, b = i: arrow i → a, vacuous since i is a sink
          simp only [ha, hb] at e; exact ((hi a).false e).elim
        · -- a ≠ i, b ≠ i: unchanged arrow
          simp only [ha, hb] at e
          exact Eq.mpr sorry (ρ.mapLinear e))
