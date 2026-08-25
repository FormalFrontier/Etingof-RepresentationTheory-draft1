import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Definition 2.8.8: Subrepresentation of a Quiver Representation

A **subrepresentation** of a representation (Vᵢ, xₕ) of a quiver Q is a representation
(Wᵢ, x'ₕ) where Wᵢ ⊆ Vᵢ for all i ∈ I and where xₕ(W_{h'}) ⊆ W_{h''} and
x'ₕ = xₕ|_{W_{h'}} for all h ∈ E.

## Mathlib correspondence (partial)

No direct Mathlib support for quiver representation subrepresentations. We define it
as a family of submodules closed under the arrow maps.
-/

/-- A subrepresentation of a quiver representation, in the sense of Etingof Definition 2.8.8.
A family of subspaces, one per vertex, that is invariant under all arrow maps. -/
structure Etingof.QuiverSubrepresentation (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q] (ρ : Etingof.QuiverRepresentation k Q) where
  /-- The submodule at each vertex -/
  carrier : ∀ v, Submodule k (ρ.obj v)
  /-- The arrow maps preserve the subspaces -/
  map_mem : ∀ {v w : Q} (e : v ⟶ w) (x : ρ.obj v),
    x ∈ carrier v → ρ.mapLinear e x ∈ carrier w

namespace Etingof.QuiverSubrepresentation

variable {k Q : Type*} [CommSemiring k] [Quiver Q]
variable {ρ : Etingof.QuiverRepresentation k Q}

/-- The representation `(W_i, x'_h)` carried by a subrepresentation. Its arrow maps are exactly
the restrictions `x'_h = x_h|_{W_{h'}}` required by Definition 2.8.8. -/
noncomputable def toRepresentation (S : Etingof.QuiverSubrepresentation k Q ρ) :
    Etingof.QuiverRepresentation k Q where
  obj i := S.carrier i
  mapLinear e := LinearMap.restrict (ρ.mapLinear e) (fun x hx => S.map_mem e x hx)

@[simp] theorem toRepresentation_obj (S : Etingof.QuiverSubrepresentation k Q ρ) (i : Q) :
    S.toRepresentation.obj i = S.carrier i :=
  rfl

end Etingof.QuiverSubrepresentation
