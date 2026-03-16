import Mathlib

/-!
# Definition 5.4.1: Solvable Group

A group G is **solvable** if there exists a chain of subgroups
  {e} = G₁ ⊲ G₂ ⊲ ... ⊲ Gₙ = G
such that each quotient Gᵢ₊₁/Gᵢ is abelian.

Equivalently, the derived series G ⊃ [G,G] ⊃ [[G,G],[G,G]] ⊃ ... terminates at {e}.

## Mathlib correspondence

Exact match: `IsSolvable G` in Mathlib, defined via the derived series.
-/

/-- A group G is solvable iff its derived series terminates at the trivial subgroup.
This is `IsSolvable G` in Mathlib. (Etingof Definition 5.4.1)

Example: S₃ is solvable with chain {e} ⊲ A₃ ⊲ S₃. -/
example : IsSolvable (Equiv.Perm (Fin 3)) := by
  sorry
