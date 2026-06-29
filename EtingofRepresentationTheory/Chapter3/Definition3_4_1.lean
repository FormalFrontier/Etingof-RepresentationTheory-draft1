import Mathlib.Order.RelSeries
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Definition 3.4.1: Filtration of a Representation

A (finite) **filtration** of V is a sequence of subrepresentations
0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ Vₙ = V.

## Mathlib correspondence

Mathlib has `CompositionSeries` for Jordan-Hölder filtrations. The underlying ascending
chain of submodules is modeled as a `RelSeries` on `Submodule A V` with the strict
less-than relation. Etingof's Definition 3.4.1 additionally requires the chain to be a
filtration *of `V`*: it must start at `0` (`V₀ = ⊥`) and end at `V` (`Vₙ = ⊤`). These two
boundary conditions are recorded as fields of the structure below; dropping them would
model an arbitrary chain between two submodules rather than a filtration of `V`.
-/

/-- A (finite) filtration of a module `V` over `A` is a finite strictly ascending chain of
submodules `0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ Vₙ = V` that starts at `⊥` and ends at `⊤`.
Etingof Definition 3.4.1. -/
structure Etingof.Filtration (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V] where
  /-- The underlying strictly ascending chain of submodules `V₀ ⊂ V₁ ⊂ ⋯ ⊂ Vₙ`. -/
  chain : RelSeries {p : Submodule A V × Submodule A V | p.1 < p.2}
  /-- The filtration starts at `0`: the first term `V₀` is the zero submodule. -/
  head_eq_bot : chain.head = ⊥
  /-- The filtration ends at `V`: the last term `Vₙ` is all of `V`. -/
  last_eq_top : chain.last = ⊤
