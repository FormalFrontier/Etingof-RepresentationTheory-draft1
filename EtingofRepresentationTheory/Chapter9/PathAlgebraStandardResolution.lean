import EtingofRepresentationTheory.Chapter9.PathAlgebraConsSplittingIso

/-!
# Injectivity of the boundary map of the standard short complex

Eighth layer of the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i), parent #6420). Write `A := PathAlgebra k Q`, `S := Q → k` the vertex
subalgebra, `V` the arrow bimodule. This file proves `Mono (stdd M)` — injectivity of the
boundary map `d` of the standard short complex
(`Chapter9/PathAlgebraStandardComplex.lean`) — the noncommutative analogue of the top-degree
argument `pm_koszul_injective` / `finsupp_shift_eq_zero` (`Chapter9/KoszulHelpers.lean`).

The crux is the **injectivity of the top half** `Φ = stdΦ` of `d`
(`Chapter9/PathAlgebraConsSplittingIso.lean`), i.e. the injectivity content of the cons-splitting
`A_n ⊗_S V ≅ A_{n+1}` tensored with `M`. We build a genuine additive **retraction** `stdΦRetr` of
`Φ` from the combinatorial cons-decomposition (`Chapter9/PathAlgebraConsSplitting.lean`): every
length-`(n+1)` basis path `q = p·e` splits into its initial length-`n` path `p` and final arrow
`e`, and the retraction sends `(x·arrow) ⊗ m ↦ x ⊗ (arrow ⊗ m)`. Injectivity of `Φ` then feeds the
top-degree telescoping: from `d ξ = 0` one gets `Φ(ξ_n) = Ψ(ξ_{n+1})`, and injectivity of `Φ`
turns this into `ξ_n = R(Ψ(ξ_{n+1}))`, so `finsupp_shift_eq_zero` forces the graded components of
`ξ` to vanish, hence `ξ = 0` (`inducedCoordMapGen_injective`).
-/

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace Etingof.PathAlgebra

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

variable (M : ModuleCat.{u + 1} (PathAlgebra k Q))

/-! ## The combinatorial cons-splitting contribution of a basis path -/

/-- **The cons-split of a single basis path.** A length-`0` (vertex) path contributes `0`; a
positive-length path `q = cons p e` contributes `p ⊗ (e ⊗ m)`, splitting off its final arrow `e`.
This is the per-basis-path core of the additive retraction `stdΦRetr` of the top half `Φ` of the
boundary `d`. -/
noncomputable def consContrib (x : QuiverPathIndex Q) (m : restrictObj M) :
    inducedVtensObj M :=
  match x with
  | ⟨_, _, .nil⟩ => 0
  | ⟨a, c, .cons (b := b) p e⟩ =>
      ((ofPath (⟨a, b, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        ((Finsupp.single (⟨b, c, e⟩ : ArrowIndex Q) (1 : k) : ArrowTgt k Q) ⊗ₜ[Q → k] m
          : VtensObj M) : inducedVtensObj M)

@[simp] theorem consContrib_nil (a : Q) (m : restrictObj M) :
    consContrib M (⟨a, a, Quiver.Path.nil⟩ : QuiverPathIndex Q) m = 0 := rfl

@[simp] theorem consContrib_cons {a b c : Q} (p : Quiver.Path a b) (e : b ⟶ c)
    (m : restrictObj M) :
    consContrib M (⟨a, c, Quiver.Path.cons p e⟩ : QuiverPathIndex Q) m
      = ((ofPath (⟨a, b, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        ((Finsupp.single (⟨b, c, e⟩ : ArrowIndex Q) (1 : k) : ArrowTgt k Q) ⊗ₜ[Q → k] m
          : VtensObj M) : inducedVtensObj M) := rfl

end Etingof.PathAlgebra
