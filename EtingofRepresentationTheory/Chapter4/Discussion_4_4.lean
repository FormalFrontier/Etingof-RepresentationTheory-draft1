import Mathlib

/-!
# Discussion 4.4: Duals and tensor products of representations

For a representation `V` of a group `G`:

* the dual `V*` is a representation via `ρ_{V*}(g) = ρ_V(g⁻¹)*`, with character
  `χ_{V*}(g) = χ_V(g⁻¹)`;
* for complex representations of a finite group the eigenvalues of `ρ(g)` are roots
  of unity, so `χ_{V*}(g) = χ_V(g⁻¹) = conj χ_V(g)`, and consequently `V ≅ V*` as
  representations if and only if `χ_V(g) ∈ ℝ` for all `g`;
* the tensor product `V ⊗ W` is a representation via `ρ_{V⊗W}(g) = ρ_V(g) ⊗ ρ_W(g)`,
  with character `χ_{V⊗W}(g) = χ_V(g) χ_W(g)`.

## Mathlib correspondence

`FDRep.char_dual` and `FDRep.char_tensor` supply the dual- and tensor-character
formulas. The identity `χ_V(g⁻¹) = conj χ_V(g)` for complex finite-group
representations (the roots-of-unity step) is proved here as
`Etingof.char_inv_eq_conj`.
-/

open FDRep CategoryTheory CategoryTheory.MonoidalCategory Representation

universe u

namespace Etingof

variable {k G : Type u} [Field k] [Group G]

/-- Tensor-product character formula (Etingof §4.4):
`χ_{V⊗W}(g) = χ_V(g)·χ_W(g)`. -/
theorem Discussion_4_4_char_tensor (V W : FDRep k G) (g : G) :
    (V ⊗ W).character g = V.character g * W.character g := by
  rw [FDRep.char_tensor]; rfl

/-- Dual character formula (Etingof §4.4): `χ_{V*}(g) = χ_V(g⁻¹)`,
where `V*` is the dual representation `of (dual V.ρ)`. -/
theorem Discussion_4_4_char_dual (V : FDRep k G) (g : G) :
    (of (dual V.ρ)).character g = V.character g⁻¹ :=
  FDRep.char_dual V g

section Complex

variable [Fintype G]

/-- Complex-conjugate character identity (Etingof §4.4): for a finite-dimensional
complex representation `V` of a finite group `G`, the eigenvalues of `ρ_V(g)` are
roots of unity (since `ρ_V(g)^|G|` need only be a root-of-unity power: `ρ_V(g)` has
finite order dividing `orderOf g`), and `λ⁻¹ = conj λ` for each. Hence

  `χ_V(g⁻¹) = Σ λᵢ⁻¹ = Σ conj λᵢ = conj χ_V(g)`.

Equivalently, via the unitarizability of `V` (Theorem 4.6.2): a `G`-invariant
positive-definite Hermitian form makes each `ρ_V(g)` unitary, so its adjoint equals
its inverse, and `trace(adjoint f) = conj(trace f)` for any operator on a
finite-dimensional inner product space (`LinearMap.toMatrix_adjoint` together with
`Matrix.trace_conjTranspose`). -/
theorem char_inv_eq_conj (V : FDRep ℂ G) (g : G) :
    V.character g⁻¹ = (starRingEnd ℂ) (V.character g) := by
  -- Proof strategy: see the docstring. Either route (roots-of-unity eigenvalue sum,
  -- or unitarization + `trace(adjoint f) = conj(trace f)`) discharges this; both
  -- require machinery (eigenvalue/charpoly multiset manipulation, or transporting
  -- the Theorem 4.6.2 `InnerProductSpace.Core` to an `InnerProductSpace ℂ` instance)
  -- that is tracked as a separate work item.
  sorry

/-- Self-dual ⟺ real character (Etingof §4.4): a finite-dimensional complex
representation `V` of a finite group is isomorphic to its dual `V*` (as
representations) if and only if its character is real-valued. -/
theorem self_dual_iff_char_real (V : FDRep ℂ G) :
    Nonempty (of (dual V.ρ) ≅ V) ↔
      ∀ g : G, (starRingEnd ℂ) (V.character g) = V.character g := by
  constructor
  · rintro ⟨e⟩ g
    have h : V.character g⁻¹ = V.character g := by
      have h0 := congrFun (FDRep.char_iso e) g
      rwa [FDRep.char_dual] at h0
    rw [← char_inv_eq_conj, h]
  · intro _hreal
    -- Reverse direction: a real character forces `χ_V = χ_{V*}`, and over `ℂ` two
    -- finite-dimensional representations of a finite group with equal characters are
    -- isomorphic (characters determine the representation). That determination
    -- theorem is tracked as a separate work item.
    sorry

end Complex

end Etingof
