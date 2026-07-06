import EtingofRepresentationTheory.Chapter3.Theorem3_6_2

/-!
# Exercise 3.6.1: Additivity of the character on a subrepresentation

Show that if `W ⊂ V` are finite dimensional representations of `A`, then
`χ_V = χ_W + χ_{V/W}`.

Following the project convention (`Etingof.character`, see `Theorem3_6_2`), a representation
of `A` is an `A`-module `V` that is also a `k`-module with `IsScalarTower k A V`; its
character is `χ_V : A → k`, `a ↦ Tr|_V (ρ(a))`. A subrepresentation is an `A`-submodule
`W : Submodule A V`; the quotient representation is `V ⧸ W`. Over the field `k` a finite
dimensional `V` yields finite dimensional `W` and `V ⧸ W` (registered below as local
instances), so all three characters are defined, and the claim is the additivity
`χ_V = χ_W + χ_{V/W}` in the dual space `Dual k A`.

Statement pass: the proof (additivity of the trace along the short exact sequence
`0 → W → V → V/W → 0`) is left as `sorry`.
-/

open Module

namespace Etingof

section Exercise361

variable (k : Type*) (A : Type*) (V : Type*)
  [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [FiniteDimensional k V]
  (W : Submodule A V)

/-- A subrepresentation of a finite dimensional representation is finite dimensional over
`k` (it is a `k`-subspace of the finite dimensional space `V`). -/
instance : Module.Finite k (W : Type _) :=
  Module.Finite.of_injective (W.subtype.restrictScalars k) Subtype.val_injective

/-- The quotient of a finite dimensional representation by a subrepresentation is finite
dimensional over `k`. -/
instance : Module.Finite k (V ⧸ W) :=
  Module.Finite.of_surjective (W.mkQ.restrictScalars k) W.mkQ_surjective

/-- Exercise 3.6.1. For a subrepresentation `W` of a finite dimensional representation `V`
of the algebra `A`, the character of `V` equals the sum of the characters of `W` and the
quotient `V ⧸ W`: `χ_V = χ_W + χ_{V/W}`. -/
theorem character_eq_character_add_character_quotient :
    Etingof.character k A V
      = Etingof.character k A (W : Type _) + Etingof.character k A (V ⧸ W) := by
  sorry

end Exercise361

end Etingof
