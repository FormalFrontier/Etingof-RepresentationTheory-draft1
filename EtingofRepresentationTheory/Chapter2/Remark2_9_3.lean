import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import EtingofRepresentationTheory.Chapter2.Definition2_9_1

/-!
# Remark 2.9.3: Ado's theorem

Etingof states **Ado's theorem**: any finite dimensional Lie algebra is a Lie subalgebra of
`𝔤𝔩(V)` for a suitable finite dimensional vector space `V`.

Being a Lie subalgebra of `𝔤𝔩(V) = End(V)` means there is an *injective* Lie algebra
homomorphism `ρ : 𝔤 → End(V)` — a faithful finite-dimensional representation. We record the
theorem in this form, with `𝔤𝔩(V)` realised as `Module.End k V` carrying its commutator bracket
(the standard idiom in this development, e.g. the adjoint representation
`LieAlgebra.ad k L : L →ₗ⁅k⁆ Module.End k L` of Example 2.9.8).

## Scope and proof status

We state Ado's theorem over a field of characteristic zero, the setting in which it was
originally proved; the extension to fields of positive characteristic is Iwasawa's theorem.
Etingof states the result without proof, and it is genuinely deep — it is not available in
Mathlib. We therefore assert the statement faithfully and leave the proof as `sorry`, matching
the book's own treatment (a remark stating a famous theorem). The mathematical content captured
here is the existence of a finite-dimensional faithful representation of an arbitrary
finite-dimensional Lie algebra.
-/

namespace Etingof

universe u

-- The Lie ring structure on `Module.End k V` (commutator bracket) is a local instance in
-- Mathlib, just as in Example 2.9.8.
attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [Field k] [CharZero k]
variable (L : Type u) [LieRing L] [LieAlgebra k L]

/-- **Ado's theorem** (Etingof, Remark 2.9.3): every finite-dimensional Lie algebra `L` over a
field `k` of characteristic zero embeds into `𝔤𝔩(V) = End(V)` for some finite-dimensional `k`-vector
space `V`. Equivalently, `L` admits a faithful (injective) finite-dimensional representation
`ρ : L →ₗ⁅k⁆ End(V)`.

The proof is omitted: Ado's theorem is stated without proof in the book and is not available in
Mathlib. -/
theorem ado [FiniteDimensional k L] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ := by
  sorry

end Etingof
