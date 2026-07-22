import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Complex.Basic

/-!
# Problem 8.1.3: Flat modules

A right `A`-module `M` is **flat** if the functor `M ⊗_A -` on the category of left `A`-modules
is exact. This problem asks to show:

* (i) any projective module is flat;
* (ii) for a commutative ring `A` and a multiplicatively closed subset `S`, the localization
  `S⁻¹A` is a flat `A`-module;
* (iii) for `A = ℂ[x]` and `M = ℂ[x, x⁻¹]`, `M` is flat but not projective.

## Formalization notes

We use Mathlib's `Module.Flat R M`, which is the exactness of `- ⊗_R M`. Mathlib develops
flatness over a commutative (semi)ring, so parts (ii) and (iii) — which are stated for
commutative `A` in the book — are formalized verbatim, and part (i) is formalized over a
commutative ring (the book states it for a general ring; over a commutative ring
`Module.Flat` is the tensor-exactness condition of the book).

For (iii), `ℂ[x, x⁻¹]` is the ring of Laurent polynomials, i.e. the localization of `ℂ[x]`
at the powers of `x`; we model it as `Localization.Away (Polynomial.X : Polynomial ℂ)`.

These are statement-level formalizations (spec-first): the proofs are deferred (`sorry`).
-/

namespace Etingof

open scoped Polynomial

/-- **Problem 8.1.3(i).** Any projective module is flat. -/
theorem Problem_8_1_3_i (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Projective A M] : Module.Flat A M := by
  sorry

/-- **Problem 8.1.3(ii).** For a commutative ring `A` and a multiplicatively closed subset `S`,
the localization `S⁻¹A` is a flat `A`-module. -/
theorem Problem_8_1_3_ii (A : Type*) [CommRing A] (S : Submonoid A) :
    Module.Flat A (Localization S) := by
  sorry

/-- **Problem 8.1.3(iii).** For `A = ℂ[x]` and `M = ℂ[x, x⁻¹]` (Laurent polynomials, realised as
the localization of `ℂ[x]` at the powers of `x`), `M` is flat but not projective. -/
theorem Problem_8_1_3_iii :
    Module.Flat ℂ[X] (Localization.Away (Polynomial.X : ℂ[X])) ∧
      ¬ Module.Projective ℂ[X] (Localization.Away (Polynomial.X : ℂ[X])) := by
  sorry

end Etingof
