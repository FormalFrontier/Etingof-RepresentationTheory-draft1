import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Batteries.Util.ProofWanted
import EtingofRepresentationTheory.Chapter2.Definition2_9_1

/-!
# Remark 2.9.3: Ado's theorem

Etingof states **Ado's theorem**: any finite dimensional Lie algebra is a Lie subalgebra of
`𝔤𝔩(V)` for a suitable finite dimensional vector space `V`.

Being a Lie subalgebra of `𝔤𝔩(V) = End(V)` means there is an *injective* Lie algebra
homomorphism `ρ : 𝔤 → End(V)`, a faithful finite-dimensional representation. We record the
theorem in this form, with `𝔤𝔩(V)` realised as `Module.End k V` carrying its commutator bracket
(the standard idiom in this development, e.g. the adjoint representation
`LieAlgebra.ad k L : L →ₗ⁅k⁆ Module.End k L` of Example 2.9.8).

## Scope and proof status

We state the Ado–Iwasawa theorem over an arbitrary field, matching the unqualified field `k`
in the chapter.  The characteristic-zero case is Ado's original theorem; the extension to
positive characteristic is due to Iwasawa.  Etingof states the result without proof, and it is
not available in
Mathlib. This project deliberately leaves that external result outside its proof boundary and
records it with `proof_wanted`: the statement is elaborated and typechecked as a proposition,
but no proof term, `sorry`, or axiom is introduced. This reviewed scope exception is documented in
`skipped-exercises.md`; it is non-blocking for project completion. The mathematical content
captured here is the existence of a finite-dimensional faithful representation of an arbitrary
finite-dimensional Lie algebra.
-/

namespace Etingof

universe u

-- The Lie ring structure on `Module.End k V` (commutator bracket) is a local instance in
-- Mathlib, just as in Example 2.9.8.
attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [Field k]
variable (L : Type u) [LieRing L] [LieAlgebra k L]

/-- A finite-dimensional associative algebra containing `L` faithfully supplies the representation
required by Ado: compose the given Lie embedding with the faithful left-regular representation. -/
theorem ado_of_finiteAssociativeEmbedding {A : Type u} [Ring A] [Algebra k A]
    [FiniteDimensional k A] (f : L →ₗ⁅k⁆ A) (hf : Function.Injective f) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ := by
  refine ⟨A, inferInstance, inferInstance, inferInstance,
    (Algebra.lmul k A).toLieHom.comp f, ?_⟩
  exact Algebra.lmul_injective.comp hf

/-- Finite-quotient form of the constructive route to Ado. It is enough to find a
finite-dimensional quotient (or other finite-dimensional target) of `U(L)` whose quotient map is
still injective on the canonical copy of `L`; left multiplication on that target then gives the
faithful representation. -/
theorem ado_of_finiteEnvelopingTarget {A : Type u} [Ring A] [Algebra k A]
    [FiniteDimensional k A]
    (q : UniversalEnvelopingAlgebra k L →ₐ[k] A)
    (hq : Function.Injective (fun x : L ↦ q (UniversalEnvelopingAlgebra.ι k x))) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ := by
  exact ado_of_finiteAssociativeEmbedding k L
    (q.toLieHom.comp (UniversalEnvelopingAlgebra.ι k)) hq

/-- Conversely, a faithful finite-dimensional representation extends along the universal
property to a finite-dimensional associative target of `U(L)` which still separates `L`. -/
theorem finiteEnvelopingTarget_of_faithfulRepresentation
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : L →ₗ⁅k⁆ Module.End k V) (hρ : Function.Injective ρ) :
    ∃ (A : Type u) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A)
      (q : UniversalEnvelopingAlgebra k L →ₐ[k] A),
        Function.Injective (fun x : L ↦ q (UniversalEnvelopingAlgebra.ι k x)) := by
  refine ⟨Module.End k V, inferInstance, inferInstance, inferInstance,
    UniversalEnvelopingAlgebra.lift k ρ, ?_⟩
  intro x y hxy
  apply hρ
  simpa using hxy

/-- The constructive enveloping-algebra target is exactly equivalent to the representation sought
in Ado's theorem. Thus all remaining content is the existence of the finite target, not the
passage from that target to a faithful action. -/
theorem faithfulRepresentation_iff_finiteEnvelopingTarget :
    (∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
        (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ) ↔
      ∃ (A : Type u) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A)
        (q : UniversalEnvelopingAlgebra k L →ₐ[k] A),
          Function.Injective (fun x : L ↦ q (UniversalEnvelopingAlgebra.ι k x)) := by
  constructor
  · rintro ⟨V, _, _, _, ρ, hρ⟩
    exact finiteEnvelopingTarget_of_faithfulRepresentation k L ρ hρ
  · rintro ⟨A, _, _, _, q, hq⟩
    exact ado_of_finiteEnvelopingTarget k L q hq

/-- **Ado's theorem** (Etingof, Remark 2.9.3): every finite-dimensional Lie algebra `L` over a
field `k` embeds into `𝔤𝔩(V) = End(V)` for some finite-dimensional `k`-vector
space `V`. Equivalently, `L` admits a faithful (injective) finite-dimensional representation
`ρ : L →ₗ⁅k⁆ End(V)`.

The proof is omitted: Ado's theorem is stated without proof in the book and is not available in
Mathlib. We record it via `proof_wanted`: no `sorry`, no axiom. -/
proof_wanted ado [FiniteDimensional k L] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ

end Etingof
