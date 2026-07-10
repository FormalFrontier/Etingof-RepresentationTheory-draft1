import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Exercise 8.2.9: (non)existence of enough projectives

* (i) The category of finite abelian groups, and the category of finite dimensional
  `k[x]`-modules, do **not** contain nonzero projective objects (so they do not have
  enough projectives).
* (ii) If `A` is a finitely generated commutative ring, then the category of finitely
  generated `A`-modules **has** enough projectives.

## Formalization notes

There is no ready-made Mathlib category of *finite* abelian groups or *finite dimensional*
`k[x]`-modules, so we express "is a projective object of that category" directly via the
defining lifting property: `P` is projective iff every epimorphism `f : Q₁ ↠ Q₂` (between
objects of the subcategory) and every map `g : P → Q₂` admit a lift `h : P → Q₁` with
`f ∘ h = g`. Part (i) is then the statement that such a `P` must be zero (`Subsingleton P`).

For part (ii), "enough projectives" for the category of finitely generated `A`-modules means
every finitely generated module is a quotient of a projective object of the category. A finite
free module `Fin n → A` is finitely generated and projective, so the content is that every
finitely generated `A`-module admits a surjection from a finite free module. The finite
generation hypothesis on the commutative ring `A` (a finitely generated `ℤ`-algebra) makes the
category abelian via the Hilbert basis theorem (`A` is Noetherian, so submodules of finitely
generated modules are finitely generated); this is what is needed for the categorical notion of
"enough projectives" to make sense.

These are statement-level formalizations (spec-first): the proofs are deferred (`sorry`).
-/

namespace Etingof

universe u

/-- **Exercise 8.2.9(i), finite abelian groups.** A finite abelian group that is a projective
object of the category of finite abelian groups — i.e. has the lifting property against
surjections of finite abelian groups — is zero. Hence that category has no nonzero projective
objects. -/
theorem Exercise_8_2_9_i_finAb
    (P : Type u) [AddCommGroup P] [Finite P]
    (hP : ∀ (Q₁ Q₂ : Type u) [AddCommGroup Q₁] [Finite Q₁] [AddCommGroup Q₂] [Finite Q₂]
      (f : Q₁ →+ Q₂) (g : P →+ Q₂), Function.Surjective f →
        ∃ h : P →+ Q₁, ∀ x, f (h x) = g x) :
    Subsingleton P := by
  sorry

/-- **Exercise 8.2.9(i), finite dimensional `k[x]`-modules.** A finite dimensional `k[x]`-module
that is a projective object of the category of finite dimensional `k[x]`-modules — i.e. has the
lifting property against surjections of finite dimensional `k[x]`-modules — is zero. Hence that
category has no nonzero projective objects. -/
theorem Exercise_8_2_9_i_polynomial
    (k : Type u) [Field k]
    (P : Type u) [AddCommGroup P] [Module (Polynomial k) P] [Module k P]
      [IsScalarTower k (Polynomial k) P] [FiniteDimensional k P]
    (hP : ∀ (Q₁ Q₂ : Type u) [AddCommGroup Q₁] [Module (Polynomial k) Q₁] [Module k Q₁]
        [IsScalarTower k (Polynomial k) Q₁] [FiniteDimensional k Q₁]
        [AddCommGroup Q₂] [Module (Polynomial k) Q₂] [Module k Q₂]
        [IsScalarTower k (Polynomial k) Q₂] [FiniteDimensional k Q₂]
        (f : Q₁ →ₗ[Polynomial k] Q₂) (g : P →ₗ[Polynomial k] Q₂), Function.Surjective f →
          ∃ h : P →ₗ[Polynomial k] Q₁, ∀ x, f (h x) = g x) :
    Subsingleton P := by
  sorry

/-- **Exercise 8.2.9(ii).** If `A` is a finitely generated commutative ring (a finitely
generated `ℤ`-algebra), then the category of finitely generated `A`-modules has enough
projectives: every finitely generated `A`-module is a quotient of a finite free module
`Fin n → A`, which is a finitely generated projective object. -/
theorem Exercise_8_2_9_ii
    (A : Type u) [CommRing A] [Algebra.FiniteType ℤ A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (n : ℕ) (f : (Fin n → A) →ₗ[A] M), Function.Surjective f :=
  Module.Finite.exists_fin' A M

end Etingof
