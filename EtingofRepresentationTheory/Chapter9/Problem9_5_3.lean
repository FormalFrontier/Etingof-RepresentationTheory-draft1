import Mathlib.Algebra.Group.Idempotent
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import EtingofRepresentationTheory.Chapter9.Definition9_5_1

/-!
# Problem 9.5.3: Blocks and central idempotents

Etingof Problem 9.5.3 relates the block decomposition of a finite abelian category `𝒞`
(here the category of finite dimensional `A`-modules) to the structure of `A`.

* **(i)** There is a natural bijection between blocks of `𝒞` and *indecomposable* central
  idempotents `eₖ` of `A` (central idempotents that cannot be split nontrivially into a sum of
  two orthogonal central idempotents), under which `𝒞ₖ` is the category of `eₖ A`-modules.

* **(ii)** Every indecomposable object of `𝒞` lies in some block `𝒞ₖ`, and
  `Hom(M, N) = 0` whenever `M ∈ 𝒞ₖ`, `N ∈ 𝒞ₗ` with `k ≠ l`. Thus `𝒞 = ⊕ₖ 𝒞ₖ`.

* **(iii)** Determine the blocks of the category of left `A`-modules for `A = k[S₃]` with `k`
  of characteristic `2`. *(Deferred: this concrete modular-representation computation is left
  to a follow-up statement-pass item.)*

## Statement-pass note

Blocks are `Etingof.Block R` and block membership is `Etingof.InBlock R S M` (Definition
9.5.1). "Indecomposable central idempotent" is the predicate
`Etingof.Problem953.IsIndecomposableCentralIdempotent` defined below (a nonzero central
idempotent not expressible as a sum of two nonzero orthogonal central idempotents).
"`Hom(M, N) = 0`" is `Subsingleton (M ⟶ N)`, and "indecomposable object" is
`CategoryTheory.Indecomposable`. Two blocks are distinct exactly when their representative
simple modules are not `Etingof.AreLinked`. Proofs are deferred (`sorry`).
-/

universe v u

open CategoryTheory

namespace Etingof.Problem953

variable (R : Type u) [Ring R]

/-- An **indecomposable central idempotent** of a ring `R`: a nonzero central idempotent that
cannot be written as a sum `e = e₁ + e₂` of two nonzero orthogonal central idempotents. These
are the primitive idempotents of the center; by Problem 9.5.3(i) they index the blocks. -/
def IsIndecomposableCentralIdempotent (e : R) : Prop :=
  e ≠ 0 ∧ IsIdempotentElem e ∧ (∀ y : R, e * y = y * e) ∧
    ¬ ∃ e₁ e₂ : R, e₁ ≠ 0 ∧ e₂ ≠ 0 ∧ IsIdempotentElem e₁ ∧ IsIdempotentElem e₂ ∧
      (∀ y, e₁ * y = y * e₁) ∧ (∀ y, e₂ * y = y * e₂) ∧ e₁ * e₂ = 0 ∧ e = e₁ + e₂

/-- **Problem 9.5.3 (i).** There is a bijection between the blocks of the category of
(finite dimensional) `R`-modules and the indecomposable central idempotents of `R`. -/
theorem blocks_equiv_indecomposableCentralIdempotents [Small.{v} R] :
    Nonempty (Etingof.Block.{v} R ≃ {e : R // IsIndecomposableCentralIdempotent R e}) := by
  sorry

/-- **Problem 9.5.3 (ii), orthogonality.** If `M` lies in the block of the simple module `S`
and `N` lies in the block of the simple module `T`, and `S`, `T` are not linked (i.e. `M`, `N`
are in different blocks), then `Hom(M, N) = 0`. -/
theorem hom_subsingleton_of_not_linked [Small.{v} R]
    {S T : ModuleCat.{v} R} (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    {M N : ModuleCat.{v} R} (hM : Etingof.InBlock R S M) (hN : Etingof.InBlock R T N)
    (hST : ¬ Etingof.AreLinked R S T) :
    Subsingleton (M ⟶ N) := by
  sorry

/-- **Problem 9.5.3 (ii), decomposition.** Every indecomposable (finite length) object lies in
some block: there is a simple module `S` such that all composition factors of `M` are linked
to `S`. The finite-length assumption is recorded as the existence of at least one composition
factor. -/
theorem exists_block_of_indecomposable [Small.{v} R]
    {M : ModuleCat.{v} R} (hM : Indecomposable M)
    (hfl : ∃ S : ModuleCat.{v} R, Etingof.IsCompositionFactor R M S) :
    ∃ S : ModuleCat.{v} R, IsSimpleModule R S ∧ Etingof.InBlock R S M := by
  sorry

end Etingof.Problem953
