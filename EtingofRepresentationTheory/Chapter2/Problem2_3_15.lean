import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Problem 2.3.15: Irreducible subrepresentations

> Let `V` be a nonzero finite dimensional representation of an algebra `A`. Show that
> it has an irreducible subrepresentation. Then show by example that this does not
> always hold for infinite dimensional representations.

A representation of a `k`-algebra `A` is an `A`-module `V` that is also a `k`-vector
space compatibly (`IsScalarTower k A V`); "finite dimensional" means `Module.Finite k V`,
and an "irreducible subrepresentation" is a simple `A`-submodule.

## Part (a): existence for finite dimensional representations

`exists_isSimpleModule_of_finite`. The argument is the elementary one: a nonzero
finite dimensional space is Artinian over `k`, hence Artinian over `A`
(`isArtinian_of_tower`); its submodule lattice is therefore atomic
(`isAtomic_of_orderBot_wellFounded_lt`), and an atom is a simple `A`-submodule
(`isSimpleModule_iff_isAtom`). This is the book's "take a subrepresentation of
minimal nonzero dimension" made precise: an atom of the submodule lattice.

## Part (b): failure in infinite dimension

`not_exists_isSimpleModule_polynomial`. The regular representation of `A = k[x]` on
itself has no irreducible subrepresentation. A simple submodule would be a *minimal*
nonzero ideal, but for any nonzero `s ∈ k[x]` the ideal `(x·s)` is a strictly smaller
nonzero submodule (`x` is not a unit), so no nonzero submodule is minimal.

## Relation to Proposition 3.1.4

The book's proof of Proposition 3.1.4 invokes this problem to extract an irreducible
`P ⊆ W`. The Lean proof of Proposition 3.1.4
(`Chapter3/Proposition3_1_4.lean`, `Etingof.subrepresentation_of_semisimple`) does
**not** route through Problem 2.3.15: the ambient module `⊕ᵢ nᵢ Vᵢ` is a finite direct
sum of simples, hence semisimple, so existence of a simple submodule of any submodule
`W` comes directly from `IsSemisimpleModule.eq_bot_or_exists_simple_le`. That is a
legitimate stronger route (it needs no finite-dimensionality), so Proposition 3.1.4 does
not silently assume this problem — it reproves the existence fact it needs. Problem
2.3.15 is formalized here in its own right.

The group-representation form of part (a) already appears as
`Etingof.exists_isSimpleModule_le` (`Chapter5/SimpleSubrepExtraction.lean`); this file
records the general `k`-algebra statement of the book problem.
-/

open Polynomial

namespace Etingof

section FiniteDimensional

variable {k A V : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V]

/-- **Problem 2.3.15(a).** A nonzero finite dimensional representation of a `k`-algebra
`A` has an irreducible subrepresentation: there is a simple `A`-submodule `S ≤ V`. -/
theorem exists_isSimpleModule_of_finite [Module.Finite k V] [Nontrivial V] :
    ∃ S : Submodule A V, IsSimpleModule A S := by
  -- Finite over the field `k` ⇒ Artinian over `k` ⇒ Artinian over `A`.
  haveI : IsArtinian k V := inferInstance
  haveI : IsArtinian A V := isArtinian_of_tower k inferInstance
  -- The `A`-submodule lattice is nontrivial and atomic; an atom is a simple submodule.
  haveI : Nontrivial (Submodule A V) := (Submodule.nontrivial_iff A).mpr inferInstance
  haveI : IsAtomic (Submodule A V) := isAtomic_of_orderBot_wellFounded_lt IsWellFounded.wf
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A V)
  exact ⟨S, isSimpleModule_iff_isAtom.mpr hS⟩

end FiniteDimensional

/-- **Problem 2.3.15(b).** The finite-dimensionality hypothesis is necessary: the
regular representation of `k[x]` on itself (an infinite dimensional representation) has
no irreducible subrepresentation. A simple submodule would be a minimal nonzero ideal,
but for any nonzero `s` the ideal `(x · s)` is a strictly smaller nonzero submodule. -/
theorem not_exists_isSimpleModule_polynomial (k : Type*) [Field k] :
    ¬ ∃ S : Submodule (Polynomial k) (Polynomial k),
        IsSimpleModule (Polynomial k) S := by
  rintro ⟨S, hS⟩
  rw [isSimpleModule_iff_isAtom] at hS
  -- `S` is an atom: nonzero, and any strictly smaller submodule is `⊥`.
  obtain ⟨s, hsS, hs0⟩ := (Submodule.ne_bot_iff S).mp hS.1
  -- `T = (x · s)` is a nonzero submodule contained in `S`.
  set T : Submodule (Polynomial k) (Polynomial k) := Submodule.span (Polynomial k) {X * s}
    with hT
  have hXs0 : X * s ≠ 0 := mul_ne_zero X_ne_zero hs0
  have hTle : T ≤ S := by
    rw [hT, Submodule.span_le, Set.singleton_subset_iff]
    exact S.smul_mem X hsS
  have hTne : T ≠ ⊥ := by
    rw [hT, Ne, Submodule.span_singleton_eq_bot]
    exact hXs0
  -- By minimality `T` cannot be strictly below `S`, so `T = S` and `s ∈ T`.
  have hsT : s ∈ T := by
    rcases eq_or_lt_of_le hTle with hTeq | hTlt
    · rw [hTeq]; exact hsS
    · exact absurd (hS.2 T hTlt) hTne
  -- `s ∈ (x · s)` means `s = a · x · s`, forcing `x` to be a unit — impossible.
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hsT
  rw [smul_eq_mul, ← mul_assoc] at ha
  have hax : a * X = 1 := by
    have : a * X * s = 1 * s := by rw [ha, one_mul]
    exact mul_right_cancel₀ hs0 this
  exact not_isUnit_X (IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact hax))

end Etingof
