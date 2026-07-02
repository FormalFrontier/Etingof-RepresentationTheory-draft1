import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import EtingofRepresentationTheory.Chapter2.Definition2_3_8

/-!
# Remark 3.8.6: Krull-Schmidt for modules of finite length

Remark 3.8.6 of Etingof observes that, although the Krull-Schmidt theorem *fails* for
infinite-dimensional modules (see Problem 3.8.5 for a counterexample), it still *holds* for
modules of **finite length**, i.e. modules `M` such that every filtration of `M` has length
bounded by a constant `l(M)`.

This file formalizes the positive statement. Finite length is captured by
`[IsArtinian A V] [IsNoetherian A V]` (equivalently `IsFiniteLength A V`, see
`isFiniteLength_iff_isNoetherian_isArtinian`), which is the property that all composition
series have a common finite length.

## Main results

* `Etingof.isNilpotent_or_isUnit_of_finiteLength_indecomposable` — **Fitting's lemma** for
  finite-length modules: any endomorphism of a finite-length indecomposable module is either
  nilpotent or an isomorphism. This is the finite-length analogue of Lemma 3.8.2, and, crucially,
  it needs **no** algebraically-closed-field hypothesis: it is powered by Mathlib's Fitting
  decomposition `LinearMap.eventually_isCompl_ker_pow_range_pow` for Artinian + Noetherian modules.
* `Etingof.isLocalRing_end_of_finiteLength_indecomposable` — the endomorphism ring of a
  finite-length indecomposable module is local. This is the abstract input that drives the
  uniqueness half of Krull-Schmidt.

The finite-length hypothesis is genuinely more general than the finite-dimensional-over-a-field
setting of Theorem 3.8.1: there is no ground field here, only the ring `A`.
-/

open LinearMap

namespace Etingof

variable {A : Type*} [Ring A] {V : Type*} [AddCommGroup V] [Module A V]

/-- **Fitting's lemma for finite-length modules.** Any endomorphism `f` of a finite-length
indecomposable `A`-module `V` is either nilpotent or an isomorphism.

The Fitting decomposition (Mathlib's `LinearMap.eventually_isCompl_ker_pow_range_pow`, valid for
Artinian + Noetherian modules) gives, for large `n`, a direct-sum splitting
`V = ker (fⁿ) ⊕ range (fⁿ)`. Indecomposability forces one summand to vanish: if `range (fⁿ) = 0`
then `fⁿ = 0` and `f` is nilpotent; if `ker (fⁿ) = 0` then `fⁿ` is bijective, hence so is `f`.

Unlike the Chapter 3 proof (Lemma 3.8.2), which diagonalizes an eigenvalue and therefore needs an
algebraically closed field, this argument works over an arbitrary ring `A`. -/
theorem isNilpotent_or_isUnit_of_finiteLength_indecomposable
    [IsArtinian A V] [IsNoetherian A V]
    (hV : Etingof.IsIndecomposable A V) (f : Module.End A V) :
    IsNilpotent f ∨ IsUnit f := by
  -- Pick `n ≥ 1` for which the Fitting decomposition splits `V` as `ker (fⁿ) ⊕ range (fⁿ)`.
  obtain ⟨n, hcompl, hn1⟩ :=
    (f.eventually_isCompl_ker_pow_range_pow.and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn1).symm⟩
  rcases hV.2 (LinearMap.ker (f ^ (m + 1))) (LinearMap.range (f ^ (m + 1))) hcompl with
    hker | hrange
  · -- `ker (fⁿ) = 0`: `fⁿ` is injective and, being complementary to `0`, surjective; so `f`
    -- is a unit.
    right
    rw [Module.End.isUnit_iff]
    have hinj_pow : Function.Injective (f ^ (m + 1)) := LinearMap.ker_eq_bot.mp hker
    have hsurj_pow : Function.Surjective (f ^ (m + 1)) := by
      rw [← LinearMap.range_eq_top]
      have hsup : LinearMap.ker (f ^ (m + 1)) ⊔ LinearMap.range (f ^ (m + 1)) = ⊤ :=
        codisjoint_iff.mp hcompl.codisjoint
      rwa [hker, bot_sup_eq] at hsup
    -- Factor `fⁿ = f^[m] ∘ f`, so injectivity/surjectivity of `fⁿ` descends to `f`.
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hinj_pow
      rw [Module.End.pow_apply, Module.End.pow_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hsurj_pow y
      refine ⟨(⇑f)^[m] z, ?_⟩
      rw [Module.End.pow_apply, Function.iterate_succ_apply'] at hz
      exact hz
  · -- `range (fⁿ) = 0`: `fⁿ` is the zero map, so `f` is nilpotent.
    left
    refine ⟨m + 1, ?_⟩
    ext x
    have hx : (f ^ (m + 1)) x ∈ LinearMap.range (f ^ (m + 1)) := LinearMap.mem_range_self _ x
    rw [hrange, Submodule.mem_bot] at hx
    simpa using hx

/-- **The endomorphism ring of a finite-length indecomposable module is local.** By the
nilpotent-or-isomorphism dichotomy of `isNilpotent_or_isUnit_of_finiteLength_indecomposable`, for
every endomorphism `a` either `a` is a unit or `1 - a` is a unit (`1 - a` is a unit whenever `a` is
nilpotent), which is exactly the local-ring criterion. -/
theorem isLocalRing_end_of_finiteLength_indecomposable
    [IsArtinian A V] [IsNoetherian A V]
    (hV : Etingof.IsIndecomposable A V) :
    IsLocalRing (Module.End A V) := by
  haveI : Nontrivial V := hV.1
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases isNilpotent_or_isUnit_of_finiteLength_indecomposable hV a with hnil | hunit
  · exact Or.inr (IsNilpotent.isUnit_one_sub hnil)
  · exact Or.inl hunit

end Etingof
