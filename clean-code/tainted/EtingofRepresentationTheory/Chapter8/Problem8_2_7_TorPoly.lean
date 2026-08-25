import EtingofRepresentationTheory.Chapter8.Problem8_2_7_TorFG
import EtingofRepresentationTheory.Chapter8.Problem8_2_7_ExtPoly

/-!
# Problem 8.2.7(ii): `Torᵢ(M, N)` for arbitrary finitely generated `k[x]`-modules

This is the `k[x]` counterpart of `Problem8_2_7_TorInt.lean`. `Problem8_2_7.lean` computes `Torᵢ`
for a pair of cyclic `k[x]`-modules and for a free generator, `Problem8_2_7_TorFG.lean` reduces the
general case to those building blocks, and this file fills in the summand table over `k[x]` and
assembles the answer for **arbitrary** finitely generated `M`, `N`.

## The summand table

Every summand of a decomposition is `k[x] ⧸ (d)` (`Etingof.PIDDecomposition.summandIso`), the free
ones being `d = 0`. Writing `f` for the first argument's generator, `g` for the second's, and
`(f, g)` for the sum ideal `(f) ⊔ (g)` (which is `(gcd f g)`, since `k[x]` is a PID):

| | `Tor₀` | `Tor₁` | `Torₙ₊₂` |
|---|---|---|---|
| `f = 0` (free) | `k[x] ⧸ (g)` | `0` | `0` |
| `f ≠ 0`, `g = 0` | `k[x] ⧸ (f)` | `0` | `0` |
| `f ≠ 0`, `g ≠ 0` | `k[x] ⧸ (f, g)` | `k[x] ⧸ (f, g)` | `0` |

As over `ℤ`, **degree `0` needs no case split** — `Problem_8_2_7_ii_tor_zero` already has no
hypothesis on `f` or `g`, since `(f, 0) = (f)` and `(0, g) = (g)` — while **degree `1` loses both
free blocks**: `Tor₁(k[x], N) = 0` because `k[x]` is projective, and `Tor₁(k[x] ⧸ (f), k[x]) = 0`
because `k[x]` is a domain, hence torsion-free.

## Universe restriction

The statements below take `k : Type`, not `k : Type u`. `Etingof.torBiproductIso` and
`Etingof.torPiIso` are indexed by a `Type 0`, so the summands of a `PIDDecomposition` have to live
there too; see the module docstring of `Problem8_2_7_TorFG.lean`. The `Ext` half
(`Problem8_2_7_ExtPoly.lean`) is universe-polymorphic in `k`.

## Main results

* `Etingof.Problem_8_2_7_ii_tor_zero_fg`:
  `M ⊗ N = Tor₀(M, N) ≅ ⨁_{j,l} k[x] ⧸ (dⱼ, e_l)` over **all** pairs of summands.
* `Etingof.Problem_8_2_7_ii_tor_one_fg`: `Tor₁(M, N) ≅ ⨁_{i,j} k[x] ⧸ (fᵢ, gⱼ)`, over the
  **torsion** summands of both arguments only.
* `Etingof.Problem_8_2_7_ii_tor_fg_vanish`: `Torᵢ(M, N) = 0` for `i ≥ 2`, `N` arbitrary.
* `Etingof.Problem_8_2_7_ii_tor_fg`: the three answers packaged with the existence of suitable
  decompositions.
-/

namespace Etingof

open CategoryTheory Limits Polynomial

attribute [local instance] mopPolyQuot

variable {k : Type} [Field k]

/-! ### Identifying the summands

As over `ℤ`, each summand has to be identified in two shapes: as an object of
`ModuleCat k[X]ᵐᵒᵖ` for the first argument of `Tor`, and as a bare module for the second. -/

/-- Every summand of a decomposition, viewed as a **right** `k[x]`-module, is the cyclic right
module `k[x] ⧸ (genOf j)` the `Tor` building blocks of `Problem8_2_7.lean` are stated for. The free
summands are `k[x] ⧸ (0)`. -/
noncomputable def mopPolySummandIso {M : Type} [AddCommGroup M] [Module k[X] M]
    (D : PIDDecomposition k[X] M) (j : D.index) :
    D.mopSummand j ≅ ModuleCat.of (k[X])ᵐᵒᵖ (k[X] ⧸ Ideal.span {D.genOf j}) :=
  D.mopSummandIso j ≪≫ mopPolyCyclicIso (D.genOf j)

/-- Every summand of a decomposition, as a plain `k[x]`-module, is `k[x] ⧸ (genOf l)`: the
`LinearEquiv` form of `Etingof.PIDDecomposition.summandIso`, needed because `Tor` takes its second
argument as a bare module rather than as an object of `ModuleCat k[X]`. -/
noncomputable def polySummandLinearEquiv {N : Type} [AddCommGroup N] [Module k[X] N]
    (E : PIDDecomposition k[X] N) (l : E.index) :
    (E.summand l : Type) ≃ₗ[k[X]] (k[X] ⧸ Ideal.span {E.genOf l}) :=
  (E.summandIso l).toLinearEquiv

/-! ### The assembled answers -/

variable {M N : Type} [AddCommGroup M] [Module k[X] M] [AddCommGroup N] [Module k[X] N]

/-- **Problem 8.2.7(ii), higher `Tor`.** `Torᵢ(M, N) = 0` for `i ≥ 2`, for `M` a finitely generated
`k[x]`-module and `N` an *arbitrary* one: `M` is a finite direct sum of cyclic modules, and higher
`Tor` out of a cyclic module over the PID `k[x]` vanishes for an arbitrary second argument
(`Etingof.tor_vanish_polyQuot`). -/
theorem Problem_8_2_7_ii_tor_fg_vanish [Module.Finite k[X] M] (Y : Type) [AddCommGroup Y]
    [Module k[X] Y] (n : ℕ) :
    Subsingleton (Etingof.Tor k[X] Y (mopOf k[X] M) (n + 2)) := by
  obtain ⟨D⟩ := exists_pidDecomposition k[X] M
  refine subsingleton_tor_of_summands D Y (n + 2) fun j => ?_
  exact AddCommGrpCat.subsingleton_of_isZero
    ((tor_vanish_polyQuot (D.genOf j) Y n).of_iso
      (torFstCongr Y (mopPolySummandIso D j) (n + 2)))

/-- **Problem 8.2.7(ii), `Tor₀`.** `M ⊗_{k[x]} N = Tor₀(M, N) ≅ ⨁_{j,l} k[x] ⧸ (dⱼ, e_l)`, the
product running over **all** pairs of summands of `M` and `N` — free ones included, where the
generator is `0` and `k[x] ⧸ (0) ≅ k[x]`. Expanding the four blocks gives the form stated in the
exercise, with `k[x] ⧸ (f, g)` in place of `ℤ/gcd(a, b)`. -/
theorem Problem_8_2_7_ii_tor_zero_fg (D : PIDDecomposition k[X] M)
    (E : PIDDecomposition k[X] N) :
    Nonempty (Etingof.Tor k[X] N (mopOf k[X] M) 0 ≃+
      ∀ (j : D.index) (l : E.index), (k[X] ⧸ Ideal.span {D.genOf j, E.genOf l})) := by
  refine ⟨(torPIDDecompositionAddEquiv D E 0).trans
    (AddEquiv.piCongrRight fun j => AddEquiv.piCongrRight fun l => ?_)⟩
  exact ((torSndCongr (polySummandLinearEquiv E l) (D.mopSummand j) 0) ≪≫
    (torFstCongr (k[X] ⧸ Ideal.span {E.genOf l}) (mopPolySummandIso D j) 0) ≪≫
    (Problem_8_2_7_ii_tor_zero k (D.genOf j)
      (E.genOf l)).some).addCommGroupIsoToAddEquiv

/-- **Problem 8.2.7(ii), `Tor₁`.** `Tor₁(M, N) ≅ ⨁_{i,j} k[x] ⧸ (fᵢ, gⱼ)`, the product running
over the **torsion** summands of `M` and of `N` only. Both free blocks drop out:
`Tor₁(k[x], N) = 0` since `k[x]` is projective (`Problem_8_2_7_ii_tor_free_vanish`), and
`Tor₁(k[x] ⧸ (fᵢ), k[x]) = 0` since `k[x]` is torsion-free
(`Problem_8_2_7_ii_tor_cyclic_free_one`). -/
theorem Problem_8_2_7_ii_tor_one_fg (D : PIDDecomposition k[X] M) (E : PIDDecomposition k[X] N)
    (hD : ∀ i, D.gen i ≠ 0) (hE : ∀ l, E.gen l ≠ 0) :
    Nonempty (Etingof.Tor k[X] N (mopOf k[X] M) 1 ≃+
      ∀ (i : D.torsionIndex) (l : E.torsionIndex),
        (k[X] ⧸ Ideal.span {D.gen i, E.gen l})) := by
  -- Split off the free summands of `M`, on which `Tor₁` vanishes.
  haveI : ∀ i : Fin D.freeRank,
      Subsingleton (Etingof.Tor k[X] N (D.mopSummand (Sum.inl i)) 1) := fun _ =>
    AddCommGrpCat.subsingleton_of_isZero
      ((Problem_8_2_7_ii_tor_free_vanish k N 0).of_iso (torFstCongr N (mopSelfIso k[X]) 1))
  haveI := subsingleton_pi fun i : Fin D.freeRank =>
    (Etingof.Tor k[X] N (D.mopSummand (Sum.inl i)) 1 : Type)
  refine ⟨(torFstDecompositionAddEquiv D N 1).trans
    (((piSumAddEquiv _).trans (subsingletonProdAddEquiv _ _)).trans
      (AddEquiv.piCongrRight fun i => ?_))⟩
  -- Identify the first argument with `k[x] ⧸ (fᵢ)`, then decompose `N` and drop *its* free block.
  refine (torFstCongr N (mopPolySummandIso D (Sum.inr i)) 1).addCommGroupIsoToAddEquiv.trans ?_
  haveI : ∀ l : Fin E.freeRank,
      Subsingleton (Etingof.Tor k[X] (E.summand (Sum.inl l))
        (ModuleCat.of (k[X])ᵐᵒᵖ (k[X] ⧸ Ideal.span {D.genOf (Sum.inr i)})) 1) := fun _ =>
    AddCommGrpCat.subsingleton_of_isZero (Problem_8_2_7_ii_tor_cyclic_free_one _ (hD i))
  haveI := subsingleton_pi fun l : Fin E.freeRank =>
    (Etingof.Tor k[X] (E.summand (Sum.inl l))
      (ModuleCat.of (k[X])ᵐᵒᵖ (k[X] ⧸ Ideal.span {D.genOf (Sum.inr i)})) 1 : Type)
  refine (torSndDecompositionAddEquiv E _ 1).trans
    (((piSumAddEquiv _).trans (subsingletonProdAddEquiv _ _)).trans
      (AddEquiv.piCongrRight fun l => ?_))
  exact ((torSndCongr (polySummandLinearEquiv E (Sum.inr l)) _ 1) ≪≫
    (Problem_8_2_7_ii_tor_one (D.gen i) (E.gen l) (hD i) (hE l)).some).addCommGroupIsoToAddEquiv

/-- **Problem 8.2.7(ii), `Tor`, packaged.** For any two finitely generated `k[x]`-modules `M`, `N`
there are decompositions `M ≅ k[x]^m ⊕ ⨁ᵢ k[x] ⧸ (fᵢ)` and `N ≅ k[x]^p ⊕ ⨁ⱼ k[x] ⧸ (gⱼ)` (with all
`fᵢ`, `gⱼ` nonzero) for which

* `Tor₀(M, N) = M ⊗ N ≅ ⨁_{j,l ∈ all summands} k[x] ⧸ (dⱼ, e_l)`,
* `Tor₁(M, N) ≅ ⨁_{i,j} k[x] ⧸ (fᵢ, gⱼ)`,
* `Torᵢ(M, N) = 0` for `i ≥ 2`.

This is the `Tor` answer part (ii) of the exercise asks for; `Etingof.Problem_8_2_7_ii_ext_fg` is
the `Ext` half. -/
theorem Problem_8_2_7_ii_tor_fg [Module.Finite k[X] M] [Module.Finite k[X] N] :
    ∃ (D : PIDDecomposition k[X] M) (E : PIDDecomposition k[X] N),
      Nonempty (Etingof.Tor k[X] N (mopOf k[X] M) 0 ≃+
        ∀ (j : D.index) (l : E.index), (k[X] ⧸ Ideal.span {D.genOf j, E.genOf l})) ∧
      Nonempty (Etingof.Tor k[X] N (mopOf k[X] M) 1 ≃+
        ∀ (i : D.torsionIndex) (l : E.torsionIndex),
          (k[X] ⧸ Ideal.span {D.gen i, E.gen l})) ∧
      ∀ n : ℕ, Subsingleton (Etingof.Tor k[X] N (mopOf k[X] M) (n + 2)) := by
  obtain ⟨D, hD⟩ := exists_pidDecomposition_gen_ne_zero k[X] M
  obtain ⟨E, hE⟩ := exists_pidDecomposition_gen_ne_zero k[X] N
  exact ⟨D, E, Problem_8_2_7_ii_tor_zero_fg D E, Problem_8_2_7_ii_tor_one_fg D E hD hE,
    fun n => Problem_8_2_7_ii_tor_fg_vanish N n⟩

/-! ### Non-vacuity check

The packaged endpoint elaborates for a concrete pair of finitely generated `ℚ[X]`-modules, so its
hypotheses are satisfiable. -/

section Examples

example : True := by
  have := Problem_8_2_7_ii_tor_fg (k := ℚ) (M := ℚ[X]) (N := ℚ[X])
  trivial

end Examples

end Etingof
