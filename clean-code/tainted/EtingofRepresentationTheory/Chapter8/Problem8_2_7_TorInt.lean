import EtingofRepresentationTheory.Chapter8.Problem8_2_7_TorFG
import EtingofRepresentationTheory.Chapter8.Problem8_2_7_ExtInt

/-!
# Problem 8.2.7(i): `Torᵢ(M, N)` for arbitrary finitely generated abelian groups

`Problem8_2_7.lean` computes `Torᵢ` for a pair of cyclic groups and for a free generator, and
`Problem8_2_7_TorFG.lean` reduces the general case to those building blocks. This file completes
the `Tor` half of part (i): it fills in the summand-level table over `ℤ` and assembles the answer
for **arbitrary** finitely generated `M`, `N`.

## The summand table

Every summand of a decomposition is `ℤ ⧸ (d) ≅ ZMod d.natAbs` (`Etingof.intSummandIso`), the free
ones being `d = 0`, i.e. `ZMod 0 = ℤ`. Writing `a` for the first argument's modulus and `c` for the
second's:

| | `Tor₀` | `Tor₁` | `Torₙ₊₂` |
|---|---|---|---|
| `a = 0` (free) | `ZMod c` | `0` | `0` |
| `a ≠ 0`, `c = 0` | `ZMod a` | `0` | `0` |
| `a ≠ 0`, `c ≠ 0` | `ZMod (gcd a c)` | `ZMod (gcd a c)` | `0` |

**Degree `0` is completely uniform**: `Tor₀` is the tensor product, and `ZMod (gcd a c)` is correct
in all three rows, since `gcd a 0 = a`, `gcd 0 c = c` and `ZMod 0 = ℤ`. So
`Problem_8_2_7_i_tor_zero_fg` below is a single product over *all* pairs of summands, with no case
split at all. **Degree `1` is where the free summands drop out**, on either side: `Tor₁(ℤ, N) = 0`
because `ℤ` is projective, and `Tor₁(ℤ/a, ℤ) = 0` because `ℤ` is torsion-free — even though
`gcd a 0 = a ≠ 0`.

This is exactly opposite to the `Ext` side (`Problem8_2_7_ExtInt.lean`), where degree `1` is the
uniform row and degree `0` is the one that breaks: `Ext¹(ℤ/a, -)` is the *cokernel* of `·a` and
`Tor₁(ℤ/a, -)` its *kernel*, and it is the kernel that vanishes on the torsion-free group `ℤ`.

## Main results

* `Etingof.Problem_8_2_7_i_tor_zero_fg`:
  `M ⊗ N = Tor₀(M, N) ≅ ⨁_{j,l} ℤ/gcd(aⱼ, c_l)` over all pairs of summands. In the notation of
  the exercise, with `M ≅ ℤ^m ⊕ ⨁ᵢ ℤ/aᵢ` and `N ≅ ℤ^p ⊕ ⨁ⱼ ℤ/bⱼ`, this is
  `ℤ^{mp} ⊕ (⨁ᵢ ℤ/aᵢ)^p ⊕ (⨁ⱼ ℤ/bⱼ)^m ⊕ ⨁_{i,j} ℤ/gcd(aᵢ, bⱼ)`.
* `Etingof.Problem_8_2_7_i_tor_one_fg`: `Tor₁(M, N) ≅ ⨁_{i,j} ℤ/gcd(aᵢ, bⱼ)`, over the *torsion*
  summands of both arguments only.
* `Etingof.Problem_8_2_7_i_tor_fg_vanish`: `Torᵢ(M, N) = 0` for `i ≥ 2`, with `N` arbitrary.
* `Etingof.Problem_8_2_7_i_tor_fg`: the three answers packaged with the existence of suitable
  decompositions.
-/

namespace Etingof

open CategoryTheory Limits

attribute [local instance] mopZMod

/-! ### The summand table -/

/-- **`ZMod c ⧸ a·ZMod c ≃+ ZMod (gcd a c)` for every `a` and every `c`**, including `c = 0`, where
`ZMod 0 = ℤ` and `ℤ ⧸ aℤ = ZMod a = ZMod (gcd a 0)`. This extends `Etingof.ZModGcd.zmodCokerEquiv`,
which assumes `c ≠ 0`. -/
theorem zmod_quotSMul_equiv (a c : ℕ) :
    Nonempty ((ZMod c ⧸ (Ideal.span {(a : ℤ)} • (⊤ : Submodule ℤ (ZMod c))))
      ≃+ ZMod (Nat.gcd a c)) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [Nat.gcd_zero_right]
    have h : Ideal.span {(a : ℤ)} • (⊤ : Submodule ℤ ℤ) = (Ideal.span {(a : ℤ)} : Ideal ℤ) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact ⟨(Submodule.quotEquivOfEq _ _ h).toAddEquiv.trans
      (Int.quotientSpanNatEquivZMod a).toAddEquiv⟩
  · haveI : NeZero c := ⟨hc⟩
    exact ⟨(ZModGcd.zmodCokerEquiv a c).toAddEquiv⟩

/-- **`Tor₀(ℤ/a, ℤ/c) ≅ ℤ/gcd(a, c)` for every `a` and `c`**, including the free cases `a = 0` and
`c = 0` (`ZMod 0 = ℤ`, `gcd a 0 = a`, `gcd 0 c = c`). Degree `0` is the tensor product
`(ℤ ⧸ (a)) ⊗_ℤ ℤ/c ≅ (ℤ/c) ⧸ a(ℤ/c)` (`Etingof.tor_zero_zmod_quotSMul`), and there the gcd formula
needs no case split — unlike degree `1`, where a free summand on either side contributes `0`. -/
theorem Problem_8_2_7_i_tor_zero_cyclic (a c : ℕ) :
    Nonempty (Etingof.Tor ℤ (ZMod c) (ModuleCat.of ℤᵐᵒᵖ (ZMod a)) 0
      ≅ AddCommGrpCat.of (ZMod (Nat.gcd a c))) := by
  obtain ⟨e⟩ := tor_zero_zmod_quotSMul a (ZMod c)
  obtain ⟨e'⟩ := zmod_quotSMul_equiv a c
  exact ⟨e ≪≫ e'.toAddCommGrpIso⟩

/-! ### Identifying the summands

The `Tor` groups of Problem 8.2.7 take their first argument in `ModuleCat ℤᵐᵒᵖ` and their second as
a plain module, so each summand of a decomposition has to be identified in two different shapes. -/

/-- Every summand of a decomposition, viewed as a **right** `ℤ`-module, is `ZMod (genOf j).natAbs`
— the shape the `Tor` building blocks of `Problem8_2_7.lean` are stated for. The free summands are
`ZMod 0 = ℤ`. -/
noncomputable def mopIntSummandIso {M : Type} [AddCommGroup M] (D : PIDDecomposition ℤ M)
    (j : D.index) : D.mopSummand j ≅ ModuleCat.of ℤᵐᵒᵖ (ZMod (D.genOf j).natAbs) :=
  (mopFunctor ℤ).mapIso (intSummandIso D j)

/-- Every summand of a decomposition, as a plain `ℤ`-module, is `ZMod (genOf l).natAbs`: the
`LinearEquiv` form of `Etingof.intSummandIso`, needed because `Tor` takes its second argument as a
bare module rather than as an object of `ModuleCat ℤ`. -/
noncomputable def intSummandLinearEquiv {N : Type} [AddCommGroup N] (E : PIDDecomposition ℤ N)
    (l : E.index) : (E.summand l : Type) ≃ₗ[ℤ] ZMod (E.genOf l).natAbs :=
  (intSummandIso E l).toLinearEquiv

/-! ### The assembled answers -/

variable {M N : Type} [AddCommGroup M] [AddCommGroup N]

/-- **Problem 8.2.7(i), higher `Tor`.** `Torᵢ(M, N) = 0` for `i ≥ 2`, for `M` a finitely generated
abelian group and `N` an *arbitrary* one: `M` is a finite direct sum of cyclic groups, and higher
`Tor` out of a cyclic group vanishes for an arbitrary second argument
(`Etingof.tor_vanish_zmod`). -/
theorem Problem_8_2_7_i_tor_fg_vanish [Module.Finite ℤ M] (Y : Type) [AddCommGroup Y] (n : ℕ) :
    Subsingleton (Etingof.Tor ℤ Y (mopOf ℤ M) (n + 2)) := by
  obtain ⟨D⟩ := exists_pidDecomposition ℤ M
  refine subsingleton_tor_of_summands D Y (n + 2) fun j => ?_
  exact AddCommGrpCat.subsingleton_of_isZero
    ((tor_vanish_zmod (D.genOf j).natAbs Y n).of_iso (torFstCongr Y (mopIntSummandIso D j) (n + 2)))

/-- **Problem 8.2.7(i), `Tor₀`.** `M ⊗_ℤ N = Tor₀(M, N) ≅ ⨁_{j,l} ℤ/gcd(aⱼ, c_l)`, the product
running over **all** pairs of summands of `M` and `N` — free ones included, where the generator is
`0` and `ZMod 0 = ℤ`. With `M ≅ ℤ^m ⊕ ⨁ᵢ ℤ/aᵢ` and `N ≅ ℤ^p ⊕ ⨁ⱼ ℤ/bⱼ`, expanding the four blocks
of the product gives the form stated in the exercise,
`ℤ^{mp} ⊕ (⨁ᵢ ℤ/aᵢ)^p ⊕ (⨁ⱼ ℤ/bⱼ)^m ⊕ ⨁_{i,j} ℤ/gcd(aᵢ, bⱼ)`. -/
theorem Problem_8_2_7_i_tor_zero_fg (D : PIDDecomposition ℤ M) (E : PIDDecomposition ℤ N) :
    Nonempty (Etingof.Tor ℤ N (mopOf ℤ M) 0 ≃+
      ∀ (j : D.index) (l : E.index),
        ZMod (Nat.gcd (D.genOf j).natAbs (E.genOf l).natAbs)) := by
  refine ⟨(torPIDDecompositionAddEquiv D E 0).trans
    (AddEquiv.piCongrRight fun j => AddEquiv.piCongrRight fun l => ?_)⟩
  exact ((torSndCongr (intSummandLinearEquiv E l) (D.mopSummand j) 0) ≪≫
    (torFstCongr (ZMod (E.genOf l).natAbs) (mopIntSummandIso D j) 0) ≪≫
    (Problem_8_2_7_i_tor_zero_cyclic (D.genOf j).natAbs
      (E.genOf l).natAbs).some).addCommGroupIsoToAddEquiv

/-- **Problem 8.2.7(i), `Tor₁`.** `Tor₁(M, N) ≅ ⨁_{i,j} ℤ/gcd(aᵢ, bⱼ)`, the product running over
the **torsion** summands of `M` and of `N` only. Both free blocks drop out: `Tor₁(ℤ, N) = 0` since
`ℤ` is projective (`Problem_8_2_7_i_tor_free_vanish`), and `Tor₁(ℤ/aᵢ, ℤ) = 0` since `ℤ` is
torsion-free (`Problem_8_2_7_i_tor_cyclic_free_one`). -/
theorem Problem_8_2_7_i_tor_one_fg (D : PIDDecomposition ℤ M) (E : PIDDecomposition ℤ N)
    (hD : ∀ i, D.gen i ≠ 0) (hE : ∀ l, E.gen l ≠ 0) :
    Nonempty (Etingof.Tor ℤ N (mopOf ℤ M) 1 ≃+
      ∀ (i : D.torsionIndex) (l : E.torsionIndex),
        ZMod (Nat.gcd (D.gen i).natAbs (E.gen l).natAbs)) := by
  -- Split off the free summands of `M`, on which `Tor₁` vanishes.
  haveI : ∀ i : Fin D.freeRank,
      Subsingleton (Etingof.Tor ℤ N (D.mopSummand (Sum.inl i)) 1) := fun _ =>
    AddCommGrpCat.subsingleton_of_isZero
      ((Problem_8_2_7_i_tor_free_vanish N 0).of_iso (torFstCongr N (mopSelfIso ℤ) 1))
  haveI := subsingleton_pi fun i : Fin D.freeRank =>
    (Etingof.Tor ℤ N (D.mopSummand (Sum.inl i)) 1 : Type)
  refine ⟨(torFstDecompositionAddEquiv D N 1).trans
    (((piSumAddEquiv _).trans (subsingletonProdAddEquiv _ _)).trans
      (AddEquiv.piCongrRight fun i => ?_))⟩
  have hne : (D.gen i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hD i)
  -- Identify the first argument with `ZMod aᵢ`, then decompose `N` and drop *its* free block.
  refine (torFstCongr N (mopIntSummandIso D (Sum.inr i)) 1).addCommGroupIsoToAddEquiv.trans ?_
  haveI : ∀ l : Fin E.freeRank,
      Subsingleton (Etingof.Tor ℤ (E.summand (Sum.inl l))
        (ModuleCat.of ℤᵐᵒᵖ (ZMod (D.genOf (Sum.inr i)).natAbs)) 1) := fun _ =>
    AddCommGrpCat.subsingleton_of_isZero (Problem_8_2_7_i_tor_cyclic_free_one _ hne)
  haveI := subsingleton_pi fun l : Fin E.freeRank =>
    (Etingof.Tor ℤ (E.summand (Sum.inl l))
      (ModuleCat.of ℤᵐᵒᵖ (ZMod (D.genOf (Sum.inr i)).natAbs)) 1 : Type)
  refine (torSndDecompositionAddEquiv E _ 1).trans
    (((piSumAddEquiv _).trans (subsingletonProdAddEquiv _ _)).trans
      (AddEquiv.piCongrRight fun l => ?_))
  exact ((torSndCongr (intSummandLinearEquiv E (Sum.inr l)) _ 1) ≪≫
    (Problem_8_2_7_i_tor_one (D.gen i).natAbs (E.gen l).natAbs hne
      (Int.natAbs_ne_zero.mpr (hE l))).some).addCommGroupIsoToAddEquiv

/-- **Problem 8.2.7(i), `Tor`, packaged.** For any two finitely generated abelian groups `M`, `N`
there are decompositions `M ≅ ℤ^m ⊕ ⨁ᵢ ℤ/aᵢ` and `N ≅ ℤ^p ⊕ ⨁ⱼ ℤ/bⱼ` (with all `aᵢ`, `bⱼ` nonzero)
for which

* `Tor₀(M, N) = M ⊗ N ≅ ⨁_{j,l ∈ all summands} ℤ/gcd(aⱼ, c_l)`
  `= ℤ^{mp} ⊕ (⨁ᵢ ℤ/aᵢ)^p ⊕ (⨁ⱼ ℤ/bⱼ)^m ⊕ ⨁_{i,j} ℤ/gcd(aᵢ, bⱼ)`,
* `Tor₁(M, N) ≅ ⨁_{i,j} ℤ/gcd(aᵢ, bⱼ)`,
* `Torᵢ(M, N) = 0` for `i ≥ 2`.

This is the `Tor` answer the exercise asks for; `Etingof.Problem_8_2_7_i_ext_fg` is the `Ext`
half. -/
theorem Problem_8_2_7_i_tor_fg [Module.Finite ℤ M] [Module.Finite ℤ N] :
    ∃ (D : PIDDecomposition ℤ M) (E : PIDDecomposition ℤ N),
      Nonempty (Etingof.Tor ℤ N (mopOf ℤ M) 0 ≃+
        ∀ (j : D.index) (l : E.index),
          ZMod (Nat.gcd (D.genOf j).natAbs (E.genOf l).natAbs)) ∧
      Nonempty (Etingof.Tor ℤ N (mopOf ℤ M) 1 ≃+
        ∀ (i : D.torsionIndex) (l : E.torsionIndex),
          ZMod (Nat.gcd (D.gen i).natAbs (E.gen l).natAbs)) ∧
      ∀ n : ℕ, Subsingleton (Etingof.Tor ℤ N (mopOf ℤ M) (n + 2)) := by
  obtain ⟨D, hD⟩ := exists_pidDecomposition_gen_ne_zero ℤ M
  obtain ⟨E, hE⟩ := exists_pidDecomposition_gen_ne_zero ℤ N
  exact ⟨D, E, Problem_8_2_7_i_tor_zero_fg D E, Problem_8_2_7_i_tor_one_fg D E hD hE,
    fun n => Problem_8_2_7_i_tor_fg_vanish N n⟩

/-! ### Non-vacuity checks

The summand-level table gives `Tor₀(ℤ/6, ℤ/4) ≅ ℤ/2` and, at a free second argument,
`Tor₀(ℤ/6, ℤ) ≅ ℤ/6` (`ZMod 0 = ℤ`, `gcd 6 0 = 6`) while `Tor₁(ℤ/6, ℤ) = 0`; and the packaged
endpoint elaborates for a concrete pair of finitely generated groups, so its hypotheses are
satisfiable. -/

section Examples

example : Nonempty (Etingof.Tor ℤ (ZMod 4) (ModuleCat.of ℤᵐᵒᵖ (ZMod 6)) 0
    ≅ AddCommGrpCat.of (ZMod 2)) := by
  have h := Problem_8_2_7_i_tor_zero_cyclic 6 4
  rwa [show Nat.gcd 6 4 = 2 from by norm_num] at h

example : Nonempty (Etingof.Tor ℤ (ZMod 0) (ModuleCat.of ℤᵐᵒᵖ (ZMod 6)) 0
    ≅ AddCommGrpCat.of (ZMod 6)) := by
  have h := Problem_8_2_7_i_tor_zero_cyclic 6 0
  rwa [Nat.gcd_zero_right] at h

example : Limits.IsZero (Etingof.Tor ℤ ℤ (ModuleCat.of ℤᵐᵒᵖ (ZMod 6)) 1) :=
  Problem_8_2_7_i_tor_cyclic_free_one 6 (by norm_num)

example : True := by
  have := Problem_8_2_7_i_tor_fg (M := ZMod 6) (N := ℤ × ZMod 4)
  trivial

end Examples

end Etingof
