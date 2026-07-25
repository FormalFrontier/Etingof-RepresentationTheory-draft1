import EtingofRepresentationTheory.Chapter8.Problem8_2_7_ExtFG

/-!
# Problem 8.2.7(i): `Extⁱ(M, N)` for arbitrary finitely generated abelian groups

`Problem8_2_7.lean` computes `Extⁱ` for a pair of cyclic groups and for a free generator, and
`Problem8_2_7_ExtFG.lean` reduces the general case to those building blocks. This file completes
part (i) of the exercise: it fills in the summand-level table over `ℤ` and assembles the answer for
**arbitrary** finitely generated `M`, `N`.

## The summand table

Every summand of a decomposition is `ℤ ⧸ (d) ≅ ZMod d.natAbs` (`Etingof.intSummandIso`), the free
ones being `d = 0`, i.e. `ZMod 0 = ℤ`. Writing `a` for the first argument's modulus and `c` for the
second's:

| | `Ext⁰` | `Ext¹` | `Extⁿ⁺²` |
|---|---|---|---|
| `a = 0` (free) | `ZMod c` | `0` | `0` |
| `a ≠ 0`, `c = 0` | `0` | `ZMod a` | `0` |
| `a ≠ 0`, `c ≠ 0` | `ZMod (gcd a c)` | `ZMod (gcd a c)` | `0` |

In degree `1` the three rows are the *single* formula `ZMod (gcd a c)` for `a ≠ 0` (note
`gcd a 0 = a`), which is why `Problem_8_2_7_i_ext_one_fg` below has no case split over the free
summands of `N`. In degree `0` the entry at `a ≠ 0`, `c = 0` genuinely breaks the pattern:
`Hom(ℤ/a, ℤ) = 0` while `gcd a 0 = a ≠ 0`.

## Main results

* `Etingof.Problem_8_2_7_i_ext_zero_fg`:
  `Hom(M, N) = Ext⁰(M, N) ≅ N^p ⊕ ⨁_{i,l} ℤ/gcd(aᵢ, b_l)`, where `p` is the free rank of `M` and
  the `aᵢ`, `b_l` are the torsion generators of `M` and `N`.
* `Etingof.Problem_8_2_7_i_ext_one_fg`:
  `Ext¹(M, N) ≅ ⨁_{i, l} ℤ/gcd(aᵢ, c_l)`, the product running over the torsion summands of `M` and
  **all** summands of `N` (`c_l = 0` on the free ones, contributing `ℤ/aᵢ`).
* `Etingof.Problem_8_2_7_i_ext_fg_vanish`: `Extⁱ(M, N) = 0` for `i ≥ 2`, with `N` arbitrary.
* `Etingof.Problem_8_2_7_i_ext_one_intrinsic`: the coordinate-free form of the degree-`1` answer,
  `Ext¹(M, N) ≅ Π i, N / aᵢN`, valid for arbitrary (not necessarily finitely generated) `N`.
-/

universe u

namespace Etingof

open CategoryTheory Limits

/-! ### Identifying the summands with `ZMod` -/

/-- `ℤ ⧸ (d) ≅ ZMod d.natAbs`, for an arbitrary integer `d` — including `d = 0`, where both sides
are `ℤ`. This extends `Etingof.intCyclicIso`, which is stated for a natural-number generator. -/
noncomputable def intCyclicIsoNatAbs (d : ℤ) :
    ModuleCat.of ℤ (ℤ ⧸ Ideal.span {d}) ≅ ModuleCat.of ℤ (ZMod d.natAbs) :=
  have hspan : Ideal.span {d} = Ideal.span {(d.natAbs : ℤ)} :=
    le_antisymm
      (Ideal.span_le.mpr (by
        simp only [Set.singleton_subset_iff, SetLike.mem_coe]
        exact Ideal.mem_span_singleton.mpr (Int.natAbs_dvd.mpr dvd_rfl)))
      (Ideal.span_le.mpr (by
        simp only [Set.singleton_subset_iff, SetLike.mem_coe]
        exact Ideal.mem_span_singleton.mpr (Int.dvd_natAbs.mpr dvd_rfl)))
  LinearEquiv.toModuleIso (Submodule.quotEquivOfEq _ _ hspan) ≪≫ intCyclicIso d.natAbs

/-- **Every summand of a decomposition of a finitely generated abelian group is a `ZMod`.** The
free summands are `ZMod 0 = ℤ`; this is the uniform shape the `ZModGcd` building blocks of
`Problem8_2_7.lean` are stated for. -/
noncomputable def intSummandIso {M : Type} [AddCommGroup M] (D : PIDDecomposition ℤ M)
    (j : D.index) : D.summand j ≅ ModuleCat.of ℤ (ZMod (D.genOf j).natAbs) :=
  D.summandIso j ≪≫ intCyclicIsoNatAbs (D.genOf j)

/-! ### The summand table -/

/-- `Ext⁰(ℤ, Z) = Hom(ℤ, Z) ≅ Z` for any abelian group `Z`: the degree-`0` value at a free summand
of `M`. -/
theorem Problem_8_2_7_i_ext_free_zero (Z : ModuleCat.{0} ℤ) :
    Nonempty (Etingof.Ext (ModuleCat.of ℤ ℤ) Z 0 ≃+ Z) := by
  obtain ⟨e⟩ := Problem_8_2_6_i_ext ℤ (ModuleCat.of ℤ ℤ) Z
  exact ⟨e.trans (ModuleCat.homAddEquiv.trans (homSelfAddEquiv ℤ Z))⟩

/-- `Ext⁰(ℤ/a, ℤ) = Hom(ℤ/a, ℤ) = 0` for `a ≠ 0`: the degree-`0` value at a torsion summand of `M`
paired with a *free* summand of `N`. This is the one entry of the table where the uniform
`ZMod (gcd a c)` answer fails. -/
theorem Problem_8_2_7_i_ext_cyclic_free_zero (a : ℕ) (ha : a ≠ 0) :
    Subsingleton (Etingof.Ext (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ ℤ) 0) := by
  haveI : NeZero a := ⟨ha⟩
  haveI := ZModGcd.subsingleton_hom_zmod_int a
  obtain ⟨e⟩ := Problem_8_2_6_i_ext ℤ (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ ℤ)
  exact (e.trans ModuleCat.homAddEquiv).toEquiv.subsingleton

/-- **`Ext¹(ℤ/a, ℤ/c) ≅ ℤ/gcd(a, c)` for `a ≠ 0` and every `c`, including `c = 0`.** For `c ≠ 0`
this is `Problem_8_2_7_i_ext_one`; for `c = 0` it says `Ext¹(ℤ/a, ℤ) ≅ ℤ/a`, which is the same
cokernel computation (`Etingof.ext_one_zmod_quotSMul`) with `ℤ ⧸ (a) ≅ ZMod a` at the end, and
`gcd a 0 = a`. -/
theorem Problem_8_2_7_i_ext_one_cyclic (a c : ℕ) (ha : a ≠ 0) :
    Nonempty (Etingof.Ext (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ (ZMod c)) 1
      ≃+ ZMod (Nat.gcd a c)) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [Nat.gcd_zero_right]
    obtain ⟨e⟩ := ext_one_zmod_quotSMul a ha ℤ
    have h : Ideal.span {(a : ℤ)} • (⊤ : Submodule ℤ ℤ) = (Ideal.span {(a : ℤ)} : Ideal ℤ) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact ⟨e.trans ((Submodule.quotEquivOfEq _ _ h).toAddEquiv.trans
      (Int.quotientSpanNatEquivZMod a).toAddEquiv)⟩
  · exact Problem_8_2_7_i_ext_one a c ha hc

/-! ### The assembled answers -/

variable {M N : Type} [AddCommGroup M] [AddCommGroup N]

/-- **Problem 8.2.7(i), higher `Ext`.** `Extⁱ(M, N) = 0` for `i ≥ 2`, for `M` a finitely generated
abelian group and `N` an *arbitrary* one: every finitely generated abelian group has projective
dimension `≤ 1` (`Etingof.fg_hasProjectiveDimensionLT_two`). -/
theorem Problem_8_2_7_i_ext_fg_vanish [Module.Finite ℤ M] (Z : ModuleCat.{0} ℤ) (n : ℕ) :
    Subsingleton (Etingof.Ext (ModuleCat.of ℤ M) Z (n + 2)) := by
  haveI := fg_hasProjectiveDimensionLT_two ℤ M
  exact HasProjectiveDimensionLT.subsingleton (ModuleCat.of ℤ M) 2 (n + 2) (by omega) Z

/-- **Problem 8.2.7(i), `Ext¹`, coordinate-free form.** `Ext¹(M, N) ≅ Π i, N / aᵢN`, where the
`aᵢ` are the torsion generators of a decomposition of `M`. `N` is arbitrary — it need not be
finitely generated, since only `M` is decomposed. -/
theorem Problem_8_2_7_i_ext_one_intrinsic (D : PIDDecomposition ℤ M) (hD : ∀ i, D.gen i ≠ 0) :
    Nonempty (Etingof.Ext (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) 1 ≃+
      ∀ i : D.torsionIndex,
        (N ⧸ Ideal.span {((D.gen i).natAbs : ℤ)} • (⊤ : Submodule ℤ N))) := by
  -- Split off the free summands of `M`, on which `Ext¹` vanishes.
  haveI : ∀ i : Fin D.freeRank,
      Subsingleton (Etingof.Ext (D.summand (Sum.inl i)) (ModuleCat.of ℤ N) 1) := fun _ =>
    Problem_8_2_7_i_ext_free_vanish (ModuleCat.of ℤ N) 0
  haveI := subsingleton_pi fun i : Fin D.freeRank =>
    Etingof.Ext (D.summand (Sum.inl i)) (ModuleCat.of ℤ N) 1
  -- On a torsion summand `ℤ/aᵢ`, `Ext¹(ℤ/aᵢ, N)` is the cokernel of multiplication by `aᵢ`.
  refine ⟨(extFstDecompositionAddEquiv D (ModuleCat.of ℤ N) 1).trans
    (((piSumAddEquiv _).trans (subsingletonProdAddEquiv _ _)).trans
      (AddEquiv.piCongrRight fun i => ?_))⟩
  have hne : (D.gen i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hD i)
  exact (extCongr (intSummandIso D (Sum.inr i)) (Iso.refl _) 1).trans
    (ext_one_zmod_quotSMul (D.gen i).natAbs hne N).some

/-- **Problem 8.2.7(i), `Ext¹`.** `Ext¹(M, N) ≅ ⨁_{i, l} ℤ/gcd(aᵢ, c_l)` for finitely generated
abelian groups `M`, `N`: the product runs over the torsion summands `ℤ/aᵢ` of `M` and over **all**
summands of `N`, the free ones contributing `c_l = 0` and hence `ℤ/gcd(aᵢ, 0) = ℤ/aᵢ`. So in the
notation of the exercise, with `N ≅ ℤ^q ⊕ ⨁_l ℤ/b_l`,
`Ext¹(M, N) ≅ (⨁_{i,l} ℤ/gcd(aᵢ, b_l)) ⊕ (⨁_i ℤ/aᵢ)^q`. -/
theorem Problem_8_2_7_i_ext_one_fg (D : PIDDecomposition ℤ M) (E : PIDDecomposition ℤ N)
    (hD : ∀ i, D.gen i ≠ 0) :
    Nonempty (Etingof.Ext (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) 1 ≃+
      ∀ (i : D.torsionIndex) (l : E.index),
        ZMod (Nat.gcd (D.gen i).natAbs (E.genOf l).natAbs)) := by
  haveI : ∀ i : Fin D.freeRank,
      Subsingleton (Etingof.Ext (D.summand (Sum.inl i)) (ModuleCat.of ℤ N) 1) := fun _ =>
    Problem_8_2_7_i_ext_free_vanish (ModuleCat.of ℤ N) 0
  haveI := subsingleton_pi fun i : Fin D.freeRank =>
    Etingof.Ext (D.summand (Sum.inl i)) (ModuleCat.of ℤ N) 1
  refine ⟨(extFstDecompositionAddEquiv D (ModuleCat.of ℤ N) 1).trans
    (((piSumAddEquiv _).trans (subsingletonProdAddEquiv _ _)).trans
      (AddEquiv.piCongrRight fun i => ?_))⟩
  have hne : (D.gen i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hD i)
  -- Identify the source with `ZMod aᵢ`, then decompose the second argument.
  refine (extCongr (intSummandIso D (Sum.inr i)) (Iso.refl _) 1).trans
    ((extSndDecompositionAddEquiv (ModuleCat.of ℤ (ZMod (D.gen i).natAbs)) E 1).trans
      (AddEquiv.piCongrRight fun l => ?_))
  exact (extCongr (Iso.refl _) (intSummandIso E l) 1).trans
    (Problem_8_2_7_i_ext_one_cyclic (D.gen i).natAbs (E.genOf l).natAbs hne).some

/-- **Problem 8.2.7(i), `Ext⁰`.** `Ext⁰(M, N) = Hom(M, N) ≅ N^p ⊕ ⨁_{i,l} ℤ/gcd(aᵢ, b_l)`, where
`p` is the free rank of `M`, the `aᵢ` are the torsion generators of `M` and the `b_l` those of `N`.
Unlike in degree `1`, the free summands of `N` do *not* contribute to the torsion block:
`Hom(ℤ/aᵢ, ℤ) = 0` (`Problem_8_2_7_i_ext_cyclic_free_zero`); their contribution is inside the `N^p`
factor coming from `Hom(ℤ, N) ≅ N`. -/
theorem Problem_8_2_7_i_ext_zero_fg (D : PIDDecomposition ℤ M) (E : PIDDecomposition ℤ N)
    (hD : ∀ i, D.gen i ≠ 0) (hE : ∀ l, E.gen l ≠ 0) :
    Nonempty (Etingof.Ext (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) 0 ≃+
      (Fin D.freeRank → N) ×
        ∀ (i : D.torsionIndex) (l : E.torsionIndex),
          ZMod (Nat.gcd (D.gen i).natAbs (E.gen l).natAbs)) := by
  refine ⟨(extFstDecompositionAddEquiv D (ModuleCat.of ℤ N) 0).trans
    ((piSumAddEquiv _).trans (AddEquiv.prodCongr (AddEquiv.piCongrRight fun _ => ?_)
      (AddEquiv.piCongrRight fun i => ?_)))⟩
  · -- free summand of `M`: `Hom(ℤ, N) ≅ N`
    exact (Problem_8_2_7_i_ext_free_zero (ModuleCat.of ℤ N)).some
  · -- torsion summand `ℤ/aᵢ` of `M`: decompose `N` and drop the free block
    have hne : (D.gen i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hD i)
    haveI : NeZero (D.gen i).natAbs := ⟨hne⟩
    haveI : ∀ l : Fin E.freeRank,
        Subsingleton (Etingof.Ext (ModuleCat.of ℤ (ZMod (D.gen i).natAbs))
          (E.summand (Sum.inl l)) 0) := fun _ =>
      Problem_8_2_7_i_ext_cyclic_free_zero (D.gen i).natAbs hne
    haveI := subsingleton_pi fun l : Fin E.freeRank =>
      Etingof.Ext (ModuleCat.of ℤ (ZMod (D.gen i).natAbs)) (E.summand (Sum.inl l)) 0
    refine (extCongr (intSummandIso D (Sum.inr i)) (Iso.refl _) 0).trans
      ((extSndDecompositionAddEquiv (ModuleCat.of ℤ (ZMod (D.gen i).natAbs)) E 0).trans
        (((piSumAddEquiv _).trans (subsingletonProdAddEquiv _ _)).trans
          (AddEquiv.piCongrRight fun l => ?_)))
    exact (extCongr (Iso.refl _) (intSummandIso E (Sum.inr l)) 0).trans
      (Problem_8_2_7_i_ext_zero (D.gen i).natAbs (E.gen l).natAbs hne
        (Int.natAbs_ne_zero.mpr (hE l))).some

/-- **Problem 8.2.7(i), packaged.** For any two finitely generated abelian groups `M`, `N` there
are decompositions `M ≅ ℤ^p ⊕ ⨁ᵢ ℤ/aᵢ` and `N ≅ ℤ^q ⊕ ⨁_l ℤ/b_l` (with all `aᵢ`, `b_l` nonzero)
for which

* `Ext⁰(M, N) = Hom(M, N) ≅ N^p ⊕ ⨁_{i,l} ℤ/gcd(aᵢ, b_l)`,
* `Ext¹(M, N) ≅ ⨁_{i} ⨁_{l ∈ all summands of N} ℤ/gcd(aᵢ, c_l)`
  `= (⨁_{i,l} ℤ/gcd(aᵢ, b_l)) ⊕ (⨁ᵢ ℤ/aᵢ)^q`,
* `Extⁱ(M, N) = 0` for `i ≥ 2`.

This is the answer the exercise asks for. -/
theorem Problem_8_2_7_i_ext_fg [Module.Finite ℤ M] [Module.Finite ℤ N] :
    ∃ (D : PIDDecomposition ℤ M) (E : PIDDecomposition ℤ N),
      Nonempty (Etingof.Ext (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) 0 ≃+
        (Fin D.freeRank → N) ×
          ∀ (i : D.torsionIndex) (l : E.torsionIndex),
            ZMod (Nat.gcd (D.gen i).natAbs (E.gen l).natAbs)) ∧
      Nonempty (Etingof.Ext (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) 1 ≃+
        ∀ (i : D.torsionIndex) (l : E.index),
          ZMod (Nat.gcd (D.gen i).natAbs (E.genOf l).natAbs)) ∧
      ∀ n : ℕ, Subsingleton (Etingof.Ext (ModuleCat.of ℤ M) (ModuleCat.of ℤ N) (n + 2)) := by
  obtain ⟨D, hD⟩ := exists_pidDecomposition_gen_ne_zero ℤ M
  obtain ⟨E, hE⟩ := exists_pidDecomposition_gen_ne_zero ℤ N
  exact ⟨D, E, Problem_8_2_7_i_ext_zero_fg D E hD hE, Problem_8_2_7_i_ext_one_fg D E hD,
    fun n => Problem_8_2_7_i_ext_fg_vanish (ModuleCat.of ℤ N) n⟩

/-! ### Non-vacuity checks

The summand-level degree-`1` formula gives `Ext¹(ℤ/6, ℤ/4) ≅ ℤ/2` and, at a free second argument,
`Ext¹(ℤ/6, ℤ) ≅ ℤ/6` (`ZMod 0 = ℤ`, `gcd 6 0 = 6`); and the packaged endpoint elaborates for a
concrete pair of finitely generated groups, so its hypotheses are satisfiable. -/

section Examples

example : Nonempty (Etingof.Ext (ModuleCat.of ℤ (ZMod 6)) (ModuleCat.of ℤ (ZMod 4)) 1
    ≃+ ZMod 2) := by
  have h := Problem_8_2_7_i_ext_one_cyclic 6 4 (by norm_num)
  rwa [show Nat.gcd 6 4 = 2 from by norm_num] at h

example : Nonempty (Etingof.Ext (ModuleCat.of ℤ (ZMod 6)) (ModuleCat.of ℤ (ZMod 0)) 1
    ≃+ ZMod 6) := by
  have h := Problem_8_2_7_i_ext_one_cyclic 6 0 (by norm_num)
  rwa [Nat.gcd_zero_right] at h

example : True := by
  have := Problem_8_2_7_i_ext_fg (M := ZMod 6) (N := ℤ × ZMod 4)
  trivial

end Examples

end Etingof
