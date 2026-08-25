import EtingofRepresentationTheory.Chapter8.Problem8_2_7_ExtFG

/-!
# Problem 8.2.7(ii): `Extⁱ(M, N)` for arbitrary finitely generated `k[x]`-modules

This is the `k[x]` counterpart of `Problem8_2_7_ExtInt.lean`. `Problem8_2_7.lean` computes `Extⁱ`
for a pair of cyclic `k[x]`-modules and for a free generator, `Problem8_2_7_ExtFG.lean` reduces the
general case to those building blocks, and this file fills in the summand table over `k[x]` and
assembles the answer for **arbitrary** finitely generated `M`, `N`.

## The summand table

Every summand of a decomposition is `k[x] ⧸ (d)` (`Etingof.PIDDecomposition.summandIso`), the free
ones being `d = 0`. Writing `f` for the first argument's generator and `g` for the second's, and
`(f, g)` for the sum ideal `(f) ⊔ (g)` (which is `(gcd f g)`, since `k[x]` is a PID):

| | `Ext⁰` | `Ext¹` | `Extⁿ⁺²` |
|---|---|---|---|
| `f = 0` (free) | `k[x] ⧸ (g)` | `0` | `0` |
| `f ≠ 0`, `g = 0` | `0` | `k[x] ⧸ (f)` | `0` |
| `f ≠ 0`, `g ≠ 0` | `k[x] ⧸ (f, g)` | `k[x] ⧸ (f, g)` | `0` |

As over `ℤ`, the degree-`1` column is a *single* formula `k[x] ⧸ (f, g)` for `f ≠ 0` — indeed
`Problem_8_2_7_ii_ext_one` already has no hypothesis on `g`, since `(f, 0) = (f)`. In degree `0` the
entry at `f ≠ 0`, `g = 0` breaks the pattern: `Hom(k[x] ⧸ (f), k[x]) = 0` while `(f, 0) = (f)`.

## Main results

* `Etingof.Problem_8_2_7_ii_ext_zero_fg`:
  `Hom(M, N) = Ext⁰(M, N) ≅ N^p ⊕ ⨁_{i,l} k[x] ⧸ (fᵢ, g_l)`.
* `Etingof.Problem_8_2_7_ii_ext_one_fg`:
  `Ext¹(M, N) ≅ ⨁_{i,l} k[x] ⧸ (fᵢ, g_l)`, the product running over the torsion summands of `M` and
  **all** summands of `N` (the free ones contributing `k[x] ⧸ (fᵢ)`).
* `Etingof.Problem_8_2_7_ii_ext_fg_vanish`: `Extⁱ(M, N) = 0` for `i ≥ 2`, `N` arbitrary.
* `Etingof.Problem_8_2_7_ii_ext_fg`: the three answers packaged with the existence of suitable
  decompositions.
-/

universe u

namespace Etingof

open CategoryTheory Limits Polynomial

variable {k : Type u} [Field k]

/-! ### The summand table -/

/-- `Ext⁰(k[x], Z) = Hom(k[x], Z) ≅ Z`: the degree-`0` value at a free summand of `M`. -/
theorem Problem_8_2_7_ii_ext_free_zero (Z : ModuleCat.{u} k[X]) :
    Nonempty (Etingof.Ext (ModuleCat.of k[X] k[X]) Z 0 ≃+ Z) := by
  obtain ⟨e⟩ := Problem_8_2_6_i_ext k[X] (ModuleCat.of k[X] k[X]) Z
  exact ⟨e.trans (ModuleCat.homAddEquiv.trans (homSelfAddEquiv k[X] Z))⟩

/-- `Hom_{k[x]}(k[x] ⧸ (f), k[x]) = 0` for `f ≠ 0`: a torsion module has no nonzero map to a
torsion-free one. A map `ψ` is determined by `ψ [1]`, and `f • ψ [1] = ψ [f] = 0` forces
`ψ [1] = 0` because `k[x]` is a domain. -/
lemma subsingleton_hom_polyQuot_self (f : k[X]) (hf : f ≠ 0) :
    Subsingleton ((k[X] ⧸ Ideal.span {f}) →ₗ[k[X]] k[X]) := by
  have hzero : ∀ ψ : (k[X] ⧸ Ideal.span {f}) →ₗ[k[X]] k[X], ψ = 0 := by
    intro ψ
    have h1 : ψ (Submodule.Quotient.mk (1 : k[X])) = 0 := by
      have hf1 : f • ψ (Submodule.Quotient.mk (1 : k[X])) = 0 := by
        rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
          (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton_self f), map_zero]
      exact (smul_eq_zero.mp hf1).resolve_left hf
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {f}) x
    rw [show (Submodule.Quotient.mk y : k[X] ⧸ Ideal.span {f})
          = y • Submodule.Quotient.mk (1 : k[X]) from by
        rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one], map_smul, h1, smul_zero,
      LinearMap.zero_apply]
  exact ⟨fun ψ φ => by rw [hzero ψ, hzero φ]⟩

/-- `Ext⁰(k[x] ⧸ (f), k[x]) = 0` for `f ≠ 0`: the degree-`0` value at a torsion summand of `M`
paired with a *free* summand of `N`. This is the one entry of the table where the uniform
`k[x] ⧸ (f, g)` answer fails. -/
theorem Problem_8_2_7_ii_ext_cyclic_free_zero (f : k[X]) (hf : f ≠ 0) :
    Subsingleton (Etingof.Ext (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {f}))
      (ModuleCat.of k[X] k[X]) 0) := by
  haveI := subsingleton_hom_polyQuot_self f hf
  obtain ⟨e⟩ := Problem_8_2_6_i_ext k[X] (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {f}))
    (ModuleCat.of k[X] k[X])
  exact (e.trans ModuleCat.homAddEquiv).toEquiv.subsingleton

/-! ### The assembled answers -/

variable {M N : Type u} [AddCommGroup M] [Module k[X] M] [AddCommGroup N] [Module k[X] N]

/-- **Problem 8.2.7(ii), higher `Ext`.** `Extⁱ(M, N) = 0` for `i ≥ 2`, for `M` a finitely generated
`k[x]`-module and `N` an *arbitrary* one: `k[x]` is a PID, so every finitely generated module has
projective dimension `≤ 1` (`Etingof.fg_hasProjectiveDimensionLT_two`). -/
theorem Problem_8_2_7_ii_ext_fg_vanish [Module.Finite k[X] M] (Z : ModuleCat.{u} k[X]) (n : ℕ) :
    Subsingleton (Etingof.Ext (ModuleCat.of k[X] M) Z (n + 2)) := by
  haveI := fg_hasProjectiveDimensionLT_two k[X] M
  exact HasProjectiveDimensionLT.subsingleton (ModuleCat.of k[X] M) 2 (n + 2) (by omega) Z

/-- **Problem 8.2.7(ii), `Ext¹`.** `Ext¹(M, N) ≅ ⨁_{i,l} k[x] ⧸ (fᵢ, g_l)`, the product running
over the torsion summands `k[x] ⧸ (fᵢ)` of `M` and over **all** summands of `N`, the free ones
having `g_l = 0` and hence contributing `k[x] ⧸ (fᵢ, 0) = k[x] ⧸ (fᵢ)`. -/
theorem Problem_8_2_7_ii_ext_one_fg (D : PIDDecomposition k[X] M) (E : PIDDecomposition k[X] N)
    (hD : ∀ i, D.gen i ≠ 0) :
    Nonempty (Etingof.Ext (ModuleCat.of k[X] M) (ModuleCat.of k[X] N) 1 ≃+
      ∀ (i : D.torsionIndex) (l : E.index), (k[X] ⧸ Ideal.span {D.gen i, E.genOf l})) := by
  haveI : ∀ i : Fin D.freeRank,
      Subsingleton (Etingof.Ext (D.summand (Sum.inl i)) (ModuleCat.of k[X] N) 1) := fun _ =>
    Problem_8_2_7_ii_ext_free_vanish k (ModuleCat.of k[X] N) 0
  haveI := subsingleton_pi fun i : Fin D.freeRank =>
    Etingof.Ext (D.summand (Sum.inl i)) (ModuleCat.of k[X] N) 1
  refine ⟨(extFstDecompositionAddEquiv D (ModuleCat.of k[X] N) 1).trans
    (((piSumAddEquiv _).trans (subsingletonProdAddEquiv _ _)).trans
      (AddEquiv.piCongrRight fun i => ?_))⟩
  -- `D.summand (Sum.inr i)` *is* `k[x] ⧸ (fᵢ)`; only `N` has to be decomposed.
  refine (extSndDecompositionAddEquiv (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {D.gen i})) E 1).trans
    (AddEquiv.piCongrRight fun l => ?_)
  exact (extCongr (Iso.refl _) (E.summandIso l) 1).trans
    (Problem_8_2_7_ii_ext_one k (D.gen i) (E.genOf l) (hD i)).some

/-- **Problem 8.2.7(ii), `Ext⁰`.** `Ext⁰(M, N) = Hom(M, N) ≅ N^p ⊕ ⨁_{i,l} k[x] ⧸ (fᵢ, g_l)`, where
`p` is the free rank of `M` and the `fᵢ`, `g_l` are the torsion generators of `M` and `N`. The free
summands of `N` do not contribute to the torsion block, since
`Hom(k[x] ⧸ (fᵢ), k[x]) = 0`; their contribution sits in the `N^p` factor. -/
theorem Problem_8_2_7_ii_ext_zero_fg (D : PIDDecomposition k[X] M) (E : PIDDecomposition k[X] N)
    (hD : ∀ i, D.gen i ≠ 0) (hE : ∀ l, E.gen l ≠ 0) :
    Nonempty (Etingof.Ext (ModuleCat.of k[X] M) (ModuleCat.of k[X] N) 0 ≃+
      (Fin D.freeRank → N) ×
        ∀ (i : D.torsionIndex) (l : E.torsionIndex),
          (k[X] ⧸ Ideal.span {D.gen i, E.gen l})) := by
  refine ⟨(extFstDecompositionAddEquiv D (ModuleCat.of k[X] N) 0).trans
    ((piSumAddEquiv _).trans (AddEquiv.prodCongr (AddEquiv.piCongrRight fun _ => ?_)
      (AddEquiv.piCongrRight fun i => ?_)))⟩
  · exact (Problem_8_2_7_ii_ext_free_zero (ModuleCat.of k[X] N)).some
  · haveI : ∀ l : Fin E.freeRank,
        Subsingleton (Etingof.Ext (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {D.gen i}))
          (E.summand (Sum.inl l)) 0) := fun _ =>
      Problem_8_2_7_ii_ext_cyclic_free_zero (D.gen i) (hD i)
    haveI := subsingleton_pi fun l : Fin E.freeRank =>
      Etingof.Ext (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {D.gen i})) (E.summand (Sum.inl l)) 0
    refine (extSndDecompositionAddEquiv (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {D.gen i})) E 0).trans
      (((piSumAddEquiv _).trans (subsingletonProdAddEquiv _ _)).trans
        (AddEquiv.piCongrRight fun l => ?_))
    exact (Problem_8_2_7_ii_ext_zero k (D.gen i) (E.gen l) (hE l)).some

/-- **Problem 8.2.7(ii), packaged.** For any two finitely generated `k[x]`-modules `M`, `N` there
are decompositions `M ≅ k[x]^p ⊕ ⨁ᵢ k[x] ⧸ (fᵢ)` and `N ≅ k[x]^q ⊕ ⨁_l k[x] ⧸ (g_l)` (with all
`fᵢ`, `g_l` nonzero) for which `Ext⁰`, `Ext¹` are as above and `Extⁱ = 0` for `i ≥ 2`. -/
theorem Problem_8_2_7_ii_ext_fg [Module.Finite k[X] M] [Module.Finite k[X] N] :
    ∃ (D : PIDDecomposition k[X] M) (E : PIDDecomposition k[X] N),
      Nonempty (Etingof.Ext (ModuleCat.of k[X] M) (ModuleCat.of k[X] N) 0 ≃+
        (Fin D.freeRank → N) ×
          ∀ (i : D.torsionIndex) (l : E.torsionIndex),
            (k[X] ⧸ Ideal.span {D.gen i, E.gen l})) ∧
      Nonempty (Etingof.Ext (ModuleCat.of k[X] M) (ModuleCat.of k[X] N) 1 ≃+
        ∀ (i : D.torsionIndex) (l : E.index), (k[X] ⧸ Ideal.span {D.gen i, E.genOf l})) ∧
      ∀ n : ℕ, Subsingleton (Etingof.Ext (ModuleCat.of k[X] M) (ModuleCat.of k[X] N) (n + 2)) := by
  obtain ⟨D, hD⟩ := exists_pidDecomposition_gen_ne_zero k[X] M
  obtain ⟨E, hE⟩ := exists_pidDecomposition_gen_ne_zero k[X] N
  exact ⟨D, E, Problem_8_2_7_ii_ext_zero_fg D E hD hE, Problem_8_2_7_ii_ext_one_fg D E hD,
    fun n => Problem_8_2_7_ii_ext_fg_vanish (ModuleCat.of k[X] N) n⟩

/-! ### Non-vacuity check

The packaged endpoint elaborates for a concrete pair of finitely generated `ℚ[x]`-modules, so its
hypotheses are satisfiable. -/

example : True := by
  have := Problem_8_2_7_ii_ext_fg (k := ℚ) (M := ℚ[X]) (N := ℚ[X])
  trivial

end Etingof
