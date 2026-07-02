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
  finite-length indecomposable module is local. This is the abstract input (Krull-Schmidt-Azumaya)
  that drives the uniqueness half of Krull-Schmidt.
* `Etingof.exists_indecomposable_decomposition` — the **existence** half: every finite-length
  module decomposes as an internal direct sum of indecomposable submodules, by induction on
  `Module.length`.

The finite-length hypothesis is genuinely more general than the finite-dimensional-over-a-field
setting of Theorem 3.8.1: there is no ground field here, only the ring `A`.

The **uniqueness** half — that any two such decompositions agree up to isomorphism and reordering
— is the Krull-Schmidt-Azumaya exchange argument built on the local endomorphism rings above; it is
the analogue of `Etingof.krull_schmidt_uniqueness` (Theorem 3.8.1) with `Module.length` in place of
the `k`-dimension, and is left as follow-up work.
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

/-- Auxiliary lemma for existence: every submodule `S` of a finite-length module admits an internal
direct-sum decomposition into indecomposable submodules. Proved by induction on `Module.length`.

This mirrors the finite-dimensional existence argument of Theorem 3.8.1, with the composition
length `Module.length A ↥S` replacing the `k`-dimension as the strictly-decreasing induction
measure — there is no ground field here. -/
private lemma exists_indecomposable_decomposition_aux
    [IsArtinian A V] [IsNoetherian A V] (d : ℕ) :
    ∀ S : Submodule A V, Module.length A (↥S) ≤ (d : ℕ∞) →
    ∃ (n : ℕ) (W : Fin n → Submodule A V),
      (∀ i, W i ≤ S) ∧
      (∀ i, Etingof.IsIndecomposable A (W i)) ∧
      (⨆ i, W i) = S ∧ iSupIndep W := by
  induction d with
  | zero =>
    intro S hd
    have hlen0 : Module.length A ↥S = 0 := le_zero_iff.mp (by simpa using hd)
    have hsub : Subsingleton ↥S := Module.length_eq_zero_iff.mp hlen0
    have hS : S = ⊥ := by
      by_contra hne
      exact (not_subsingleton_iff_nontrivial.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne)) hsub
    subst hS
    exact ⟨0, Fin.elim0, nofun, nofun, by simp, iSupIndep_subsingleton _⟩
  | succ d ih =>
    intro S hd
    by_cases hIndec : Etingof.IsIndecomposable A S
    · exact ⟨1, fun _ => S, fun _ => le_refl S, fun _ => hIndec,
        by simp, iSupIndep_subsingleton _⟩
    · -- `S` is decomposable
      by_cases hS_triv : S = ⊥
      · subst hS_triv
        exact ⟨0, Fin.elim0, nofun, nofun, by simp, iSupIndep_subsingleton _⟩
      have hS_nt : Nontrivial ↥S := Submodule.nontrivial_iff_ne_bot.mpr hS_triv
      unfold Etingof.IsIndecomposable at hIndec
      push_neg at hIndec
      obtain ⟨M', N', hCompl, hM'ne, hN'ne⟩ := hIndec hS_nt
      have hSup' : M' ⊔ N' = ⊤ := codisjoint_iff.mp hCompl.codisjoint
      have hInf' : M' ⊓ N' = ⊥ := disjoint_iff.mp hCompl.disjoint
      -- Push the two summands of `↥S` forward to submodules of `V`.
      set M := Submodule.map S.subtype M' with hM_def
      set N := Submodule.map S.subtype N' with hN_def
      have hML : M ≤ S := Submodule.map_subtype_le S M'
      have hNL : N ≤ S := Submodule.map_subtype_le S N'
      have hMN_sup : M ⊔ N = S := by
        rw [hM_def, hN_def, ← Submodule.map_sup, hSup',
          Submodule.map_top, Submodule.range_subtype]
      have hMN_disj : Disjoint M N := by
        rw [disjoint_iff, hM_def, hN_def,
          ← Submodule.map_inf S.subtype S.injective_subtype,
          hInf', Submodule.map_bot]
      have hM'_ne_top : M' ≠ ⊤ := by
        intro h; rw [h, top_inf_eq] at hInf'; exact hN'ne hInf'
      have hN'_ne_top : N' ≠ ⊤ := by
        intro h; rw [h, inf_top_eq] at hInf'; exact hM'ne hInf'
      have hM_lt_S : M < S := by
        refine lt_of_le_of_ne hML fun heq => hN'ne ?_
        have hN_le_M : N ≤ M := by rw [heq]; exact hMN_sup ▸ le_sup_right
        have hN_bot : N = ⊥ := eq_bot_iff.mpr (hMN_disj hN_le_M le_rfl)
        exact Submodule.map_injective_of_injective (S.injective_subtype)
          (hN_bot.trans (Submodule.map_bot _).symm)
      have hN_lt_S : N < S := by
        refine lt_of_le_of_ne hNL fun heq => hM'ne ?_
        have hM_le_N : M ≤ N := by rw [heq]; exact hMN_sup ▸ le_sup_left
        have hM_bot : M = ⊥ := eq_bot_iff.mpr (hMN_disj.symm hM_le_N le_rfl)
        exact Submodule.map_injective_of_injective (S.injective_subtype)
          (hM_bot.trans (Submodule.map_bot _).symm)
      -- Length strictly drops when passing to a proper submodule of `S`.
      have hlen : ∀ P : Submodule A V, P < S → Module.length A ↥P ≤ (d : ℕ∞) := by
        intro P hP
        have hPle : P ≤ S := hP.le
        have hne_top : Submodule.comap S.subtype P ≠ ⊤ := by
          rw [ne_eq, Submodule.comap_subtype_eq_top]
          exact fun hSP => hP.ne (le_antisymm hPle hSP)
        have hlt : Module.length A ↥(Submodule.comap S.subtype P) < Module.length A ↥S :=
          Submodule.length_lt hne_top
        rw [(Submodule.comapSubtypeEquivOfLe hPle).length_eq] at hlt
        have hstep : Module.length A ↥P < (d : ℕ∞) + 1 :=
          lt_of_lt_of_le hlt (by rw [← Nat.cast_add_one]; exact hd)
        exact (ENat.lt_add_one_iff (ENat.coe_ne_top d)).mp hstep
      obtain ⟨nM, WM, hWM_le, hWM_indec, hWM_sup, hWM_ind⟩ := ih M (hlen M hM_lt_S)
      obtain ⟨nN, WN, hWN_le, hWN_indec, hWN_sup, hWN_ind⟩ := ih N (hlen N hN_lt_S)
      -- Combine the two decompositions via `Sum.elim` (identical to the finite-dimensional proof).
      set W' : Fin nM ⊕ Fin nN → Submodule A V := Sum.elim WM WN with hW'_def
      have hW'_le : ∀ i, W' i ≤ S := by
        intro i; cases i with
        | inl j => exact le_trans (hWM_le j) hML
        | inr j => exact le_trans (hWN_le j) hNL
      have hW'_indec : ∀ i, Etingof.IsIndecomposable A (W' i) := by
        intro i; cases i with
        | inl j => exact hWM_indec j
        | inr j => exact hWN_indec j
      have hW'_sup : (⨆ i, W' i) = S := by
        simp only [W', iSup_sum, Sum.elim_inl, Sum.elim_inr, hWM_sup, hWN_sup, hMN_sup]
      have hW'_ind : iSupIndep W' := by
        intro i
        cases i with
        | inl j =>
          have h_comp_le : (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i) ≤
              (⨆ j', ⨆ (_ : j' ≠ j), WM j') ⊔ (⨆ j', WN j') := by
            apply iSup_le; intro i; apply iSup_le; intro hi
            cases i with
            | inl j' =>
              exact le_sup_of_le_left
                (le_iSup_of_le j' (le_iSup_of_le (fun h => hi (congrArg Sum.inl h)) le_rfl))
            | inr j' => exact le_sup_of_le_right (le_iSup WN j')
          have hWM_j_le_M : WM j ≤ M := hWM_le j
          have hrest_le_M : (⨆ j', ⨆ (_ : j' ≠ j), WM j') ≤ M :=
            iSup₂_le fun j' _ => hWM_le j'
          have hN_eq : ⨆ j', WN j' = N := hWN_sup
          rw [disjoint_iff]
          apply eq_bot_iff.mpr
          have h_le_rest : WM j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i) ≤
              (⨆ j', ⨆ (_ : j' ≠ j), WM j') :=
            calc WM j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i)
                ≤ WM j ⊓ ((⨆ j', ⨆ (_ : j' ≠ j), WM j') ⊔ (⨆ j', WN j')) :=
                  inf_le_inf_left _ h_comp_le
              _ = WM j ⊓ ((⨆ j', ⨆ (_ : j' ≠ j), WM j') ⊔ N) := by rw [hN_eq]
              _ ≤ M ⊓ (N ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WM j')) := by
                  rw [sup_comm]; exact inf_le_inf_right _ hWM_j_le_M
              _ = M ⊓ N ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WM j') :=
                  (inf_sup_assoc_of_le N hrest_le_M).symm
              _ = (⨆ j', ⨆ (_ : j' ≠ j), WM j') := by
                  rw [disjoint_iff.mp hMN_disj, bot_sup_eq]
          calc WM j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i)
              ≤ WM j ⊓ (⨆ j', ⨆ (_ : j' ≠ j), WM j') :=
                le_inf inf_le_left h_le_rest
            _ = ⊥ := disjoint_iff.mp (hWM_ind j)
        | inr j =>
          have h_comp_le : (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i) ≤
              (⨆ j', WM j') ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j') := by
            apply iSup_le; intro i; apply iSup_le; intro hi
            cases i with
            | inl j' => exact le_sup_of_le_left (le_iSup WM j')
            | inr j' =>
              exact le_sup_of_le_right
                (le_iSup_of_le j' (le_iSup_of_le (fun h => hi (congrArg Sum.inr h)) le_rfl))
          have hWN_j_le_N : WN j ≤ N := hWN_le j
          have hrest_le_N : (⨆ j', ⨆ (_ : j' ≠ j), WN j') ≤ N :=
            iSup₂_le fun j' _ => hWN_le j'
          have hM_eq : ⨆ j', WM j' = M := hWM_sup
          rw [disjoint_iff]
          apply eq_bot_iff.mpr
          have h_le_rest : WN j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i) ≤
              (⨆ j', ⨆ (_ : j' ≠ j), WN j') :=
            calc WN j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i)
                ≤ WN j ⊓ ((⨆ j', WM j') ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j')) :=
                  inf_le_inf_left _ h_comp_le
              _ = WN j ⊓ (M ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j')) := by rw [hM_eq]
              _ ≤ N ⊓ (M ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j')) :=
                  inf_le_inf_right _ hWN_j_le_N
              _ = N ⊓ M ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j') :=
                  (inf_sup_assoc_of_le M hrest_le_N).symm
              _ = (⨆ j', ⨆ (_ : j' ≠ j), WN j') := by
                  rw [inf_comm, disjoint_iff.mp hMN_disj, bot_sup_eq]
          calc WN j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i)
              ≤ WN j ⊓ (⨆ j', ⨆ (_ : j' ≠ j), WN j') :=
                le_inf inf_le_left h_le_rest
            _ = ⊥ := disjoint_iff.mp (hWN_ind j)
      refine ⟨nM + nN, W' ∘ finSumFinEquiv.symm, ?_, ?_, ?_, ?_⟩
      · exact fun i => hW'_le (finSumFinEquiv.symm i)
      · exact fun i => hW'_indec (finSumFinEquiv.symm i)
      · rw [show (⨆ i, (W' ∘ finSumFinEquiv.symm) i) = ⨆ i, W' i from
          finSumFinEquiv.symm.surjective.iSup_comp W', hW'_sup]
      · exact hW'_ind.comp finSumFinEquiv.symm.injective

/-- **Existence half of Krull-Schmidt for finite-length modules.** Every finite-length module admits
an internal direct-sum decomposition into indecomposable submodules. The book calls this half
"clear"; formally it is the length induction of `exists_indecomposable_decomposition_aux`. -/
theorem exists_indecomposable_decomposition [IsArtinian A V] [IsNoetherian A V] :
    ∃ (n : ℕ) (W : Fin n → Submodule A V),
      (∀ i, Etingof.IsIndecomposable A (W i)) ∧ iSup W = ⊤ ∧ iSupIndep W := by
  have hbound : Module.length A (↥(⊤ : Submodule A V)) ≤ ((Module.length A V).toNat : ℕ∞) := by
    rw [Submodule.topEquiv.length_eq, ENat.coe_toNat Module.length_ne_top]
  obtain ⟨n, W, _, hindec, hsup, hind⟩ :=
    exists_indecomposable_decomposition_aux (Module.length A V).toNat ⊤ hbound
  exact ⟨n, W, hindec, hsup, hind⟩

end Etingof
