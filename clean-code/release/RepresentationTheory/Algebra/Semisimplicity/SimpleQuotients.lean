/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Semisimplicity.EndomorphismProduct
import RepresentationTheory.Algebra.Module.Simple.FiniteDimensional
import RepresentationTheory.Alignment.Attribute

/-! # Simple quotients -/

universe u v

open Module

namespace RepresentationTheory.Algebra.Semisimplicity.SimpleQuotients

/-- A quotient of a finite-dimensional algebra by a submodule is finite-dimensional. -/
theorem finiteDimensional_quotient (k : Type*) (A : Type u)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] (M : Submodule A A) :
    FiniteDimensional k (A ⧸ M) :=
  Module.Finite.of_surjective ((Submodule.mkQ M).restrictScalars k)
    (Submodule.Quotient.mk_surjective _)

/-- Every simple module is equivalent to a quotient by a coatom submodule of the regular module. -/
@[source_ref "Chapter3/Theorem3.5.4" (role := primary)]
theorem exists_coatom_quotient_equiv (A : Type u) (V : Type v)
    [Ring A] [AddCommGroup V] [Module A V] [IsSimpleModule A V] :
    ∃ M : Submodule A A, IsCoatom M ∧ Nonempty (V ≃ₗ[A] (A ⧸ M)) := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton A V v) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton]
    exact (eq_bot_or_eq_top (Submodule.span A {v})).resolve_left (by
      rw [Submodule.span_singleton_eq_bot]; exact hv)
  exact ⟨_, LinearMap.isCoatom_ker_of_surjective hsurj,
    ⟨((LinearMap.toSpanSingleton A V v).quotKerEquivOfSurjective hsurj).symm⟩⟩

private def Separated (A : Type u) [Ring A] (s : Finset (Submodule A A)) : Prop :=
  (∀ M ∈ s, IsCoatom M) ∧
    ∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))

/-- A finite-dimensional algebra has a bounded finite family of pairwise inequivalent coatom
quotients representing every coatom quotient. -/
@[source_ref "Chapter3/Theorem3.5.4" (role := supporting)]
theorem exists_finite_coatomFamily_of_coatoms (k : Type*) (A : Type u)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    ∃ s : Finset (Submodule A A),
      (∀ M ∈ s, IsCoatom M) ∧
      s.card ≤ finrank k A ∧
      (∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))) ∧
      ∀ N : Submodule A A, IsCoatom N → ∃ M ∈ s, Nonempty ((A ⧸ N) ≃ₗ[A] (A ⧸ M)) := by
  classical
  have hbound : ∀ s : Finset (Submodule A A), Separated A s → s.card ≤ finrank k A := by
    intro s hs
    haveI : ∀ i : {x // x ∈ s}, IsSimpleModule A (A ⧸ (i : Submodule A A)) := fun i =>
      isSimpleModule_iff_isCoatom.mpr (hs.1 i i.2)
    haveI : ∀ i : {x // x ∈ s}, FiniteDimensional k (A ⧸ (i : Submodule A A)) := fun i =>
      finiteDimensional_quotient k A _
    have h := RepresentationTheory.Algebra.Module.Simple.FiniteDimensional.card_le_finrank_of_pairwise_nonisomorphic
      k A {x // x ∈ s} (fun i => A ⧸ (i : Submodule A A))
      (fun i j hij => hs.2 i i.2 j j.2 fun h => hij (Subtype.ext h))
    simpa using h
  set P : ℕ → Prop := fun n => ∃ s : Finset (Submodule A A), Separated A s ∧ s.card = n with hP
  have hP0 : P 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨s, hsSep, hscard⟩ : P (Nat.findGreatest P (finrank k A)) :=
    Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ t : Finset (Submodule A A), Separated A t →
      t.card ≤ Nat.findGreatest P (finrank k A) := fun t ht =>
    Nat.le_findGreatest (hbound t ht) ⟨t, ht, rfl⟩
  refine ⟨s, hsSep.1, hbound s hsSep, hsSep.2, ?_⟩
  intro N hN
  by_contra hcon
  push Not at hcon
  have hempty : ∀ M ∈ s, IsEmpty ((A ⧸ N) ≃ₗ[A] (A ⧸ M)) := hcon
  have hNs : N ∉ s := fun h => (hempty N h).elim (LinearEquiv.refl A _)
  have hins : Separated A (insert N s) := by
    refine ⟨fun M hM => ?_, fun M hM M' hM' hne => ?_⟩
    · obtain rfl | hM := Finset.mem_insert.mp hM
      · exact hN
      · exact hsSep.1 M hM
    · obtain hMN | hMs := Finset.mem_insert.mp hM
      · obtain hM'N | hM's := Finset.mem_insert.mp hM'
        · exact absurd (hMN.trans hM'N.symm) hne
        · subst hMN; exact hempty M' hM's
      · obtain hM'N | hM's := Finset.mem_insert.mp hM'
        · subst hM'N; exact ⟨fun e => (hempty M hMs).elim e.symm⟩
        · exact hsSep.2 M hMs M' hM's hne
  have hcard : (insert N s).card = s.card + 1 := Finset.card_insert_of_notMem hNs
  have hle := hmax _ hins
  omega

/-- A finite-dimensional algebra has a bounded finite family of pairwise inequivalent coatom
quotients representing every simple module. -/
@[source_ref "Chapter3/Theorem3.5.4" (role := primary)]
theorem exists_finite_coatomFamily (k : Type*) (A : Type u)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    ∃ s : Finset (Submodule A A),
      (∀ M ∈ s, IsCoatom M) ∧
      s.card ≤ finrank k A ∧
      (∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))) ∧
      ∀ (V : Type v) [AddCommGroup V] [Module A V] [IsSimpleModule A V],
        ∃ M ∈ s, Nonempty (V ≃ₗ[A] (A ⧸ M)) := by
  obtain ⟨s, hcoatom, hcard, hnoniso, hexh⟩ := exists_finite_coatomFamily_of_coatoms k A
  refine ⟨s, hcoatom, hcard, hnoniso, ?_⟩
  intro V _ _ _
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_coatom_quotient_equiv A V
  obtain ⟨M, hM, ⟨f⟩⟩ := hexh N hN
  exact ⟨M, hM, ⟨e.trans f⟩⟩

/-- A finite-dimensional algebra has the displayed coatom family together with an equivalence
from the indicated quotient algebra to a product of endomorphism algebras. -/
@[source_ref "Chapter3/Theorem3.5.4" (role := supporting)]
theorem exists_finite_coatomFamily_algEquiv_quotient (k : Type*) (A : Type u)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    ∃ s : Finset (Submodule A A),
      (∀ M ∈ s, IsCoatom M) ∧
      s.card ≤ finrank k A ∧
      (∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))) ∧
      (∀ (W : Type u) [AddCommGroup W] [Module A W] [IsSimpleModule A W],
        ∃ M ∈ s, Nonempty (W ≃ₗ[A] (A ⧸ M))) ∧
      Nonempty ((A ⧸ RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A) ≃ₐ[k]
        ∀ M : {x // x ∈ s}, Module.End k (A ⧸ (M : Submodule A A))) := by
  obtain ⟨s, hcoatom, hcard, hnoniso, hexh⟩ := exists_finite_coatomFamily.{u, u} k A
  refine ⟨s, hcoatom, hcard, hnoniso, hexh, ?_⟩
  haveI : ∀ i : {x // x ∈ s}, IsSimpleModule A (A ⧸ (i : Submodule A A)) := fun i =>
    isSimpleModule_iff_isCoatom.mpr (hcoatom i i.2)
  haveI : ∀ i : {x // x ∈ s}, FiniteDimensional k (A ⧸ (i : Submodule A A)) := fun i =>
    finiteDimensional_quotient k A _
  exact RepresentationTheory.Algebra.Semisimplicity.EndomorphismProduct.nonempty_algEquiv_quotient_endProduct
    k A {x // x ∈ s} (fun i => A ⧸ (i : Submodule A A))
    (fun i j hij => hnoniso i i.2 j j.2 fun h => hij (Subtype.ext h))
    (fun W _ _ _ _ _ _ => by
      obtain ⟨M, hM, e⟩ := hexh W
      exact ⟨⟨M, hM⟩, e⟩)

end RepresentationTheory.Algebra.Semisimplicity.SimpleQuotients
