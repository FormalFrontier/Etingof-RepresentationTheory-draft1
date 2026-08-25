import EtingofRepresentationTheory.Chapter3.Theorem3_5_4
import EtingofRepresentationTheory.Chapter3.Theorem3_5_4_Finiteness

/-!
# Theorem 3.5.4: existence of a complete family of irreducibles

`Etingof.structure_mod_radical` (in `Theorem3_5_4.lean`) proves the isomorphism clause
`A / Rad(A) ≅ ∏ᵢ End(Vᵢ)` of Theorem 3.5.4, but *assumes* the complete family: it takes
`[Fintype ι]` together with a completeness hypothesis. `Theorem3_5_4_Finiteness.lean` supplies
the two conditional ingredients the book uses (every irreducible is finite dimensional; an
already-finite pairwise nonisomorphic family has cardinality at most `dim A`).

This file discharges the remaining, existential half of the book statement: a finite,
pairwise nonisomorphic, *exhaustive* family of irreducibles actually exists.

The family is built concretely. Every irreducible `V` is cyclic, hence `V ≃ₗ[A] A ⧸ M` for a
maximal left ideal (`IsCoatom` submodule) `M` — this is `Etingof.exists_isCoatom_quotient_equiv`.
So it suffices to choose finitely many maximal left ideals whose quotients are pairwise
nonisomorphic and exhaust all of them. Since `Etingof.card_irreducibles_le_finrank` bounds the
cardinality of *every* pairwise-nonisomorphic finite family by `dim A`, a family of maximum
cardinality exists, and maximality forces exhaustiveness: an omitted irreducible could be
adjoined, contradicting maximality.

Main results:

* `Etingof.exists_isCoatom_quotient_equiv`: every simple `A`-module is `A ⧸ M` for a coatom `M`.
* `Etingof.exists_finset_complete_family`: the maximum-cardinality family exists, is bounded by
  `dim A`, and exhausts the quotients `A ⧸ N` by coatoms.
* `Etingof.exists_complete_family_of_simples`: the same family, with exhaustiveness stated for
  an arbitrary simple `A`-module in an arbitrary universe.
* `Etingof.exists_structure_mod_radical`: the existential form of `Etingof.structure_mod_radical`
  — it *constructs* the complete family rather than taking it as a hypothesis, and returns the
  algebra isomorphism `A / Rad(A) ≃ₐ[k] ∏_{M ∈ s} End_k (A ⧸ M)`.
-/

universe u v

open Module

namespace Etingof

/-- The quotient of a finite dimensional algebra by a left ideal is finite dimensional. -/
theorem finiteDimensional_quotient (k : Type*) (A : Type u)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] (M : Submodule A A) :
    FiniteDimensional k (A ⧸ M) :=
  Module.Finite.of_surjective ((Submodule.mkQ M).restrictScalars k)
    (Submodule.Quotient.mk_surjective _)

/-- Every irreducible representation is cyclic, hence of the form `A ⧸ M` for a maximal left
ideal `M`.

Book (Theorem 3.5.4, first paragraph): for `0 ≠ v ∈ V`, the map `a ↦ a • v` is a surjection
`A ↠ V` because `A • v` is a nonzero subrepresentation of the irreducible `V`. Etingof
Theorem 3.5.4. -/
theorem exists_isCoatom_quotient_equiv (A : Type u) (V : Type v)
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

/-- A finite set of maximal left ideals is *separated* when the corresponding irreducibles
`A ⧸ M` are pairwise nonisomorphic. This is the auxiliary predicate used to run the
maximum-cardinality argument for `Etingof.exists_finset_complete_family`. -/
private def Separated (A : Type u) [Ring A] (s : Finset (Submodule A A)) : Prop :=
  (∀ M ∈ s, IsCoatom M) ∧
    ∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))

/-- **Theorem 3.5.4, finiteness half.** A finite dimensional algebra over an algebraically
closed field has a finite complete family of pairwise nonisomorphic irreducible
representations, of cardinality at most `dim A`.

The family is presented concretely as the quotients `A ⧸ M` for `M` ranging over a finite set
`s` of maximal left ideals. Exhaustiveness is stated for quotients by maximal left ideals; see
`Etingof.exists_complete_family_of_simples` for the version covering an arbitrary simple module.
Etingof Theorem 3.5.4. -/
theorem exists_finset_complete_family (k : Type*) (A : Type u)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    ∃ s : Finset (Submodule A A),
      (∀ M ∈ s, IsCoatom M) ∧
      s.card ≤ finrank k A ∧
      (∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))) ∧
      ∀ N : Submodule A A, IsCoatom N → ∃ M ∈ s, Nonempty ((A ⧸ N) ≃ₗ[A] (A ⧸ M)) := by
  classical
  -- Every separated family has at most `dim A` members (Theorem 3.2.2, via
  -- `card_irreducibles_le_finrank`).
  have hbound : ∀ s : Finset (Submodule A A), Separated A s → s.card ≤ finrank k A := by
    intro s hs
    haveI : ∀ i : {x // x ∈ s}, IsSimpleModule A (A ⧸ (i : Submodule A A)) := fun i =>
      isSimpleModule_iff_isCoatom.mpr (hs.1 i i.2)
    haveI : ∀ i : {x // x ∈ s}, FiniteDimensional k (A ⧸ (i : Submodule A A)) := fun i =>
      finiteDimensional_quotient k A _
    have h := Etingof.card_irreducibles_le_finrank k A {x // x ∈ s}
      (fun i => A ⧸ (i : Submodule A A))
      (fun i j hij => hs.2 i i.2 j j.2 fun h => hij (Subtype.ext h))
    simpa using h
  -- So the cardinalities of separated families form a set of naturals bounded by `dim A`;
  -- pick a family of maximum cardinality.
  set P : ℕ → Prop := fun n => ∃ s : Finset (Submodule A A), Separated A s ∧ s.card = n with hP
  have hP0 : P 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨s, hsSep, hscard⟩ : P (Nat.findGreatest P (finrank k A)) :=
    Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ t : Finset (Submodule A A), Separated A t →
      t.card ≤ Nat.findGreatest P (finrank k A) := fun t ht =>
    Nat.le_findGreatest (hbound t ht) ⟨t, ht, rfl⟩
  refine ⟨s, hsSep.1, hbound s hsSep, hsSep.2, ?_⟩
  -- Maximality forces exhaustiveness: an omitted irreducible could be adjoined.
  intro N hN
  by_contra hcon
  push Not at hcon
  have hempty : ∀ M ∈ s, IsEmpty ((A ⧸ N) ≃ₗ[A] (A ⧸ M)) := hcon
  have hNs : N ∉ s := fun h => (hempty N h).elim (LinearEquiv.refl A _)
  -- `insert N s` is still separated, but strictly larger.
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

/-- **Theorem 3.5.4, finiteness half**, with exhaustiveness for arbitrary simple modules.

A finite dimensional algebra over an algebraically closed field has, up to isomorphism, only
finitely many irreducible representations — at most `dim A` of them — and they are exhausted by
the quotients `A ⧸ M` for `M` in a finite set `s` of maximal left ideals. Etingof
Theorem 3.5.4. -/
theorem exists_complete_family_of_simples (k : Type*) (A : Type u)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    ∃ s : Finset (Submodule A A),
      (∀ M ∈ s, IsCoatom M) ∧
      s.card ≤ finrank k A ∧
      (∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))) ∧
      ∀ (V : Type v) [AddCommGroup V] [Module A V] [IsSimpleModule A V],
        ∃ M ∈ s, Nonempty (V ≃ₗ[A] (A ⧸ M)) := by
  obtain ⟨s, hcoatom, hcard, hnoniso, hexh⟩ := exists_finset_complete_family k A
  refine ⟨s, hcoatom, hcard, hnoniso, ?_⟩
  intro V _ _ _
  -- Every simple module is `A ⧸ N` for some maximal left ideal `N`, which is in turn
  -- isomorphic to a member of the family.
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_isCoatom_quotient_equiv A V
  obtain ⟨M, hM, ⟨f⟩⟩ := hexh N hN
  exact ⟨M, hM, ⟨e.trans f⟩⟩

/-- **Theorem 3.5.4**, existential form: for a finite dimensional algebra `A` over an
algebraically closed field there *exists* a finite complete family of pairwise nonisomorphic
irreducibles `A ⧸ M` (`M ∈ s`, `s.card ≤ dim A`) with

  `A / Rad(A) ≃ₐ[k] ∏_{M ∈ s} End_k (A ⧸ M)`.

Unlike `Etingof.structure_mod_radical`, this version constructs the family instead of taking
`[Fintype ι]` plus completeness as hypotheses, so it formalizes the whole book statement.
Etingof Theorem 3.5.4. -/
theorem exists_structure_mod_radical (k : Type*) (A : Type u)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    ∃ s : Finset (Submodule A A),
      (∀ M ∈ s, IsCoatom M) ∧
      s.card ≤ finrank k A ∧
      (∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))) ∧
      (∀ (W : Type u) [AddCommGroup W] [Module A W] [IsSimpleModule A W],
        ∃ M ∈ s, Nonempty (W ≃ₗ[A] (A ⧸ M))) ∧
      Nonempty ((A ⧸ Etingof.Radical A) ≃ₐ[k]
        ∀ M : {x // x ∈ s}, Module.End k (A ⧸ (M : Submodule A A))) := by
  obtain ⟨s, hcoatom, hcard, hnoniso, hexh⟩ := exists_complete_family_of_simples.{u, u} k A
  refine ⟨s, hcoatom, hcard, hnoniso, hexh, ?_⟩
  haveI : ∀ i : {x // x ∈ s}, IsSimpleModule A (A ⧸ (i : Submodule A A)) := fun i =>
    isSimpleModule_iff_isCoatom.mpr (hcoatom i i.2)
  haveI : ∀ i : {x // x ∈ s}, FiniteDimensional k (A ⧸ (i : Submodule A A)) := fun i =>
    finiteDimensional_quotient k A _
  exact Etingof.structure_mod_radical k A {x // x ∈ s} (fun i => A ⧸ (i : Submodule A A))
    (fun i j hij => hnoniso i i.2 j j.2 fun h => hij (Subtype.ext h))
    (fun W _ _ _ _ _ _ => by
      obtain ⟨M, hM, e⟩ := hexh W
      exact ⟨⟨M, hM⟩, e⟩)

end Etingof
