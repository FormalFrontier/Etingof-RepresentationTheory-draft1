/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.RepresentationTensorDecompositions
import RepresentationTheory.Group.SimpleRepresentations

/-!
# `A₅`: completeness of the irreducible list `indexedSimpleRepresentations`

The five representations `indexedSimpleRepresentations 0..4 : Fin 5 → FDRep ℂ A₅` are simple
(`simple_indexedSimpleRepresentations`) and pairwise non-isomorphic (`indexedSimpleRepresentations_pairwise_nonisomorphic`). Since `A₅` has exactly
`5` conjugacy classes (`RepresentationTheory.Group.SmallRepresentationData.card_conjClasses_alternatingGroup_fin5`), Corollary 4.2.2, which
produces a complete list of `|ConjClasses G|` simple representations, forces `indexedSimpleRepresentations` to be
a complete list: every simple `FDRep ℂ A₅` is isomorphic to some `indexedSimpleRepresentations i`.

* `exists_iso_alternatingGroupFin5RepFamily`: every simple `V : FDRep ℂ A₅` satisfies `V ≅ indexedSimpleRepresentations i` for some `i`.
* `exists_character_eq_indexedTableRow`: hence its character is the `i`-th row `indexedTable i` of the `A₅`
  character table (evaluated at the conjugacy class of `g`).

This is the reusable completeness input for the icosahedral decomposition theorems of
Problem 4.12.5.
-/

open CategoryTheory

namespace RepresentationTheory.Group.AlternatingGroupFin5Classification

/-- `|A₅| = 60` is invertible in `ℂ`, so Corollary 4.2.2 applies. -/
private noncomputable instance : Invertible (Fintype.card (alternatingGroup (Fin 5)) : ℂ) :=
  invertibleOfNonzero (by rw [RepresentationTheory.Group.SmallRepresentationData.card_alternatingGroup_fin5]; norm_num)

/-- Every simple complex representation of the alternating group on five letters is isomorphic to a member of the displayed indexed family. -/
theorem exists_iso_alternatingGroupFin5RepFamily (V : FDRep ℂ (alternatingGroup (Fin 5))) [Simple V] :
    ∃ i : Fin 5, Nonempty (V ≅ RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i) := by
  obtain ⟨n, W, _hWsimp, _hWinj, hWsurj, hn⟩ :=
    RepresentationTheory.Group.SimpleRepresentations.exists_simpleReps_card_eq_conjClasses (k := ℂ) (G := alternatingGroup (Fin 5))
  rw [RepresentationTheory.Group.SmallRepresentationData.card_conjClasses_alternatingGroup_fin5] at hn
  subst hn
  -- Each `indexedSimpleRepresentations i` is isomorphic to some `W (c i)`.
  choose c hc using fun i => hWsurj (RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i) (RepresentationTheory.TensorSquareSpectralDecomposition.simple_indexedSimpleRepresentations i)
  -- `c` is injective: distinct `indexedSimpleRepresentations` are non-isomorphic, so land in distinct `W`.
  have hcinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    refine RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations_pairwise_nonisomorphic i j hne ?_
    obtain ⟨αi⟩ := hc i
    obtain ⟨αj⟩ := hc j
    exact ⟨αi ≪≫ eqToIso (congrArg W hij) ≪≫ αj.symm⟩
  -- `c : Fin 5 → Fin 5` injective, hence surjective.
  have hcsurj : Function.Surjective c := Finite.surjective_of_injective hcinj
  -- `V` is simple, so `V ≅ W k` for some `k = c i`.
  obtain ⟨k, hk⟩ := hWsurj V ‹Simple V›
  obtain ⟨i, hi⟩ := hcsurj k
  refine ⟨i, ?_⟩
  obtain ⟨αV⟩ := hk
  obtain ⟨αi⟩ := hc i
  exact ⟨αV ≪≫ eqToIso (congrArg W hi.symm) ≪≫ αi.symm⟩

/-- The character of every simple complex representation of the alternating group on five letters agrees with an indexed row of the displayed table. -/
theorem exists_character_eq_indexedTableRow (V : FDRep ℂ (alternatingGroup (Fin 5))) [Simple V] :
    ∃ i : Fin 5, ∀ g, V.character g = RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (RepresentationTheory.Group.PermutationSubgroupData.indexedTable i (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)) := by
  obtain ⟨i, ⟨α⟩⟩ := exists_iso_alternatingGroupFin5RepFamily V
  refine ⟨i, fun g => ?_⟩
  rw [FDRep.char_iso α, RepresentationTheory.RepresentationTensorDecompositions.firstFiveRepresentationFamily_character_formula i g]

end RepresentationTheory.Group.AlternatingGroupFin5Classification
