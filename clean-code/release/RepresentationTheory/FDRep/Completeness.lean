/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Group.SimpleRepresentations

open CategoryTheory

universe u v

namespace RepresentationTheory.FDRep.Completeness

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Fintype G]

omit [IsAlgClosed k] [Fintype G] in
/-- A pairwise nonisomorphic family of simple finite-dimensional representations is complete if it has the same size as a complete family. -/
theorem simpleFDRepFamily_complete_of_completeFamily_card_eq {n N : ℕ}
    (V : Fin n → FDRep k G)
    (hVcomplete : ∀ U : FDRep k G, Simple U → ∃ i, Nonempty (U ≅ V i))
    (W : Fin N → FDRep k G) (hWsimple : ∀ i, Simple (W i))
    (hWnoniso : ∀ i j, Nonempty (W i ≅ W j) → i = j)
    (hcard : N = n) :
    ∀ U : FDRep k G, Simple U → ∃ i, Nonempty (U ≅ W i) := by
  subst hcard
  choose f hf using fun i => hVcomplete (W i) (hWsimple i)
  have hfinj : Function.Injective f := by
    intro i j hij
    exact hWnoniso i j ⟨(hf i).some ≪≫ eqToIso (congrArg V hij) ≪≫ (hf j).some.symm⟩
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  intro U hU
  obtain ⟨j, hj⟩ := hVcomplete U hU
  obtain ⟨i, rfl⟩ := hfbij.2 j
  exact ⟨i, ⟨hj.some ≪≫ (hf i).some.symm⟩⟩

/-- A pairwise nonisomorphic family of simple finite-dimensional representations is complete when its size equals the number of conjugacy classes. -/
theorem simpleFDRepFamily_complete_of_card_eq_conjClasses
    [Invertible (Fintype.card G : k)] {N : ℕ}
    (W : Fin N → FDRep k G) (hWsimple : ∀ i, Simple (W i))
    (hWnoniso : ∀ i j, Nonempty (W i ≅ W j) → i = j)
    (hN : N = Nat.card (ConjClasses G)) :
    ∀ U : FDRep k G, Simple U → ∃ i, Nonempty (U ≅ W i) := by
  classical
  obtain ⟨n, V, -, -, hVcomplete, hn⟩ :=
    RepresentationTheory.Group.SimpleRepresentations.exists_simpleReps_card_eq_conjClasses (k := k) (G := G)
  exact simpleFDRepFamily_complete_of_completeFamily_card_eq V hVcomplete W hWsimple hWnoniso
    (by rw [hN, hn, Nat.card_eq_fintype_card])

end RepresentationTheory.FDRep.Completeness
