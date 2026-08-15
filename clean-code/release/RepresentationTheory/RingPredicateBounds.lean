/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.Auxiliary.RingData
import Mathlib.Data.ENat.Lattice

/-!
# Bounds for a ring-indexed invariant

This module records elementary bounds for an extended-natural-valued invariant determined by
natural-number-indexed predicates on rings.
-/

universe u

namespace RepresentationTheory.RingPredicateBounds

/-- The ring-indexed value is top when the index predicate fails for every natural number. -/
theorem eq_top_of_forall_not_predicate {R : Type u} [Ring R]
    (h : ∀ d : ℕ,
      ¬ RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R d) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant R = ⊤ := by
  unfold RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant
  have hd : ∀ d : ℕ,
      (⨅ (_ : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R d),
        (d : ℕ∞)) = ⊤ := fun d => iInf_neg (h d)
  simp_rw [hd]
  exact iInf_top

/-- Whenever the index predicate holds, the ring-indexed value is at most that index viewed in its ambient ordered type. -/
theorem le_natCast_of_predicate {R : Type u} [Ring R] {d : ℕ}
    (h : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R d) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant R ≤ (d : ℕ∞) := by
  unfold RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant
  exact iInf₂_le d h

/-- The ring-indexed value equals one when its index predicate holds at one and fails at zero. -/
theorem eq_one_of_predicate_one_and_not_predicate_zero {R : Type u} [Ring R]
    (h1 : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R 1)
    (h0 : ¬ RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R 0) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant R = 1 := by
  refine le_antisymm ?_ ?_
  · simpa using le_natCast_of_predicate h1
  · unfold RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant
    refine le_iInf₂ (fun d hd => ?_)
    match d with
    | 0 => exact absurd hd h0
    | (n + 1) => exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

end RepresentationTheory.RingPredicateBounds
