/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.Length
import RepresentationTheory.Alignment.Attribute

/-! # Lengths of composition series -/

open Order

namespace RepresentationTheory.Module.CompositionSeriesLength

variable (A : Type*) (V : Type*) [Ring A] [AddCommGroup V] [Module A V]

/-- The length of a composition series running from the bottom submodule to the top submodule is
greatest among the lengths of composition series. -/
@[source_ref "Chapter3/Discussion_after_Theorem3.7.1" (role := supporting)]
theorem compositionSeries_length_isGreatest
    (s : CompositionSeries (Submodule A V)) (hbot : s.head = ⊥) (htop : s.last = ⊤) :
    IsGreatest (Set.range fun l : LTSeries (Submodule A V) => (l.length : ℕ∞))
      (s.length : ℕ∞) := by
  constructor
  · refine ⟨s.map ⟨id, fun h => h.1⟩, ?_⟩
    simp only [RelSeries.map_length]
  · rintro _ ⟨l, rfl⟩
    have hkrull : (l.length : ℕ∞) ≤ Module.length A V := by
      have h1 := LTSeries.length_le_krullDim l
      rw [← Module.coe_length] at h1
      exact_mod_cast h1
    rwa [Module.length_compositionSeries s hbot htop]

end RepresentationTheory.Module.CompositionSeriesLength
