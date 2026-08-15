/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! # A simple-character criterion -/

open FDRep CategoryTheory

universe u

namespace RepresentationTheory.Group.SimpleCharacterCriterion

/-- A finite-group representation is simple exactly when its displayed character inner value is
one. -/
@[source_ref "Chapter4/Discussion_after_Theorem4.5.1" (role := primary)]
theorem simple_iff_characterInner_eq_one
    {k G : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V : FDRep k G) :
    Simple V ↔
      ⅟(Fintype.card G : k) • ∑ g : G, V.character g * V.character g⁻¹ = 1 := by
  rw [simple_iff_char_is_norm_one V, smul_eq_mul]
  rw [show ((Nat.card G : k)) = (Fintype.card G : k) from by rw [Fintype.card_eq_nat_card]]
  constructor
  · intro h; rw [h]; exact invOf_mul_self _
  · intro h
    have h2 := congrArg (fun x => (Fintype.card G : k) * x) h
    simpa only [mul_one, ← mul_assoc, mul_invOf_self, one_mul] using h2

end RepresentationTheory.Group.SimpleCharacterCriterion
