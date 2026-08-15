/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.RepresentationTheory.Character

/-!
# Character sums for finite-dimensional representations

This module gives character-sum identities using an explicit finite group cardinality.
-/

open CategoryTheory

universe u v

namespace RepresentationTheory.FDRep.Character

/-- The group-cardinality-normalized sum of the character values of the first representation at
each element times those of the second at its inverse equals the field dimension of the morphisms
from the second representation to the first. -/
theorem normalizedCharacterSum_eq_finrank_hom
    {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)] (V W : FDRep k G) :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
      Module.finrank k (W ⟶ V) := by
  haveI : Invertible (Nat.card G : k) := by
    rwa [← Fintype.card_eq_nat_card]
  simpa only [invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card] using
    _root_.FDRep.scalar_product_char_eq_finrank_equivariant W V

open scoped Classical in
/-- For simple finite-dimensional representations, the group-cardinality-normalized sum of their
character values at an element and its inverse is one when the representations are isomorphic and
zero otherwise. -/
theorem normalizedCharacterSum_eq_ite_iso_of_simple
    {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)] (V W : FDRep k G) [Simple V] [Simple W] :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then (1 : k) else (0 : k) := by
  haveI : Invertible (Nat.card G : k) := by
    rwa [← Fintype.card_eq_nat_card]
  simpa only [invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card] using
    _root_.FDRep.char_orthonormal V W

end RepresentationTheory.FDRep.Character
