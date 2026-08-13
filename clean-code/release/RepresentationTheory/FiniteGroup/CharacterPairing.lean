/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier
-/

import RepresentationTheory.FDRep.Character

open FDRep CategoryTheory

universe u v

namespace RepresentationTheory.FiniteGroup.CharacterPairing

/-- The group-order-normalized sum of the character of V times the inverse-argument character of
W equals the dimension of the morphism space from W to V. -/
theorem FiniteGroup.normalized_characterPairing_eq_finrank_hom
    {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V W : FDRep k G) :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
    Module.finrank k (W ⟶ V) := by
  exact FDRep.Character.normalizedCharacterSum_eq_finrank_hom V W

open scoped Classical in
/-- For simple finite-dimensional representations, the normalized character pairing is one when
the representations are isomorphic and zero otherwise. -/
theorem FiniteGroup.normalized_characterPairing_of_simple
    {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V W : FDRep k G) [Simple V] [Simple W] :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
    if Nonempty (V ≅ W) then (1 : k) else (0 : k) := by
  exact FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple V W

end RepresentationTheory.FiniteGroup.CharacterPairing
