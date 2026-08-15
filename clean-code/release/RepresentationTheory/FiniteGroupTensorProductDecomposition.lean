/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.FDRep.CharacterDecomposition
import RepresentationTheory.FDRep.GroupAlgebraDecomposition

/-!
# Tensor product decomposition for finite-group representations

This module computes tensor-product multiplicities using characters and decomposes tensor
products into a complete family of pairwise nonisomorphic simple representations.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Module
  RepresentationTheory.FDRep.CharacterDecomposition
  RepresentationTheory.FDRep.GroupAlgebraDecomposition
  RepresentationTheory.FiniteGroup.CharacterPairing

namespace RepresentationTheory.FiniteGroupTensorProductDecomposition

variable {G : Type} [Group G] [Fintype G]

/-- A natural-number multiplicity attached to three finite-dimensional complex representations of
a group. -/
@[source_ref"Chapter4/Introduction_4.9"(role:=supporting)]
noncomputable def tensorProductMultiplicity (X Y S : FDRep ℂ G) : ℕ :=
  finrank ℂ (S ⟶ X ⊗ Y)

/-- The complex cast of the tensor-product multiplicity is the group average of the product of two
characters with the inverse-argument character of the third representation. -/
@[source_ref"Chapter4/Introduction_4.9"(role:=primary)]
theorem cast_tensorProductMultiplicity_eq_character_average (X Y S : FDRep ℂ G) :
    (tensorProductMultiplicity X Y S : ℂ) =
      ⅟(Fintype.card G : ℂ) •
        ∑ g : G, (X.character g * Y.character g) * S.character g⁻¹ := by
  rw [tensorProductMultiplicity,
    ← FiniteGroup.normalized_characterPairing_eq_finrank_hom (X ⊗ Y) S]
  simp only [FDRep.char_tensor, Pi.mul_apply]

section Decomposition

variable {ι : Type} [Fintype ι] [DecidableEq ι] (V : ι → FDRep ℂ G)
  (hV : ∀ i, Simple (V i)) (hinj : ∀ i j, Nonempty (V i ≅ V j) → i = j)
  (hcomplete : ∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ V i))

/-- An auxiliary finite-dimensional representation associated with an indexed family and two
representations. -/
noncomputable def auxiliaryTensorProductDecomposition (X Y : FDRep ℂ G) : FDRep ℂ G :=
  representationFromIndexedNats V (tensorProductMultiplicity X Y <| V ·)

include hV hinj hcomplete in
/-- A tensor product is isomorphic to the specified auxiliary decomposition whenever the indexing
family is simple, pairwise nonisomorphic, and exhaustive among simple representations. -/
@[source_ref"Chapter4/Introduction_4.9"(role:=supporting)]
theorem tensorProduct_iso_auxiliaryDecomposition (X Y : FDRep ℂ G) :
    Nonempty (X ⊗ Y ≅ auxiliaryTensorProductDecomposition V X Y) := by
  have h := iso_representationFromIndexedNats_indexedNatForRepresentation
    V hV hinj hcomplete (X ⊗ Y)
  have hmul : indexedNatForRepresentation V (X ⊗ Y) =
      (tensorProductMultiplicity X Y <| V ·) := rfl
  rwa [hmul] at h

include hV hinj hcomplete in
/-- For a complete finite family of pairwise nonisomorphic simple representations, the dimension
of morphisms into a tensor product is the sum of tensor-product multiplicities weighted by the
corresponding morphism-space dimensions. -/
theorem finrank_hom_tensor_eq_sum_multiplicity_mul_finrank_hom
    (X Y S : FDRep ℂ G) :
    finrank ℂ (S ⟶ X ⊗ Y) =
      ∑ i, tensorProductMultiplicity X Y (V i) * finrank ℂ (S ⟶ V i) :=
  finrank_hom_eq_sum_indexedNatForRepresentation_mul V hV hinj hcomplete (X ⊗ Y) S

end Decomposition

/-- The tensor product of two finite-dimensional complex representations of a finite group is
isomorphic to a decomposition indexed by pairwise nonisomorphic simple representations that
exhaust all simple objects. -/
@[source_ref"Chapter4/Introduction_4.9"(role:=supporting)]
theorem tensorProduct_exists_simpleDecomposition (X Y : FDRep ℂ G) :
    ∃ (n : ℕ) (V : Fin n → FDRep ℂ G),
      (∀ i, Simple (V i)) ∧ (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ V i)) ∧
      Nonempty (X ⊗ Y ≅ auxiliaryTensorProductDecomposition V X Y) := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let D : DecompositionData ℂ G := DecompositionData.default
  refine ⟨D.count, D.representation, D.simple_representation,
    fun i j h => D.representation_index_eq_of_iso i j h,
    fun S hS => D.exists_iso_representation_of_simple S hS, ?_⟩
  exact tensorProduct_iso_auxiliaryDecomposition D.representation D.simple_representation
    (fun i j h => D.representation_index_eq_of_iso i j h)
    (fun S hS => D.exists_iso_representation_of_simple S hS) X Y

end RepresentationTheory.FiniteGroupTensorProductDecomposition
