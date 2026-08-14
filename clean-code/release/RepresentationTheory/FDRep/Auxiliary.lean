/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.FDRep.RegularRepresentationCharacter
import RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar

open FDRep CategoryTheory

universe u

namespace RepresentationTheory.FDRep.Auxiliary

variable {k G : Type u} [Field k] [Group G] [Fintype G]

/-- An auxiliary scalar invariant attached to a finite-dimensional group representation. -/
noncomputable def auxiliaryInvariant
    [Invertible (Fintype.card G : k)]
    (V : FDRep k G) : k :=
  ⅟(Fintype.card G : k) • ∑ g : G, V.character (g * g)

private lemma sum_dim_char_eq_regularChar
    [DecidableEq G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G)
    (V : Fin D.count → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (h : G) :
    ∑ i, (Module.finrank k (V i) : k) * (V i).character h =
      if h = 1 then (Fintype.card G : k) else 0 := by
  split
  case isTrue heq =>
    subst heq
    simp only [FDRep.char_one]
    obtain ⟨σ, hσ⟩ := D.exists_reindex_dimension_eq_finrank V hV hinj
    have hcast : ∀ i, (Module.finrank k (V i) : k) = (D.dimension (σ i) : k) := by
      intro i; congr 1; exact (hσ i).symm
    simp_rw [hcast]
    rw [show ∑ i, (D.dimension (σ i) : k) * (D.dimension (σ i) : k) =
      ∑ j, (D.dimension j : k) * (D.dimension j : k) from
      Finset.sum_equiv σ (fun _ => by simp) (fun _ _ => rfl)]
    rw [← D.sum_dimension_sq_eq_card]; push_cast; congr 1; ext i; ring
  case isFalse hne =>
    exact RepresentationTheory.FDRep.RegularRepresentationCharacter.sum_finrank_mul_character_eq_zero_of_ne_one
      D V hV hinj h hne

/-- Relates the number of group elements whose square is one to the sum of their representation-theoretic contributions over a simple, pairwise nonisomorphic family. -/
@[source_ref "Chapter5/Theorem5.1.5" (role := primary)]
theorem card_sq_eq_one_eq_sum_finrank_mul_auxiliaryInvariant
    [DecidableEq G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    [Invertible (Fintype.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G)
    (V : Fin D.count → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) :
    (Finset.univ.filter (fun g : G => g * g = 1)).card =
    ∑ i : Fin D.count, Module.finrank k (V i) * auxiliaryInvariant (V i) := by
  simp only [auxiliaryInvariant]
  simp_rw [mul_smul_comm]
  rw [← Finset.smul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_dim_char_eq_regularChar D V hV hinj]
  rw [← Finset.sum_filter, Finset.sum_const]
  simp only [nsmul_eq_mul, smul_eq_mul]
  rw [invOf_eq_inv]
  have hne : (Fintype.card G : k) ≠ 0 := Invertible.ne_zero _
  field_simp [hne]

section ComplexIndicatorForm

variable {G : Type} [Group G] [Fintype G]

/-- Identifies the auxiliary representation invariant with the invariant obtained from its action map. -/
lemma representationInvariant_eq_auxiliaryInvariant
    [DecidableEq G] [Invertible (Fintype.card G : ℂ)]
    (V : FDRep ℂ G) :
    RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar V.ρ =
      auxiliaryInvariant V := by
  simp only [RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar,
    auxiliaryInvariant, FDRep.character, invOf_eq_inv, smul_eq_mul]

/-- Expresses the number of group elements whose square is one as a sum over a simple, pairwise nonisomorphic family of complex representations. -/
@[source_ref "Chapter5/Theorem5.1.5" (role := primary)]
theorem card_sq_eq_one_eq_sum_representationInvariant_mul_finrank
    [DecidableEq G] [NeZero (Nat.card G : ℂ)] [Invertible (Fintype.card G : ℂ)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData ℂ G)
    (V : Fin D.count → FDRep ℂ G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) :
    ((Finset.univ.filter (fun g : G => g * g = 1)).card : ℂ) =
      ∑ i : Fin D.count,
        RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar (V i).ρ *
          (Module.finrank ℂ (V i) : ℂ) := by
  rw [card_sq_eq_one_eq_sum_finrank_mul_auxiliaryInvariant D V hV hinj]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [representationInvariant_eq_auxiliaryInvariant, mul_comm]

end ComplexIndicatorForm

end RepresentationTheory.FDRep.Auxiliary
