/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Group.CharacterAuxiliary
import RepresentationTheory.Alignment.Attribute

open FDRep CategoryTheory CategoryTheory.MonoidalCategory Representation
open scoped Matrix ComplexOrder

universe u

namespace RepresentationTheory.Group.CharacterOperations

variable {k G : Type u} [Field k] [Group G]

/-- The character of a tensor product is the product of the two characters. -/
@[source_ref "Chapter4/Discussion_4.4" (role := primary)]
theorem character_tensor (V W : FDRep k G) (g : G) :
    (V ⊗ W).character g = V.character g * W.character g := by
  rw [FDRep.char_tensor]; rfl

/-- The character of the dual representation is the character evaluated at the inverse group element. -/
@[source_ref "Chapter4/Discussion_4.4" (role := primary)]
theorem character_dual (V : FDRep k G) (g : G) :
    (of (dual V.ρ)).character g = V.character g⁻¹ :=
  FDRep.char_dual V g

section Complex

variable [Finite G]

/-- For a finite group over the complex numbers, character evaluation at an inverse is complex conjugation. -/
@[source_ref "Chapter4/Discussion_4.4" (role := primary)]
theorem character_inv_eq_conj (V : FDRep ℂ G) (g : G) :
    V.character g⁻¹ = (starRingEnd ℂ) (V.character g) := by
  classical
  letI := Fintype.ofFinite G
  haveI : Nonempty G := ⟨1⟩
  let b := Module.finBasis ℂ V
  set M : G → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun h => LinearMap.toMatrix b b (V.ρ h) with hM
  have hM_mul : ∀ a c : G, M (a * c) = M a * M c := by
    intro a c; simp only [hM, map_mul, LinearMap.toMatrix_mul]
  have hM_one : M 1 = 1 := by simp only [hM, map_one, LinearMap.toMatrix_one]
  have hchar : ∀ h : G, V.character h = (M h).trace := by
    intro h; simp only [FDRep.character, hM]; rw [LinearMap.trace_eq_matrix_trace ℂ b]
  have hunit : ∀ h : G, IsUnit (M h) := fun h =>
    ⟨⟨M h, M h⁻¹, by rw [← hM_mul, mul_inv_cancel, hM_one],
      by rw [← hM_mul, inv_mul_cancel, hM_one]⟩, rfl⟩
  have hdet : ∀ h : G, IsUnit (M h).det :=
    fun h => (Matrix.isUnit_iff_isUnit_det _).mp (hunit h)
  have hginv : (M g)⁻¹ = M g⁻¹ :=
    Matrix.inv_eq_left_inv (by rw [← hM_mul, inv_mul_cancel, hM_one])
  set H : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    ∑ h : G, (M h)ᴴ * M h with hH
  have hH_pd : H.PosDef := by
    rw [hH]
    refine Matrix.posDef_sum Finset.univ_nonempty (fun h _ => ?_)
    have := (Matrix.IsUnit.posDef_star_left_conjugate_iff (hunit h)).mpr Matrix.PosDef.one
    simpa [Matrix.star_eq_conjTranspose] using this
  have hH_det : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).mp hH_pd.isUnit
  have hinv : (M g)ᴴ * H * M g = H := by
    have step : ∀ h : G, (M g)ᴴ * ((M h)ᴴ * M h) * M g = (M (h * g))ᴴ * M (h * g) := by
      intro h; rw [hM_mul, Matrix.conjTranspose_mul]; simp only [mul_assoc]
    calc (M g)ᴴ * H * M g
        = ∑ h : G, (M g)ᴴ * ((M h)ᴴ * M h) * M g := by rw [hH, Finset.mul_sum, Finset.sum_mul]
      _ = ∑ h : G, (M (h * g))ᴴ * M (h * g) := Finset.sum_congr rfl (fun h _ => step h)
      _ = ∑ h : G, (M h)ᴴ * M h := Equiv.sum_comp (Equiv.mulRight g) fun h => (M h)ᴴ * M h
      _ = H := rfl
  have e1 : (M g)ᴴ * H = H * (M g)⁻¹ := by
    have h2 : (M g)ᴴ * H * M g * (M g)⁻¹ = H * (M g)⁻¹ := by rw [hinv]
    rwa [mul_assoc ((M g)ᴴ * H) (M g) (M g)⁻¹, Matrix.mul_nonsing_inv _ (hdet g), mul_one] at h2
  have hconj : (M g)ᴴ = H * (M g)⁻¹ * H⁻¹ := by
    calc (M g)ᴴ = (M g)ᴴ * H * H⁻¹ := by
          rw [mul_assoc, Matrix.mul_nonsing_inv _ hH_det, mul_one]
      _ = H * (M g)⁻¹ * H⁻¹ := by rw [e1]
  rw [hchar g⁻¹, hchar g, starRingEnd_apply, ← Matrix.trace_conjTranspose, hconj,
    Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hH_det, one_mul, hginv]

/-- A complex representation is isomorphic to its dual exactly when every value of its character is fixed by complex conjugation. -/
@[source_ref "Chapter4/Discussion_4.4" (role := primary)]
theorem dual_iso_iff_character_star_eq {G : Type} [Group G] [Finite G] (V : FDRep ℂ G) :
    Nonempty (of (dual V.ρ) ≅ V) ↔
      ∀ g : G, (starRingEnd ℂ) (V.character g) = V.character g := by
  constructor
  · rintro ⟨e⟩ g
    have h : V.character g⁻¹ = V.character g := by
      have h0 := congrFun (FDRep.char_iso e) g
      rwa [FDRep.char_dual] at h0
    rw [← character_inv_eq_conj, h]
  · intro hreal
    classical
    have hchar_eq : FDRep.character (of (dual V.ρ)) = FDRep.character V := by
      funext g
      rw [character_dual V g, character_inv_eq_conj V g]
      exact hreal g
    exact RepresentationTheory.Group.CharacterAuxiliary.iso_of_character_eq G (of (dual V.ρ)) V hchar_eq

end Complex

end RepresentationTheory.Group.CharacterOperations
