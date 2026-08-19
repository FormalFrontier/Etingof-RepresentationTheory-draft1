/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.Auxiliary
import RepresentationTheory.AuxiliaryQuiverRepresentationDimensions
import RepresentationTheory.Alignment.Attribute

/-!
# Vertex orders for finite quivers
-/

namespace RepresentationTheory.Quiver.VertexOrder.Quiver

open RepresentationTheory Module

universe u

/-- A compatible finite quiver admits an ordering in which the target of every arrow precedes its source. -/
theorem exists_order_target_lt_source {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    [Q : Quiver.{0, 0} (Fin n)]
    (hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj) :
    ∃ order : Fin n ≃ Fin n,
      ∀ {v w : Fin n}, (v ⟶ w) → (order w : ℕ) < (order v : ℕ) := by
  classical
  obtain ⟨ordering, hperm, hnodup, htopo⟩ :=
    RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_exists_ordering_no_hom_of_le
      hDynkin hQ
  have hlen : ordering.length = n := by
    rw [hperm.length_eq, List.length_finRange]
  have hlt : ∀ j : Fin n, (j : ℕ) < ordering.length := fun j => by rw [hlen]; exact j.isLt
  set g : Fin n → Fin n := fun j => ordering.get ⟨(j : ℕ), hlt j⟩ with hg
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 := hnodup.injective_get hab
    have h2 : (a : ℕ) = (b : ℕ) := by simpa using h1
    exact Fin.ext h2
  set G : Fin n ≃ Fin n := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj) with hG
  refine ⟨G.symm, ?_⟩
  intro v w arr
  by_contra hcon
  have hle : ((G.symm v : Fin n) : ℕ) ≤ ((G.symm w : Fin n) : ℕ) := by omega
  have hv : ordering.get ⟨((G.symm v : Fin n) : ℕ), hlt _⟩ = v := G.apply_symm_apply v
  have hw : ordering.get ⟨((G.symm w : Fin n) : ℕ), hlt _⟩ = w := G.apply_symm_apply w
  have hempty := htopo ((G.symm v : Fin n) : ℕ) ((G.symm w : Fin n) : ℕ) (hlt _) (hlt _) hle
  rw [hv, hw] at hempty
  exact hempty.elim arr

/-- Under the stated compatibility and thinness assumptions, there is a witness whose associated natural-number values agree with the supplied integer vector, as do those of a further witness. -/
@[source_ref "Chapter6/Problem6.9.3" (role := primary)]
theorem exists_witness_with_prescribed_values
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (α : Fin n → ℤ)
    (hα : RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj α)
    (k : Type u) [Field k]
    [Q : Quiver.{0, 0} (Fin n)]
    (hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ a b : Fin n, Subsingleton (a ⟶ b)] :
    ∃ Vα : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, u, 0}
        k (Fin n),
      Vα.AuxiliaryCondition ∧
      (∀ v, (RepresentationTheory.Quiver.Auxiliary.auxiliaryVertexValue Vα v : ℤ) = α v) ∧
      ∃ s : RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.VertexCompositionSeries Vα,
        ∀ i, (s.multiplicity i : ℤ) = α i := by
  classical
  obtain ⟨Vα, hFree, hFinite, hIndec, hdim⟩ :=
    RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliary_exists_representation_finrank_eq
      hDynkin α hα k hQ
  obtain ⟨order, horder⟩ := exists_order_target_lt_source hDynkin hQ
  have hdv : ∀ v, Module.finrank k (Vα.obj v) = (α v).toNat := by
    intro v
    have := hdim v
    omega
  have basis : ∀ v, Basis (Fin ((α v).toNat)) k (Vα.obj v) := by
    intro v
    haveI := hFree v
    haveI := hFinite v
    exact Module.finBasisOfFinrankEq k (Vα.obj v) (hdv v)
  obtain ⟨s, _, hmult⟩ :=
    RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.exists_vertexCompositionSeries_with_multiplicity
      Vα n order horder (fun v => (α v).toNat) basis
  refine ⟨Vα, hIndec, fun v => ?_, s, fun i => ?_⟩
  · rw [RepresentationTheory.Quiver.Auxiliary.auxiliaryVertexValue, hdv v]
    have := hdim v
    omega
  · rw [hmult i]
    have := hdim i
    omega

end RepresentationTheory.Quiver.VertexOrder.Quiver
