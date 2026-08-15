/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.QuiverRepresentation.Auxiliary
import RepresentationTheory.Quiver.MatrixOrientation
import RepresentationTheory.Alignment.Attribute

section QuiverRepresentationIso

variable {k : Type*} [Field k] {n : ℕ} {Q : Quiver (Fin n)}

/-- The binary relation between two objects over the same finite quiver and base field. -/
def RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.Related
    (V W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n) _ Q) : Prop :=
  ∃ (e : ∀ v, V.obj v ≃ₗ[k] W.obj v),
    ∀ {a b : Fin n} (f : a ⟶ b),
      (e b).toLinearMap ∘ₗ V.map f = W.map f ∘ₗ (e a).toLinearMap

end QuiverRepresentationIso

/-- A square integer matrix satisfies the adjacency conditions for a finite quiver. -/
@[source_ref "Chapter6/Problem6.1.5" (role := supporting)]
def RepresentationTheory.Quiver.Finite.IsAdjacencyMatrix (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∃ (Q : @Quiver.{0, 0} (Fin n)),
      (∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)) ∧
        @RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation n Q adj) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k]
      (Q : @Quiver.{0, 0} (Fin n))
      [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)],
      @RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation n Q adj →
        ∃ reps : Set (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.{0, 0, 0, 0} k (Fin n)),
          reps.Finite ∧
          (∀ V ∈ reps, V.AuxiliaryCondition) ∧
          ∀ (W : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.{0, 0, 0, 0} k (Fin n)),
            (∀ v, Module.Free k (W.obj v)) → (∀ v, Module.Finite k (W.obj v)) →
              W.AuxiliaryCondition → ∃ V ∈ reps, W.Related V

/-- A zero-one quiver adjacency matrix has every diagonal entry equal to zero. -/
@[source_ref "Chapter6/Problem6.1.5_parts" (role := primary)]
theorem RepresentationTheory.Quiver.Finite.IsAdjacencyMatrix.diagonal_eq_zero_of_entries_eq_zero_or_one {n : ℕ}
    {adj : Matrix (Fin n) (Fin n) ℤ} (hft : RepresentationTheory.Quiver.Finite.IsAdjacencyMatrix n adj)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1) : ∀ i, adj i i = 0 := by
  obtain ⟨Q, _, hQ⟩ := hft.1
  intro i
  rcases h01 i i with hii | hii
  · exact hii
  · exfalso
    rcases hQ.2.1 i i hii with hi | hi
    · exact hQ.2.2 i i hi hi
    · exact hQ.2.2 i i hi hi
