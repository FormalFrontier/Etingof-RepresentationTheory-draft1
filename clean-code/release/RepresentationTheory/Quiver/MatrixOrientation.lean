/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.QuiverVertexReversal

/-!
# Matrix orientations of quivers
-/

namespace RepresentationTheory.Quiver.MatrixOrientation

open scoped Matrix

universe v_arrow in
private lemma nonempty_of_eq {X Y : Sort v_arrow} (h : X = Y) :
    Nonempty X → Nonempty Y :=
  fun hx => match h with | rfl => hx

universe v_arrow in
private lemma isEmpty_of_eq {X Y : Sort v_arrow} (h : X = Y) :
    IsEmpty Y → IsEmpty X :=
  fun hy => match h with | rfl => hy

/-- Records that a quiver on `Fin n` realizes the orientation data encoded by an integer adjacency matrix. -/
def IsMatrixOrientation {n : ℕ} (Q : Quiver (Fin n))
    (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j : Fin n, adj i j ≠ 1 → IsEmpty (Q.Hom i j)) ∧
  (∀ i j : Fin n, adj i j = 1 → Nonempty (Q.Hom i j) ∨ Nonempty (Q.Hom j i)) ∧
  (∀ i j : Fin n, Nonempty (Q.Hom i j) → Nonempty (Q.Hom j i) → False)

/-- Builds a quiver on `Fin n` from an integer adjacency matrix. -/
def quiverOfAdjacencyMatrix {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) :
    Quiver (Fin n) where
  Hom i j := PLift (adj i j = 1 ∧ i < j)

/-- Between any two vertices, the quiver constructed from an adjacency matrix has at most one arrow. -/
instance quiverOfAdjacencyMatrix_hom_subsingleton {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) :
    Subsingleton (@Quiver.Hom (Fin n) (quiverOfAdjacencyMatrix adj) a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- The quiver constructed from a symmetric zero-diagonal matrix realizes the matrix as an orientation. -/
theorem quiverOfAdjacencyMatrix_isMatrixOrientation {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ) (hsymm : adj.IsSymm) (hdiag : ∀ i, adj i i = 0) :
    IsMatrixOrientation (quiverOfAdjacencyMatrix adj) adj := by
  have adj_symm : ∀ i j, adj i j = adj j i := by
    intro i j
    have := congr_fun (congr_fun hsymm j) i
    simpa [Matrix.transpose_apply] using this
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · constructor
    rintro ⟨⟨he, _⟩⟩
    exact hij he
  · have hne : i ≠ j := by
      rintro rfl; rw [hdiag] at hij; exact one_ne_zero hij.symm
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨⟨hij, h⟩⟩
    · exact Or.inr ⟨⟨by rw [adj_symm]; exact hij, h⟩⟩
  · obtain ⟨⟨_, hlt⟩⟩ := hi
    obtain ⟨⟨_, hgt⟩⟩ := hj
    exact absurd (hlt.trans hgt) (lt_irrefl i)

/-- Reorienting a matrix-compatible quiver at a vertex preserves its matrix orientation when the matrix is symmetric with zero diagonal. -/
lemma isMatrixOrientation_vertexReorientation
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hadj_symm : adj.IsSymm) (hnoloop : ∀ v, adj v v = 0)
    {Q : Quiver (Fin n)} (hQ : IsMatrixOrientation Q adj) (p : Fin n) :
    IsMatrixOrientation
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q p) adj := by
  obtain ⟨hQ_nonarrow, hQ_edge, hQ_unique⟩ := hQ
  have adj_symm : ∀ i j, adj i j = adj j i := by
    intro i j
    have := congr_fun (congr_fun hadj_symm j) i
    simp [Matrix.transpose_apply] at this
    exact this
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a b ha_arr hb_arr => ?_⟩
  · by_cases ha : a = p <;> by_cases hb : b = p
    · exact isEmpty_of_eq
        (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq ha hb)
        (hQ_nonarrow a b hab)
    · exact isEmpty_of_eq
        (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne ha hb)
        (hQ_nonarrow b p fun h => hab (by rw [ha, adj_symm p b]; exact h))
    · exact isEmpty_of_eq
        (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq ha hb)
        (hQ_nonarrow p a fun h => hab (by rw [hb, adj_symm a p]; exact h))
    · exact isEmpty_of_eq
        (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha hb)
        (hQ_nonarrow a b hab)
  · by_cases ha : a = p <;> by_cases hb : b = p
    · exact absurd (by rw [ha, hb] at hab; rw [hnoloop] at hab; exact hab.symm) one_ne_zero
    · have h_bp : adj b p = 1 := by rw [adj_symm b p, ← ha]; exact hab
      rcases hQ_edge b p h_bp with h | h
      · left; exact nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne ha hb).symm h
      · right; exact nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq hb ha).symm h
    · have h_pa : adj p a = 1 := by rw [adj_symm p a, ← hb]; exact hab
      rcases hQ_edge p a h_pa with h | h
      · left; exact nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq ha hb).symm h
      · right; exact nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne hb ha).symm h
    · rcases hQ_edge a b hab with h | h
      · left; exact nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha hb).symm h
      · right; exact nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne hb ha).symm h
  · by_cases ha : a = p <;> by_cases hb : b = p
    · exact hQ_unique a b
        (nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq ha hb) ha_arr)
        (nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq hb ha) hb_arr)
    · exact hQ_unique b p
        (nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne ha hb) ha_arr)
        (nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq hb ha) hb_arr)
    · exact hQ_unique p a
        (nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq ha hb) ha_arr)
        (nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne hb ha) hb_arr)
    · exact hQ_unique a b
        (nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha hb) ha_arr)
        (nonempty_of_eq
          (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne hb ha) hb_arr)

end RepresentationTheory.Quiver.MatrixOrientation
