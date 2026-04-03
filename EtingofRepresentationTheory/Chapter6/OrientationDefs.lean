import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_6_2

/-!
# Orientation Definitions for Quivers

This file defines `IsOrientationOf` (linking an oriented quiver Q to an unoriented
adjacency matrix adj) and proves that `reversedAtVertex` preserves this property.

These definitions are used both by the main Gabriel's theorem files (Corollary 6.8.4)
and by the Coxeter infrastructure (admissible orderings). Extracting them here avoids
a circular import dependency.
-/

open scoped Matrix

universe v_arrow in
private lemma nonempty_of_eq {X Y : Sort v_arrow} (h : X = Y) :
    Nonempty X → Nonempty Y :=
  fun hx => match h with | rfl => hx

universe v_arrow in
private lemma isEmpty_of_eq {X Y : Sort v_arrow} (h : X = Y) :
    IsEmpty Y → IsEmpty X :=
  fun hy => match h with | rfl => hy

/-- A quiver `Q` on `Fin n` is an orientation of the undirected graph with adjacency
matrix `adj` if:
- for each edge (`adj i j = 1`), exactly one of `i ⟶ j` or `j ⟶ i` is inhabited;
- for non-edges (`adj i j ≠ 1`), no arrows exist in either direction.

This predicate connects the unoriented graph (encoded by `adj`) to the oriented
quiver `Q`, which is needed for Gabriel's theorem: the positive roots of the
Dynkin diagram correspond to indecomposable representations of any orientation. -/
def Etingof.IsOrientationOf {n : ℕ} (Q : Quiver (Fin n))
    (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  -- Non-edges have no arrows
  (∀ i j : Fin n, adj i j ≠ 1 → IsEmpty (Q.Hom i j)) ∧
  -- Each edge is oriented: exactly one direction
  (∀ i j : Fin n, adj i j = 1 → Nonempty (Q.Hom i j) ∨ Nonempty (Q.Hom j i)) ∧
  (∀ i j : Fin n, Nonempty (Q.Hom i j) → Nonempty (Q.Hom j i) → False)

/-- Reversing all arrows at a vertex preserves the orientation property. -/
lemma Etingof.reversedAtVertex_isOrientationOf
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hadj_symm : adj.IsSymm) (hnoloop : ∀ v, adj v v = 0)
    {Q : Quiver (Fin n)} (hQ : Etingof.IsOrientationOf Q adj) (p : Fin n) :
    Etingof.IsOrientationOf (@Etingof.reversedAtVertex (Fin n) _ Q p) adj := by
  obtain ⟨hQ_nonarrow, hQ_edge, hQ_unique⟩ := hQ
  have adj_symm : ∀ i j, adj i j = adj j i := by
    intro i j
    have := congr_fun (congr_fun hadj_symm j) i
    simp [Matrix.transpose_apply] at this
    exact this
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a b ha_arr hb_arr => ?_⟩
  · -- Non-edges: no arrows in reversed quiver
    by_cases ha : a = p <;> by_cases hb : b = p
    · exact isEmpty_of_eq (Etingof.ReversedAtVertexHom_eq_eq ha hb) (hQ_nonarrow a b hab)
    · exact isEmpty_of_eq (Etingof.ReversedAtVertexHom_eq_ne ha hb)
        (hQ_nonarrow b p fun h => hab (by rw [ha, adj_symm p b]; exact h))
    · exact isEmpty_of_eq (Etingof.ReversedAtVertexHom_ne_eq ha hb)
        (hQ_nonarrow p a fun h => hab (by rw [hb, adj_symm a p]; exact h))
    · exact isEmpty_of_eq (Etingof.ReversedAtVertexHom_ne_ne ha hb) (hQ_nonarrow a b hab)
  · -- Each edge has an arrow in reversed quiver
    by_cases ha : a = p <;> by_cases hb : b = p
    · exact absurd (by rw [ha, hb] at hab; rw [hnoloop] at hab; exact hab.symm) one_ne_zero
    · have h_bp : adj b p = 1 := by rw [adj_symm b p, ← ha]; exact hab
      rcases hQ_edge b p h_bp with h | h
      · left; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_ne ha hb).symm h
      · right; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_eq hb ha).symm h
    · have h_pa : adj p a = 1 := by rw [adj_symm p a, ← hb]; exact hab
      rcases hQ_edge p a h_pa with h | h
      · left; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_eq ha hb).symm h
      · right; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_ne hb ha).symm h
    · rcases hQ_edge a b hab with h | h
      · left; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_ne ha hb).symm h
      · right; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_ne hb ha).symm h
  · -- No two-way arrows in reversed quiver
    by_cases ha : a = p <;> by_cases hb : b = p
    · exact hQ_unique a b
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_eq ha hb) ha_arr)
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_eq hb ha) hb_arr)
    · exact hQ_unique b p
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_ne ha hb) ha_arr)
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_eq hb ha) hb_arr)
    · exact hQ_unique p a
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_eq ha hb) ha_arr)
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_ne hb ha) hb_arr)
    · exact hQ_unique a b
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_ne ha hb) ha_arr)
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_ne hb ha) hb_arr)
