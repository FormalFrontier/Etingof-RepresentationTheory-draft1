/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.AdjacencyMatrixQuadraticForms
import RepresentationTheory.Quiver.Representation.MatrixModel
import RepresentationTheory.Quiver.MatrixOrientation

namespace RepresentationTheory.Quiver.AdjacencyQuadraticForm

open Matrix

variable {n : ℕ} [Q : Quiver.{0} (Fin n)]
  [∀ i j : Fin n, Fintype (i ⟶ j)] [∀ i j : Fin n, Subsingleton (i ⟶ j)]

/-- For a quiver compatible with a symmetric zero-one adjacency matrix, the number of arrows from one vertex to another plus the number in the reverse direction equals the corresponding adjacency entry. -/
theorem arrow_count_add_reverse_eq_adjacency_entry
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    (i j : Fin n) :
    (RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount i j : ℤ) +
      (RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount j i : ℤ) =
        adj i j := by
  classical
  have adj_symm : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congr_fun (congr_fun hsymm b) a
    simpa [Matrix.transpose_apply] using h
  have card_eq : ∀ a b : Fin n,
      (RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount a b : ℤ) =
        if Nonempty (a ⟶ b) then 1 else 0 := by
    intro a b
    by_cases h : Nonempty (a ⟶ b)
    · have hc : RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount a b = 1 :=
        le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr inferInstance)
          (Fintype.card_pos_iff.mpr h)
      rw [hc, if_pos h]; norm_num
    · have hc : RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount a b = 0 :=
        Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp h)
      rw [hc, if_neg h]; norm_num
  rw [card_eq i j, card_eq j i]
  rcases h01 i j with h0 | h1
  · have hji : adj j i = 0 := by rw [adj_symm j i]; exact h0
    have e1 : ¬ Nonempty (i ⟶ j) :=
      not_nonempty_iff.mpr (hQ.1 i j (by rw [h0]; norm_num))
    have e2 : ¬ Nonempty (j ⟶ i) :=
      not_nonempty_iff.mpr (hQ.1 j i (by rw [hji]; norm_num))
    rw [if_neg e1, if_neg e2, h0]; norm_num
  · rcases hQ.2.1 i j h1 with hn | hn
    · have hnot : ¬ Nonempty (j ⟶ i) := fun hm => hQ.2.2 i j hn hm
      rw [if_pos hn, if_neg hnot, h1]; norm_num
    · have hnot : ¬ Nonempty (i ⟶ j) := fun hm => hQ.2.2 j i hn hm
      rw [if_neg hnot, if_pos hn, h1]; norm_num

/-- For every natural dimension vector of a quiver compatible with a symmetric zero-one adjacency matrix, evaluating twice the identity minus the adjacency matrix on that vector gives twice the difference between the coordinate square sum and the arrow-weighted product sum. -/
theorem two_identity_sub_adjacency_quadratic_eq_twice_quiver_form
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    (m : Fin n → ℕ) :
    dotProduct (fun i => (m i : ℤ)) ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec
        (fun i => (m i : ℤ))) =
      2 * ((∑ i, ((m i : ℤ)) ^ 2) -
        ∑ i, ∑ j, (RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount i j : ℤ) *
          ((m i : ℤ) * (m j : ℤ))) := by
  have hswap :
      (∑ i, ∑ j, (RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount j i : ℤ) *
        ((m i : ℤ) * (m j : ℤ))) =
      ∑ i, ∑ j, (RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount i j : ℤ) *
        ((m i : ℤ) * (m j : ℤ)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hadj_sum : (∑ i, ∑ j, adj i j * (m i : ℤ) * (m j : ℤ)) =
      2 * ∑ i, ∑ j,
        (RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount i j : ℤ) *
          ((m i : ℤ) * (m j : ℤ)) := by
    have hsplit : (∑ i, ∑ j, adj i j * (m i : ℤ) * (m j : ℤ)) =
        (∑ i, ∑ j,
          (RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount i j : ℤ) *
            ((m i : ℤ) * (m j : ℤ))) +
          (∑ i, ∑ j,
            (RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount j i : ℤ) *
              ((m i : ℤ) * (m j : ℤ))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← arrow_count_add_reverse_eq_adjacency_entry adj hsymm h01 hQ i j]; ring
    rw [hsplit, hswap]; ring
  rw [RepresentationTheory.AdjacencyMatrixQuadraticForms.two_smul_one_sub_quadratic_eq,
    hadj_sum]
  have hsq : (∑ i, (m i : ℤ) * (m i : ℤ)) = ∑ i, ((m i : ℤ)) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [hsq]; ring

/-- For a quiver compatible with a symmetric zero-one adjacency matrix, assume every nonzero natural dimension vector has arrow-weighted product sum strictly smaller than its coordinate square sum. Then the quadratic form associated with twice the identity minus the adjacency matrix is positive on every nonzero coordinatewise nonnegative integer vector. -/
theorem quadratic_pos_on_nonnegative_int_vectors_of_arrow_sum_lt_square_sum
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    (hstrict : ∀ m : Fin n → ℕ, m ≠ 0 →
      (∑ i, ∑ j, RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount i j *
        (m i * m j)) < ∑ i, (m i) ^ 2) :
    ∀ x : Fin n → ℤ, (∀ i, 0 ≤ x i) → x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) := by
  intro x hx hne
  classical
  set m : Fin n → ℕ := fun i => (x i).toNat with hm
  have hcast : ∀ i, ((m i : ℤ)) = x i := fun i => Int.toNat_of_nonneg (hx i)
  have hx_eq : x = fun i => (m i : ℤ) := funext fun i => (hcast i).symm
  have hmne : m ≠ 0 := by
    intro h
    apply hne
    funext i
    have hmi : (m i : ℤ) = 0 := by simp [congrFun h i]
    rw [← hcast i, hmi]; simp
  have hltZ :
      (∑ i, ∑ j, (RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount i j : ℤ) *
        ((m i : ℤ) * (m j : ℤ))) < ∑ i, ((m i : ℤ)) ^ 2 := by
    have h :
        ((∑ i, ∑ j, RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount i j *
          (m i * m j) : ℕ) : ℤ) < ((∑ i, (m i) ^ 2 : ℕ) : ℤ) := by
      exact_mod_cast hstrict m hmne
    push_cast at h
    convert h using 2
  rw [hx_eq, two_identity_sub_adjacency_quadratic_eq_twice_quiver_form
    adj hsymm h01 hQ m]
  have hX : 0 < (∑ i, ((m i : ℤ)) ^ 2) -
      ∑ i, ∑ j, (RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount i j : ℤ) *
        ((m i : ℤ) * (m j : ℤ)) := by
    linarith [hltZ]
  linarith [hX]

/-- Let a symmetric loopless zero-one adjacency matrix be connected by edges of weight one and compatible with a quiver. If every nonzero natural dimension vector has arrow-weighted product sum strictly smaller than its coordinate square sum, then the adjacency matrix is of simply laced Dynkin type. -/
theorem is_simply_laced_dynkin_of_arrow_sum_lt_square_sum
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (hloop : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    (hstrict : ∀ m : Fin n → ℕ, m ≠ 0 →
      (∑ i, ∑ j, RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount i j *
        (m i * m j)) < ∑ i, (m i) ^ 2) :
    RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj :=
  RepresentationTheory.AdjacencyMatrixQuadraticForms.connected_zero_one_adjacency_quadratic_pos
    adj hsymm hloop h01 hconn
      (quadratic_pos_on_nonnegative_int_vectors_of_arrow_sum_lt_square_sum
        adj hsymm h01 hQ hstrict)

set_option linter.unusedFintypeInType false in
/-- Let a symmetric loopless zero-one adjacency matrix be connected by edges of weight one and compatible with a quiver. If, over a field, the quiver representation space has smaller finite dimension than the product of the vertex endomorphism spaces for every nonzero dimension vector, then the adjacency matrix is of simply laced Dynkin type. -/
theorem is_simply_laced_dynkin_of_representation_finrank_lt_vertex_endomorphism_finrank
    (k : Type) [Field k] (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (hloop : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    (hstrict : ∀ m : Fin n → ℕ, m ≠ 0 →
      Module.finrank k
          (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m) <
        Module.finrank k (∀ i : Fin n, Matrix (Fin (m i)) (Fin (m i)) k)) :
    RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj := by
  refine is_simply_laced_dynkin_of_arrow_sum_lt_square_sum
    adj hsymm hloop h01 hconn hQ ?_
  intro m hmne
  have h := hstrict m hmne
  rwa [RepresentationTheory.Quiver.Representation.MatrixModel.finrank_matrixData (k := k),
    RepresentationTheory.Quiver.Representation.MatrixModel.finrank_vertexMatrixFamily (k := k)] at h

end RepresentationTheory.Quiver.AdjacencyQuadraticForm

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.Quiver.AdjacencyQuadraticForm.Auxiliary.statement020829 := _root_.RepresentationTheory.Quiver.AdjacencyQuadraticForm.is_simply_laced_dynkin_of_arrow_sum_lt_square_sum

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.Quiver.AdjacencyQuadraticForm.Auxiliary.statement020831 := _root_.RepresentationTheory.Quiver.AdjacencyQuadraticForm.is_simply_laced_dynkin_of_representation_finrank_lt_vertex_endomorphism_finrank
