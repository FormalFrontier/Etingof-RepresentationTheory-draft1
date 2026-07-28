import EtingofRepresentationTheory.Chapter2.Example2_9_12
import EtingofRepresentationTheory.Chapter2.Example2_9_13
import EtingofRepresentationTheory.Chapter2.Exercise2_9_5

/-!
# Concrete Lie-algebra examples in §2.9

The cross-product model of `ℝ³` is formalized in `Exercise2_9_5`, and the traceless-matrix
model of `𝔰𝔩₂` is formalized in `Example2_9_12`.  The one remaining identification in the
first half of the list is that the coordinate Heisenberg algebra from `Example2_9_13` is exactly
the Lie algebra of strictly upper-triangular `3 × 3` matrices.  This file supplies that
identification, matching the named basis `x = E₁₂`, `y = E₀₁`, `c = E₀₂` from the book.
-/

namespace Etingof.DiscussionConcreteLieExamples

open scoped Matrix
open Etingof.Example2_9_13

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type*) [CommRing k]

/-- The book's concrete Heisenberg Lie algebra: the strictly upper-triangular `3 × 3`
matrices `[[0, b, d], [0, 0, a], [0, 0, 0]]`. -/
def heisenbergMatrices : LieSubalgebra k (Matrix (Fin 3) (Fin 3) k) where
  carrier := {A | ∃ a b d : k, A = !![0, b, d; 0, 0, a; 0, 0, 0]}
  zero_mem' := ⟨0, 0, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  add_mem' := by
    rintro A B ⟨a, b, d, rfl⟩ ⟨a', b', d', rfl⟩
    refine ⟨a + a', b + b', d + d', ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  smul_mem' := by
    rintro t A ⟨a, b, d, rfl⟩
    refine ⟨t * a, t * b, t * d, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [smul_eq_mul]
  lie_mem' := by
    rintro A B ⟨a, b, d, rfl⟩ ⟨a', b', d', rfl⟩
    refine ⟨0, 0, b * a' - b' * a, ?_⟩
    rw [LieRing.of_associative_ring_bracket]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp

/-- The coordinate matrix of `(a,b,d) = a·x + b·y + d·c`. -/
def heisenbergToMatrix (u : Heisenberg k) : Matrix (Fin 3) (Fin 3) k :=
  !![0, u.2.1, u.2.2; 0, 0, u.1; 0, 0, 0]

/-- The coordinate matrix is strictly upper triangular. -/
theorem heisenbergToMatrix_mem (u : Heisenberg k) :
    heisenbergToMatrix k u ∈ heisenbergMatrices k :=
  ⟨u.1, u.2.1, u.2.2, rfl⟩

/-- The coordinate Heisenberg algebra of Example 2.9.13 is Lie-isomorphic to the concrete
matrix algebra in the book. -/
noncomputable def heisenbergMatrixEquiv :
    Heisenberg k ≃ₗ⁅k⁆ heisenbergMatrices k where
  toFun u := ⟨heisenbergToMatrix k u, heisenbergToMatrix_mem k u⟩
  map_add' u v := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisenbergToMatrix]
  map_smul' t u := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisenbergToMatrix]
  map_lie' {u v} := by
    apply Subtype.ext
    rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisenbergToMatrix, bracket_def]
    ring
  invFun A := (A.val 1 2, A.val 0 1, A.val 0 2)
  left_inv u := by
    apply Heisenberg.ext <;> simp [heisenbergToMatrix]
  right_inv A := by
    rcases A.property with ⟨a, b, d, hA⟩
    apply Subtype.ext
    change heisenbergToMatrix k (A.val 1 2, A.val 0 1, A.val 0 2) = A.val
    simp_rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisenbergToMatrix]

@[simp] theorem heisenbergMatrixEquiv_x :
    ((heisenbergMatrixEquiv k (x : Heisenberg k) : heisenbergMatrices k) :
      Matrix (Fin 3) (Fin 3) k) = Matrix.single 1 2 1 := by
  change heisenbergToMatrix k (x : Heisenberg k) = Matrix.single 1 2 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisenbergToMatrix, x]

@[simp] theorem heisenbergMatrixEquiv_y :
    ((heisenbergMatrixEquiv k (y : Heisenberg k) : heisenbergMatrices k) :
      Matrix (Fin 3) (Fin 3) k) = Matrix.single 0 1 1 := by
  change heisenbergToMatrix k (y : Heisenberg k) = Matrix.single 0 1 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisenbergToMatrix, y]

@[simp] theorem heisenbergMatrixEquiv_c :
    ((heisenbergMatrixEquiv k (c : Heisenberg k) : heisenbergMatrices k) :
      Matrix (Fin 3) (Fin 3) k) = Matrix.single 0 2 1 := by
  change heisenbergToMatrix k (c : Heisenberg k) = Matrix.single 0 2 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisenbergToMatrix, c]

end Etingof.DiscussionConcreteLieExamples
