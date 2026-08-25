/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FDRep.GroupAlgebraDecomposition

open CategoryTheory Representation

universe u

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [Invertible (Fintype.card G : k)]

namespace RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData

variable [NeZero (Nat.card G : k)] (D : DecompositionData k G) (i : Fin D.count)

private lemma projRingHom_smul (r : k) (α : MonoidAlgebra k G) :
    D.matrixBlockHom i (r • α) = r • D.matrixBlockHom i α := by
  change (Pi.evalRingHom _ i) (D.groupAlgebraEquivMatrix (r • α)) = r • (Pi.evalRingHom _ i) (D.groupAlgebraEquivMatrix α)
  rw [show D.groupAlgebraEquivMatrix (r • α) = r • D.groupAlgebraEquivMatrix α from map_smul D.groupAlgebraEquivMatrix r α]; simp [Pi.evalRingHom_apply, Pi.smul_apply]

private lemma projRingHom_mulVec_mem_subrepresentation
    (S : Subrepresentation (D.coordinateRepresentation i))
    (α : MonoidAlgebra k G) (v : Fin (D.dimension i) → k) (hv : v ∈ S.toSubmodule) :
    Matrix.mulVec (D.matrixBlockHom i α) v ∈ S.toSubmodule := by
  induction α using MonoidAlgebra.induction_on with
  | hM g =>
    have : (D.coordinateRepresentation i) g v = Matrix.mulVec (D.matrixBlockHom i (MonoidAlgebra.of k G g)) v := by
      simp [coordinateRepresentation, matrixBlockHom, MonoidAlgebra.of_apply]
    rw [← this]
    exact S.apply_mem_toSubmodule g hv
  | hadd a b ha hb =>
    rw [map_add, Matrix.add_mulVec]
    exact S.toSubmodule.add_mem ha hb
  | hsmul r a ha =>
    rw [projRingHom_smul, Matrix.smul_mulVec]
    exact S.toSubmodule.smul_mem r ha

private def toMatSubmodule (S : Subrepresentation (D.coordinateRepresentation i)) :
    Submodule (Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k) (Fin (D.dimension i) → k) where
  carrier := S.toSubmodule.carrier
  add_mem' := S.toSubmodule.add_mem'
  zero_mem' := S.toSubmodule.zero_mem'
  smul_mem' M v hv := by
    rw [Matrix.smul_eq_mulVec]
    obtain ⟨α, rfl⟩ := D.matrixBlockHom_surjective i M
    exact D.projRingHom_mulVec_mem_subrepresentation i S α v hv

/-- Every representation selected by an index from the given datum is irreducible. -/
instance isIrreducible : (D.coordinateRepresentation i).IsIrreducible := by
  haveI := D.dimension_neZero i
  haveI hSimple : IsSimpleModule (Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k) (Fin (D.dimension i) → k) :=
    isSimpleModule_matrix_fin (D.dimension i)
  refine {
    exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩
    eq_bot_or_eq_top := fun S => ?_ }
  · have hmem : Pi.single (0 : Fin (D.dimension i)) (1 : k) ∈
        (⊤ : Subrepresentation (D.coordinateRepresentation i)).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    have hne : (0 : Fin (D.dimension i) → k) ≠ Pi.single (0 : Fin (D.dimension i)) (1 : k) := by
      intro heq; have := congr_fun heq 0; simp at this
    exact hne (by change Pi.single 0 1 ∈ (⊥ : Submodule k _) at hmem; rw [Submodule.mem_bot] at hmem; exact hmem.symm)
  · rcases hSimple.eq_bot_or_eq_top (D.toMatSubmodule i S) with h | h
    · left; apply Subrepresentation.toSubmodule_injective
      apply le_antisymm
      · intro x hx
        have hx' : x ∈ (D.toMatSubmodule i S) := hx
        rw [h] at hx'; rw [Submodule.mem_bot] at hx'
        subst hx'; exact Submodule.zero_mem _
      · exact bot_le
    · right; apply Subrepresentation.toSubmodule_injective
      apply le_antisymm
      · exact le_top
      · intro x _
        change x ∈ (D.toMatSubmodule i S)
        rw [h]; exact Submodule.mem_top

private lemma columnRep_inv_mul_cancel (g : G) (v : Fin (D.dimension i) → k) :
    (D.coordinateRepresentation i) g⁻¹ ((D.coordinateRepresentation i) g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private lemma columnRep_mul_inv_cancel (g : G) (v : Fin (D.dimension i) → k) :
    (D.coordinateRepresentation i) g ((D.coordinateRepresentation i) g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

private noncomputable def invariantsEquivIntertwining :
    (Representation.linHom (D.coordinateRepresentation i) (D.coordinateRepresentation i)).invariants ≃ₗ[k]
      Representation.IntertwiningMap (D.coordinateRepresentation i) (D.coordinateRepresentation i) where
  toFun f := {
    toLinearMap := f.val
    isIntertwining' := fun g => by
      have hf := f.property g
      rw [Representation.linHom_apply] at hf
      apply LinearMap.ext; intro v
      simp only [LinearMap.comp_apply]
      have key := LinearMap.congr_fun hf.symm ((D.coordinateRepresentation i) g v)
      simp only [LinearMap.comp_apply, D.columnRep_inv_mul_cancel] at key
      exact key }
  invFun f := {
    val := f.toLinearMap
    property := fun g => by
      rw [Representation.linHom_apply]
      apply LinearMap.ext; intro v
      simp only [LinearMap.comp_apply]
      have := Representation.IntertwiningMap.isIntertwining _ _ f g ((D.coordinateRepresentation i) g⁻¹ v)
      rw [D.columnRep_mul_inv_cancel] at this
      exact this.symm }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

attribute [instance] DecompositionData.simple_representation

end RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData
