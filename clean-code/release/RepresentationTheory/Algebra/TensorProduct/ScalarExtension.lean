/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.RingTheory.TensorProduct.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Scalar extension for tensor products -/

namespace RepresentationTheory.Algebra.TensorProduct.ScalarExtension

open scoped TensorProduct

variable (K L A V : Type*) [CommRing K] [CommRing L] [Algebra K L] [Ring A] [Algebra K A]

/-- Algebra structure over the right scalar algebra on a tensor product. -/
@[source_ref "Chapter2/Exercise2.11.5" (role := primary)]
noncomputable instance rightTensorProductAlgebra :
    Algebra L (_root_.TensorProduct K A L) :=
  Algebra.TensorProduct.rightAlgebra

/-- The algebra map into a tensor product sends a scalar to the pure tensor with left factor one. -/
@[source_ref "Chapter2/Exercise2.11.5" (role := supporting)]
theorem algebraMap_apply (l : L) :
    (algebraMap L (_root_.TensorProduct K A L)) l = 1 ⊗ₜ[K] l :=
  rfl

/-- Existence of a module structure on a tensor product with the stated pure-tensor scalar action. -/
@[source_ref "Chapter2/Exercise2.11.5" (role := supporting)]
theorem exists_tensorProductModule [AddCommGroup V] [Module K V] [Module A V]
    [IsScalarTower K A V] :
    ∃ inst : Module (_root_.TensorProduct K A L) (_root_.TensorProduct K V L),
      ∀ (a : A) (l l' : L) (v : V),
        (letI := inst; (a ⊗ₜ[K] l) • (v ⊗ₜ[K] l')) = (a • v) ⊗ₜ[K] (l * l') := by
  let e : (_root_.TensorProduct K V L) ≃ₗ[K] (_root_.TensorProduct K L V) :=
    TensorProduct.comm K V L
  letI sm : SMul L (_root_.TensorProduct K V L) := ⟨fun l x => e.symm (l • e x)⟩
  have hsmul : ∀ (l : L) (x : _root_.TensorProduct K V L), e (l • x) = l • e x :=
    fun l x => e.apply_symm_apply _
  letI mod : Module L (_root_.TensorProduct K V L) :=
    Function.Injective.module L e.toLinearMap.toAddMonoidHom e.injective hsmul
  have smul_tmul_L : ∀ (l l' : L) (v : V), l • (v ⊗ₜ[K] l') = v ⊗ₜ[K] (l * l') := by
    intro l l' v
    apply e.injective
    rw [hsmul]
    simp only [e, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  letI tower : IsScalarTower K L (_root_.TensorProduct K V L) := by
    refine ⟨fun k l x => e.injective ?_⟩
    simp only [hsmul, map_smul]
    exact smul_assoc k l (e x)
  letI comm : SMulCommClass A L (_root_.TensorProduct K V L) := by
    refine ⟨fun a l x => ?_⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v l' =>
      rw [smul_tmul_L, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_tmul_L]
    | add x y hx hy => simp only [smul_add, hx, hy]
  refine ⟨TensorProduct.Algebra.module, fun a l l' v => ?_⟩
  rw [TensorProduct.Algebra.smul_def, smul_tmul_L, TensorProduct.smul_tmul']

end RepresentationTheory.Algebra.TensorProduct.ScalarExtension

attribute [nolint defsWithUnderscore]
  RepresentationTheory.Algebra.TensorProduct.ScalarExtension.rightTensorProductAlgebra
