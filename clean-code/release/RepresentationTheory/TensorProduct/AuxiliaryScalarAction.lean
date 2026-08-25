/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Homology.TensorProductConstruction

/-!
# An auxiliary scalar action on a tensor-product construction
-/

open TensorProduct

namespace RepresentationTheory.TensorProduct.AuxiliaryScalarAction

universe u

variable (k : Type u) [CommRing k]
variable (A : Type u) [Ring A]
variable (N : Type u) [AddCommGroup N] [Module A N]
variable (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M]
  [Module k M] [SMulCommClass k Aᵐᵒᵖ M]

/-- Shows that the displayed auxiliary membership predicate is closed under scalar multiplication. -/
theorem TensorProduct.Auxiliary.smul_mem (c : k) {x : TensorProduct ℤ M N}
    (hx : x ∈ RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup
      A N M) :
    c • x ∈ RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup
      A N M := by
  have h : RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup
      A N M ≤
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup
        A N M).comap (DistribSMul.toAddMonoidHom (TensorProduct ℤ M N) c) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨a, m, n, rfl⟩
    change c • ((MulOpposite.op a • m) ⊗ₜ[ℤ] n - m ⊗ₜ[ℤ] (a • n)) ∈
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A N M
    rw [smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_comm c (MulOpposite.op a) m]
    exact AddSubgroup.subset_closure ⟨a, c • m, n, rfl⟩
  exact AddSubgroup.mem_comap.mp (h hx)

/-- Defines the indicated scalar action on the auxiliary target. -/
noncomputable instance TensorProduct.Auxiliary.scalarAction :
    SMul k
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M) where
  smul c := QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom _ c)
    (fun _ hx => AddSubgroup.mem_comap.mpr (TensorProduct.Auxiliary.smul_mem k A N M c hx))

variable {k A N M}

/-- Computes scalar multiplication on the quotient class of a tensor product element. -/
@[simp]
theorem TensorProduct.Auxiliary.smul_mk (c : k) (x : TensorProduct ℤ M N) :
    c • (QuotientAddGroup.mk x :
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M) =
      QuotientAddGroup.mk (c • x) := rfl

variable (k A N M)

/-- Provides the indicated module structure over the commutative scalar ring for the auxiliary target. -/
noncomputable instance TensorProduct.Auxiliary.moduleStructure :
    Module k
      (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M) where
  one_smul x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a => rw [TensorProduct.Auxiliary.smul_mk, one_smul]
  mul_smul c d x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a => rw [TensorProduct.Auxiliary.smul_mk, TensorProduct.Auxiliary.smul_mk,
        TensorProduct.Auxiliary.smul_mk, mul_smul]
  smul_zero c := by
    rw [← QuotientAddGroup.mk_zero, TensorProduct.Auxiliary.smul_mk, smul_zero]
  smul_add c x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b => rw [← QuotientAddGroup.mk_add, TensorProduct.Auxiliary.smul_mk,
          TensorProduct.Auxiliary.smul_mk, TensorProduct.Auxiliary.smul_mk,
          ← QuotientAddGroup.mk_add, smul_add]
  add_smul c d x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a => rw [TensorProduct.Auxiliary.smul_mk, TensorProduct.Auxiliary.smul_mk,
        TensorProduct.Auxiliary.smul_mk, ← QuotientAddGroup.mk_add, add_smul]
  zero_smul x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a => rw [TensorProduct.Auxiliary.smul_mk, zero_smul, QuotientAddGroup.mk_zero]

end RepresentationTheory.TensorProduct.AuxiliaryScalarAction
