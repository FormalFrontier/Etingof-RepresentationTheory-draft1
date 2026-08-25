/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import RepresentationTheory.LinearAlgebra.ModuleDecompositions

/-! # Module family natural-number matrix -/

set_option linter.dupNamespace false

namespace RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]

/-- An auxiliary natural-number matrix associated with a family of modules. -/
noncomputable def matrix
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)] :
    Matrix ι ι ℕ :=
  Matrix.of fun i j => Module.finrank k (P i →ₗ[A] P j)

/-- The diagonal entry of the auxiliary matrix is positive for a finite nontrivial module. -/
theorem matrix_diagonal_pos
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, IsScalarTower k A (P i)]
    (i : ι) [Module.Finite k (P i)] [Nontrivial (P i)] :
    0 < matrix (k := k) (A := A) P i i := by
  change 0 < Module.finrank k (P i →ₗ[A] P i)
  haveI : Module.Finite k (P i →ₗ[A] P i) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A (P i) (P i) k)
      (LinearMap.restrictScalars_injective k)
  rw [Module.finrank_pos_iff (R := k)]
  obtain ⟨x, hx⟩ := exists_ne (0 : P i)
  refine nontrivial_of_ne (LinearMap.id : P i →ₗ[A] P i) 0 ?_
  intro h
  exact hx (by have := LinearMap.congr_fun h x; simpa using this)

/-- An auxiliary hypothesis yields positivity of the corresponding diagonal matrix entry. -/
theorem matrix_diagonal_pos_of_auxiliary
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, IsScalarTower k A (P i)]
    (i : ι) [Module.Finite k (P i)]
    (hP : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate
      A (P i)) :
    0 < matrix (k := k) (A := A) P i i :=
  haveI : Nontrivial (P i) := hP.1
  matrix_diagonal_pos P i

omit [Algebra k A] in
/-- Every entry of the auxiliary matrix is nonnegative. -/
theorem matrix_nonneg
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    (i j : ι) : 0 ≤ matrix (k := k) (A := A) P i j :=
  Nat.zero_le _

/-- The diagonal entry remains positive after the auxiliary matrix is mapped by natural-number casting. -/
theorem matrix_natCast_diagonal_pos
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, IsScalarTower k A (P i)]
    (i : ι) [Module.Finite k (P i)] [Nontrivial (P i)] :
    (0 : ℤ) < ((matrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)) i i := by
  rw [Matrix.map_apply]
  exact_mod_cast matrix_diagonal_pos P i

omit [Algebra k A] in
/-- Every entry remains nonnegative after the auxiliary matrix is mapped by natural-number casting. -/
theorem matrix_natCast_nonneg
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, SMulCommClass A k (P i)]
    (i j : ι) :
    (0 : ℤ) ≤ ((matrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)) i j := by
  rw [Matrix.map_apply]; exact Int.natCast_nonneg _

end RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix
