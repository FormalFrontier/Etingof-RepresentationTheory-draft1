/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import RepresentationTheory.Alignment.Attribute

/-! # Basis expansions from free modules -/

open Module

namespace RepresentationTheory.Algebra.Module.BasisExpansion

variable {k : Type*} (A : Type*) {X : Type*}
  [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  {ι : Type*} [Fintype ι]

/-- The linear map that expands a finite family of algebra coefficients against a module basis. -/
@[source_ref "Chapter3/Remark3.3.4" (role := supporting)]
noncomputable def basisExpansion (b : Basis ι k X) : (ι → A) →ₗ[A] X where
  toFun a := ∑ i, (a i • b i : X)
  map_add' a a' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

omit [Algebra k A] [IsScalarTower k A X] in
/-- The basis expansion is the sum of the coefficients acting on their basis elements. -/
@[simp, source_ref "Chapter3/Remark3.3.4" (role := supporting)]
theorem basisExpansion_apply (b : Basis ι k X) (a : ι → A) :
    basisExpansion A b a = ∑ i, (a i • b i : X) := rfl

omit [Algebra k A] [IsScalarTower k A X] in
/-- A linear map with the displayed coefficient-expansion formula equals the basis expansion. -/
@[source_ref "Chapter3/Remark3.3.4" (role := primary)]
theorem eq_basisExpansion_of_apply (b : Basis ι k X) (f : (ι → A) →ₗ[A] X)
    (hf : ∀ a, f a = ∑ i, (a i • b i : X)) :
    f = basisExpansion A b := by
  ext a
  rw [hf, basisExpansion_apply]

/-- A basis expansion is surjective under the displayed scalar-tower hypotheses. -/
@[source_ref "Chapter3/Remark3.3.4" (role := primary)]
theorem basisExpansion_surjective (b : Basis ι k X) :
    Function.Surjective (basisExpansion A b) := by
  intro x
  refine ⟨fun i => algebraMap k A (b.repr x i), ?_⟩
  rw [basisExpansion_apply]
  rw [show (∑ i, (algebraMap k A (b.repr x i) • b i : X)) = ∑ i, ((b.repr x i) • b i : X) from
    Finset.sum_congr rfl fun i _ => algebraMap_smul A (b.repr x i) (b i)]
  exact b.sum_repr x

/-- The quotient by the kernel of a basis expansion is linearly equivalent to the target module. -/
@[source_ref "Chapter3/Remark3.3.4" (role := primary)]
noncomputable def quotientKerBasisExpansionEquiv (b : Basis ι k X) :
    ((ι → A) ⧸ LinearMap.ker (basisExpansion A b)) ≃ₗ[A] X :=
  (basisExpansion A b).quotKerEquivOfSurjective (basisExpansion_surjective A b)

end RepresentationTheory.Algebra.Module.BasisExpansion
