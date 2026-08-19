/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.Trace.CommutatorQuotient
import RepresentationTheory.Alignment.Attribute

/-!
# Matrix trace kernels

Results identifying matrix submodules with kernels of trace maps.
-/

namespace RepresentationTheory.LinearAlgebra.MatrixTraceKernels

open Matrix

/-- For square matrices indexed by a finite type, the auxiliary submodule is the kernel of the
trace linear map. -/
@[source_ref "Chapter3/Theorem3.6.2" (role := primary),
  source_ref "Chapter3/Theorem3.6.2/Derived9" (role := supporting)]
theorem auxiliaryMatrixSubmodule_eq_traceKernel
    (k : Type*) [CommRing k] (n : Type*) [Fintype n] [DecidableEq n] :
    RepresentationTheory.Algebra.Trace.CommutatorQuotient.commutatorSubmodule k (Matrix n n k) =
      LinearMap.ker (Matrix.traceLinearMap n k k) := by
  apply le_antisymm
  ·
    rw [RepresentationTheory.Algebra.Trace.CommutatorQuotient.commutatorSubmodule, Submodule.span_le]
    rintro z ⟨x, y, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Matrix.traceLinearMap_apply]
    rw [Matrix.trace_mul_comm, sub_self]
  ·
    intro M hM
    rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hM
    rcases isEmpty_or_nonempty n with hn | hn
    ·
      have hM0 : M = 0 := Subsingleton.elim _ _
      rw [hM0]; exact Submodule.zero_mem _
    · obtain ⟨i₀⟩ := hn
      have hoff : ∀ i j : n, i ≠ j →
          Matrix.single i j (1 : k) ∈
            RepresentationTheory.Algebra.Trace.CommutatorQuotient.commutatorSubmodule k
              (Matrix n n k) := by
        intro i j hij
        rw [RepresentationTheory.Algebra.Trace.CommutatorQuotient.commutatorSubmodule]
        apply Submodule.subset_span
        refine ⟨Matrix.single i i 1, Matrix.single i j 1, ?_⟩
        have p1 : Matrix.single i i (1 : k) * Matrix.single i j 1 = Matrix.single i j 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        have p2 : Matrix.single i j (1 : k) * Matrix.single i i 1 = 0 := by
          apply Matrix.single_mul_single_of_ne; exact hij.symm
        rw [p1, p2, sub_zero]
      have hdiag : ∀ i : n,
          Matrix.single i i (1 : k) - Matrix.single i₀ i₀ (1 : k) ∈
            RepresentationTheory.Algebra.Trace.CommutatorQuotient.commutatorSubmodule k
              (Matrix n n k) := by
        intro i
        rw [RepresentationTheory.Algebra.Trace.CommutatorQuotient.commutatorSubmodule]
        apply Submodule.subset_span
        refine ⟨Matrix.single i i₀ 1, Matrix.single i₀ i 1, ?_⟩
        have q1 : Matrix.single i i₀ (1 : k) * Matrix.single i₀ i 1 = Matrix.single i i 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        have q2 : Matrix.single i₀ i (1 : k) * Matrix.single i i₀ 1 = Matrix.single i₀ i₀ 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        rw [q1, q2]
      have hcorr :
          (∑ i : n, ∑ j : n,
            (if i = j then (M i i) • Matrix.single i₀ i₀ (1 : k) else 0)) = 0 := by
        have hinner : ∀ i : n,
            (∑ j : n, (if i = j then (M i i) • Matrix.single i₀ i₀ (1 : k) else 0))
              = (M i i) • Matrix.single i₀ i₀ 1 := by
          intro i; rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
        rw [Finset.sum_congr rfl (fun i _ => hinner i), ← Finset.sum_smul]
        have htr : (∑ i, M i i) = M.trace := rfl
        rw [htr, hM, zero_smul]
      have key : M = ∑ i : n, ∑ j : n,
          (Matrix.single i j (M i j) -
            (if i = j then (M i i) • Matrix.single i₀ i₀ (1 : k) else 0)) := by
        simp_rw [Finset.sum_sub_distrib]
        rw [← Matrix.matrix_eq_sum_single, hcorr, sub_zero]
      rw [key]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      by_cases hp : i = j
      ·
        subst hp
        rw [if_pos rfl]
        have e1 : Matrix.single i i (M i i) = (M i i) • Matrix.single i i (1 : k) := by
          rw [smul_single, smul_eq_mul, mul_one]
        rw [e1, ← smul_sub]
        exact Submodule.smul_mem _ _ (hdiag i)
      ·
        rw [if_neg hp, sub_zero]
        have e2 : Matrix.single i j (M i j) = (M i j) • Matrix.single i j (1 : k) := by
          rw [smul_single, smul_eq_mul, mul_one]
        rw [e2]
        exact Submodule.smul_mem _ _ (hoff i j hp)

/-- For square matrices indexed by `Fin d`, the auxiliary submodule is the kernel of the trace
linear map. -/
@[source_ref "Chapter3/Theorem3.6.2" (role := primary),
  source_ref "Chapter3/Theorem3.6.2/Derived11" (role := supporting)]
theorem auxiliaryFinMatrixSubmodule_eq_traceKernel
    (k : Type*) [CommRing k] (d : ℕ) :
    RepresentationTheory.Algebra.Trace.CommutatorQuotient.commutatorSubmodule k
        (Matrix (Fin d) (Fin d) k) =
      LinearMap.ker (Matrix.traceLinearMap (Fin d) k k) :=
  auxiliaryMatrixSubmodule_eq_traceKernel k (Fin d)

end RepresentationTheory.LinearAlgebra.MatrixTraceKernels
