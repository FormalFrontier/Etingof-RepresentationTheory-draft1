/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Contraction on exterior powers
-/

universe u v

open scoped BigOperators

namespace RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

section Formula

variable (R)

/-- A theorem declaration whose formal type was not rendered in the supplied data. -/
theorem unrenderedTheorem (u : Module.Dual R M) :
    ∀ (n : ℕ) (v : Fin (n + 1) → M),
      CliffordAlgebra.contractLeft u (ExteriorAlgebra.ιMulti R (n + 1) v) =
        ∑ j : Fin (n + 1),
          ((-1 : R) ^ (j : ℕ) * u (v j)) • ExteriorAlgebra.ιMulti R n (v ∘ j.succAbove) := by
  intro n
  induction n with
  | zero =>
    intro v
    rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul]
    simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ n ih =>
    intro v
    rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul]
    have htail : Matrix.vecTail v = v ∘ Fin.succ := rfl
    rw [htail, ih (v ∘ Fin.succ)]
    rw [Finset.mul_sum]
    rw [Fin.sum_univ_succ (f := fun j : Fin (n + 2) =>
      ((-1 : R) ^ (j : ℕ) * u (v j)) • ExteriorAlgebra.ιMulti R (n + 1) (v ∘ j.succAbove))]
    have h0 : (v ∘ (0 : Fin (n + 2)).succAbove) = v ∘ Fin.succ := by
      funext i; simp [Fin.succAbove_zero]
    rw [h0]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsucc : (v ∘ (Fin.succ j).succAbove) =
        Fin.cons (v 0) ((v ∘ Fin.succ) ∘ j.succAbove) := by
      funext i
      induction i using Fin.cases with
      | zero => simp
      | succ i => simp [Fin.succ_succAbove_succ]
    have htl : Matrix.vecTail (Fin.cons (v 0) ((v ∘ Fin.succ) ∘ j.succAbove)) =
        (v ∘ Fin.succ) ∘ j.succAbove := by
      funext i; simp [Matrix.vecTail]
    rw [hsucc, ExteriorAlgebra.ιMulti_succ_apply, htl]
    simp only [Fin.cons_zero, Function.comp_apply]
    rw [mul_smul_comm]
    module

end Formula

section Graded

variable (R)

/-- Left contraction maps elements of exterior degree `n + 1` into exterior degree `n`. -/
theorem contractLeft_maps_exteriorPower_succ (u : Module.Dual R M) (n : ℕ)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n + 1) M) :
    CliffordAlgebra.contractLeft u x ∈ ⋀[R]^n M := by
  rw [← exteriorPower.ιMulti_span_fixedDegree R (n + 1) M] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [unrenderedTheorem R u n v]
      refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
      exact ExteriorAlgebra.ιMulti_range R n (Set.mem_range_self _)
  | zero => simp
  | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
  | smul r y _ hy => simpa using Submodule.smul_mem _ r hy

/-- The linear map induced by left contraction from exterior degree `n + 1` to degree `n`. -/
noncomputable def exteriorPowerContraction (u : Module.Dual R M) (n : ℕ) :
    ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  -(LinearMap.restrict (CliffordAlgebra.contractLeft u)
    (fun _ hx => contractLeft_maps_exteriorPower_succ R u n hx))

variable {R}

/-- Evaluating exterior-power contraction gives the negative of left contraction on the underlying element. -/
@[simp]
theorem exteriorPowerContraction_apply (u : Module.Dual R M) (n : ℕ)
    (x : ⋀[R]^(n + 1) M) :
    (exteriorPowerContraction R u n x : ExteriorAlgebra R M) =
      -CliffordAlgebra.contractLeft u (x : ExteriorAlgebra R M) :=
  rfl

/-- The supplied data does not provide a rendered formal type for this theorem declaration. -/
theorem exteriorPowerContraction_unrenderedAux (u : Module.Dual R M) (n : ℕ)
    (v : Fin (n + 1) → M) :
    exteriorPowerContraction R u n (exteriorPower.ιMulti R (n + 1) v) =
      ∑ j : Fin (n + 1),
        ((-1 : R) ^ ((j : ℕ) + 1) * u (v j)) • exteriorPower.ιMulti R n
          (v ∘ j.succAbove) := by
  apply Subtype.ext
  push_cast
  rw [exteriorPowerContraction_apply]
  simp only [exteriorPower.ιMulti_apply_coe]
  rw [unrenderedTheorem R u n v, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pow_succ]
  module

/-- Applying consecutive exterior-power contractions using the same dual vector gives zero. -/
@[simp]
theorem exteriorPowerContraction_apply_succ (u : Module.Dual R M) (n : ℕ)
    (x : ⋀[R]^(n + 2) M) :
    exteriorPowerContraction R u n (exteriorPowerContraction R u (n + 1) x) = 0 := by
  apply Subtype.ext
  simp [CliffordAlgebra.contractLeft_contractLeft]

/-- The composite of consecutive exterior-power contractions using the same dual vector is zero. -/
theorem exteriorPowerContraction_comp_succ (u : Module.Dual R M) (n : ℕ) :
    (exteriorPowerContraction R u n).comp (exteriorPowerContraction R u (n + 1)) = 0 :=
  LinearMap.ext fun x => exteriorPowerContraction_apply_succ u n x

/-- Exterior-power contractions by two dual vectors anticommute on elements two degrees higher. -/
theorem exteriorPowerContraction_anticommute (u u' : Module.Dual R M) (n : ℕ)
    (x : ⋀[R]^(n + 2) M) :
    exteriorPowerContraction R u n (exteriorPowerContraction R u' (n + 1) x) =
      -exteriorPowerContraction R u' n (exteriorPowerContraction R u (n + 1) x) := by
  apply Subtype.ext
  simp [CliffordAlgebra.contractLeft_comm (d := u) (d' := u')]

end Graded

end RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction
