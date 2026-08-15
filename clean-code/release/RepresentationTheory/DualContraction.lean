/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib

open scoped TensorProduct

namespace RepresentationTheory.DualContraction

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Contracting a pure tensor after applying the dual and original representation actions gives the original contraction. -/
theorem contractLeft_dual_action_tmul_action (ρ : Representation k G V) (g : G)
    (f : Module.Dual k V) (v : V) :
    contractLeft k V ((ρ.dual g) f ⊗ₜ[k] (ρ g v))
      = contractLeft k V (f ⊗ₜ[k] v) := by
  rw [contractLeft_apply, contractLeft_apply,
    Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- Left contraction on a nontrivial finite-dimensional vector space is nonzero. -/
theorem contractLeft_ne_zero [Nontrivial V] [FiniteDimensional k V] :
    contractLeft k V ≠ 0 := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine hv ((Module.forall_dual_apply_eq_zero_iff k v).mp (fun f => ?_))
  have := congrArg (fun (m : Module.Dual k V ⊗[k] V →ₗ[k] k) => m (f ⊗ₜ[k] v)) h
  simpa [contractLeft_apply] using this

end RepresentationTheory.DualContraction
