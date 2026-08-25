/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.LinearMap.FiniteRange
import Mathlib.RingTheory.Noetherian.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Dual tensors of finitely supported sequences
-/

open TensorProduct LinearMap

namespace RepresentationTheory.FinsuppDualTensor

universe u

variable (k : Type u) [Field k]

/-- Send a tensor of linear functionals on finitely supported sequences to the associated linear map into the dual. -/
noncomputable def finsuppDualTensorToLinearMap :
    Module.Dual k (ℕ →₀ k) ⊗[k] Module.Dual k (ℕ →₀ k) →ₗ[k]
      ((ℕ →₀ k) →ₗ[k] Module.Dual k (ℕ →₀ k)) :=
  TensorProduct.lift LinearMap.smulRightₗ

variable {k}

/-- A pure tensor of linear functionals yields the corresponding scalar-valued rank-one linear map. -/
@[simp]
theorem finsuppDualTensorToLinearMap_tmul (f g : Module.Dual k (ℕ →₀ k)) :
    finsuppDualTensorToLinearMap k (f ⊗ₜ[k] g) = f.smulRight g :=
  TensorProduct.lift.tmul f g

/-- Evaluating the linear map associated to a dual tensor agrees with evaluating the distributed tensor on a pure tensor of vectors. -/
theorem finsuppDualTensorToLinearMap_apply
    (t : Module.Dual k (ℕ →₀ k) ⊗[k] Module.Dual k (ℕ →₀ k))
    (x y : ℕ →₀ k) :
    finsuppDualTensorToLinearMap k t x y =
      TensorProduct.dualDistrib k (ℕ →₀ k) (ℕ →₀ k) t (x ⊗ₜ[k] y) := by
  induction t with
  | zero => simp
  | tmul f g => simp [smul_eq_mul]
  | add a b ha hb => simp [ha, hb]

/-- Every linear map obtained from a tensor of duals of finitely supported sequences has Noetherian range. -/
theorem finsuppDualTensorToLinearMap_hasNoetherianRange
    (t : Module.Dual k (ℕ →₀ k) ⊗[k] Module.Dual k (ℕ →₀ k)) :
    (finsuppDualTensorToLinearMap k t).HasNoetherianRange := by
  induction t with
  | zero =>
      rw [map_zero]
      change IsNoetherian k ↥(LinearMap.range (0 : (ℕ →₀ k) →ₗ[k] Module.Dual k (ℕ →₀ k)))
      rw [LinearMap.range_zero]
      infer_instance
  | tmul f g =>
      have hle : LinearMap.range (finsuppDualTensorToLinearMap k (f ⊗ₜ[k] g)) ≤
          Submodule.span k {g} := by
        rw [finsuppDualTensorToLinearMap_tmul]
        rintro _ ⟨v, rfl⟩
        simpa [LinearMap.smulRight_apply] using
          Submodule.smul_mem _ (f v) (Submodule.mem_span_singleton_self g)
      haveI : IsNoetherian k ↥(Submodule.span k {g}) :=
        isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_singleton g))
      exact isNoetherian_of_le hle
  | add a b ha hb =>
      rw [map_add]
      exact ha.add hb

end RepresentationTheory.FinsuppDualTensor

open RepresentationTheory.FinsuppDualTensor in
/-- The canonical distribution map from a tensor product of duals of finitely supported sequences is not surjective. -/
@[source_ref "Chapter8/Problem8.2.8/Derived2" (role := supporting)]
theorem RepresentationTheory.FinsuppDualTensor.dualDistrib_finsuppNat_not_surjective
    (k : Type u) [Field k] :
    ¬ Function.Surjective
      (TensorProduct.dualDistrib k (ℕ →₀ k) (ℕ →₀ k)) := by
  intro hsurj
  set D : (ℕ →₀ k) →ₗ[k] Module.Dual k (ℕ →₀ k) :=
    Finsupp.linearCombination k (fun i => Finsupp.lapply i) with hD
  set Ψ : Module.Dual k ((ℕ →₀ k) ⊗[k] (ℕ →₀ k)) := TensorProduct.lift D with hΨ
  obtain ⟨t, ht⟩ := hsurj Ψ
  haveI : IsNoetherian k ↥(LinearMap.range (finsuppDualTensorToLinearMap k t)) :=
    finsuppDualTensorToLinearMap_hasNoetherianRange t
  have hmem : ∀ i, (Finsupp.lapply i : Module.Dual k (ℕ →₀ k)) ∈
      LinearMap.range (finsuppDualTensorToLinearMap k t) := by
    intro i
    refine ⟨Finsupp.single i 1, ?_⟩
    refine LinearMap.ext fun y => ?_
    rw [finsuppDualTensorToLinearMap_apply, ht, hΨ, TensorProduct.lift.tmul, hD,
      Finsupp.linearCombination_single, one_smul]
  have hli : LinearIndependent k (fun i : ℕ => (Finsupp.lapply i : Module.Dual k (ℕ →₀ k))) := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have h0 : (∑ j ∈ s, c j • Finsupp.lapply (R := k) (M := k) j) (Finsupp.single i 1) = 0 := by
      rw [hsum]; simp
    simpa [Finsupp.single_apply, Finset.sum_ite_eq, hi] using h0
  set W := LinearMap.range (finsuppDualTensorToLinearMap k t)
  set w : ℕ → W := fun i => ⟨Finsupp.lapply i, hmem i⟩ with hw
  have hwli : LinearIndependent k w := by
    apply LinearIndependent.of_comp W.subtype
    change LinearIndependent k (fun i : ℕ => (Finsupp.lapply i : Module.Dual k (ℕ →₀ k)))
    exact hli
  haveI : Finite ℕ := hwli.finite_of_isNoetherian
  exact not_finite ℕ
