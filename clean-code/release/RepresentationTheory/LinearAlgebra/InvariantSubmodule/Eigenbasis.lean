/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib

/-!
# Coordinate submodules of a diagonal operator, and an irreducibility criterion

This file isolates two reusable, representation-free ingredients:

* If a linear operator acts diagonally on a basis with pairwise distinct eigenvalues, then every
  invariant submodule is a coordinate submodule.
* If basis indices are connected by a relation that propagates membership in an invariant
  submodule, then that submodule is either bottom or top.
-/

open scoped BigOperators
open Module

namespace RepresentationTheory.LinearAlgebra.InvariantSubmodule.Eigenbasis

variable {k : Type*} [Field k]
  {M : Type*} [AddCommGroup M] [Module k M]
  {B : Type*} (b : Basis B k M)

section CoordinateSubmodule

variable {T : Module.End k M} {w : B → k}

open Polynomial

/-- A polynomial in a `W`-invariant operator preserves `W`. -/
private lemma aeval_mem {W : Submodule k M} (hW : ∀ x ∈ W, T x ∈ W) (q : k[X]) :
    ∀ z ∈ W, aeval T q z ∈ W := by
  induction q using Polynomial.induction_on with
  | C a => intro z hz; rw [aeval_C, Module.algebraMap_end_apply]; exact W.smul_mem a hz
  | add p q hp hq =>
    intro z hz; rw [map_add, LinearMap.add_apply]; exact W.add_mem (hp z hz) (hq z hz)
  | monomial n a ih =>
    intro z hz
    rw [show C a * X ^ (n + 1) = (C a * X ^ n) * X by ring, map_mul, Module.End.mul_apply, aeval_X]
    exact ih (T z) (hW z hz)

/-- A basis vector belongs to an invariant submodule whenever it has a nonzero coefficient in a
member of that submodule and the basis has distinct eigenvalues. -/
theorem basis_mem_of_mem_invariant_and_repr_ne_zero
    (hT : ∀ s, T (b s) = w s • b s) (hw : Function.Injective w)
    {W : Submodule k M} (hW : ∀ x ∈ W, T x ∈ W)
    {y : M} (hy : y ∈ W) {t : B} (ht : b.repr y t ≠ 0) : b t ∈ W := by
  classical
  set σ := (b.repr y).support with hσ
  have htσ : t ∈ σ := Finsupp.mem_support_iff.mpr ht
  -- The interpolating polynomial killing every eigenvalue except `w t`.
  set p : k[X] := ∏ s ∈ σ.erase t, (X - C (w s)) with hp
  -- Scalar that survives at `t`.
  set c := ∏ s ∈ σ.erase t, (w t - w s) with hc
  have hcne : c ≠ 0 := by
    rw [hc, Finset.prod_ne_zero_iff]
    intro s hs
    exact sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hs) (hw h).symm)
  -- `aeval T p` acts on each basis vector `b u` as the scalar `p.eval (w u)`.
  have heval : ∀ u, aeval T p (b u) = (∏ s ∈ σ.erase t, (w u - w s)) • b u := by
    intro u
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hT u)]
    congr 1
    rw [hp, eval_prod]
    exact Finset.prod_congr rfl (fun s _ => by rw [eval_sub, eval_X, eval_C])
  -- Expand `y` along the basis and push `aeval T p` through.
  have hyexp : y = (b.repr y).sum (fun i a => a • b i) := by
    conv_lhs => rw [← b.linearCombination_repr y]
    rw [Finsupp.linearCombination_apply]
  have hPy : aeval T p y = (b.repr y t * c) • b t := by
    conv_lhs => rw [hyexp]
    rw [map_finsuppSum, Finsupp.sum, Finset.sum_eq_single t]
    · rw [map_smul, heval t, smul_smul]
    · intro u hu hut
      rw [map_smul, heval u]
      have : (∏ s ∈ σ.erase t, (w u - w s)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hut, hu⟩) (by simp)
      rw [this, zero_smul, smul_zero]
    · intro h; exact absurd htσ h
  -- `aeval T p y ∈ W`, and the surviving scalar is nonzero, so `b t ∈ W`.
  have hPyW : aeval T p y ∈ W := aeval_mem hW p y hy
  rw [hPy] at hPyW
  have hscale : b.repr y t * c ≠ 0 := mul_ne_zero ht hcne
  have := W.smul_mem (b.repr y t * c)⁻¹ hPyW
  rwa [smul_smul, inv_mul_cancel₀ hscale, one_smul] at this

end CoordinateSubmodule

section Irreducible

variable {T : Module.End k M} {w : B → k}

/-- An invariant submodule is either bottom or top when a basis has distinct eigenvalues and basis
membership propagates along a connected relation. -/
theorem eq_bot_or_top_of_invariant_of_eigenbasis_connected
    (hT : ∀ s, T (b s) = w s • b s) (hw : Function.Injective w)
    {W : Submodule k M} (hW : ∀ x ∈ W, T x ∈ W)
    (Adj : B → B → Prop)
    (hconn : ∀ s t, Relation.ReflTransGen Adj s t)
    (hstep : ∀ s t, b s ∈ W → Adj s t → b t ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  rcases eq_or_ne W ⊥ with hbot | hbot
  · exact Or.inl hbot
  -- `W ≠ ⊥`, so some basis vector lies in `W`.
  right
  obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff W).mp hbot
  obtain ⟨s, hs⟩ : ∃ s, b.repr y s ≠ 0 := by
    have hry : b.repr y ≠ 0 := fun h => hy0 (by simpa using congrArg b.repr.symm h)
    simpa using Finsupp.ne_iff.mp hry
  have hsW : b s ∈ W := basis_mem_of_mem_invariant_and_repr_ne_zero b hT hw hW hyW hs
  -- Propagate membership along the connected `Adj`-graph to every basis vector.
  have hall : ∀ t, b t ∈ W := by
    intro t
    have : Relation.ReflTransGen Adj s t := hconn s t
    induction this with
    | refl => exact hsW
    | tail _ hadj ih => exact hstep _ _ ih hadj
  rw [eq_top_iff, ← b.span_eq]
  exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hall)

end Irreducible

end RepresentationTheory.LinearAlgebra.InvariantSubmodule.Eigenbasis
