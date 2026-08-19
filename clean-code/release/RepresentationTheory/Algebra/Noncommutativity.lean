/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin
import RepresentationTheory.Alignment.Attribute

/-! # Noncommutativity criteria -/

namespace RepresentationTheory.Algebra.Noncommutativity

open Matrix

/-- All elements of a monoid algebra commute exactly when all elements of its indexing monoid
commute. -/
@[source_ref "Chapter2/Discussion_commutativity_examples" (role := primary)]
theorem monoidAlgebra_mul_comm_iff (k : Type*) [CommSemiring k] [Nontrivial k]
    (G : Type*) [Monoid G] :
    (∀ x y : MonoidAlgebra k G, x * y = y * x) ↔ (∀ g h : G, g * h = h * g) := by
  constructor
  · intro hcomm g h
    have key := hcomm (MonoidAlgebra.single g 1) (MonoidAlgebra.single h 1)
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single] at key
    simp only [mul_one] at key
    exact MonoidAlgebra.single_left_injective one_ne_zero key
  · intro hcomm
    letI : CommMonoid G := { (inferInstance : Monoid G) with mul_comm := hcomm }
    intro x y
    exact mul_comm x y

section Noncommutative

variable (k : Type*) [CommRing k] [Nontrivial k]

private lemma single_not_commute :
    (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) k) * Matrix.single 1 0 1
      ≠ Matrix.single 1 0 1 * Matrix.single 0 1 1 := by
  intro h
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have h00 := congrFun (congrFun h 0) 0
  rw [Matrix.single_apply, Matrix.single_apply, if_pos (by decide), if_neg (by decide),
    mul_one] at h00
  exact one_ne_zero h00

example : ∃ f g : Module.End k (Fin 2 → k), f * g ≠ g * f := by
  refine ⟨Matrix.toLinAlgEquiv' (Matrix.single 0 1 1),
    Matrix.toLinAlgEquiv' (Matrix.single 1 0 1), ?_⟩
  intro h
  rw [← map_mul, ← map_mul] at h
  exact single_not_commute k ((Matrix.toLinAlgEquiv' (R := k)).injective h)

/-- For a nontrivial commutative ring and a natural number greater than one, there are elements
with unequal products in opposite orders. -/
@[source_ref "Chapter2/Discussion_commutativity_examples" (role := supporting)]
theorem exists_noncommuting_pair_of_one_lt (n : ℕ) (hn : 1 < n) :
    ∃ a b : FreeAlgebra k (Fin n), a * b ≠ b * a := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let images : Fin n → Matrix (Fin 2) (Fin 2) k := fun i =>
    if i = i0 then Matrix.single 0 1 1
    else if i = i1 then Matrix.single 1 0 1
    else 0
  refine ⟨FreeAlgebra.ι k i0, FreeAlgebra.ι k i1, fun hcomm => ?_⟩
  apply single_not_commute k
  have := congrArg (FreeAlgebra.lift k images) hcomm
  simpa only [map_mul, FreeAlgebra.lift_ι_apply, images, if_pos, if_neg hne.symm, hne] using this

end Noncommutative

section GeneralEndomorphism

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- If a module over a field has rank at least two, there exist two elements whose products differ
when their order is reversed. -/
@[source_ref "Chapter2/Discussion_commutativity_examples" (role := primary)]
theorem exists_noncommuting_pair_of_two_le_rank
    (h : (2 : Cardinal) ≤ Module.rank k V) :
    ∃ f g : Module.End k V, f * g ≠ g * f := by
  let b := Module.Free.chooseBasis k V
  have hcard : (2 : Cardinal) ≤ Cardinal.mk (Module.Free.ChooseBasisIndex k V) := by
    rwa [← Module.Free.rank_eq_card_chooseBasisIndex]
  obtain ⟨i0, i1, hne⟩ := Cardinal.two_le_iff.mp hcard
  let f : Module.End k V := b.constr k (fun i => if i = i1 then b i0 else 0)
  let g : Module.End k V := b.constr k (fun i => if i = i0 then b i1 else 0)
  have hf0 : f (b i0) = 0 := by simp [f, hne]
  have hf1 : f (b i1) = b i0 := by simp [f]
  have hg0 : g (b i0) = b i1 := by simp [g]
  refine ⟨f, g, fun hcomm => ?_⟩
  have key := congrArg (fun φ : Module.End k V => φ (b i0)) hcomm
  simp only [Module.End.mul_apply, hg0, hf1, hf0, map_zero] at key
  exact b.ne_zero i0 key

end GeneralEndomorphism

end RepresentationTheory.Algebra.Noncommutativity
