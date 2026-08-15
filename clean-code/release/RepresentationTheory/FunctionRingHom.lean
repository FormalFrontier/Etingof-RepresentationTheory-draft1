/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.Quiver.PathAlgebra
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Function rings in path algebras

This module defines the ring homomorphism that embeds vertex-indexed functions into a path
algebra by weighting its length-zero paths.
-/

set_option backward.isDefEq.respectTransparency false

universe u

namespace RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra

/-- The ring of functions from a finite type to a field is semisimple. -/
theorem functionRing_isSemisimpleRing (k Q : Type*) [Field k] [Finite Q] :
    IsSemisimpleRing (Q → k) :=
  inferInstance

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]

/-- The product of the displayed elements indexed by nil paths is the first element when the quiver indices agree and zero otherwise. -/
theorem auxiliary_nilPath_mul (i j : Q) :
    (ofPath ⟨i, i, Quiver.Path.nil⟩ : Quiver.PathAlgebra k Q) * ofPath ⟨j, j, Quiver.Path.nil⟩
      = if i = j then ofPath ⟨i, i, Quiver.Path.nil⟩ else 0 := by
  rw [ofPath, ofPath, single_mul_single, one_mul, one_smul, mulPath_vertexPath]
  split_ifs with h
  · subst h; rfl
  · rfl

variable (k Q) in
/-- A ring homomorphism from vertex-indexed field-valued functions to the displayed algebra. -/
noncomputable def functionRingHom [Fintype Q] : (Q → k) →+* Quiver.PathAlgebra k Q where
  toFun a := ∑ i, Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) (a i)
  map_one' := by
    simp only [Pi.one_apply]
    exact one_eq_sum_single_vertexPath.symm
  map_mul' a b := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [single_mul_single, mulPath_vertexPath, if_pos rfl, Finsupp.smul_single,
        smul_eq_mul, mul_one]
      rfl
    · intro j _ hji
      rw [single_mul_single, mulPath_vertexPath, if_neg (Ne.symm hji), smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  map_zero' := by simp
  map_add' a b := by
    simp only [Pi.add_apply, Finsupp.single_add]
    rw [Finset.sum_add_distrib]

/-- The function-ring homomorphism sends a function to the sum of singleton terms on the trivial paths, weighted by its vertex values. -/
@[simp]
theorem functionRingHom_apply [Fintype Q] (a : Q → k) :
    functionRingHom k Q a
      = ∑ i, Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) (a i) :=
  rfl

end RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra
