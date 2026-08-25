/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import RepresentationTheory.Alignment.Attribute

/-!
# Evaluation of endomorphisms on a basis

Evaluation on a finite basis identifies a module endomorphism with the family of its values on
the basis vectors. For a finite-dimensional simple module, this identification also transfers
semisimplicity to its endomorphism space.
-/

set_option autoImplicit false

namespace RepresentationTheory.Module.EndomorphismEvaluation

section

variable {k : Type*} {A : Type*} {V : Type*} {ι : Type*}
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- Evaluation on a basis defines a linear map from module endomorphisms to basis-indexed
families of vectors. -/
noncomputable def endApplyBasisLinearMap (b : Module.Basis ι k V) :
    Module.End k V →ₗ[A] (ι → V) where
  toFun f i := f (b i)
  map_add' f g := by ext i; simp
  map_smul' (a : A) f := by ext i; simp [LinearMap.smul_apply]

/-- The basis-evaluation linear map sends an endomorphism to its value on each basis vector. -/
@[simp] theorem endApplyBasisLinearMap_apply (b : Module.Basis ι k V)
    (f : Module.End k V) (i : ι) :
    endApplyBasisLinearMap (A := A) b f i = f (b i) := rfl

/- Finiteness is a proof hypothesis for surjectivity, although it does not occur in the
proposition returned by `Function.Bijective`. -/
set_option linter.unusedFintypeInType false in
/-- For a finite index type, evaluation on a basis is a bijection from module endomorphisms to
basis-indexed families of vectors. -/
theorem endApplyBasisLinearMap_bijective [Fintype ι] (b : Module.Basis ι k V) :
    Function.Bijective (endApplyBasisLinearMap (A := A) b) := by
  constructor
  · intro f g h
    ext v
    have hfg : ∀ i, f (b i) = g (b i) := congr_fun h
    rw [← b.sum_repr v, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, hfg i]
  · intro g
    refine ⟨b.constr k g, ?_⟩
    ext i
    rw [endApplyBasisLinearMap_apply]
    exact b.constr_basis k g i

/-- Evaluation on a finite basis gives a linear equivalence from module endomorphisms to
basis-indexed families of vectors. -/
@[source_ref "Chapter3/Example3.1.2" (role := supporting)]
noncomputable def endApplyBasisLinearEquiv [Fintype ι] (b : Module.Basis ι k V) :
    Module.End k V ≃ₗ[A] (ι → V) :=
  LinearEquiv.ofBijective (endApplyBasisLinearMap b) (endApplyBasisLinearMap_bijective b)

/-- The basis-evaluation linear equivalence sends an endomorphism to its values on the basis
vectors. -/
@[source_ref "Chapter3/Example3.1.2" (role := supporting), simp]
theorem endApplyBasisLinearEquiv_apply [Fintype ι] (b : Module.Basis ι k V)
    (f : Module.End k V) (i : ι) :
    endApplyBasisLinearEquiv (A := A) b f i = f (b i) := rfl

/-- Evaluation on the canonical finite basis gives a linear equivalence from module endomorphisms
to finite families of vectors. -/
@[source_ref "Chapter3/Example3.1.2" (role := supporting)]
noncomputable def endApplyFinBasisLinearEquiv [FiniteDimensional k V] :
    Module.End k V ≃ₗ[A] (Fin (Module.finrank k V) → V) :=
  endApplyBasisLinearEquiv (Module.finBasis k V)

/-- The canonical finite-basis equivalence sends an endomorphism to its values on the canonical
basis vectors. -/
@[source_ref "Chapter3/Example3.1.2" (role := supporting), simp]
theorem endApplyFinBasisLinearEquiv_apply [FiniteDimensional k V] (f : Module.End k V)
    (i : Fin (Module.finrank k V)) :
    endApplyFinBasisLinearEquiv (A := A) f i = f (Module.finBasis k V i) := rfl

end

/-- The endomorphism space of a finite-dimensional simple module is semisimple as a module over
the acting algebra. -/
@[source_ref "Chapter3/Example3.1.2" (role := supporting)]
theorem endomorphismModule_isSemisimple (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSimpleModule A V] :
    IsSemisimpleModule A (Module.End k V) :=
  IsSemisimpleModule.congr (endApplyFinBasisLinearEquiv (k := k) (A := A) (V := V))

end RepresentationTheory.Module.EndomorphismEvaluation
