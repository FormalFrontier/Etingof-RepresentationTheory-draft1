/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Module.Dual.SimpleFamilies
import RepresentationTheory.Alignment.Attribute

/-!
# Trace computations on function spaces
-/

open Module

namespace RepresentationTheory.LinearAlgebra.Trace.FunctionSpace

section Diagonal

variable (k : Type*) (V : Type*)
  [CommRing k] [AddCommGroup V] [Module k V]

/-- A linear endomorphism induces a linear endomorphism of a function space by acting pointwise. -/
def linearMapOnFunctions {ι : Type*} (f : V →ₗ[k] V) : (ι → V) →ₗ[k] (ι → V) :=
  LinearMap.pi fun i => f ∘ₗ LinearMap.proj i

/-- The pointwise endomorphism of a function space applies the original linear map at each input. -/
@[simp]
lemma linearMapOnFunctions_apply {ι : Type*} (f : V →ₗ[k] V) (g : ι → V) (i : ι) :
    linearMapOnFunctions k V f g i = f (g i) := rfl

variable [Module.Free k V] [Module.Finite k V]

/-- The trace of the pointwise endomorphism on a finite family of copies is the family cardinality times the trace of the original endomorphism. -/
lemma trace_linearMapOnFunctions (n : ℕ) (f : V →ₗ[k] V) :
    LinearMap.trace k (Fin n → V) (linearMapOnFunctions k V f) =
      n • LinearMap.trace k V f := by
  induction n with
  | zero =>
    rw [zero_smul, Subsingleton.elim (linearMapOnFunctions k V f) 0, map_zero]
  | succ n ih =>
    set e := (Fin.consLinearEquiv k (fun _ : Fin (n + 1) => V)).symm with he
    have key : e.conj (linearMapOnFunctions k V f) =
        LinearMap.prodMap f (linearMapOnFunctions k V f) := by
      apply LinearMap.ext
      rintro ⟨v, w⟩
      rw [LinearEquiv.conj_apply, LinearMap.prodMap_apply]
      apply Prod.ext
      · simp [he, linearMapOnFunctions]
      · funext i
        simp [he, linearMapOnFunctions, Fin.tail]
    calc LinearMap.trace k (Fin (n + 1) → V) (linearMapOnFunctions k V f)
        = LinearMap.trace k (V × (Fin n → V))
            (e.conj (linearMapOnFunctions k V f)) :=
          (LinearMap.trace_conj' _ _).symm
      _ = LinearMap.trace k (V × (Fin n → V))
            (LinearMap.prodMap f (linearMapOnFunctions k V f)) := by rw [key]
      _ = LinearMap.trace k V f +
            LinearMap.trace k (Fin n → V) (linearMapOnFunctions k V f) :=
          LinearMap.trace_prodMap' f (linearMapOnFunctions k V f)
      _ = LinearMap.trace k V f + n • LinearMap.trace k V f := by rw [ih]
      _ = (n + 1) • LinearMap.trace k V f := by rw [succ_nsmul, add_comm]

end Diagonal

section Characteristic

variable (k : Type*) (A : Type*) (V : Type*)
  [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [Module.Free k V] [Module.Finite k V]

/-- The trace-valued function of an action on a finite family of copies of a module is the family cardinality times its value on the module. -/
@[source_ref "Chapter3/Theorem3.7.1/Derived6" (role := supporting),
  source_ref "Chapter3/Theorem3.7.1/Derived9" (role := supporting)]
theorem representationTrace_finFun (n : ℕ) (a : A) :
    RepresentationTheory.Algebra.Module.Dual.SimpleFamilies.moduleDualElement k A (Fin n → V) a =
      n • RepresentationTheory.Algebra.Module.Dual.SimpleFamilies.moduleDualElement k A V a := by
  have h1 : (Algebra.lsmul k k (Fin n → V) : A →ₐ[k] Module.End k (Fin n → V)) a
      = linearMapOnFunctions k V ((Algebra.lsmul k k V : A →ₐ[k] Module.End k V) a) := by
    apply LinearMap.ext
    intro g
    funext i
    rfl
  simp only [RepresentationTheory.Algebra.Module.Dual.SimpleFamilies.moduleDualElement,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, h1]
  exact trace_linearMapOnFunctions k V n _

/-- In characteristic p, the trace-valued function of an action on p copies of a module is zero. -/
@[source_ref "Chapter3/Theorem3.7.1/Derived9" (role := supporting),
  source_ref "Chapter3/Theorem3.7.1" (role := primary)]
theorem representationTrace_finFun_eq_zero_of_char (p : ℕ) [CharP k p] :
    RepresentationTheory.Algebra.Module.Dual.SimpleFamilies.moduleDualElement k A (Fin p → V) = 0 := by
  ext a
  rw [representationTrace_finFun k A V p a, LinearMap.zero_apply, nsmul_eq_mul,
    CharP.cast_eq_zero, zero_mul]

end Characteristic

end RepresentationTheory.LinearAlgebra.Trace.FunctionSpace
