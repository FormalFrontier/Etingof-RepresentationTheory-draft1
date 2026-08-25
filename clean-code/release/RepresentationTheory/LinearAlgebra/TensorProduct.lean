/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Determinant
import RepresentationTheory.Alignment.Attribute

/-! # Linear algebra constructions for tensor products -/

namespace RepresentationTheory.LinearAlgebra.TensorProduct

variable {k : Type*} [Field k]
variable {V W U : Type*}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

/-- Provides a linear map out of a tensor product with the stated values on pure tensors. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
theorem exists_tensorProductLift :
    ∃ e : (V →ₗ[k] W →ₗ[k] U) ≃ (TensorProduct k V W →ₗ[k] U),
      ∀ (f : V →ₗ[k] W →ₗ[k] U) (v : V) (w : W),
        e f (TensorProduct.tmul k v w) = f v w := by
  refine ⟨(TensorProduct.lift.equiv (RingHom.id k) V W U).toEquiv, ?_⟩
  intro f v w
  simp only [LinearEquiv.coe_toEquiv, TensorProduct.lift.equiv_apply]

/-- Produces a basis whose vectors at pairs of indices are pure tensors of the given basis vectors. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
theorem exists_tensorProductBasis {ι κ : Type*} (b : Module.Basis ι k V)
    (c : Module.Basis κ k W) :
    ∃ B : Module.Basis (ι × κ) k (TensorProduct k V W),
      ∀ (i : ι) (j : κ), B (i, j) = TensorProduct.tmul k (b i) (c j) := by
  refine ⟨b.tensorProduct c, ?_⟩
  intro i j
  simp [Module.Basis.tensorProduct_apply]

/-- Provides the linear action on a tensor of a dual vector and a vector, evaluated by scalar multiplication. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
theorem exists_dualTensorAction [FiniteDimensional k V] :
    ∃ e : TensorProduct k (Module.Dual k V) W ≃ₗ[k] (V →ₗ[k] W),
      ∀ (f : Module.Dual k V) (w : W) (v : V),
        e (TensorProduct.tmul k f w) v = f v • w := by
  refine ⟨dualTensorHomEquiv k V W, ?_⟩
  intro f w v
  simp [dualTensorHomEquiv, dualTensorHom_apply]

/-- The determinant of a composite of endomorphisms is the product of their determinants. -/
theorem det_comp (A B : V →ₗ[k] V) :
    LinearMap.det (A ∘ₗ B) = LinearMap.det A * LinearMap.det B :=
  LinearMap.det_comp A B

end RepresentationTheory.LinearAlgebra.TensorProduct
