/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps

open scoped TensorProduct

namespace RepresentationTheory.SymmetricAlgebra.ProductTensorProduct

universe u

variable (k U W : Type u) [CommRing k]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]

/-- The algebra homomorphism from the symmetric algebra on a product module to the tensor product
of the symmetric algebras of its factors. -/
noncomputable def SymmetricAlgebra.prodToTensorProduct :
    SymmetricAlgebra k (U × W) →ₐ[k]
      SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W :=
  SymmetricAlgebra.lift
    (((Algebra.TensorProduct.includeLeft.toLinearMap.comp
      (SymmetricAlgebra.ι k U)).comp (LinearMap.fst k U W)) +
    ((Algebra.TensorProduct.includeRight.toLinearMap.comp
      (SymmetricAlgebra.ι k W)).comp (LinearMap.snd k U W)))

/-- The algebra homomorphism from a tensor product of symmetric algebras to the symmetric algebra
on the product module. -/
noncomputable def SymmetricAlgebra.tensorProductToProd :
    SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W →ₐ[k]
      SymmetricAlgebra k (U × W) :=
  Algebra.TensorProduct.lift
    (SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι k (U × W)).comp (LinearMap.inl k U W)))
    (SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι k (U × W)).comp (LinearMap.inr k U W)))
    (fun _ _ => Commute.all _ _)

/-- The algebra equivalence between the symmetric algebra on a product module and the tensor
product of the two symmetric algebras. -/
noncomputable def SymmetricAlgebra.prodAlgEquivTensorProduct :
    SymmetricAlgebra k (U × W) ≃ₐ[k]
      SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W :=
  AlgEquiv.ofAlgHom (SymmetricAlgebra.prodToTensorProduct k U W)
    (SymmetricAlgebra.tensorProductToProd k U W) (by
      apply Algebra.TensorProduct.liftEquiv.symm.injective
      apply Subtype.ext
      apply Prod.ext
      · apply SymmetricAlgebra.algHom_ext
        ext u
        simp [SymmetricAlgebra.prodToTensorProduct, SymmetricAlgebra.tensorProductToProd]
      · apply SymmetricAlgebra.algHom_ext
        ext w
        simp [SymmetricAlgebra.prodToTensorProduct, SymmetricAlgebra.tensorProductToProd]) (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      rintro ⟨u, w⟩
      simp [SymmetricAlgebra.prodToTensorProduct, SymmetricAlgebra.tensorProductToProd]
      simpa using (SymmetricAlgebra.ι k (U × W)).map_add (u, 0) (0, w) |>.symm)

/-- The product-to-tensor algebra equivalence sends a generator from the first factor to its left
tensor inclusion. -/
@[simp]
theorem SymmetricAlgebra.prodAlgEquivTensorProduct_iota_fst (u : U) :
    SymmetricAlgebra.prodAlgEquivTensorProduct k U W
        (SymmetricAlgebra.ι k (U × W) (u, 0)) =
      (Algebra.TensorProduct.includeLeft (R := k) (S := k)
        (A := SymmetricAlgebra k U) (B := SymmetricAlgebra k W))
          (SymmetricAlgebra.ι k U u) := by
  simp [SymmetricAlgebra.prodAlgEquivTensorProduct, SymmetricAlgebra.prodToTensorProduct]

/-- The product-to-tensor algebra equivalence sends a generator from the second factor to its right
tensor inclusion. -/
@[simp]
theorem SymmetricAlgebra.prodAlgEquivTensorProduct_iota_snd (w : W) :
    SymmetricAlgebra.prodAlgEquivTensorProduct k U W
        (SymmetricAlgebra.ι k (U × W) (0, w)) =
      (Algebra.TensorProduct.includeRight (R := k)
        (A := SymmetricAlgebra k U)) (SymmetricAlgebra.ι k W w) := by
  simp [SymmetricAlgebra.prodAlgEquivTensorProduct, SymmetricAlgebra.prodToTensorProduct]

end RepresentationTheory.SymmetricAlgebra.ProductTensorProduct
