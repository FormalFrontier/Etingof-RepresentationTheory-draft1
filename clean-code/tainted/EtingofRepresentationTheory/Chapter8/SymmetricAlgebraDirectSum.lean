import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The symmetric algebra of a direct sum

This file supplies the algebra equivalence used in Problem 8.2.10(ii):

`S(U ⊕ W) ≃ S(U) ⊗[k] S(W)`.

Mathlib exposes both universal properties needed for the proof, but does not currently package
this particular equivalence.  We construct the forward map from the two canonical inclusions into
the tensor product and the inverse from the inclusions of `U` and `W` into `U × W`.
-/

open scoped TensorProduct

namespace Etingof

universe u

variable (k U W : Type u) [CommRing k]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]

/-- The canonical map `S(U ⊕ W) → S(U) ⊗ S(W)`. -/
noncomputable def symmetricAlgebraProdToTensor :
    SymmetricAlgebra k (U × W) →ₐ[k]
      SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W :=
  SymmetricAlgebra.lift
    (((Algebra.TensorProduct.includeLeft.toLinearMap.comp
      (SymmetricAlgebra.ι k U)).comp (LinearMap.fst k U W)) +
    ((Algebra.TensorProduct.includeRight.toLinearMap.comp
      (SymmetricAlgebra.ι k W)).comp (LinearMap.snd k U W)))

/-- The canonical map `S(U) ⊗ S(W) → S(U ⊕ W)`. -/
noncomputable def symmetricAlgebraTensorToProd :
    SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W →ₐ[k]
      SymmetricAlgebra k (U × W) :=
  Algebra.TensorProduct.lift
    (SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι k (U × W)).comp (LinearMap.inl k U W)))
    (SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι k (U × W)).comp (LinearMap.inr k U W)))
    (fun _ _ => Commute.all _ _)

/-- **The symmetric algebra takes a binary direct sum to the tensor product.** -/
noncomputable def symmetricAlgebraProdEquivTensor :
    SymmetricAlgebra k (U × W) ≃ₐ[k]
      SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W :=
  AlgEquiv.ofAlgHom (symmetricAlgebraProdToTensor k U W)
    (symmetricAlgebraTensorToProd k U W) (by
      apply Algebra.TensorProduct.liftEquiv.symm.injective
      apply Subtype.ext
      apply Prod.ext
      · apply SymmetricAlgebra.algHom_ext
        ext u
        simp [symmetricAlgebraProdToTensor, symmetricAlgebraTensorToProd]
      · apply SymmetricAlgebra.algHom_ext
        ext w
        simp [symmetricAlgebraProdToTensor, symmetricAlgebraTensorToProd]) (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      rintro ⟨u, w⟩
      simp [symmetricAlgebraProdToTensor, symmetricAlgebraTensorToProd]
      simpa using (SymmetricAlgebra.ι k (U × W)).map_add (u, 0) (0, w) |>.symm)

@[simp]
theorem symmetricAlgebraProdEquivTensor_ι_fst (u : U) :
    symmetricAlgebraProdEquivTensor k U W (SymmetricAlgebra.ι k (U × W) (u, 0)) =
      (Algebra.TensorProduct.includeLeft (R := k) (S := k)
        (A := SymmetricAlgebra k U) (B := SymmetricAlgebra k W))
          (SymmetricAlgebra.ι k U u) := by
  simp [symmetricAlgebraProdEquivTensor, symmetricAlgebraProdToTensor]

@[simp]
theorem symmetricAlgebraProdEquivTensor_ι_snd (w : W) :
    symmetricAlgebraProdEquivTensor k U W (SymmetricAlgebra.ι k (U × W) (0, w)) =
      (Algebra.TensorProduct.includeRight (R := k)
        (A := SymmetricAlgebra k U)) (SymmetricAlgebra.ι k W w) := by
  simp [symmetricAlgebraProdEquivTensor, symmetricAlgebraProdToTensor]

end Etingof
