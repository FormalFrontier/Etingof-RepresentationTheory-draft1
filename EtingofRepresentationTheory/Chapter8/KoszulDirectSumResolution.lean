import EtingofRepresentationTheory.Chapter8.SymmetricAlgebraDirectSum
import EtingofRepresentationTheory.Chapter8.ExternalTensorResolutionLeft
import EtingofRepresentationTheory.Chapter8.KoszulResolution

/-!
# The Koszul resolution of a complementary symmetric algebra

For finite-dimensional vector spaces `U` and `W`, this file constructs the resolution in Problem
8.2.10(ii).  We tensor the Koszul resolution of the trivial `S(U)`-module with the degree-zero
resolution of the regular `S(W)`-module.  The external tensor product is a resolution over
`S(U) ⊗ S(W)`; restriction along `S(U ⊕ W) ≃ S(U) ⊗ S(W)` transports it to `S(U ⊕ W)`.

The resolved object `koszulComplementModule k U W` has underlying vector space
`k ⊗[k] S(W)`, canonically equivalent to `S(W)`.  Its action is the requested one: the `U`
generators act through the augmentation of `S(U)`, hence by zero, while the `W` generators act
regularly on the second factor.
-/

open scoped TensorProduct
open CategoryTheory

namespace Etingof

universe u

variable (k U W : Type u) [Field k]
  [AddCommGroup U] [Module k U] [FiniteDimensional k U]
  [AddCommGroup W] [Module k W]

/-- The degree-zero projective resolution of the regular `S(W)`-module. -/
noncomputable def symmetricAlgebraSelfResolution :
    ProjectiveResolution
      (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) :=
  ProjectiveResolution.self
    (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))

/-- Tensor the Koszul resolution of `k` over `S(U)` with the regular `S(W)`-module.  This is the
untransported form of Problem 8.2.10(ii), over `S(U) ⊗ S(W)`. -/
noncomputable def tensorKoszulComplementResolution :
    ProjectiveResolution
      (extTensorFunctorLeftObj k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
        (ModuleCat.of (SymmetricAlgebra k U) (KoszulAugModule k U))
        (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))) :=
  extTensorProjectiveResolutionLeft
    (koszulResolutionOfFiniteDimensional k U)
    (symmetricAlgebraSelfResolution k W)

/-- Change scalars from `S(U) ⊗ S(W)` to `S(U ⊕ W)` along the canonical algebra equivalence. -/
noncomputable abbrev restrictTensorToProd :
    ModuleCat (SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W) ⥤
      ModuleCat (SymmetricAlgebra k (U × W)) :=
  ModuleCat.restrictScalars
    (symmetricAlgebraProdEquivTensor k U W).toRingEquiv.toRingHom

/-- `S(W)` as an `S(U ⊕ W)`-module, presented as `k ⊗[k] S(W)`.  The first summand acts through
the augmentation and the second summand acts regularly. -/
noncomputable def koszulComplementModule : ModuleCat (SymmetricAlgebra k (U × W)) :=
  (restrictTensorToProd k U W).obj
    (extTensorFunctorLeftObj k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
      (ModuleCat.of (SymmetricAlgebra k U) (KoszulAugModule k U))
      (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)))

/-- **Problem 8.2.10(ii), resolution endpoint.**  The external tensor Koszul complex, transported
along `S(U ⊕ W) ≃ S(U) ⊗ S(W)`, is a projective resolution of the complementary symmetric-algebra
module.  Exactness is inherited from `extTensorProjectiveResolutionLeft`; no new homological
choice is made here. -/
noncomputable def koszulComplementResolution :
    ProjectiveResolution (koszulComplementModule k U W) :=
  (restrictTensorToProd k U W).mapProjectiveResolution
    (tensorKoszulComplementResolution k U W)

@[simp]
theorem koszulComplementResolution_complex :
    (koszulComplementResolution k U W).complex =
      ((restrictTensorToProd k U W).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (tensorKoszulComplementResolution k U W).complex :=
  rfl

/-- Every term of the transported complex is projective. -/
theorem koszulComplementResolution_projective (i : ℕ) :
    Projective ((koszulComplementResolution k U W).complex.X i) :=
  (koszulComplementResolution k U W).projective i

/-- The augmentation of the transported complex is a quasi-isomorphism, i.e. the complex is
exact and resolves `koszulComplementModule`. -/
theorem koszulComplementResolution_quasiIso :
    QuasiIso (koszulComplementResolution k U W).π :=
  (koszulComplementResolution k U W).quasiIso

end Etingof
