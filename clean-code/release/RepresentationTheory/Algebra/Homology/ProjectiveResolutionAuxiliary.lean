/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LinearAlgebra.ExteriorAlgebra.Contraction
import RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex
import RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero
import RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis
import RepresentationTheory.SymmetricAlgebra.ProjectiveResolution
import RepresentationTheory.Algebra.Homology.SymmetricAlgebra.ProductResolution
import RepresentationTheory.Algebra.Homology.SymmetricAlgebraResolution
import RepresentationTheory.Alignment.Attribute

universe u v w

namespace RepresentationTheory.Algebra.Homology.ProjectiveResolutionAuxiliary

/-- A basis-indexed projective resolution of the displayed module over a symmetric algebra. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
noncomputable def basisProjectiveResolutionAuxiliary {k : Type u} [CommRing k] {V : Type v}
    [AddCommGroup V] [Module k V] {κ : Type w} [LinearOrder κ] [Fintype κ]
    (b : Module.Basis κ k V) :
    CategoryTheory.ProjectiveResolution
      (ModuleCat.of (SymmetricAlgebra k V)
        (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V)) :=
  RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis b

section

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]
variable {κ : Type w} [LinearOrder κ] [Fintype κ] (b : Module.Basis κ k V)

/-- The complex underlying the basis-indexed auxiliary projective resolution equals the displayed complex. -/
theorem basisProjectiveResolutionAuxiliary_complex_eq :
    (basisProjectiveResolutionAuxiliary b).complex =
      RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex b := rfl

/-- Every degree of the complex underlying the basis-indexed auxiliary projective resolution is free over the symmetric algebra. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
theorem basisProjectiveResolutionAuxiliary_free (i : ℕ) :
    Module.Free (SymmetricAlgebra k V) ((basisProjectiveResolutionAuxiliary b).complex.X i) :=
  RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfBasis_X_free b i

/-- The degree-zero component of the augmentation of the basis-indexed auxiliary projective resolution equals the displayed module morphism. -/
theorem basisProjectiveResolutionAuxiliary_pi_f_zero_eq :
    (basisProjectiveResolutionAuxiliary b).π.f 0 =
      ModuleCat.ofHom
        (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero k V) :=
  RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.basisComplexToSingleZero_f_zero b

end

section

variable (k U W : Type u) [Field k]
  [AddCommGroup U] [Module k U] [FiniteDimensional k U]
  [AddCommGroup W] [Module k W]

/-- An auxiliary projective resolution of the displayed module associated with a finite-dimensional module and a second module over a field. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
noncomputable def finiteDimensionalProjectiveResolutionAuxiliary :
    CategoryTheory.ProjectiveResolution
      (RepresentationTheory.Algebra.Homology.SymmetricAlgebra.ProductResolution.productSymmetricAlgebraModule k U W) :=
  RepresentationTheory.Algebra.Homology.SymmetricAlgebra.ProductResolution.productSymmetricAlgebraProjectiveResolution k U W

/-- Each component of the finite-dimensional auxiliary projective resolution is isomorphic to the displayed module over the symmetric algebra on the product module. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
noncomputable def finiteDimensionalProjectiveResolutionAuxiliary_componentIso (i : ℕ) :
    (finiteDimensionalProjectiveResolutionAuxiliary k U W).complex.X i ≅
      ModuleCat.of (SymmetricAlgebra k (U × W))
        (RepresentationTheory.Algebra.Homology.SymmetricAlgebra.ProductResolution.productResolutionTerm k U W i) :=
  RepresentationTheory.Algebra.Homology.SymmetricAlgebra.ProductResolution.productResolutionComponentIso k U W i

/-- Every degree of the finite-dimensional auxiliary projective resolution is free over the symmetric algebra on the product module. -/
theorem finiteDimensionalProjectiveResolutionAuxiliary_free (i : ℕ) :
    Module.Free (SymmetricAlgebra k (U × W))
      ((finiteDimensionalProjectiveResolutionAuxiliary k U W).complex.X i) :=
  RepresentationTheory.Algebra.Homology.SymmetricAlgebra.ProductResolution.productResolutionComponent_free k U W i

/-- The augmentation of the finite-dimensional auxiliary projective resolution is a quasi-isomorphism. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
theorem finiteDimensionalProjectiveResolutionAuxiliary_pi_quasiIso :
    QuasiIso (finiteDimensionalProjectiveResolutionAuxiliary k U W).π :=
  RepresentationTheory.Algebra.Homology.SymmetricAlgebra.ProductResolution.productResolution_augmentation_quasiIso k U W

end


section PartV

variable {k V κ : Type u} [Field k] [AddCommGroup V] [Module k V]
variable [LinearOrder κ] [Fintype κ] (b : Module.Basis κ k V)

/-- A basis-indexed isomorphism from the displayed module construction to the dual of an exterior power. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
noncomputable def basisIndexedDualExteriorPowerIsoAuxiliary (i : ℕ) :
    RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology k
        (SymmetricAlgebra k V)
        (ModuleCat.of (SymmetricAlgebra k V)
          (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V))
        (ModuleCat.of (SymmetricAlgebra k V)
          (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V)) i ≅
      ModuleCat.of k (Module.Dual k (⋀[k]^i V)) :=
  RepresentationTheory.Algebra.Homology.SymmetricAlgebraResolution.SymmetricAlgebra.indexedObjectIsoExteriorPowerDual k V b i

/-- A basis-indexed isomorphism from the displayed module construction to an exterior power. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
noncomputable def basisIndexedExteriorPowerIsoAuxiliary (i : ℕ) :
    RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k
        (SymmetricAlgebra k V)
        (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V)
        ((RepresentationTheory.Algebra.Module.DirectSumData.commRingModuleToOpposite
          (SymmetricAlgebra k V)).obj
          (ModuleCat.of (SymmetricAlgebra k V)
            (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V))) i ≅
      ModuleCat.of k (⋀[k]^i V) :=
  RepresentationTheory.Algebra.Homology.SymmetricAlgebraResolution.SymmetricAlgebra.indexedObjectIsoExteriorPower k V b i

end PartV

end RepresentationTheory.Algebra.Homology.ProjectiveResolutionAuxiliary
