/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.MatrixPolynomialHomogeneity
import RepresentationTheory.GeneralLinearGroup.WeightCharacter

namespace RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations

open MvPolynomial RepresentationTheory.MatrixPolynomialHomogeneity

variable {k : Type*} [Field k] {N : ℕ}

/-- The degree-`d` homogeneous submodule of multivariable polynomials in pairs of finite indices is
finite-dimensional over the coefficient field. -/
instance finiteDimensional_homogeneousSubmodule (d : ℕ) :
    FiniteDimensional k (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d) :=
  Submodule.finiteDimensional_of_le
      (S₂ := MvPolynomial.restrictTotalDegree (Fin N × Fin N) k d) <| by
    intro f hf
    rw [MvPolynomial.mem_restrictTotalDegree]
    exact ((MvPolynomial.mem_homogeneousSubmodule d f).1 hf).totalDegree_le

/-- Assigns an auxiliary finite-dimensional general linear group representation to a natural-number
index. -/
noncomputable def auxiliaryIndexedGeneralLinearFDRep
    (k : Type*) [Field k] (N d : ℕ) : FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  haveI : FiniteDimensional k (homogeneousSubrepresentation k N d).toSubmodule :=
    finiteDimensional_homogeneousSubmodule d
  FDRep.of (homogeneousSubrepresentation k N d).toRepresentation

end RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations
