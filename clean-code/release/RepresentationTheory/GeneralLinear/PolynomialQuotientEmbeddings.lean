/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies
import RepresentationTheory.GeneralLinear.AuxiliaryPolynomialQuotient
import RepresentationTheory.GeneralLinearRepresentation.WeightPolynomialDecomposition
import RepresentationTheory.Auxiliary.AuxiliaryPolynomialSubrepresentation
import RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
import RepresentationTheory.LinearAlgebra.GeneralLinearGroup.PolynomialCoefficients
import RepresentationTheory.AuxiliaryModuleData

namespace RepresentationTheory.GeneralLinear.PolynomialQuotientEmbeddings

open MvPolynomial
open RepresentationTheory.GeneralLinear.AuxiliaryPolynomialQuotient
open RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.GeneralLinearRepresentation.WeightPolynomialDecomposition
open GeneralLinearRepresentation
open RepresentationTheory.LinearAlgebra.GeneralLinearGroup.PolynomialCoefficients
open RepresentationTheory.SymmetricPolynomials.Alternant

/-- A simple finite-dimensional representation admitting an injective equivariant linear map into
the polynomial quotient has an auxiliary antitone function whose range contains zero and whose
auxiliary value agrees with that of the representation. -/
theorem exists_auxiliary_antitone_with_zero_of_equivariant_embedding
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (φ : L →ₗ[k]
      (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N))
    (hφ_inj : Function.Injective φ)
    (hφ_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      φ (L.ρ g v) = matrixPolynomialQuotientRepresentation k N g (φ v)) :
    ∃ ν : Fin N → ℕ, Antitone ν ∧ (0 : ℕ) ∈ Set.range ν ∧
      weightCharacter k N L = partitionPolynomial N ν := by
  classical
  obtain ⟨d, ψ, hψ_inj, hψ_equiv⟩ :=
    exists_equivariantEmbedding_auxiliaryRepresentationFamily
      k N L hLsimp φ hφ_inj hφ_equiv
  obtain ⟨S, c, hS0, hchar⟩ :=
    exists_auxiliaryPolynomial_familyOne_expansion (k := k) N d
  obtain ⟨ν, hνS, _hcpos, hcharL⟩ :=
    exists_positive_polynomial_term_of_simple_subrepresentation k N
      (auxiliaryRepresentationFamilyOne k N d)
      (fdRep_rho_satisfies_property' k N d)
      (iSup_familyOneAuxiliarySubmodule_eq_top (k := k) (N := N) d)
      S c hchar L hLsimp ψ hψ_inj hψ_equiv
  exact ⟨ν.val, ν.property, hS0 ν hνS, hcharL⟩

end RepresentationTheory.GeneralLinear.PolynomialQuotientEmbeddings
