/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

open Finset Equiv.Perm MvPowerSeries

noncomputable section

namespace RepresentationTheory.LinearAlgebra.AuxiliaryPowerSeriesMatrix

variable (N : ℕ) (k : Type*) [Field k]

/-- An auxiliary type family indexed by natural numbers. -/
abbrev AuxiliaryIndex (N : ℕ) := Fin N ⊕ Fin N

/-- An auxiliary two-indexed family of multivariate power series. -/
noncomputable def auxiliaryPowerSeriesArray (i j : Fin N) :
    MvPowerSeries (AuxiliaryIndex N) k :=
  MvPowerSeries.invOfUnit
    (1 - MvPowerSeries.X (Sum.inl i) * MvPowerSeries.X (Sum.inr j))
    1

/-- An auxiliary square matrix of multivariate power series. -/
noncomputable def auxiliaryPowerSeriesMatrix :
    Matrix (Fin N) (Fin N) (MvPowerSeries (AuxiliaryIndex N) k) :=
  Matrix.of (fun i j => auxiliaryPowerSeriesArray N k i j)

/-- An auxiliary multivariate power series identified with the matrix determinant. -/
noncomputable def auxiliaryDeterminantPowerSeries :
    MvPowerSeries (AuxiliaryIndex N) k :=
  ∑ σ : Equiv.Perm (Fin N),
    (MvPowerSeries.C (Int.cast (Equiv.Perm.sign σ : ℤ) : k)) *
      ∏ j : Fin N,
        MvPowerSeries.invOfUnit
          (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)))
          1

/-- The determinant of the auxiliary multivariate power series matrix is the auxiliary determinant power series. -/
@[source_ref "Chapter5/Corollary5.15.4" (role := supporting)]
theorem det_auxiliaryPowerSeriesMatrix
    (N : ℕ) :
    (auxiliaryPowerSeriesMatrix N k).det = auxiliaryDeterminantPowerSeries N k := by
  simp only [Matrix.det_apply', auxiliaryDeterminantPowerSeries, auxiliaryPowerSeriesMatrix,
    Matrix.of_apply, auxiliaryPowerSeriesArray]
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin N)))
  intro σ
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv]
  congr 1
  · exact (map_intCast (MvPowerSeries.C (σ := AuxiliaryIndex N) (R := k)) _).symm
  · exact Fintype.prod_equiv σ _ _ (fun i => by simp)

end RepresentationTheory.LinearAlgebra.AuxiliaryPowerSeriesMatrix
