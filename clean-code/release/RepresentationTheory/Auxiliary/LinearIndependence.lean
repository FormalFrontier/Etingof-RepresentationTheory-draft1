/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryCharacter

open CategoryTheory MvPolynomial

open scoped TensorProduct

namespace RepresentationTheory.Auxiliary.LinearIndependence

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

omit [CharZero k] in
/-- Auxiliary linear-independence statement from the displayed injectivity and pointwise equality
hypotheses. -/
theorem auxiliaryLinearIndependentOfInjectiveParameterization
    (N : ℕ) {ι : Type*}
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (lam : ι → {l : Fin N → ℕ // Antitone l})
    (hlam : Function.Injective lam)
    (hchar : ∀ i,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (L i) =
        RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N (lam i).val) :
    LinearIndependent ℚ (fun i =>
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (L i)) := by
  have hcomp :
      (fun i => RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (L i))
        = (fun p : {l : Fin N → ℕ // Antitone l} =>
          RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N p.val)
            ∘ lam := by
    funext i; exact hchar i
  rw [hcomp]
  exact
    (RepresentationTheory.AuxiliaryCharacter.auxiliaryPolynomial_linearIndependent N).comp lam hlam

end RepresentationTheory.Auxiliary.LinearIndependence
