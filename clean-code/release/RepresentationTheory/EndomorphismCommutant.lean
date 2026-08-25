/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.TensorPolynomial.Contraction
import RepresentationTheory.TensorPower

/-!
# Endomorphism commutants

This module characterizes a permutation endomorphism algebra by commutation
with tensor-power images of invertible endomorphisms.
-/

noncomputable section

namespace RepresentationTheory.EndomorphismCommutant

open scoped TensorProduct

variable (N n : ℕ)

private abbrev diagOp
    (g : (Module.End ℂ
      (RepresentationTheory.TensorPolynomial.Contraction.TensorPolynomial.AuxiliaryIndexType N))ˣ) :
    Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ
      (RepresentationTheory.TensorPolynomial.Contraction.TensorPolynomial.AuxiliaryIndexType N) n) :=
  PiTensorProduct.map (R := ℂ) (fun _ : Fin n => (g : Module.End ℂ
    (RepresentationTheory.TensorPolynomial.Contraction.TensorPolynomial.AuxiliaryIndexType N)))

/-- An endomorphism belongs to the given collection exactly when it commutes with the image of every unit of the specified endomorphism ring. -/
theorem mem_iff_commutes_with_unit_images
    (M : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ
      (RepresentationTheory.TensorPolynomial.Contraction.TensorPolynomial.AuxiliaryIndexType N) n)) :
    M ∈ RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ
        (RepresentationTheory.TensorPolynomial.Contraction.TensorPolynomial.AuxiliaryIndexType N) n ↔
      ∀ g : (Module.End ℂ
        (RepresentationTheory.TensorPolynomial.Contraction.TensorPolynomial.AuxiliaryIndexType N))ˣ,
        Commute (diagOp N n g) M := by
  rw [(RepresentationTheory.Auxiliary.MutualCentralizers.mutual_centralizer_algebras ℂ
    (RepresentationTheory.TensorPolynomial.Contraction.TensorPolynomial.AuxiliaryIndexType N) n).1,
    Subalgebra.mem_centralizer_iff]
  constructor
  ·
    intro h g
    have hmem : diagOp N n g ∈
        (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra ℂ
          (RepresentationTheory.TensorPolynomial.Contraction.TensorPolynomial.AuxiliaryIndexType N) n :
          Set (Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ
            (RepresentationTheory.TensorPolynomial.Contraction.TensorPolynomial.AuxiliaryIndexType N) n))) := by
      rw [← RepresentationTheory.TensorPower.adjoin_piTensorProductMaps_eq_auxiliary
        (V := RepresentationTheory.TensorPolynomial.Contraction.TensorPolynomial.AuxiliaryIndexType N) ℂ n]
      exact Algebra.subset_adjoin ⟨g, rfl⟩
    exact h _ hmem
  ·
    intro h y hy
    rw [← RepresentationTheory.TensorPower.adjoin_piTensorProductMaps_eq_auxiliary
      (V := RepresentationTheory.TensorPolynomial.Contraction.TensorPolynomial.AuxiliaryIndexType N) ℂ n] at hy
    have hcomm : Commute M y :=
      Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy (by
        rintro _ ⟨g, rfl⟩; exact (h g).symm)
    exact hcomm.symm

end RepresentationTheory.EndomorphismCommutant
