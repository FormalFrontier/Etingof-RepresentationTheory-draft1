/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.FreeAlgebra.PolynomialOperators
import RepresentationTheory.Alignment.Attribute

/-! # An auxiliary endomorphism model for polynomial operators -/

namespace RepresentationTheory.Algebra.Polynomial.EndomorphismAuxiliary

open Polynomial
open RepresentationTheory.FreeAlgebra.PolynomialOperators

variable (k : Type*) [CommRing k]

/-- Adjoining the two displayed elements gives the top subalgebra. -/
theorem auxiliary_adjoin_pair_eq_top :
    Algebra.adjoin k {OperatorAlgebra.firstOperator k, OperatorAlgebra.secondOperator k} = ⊤ := by
  rw [eq_top_iff]

  have hsub :
      Submodule.span k (Set.range (fun p : ℕ × ℕ => OperatorAlgebra.monomialOperator k p.1 p.2))
        ≤ (Algebra.adjoin k {OperatorAlgebra.firstOperator k, OperatorAlgebra.secondOperator k}).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    refine Subalgebra.mul_mem _
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin ?_) i)
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin ?_) j)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  intro w _
  exact hsub (OperatorAlgebra.span_monomialOperator k (Submodule.mem_top))

/-- An auxiliary subalgebra of endomorphisms of the polynomial module over a commutative ring. -/
@[source_ref "Chapter2/Remark2.7.2" (role := supporting)]
noncomputable def auxiliaryEndomorphismSubalgebra : Subalgebra k (Module.End k (Polynomial k)) :=
  Algebra.adjoin k {polynomialMulX k, (Polynomial.derivative : Module.End k (Polynomial k))}

/-- The range of the displayed algebra homomorphism equals the displayed subalgebra. -/
@[source_ref "Chapter2/Remark2.7.2" (role := supporting)]
theorem auxiliaryMap_range :
    (toPolynomialEnd k).range = auxiliaryEndomorphismSubalgebra k := by
  rw [auxiliaryEndomorphismSubalgebra, ← Algebra.map_top, ← auxiliary_adjoin_pair_eq_top k,
    AlgHom.map_adjoin]
  congr 1
  rw [Set.image_insert_eq, Set.image_singleton, toPolynomialEnd_firstOperator,
    toPolynomialEnd_secondOperator]

/-- An auxiliary algebra equivalence to the subtype of the displayed subalgebra. -/
@[source_ref "Chapter2/Remark2.7.2" (role := supporting)]
noncomputable def auxiliaryAlgEquiv [CharZero k] [NoZeroDivisors k] :
    OperatorAlgebra k ≃ₐ[k] auxiliaryEndomorphismSubalgebra k :=
  (AlgEquiv.ofInjective (toPolynomialEnd k) (OperatorAlgebra.toPolynomialEnd_injective k)).trans
    (Subalgebra.equivOfEq _ _ (auxiliaryMap_range k))

/-- The value underlying the auxiliary algebra equivalence agrees with the displayed map. -/
@[simp] theorem auxiliaryAlgEquiv_apply [CharZero k] [NoZeroDivisors k]
    (w : OperatorAlgebra k) :
    (auxiliaryAlgEquiv k w : Module.End k (Polynomial k)) = toPolynomialEnd k w := rfl

end RepresentationTheory.Algebra.Polynomial.EndomorphismAuxiliary
