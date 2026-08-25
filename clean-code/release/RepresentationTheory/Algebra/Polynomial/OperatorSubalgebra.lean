/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.FreeAlgebra.PolynomialOperators

/-! # Polynomial operator subalgebra -/

namespace RepresentationTheory.FreeAlgebra.PolynomialOperators

open Polynomial

variable (k : Type*) [CommRing k]

/-- The two distinguished endomorphisms generate the full algebra under consideration. -/
theorem AuxiliaryAlgebra.operator_pair_adjoin_eq_top :
    Algebra.adjoin k {AuxiliaryAlgebra.firstOperator k, AuxiliaryAlgebra.secondOperator k} = ⊤ := by
  rw [eq_top_iff]
  have hsub :
      Submodule.span k (Set.range (fun p : ℕ × ℕ => AuxiliaryAlgebra.indexedElement k p.1 p.2))
        ≤ (Algebra.adjoin k {AuxiliaryAlgebra.firstOperator k, AuxiliaryAlgebra.secondOperator k}).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    refine Subalgebra.mul_mem _
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin ?_) i)
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin ?_) j)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  intro w _
  exact hsub (AuxiliaryAlgebra.span_range_indexedElement k (Submodule.mem_top))

end RepresentationTheory.FreeAlgebra.PolynomialOperators

namespace RepresentationTheory.Algebra.Polynomial.OperatorSubalgebra

open RepresentationTheory.FreeAlgebra.PolynomialOperators

variable (k : Type*) [CommRing k]

/-- A subalgebra of linear endomorphisms of the polynomial module over a commutative ring. -/
noncomputable def polynomialOperatorSubalgebra : Subalgebra k (Module.End k (Polynomial k)) :=
  Algebra.adjoin k {polynomialMulX k, (Polynomial.derivative : Module.End k (Polynomial k))}

end RepresentationTheory.Algebra.Polynomial.OperatorSubalgebra

namespace RepresentationTheory.FreeAlgebra.PolynomialOperators

open Polynomial
open RepresentationTheory.Algebra.Polynomial.OperatorSubalgebra

variable (k : Type*) [CommRing k]

/-- The range of the polynomial endomorphism map is the designated operator subalgebra. -/
theorem AuxiliaryAlgebra.operatorMap_range :
    (toPolynomialEnd k).range = polynomialOperatorSubalgebra k := by
  rw [polynomialOperatorSubalgebra, ← Algebra.map_top,
    ← AuxiliaryAlgebra.operator_pair_adjoin_eq_top k, AlgHom.map_adjoin]
  congr 1
  rw [Set.image_insert_eq, Set.image_singleton, toPolynomialEnd_firstOperator,
    toPolynomialEnd_secondOperator]

/-- An algebra equivalence from the ambient algebra to the range subalgebra of its polynomial
endomorphism action. -/
noncomputable def AuxiliaryAlgebra.equivOperatorRange [CharZero k] [NoZeroDivisors k] :
    AuxiliaryAlgebra k ≃ₐ[k] polynomialOperatorSubalgebra k :=
  (AlgEquiv.ofInjective (toPolynomialEnd k) (AuxiliaryAlgebra.toPolynomialEnd_injective k)).trans
    (Subalgebra.equivOfEq _ _ (AuxiliaryAlgebra.operatorMap_range k))

/-- The underlying endomorphism of the range equivalence agrees with the associated polynomial
action map. -/
@[simp] theorem AuxiliaryAlgebra.equivOperatorRange_apply [CharZero k] [NoZeroDivisors k]
    (w : AuxiliaryAlgebra k) :
    (AuxiliaryAlgebra.equivOperatorRange k w : Module.End k (Polynomial k)) = toPolynomialEnd k w := rfl

end RepresentationTheory.FreeAlgebra.PolynomialOperators
