/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.FreeAlgebra.PolynomialOperators

/-! # Endomorphism relation action -/

namespace RepresentationTheory.FreeAlgebra.PolynomialOperators

universe u v

namespace AuxiliaryAlgebra

variable (k : Type u) [CommRing k]
variable (M : Type v) [AddCommGroup M] [Module k M]

/-- The assignment of the two free generators to a pair of endomorphisms. -/
private noncomputable def repGen (X Y : Module.End k M) : Fin 2 → Module.End k M :=
  ![X, Y]

/-- The representation of the free algebra determined by `X` and `Y`. -/
private noncomputable def repFree (X Y : Module.End k M) :
    FreeAlgebra k (Fin 2) →ₐ[k] Module.End k M :=
  FreeAlgebra.lift k (repGen k M X Y)

private theorem repFree_rel (X Y : Module.End k M) (hrel : Y * X = X * Y + 1) :
    ∀ ⦃a b⦄, auxiliaryRelation k a b → repFree k M X Y a = repFree k M X Y b := by
  rintro _ _ ⟨rfl, rfl⟩
  simpa [repFree, repGen] using hrel

/-- The algebra homomorphism into module endomorphisms induced by a pair satisfying the displayed
commutation relation. -/
noncomputable def endomorphismAction (X Y : Module.End k M) (hrel : Y * X = X * Y + 1) :
    AuxiliaryAlgebra k →ₐ[k] Module.End k M :=
  RingQuot.liftAlgHom k ⟨repFree k M X Y, repFree_rel k M X Y hrel⟩

/-- The induced endomorphism action sends the first distinguished generator to the first given
endomorphism. -/
@[simp] theorem endomorphismAction_firstGenerator (X Y : Module.End k M)
    (hrel : Y * X = X * Y + 1) :
    endomorphismAction k M X Y hrel (AuxiliaryAlgebra.firstOperator k) = X := by
  simp [endomorphismAction, AuxiliaryAlgebra.firstOperator, AuxiliaryAlgebra.fromFreeAlgebra,
    RingQuot.liftAlgHom_mkAlgHom_apply, repFree, repGen]

/-- The induced endomorphism action sends the second distinguished generator to the second given
endomorphism. -/
@[simp] theorem endomorphismAction_secondGenerator (X Y : Module.End k M)
    (hrel : Y * X = X * Y + 1) :
    endomorphismAction k M X Y hrel (AuxiliaryAlgebra.secondOperator k) = Y := by
  simp [endomorphismAction, AuxiliaryAlgebra.secondOperator, AuxiliaryAlgebra.fromFreeAlgebra,
    RingQuot.liftAlgHom_mkAlgHom_apply, repFree, repGen]

/-- To prove a predicate for every algebra element, it suffices to check both generators and
scalars and to preserve addition and multiplication. -/
theorem induction_on {p : AuxiliaryAlgebra k → Prop} (a : AuxiliaryAlgebra k)
    (hfirst : p (AuxiliaryAlgebra.firstOperator k)) (hsecond : p (AuxiliaryAlgebra.secondOperator k))
    (halgebraMap : ∀ r, p (algebraMap k (AuxiliaryAlgebra k) r))
    (hadd : ∀ a b, p a → p b → p (a + b))
    (hmul : ∀ a b, p a → p b → p (a * b)) : p a := by
  obtain ⟨a', rfl⟩ := RingQuot.mkAlgHom_surjective k (auxiliaryRelation k) a
  have ha' : a' ∈ Algebra.adjoin k (Set.range (FreeAlgebra.ι k)) := by
    rw [FreeAlgebra.adjoin_range_ι]
    exact Algebra.mem_top
  induction ha' using Algebra.adjoin_induction with
  | mem g hg =>
      obtain ⟨idx, rfl⟩ := hg
      fin_cases idx
      · simpa [AuxiliaryAlgebra.firstOperator, AuxiliaryAlgebra.fromFreeAlgebra] using hfirst
      · simpa [AuxiliaryAlgebra.secondOperator, AuxiliaryAlgebra.fromFreeAlgebra] using hsecond
  | algebraMap r =>
      simpa using halgebraMap r
  | add u v _ _ ihu ihv =>
      simpa only [map_add] using hadd _ _ ihu ihv
  | mul u v _ _ ihu ihv =>
      simpa only [map_mul] using hmul _ _ ihu ihv

/-- Endomorphisms satisfying the displayed commutation relation induce a module structure over
the associated algebra. -/
@[reducible] noncomputable def moduleOfEndomorphismRelation (X Y : Module.End k M)
    (hrel : Y * X = X * Y + 1) : Module (AuxiliaryAlgebra k) M :=
  Module.compHom M (endomorphismAction k M X Y hrel).toRingHom

/-- Scalar multiplication by an algebra element agrees with evaluation of its induced endomorphism
action. -/
theorem smul_eq_action_apply (X Y : Module.End k M) (hrel : Y * X = X * Y + 1)
    (a : AuxiliaryAlgebra k) (m : M) :
    (moduleOfEndomorphismRelation k M X Y hrel).toSMul.smul a m =
      endomorphismAction k M X Y hrel a m := rfl

/-- The module action induced by endomorphisms satisfying the displayed commutation relation
extends the scalar tower from the coefficient ring. -/
theorem isScalarTower (X Y : Module.End k M)
    (hrel : Y * X = X * Y + 1) :
    letI : Module (AuxiliaryAlgebra k) M := moduleOfEndomorphismRelation k M X Y hrel
    IsScalarTower k (AuxiliaryAlgebra k) M := by
  letI : Module (AuxiliaryAlgebra k) M := moduleOfEndomorphismRelation k M X Y hrel
  exact
    { smul_assoc := fun c a m => by
        change endomorphismAction k M X Y hrel (c • a) m =
          c • endomorphismAction k M X Y hrel a m
        rw [map_smul]
        rfl }

end AuxiliaryAlgebra

end RepresentationTheory.FreeAlgebra.PolynomialOperators
