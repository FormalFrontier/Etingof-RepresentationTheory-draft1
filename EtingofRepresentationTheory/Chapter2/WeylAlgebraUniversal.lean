import EtingofRepresentationTheory.Chapter2.Proposition2_7_1

/-!
# Universal mapping property of the Weyl algebra

The quotient presentation of `WeylAlgebra k` is useful for its PBW basis, but representations
are most conveniently constructed from two endomorphisms `X` and `Y` satisfying
`Y * X = X * Y + 1`.  This file packages that construction as an algebra homomorphism and as a
module structure.
-/

namespace Etingof

universe u v

namespace WeylAlgebra

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
    ∀ ⦃a b⦄, WeylAlgebraRel k a b → repFree k M X Y a = repFree k M X Y b := by
  rintro _ _ ⟨rfl, rfl⟩
  simpa [repFree, repGen] using hrel

/-- **Universal mapping property of the Weyl algebra.** A pair of `k`-linear endomorphisms
`X, Y` satisfying `Y * X = X * Y + 1` determines a representation of `WeylAlgebra k`. -/
noncomputable def toEnd (X Y : Module.End k M) (hrel : Y * X = X * Y + 1) :
    WeylAlgebra k →ₐ[k] Module.End k M :=
  RingQuot.liftAlgHom k ⟨repFree k M X Y, repFree_rel k M X Y hrel⟩

@[simp] theorem toEnd_x (X Y : Module.End k M) (hrel : Y * X = X * Y + 1) :
    toEnd k M X Y hrel (WeylAlgebra.x k) = X := by
  simp [toEnd, WeylAlgebra.x, WeylAlgebra.mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    repFree, repGen]

@[simp] theorem toEnd_y (X Y : Module.End k M) (hrel : Y * X = X * Y + 1) :
    toEnd k M X Y hrel (WeylAlgebra.y k) = Y := by
  simp [toEnd, WeylAlgebra.y, WeylAlgebra.mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    repFree, repGen]

/-- Induction on the two Weyl generators. This is the quotient-algebra counterpart of
`FreeAlgebra.induction_on`; it is useful for extending identities checked on `x` and `y` to the
whole Weyl algebra. -/
theorem induction_on {p : WeylAlgebra k → Prop} (a : WeylAlgebra k)
    (hx : p (WeylAlgebra.x k)) (hy : p (WeylAlgebra.y k))
    (halgebraMap : ∀ r, p (algebraMap k (WeylAlgebra k) r))
    (hadd : ∀ a b, p a → p b → p (a + b))
    (hmul : ∀ a b, p a → p b → p (a * b)) : p a := by
  obtain ⟨a', rfl⟩ := RingQuot.mkAlgHom_surjective k (WeylAlgebraRel k) a
  have ha' : a' ∈ Algebra.adjoin k (Set.range (FreeAlgebra.ι k)) := by
    rw [FreeAlgebra.adjoin_range_ι]
    exact Algebra.mem_top
  induction ha' using Algebra.adjoin_induction with
  | mem g hg =>
      obtain ⟨idx, rfl⟩ := hg
      fin_cases idx
      · simpa [WeylAlgebra.x, WeylAlgebra.mk] using hx
      · simpa [WeylAlgebra.y, WeylAlgebra.mk] using hy
  | algebraMap r =>
      simpa using halgebraMap r
  | add u v _ _ ihu ihv =>
      simpa only [map_add] using hadd _ _ ihu ihv
  | mul u v _ _ ihu ihv =>
      simpa only [map_mul] using hmul _ _ ihu ihv

/-- The module structure associated to a Weyl pair. -/
@[reducible] noncomputable def module (X Y : Module.End k M) (hrel : Y * X = X * Y + 1) :
    Module (WeylAlgebra k) M :=
  Module.compHom M (toEnd k M X Y hrel).toRingHom

/-- The action associated to `module` is evaluation of `toEnd`. -/
theorem smul_def (X Y : Module.End k M) (hrel : Y * X = X * Y + 1)
    (a : WeylAlgebra k) (m : M) :
    (module k M X Y hrel).toSMul.smul a m = toEnd k M X Y hrel a m := rfl

/-- The scalar tower associated to a Weyl-pair representation. -/
theorem isScalarTower (X Y : Module.End k M)
    (hrel : Y * X = X * Y + 1) :
    letI : Module (WeylAlgebra k) M := module k M X Y hrel
    IsScalarTower k (WeylAlgebra k) M := by
  letI : Module (WeylAlgebra k) M := module k M X Y hrel
  exact
    { smul_assoc := fun c a m => by
        change toEnd k M X Y hrel (c • a) m = c • toEnd k M X Y hrel a m
        rw [map_smul]
        rfl }

end WeylAlgebra

end Etingof
