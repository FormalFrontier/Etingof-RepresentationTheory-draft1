import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Order.Lattice
import RepresentationTheory.LinearAlgebra.ModuleDecompositions

namespace RepresentationTheory.RingModuleAuxiliary

/-- A parameterized auxiliary object associated with a ring and one of its modules. -/
structure Auxiliary (R : Type*) [Ring R]
    (M : Type*) [AddCommGroup M] [Module R M] where
  /-- The type attached to a given auxiliary object. -/
  Carrier : Type*
  /-- The additive commutative group structure provided on the attached type. -/
  [instAddCommGroupCarrier : AddCommGroup Carrier]
  /-- The scalar action of the ambient ring on the attached type. -/
  [instModuleCarrier : Module R Carrier]
  /-- The attached type is a projective module over the ambient ring. -/
  [projective : Module.Projective R Carrier]
  /-- An opaque property asserted for the attached type over the ambient ring. -/
  auxiliaryProperty :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate R Carrier
  /-- The linear map from the attached type to the ambient module. -/
  toLinearMap : Carrier →ₗ[R] M
  /-- The associated linear map reaches every element of the ambient module. -/
  surjective_toLinearMap : Function.Surjective toLinearMap
  /-- If a submodule together with the map kernel spans the attached type, then the submodule is
  all of it. -/
  eq_top_of_sup_kernel_eq_top :
    ∀ N : Submodule R Carrier, N ⊔ LinearMap.ker toLinearMap = ⊤ → N = ⊤

attribute [instance] Auxiliary.instAddCommGroupCarrier
  Auxiliary.instModuleCarrier
  Auxiliary.projective

end RepresentationTheory.RingModuleAuxiliary
