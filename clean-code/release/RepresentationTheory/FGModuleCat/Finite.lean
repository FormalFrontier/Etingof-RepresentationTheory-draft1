import RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence
import RepresentationTheory.CategoryTheory.Projective.Auxiliary
import RepresentationTheory.FGModuleCat.SimpleModules
import RepresentationTheory.FGModuleCat.FiniteLengthAndSubmoduleComplexes
import RepresentationTheory.FGModuleCat.SubobjectOrder
import RepresentationTheory.FGModuleCat.Projectivity

set_option linter.dupNamespace false

open CategoryTheory Limits

open scoped ModuleCat.Algebra

open RepresentationTheory.CategoryTheory.Abelian.FiniteLength
open RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence
open RepresentationTheory.CategoryTheory.Projective.Auxiliary
open RepresentationTheory.CategoryTheory.ProjectiveEpiProperties
open RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional
open RepresentationTheory.FGModuleCat.FiniteLengthAndSubmoduleComplexes

namespace RepresentationTheory.FGModuleCat.Finite

universe u

noncomputable section

variable (k : Type u) [Field k] [IsAlgClosed k]
variable (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]

include k

omit [IsAlgClosed k] in
/-- A ring finite as a module over a field is Artinian. -/
theorem isArtinianRing_of_module_finite : IsArtinianRing A :=
  IsArtinianRing.of_finite k A

/-- The category of finitely generated modules satisfies the displayed auxiliary condition. -/
@[reducible]
def FGModuleCat.auxiliary : SubobjectFiniteDimensional (FGModuleCat.{u} A) :=
  haveI : IsArtinianRing A := isArtinianRing_of_module_finite k A
  haveI : IsNoetherianRing A := inferInstance
  let H := RepresentationTheory.FGModuleCat.SimpleModules.exists_completeSimpleObjectFamily k A
  { Auxiliary := H.choose
    auxiliaryFintype := H.choose_spec.choose
    auxiliaryObject := H.choose_spec.choose_spec.choose
    simple_auxiliaryObject := H.choose_spec.choose_spec.choose_spec.1
    simple_iso_auxiliaryObject_data := H.choose_spec.choose_spec.choose_spec.2
    finiteDimensionalOrder_subobject_data := fun X =>
      RepresentationTheory.FGModuleCat.SubobjectOrder.finiteDimensionalOrder_subobject X }

/-- The hom space between finitely generated modules is linearly equivalent to the corresponding space of linear maps. -/
def FGModuleCat.homLinearEquiv (X Y : FGModuleCat.{u} A) :
    (X ⟶ Y) ≃ₗ[k] (X →ₗ[A] Y) :=
  (InducedCategory.homLinearEquiv (R := k)).trans ModuleCat.homLinearEquiv

omit [IsAlgClosed k] in
/-- Hom spaces between finitely generated modules are finite-dimensional over the base field. -/
theorem FGModuleCat.finiteDimensional_hom (X Y : FGModuleCat.{u} A) :
    FiniteDimensional k (X ⟶ Y) := by
  haveI : Module.Finite k (X : Type u) := Module.Finite.trans A (X : Type u)
  haveI : Module.Finite k (Y : Type u) := Module.Finite.trans A (Y : Type u)
  haveI : Module.Finite k (X →ₗ[A] Y) :=
    Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ (S := A) (M := (X : Type u)) (N := (Y : Type u)) (R := k)
        (R₁ := k))
      (LinearMap.restrictScalars_injective k)
  exact Module.Finite.equiv (FGModuleCat.homLinearEquiv k A X Y).symm

/-- The endomorphism algebra of a simple finitely generated module is algebra-equivalent to the base field. -/
theorem FGModuleCat.simple_endAlgEquiv (X : FGModuleCat.{u} A) (hX : Simple X) :
    Nonempty (End X ≃ₐ[k] k) := by
  haveI : IsArtinianRing A := isArtinianRing_of_module_finite k A
  haveI : IsNoetherianRing A := inferInstance
  haveI := hX
  haveI : FiniteDimensional k (X ⟶ X) := FGModuleCat.finiteDimensional_hom k A X X
  haveI : Nontrivial (End X) := nontrivial_of_ne _ _ (id_nonzero X)
  have hsurj : Function.Surjective (algebraMap k (End X)) := by
    intro f
    obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k f
    refine ⟨c, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, End.one_def]
    exact hc
  have hinj : Function.Injective (algebraMap k (End X)) := RingHom.injective _
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k (End X)) ⟨hinj, hsurj⟩).symm⟩

/-- Over an algebraically closed field, the category of finitely generated modules has the displayed auxiliary property. -/
theorem FGModuleCat.auxiliaryOfAlgebraicallyClosed :
    letI := FGModuleCat.auxiliary k A
    SchurFiniteLengthCategory k (FGModuleCat.{u} A) := by
  letI := FGModuleCat.auxiliary k A
  haveI : IsArtinianRing A := isArtinianRing_of_module_finite k A
  haveI : IsNoetherianRing A := inferInstance
  exact
    { hasFiniteLength := fun X => fgModuleProperty_of_isNoetherianRing_of_isArtinianRing X
      simpleEndAlgEquiv := fun X hX => FGModuleCat.simple_endAlgEquiv k A X hX }

omit [IsAlgClosed k] in
/-- There is an object satisfying the displayed auxiliary predicate. -/
theorem auxiliary_exists_nonempty :
    ∃ P : FGModuleCat.{u} A, Nonempty (HasProjectiveEpiWitnesses P) := by
  letI := FGModuleCat.auxiliary k A
  exact exists_object_with_nonempty_auxiliary (FGModuleCat.{u} A)

/-- The opposite endomorphism ring of a finitely generated module is Noetherian. -/
theorem FGModuleCat.isNoetherianRing_opEnd (P : FGModuleCat.{u} A) :
    IsNoetherianRing (End P)ᵐᵒᵖ := by
  letI := FGModuleCat.auxiliary k A
  letI := FGModuleCat.auxiliaryOfAlgebraicallyClosed k A
  exact opEnd_isNoetherian (k := k) P

/-- There is a finitely generated module whose opposite endomorphism ring gives an equivalent category of finitely generated modules. -/
theorem FGModuleCat.exists_equivalence_opEnd :
    ∃ P : FGModuleCat.{u} A, Nonempty (FGModuleCat.{u} A ≌ FGModuleCat.{u} (End P)ᵐᵒᵖ) := by
  letI := FGModuleCat.auxiliary k A
  letI := FGModuleCat.auxiliaryOfAlgebraicallyClosed k A
  obtain ⟨P, ⟨hP⟩⟩ := exists_object_with_nonempty_auxiliary (FGModuleCat.{u} A)
  haveI := hP
  exact ⟨P, nonempty_fgModuleEquivalence (k := k) (FGModuleCat.{u} A) P⟩

end

end RepresentationTheory.FGModuleCat.Finite
