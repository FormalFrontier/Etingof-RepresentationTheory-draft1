/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Homological.TensorActionComparison
import RepresentationTheory.HomologicalAlgebra.SymmetricAlgebra.ProjectiveDimension
import RepresentationTheory.Alignment.Attribute

open CategoryTheory Limits TensorProduct MonoidalCategory

universe u
namespace RepresentationTheory.Auxiliary.TensorResolution

private theorem quasiIso_comp_iso
    {C : Type u} [Category C] [Abelian C] {K L M : ChainComplex C ℕ}
    (φ : K ⟶ L) [QuasiIso φ] (e : L ≅ M) : QuasiIso (φ ≫ e.hom) := by
  infer_instance

private theorem quasiIso_comp_explicit
    {C : Type u} [Category C] [Abelian C] {K L M : ChainComplex C ℕ}
    (φ : K ⟶ L) (φ' : L ⟶ M) (hφ : QuasiIso φ) (hφ' : QuasiIso φ') :
    QuasiIso (φ ≫ φ') := by
  letI : QuasiIso φ := hφ
  letI : QuasiIso φ' := hφ'
  infer_instance

private theorem quasiIso_of_comp_right_explicit
    {C : Type u} [Category C] [Abelian C] {K L M : ChainComplex C ℕ}
    (φ : K ⟶ L) (φ' : L ⟶ M) (hφ' : QuasiIso φ')
    (hcomp : QuasiIso (φ ≫ φ')) : QuasiIso φ := by
  letI : QuasiIso φ' := hφ'
  letI : QuasiIso (φ ≫ φ') := hcomp
  exact quasiIso_of_comp_right φ φ'

variable (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V]

/-- Defines an auxiliary functor between the displayed module categories. -/
noncomputable abbrev Auxiliary.baseChangeFunctor :
    ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ⥤ ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) :=
  ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight.toRingHom)

/-- Defines an auxiliary family of module objects indexed by natural numbers. -/
noncomputable abbrev Auxiliary.componentModule (i : ℕ) : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) :=
  (Auxiliary.baseChangeFunctor k V).obj
    (@ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.GradedTensorObject k V i) _
      (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.alternateGradedTensorModule k V i))

/-- Relates scalar multiplication on the displayed auxiliary component module to multiplication in its argument. -/
theorem Auxiliary.componentModule_smul (i : ℕ) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
    (q : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) :
    a • (show Auxiliary.componentModule k V i from
      RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.gradedAct k V i q t) =
      RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.gradedAct k V i q (a * t) := by
  change (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.gradedTensorModule k V i).toSMul.smul
      (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.selfAlgEquiv k V (Algebra.TensorProduct.includeRight a))
      (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.gradedAct k V i q t) = _
  rw [show RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.selfAlgEquiv k V (Algebra.TensorProduct.includeRight a) =
      Algebra.TensorProduct.includeRight a by
        simp [RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.selfAlgEquiv, RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.selfAlgHom]]
  simpa [Algebra.TensorProduct.includeRight_apply] using
    RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.smul_gradedAct k V i 1 a q t

/-- Defines the displayed action on the auxiliary component module. -/
noncomputable def Auxiliary.componentModuleAction (i : ℕ) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
    (z : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.GradedTensorObject k V i) : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.GradedTensorObject k V i :=
  show Auxiliary.componentModule k V i from
    a • (show Auxiliary.componentModule k V i from z)

/-- The auxiliary component-module action sends zero to zero. -/
@[simp] theorem Auxiliary.componentModuleAction_zero (i : ℕ) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) :
    Auxiliary.componentModuleAction k V i a 0 = 0 := by
  change a • (0 : Auxiliary.componentModule k V i) = 0
  exact smul_zero a

/-- The auxiliary component-module action preserves addition. -/
theorem Auxiliary.componentModuleAction_add (i : ℕ) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
    (x y : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.GradedTensorObject k V i) :
    Auxiliary.componentModuleAction k V i a (x + y) =
      Auxiliary.componentModuleAction k V i a x +
        Auxiliary.componentModuleAction k V i a y := by
  change a • (show Auxiliary.componentModule k V i from x + y) = _
  exact (Auxiliary.componentModule k V i).isModule.smul_add a
    (show Auxiliary.componentModule k V i from x)
    (show Auxiliary.componentModule k V i from y)

/-- Describes the auxiliary component-module action on the displayed product. -/
@[simp] theorem Auxiliary.componentModuleAction_apply (i : ℕ) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
    (q : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) :
    Auxiliary.componentModuleAction k V i a
        (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.gradedAct k V i q t) =
      RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.gradedAct k V i q (a * t) :=
  Auxiliary.componentModule_smul k V i a q t

/-- Gives a linear equivalence from an auxiliary component module to a tensor product. -/
noncomputable def Auxiliary.componentModuleLinearEquiv (i : ℕ) :
    Auxiliary.componentModule k V i ≃ₗ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V]
      (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) where
  toFun := TensorProduct.comm k (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
  invFun := (TensorProduct.comm k (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)).symm
  left_inv := (TensorProduct.comm k (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)).left_inv
  right_inv := (TensorProduct.comm k (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)).right_inv
  map_add' := (TensorProduct.comm k (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)).map_add
  map_smul' := by
    intro a z
    change (TensorProduct.comm k (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
        (Auxiliary.componentModuleAction k V i a z) =
      a • (TensorProduct.comm k (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        rw [Auxiliary.componentModuleAction_add, map_add, hx, hy, map_add, smul_add]
    | tmul q t =>
        change (TensorProduct.comm k (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
            (Auxiliary.componentModuleAction k V i a
              (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.gradedAct k V i q t)) = _
        rw [Auxiliary.componentModuleAction_apply]
        rfl

/-- Each displayed auxiliary component module is free. -/
theorem Auxiliary.componentModule_free (i : ℕ) :
    Module.Free (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (Auxiliary.componentModule k V i) := by
  letI : Module.Free k (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) := inferInstance
  letI : Module.Free (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) := inferInstance
  exact Module.Free.of_equiv (Auxiliary.componentModuleLinearEquiv k V i).symm

/-- Evaluates the auxiliary component linear equivalence on the displayed element. -/
@[simp] theorem Auxiliary.componentModuleLinearEquiv_apply (i : ℕ)
    (s t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (x : ⋀[k]^i V) :
    Auxiliary.componentModuleLinearEquiv k V i
      (show Auxiliary.componentModule k V i from
        RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.gradedAct k V i (s ⊗ₜ[k] x) t) =
      t ⊗ₜ[k] (s ⊗ₜ[k] x) := rfl

/-- Provides an isomorphism from a mapped resolution component to an auxiliary component. -/
noncomputable def Auxiliary.mappedResolutionComponentIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (i : ℕ) :
    (((Auxiliary.baseChangeFunctor k V).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).complex).X i ≅
      Auxiliary.componentModule k V i :=
  (Auxiliary.baseChangeFunctor k V).mapIso (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolutionTermIso k V b i)

/-- The displayed mapped resolution component is free. -/
theorem Auxiliary.mappedResolutionComponent_free
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (i : ℕ) :
    Module.Free (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
      ((((Auxiliary.baseChangeFunctor k V).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).complex).X i) := by
  letI : Module.Free (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (Auxiliary.componentModule k V i) :=
    Auxiliary.componentModule_free k V i
  exact Module.Free.of_equiv
    (Auxiliary.mappedResolutionComponentIso k V b i).symm.toLinearEquiv

/-- Defines an auxiliary distinguished module object. -/
noncomputable abbrev Auxiliary.distinguishedModule : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) :=
  (Auxiliary.baseChangeFunctor k V).obj
    (@ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.coefficientModule k V))

/-- Provides an isomorphism from the auxiliary distinguished module. -/
noncomputable def Auxiliary.distinguishedModuleIso :
    Auxiliary.distinguishedModule k V ≅ RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.SecondCoefficientModuleObject k V := by
  let e : Auxiliary.distinguishedModule k V ≃ₗ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.actOnCoefficient k V (Algebra.TensorProduct.includeRight a) (show RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V from x) =
          a * (show RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V from x)
        simpa [Algebra.TensorProduct.includeRight_apply] using
          RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.tmul_actOnCoefficient k V 1 a x }
  exact e.toModuleIso

/-- Constructs an auxiliary projective resolution from a displayed basis. -/
noncomputable def Auxiliary.basisProjectiveResolution
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    ProjectiveResolution (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.SecondCoefficientModuleObject k V) where
  complex := ((Auxiliary.baseChangeFunctor k V).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).complex
  projective i := by
    letI : Module.Free (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
        ((((Auxiliary.baseChangeFunctor k V).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
          (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).complex).X i) :=
      Auxiliary.mappedResolutionComponent_free k V b i
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _)
  π := ((Auxiliary.baseChangeFunctor k V).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).π ≫
    (HomologicalComplex.singleMapHomologicalComplex (Auxiliary.baseChangeFunctor k V)
      (ComplexShape.down ℕ) 0).hom.app _ ≫
    (ChainComplex.single₀ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))).map
      (Auxiliary.distinguishedModuleIso k V).hom
  quasiIso := by
    letI : (Auxiliary.baseChangeFunctor k V).PreservesHomology :=
      RepresentationTheory.Algebra.Homology.TensorResolution.restrictScalars_preservesHomology _
    let φ := ((Auxiliary.baseChangeFunctor k V).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).π
    let e₁ := (HomologicalComplex.singleMapHomologicalComplex (Auxiliary.baseChangeFunctor k V)
      (ComplexShape.down ℕ) 0).app
        (@ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.coefficientModule k V))
    let e₂ := (ChainComplex.single₀ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))).mapIso
      (Auxiliary.distinguishedModuleIso k V)
    haveI : QuasiIso φ := inferInstance
    haveI hφe₁ : QuasiIso (φ ≫ e₁.hom) := quasiIso_comp_iso φ e₁
    change QuasiIso (φ ≫ e₁.hom ≫ e₂.hom)
    exact quasiIso_comp_iso (φ ≫ e₁.hom) e₂



/-- Defines a second displayed homomorphism between the auxiliary algebraic structures. -/
noncomputable abbrev Auxiliary.algebraToRingHomAux : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V →+* RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V :=
  (Algebra.TensorProduct.includeRight (R := k) (A := RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (B := RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)).toRingHom

/-- Defines the displayed homomorphism between the auxiliary algebraic structures. -/
noncomputable abbrev Auxiliary.algebraToRingHom : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V →+* RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V :=
  (Algebra.TensorProduct.includeLeft (R := k) (S := k)
    (A := RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (B := RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)).toRingHom

/-- Provides the displayed module structure on the auxiliary tensor product. -/
@[reducible] noncomputable def Auxiliary.tensorModule (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    (X : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)) :
    Module (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) ((Auxiliary.baseChangeFunctor k V).obj X ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) := by
  letI : Module (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ((Auxiliary.baseChangeFunctor k V).obj X) := X.isModule
  letI : SMulCommClass (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ((Auxiliary.baseChangeFunctor k V).obj X) := by
    constructor
    intro a r x
    simp only [ModuleCat.restrictScalars.smul_def]
    exact smul_comm (Auxiliary.algebraToRingHomAux k V a) r (show X from x)
  letI : Module (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ((Auxiliary.baseChangeFunctor k V).obj X ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) :=
    TensorProduct.leftModule
  exact Module.compHom _ (Auxiliary.algebraToRingHom k V)

/-- Defines the object part of an auxiliary tensor construction. -/
noncomputable def Auxiliary.tensorFunctorObj (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    (X : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)) : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) :=
  @ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _
    ((Auxiliary.baseChangeFunctor k V).obj X ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) _
      (Auxiliary.tensorModule k V M X)

/-- Defines the displayed action on the auxiliary tensor product. -/
noncomputable def Auxiliary.tensorAction (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    (X : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
    (z : (Auxiliary.baseChangeFunctor k V).obj X ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) :
    (Auxiliary.baseChangeFunctor k V).obj X ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M :=
  show Auxiliary.tensorFunctorObj k V M X from
    a • (show Auxiliary.tensorFunctorObj k V M X from z)

/-- The auxiliary tensor action sends zero to zero. -/
@[simp] theorem Auxiliary.tensorAction_zero (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    (X : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) :
    Auxiliary.tensorAction k V M X a 0 = 0 := by
  change a • (0 : Auxiliary.tensorFunctorObj k V M X) = 0
  exact (Auxiliary.tensorFunctorObj k V M X).isModule.smul_zero a

/-- The auxiliary tensor action preserves addition. -/
theorem Auxiliary.tensorAction_add (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    (X : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
    (x y : (Auxiliary.baseChangeFunctor k V).obj X ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) :
    Auxiliary.tensorAction k V M X a (x + y) =
      Auxiliary.tensorAction k V M X a x + Auxiliary.tensorAction k V M X a y := by
  change a • (show Auxiliary.tensorFunctorObj k V M X from x + y) = _
  exact (Auxiliary.tensorFunctorObj k V M X).isModule.smul_add a x y

/-- Evaluates the auxiliary tensor action on a pure tensor. -/
@[simp] theorem Auxiliary.tensorAction_tmul (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    (X : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
    (x : (Auxiliary.baseChangeFunctor k V).obj X) (m : M) :
    Auxiliary.tensorAction k V M X a (x ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m) =
      (show (Auxiliary.baseChangeFunctor k V).obj X from
        (Auxiliary.algebraToRingHom k V a) • (show X from x)) ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m := by
  rfl

/-- Defines the linear map induced by a morphism under the auxiliary construction. -/
noncomputable def Auxiliary.tensorFunctorMapLinear (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    {X Y : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)} (f : X ⟶ Y) :
    Auxiliary.tensorFunctorObj k V M X →ₗ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] Auxiliary.tensorFunctorObj k V M Y := by
  let g : ((Auxiliary.baseChangeFunctor k V).obj X ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) →ₗ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V]
      ((Auxiliary.baseChangeFunctor k V).obj Y ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) :=
    TensorProduct.map ((Auxiliary.baseChangeFunctor k V).map f).hom LinearMap.id
  exact
  { toFun := g
    map_add' := g.map_add
    map_smul' := by
      intro a z
      change g (Auxiliary.tensorAction k V M X a z) =
        Auxiliary.tensorAction k V M Y a (g z)
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          rw [Auxiliary.tensorAction_add, map_add, hx, hy, map_add,
            Auxiliary.tensorAction_add]
      | tmul x m =>
          rw [Auxiliary.tensorAction_tmul, TensorProduct.map_tmul,
            TensorProduct.map_tmul, Auxiliary.tensorAction_tmul]
          congr 1
          exact f.hom.map_smul (Auxiliary.algebraToRingHom k V a) (show X from x) }

/-- Defines the module morphism induced by a morphism under the auxiliary construction. -/
noncomputable def Auxiliary.tensorFunctorMap (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    {X Y : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)} (f : X ⟶ Y) :
    Auxiliary.tensorFunctorObj k V M X ⟶ Auxiliary.tensorFunctorObj k V M Y :=
  (ModuleCat.hom_bijective.surjective (Auxiliary.tensorFunctorMapLinear k V M f)).choose

/-- Identifies the underlying linear map of the induced module morphism. -/
@[simp] theorem Auxiliary.tensorFunctorMap_hom (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    {X Y : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)} (f : X ⟶ Y) :
    (Auxiliary.tensorFunctorMap k V M f).hom = Auxiliary.tensorFunctorMapLinear k V M f :=
  (ModuleCat.hom_bijective.surjective (Auxiliary.tensorFunctorMapLinear k V M f)).choose_spec

/-- Evaluates the induced module morphism on a pure tensor. -/
@[simp] theorem Auxiliary.tensorFunctorMap_tmul (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    {X Y : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)} (f : X ⟶ Y)
    (x : (Auxiliary.baseChangeFunctor k V).obj X) (m : M) :
    (Auxiliary.tensorFunctorMap k V M f).hom
        (show Auxiliary.tensorFunctorObj k V M X from x ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m) =
      (show (Auxiliary.baseChangeFunctor k V).obj Y from f.hom x) ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m := by
  rw [Auxiliary.tensorFunctorMap_hom]
  rfl

/-- Defines the displayed tensor-product map induced by a morphism. -/
noncomputable def Auxiliary.tensorFunctorTensorMap (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    {X Y : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)} (f : X ⟶ Y)
    (z : (Auxiliary.baseChangeFunctor k V).obj X ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) :
    (Auxiliary.baseChangeFunctor k V).obj Y ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M :=
  show Auxiliary.tensorFunctorObj k V M Y from
    (Auxiliary.tensorFunctorMap k V M f).hom (show Auxiliary.tensorFunctorObj k V M X from z)

/-- The displayed tensor-product map sends zero to zero. -/
@[simp] theorem Auxiliary.tensorFunctorTensorMap_zero (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    {X Y : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)} (f : X ⟶ Y) :
    Auxiliary.tensorFunctorTensorMap k V M f 0 = 0 := by
  exact map_zero (Auxiliary.tensorFunctorMap k V M f).hom

/-- The displayed tensor-product map preserves addition. -/
theorem Auxiliary.tensorFunctorTensorMap_add (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    {X Y : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)} (f : X ⟶ Y)
    (x y : (Auxiliary.baseChangeFunctor k V).obj X ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) :
    Auxiliary.tensorFunctorTensorMap k V M f (x + y) =
      Auxiliary.tensorFunctorTensorMap k V M f x + Auxiliary.tensorFunctorTensorMap k V M f y := by
  exact map_add (Auxiliary.tensorFunctorMap k V M f).hom x y

/-- Evaluates the displayed tensor-product map on a pure tensor. -/
@[simp] theorem Auxiliary.tensorFunctorTensorMap_tmul (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    {X Y : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)} (f : X ⟶ Y)
    (x : (Auxiliary.baseChangeFunctor k V).obj X) (m : M) :
    Auxiliary.tensorFunctorTensorMap k V M f (x ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m) =
      (show (Auxiliary.baseChangeFunctor k V).obj Y from f.hom x) ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m := by
  exact Auxiliary.tensorFunctorMap_tmul k V M f x m

/-- Defines an auxiliary functor parameterized by a module object. -/
noncomputable def Auxiliary.tensorFunctor (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) :
    ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ⥤ ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) where
  obj := Auxiliary.tensorFunctorObj k V M
  map := Auxiliary.tensorFunctorMap k V M
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change Auxiliary.tensorFunctorTensorMap k V M (𝟙 X) z = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [Auxiliary.tensorFunctorTensorMap_add, hx, hy]
    | tmul x m => rw [Auxiliary.tensorFunctorTensorMap_tmul]; rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change Auxiliary.tensorFunctorTensorMap k V M (f ≫ g) z =
      Auxiliary.tensorFunctorTensorMap k V M g (Auxiliary.tensorFunctorTensorMap k V M f z)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [Auxiliary.tensorFunctorTensorMap_add, Auxiliary.tensorFunctorTensorMap_add,
        Auxiliary.tensorFunctorTensorMap_add, hx, hy]
    | tmul x m => rw [Auxiliary.tensorFunctorTensorMap_tmul, Auxiliary.tensorFunctorTensorMap_tmul,
        Auxiliary.tensorFunctorTensorMap_tmul]; rfl

/-- The auxiliary tensor functor is additive. -/
instance Auxiliary.tensorFunctor_additive (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) : (Auxiliary.tensorFunctor k V M).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change Auxiliary.tensorFunctorTensorMap k V M (f + g) z =
      Auxiliary.tensorFunctorTensorMap k V M f z + Auxiliary.tensorFunctorTensorMap k V M g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [Auxiliary.tensorFunctorTensorMap_add, Auxiliary.tensorFunctorTensorMap_add,
        Auxiliary.tensorFunctorTensorMap_add, hx, hy]; abel
    | tmul x m =>
        rw [Auxiliary.tensorFunctorTensorMap_tmul, Auxiliary.tensorFunctorTensorMap_tmul,
          Auxiliary.tensorFunctorTensorMap_tmul]
        change (show (Auxiliary.baseChangeFunctor k V).obj Y from
            f.hom x + g.hom x) ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m = _
        exact TensorProduct.add_tmul _ _ _

/-- Provides the displayed module structure over the base field. -/
noncomputable local instance Auxiliary.moduleOverField (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) : Module k M :=
  Module.compHom M (algebraMap k (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))

/-- The displayed module structure forms a scalar tower over the base field. -/
local instance Auxiliary.scalarTower (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) :
    IsScalarTower k (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) M where
  smul_assoc r s m := by
    change ((algebraMap k (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) r) * s) • m =
      (algebraMap k (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) r) • (s • m)
    rw [mul_smul]

/-- Defines an additive equivalence from an auxiliary component tensor product. -/
noncomputable def Auxiliary.componentTensorAddEquiv
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ) :
    (Auxiliary.componentModule k V i ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) ≃+
      (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) :=
  (TensorProduct.congr (Auxiliary.componentModuleLinearEquiv k V i)
      (LinearEquiv.refl (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) M)).toAddEquiv.trans <|
    (TensorProduct.comm (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) M).toAddEquiv.trans <|
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
        M (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)).toAddEquiv.trans <|
        (TensorProduct.comm k M (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)).toAddEquiv.trans <|
          (TensorProduct.assoc k (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (⋀[k]^i V) M).toAddEquiv

/-- Evaluates the component tensor additive equivalence on a displayed pure tensor. -/
@[simp] theorem Auxiliary.componentTensorAddEquiv_tmul
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ)
    (s t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (x : ⋀[k]^i V) (m : M) :
    Auxiliary.componentTensorAddEquiv k V M i
      ((show Auxiliary.componentModule k V i from
          RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.gradedAct k V i (s ⊗ₜ[k] x) t) ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m) =
      s ⊗ₜ[k] (x ⊗ₜ[k] (t • m)) := by
  simp [Auxiliary.componentTensorAddEquiv]

/-- Defines an auxiliary family of modules indexed by natural numbers. -/
noncomputable abbrev Auxiliary.gradedModule (i : ℕ) : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) :=
  ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.AuxiliaryGradedObject k V i)

/-- Defines the displayed action on the auxiliary graded module. -/
noncomputable def Auxiliary.gradedModuleAction (i : ℕ) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
    (z : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.AuxiliaryGradedObject k V i) : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.AuxiliaryGradedObject k V i :=
  show (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.gradedModule k V i) from
    a • (show (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.gradedModule k V i) from z)

/-- The auxiliary graded-module action sends zero to zero. -/
@[simp] theorem Auxiliary.gradedModuleAction_zero (i : ℕ) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) :
    Auxiliary.gradedModuleAction k V i a 0 = 0 := by
  change a • (0 : (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.gradedModule k V i)) = 0
  exact smul_zero a

/-- The auxiliary graded-module action preserves addition. -/
theorem Auxiliary.gradedModuleAction_add (i : ℕ) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
    (x y : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.AuxiliaryGradedObject k V i) :
    Auxiliary.gradedModuleAction k V i a (x + y) =
      Auxiliary.gradedModuleAction k V i a x + Auxiliary.gradedModuleAction k V i a y := by
  change a • (show (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.gradedModule k V i) from
    x + y) = _
  exact ((Auxiliary.baseChangeFunctor k V).obj (Auxiliary.gradedModule k V i)).isModule.smul_add a x y

/-- Describes the auxiliary graded-module action on the displayed pure tensor. -/
@[simp] theorem Auxiliary.gradedModuleAction_tensor (i : ℕ) (a s t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
    (x : ⋀[k]^i V) :
    Auxiliary.gradedModuleAction k V i a
        (((s ⊗ₜ[k] t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ⊗ₜ[k] x : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.AuxiliaryGradedObject k V i)) =
      ((s ⊗ₜ[k] (a * t) : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ⊗ₜ[k] x) := by
  change ((Auxiliary.algebraToRingHomAux k V a) * (s ⊗ₜ[k] t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)) ⊗ₜ[k] x = _
  simp [Auxiliary.algebraToRingHomAux, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]


/-- Gives a linear equivalence from the displayed graded module to a tensor product. -/
noncomputable def Auxiliary.gradedModuleLinearEquiv (i : ℕ) :
    (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.gradedModule k V i) ≃ₗ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V]
      (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) := by
  let eₖ : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.AuxiliaryGradedObject k V i ≃ₗ[k] RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i :=
    TensorProduct.congr (Algebra.TensorProduct.comm k (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)).toLinearEquiv
        (LinearEquiv.refl k (⋀[k]^i V)) ≪≫ₗ
      TensorProduct.assoc k (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (⋀[k]^i V)
  exact
  { toFun := eₖ
    invFun := eₖ.symm
    left_inv := eₖ.left_inv
    right_inv := eₖ.right_inv
    map_add' := eₖ.map_add
    map_smul' := by
      intro a z
      change eₖ (Auxiliary.gradedModuleAction k V i a z) = a • eₖ z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          rw [Auxiliary.gradedModuleAction_add, map_add, hx, hy, map_add, smul_add]
      | tmul e x =>
          induction e using TensorProduct.induction_on with
          | zero => simp
          | add p q hp hq =>
              rw [add_tmul, Auxiliary.gradedModuleAction_add, map_add, hp, hq, map_add, smul_add]
          | tmul s t =>
              rw [Auxiliary.gradedModuleAction_tensor]
              simp only [Algebra.TensorProduct.comm_toLinearEquiv, LinearEquiv.trans_apply,
                congr_tmul, comm_tmul, LinearEquiv.refl_apply, assoc_tmul, eₖ]
              rw [TensorProduct.smul_tmul', smul_eq_mul]
  }

/-- Defines an additive equivalence between the displayed graded tensor products. -/
noncomputable def Auxiliary.gradedTensorAddEquiv
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ) :
    (((Auxiliary.baseChangeFunctor k V).obj (Auxiliary.gradedModule k V i)) ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) ≃+
      (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) :=
  (TensorProduct.congr (Auxiliary.gradedModuleLinearEquiv k V i)
      (LinearEquiv.refl (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) M)).toAddEquiv.trans <|
    (TensorProduct.comm (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i) M).toAddEquiv.trans <|
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
        M (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)).toAddEquiv.trans <|
        (TensorProduct.comm k M (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i)).toAddEquiv.trans <|
          (TensorProduct.assoc k (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (⋀[k]^i V) M).toAddEquiv

/-- Evaluates the graded tensor additive equivalence on a pure tensor. -/
@[simp] theorem Auxiliary.gradedTensorAddEquiv_tmul
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ)
    (s t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (x : ⋀[k]^i V) (m : M) :
    Auxiliary.gradedTensorAddEquiv k V M i
      ((((s ⊗ₜ[k] t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ⊗ₜ[k] x : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.AuxiliaryGradedObject k V i) ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m)) =
      s ⊗ₜ[k] (x ⊗ₜ[k] (t • m)) := by
  simp [Auxiliary.gradedTensorAddEquiv, Auxiliary.gradedModuleLinearEquiv]

/-- Defines the displayed map from a graded component and a module element to a tensor product. -/
noncomputable def Auxiliary.gradedTensorMap
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ)
    (q : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.AuxiliaryGradedObject k V i) (m : M) :
    (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.gradedModule k V i) ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M :=
  (show (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.gradedModule k V i) from q) ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m

/-- The displayed graded tensor map vanishes at zero in its graded-component argument. -/
@[simp] theorem Auxiliary.gradedTensorMap_zero
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ) (m : M) :
    Auxiliary.gradedTensorMap k V M i 0 m = 0 := by
  change (0 : (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.gradedModule k V i))
    ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m = 0
  exact TensorProduct.zero_tmul
    ((Auxiliary.baseChangeFunctor k V).obj (Auxiliary.gradedModule k V i)) m

/-- The displayed graded tensor map is additive in its graded-component argument. -/
theorem Auxiliary.gradedTensorMap_add
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ)
    (p q : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.AuxiliaryGradedObject k V i) (m : M) :
    Auxiliary.gradedTensorMap k V M i (p + q) m =
      Auxiliary.gradedTensorMap k V M i p m +
        Auxiliary.gradedTensorMap k V M i q m := by
  exact TensorProduct.add_tmul _ _ _

/-- Relates the tensor action to the displayed graded tensor map. -/
theorem Auxiliary.tensorAction_gradedTensorMap
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ)
    (a s t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (x : ⋀[k]^i V) (m : M) :
    Auxiliary.tensorAction k V M (Auxiliary.gradedModule k V i) a
        (Auxiliary.gradedTensorMap k V M i
          ((s ⊗ₜ[k] t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ⊗ₜ[k] x) m) =
      Auxiliary.gradedTensorMap k V M i
        (((a * s) ⊗ₜ[k] t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ⊗ₜ[k] x) m := by
  unfold Auxiliary.gradedTensorMap
  rw [Auxiliary.tensorAction_tmul]
  congr 1
  change ((Auxiliary.algebraToRingHom k V a) * (s ⊗ₜ[k] t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V)) ⊗ₜ[k] x = _
  simp [Auxiliary.algebraToRingHom, Algebra.TensorProduct.tmul_mul_tmul]



/-- Gives a linear equivalence between the displayed tensor modules. -/
noncomputable def Auxiliary.gradedTensorLinearEquiv
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ) :
    Auxiliary.tensorFunctorObj k V M (Auxiliary.gradedModule k V i) ≃ₗ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V]
      (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) := by
  let e := Auxiliary.gradedTensorAddEquiv k V M i
  exact
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := by
      intro a z
      change e (Auxiliary.tensorAction k V M (Auxiliary.gradedModule k V i) a z) =
        a • e z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add p q hp hq =>
          rw [Auxiliary.tensorAction_add, map_add, hp, hq, map_add, smul_add]
      | tmul q m =>
          change e (Auxiliary.tensorAction k V M (Auxiliary.gradedModule k V i) a
            (Auxiliary.gradedTensorMap k V M i q m)) =
              a • e (Auxiliary.gradedTensorMap k V M i q m)
          induction q using TensorProduct.induction_on with
          | zero =>
              rw [Auxiliary.gradedTensorMap_zero, Auxiliary.tensorAction_zero,
                map_zero]
              exact smul_zero a
          | add p q hp hq =>
              rw [Auxiliary.gradedTensorMap_add, Auxiliary.tensorAction_add,
                map_add, hp, hq, map_add, smul_add]
          | tmul r x =>
              induction r using TensorProduct.induction_on with
              | zero =>
                  rw [TensorProduct.zero_tmul, Auxiliary.gradedTensorMap_zero,
                    Auxiliary.tensorAction_zero, map_zero]
                  exact smul_zero a
              | add s t hs ht =>
                  rw [TensorProduct.add_tmul, Auxiliary.gradedTensorMap_add,
                    Auxiliary.tensorAction_add, map_add, hs, ht, map_add, smul_add]
              | tmul s t =>
                  rw [Auxiliary.tensorAction_gradedTensorMap]
                  change Auxiliary.gradedTensorAddEquiv k V M i
                      (Auxiliary.gradedTensorMap k V M i
                        (((a * s) ⊗ₜ[k] t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ⊗ₜ[k] x) m) =
                    a • Auxiliary.gradedTensorAddEquiv k V M i
                      (Auxiliary.gradedTensorMap k V M i
                        ((s ⊗ₜ[k] t : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ⊗ₜ[k] x) m)
                  unfold Auxiliary.gradedTensorMap
                  rw [
                    Auxiliary.gradedTensorAddEquiv_tmul,
                    Auxiliary.gradedTensorAddEquiv_tmul,
                    TensorProduct.smul_tmul', smul_eq_mul] }



/-- Provides an isomorphism from a mapped resolution component to a displayed tensor product. -/
noncomputable def Auxiliary.basisTensorResolutionComponentIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ) :
    (((Auxiliary.tensorFunctor k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).complex).X i ≅
      ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) :=
  (Auxiliary.tensorFunctor k V M).mapIso
      (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolutionTermIso k V b i) ≪≫
    (Auxiliary.tensorFunctor k V M).mapIso
      (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.gradedAuxiliaryIso k V i) ≪≫
    (Auxiliary.gradedTensorLinearEquiv k V M i).toModuleIso



/-- The displayed tensor resolution component is free. -/
theorem Auxiliary.basisTensorResolutionComponent_free
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ) :
    Module.Free (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
      ((((Auxiliary.tensorFunctor k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).complex).X i) := by
  letI : Module.Free k ((⋀[k]^i V) ⊗[k] M) := inferInstance
  letI : Module.Free (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) := inferInstance
  exact Module.Free.of_equiv
    (Auxiliary.basisTensorResolutionComponentIso k V b M i).symm.toLinearEquiv

/-- The displayed tensor resolution component is projective. -/
theorem Auxiliary.basisTensorResolutionComponent_projective
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ) :
    Projective
      ((((Auxiliary.tensorFunctor k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).complex).X i) := by
  letI := Auxiliary.basisTensorResolutionComponent_free k V b M i
  exact ModuleCat.projective_of_free (Module.Free.chooseBasis (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _)



/-- The displayed tensor resolution component is zero above the finite rank. -/
theorem Auxiliary.basisTensorResolutionComponent_isZeroAbove
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ)
    (hi : Module.finrank k V < i) :
    IsZero
      ((((Auxiliary.tensorFunctor k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).complex).X i) := by
  letI : Module.Finite k V := Module.Finite.of_basis b
  have hfin : Module.finrank k (⋀[k]^i V) = 0 := by
    rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt hi]
  have hext : ∀ x : ⋀[k]^i V, x = 0 :=
    finrank_zero_iff_forall_zero.mp hfin
  have hinner : ∀ z : (⋀[k]^i V) ⊗[k] M, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add x y hx hy => rw [hx, hy, add_zero]
    | tmul x m => rw [hext x, TensorProduct.zero_tmul]
  have houter : ∀ z : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] ((⋀[k]^i V) ⊗[k] M), z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add x y hx hy => rw [hx, hy, add_zero]
    | tmul s x => rw [hinner x, TensorProduct.tmul_zero]
  letI : Subsingleton (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V ⊗[k] ((⋀[k]^i V) ⊗[k] M)) :=
    ⟨fun x y => (houter x).trans (houter y).symm⟩
  exact (Auxiliary.basisTensorResolutionComponentIso k V b M i).isZero_iff.mpr
    (ModuleCat.isZero_of_subsingleton _)

/-- Defines an auxiliary distinguished object in the displayed module category. -/
noncomputable abbrev Auxiliary.distinguishedObject : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) :=
  @ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.coefficientModule k V)



/-- Defines an additive equivalence from the distinguished tensor product to the module. -/
noncomputable def Auxiliary.distinguishedTensorAddEquiv
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) :
    ((Auxiliary.baseChangeFunctor k V).obj (Auxiliary.distinguishedObject k V) ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M) ≃+ M :=
  (TensorProduct.congr (Auxiliary.distinguishedModuleIso k V).toLinearEquiv
      (LinearEquiv.refl (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) M)).toAddEquiv.trans
    (TensorProduct.lid (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) M).toAddEquiv

/-- The forward map of the distinguished-module isomorphism acts as the identity. -/
@[simp] theorem Auxiliary.distinguishedModuleIso_hom
    (s : Auxiliary.distinguishedModule k V) :
    (Auxiliary.distinguishedModuleIso k V).hom.hom s = (show RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V from s) := by
  rfl

/-- Evaluates the distinguished tensor additive equivalence on a pure tensor. -/
@[simp] theorem Auxiliary.distinguishedTensorAddEquiv_tmul
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    (s : (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.distinguishedObject k V)) (m : M) :
    Auxiliary.distinguishedTensorAddEquiv k V M
      (s ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m) = (show RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V from s) • m := by
  change (Auxiliary.distinguishedModuleIso k V).hom.hom
      (show Auxiliary.distinguishedModule k V from s) • m =
    (show RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V from s) • m
  rw [Auxiliary.distinguishedModuleIso_hom]

/-- Defines the displayed tensor-valued map from the distinguished object. -/
noncomputable def Auxiliary.distinguishedTensorMap
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))
    (s : (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.distinguishedObject k V)) (m : M) :
    (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.distinguishedObject k V) ⊗[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M :=
  s ⊗ₜ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] m

/-- Relates the tensor action to the distinguished tensor map. -/
theorem Auxiliary.tensorAction_distinguishedTensorMap
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (a : RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)
    (s : (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.distinguishedObject k V)) (m : M) :
    Auxiliary.tensorAction k V M (Auxiliary.distinguishedObject k V) a
        (Auxiliary.distinguishedTensorMap k V M s m) =
      Auxiliary.distinguishedTensorMap k V M
        (show (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.distinguishedObject k V) from
          a * (show RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V from s)) m := by
  unfold Auxiliary.distinguishedTensorMap
  rw [Auxiliary.tensorAction_tmul]
  congr 1
  change RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.actOnCoefficient k V (Auxiliary.algebraToRingHom k V a) (show RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V from s) =
    a * (show RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V from s)
  simpa [Auxiliary.algebraToRingHom, Algebra.TensorProduct.includeLeft_apply] using
    RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.tmul_actOnCoefficient k V a 1 (show RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V from s)



/-- Provides an isomorphism from the distinguished object under the auxiliary functor. -/
noncomputable def Auxiliary.tensorFunctorObj_distinguishedIso
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) :
    (Auxiliary.tensorFunctor k V M).obj (Auxiliary.distinguishedObject k V) ≅ M := by
  let e := Auxiliary.distinguishedTensorAddEquiv k V M
  let eₗ : Auxiliary.tensorFunctorObj k V M (Auxiliary.distinguishedObject k V) ≃ₗ[RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V] M :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro a z
        change e (Auxiliary.tensorAction k V M (Auxiliary.distinguishedObject k V) a z) =
          a • e z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
            rw [Auxiliary.tensorAction_add, map_add, hx, hy, map_add, smul_add]
        | tmul s m =>
            change e (Auxiliary.tensorAction k V M (Auxiliary.distinguishedObject k V) a
                (Auxiliary.distinguishedTensorMap k V M s m)) =
              a • e (Auxiliary.distinguishedTensorMap k V M s m)
            rw [Auxiliary.tensorAction_distinguishedTensorMap]
            change Auxiliary.distinguishedTensorAddEquiv k V M
                (Auxiliary.distinguishedTensorMap k V M
                  (show (Auxiliary.baseChangeFunctor k V).obj (Auxiliary.distinguishedObject k V) from
                    a * (show RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V from s)) m) =
              a • Auxiliary.distinguishedTensorAddEquiv k V M
                (Auxiliary.distinguishedTensorMap k V M s m)
            unfold Auxiliary.distinguishedTensorMap
            rw [Auxiliary.distinguishedTensorAddEquiv_tmul,
              Auxiliary.distinguishedTensorAddEquiv_tmul, mul_smul] }
  exact eₗ.toModuleIso

/-- Defines a second displayed auxiliary functor parameterized by a module object. -/
noncomputable abbrev Auxiliary.tensorFunctorAux
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) :
    ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) ⥤ ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) :=
  Auxiliary.baseChangeFunctor k V ⋙ MonoidalCategory.tensorRight M



/-- Provides an isomorphism between the displayed functors after forgetting structure. -/
noncomputable def Auxiliary.forgetFunctorIso
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) :
    Auxiliary.tensorFunctor k V M ⋙
        forget₂ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) AddCommGrpCat.{u} ≅
      Auxiliary.tensorFunctorAux k V M ⋙
        forget₂ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    simp only [Functor.comp_map, Iso.refl_hom]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change Auxiliary.tensorFunctorTensorMap k V M f z =
      (((Auxiliary.baseChangeFunctor k V).map f) ▷ M).hom z
    induction z using TensorProduct.induction_on with
    | zero => rw [Auxiliary.tensorFunctorTensorMap_zero, map_zero]
    | add x y hx hy =>
        rw [Auxiliary.tensorFunctorTensorMap_add, map_add, hx, hy]
    | tmul x m =>
        rw [Auxiliary.tensorFunctorTensorMap_tmul,
          ModuleCat.MonoidalCategory.whiskerRight_apply]
        rfl)

/-- Shows that the second auxiliary functor sends the indicated resolution morphism to a quasi-isomorphism. -/
theorem Auxiliary.tensorFunctorAux_mapQuasiIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) :
    QuasiIso
      (((Auxiliary.tensorFunctorAux k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).π) := by
  let P := RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b
  let Q := Auxiliary.basisProjectiveResolution k V b
  let R := Auxiliary.baseChangeFunctor k V
  let T := MonoidalCategory.tensorRight M
  let e := (HomologicalComplex.singleMapHomologicalComplex R
    (ComplexShape.down ℕ) 0).app
      (@ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.coefficientModule k V))
      ≪≫ (ChainComplex.single₀ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))).mapIso
        (Auxiliary.distinguishedModuleIso k V)
  let e' : (ProjectiveResolution.self (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.SecondCoefficientModuleObject k V)).complex ≅
      (R.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((ChainComplex.single₀ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V))).obj
          (@ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.coefficientModule k V))) := e.symm
  have hQ : Q.π = (Q.homotopyEquiv (ProjectiveResolution.self (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.SecondCoefficientModuleObject k V))).hom := by
    have h := ProjectiveResolution.homotopyEquiv_hom_π Q
      (ProjectiveResolution.self (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.SecondCoefficientModuleObject k V))
    change (Q.homotopyEquiv (ProjectiveResolution.self (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.SecondCoefficientModuleObject k V))).hom ≫
      𝟙 _ = Q.π at h
    rw [Category.comp_id] at h
    exact h.symm
  have hQ_def : Q.π =
      (R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫ e'.inv := by
    rfl
  let hraw := (Q.homotopyEquiv (ProjectiveResolution.self (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.SecondCoefficientModuleObject k V))).trans
    (HomotopyEquiv.ofIso e')
  have hraw_hom : hraw.hom =
      (R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π := by
    change (Q.homotopyEquiv (ProjectiveResolution.self (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.SecondCoefficientModuleObject k V))).hom ≫
      e'.hom = (R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π
    rw [← hQ, hQ_def]
    change (((R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫ e'.inv) ≫
      e'.hom) = (R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change QuasiIso
    ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((R.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π))
  rw [← hraw_hom]
  exact (T.mapHomotopyEquiv hraw).quasiIso_hom

/-- Shows that the displayed functor sends the indicated resolution morphism to a quasi-isomorphism. -/
theorem Auxiliary.tensorFunctor_mapQuasiIso
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) :
    QuasiIso
      (((Auxiliary.tensorFunctor k V M).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).π) := by
  let P := RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b
  let B := Auxiliary.tensorFunctor k V M
  let G := Auxiliary.tensorFunctorAux k V M
  let U := forget₂ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) AddCommGrpCat.{u}
  let η := NatIso.mapHomologicalComplex (Auxiliary.forgetFunctorIso k V M)
    (ComplexShape.down ℕ)
  let φB := (B.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π
  let φG := (G.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π
  let φU := (U.mapHomologicalComplex (ComplexShape.down ℕ)).map φB
  let φGU := (U.mapHomologicalComplex (ComplexShape.down ℕ)).map φG
  haveI hG : QuasiIso φG := Auxiliary.tensorFunctorAux_mapQuasiIso k V b M
  haveI hGU : QuasiIso φGU := inferInstance
  haveI hηP : QuasiIso (η.hom.app P.complex) := inferInstance
  haveI hηS : QuasiIso
      (η.hom.app ((ChainComplex.single₀ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V))).obj
        (@ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.coefficientModule k V)))) := inferInstance
  haveI hright : QuasiIso (η.hom.app P.complex ≫ φGU) :=
    quasiIso_comp_explicit _ _ hηP hGU
  have hnat : φU ≫
      η.hom.app ((ChainComplex.single₀ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V))).obj
        (@ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.coefficientModule k V))) =
      η.hom.app P.complex ≫ φGU := by
    exact NatTrans.mapHomologicalComplex_naturality
      (Auxiliary.forgetFunctorIso k V M).hom P.π
  haveI hcomp : QuasiIso
      (φU ≫ η.hom.app ((ChainComplex.single₀ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V))).obj
        (@ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.coefficientModule k V)))) :=
    hnat ▸ hright
  haveI hU : QuasiIso φU := quasiIso_of_comp_right_explicit φU
    (η.hom.app ((ChainComplex.single₀ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V))).obj
      (@ModuleCat.of (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.ActingAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V) _ (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.coefficientModule k V)))) hηS hcomp
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology φB U).mp hU




/-- Constructs an auxiliary projective resolution from a basis and a module object. -/
noncomputable def Auxiliary.basisTensorProjectiveResolution
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) : ProjectiveResolution M where
  complex := ((Auxiliary.tensorFunctor k V M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).complex
  projective i := Auxiliary.basisTensorResolutionComponent_projective k V b M i
  π := ((Auxiliary.tensorFunctor k V M).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).π ≫
    (HomologicalComplex.singleMapHomologicalComplex (Auxiliary.tensorFunctor k V M)
      (ComplexShape.down ℕ) 0).hom.app (Auxiliary.distinguishedObject k V) ≫
    (ChainComplex.single₀ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))).map
      (Auxiliary.tensorFunctorObj_distinguishedIso k V M).hom
  quasiIso := by
    let φ := ((Auxiliary.tensorFunctor k V M).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.auxiliaryProjectiveResolution k V b).π
    let e₁ := (HomologicalComplex.singleMapHomologicalComplex
      (Auxiliary.tensorFunctor k V M) (ComplexShape.down ℕ) 0).app
        (Auxiliary.distinguishedObject k V)
    let e₂ := (ChainComplex.single₀ (ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V))).mapIso
      (Auxiliary.tensorFunctorObj_distinguishedIso k V M)
    haveI : QuasiIso φ := Auxiliary.tensorFunctor_mapQuasiIso k V b M
    haveI : QuasiIso (φ ≫ e₁.hom) := quasiIso_comp_iso φ e₁
    change QuasiIso (φ ≫ e₁.hom ≫ e₂.hom)
    exact quasiIso_comp_iso (φ ≫ e₁.hom) e₂

/-- The auxiliary basis-dependent projective resolution is zero above the finite rank. -/
theorem Auxiliary.basisTensorProjectiveResolution_isZeroAbove
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ)
    (hi : Module.finrank k V < i) :
    IsZero ((Auxiliary.basisTensorProjectiveResolution k V b M).complex.X i) :=
  Auxiliary.basisTensorResolutionComponent_isZeroAbove k V b M i hi





/-- Constructs an auxiliary projective resolution for the displayed module. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
noncomputable def Auxiliary.projectiveResolution [FiniteDimensional k V]
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) : ProjectiveResolution M :=
  Auxiliary.basisTensorProjectiveResolution k V (Module.finBasis k V) M




/-- Shows that the displayed resolution has zero components above the finite rank. -/
@[source_ref "Chapter8/Problem8.2.10" (role := supporting)]
theorem Auxiliary.projectiveResolution_isZeroAbove [FiniteDimensional k V]
    (M : ModuleCat.{u} (RepresentationTheory.Algebra.Homological.TensorActionComparison.TensorActionComparison.CoefficientAlgebra k V)) (i : ℕ) (hi : Module.finrank k V < i) :
    IsZero ((Auxiliary.projectiveResolution k V M).complex.X i) :=
  Auxiliary.basisTensorProjectiveResolution_isZeroAbove k V
    (Module.finBasis k V) M i hi

end RepresentationTheory.Auxiliary.TensorResolution
