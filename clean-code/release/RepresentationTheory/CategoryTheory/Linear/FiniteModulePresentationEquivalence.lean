/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Map
import RepresentationTheory.Alignment.Attribute

/-!
# Finite-module presentation equivalence

This module constructs an explicit presentation functor from finite modules over an opposite
endomorphism algebra and proves that it is quasi-inverse to the associated module-valued functor.
-/


universe u v w

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence


set_option backward.isDefEq.respectTransparency false


section Copower

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [Linear k C]


/-- The object obtained from a chosen object and a finite-dimensional vector space by the available finite additive construction. -/
noncomputable def finiteCopower (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] : C :=
  ⨁ fun _ : Fin (Module.finrank k V) => P


/-- The linear map sending each vector to its canonical morphism from the chosen object into the finite copower. -/
noncomputable def finiteCopowerGenerator (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] :
    V →ₗ[k] (P ⟶ finiteCopower (k := k) P V) where
  toFun x := biproduct.lift fun i =>
    ((Module.finBasis k V).repr x i) • 𝟙 P
  map_add' x y := by
    apply biproduct.hom_ext
    intro i
    rw [Preadditive.add_comp, biproduct.lift_π, biproduct.lift_π]
    simp [add_smul]
  map_smul' r x := by
    apply biproduct.hom_ext
    intro i
    rw [Linear.smul_comp, biproduct.lift_π]
    simp [mul_smul]

/-- A finite-copower generator followed by a basis projection is the corresponding coordinate times the identity. -/
@[simp]
theorem finiteCopowerGenerator_comp_projection (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (x : V) (i : Fin (Module.finrank k V)) :
    finiteCopowerGenerator (k := k) P V x ≫ biproduct.π (fun _ : Fin (Module.finrank k V) => P) i =
      ((Module.finBasis k V).repr x i) • 𝟙 P := by
  change (biproduct.lift fun j =>
    ((Module.finBasis k V).repr x j) • 𝟙 P) ≫
      biproduct.π (fun _ : Fin (Module.finrank k V) => P) i = _
  simp

/-- The generator associated to a finite-basis vector is the corresponding biproduct inclusion. -/
@[simp]
theorem finiteCopowerGenerator_finBasis (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (i : Fin (Module.finrank k V)) :
    finiteCopowerGenerator (k := k) P V (Module.finBasis k V i) =
      biproduct.ι (fun _ : Fin (Module.finrank k V) => P) i := by
  classical
  change (biproduct.lift fun j =>
    ((Module.finBasis k V).repr (Module.finBasis k V i) j) • 𝟙 P) = _
  apply biproduct.hom_ext
  intro j
  by_cases h : i = j <;> simp [h]


/-- A linear family of morphisms from the chosen object induces a morphism from the corresponding finite copower. -/
noncomputable def finiteCopowerDesc (P : C) {V : Type v} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {Y : C} (f : V →ₗ[k] (P ⟶ Y)) :
    finiteCopower (k := k) P V ⟶ Y :=
  biproduct.desc fun i => f (Module.finBasis k V i)

/-- Composing a canonical generator with the morphism induced by a linear family evaluates that family. -/
@[simp, reassoc]
theorem finiteCopowerGenerator_comp_desc (P : C) {V : Type v} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {Y : C} (f : V →ₗ[k] (P ⟶ Y)) (x : V) :
    finiteCopowerGenerator (k := k) P V x ≫ finiteCopowerDesc (k := k) P f = f x := by
  let g : V →ₗ[k] (P ⟶ Y) := {
    toFun := fun y => finiteCopowerGenerator (k := k) P V y ≫ finiteCopowerDesc (k := k) P f
    map_add' := fun y z => by simp
    map_smul' := fun r y => by simp }
  have hg : g = f := by
    apply (Module.finBasis k V).ext
    intro i
    change finiteCopowerGenerator (k := k) P V (Module.finBasis k V i) ≫
      finiteCopowerDesc (k := k) P f = f (Module.finBasis k V i)
    rw [finiteCopowerGenerator_finBasis]
    simp [finiteCopowerDesc]
  exact LinearMap.congr_fun hg x


/-- Evaluation of a descended linear family at a generator is compatible with a further postcomposition. -/
add_decl_doc finiteCopowerGenerator_comp_desc_assoc

/-- Morphisms from a finite copower are linearly equivalent to linear families of morphisms from its chosen object. -/
@[source_ref "Chapter9/Problem9.6.5" (role := supporting)]
noncomputable def finiteCopowerHomEquiv (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (Y : C) :
    (finiteCopower (k := k) P V ⟶ Y) ≃ₗ[k] (V →ₗ[k] (P ⟶ Y)) where
  toFun f := {
    toFun := fun x => finiteCopowerGenerator (k := k) P V x ≫ f
    map_add' := fun x y => by simp
    map_smul' := fun r x => by simp }
  invFun := finiteCopowerDesc (k := k) P
  left_inv f := by
    apply biproduct.hom_ext'
    intro i
    change biproduct.ι (fun _ : Fin (Module.finrank k V) => P) i ≫
      biproduct.desc (fun j =>
        finiteCopowerGenerator (k := k) P V (Module.finBasis k V j) ≫ f) = _
    rw [biproduct.ι_desc, finiteCopowerGenerator_finBasis]
  right_inv f := by
    ext x
    exact finiteCopowerGenerator_comp_desc (k := k) P f x
  map_add' f g := by
    ext x
    simp
  map_smul' r f := by
    ext x
    simp


/-- Two morphisms from a finite copower are equal when they agree after every canonical generator. -/
theorem finiteCopower_hom_ext (P : C) {V : Type v} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {Y : C} {f g : finiteCopower (k := k) P V ⟶ Y}
    (h : ∀ x, finiteCopowerGenerator (k := k) P V x ≫ f =
      finiteCopowerGenerator (k := k) P V x ≫ g) : f = g := by
  exact (finiteCopowerHomEquiv (k := k) P V Y).injective (LinearMap.ext h)


/-- A linear map between finite-dimensional vector spaces induces a morphism between their finite copowers. -/
noncomputable def finiteCopowerMap (P : C) {V W : Type v}
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (f : V →ₗ[k] W) : finiteCopower (k := k) P V ⟶ finiteCopower (k := k) P W :=
  finiteCopowerDesc (k := k) P ((finiteCopowerGenerator (k := k) P W).comp f)

/-- A canonical generator followed by an induced finite-copower map is the generator of the image vector. -/
@[simp, reassoc]
theorem finiteCopowerGenerator_naturality (P : C) {V W : Type v}
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (f : V →ₗ[k] W) (x : V) :
    finiteCopowerGenerator (k := k) P V x ≫ finiteCopowerMap (k := k) P f =
      finiteCopowerGenerator (k := k) P W (f x) := by
  exact finiteCopowerGenerator_comp_desc (k := k) P _ x

/-- Naturality of finite-copower generators is preserved by a subsequent morphism. -/
add_decl_doc finiteCopowerGenerator_naturality_assoc

/-- The finite-copower morphism induced by the identity linear map is the identity morphism. -/
@[simp]
theorem finiteCopowerMap_id (P : C) (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] :
    finiteCopowerMap (k := k) P (LinearMap.id : V →ₗ[k] V) = 𝟙 _ := by
  apply finiteCopower_hom_ext (k := k) P
  intro x
  rw [finiteCopowerGenerator_naturality]
  simp

/-- The finite-copower morphism induced by a composite linear map is the composite of the induced morphisms. -/
@[reassoc]
theorem finiteCopowerMap_comp (P : C) {U V W : Type v}
    [AddCommGroup U] [Module k U] [Module.Finite k U]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (f : U →ₗ[k] V) (g : V →ₗ[k] W) :
    finiteCopowerMap (k := k) P (g.comp f) =
      finiteCopowerMap (k := k) P f ≫ finiteCopowerMap (k := k) P g := by
  apply finiteCopower_hom_ext (k := k) P
  intro x
  calc
    finiteCopowerGenerator (k := k) P U x ≫ finiteCopowerMap (k := k) P (g.comp f) =
        finiteCopowerGenerator (k := k) P W ((g.comp f) x) := finiteCopowerGenerator_naturality P _ _
    _ = finiteCopowerGenerator (k := k) P W (g (f x)) := rfl
    _ = finiteCopowerGenerator (k := k) P V (f x) ≫ finiteCopowerMap (k := k) P g :=
      (finiteCopowerGenerator_naturality P g (f x)).symm
    _ = (finiteCopowerGenerator (k := k) P U x ≫ finiteCopowerMap (k := k) P f) ≫
        finiteCopowerMap (k := k) P g :=
      congrArg (fun h : P ⟶ finiteCopower (k := k) P V =>
        h ≫ finiteCopowerMap (k := k) P g) (finiteCopowerGenerator_naturality P f x).symm
    _ = _ := Category.assoc _ _ _

/-- Compatibility of finite-copower maps with linear-map composition persists after postcomposition. -/
add_decl_doc finiteCopowerMap_comp_assoc

end Copower


section BalancedTensor

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [Linear k C]
  [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]


/-- The coefficient type of opposite endomorphisms associated to an object of a category. -/
abbrev oppositeEnd (P : C) := (End P)ᵐᵒᵖ

/-- The endomorphism space of an object is finite-dimensional over the ground field. -/
noncomputable local instance finiteDimensional_end (P : C) : FiniteDimensional k (End P) :=
  RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory.finiteDimensional_hom P P

/-- The ground-field module structure on the carrier of a finite module over the coefficient type. -/
noncomputable local instance carrierGroundFieldModule (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    Module k X :=
  Module.compHom X (algebraMap k (oppositeEnd P))

/-- Ground-field scalars and coefficient scalars form a scalar tower on the finite-module carrier. -/
local instance carrier_isScalarTower (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    IsScalarTower k (oppositeEnd P) X where
  smul_assoc a b x := by
    rw [Algebra.smul_def]
    exact mul_smul _ _ _

/-- The coefficient and ground-field scalar actions commute on the carrier of a finite module. -/
local instance carrier_smulCommClass (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    SMulCommClass (oppositeEnd P) k X where
  smul_comm b a x := by
    change b • ((algebraMap k (oppositeEnd P) a) • x) =
      (algebraMap k (oppositeEnd P) a) • (b • x)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- The carrier of a finite module over the coefficient type is finite-dimensional over the ground field. -/
noncomputable local instance carrier_finiteDimensional
    (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    FiniteDimensional k X :=
  Module.Finite.trans (oppositeEnd P) X


/-- The morphism from the finite copower on opposite endomorphisms to the chosen object given by evaluation. -/
@[source_ref "Chapter9/Problem9.6.5" (role := supporting)]
noncomputable def oppositeEndEvaluation (P : C) :
    finiteCopower (k := k) P (oppositeEnd P) ⟶ P :=
  finiteCopowerDesc (k := k) P
    (MulOpposite.opLinearEquiv k : End P ≃ₗ[k] oppositeEnd P).symm.toLinearMap

/-- Evaluating the finite-copower generator of an opposite endomorphism yields its underlying endomorphism. -/
@[simp, reassoc]
theorem oppositeEndEvaluation_generator (P : C) (b : oppositeEnd P) :
    finiteCopowerGenerator (k := k) P (oppositeEnd P) b ≫ oppositeEndEvaluation (k := k) P = b.unop := by
  exact finiteCopowerGenerator_comp_desc (k := k) P _ b


/-- Evaluation of an opposite-endomorphism generator is compatible with postcomposition out of the chosen object. -/
add_decl_doc oppositeEndEvaluation_generator_assoc

/-- The ground-field linear map from the coefficient tensor product with a module carrier to that carrier. -/
@[source_ref "Chapter9/Problem9.6.5" (role := supporting)]
noncomputable def tensorScalarAction (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    TensorProduct k (oppositeEnd P) X →ₗ[k] X :=
  TensorProduct.lift (Algebra.lsmul k k X).toLinearMap

omit [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C] in
/-- The tensor scalar-action map sends a pure tensor to the corresponding coefficient action. -/
@[simp]
theorem tensorScalarAction_tmul (P : C) (X : FGModuleCat.{v} (oppositeEnd P))
    (b : oppositeEnd P) (x : X) :
    tensorScalarAction (k := k) P X (b ⊗ₜ[k] x) = b • x := by
  simp [tensorScalarAction, Algebra.lsmul_apply]


/-- The morphism from the copower on opposite endomorphisms tensored with a module to the copower on its carrier induced by composition. -/
noncomputable def oppositeEndActionMap (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    finiteCopower (k := k) P (TensorProduct k (oppositeEnd P) X) ⟶
      finiteCopower (k := k) P X :=
  finiteCopowerDesc (k := k) P (TensorProduct.lift {
    toFun := fun b => {
      toFun := fun x => b.unop ≫ finiteCopowerGenerator (k := k) P X x
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
    map_add' := fun b c => by
      ext x
      change (b.unop + c.unop) ≫ finiteCopowerGenerator (k := k) P X x = _
      exact Preadditive.add_comp P P (finiteCopower (k := k) P X) b.unop c.unop
        (finiteCopowerGenerator (k := k) P X x)
    map_smul' := fun r b => by
      ext x
      change (r • b.unop) ≫ finiteCopowerGenerator (k := k) P X x = _
      exact Linear.smul_comp P P (finiteCopower (k := k) P X) r b.unop
        (finiteCopowerGenerator (k := k) P X x) })

/-- The pure-tensor generator followed by the endomorphism-action morphism is composition with the underlying endomorphism. -/
@[simp, reassoc]
theorem oppositeEndAction_generator (P : C)
    (X : FGModuleCat.{v} (oppositeEnd P)) (b : oppositeEnd P) (x : X) :
    finiteCopowerGenerator (k := k) P (TensorProduct k (oppositeEnd P) X) (b ⊗ₜ[k] x) ≫
      oppositeEndActionMap (k := k) P X =
        b.unop ≫ finiteCopowerGenerator (k := k) P X x := by
  simp [oppositeEndActionMap]


/-- The generator formula for the endomorphism-action morphism continues to hold after postcomposition. -/
add_decl_doc oppositeEndAction_generator_assoc

/-- The morphism from the finite copower on a coefficient tensor product to the finite copower on the module carrier induced by scalar action. -/
noncomputable def copowerActionMap (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    finiteCopower (k := k) P (TensorProduct k (oppositeEnd P) X) ⟶
      finiteCopower (k := k) P X :=
  finiteCopowerMap (k := k) P (tensorScalarAction (k := k) P X)

/-- The action morphism sends the generator of a pure tensor to the generator of the scalar action on the vector. -/
@[simp, reassoc]
theorem copowerActionMap_tmul (P : C)
    (X : FGModuleCat.{v} (oppositeEnd P)) (b : oppositeEnd P) (x : X) :
    finiteCopowerGenerator (k := k) P (TensorProduct k (oppositeEnd P) X) (b ⊗ₜ[k] x) ≫
      copowerActionMap (k := k) P X =
        finiteCopowerGenerator (k := k) P X (b • x) := by
  simp [copowerActionMap]


/-- The pure-tensor formula for the copower action morphism holds after postcomposition. -/
add_decl_doc copowerActionMap_tmul_assoc

/-- The morphism from the finite copower on the scalar tensor product to the finite copower on a module carrier. -/
@[source_ref "Chapter9/Problem9.6.5" (role := primary)]
noncomputable def modulePresentationRelation (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    finiteCopower (k := k) P (TensorProduct k (oppositeEnd P) X) ⟶
      finiteCopower (k := k) P X :=
  oppositeEndActionMap (k := k) P X - copowerActionMap (k := k) P X

/-- On a pure tensor, the presentation relation is the difference between endomorphism composition and coefficient action. -/
@[simp, reassoc]
theorem modulePresentationRelation_tmul (P : C)
    (X : FGModuleCat.{v} (oppositeEnd P)) (b : oppositeEnd P) (x : X) :
    finiteCopowerGenerator (k := k) P (TensorProduct k (oppositeEnd P) X) (b ⊗ₜ[k] x) ≫
      modulePresentationRelation (k := k) P X =
        b.unop ≫ finiteCopowerGenerator (k := k) P X x -
          finiteCopowerGenerator (k := k) P X (b • x) := by
  simp [modulePresentationRelation, Preadditive.comp_sub]


/-- The pure-tensor formula for the presentation relation remains valid after postcomposition. -/
add_decl_doc modulePresentationRelation_tmul_assoc

/-- The ground-field linear map on carriers underlying a morphism of finite modules. -/
noncomputable def moduleHomLinearMap (P : C) {X Y : FGModuleCat.{v} (oppositeEnd P)} (f : X ⟶ Y) :
    X →ₗ[k] Y where
  toFun := f
  map_add' := f.hom.hom.map_add
  map_smul' r x := by
    change f ((algebraMap k (oppositeEnd P) r) • x) =
      (algebraMap k (oppositeEnd P) r) • f x
    exact f.hom.hom.map_smul _ _

omit [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C] in
/-- The linear map underlying a finite-module morphism agrees pointwise with its concrete carrier map. -/
@[simp]
theorem moduleHomLinearMap_apply (P : C) {X Y : FGModuleCat.{v} (oppositeEnd P)} (f : X ⟶ Y)
    (x : X) : moduleHomLinearMap (k := k) P f x = f x := rfl

omit [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C] in
/-- The carrier linear map of an identity module morphism is the identity linear map. -/
@[simp]
theorem moduleHomLinearMap_id (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    moduleHomLinearMap (k := k) P (𝟙 X) = LinearMap.id := by
  ext x
  rfl

omit [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C] in
/-- The carrier linear map of a composite module morphism is the composite of the carrier linear maps. -/
@[simp]
theorem moduleHomLinearMap_comp (P : C) {X Y Z : FGModuleCat.{v} (oppositeEnd P)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleHomLinearMap (k := k) P (f ≫ g) =
      (moduleHomLinearMap (k := k) P g).comp (moduleHomLinearMap (k := k) P f) := by
  ext x
  rfl


/-- A finite-module morphism induces a ground-field linear map on its tensor product with the opposite endomorphism type. -/
noncomputable def oppositeEndTensorMap (P : C) {X Y : FGModuleCat.{v} (oppositeEnd P)} (f : X ⟶ Y) :
    TensorProduct k (oppositeEnd P) X →ₗ[k] TensorProduct k (oppositeEnd P) Y :=
  TensorProduct.map LinearMap.id (moduleHomLinearMap (k := k) P f)

omit [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C] in
/-- The tensor map induced by a module morphism sends a pure tensor by applying the morphism to its module factor. -/
@[simp]
theorem oppositeEndTensorMap_tmul (P : C) {X Y : FGModuleCat.{v} (oppositeEnd P)} (f : X ⟶ Y)
    (b : oppositeEnd P) (x : X) :
    oppositeEndTensorMap (k := k) P f (b ⊗ₜ[k] x) = b ⊗ₜ[k] f x := by
  simp [oppositeEndTensorMap, moduleHomLinearMap]


/-- The presentation relation commutes with the finite-copower maps induced by a module morphism. -/
theorem modulePresentationRelation_naturality (P : C) {X Y : FGModuleCat.{v} (oppositeEnd P)} (f : X ⟶ Y) :
    modulePresentationRelation (k := k) P X ≫
        finiteCopowerMap (k := k) P (moduleHomLinearMap (k := k) P f) =
      finiteCopowerMap (k := k) P (oppositeEndTensorMap (k := k) P f) ≫
        modulePresentationRelation (k := k) P Y := by
  apply finiteCopower_hom_ext (k := k) P
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
      rw [← Category.assoc, ← Category.assoc]
      calc
        (finiteCopowerGenerator (k := k) P (TensorProduct k (oppositeEnd P) X) (b ⊗ₜ[k] x) ≫
            modulePresentationRelation (k := k) P X) ≫
              finiteCopowerMap (k := k) P (moduleHomLinearMap (k := k) P f) =
            (b.unop ≫ finiteCopowerGenerator (k := k) P X x -
              finiteCopowerGenerator (k := k) P X (b • x)) ≫
                finiteCopowerMap (k := k) P (moduleHomLinearMap (k := k) P f) := by
                  rw [modulePresentationRelation_tmul]
        _ = b.unop ≫ finiteCopowerGenerator (k := k) P Y (f x) -
              finiteCopowerGenerator (k := k) P Y (f (b • x)) := by
                rw [Preadditive.sub_comp, Category.assoc, finiteCopowerGenerator_naturality,
                  finiteCopowerGenerator_naturality]
                rfl
        _ = b.unop ≫ finiteCopowerGenerator (k := k) P Y (f x) -
              finiteCopowerGenerator (k := k) P Y (b • f x) := by
                congr 2
                exact f.hom.hom.map_smul b x
        _ = finiteCopowerGenerator (k := k) P (TensorProduct k (oppositeEnd P) Y)
              (b ⊗ₜ[k] f x) ≫ modulePresentationRelation (k := k) P Y :=
                (modulePresentationRelation_tmul (k := k) P Y b (f x)).symm
        _ = (finiteCopowerGenerator (k := k) P (TensorProduct k (oppositeEnd P) X) (b ⊗ₜ[k] x) ≫
              finiteCopowerMap (k := k) P (oppositeEndTensorMap (k := k) P f)) ≫
                modulePresentationRelation (k := k) P Y := by
                  rw [finiteCopowerGenerator_naturality, oppositeEndTensorMap_tmul]
  | add z z' hz hz' =>
      simp only [map_add, Preadditive.add_comp]
      rw [hz, hz']


/-- Associates an object of the linear category to a finite module over the coefficient type of a chosen object. -/
@[source_ref "Chapter9/Problem9.6.5" (role := supporting)]
noncomputable def modulePresentationObject (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) : C :=
  cokernel (modulePresentationRelation (k := k) P X)


/-- The canonical morphism from the finite copower on a module carrier to its presentation object. -/
noncomputable def finiteCopowerToPresentation (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    finiteCopower (k := k) P X ⟶ modulePresentationObject (k := k) P X :=
  cokernel.π (modulePresentationRelation (k := k) P X)

/-- The canonical morphism from the finite copower to the presentation object is an epimorphism. -/
noncomputable instance finiteCopowerToPresentation_epi (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    Epi (finiteCopowerToPresentation (k := k) P X) := by
  dsimp [finiteCopowerToPresentation]
  infer_instance

/-- The presentation relation is annihilated by the morphism to the associated quotient object. -/
@[reassoc (attr := simp)]
theorem modulePresentationRelation_comp_quotient (P : C) (X : FGModuleCat.{v} (oppositeEnd P)) :
    modulePresentationRelation (k := k) P X ≫ finiteCopowerToPresentation (k := k) P X = 0 :=
  cokernel.condition _


/-- Postcomposing the zero presentation composite with another morphism agrees with postcomposing zero. -/
add_decl_doc modulePresentationRelation_comp_quotient_assoc

/-- The morphism between presentation objects induced by a morphism of finite modules. -/
noncomputable def modulePresentationMap (P : C) {X Y : FGModuleCat.{v} (oppositeEnd P)} (f : X ⟶ Y) :
    modulePresentationObject (k := k) P X ⟶ modulePresentationObject (k := k) P Y :=
  cokernel.desc (modulePresentationRelation (k := k) P X)
    (finiteCopowerMap (k := k) P (moduleHomLinearMap (k := k) P f) ≫
      finiteCopowerToPresentation (k := k) P Y) (by
        rw [← Category.assoc, modulePresentationRelation_naturality, Category.assoc,
          modulePresentationRelation_comp_quotient, comp_zero])

/-- The canonical maps to presentation objects are natural with respect to finite-module morphisms. -/
@[reassoc (attr := simp)]
theorem finiteCopowerToPresentation_naturality (P : C) {X Y : FGModuleCat.{v} (oppositeEnd P)} (f : X ⟶ Y) :
    finiteCopowerToPresentation (k := k) P X ≫ modulePresentationMap (k := k) P f =
      finiteCopowerMap (k := k) P (moduleHomLinearMap (k := k) P f) ≫
        finiteCopowerToPresentation (k := k) P Y :=
  cokernel.π_desc _ _ _


/-- Naturality of the maps to presentation objects is preserved by a further postcomposition. -/
add_decl_doc finiteCopowerToPresentation_naturality_assoc

/-- The functor from finite modules over the coefficient type to the given linear category. -/
@[source_ref "Chapter9/Problem9.6.5" (role := supporting)]
noncomputable def modulePresentationFunctor (P : C) : FGModuleCat.{v} (oppositeEnd P) ⥤ C where
  obj X := modulePresentationObject (k := k) P X
  map f := modulePresentationMap (k := k) P f
  map_id X := by
    apply (cancel_epi (finiteCopowerToPresentation (k := k) P X)).1
    rw [finiteCopowerToPresentation_naturality, moduleHomLinearMap_id, finiteCopowerMap_id,
      Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply (cancel_epi (finiteCopowerToPresentation (k := k) P _)).1
    rw [finiteCopowerToPresentation_naturality, ← Category.assoc, finiteCopowerToPresentation_naturality, Category.assoc,
      finiteCopowerToPresentation_naturality, moduleHomLinearMap_comp, finiteCopowerMap_comp]
    exact Category.assoc _ _ _

end BalancedTensor


attribute [local instance] finiteDimensional_end carrierGroundFieldModule carrier_isScalarTower carrier_smulCommClass
  carrier_finiteDimensional


section Unit

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [Linear k C]
  [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
variable {P : C} [hp : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P]

omit [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C] hp in
/-- Unop of a scalar from the algebra map is scalar multiplication of the identity endomorphism. -/
theorem oppositeEnd_algebraMap_unop (r : k) :
    (algebraMap k (oppositeEnd P) r).unop = r • 𝟙 P := by
  rfl


/-- The coefficient-linear map from morphisms out of the chosen object into a finite copower to the underlying module carrier. -/
noncomputable def presentationHomToCarrier (X : FGModuleCat.{v} (oppositeEnd P)) :
    (P ⟶ finiteCopower (k := k) P X) →ₗ[oppositeEnd P] X where
  toFun g := ∑ i : Fin (Module.finrank k X),
    (MulOpposite.op (g ≫ biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) :
      oppositeEnd P) • Module.finBasis k X i
  map_add' g h := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Preadditive.add_comp]
    change (MulOpposite.op ((g ≫ biproduct.π
        (fun _ : Fin (Module.finrank k X) => P) i) +
          (h ≫ biproduct.π (fun _ : Fin (Module.finrank k X) => P) i)) : oppositeEnd P) •
            Module.finBasis k X i = _
    rw [MulOpposite.op_add, add_smul]
  map_smul' b g := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (MulOpposite.op ((b.unop ≫ g) ≫
        biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : oppositeEnd P) •
          Module.finBasis k X i =
      b • ((MulOpposite.op (g ≫
        biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : oppositeEnd P) •
          Module.finBasis k X i)
    rw [smul_smul]
    congr 1
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_mul]
    exact Category.assoc _ _ _

omit hp in
/-- The coefficient map sends the canonical finite-copower generator of an element back to that element. -/
@[simp]
theorem presentationHomToCarrier_generator (X : FGModuleCat.{v} (oppositeEnd P)) (x : X) :
    presentationHomToCarrier (k := k) (P := P) X (finiteCopowerGenerator (k := k) P X x) = x := by
  classical
  unfold presentationHomToCarrier
  change (∑ i : Fin (Module.finrank k X),
    (MulOpposite.op ((biproduct.lift fun j =>
      ((Module.finBasis k X).repr x j) • 𝟙 P) ≫
        biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : oppositeEnd P) •
          Module.finBasis k X i) = x
  simp_rw [biproduct.lift_π]
  have hop (r : k) : MulOpposite.op (r • 𝟙 P) = algebraMap k (oppositeEnd P) r := by
    apply MulOpposite.unop_injective
    rw [oppositeEnd_algebraMap_unop]
    rfl
  simp_rw [hop]
  exact (Module.finBasis k X).sum_repr x

omit hp in
/-- A finite-copower generator followed by the presentation relation maps to zero in the module carrier. -/
theorem presentationHomToCarrier_relationGenerator (X : FGModuleCat.{v} (oppositeEnd P))
    (z : TensorProduct k (oppositeEnd P) X) :
    presentationHomToCarrier (k := k) (P := P) X
      (finiteCopowerGenerator (k := k) P (TensorProduct k (oppositeEnd P) X) z ≫
        modulePresentationRelation (k := k) P X) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
      rw [modulePresentationRelation_tmul]
      change presentationHomToCarrier (k := k) (P := P) X
        (b • finiteCopowerGenerator (k := k) P X x -
          finiteCopowerGenerator (k := k) P X (b • x)) = 0
      rw [map_sub, map_smul, presentationHomToCarrier_generator, presentationHomToCarrier_generator, sub_self]
  | add z z' hz hz' =>
      rw [map_add, Preadditive.add_comp, map_add, hz, hz', add_zero]

omit hp in
/-- Every morphism through the presentation relation maps to zero under the coefficient map to the carrier. -/
theorem presentationHomToCarrier_relation (X : FGModuleCat.{v} (oppositeEnd P))
    (h : P ⟶ finiteCopower (k := k) P (TensorProduct k (oppositeEnd P) X)) :
    presentationHomToCarrier (k := k) (P := P) X (h ≫ modulePresentationRelation (k := k) P X) = 0 := by
  let I := Fin (Module.finrank k (TensorProduct k (oppositeEnd P) X))
  let Q := fun _ : I => P
  have hh : h = ∑ i : I,
      (h ≫ biproduct.π Q i) ≫ biproduct.ι Q i := by
    have htotal : (∑ i : I, biproduct.π Q i ≫ biproduct.ι Q i) =
        𝟙 (finiteCopower (k := k) P (TensorProduct k (oppositeEnd P) X)) := biproduct.total
    calc
      h = h ≫ 𝟙 _ := (Category.comp_id h).symm
      _ = h ≫ ∑ i : I, biproduct.π Q i ≫ biproduct.ι Q i := by rw [htotal]
      _ = _ := by rw [Preadditive.comp_sum]; simp only [Category.assoc]
  rw [hh, Preadditive.sum_comp, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Category.assoc]
  change presentationHomToCarrier (k := k) (P := P) X
      ((MulOpposite.op (h ≫ biproduct.π Q i) : oppositeEnd P) •
        (biproduct.ι Q i ≫ modulePresentationRelation (k := k) P X)) = 0
  rw [map_smul]
  rw [← finiteCopowerGenerator_finBasis (k := k) P (TensorProduct k (oppositeEnd P) X) i]
  rw [presentationHomToCarrier_relationGenerator, smul_zero]


/-- Lifts a morphism from the chosen object into a finite copower to the finite copower on the coefficient tensor product. -/
noncomputable def presentationRelationLift (X : FGModuleCat.{v} (oppositeEnd P))
    (g : P ⟶ finiteCopower (k := k) P X) :
    P ⟶ finiteCopower (k := k) P (TensorProduct k (oppositeEnd P) X) :=
  ∑ i : Fin (Module.finrank k X),
    finiteCopowerGenerator (k := k) P (TensorProduct k (oppositeEnd P) X)
      ((MulOpposite.op (g ≫
        biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : oppositeEnd P) ⊗ₜ[k]
          Module.finBasis k X i)

omit hp in
/-- The lifted morphism followed by the presentation relation equals the original morphism minus its reconstructed generator. -/
theorem presentationRelationLift_comp_relation (X : FGModuleCat.{v} (oppositeEnd P))
    (g : P ⟶ finiteCopower (k := k) P X) :
    presentationRelationLift (k := k) (P := P) X g ≫ modulePresentationRelation (k := k) P X =
      g - finiteCopowerGenerator (k := k) P X (presentationHomToCarrier (k := k) (P := P) X g) := by
  classical
  unfold presentationRelationLift
  rw [Preadditive.sum_comp]
  simp_rw [modulePresentationRelation_tmul]
  rw [Finset.sum_sub_distrib]
  simp_rw [MulOpposite.unop_op, finiteCopowerGenerator_finBasis]
  have hfirst : (∑ i : Fin (Module.finrank k X),
      (g ≫ biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) ≫
        biproduct.ι (fun _ : Fin (Module.finrank k X) => P) i) = g := by
    have htotal : (∑ i : Fin (Module.finrank k X),
        biproduct.π (fun _ : Fin (Module.finrank k X) => P) i ≫
          biproduct.ι (fun _ : Fin (Module.finrank k X) => P) i) =
        𝟙 (finiteCopower (k := k) P X) := biproduct.total
    calc
      _ = g ≫ ∑ i : Fin (Module.finrank k X),
          biproduct.π (fun _ : Fin (Module.finrank k X) => P) i ≫
            biproduct.ι (fun _ : Fin (Module.finrank k X) => P) i := by
              rw [Preadditive.comp_sum]
              simp only [Category.assoc]
      _ = g ≫ 𝟙 _ := by rw [htotal]
      _ = g := Category.comp_id g
  rw [hfirst]
  congr 1
  change (∑ i : Fin (Module.finrank k X),
      finiteCopowerGenerator (k := k) P X
        ((MulOpposite.op (g ≫
          biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : oppositeEnd P) •
            Module.finBasis k X i)) =
    finiteCopowerGenerator (k := k) P X
      (∑ i : Fin (Module.finrank k X),
        (MulOpposite.op (g ≫
          biproduct.π (fun _ : Fin (Module.finrank k X) => P) i) : oppositeEnd P) •
            Module.finBasis k X i)
  exact (map_sum (finiteCopowerGenerator (k := k) P X) _ _).symm


/-- A morphism from the chosen object killed by the presentation quotient factors through the presentation relation. -/
theorem exists_relationFactorization (X : FGModuleCat.{v} (oppositeEnd P))
    (g : P ⟶ finiteCopower (k := k) P X)
    (hg : g ≫ finiteCopowerToPresentation (k := k) P X = 0) :
    ∃ h : P ⟶ finiteCopower (k := k) P (TensorProduct k (oppositeEnd P) X),
      h ≫ modulePresentationRelation (k := k) P X = g := by
  haveI : Projective P := hp.toProjective
  let gLift := kernel.lift (finiteCopowerToPresentation (k := k) P X) g hg
  let h := Projective.factorThru gLift
    (Abelian.factorThruImage (modulePresentationRelation (k := k) P X))
  refine ⟨h, ?_⟩
  have h₁ := Projective.factorThru_comp gLift
    (Abelian.factorThruImage (modulePresentationRelation (k := k) P X))
  have h₂ := Abelian.image.fac (modulePresentationRelation (k := k) P X)
  calc
    h ≫ modulePresentationRelation (k := k) P X =
        h ≫ (Abelian.factorThruImage (modulePresentationRelation (k := k) P X) ≫
          Abelian.image.ι (modulePresentationRelation (k := k) P X)) := by rw [h₂]
    _ = (h ≫ Abelian.factorThruImage (modulePresentationRelation (k := k) P X)) ≫
          Abelian.image.ι (modulePresentationRelation (k := k) P X) := by rw [Category.assoc]
    _ = gLift ≫ Abelian.image.ι (modulePresentationRelation (k := k) P X) := by rw [h₁]
    _ = gLift ≫ kernel.ι (finiteCopowerToPresentation (k := k) P X) := rfl
    _ = g := kernel.lift_ι _ _ _


/-- The coefficient-linear map from a finite-module carrier to morphisms from the chosen object into its presentation. -/
noncomputable def carrierToPresentationHom (X : FGModuleCat.{v} (oppositeEnd P)) :
    X →ₗ[oppositeEnd P] (P ⟶ modulePresentationObject (k := k) P X) where
  toFun x := finiteCopowerGenerator (k := k) P X x ≫ finiteCopowerToPresentation (k := k) P X
  map_add' x y := by simp
  map_smul' b x := by
    change finiteCopowerGenerator (k := k) P X (b • x) ≫ finiteCopowerToPresentation (k := k) P X =
      b.unop ≫ (finiteCopowerGenerator (k := k) P X x ≫ finiteCopowerToPresentation (k := k) P X)
    symm
    apply sub_eq_zero.mp
    calc
      b.unop ≫ (finiteCopowerGenerator (k := k) P X x ≫ finiteCopowerToPresentation (k := k) P X) -
          finiteCopowerGenerator (k := k) P X (b • x) ≫ finiteCopowerToPresentation (k := k) P X =
        (b.unop ≫ finiteCopowerGenerator (k := k) P X x -
          finiteCopowerGenerator (k := k) P X (b • x)) ≫
            finiteCopowerToPresentation (k := k) P X := by
              rw [Preadditive.sub_comp, Category.assoc]
      _ = (finiteCopowerGenerator (k := k) P (TensorProduct k (oppositeEnd P) X) (b ⊗ₜ[k] x) ≫
          modulePresentationRelation (k := k) P X) ≫ finiteCopowerToPresentation (k := k) P X := by
            rw [modulePresentationRelation_tmul]
      _ = 0 := by rw [Category.assoc, modulePresentationRelation_comp_quotient, comp_zero]


/-- The component mapping a finite module into the module associated to its presentation object. -/
noncomputable def moduleToPresentationModule (X : FGModuleCat.{v} (oppositeEnd P)) :
    X ⟶ hp.fgModuleFunctor.obj (modulePresentationObject (k := k) P X) :=
  InducedCategory.homMk (ModuleCat.ofHom (carrierToPresentationHom (k := k) (P := P) X))

/-- The comparison map sends a module element to its copower generator followed by the presentation quotient. -/
@[simp]
theorem moduleToPresentationModule_apply (X : FGModuleCat.{v} (oppositeEnd P)) (x : X) :
    moduleToPresentationModule (k := k) (P := P) X x =
      finiteCopowerGenerator (k := k) P X x ≫ finiteCopowerToPresentation (k := k) P X := rfl


/-- The natural morphism from the identity on finite modules to the presentation functor followed by the module-valued functor. -/
noncomputable def moduleToPresentationModuleHom :
    𝟭 (FGModuleCat.{v} (oppositeEnd P)) ⟶
      modulePresentationFunctor (k := k) P ⋙ hp.fgModuleFunctor where
  app X := moduleToPresentationModule (k := k) (P := P) X
  naturality X Y f := by
    apply FGModuleCat.hom_ext
    ext x
    change finiteCopowerGenerator (k := k) P Y (f x) ≫ finiteCopowerToPresentation (k := k) P Y =
      (finiteCopowerGenerator (k := k) P X x ≫ finiteCopowerToPresentation (k := k) P X) ≫
        modulePresentationMap (k := k) P f
    symm
    calc
      (finiteCopowerGenerator (k := k) P X x ≫ finiteCopowerToPresentation (k := k) P X) ≫
          modulePresentationMap (k := k) P f =
        finiteCopowerGenerator (k := k) P X x ≫
          (finiteCopowerToPresentation (k := k) P X ≫ modulePresentationMap (k := k) P f) :=
            Category.assoc _ _ _
      _ = finiteCopowerGenerator (k := k) P X x ≫
          (finiteCopowerMap (k := k) P (moduleHomLinearMap (k := k) P f) ≫
            finiteCopowerToPresentation (k := k) P Y) := by rw [finiteCopowerToPresentation_naturality]
      _ = (finiteCopowerGenerator (k := k) P X x ≫
          finiteCopowerMap (k := k) P (moduleHomLinearMap (k := k) P f)) ≫
            finiteCopowerToPresentation (k := k) P Y := (Category.assoc _ _ _).symm
      _ = finiteCopowerGenerator (k := k) P Y (f x) ≫ finiteCopowerToPresentation (k := k) P Y := by
        rw [finiteCopowerGenerator_naturality]
        rfl


/-- The linear map from the module carrier to morphisms into its presentation object is injective. -/
theorem carrierToPresentationHom_injective (X : FGModuleCat.{v} (oppositeEnd P)) :
    Function.Injective (carrierToPresentationHom (k := k) (P := P) X) := by
  intro x y hxy
  apply sub_eq_zero.mp
  let g := finiteCopowerGenerator (k := k) P X (x - y)
  have hg : g ≫ finiteCopowerToPresentation (k := k) P X = 0 := by
    change carrierToPresentationHom (k := k) (P := P) X (x - y) = 0
    rw [map_sub, hxy, sub_self]
  obtain ⟨t, ht⟩ := exists_relationFactorization (k := k) (P := P) X g hg
  calc
    x - y = presentationHomToCarrier (k := k) (P := P) X g := by
      symm
      exact presentationHomToCarrier_generator (k := k) (P := P) X (x - y)
    _ = presentationHomToCarrier (k := k) (P := P) X
        (t ≫ modulePresentationRelation (k := k) P X) := by rw [ht]
    _ = 0 := presentationHomToCarrier_relation (k := k) (P := P) X t


/-- The linear map from the module carrier to morphisms into its presentation object is surjective. -/
theorem carrierToPresentationHom_surjective (X : FGModuleCat.{v} (oppositeEnd P)) :
    Function.Surjective (carrierToPresentationHom (k := k) (P := P) X) := by
  intro y
  haveI : Projective P := hp.toProjective
  let g : P ⟶ finiteCopower (k := k) P X :=
    Projective.factorThru y (finiteCopowerToPresentation (k := k) P X)
  refine ⟨presentationHomToCarrier (k := k) (P := P) X g, ?_⟩
  have hrel := modulePresentationRelation_comp_quotient (k := k) P X
  have hlift := presentationRelationLift_comp_relation (k := k) (P := P) X g
  have hz : (g - finiteCopowerGenerator (k := k) P X
      (presentationHomToCarrier (k := k) (P := P) X g)) ≫
        finiteCopowerToPresentation (k := k) P X = 0 := by
    rw [← hlift, Category.assoc, hrel, comp_zero]
  have heq : g ≫ finiteCopowerToPresentation (k := k) P X =
      finiteCopowerGenerator (k := k) P X (presentationHomToCarrier (k := k) (P := P) X g) ≫
        finiteCopowerToPresentation (k := k) P X := by
    exact sub_eq_zero.mp (by simpa [Preadditive.sub_comp] using hz)
  change finiteCopowerGenerator (k := k) P X (presentationHomToCarrier (k := k) (P := P) X g) ≫
      finiteCopowerToPresentation (k := k) P X = y
  rw [← heq]
  exact Projective.factorThru_comp y (finiteCopowerToPresentation (k := k) P X)

/-- The isomorphism from a finite module to the module obtained from its presentation object. -/
noncomputable def moduleToPresentationModuleIso (X : FGModuleCat.{v} (oppositeEnd P)) :
    X ≅ hp.fgModuleFunctor.obj (modulePresentationObject (k := k) P X) := by
  let e : X ≃ₗ[oppositeEnd P] (P ⟶ modulePresentationObject (k := k) P X) :=
    LinearEquiv.ofBijective (carrierToPresentationHom (k := k) (P := P) X)
      ⟨carrierToPresentationHom_injective (k := k) (P := P) X,
        carrierToPresentationHom_surjective (k := k) (P := P) X⟩
  exact {
    hom := moduleToPresentationModule (k := k) (P := P) X
    inv := InducedCategory.homMk (ModuleCat.ofHom e.symm.toLinearMap)
    hom_inv_id := by
      apply FGModuleCat.hom_ext
      ext x
      exact e.left_inv x
    inv_hom_id := by
      apply FGModuleCat.hom_ext
      ext x
      exact e.right_inv x }

/-- The comparison morphism from a finite module to the module of its presentation is an isomorphism. -/
noncomputable instance moduleToPresentationModule_isIso (X : FGModuleCat.{v} (oppositeEnd P)) :
    IsIso (moduleToPresentationModule (k := k) (P := P) X) :=
  (moduleToPresentationModuleIso (k := k) (P := P) X).isIso_hom

/-- The forward map of the module comparison isomorphism is the canonical comparison morphism. -/
@[simp]
theorem moduleToPresentationModuleIso_hom (X : FGModuleCat.{v} (oppositeEnd P)) :
    (moduleToPresentationModuleIso (k := k) (P := P) X).hom = moduleToPresentationModule (k := k) (P := P) X := rfl


/-- The composite of the presentation functor with the module-valued functor is isomorphic to the identity on finite modules. -/
@[source_ref "Chapter9/Problem9.6.5" (role := primary)]
noncomputable def presentationThenModuleIso :
    modulePresentationFunctor (k := k) P ⋙ hp.fgModuleFunctor ≅
      𝟭 (FGModuleCat.{v} (oppositeEnd P)) :=
  (NatIso.ofComponents
    (fun X => moduleToPresentationModuleIso (k := k) (P := P) X)
    (fun f => (moduleToPresentationModuleHom (k := k) (P := P)).naturality f)).symm

end Unit


section Evaluation

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C] [Linear k C]
  [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
variable {P : C} [hp : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P]


/-- The ground-field linear map from elements of the module attached to an object to morphisms from the chosen object. -/
noncomputable def moduleElementToHom (Y : C) :
    hp.fgModuleFunctor.obj Y →ₗ[k] (P ⟶ Y) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' r f := by
    change (algebraMap k (oppositeEnd P) r).unop ≫ f = _
    rw [oppositeEnd_algebraMap_unop, Linear.smul_comp, Category.id_comp]
    rfl


/-- The morphism evaluating the finite copower on the carrier of the module associated to an object. -/
noncomputable def finiteCopowerEvaluation (Y : C) :
    finiteCopower (k := k) P (hp.fgModuleFunctor.obj Y) ⟶ Y :=
  finiteCopowerDesc (k := k) P (moduleElementToHom (k := k) (P := P) Y)

/-- A generator in the finite copower associated to an object evaluates to its represented morphism. -/
@[simp, reassoc]
theorem finiteCopowerGenerator_comp_evaluation (Y : C)
    (f : hp.fgModuleFunctor.obj Y) :
    finiteCopowerGenerator (k := k) P (hp.fgModuleFunctor.obj Y) f ≫
      finiteCopowerEvaluation (k := k) (P := P) Y = f :=
  finiteCopowerGenerator_comp_desc (k := k) P (moduleElementToHom (k := k) (P := P) Y) f


/-- The finite-copower generator evaluation identity is stable under postcomposition. -/
add_decl_doc finiteCopowerGenerator_comp_evaluation_assoc

/-- The presentation relation followed by evaluation at an object is zero. -/
theorem modulePresentationRelation_comp_evaluation (Y : C) :
    modulePresentationRelation (k := k) P (hp.fgModuleFunctor.obj Y) ≫
      finiteCopowerEvaluation (k := k) (P := P) Y = 0 := by
  apply finiteCopower_hom_ext (k := k) P
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b f =>
      rw [← Category.assoc, modulePresentationRelation_tmul,
        Preadditive.sub_comp, Category.assoc, finiteCopowerGenerator_comp_evaluation,
        finiteCopowerGenerator_comp_evaluation]
      simp only [comp_zero]
      change b.unop ≫ f - b.unop ≫ f = 0
      rw [sub_self]
  | add z z' hz hz' =>
      simp only [map_add, Preadditive.add_comp, hz, hz', comp_zero, add_zero]


/-- The evaluation morphism from the presentation of the finite module attached to an object back to that object. -/
noncomputable def presentationEvaluation (Y : C) :
    modulePresentationObject (k := k) P (hp.fgModuleFunctor.obj Y) ⟶ Y :=
  cokernel.desc _ (finiteCopowerEvaluation (k := k) (P := P) Y)
    (modulePresentationRelation_comp_evaluation (k := k) (P := P) Y)

/-- For a module obtained from an object, the presentation quotient followed by evaluation is the finite-copower evaluation. -/
@[reassoc (attr := simp)]
theorem finiteCopowerToPresentation_comp_evaluation (Y : C) :
    finiteCopowerToPresentation (k := k) P (hp.fgModuleFunctor.obj Y) ≫
      presentationEvaluation (k := k) (P := P) Y = finiteCopowerEvaluation (k := k) (P := P) Y :=
  cokernel.π_desc _ _ _

/-- The evaluation identity for the presentation quotient remains valid after postcomposition. -/
add_decl_doc finiteCopowerToPresentation_comp_evaluation_assoc

/-- A module element represented by its copower generator evaluates to the same morphism out of the chosen object. -/
@[simp, reassoc]
theorem copowerGenerator_comp_quotient_comp_evaluation (Y : C) (f : hp.fgModuleFunctor.obj Y) :
    finiteCopowerGenerator (k := k) P (hp.fgModuleFunctor.obj Y) f ≫
      (finiteCopowerToPresentation (k := k) P (hp.fgModuleFunctor.obj Y) ≫
        presentationEvaluation (k := k) (P := P) Y) = f := by
  rw [finiteCopowerToPresentation_comp_evaluation, finiteCopowerGenerator_comp_evaluation]

/-- The generator evaluation formula holds after composing with any morphism out of the evaluated object. -/
add_decl_doc copowerGenerator_comp_quotient_comp_evaluation_assoc

/-- Finite-copower evaluation is natural with respect to morphisms in the linear category. -/
theorem finiteCopowerEvaluation_naturality {Y Z : C} (f : Y ⟶ Z) :
    finiteCopowerMap (k := k) P
        (moduleHomLinearMap (k := k) P (hp.fgModuleFunctor.map f)) ≫
      finiteCopowerEvaluation (k := k) (P := P) Z =
        finiteCopowerEvaluation (k := k) (P := P) Y ≫ f := by
  apply finiteCopower_hom_ext (k := k) P
  intro g
  rw [← Category.assoc, finiteCopowerGenerator_naturality, finiteCopowerGenerator_comp_evaluation,
    ← Category.assoc, finiteCopowerGenerator_comp_evaluation]
  rfl


/-- The natural morphism from the module-valued functor followed by the presentation functor to the identity functor. -/
@[source_ref "Chapter9/Problem9.6.5" (role := primary)]
noncomputable def moduleThenPresentationHom :
    hp.fgModuleFunctor ⋙ modulePresentationFunctor (k := k) P ⟶ 𝟭 C where
  app Y := presentationEvaluation (k := k) (P := P) Y
  naturality Y Z f := by
    apply (cancel_epi
      (finiteCopowerToPresentation (k := k) P (hp.fgModuleFunctor.obj Y))).1
    change finiteCopowerToPresentation (k := k) P (hp.fgModuleFunctor.obj Y) ≫
        (modulePresentationMap (k := k) P (hp.fgModuleFunctor.map f) ≫
          presentationEvaluation (k := k) (P := P) Z) =
      finiteCopowerToPresentation (k := k) P (hp.fgModuleFunctor.obj Y) ≫
        (presentationEvaluation (k := k) (P := P) Y ≫ f)
    rw [← Category.assoc, finiteCopowerToPresentation_naturality, Category.assoc,
      finiteCopowerToPresentation_comp_evaluation, ← Category.assoc, finiteCopowerToPresentation_comp_evaluation]
    exact finiteCopowerEvaluation_naturality (k := k) (P := P) f


/-- The evaluation morphism from the reconstructed presentation object is an epimorphism. -/
noncomputable instance presentationEvaluation_epi (Y : C) :
    Epi (presentationEvaluation (k := k) (P := P) Y) := by
  constructor
  intro Z f g hfg
  apply sub_eq_zero.mp
  apply (Preadditive.isSeparator_iff P).1 hp.isSeparator (f - g)
  intro a
  rw [Preadditive.comp_sub]
  apply sub_eq_zero.mpr
  rw [← copowerGenerator_comp_quotient_comp_evaluation (k := k) (P := P) Y a]
  simp only [Category.assoc]
  rw [hfg]


/-- Every component of the natural morphism from the module-presentation composite to the identity is an epimorphism. -/
@[source_ref "Chapter9/Problem9.6.5" (role := primary)]
theorem moduleThenPresentationHom_app_epi (Y : C) : Epi ((moduleThenPresentationHom (k := k) (P := P)).app Y) := by
  change Epi (presentationEvaluation (k := k) (P := P) Y)
  infer_instance


/-- The module comparison at an associated module followed by the mapped evaluation morphism is the identity. -/
theorem modulePresentation_triangle (Y : C) :
    moduleToPresentationModule (k := k) (P := P) (hp.fgModuleFunctor.obj Y) ≫
        hp.fgModuleFunctor.map (presentationEvaluation (k := k) (P := P) Y) =
      𝟙 (hp.fgModuleFunctor.obj Y) := by
  apply FGModuleCat.hom_ext
  ext f
  change (finiteCopowerGenerator (k := k) P (hp.fgModuleFunctor.obj Y) f ≫
      finiteCopowerToPresentation (k := k) P (hp.fgModuleFunctor.obj Y)) ≫
        presentationEvaluation (k := k) (P := P) Y = f
  simpa only [Category.assoc] using copowerGenerator_comp_quotient_comp_evaluation (k := k) (P := P) Y f

/-- Applying the module-valued functor to the evaluation morphism produces an isomorphism. -/
noncomputable instance moduleFunctor_map_evaluation_isIso (Y : C) :
    IsIso (hp.fgModuleFunctor.map
      (presentationEvaluation (k := k) (P := P) Y)) := by
  haveI : IsIso (moduleToPresentationModule (k := k) (P := P)
      (hp.fgModuleFunctor.obj Y)) :=
    moduleToPresentationModule_isIso (k := k) (P := P) (hp.fgModuleFunctor.obj Y)
  haveI : IsIso
      (moduleToPresentationModule (k := k) (P := P) (hp.fgModuleFunctor.obj Y) ≫
        hp.fgModuleFunctor.map (presentationEvaluation (k := k) (P := P) Y)) := by
    rw [modulePresentation_triangle]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (moduleToPresentationModule (k := k) (P := P) (hp.fgModuleFunctor.obj Y))
    (hp.fgModuleFunctor.map (presentationEvaluation (k := k) (P := P) Y))


/-- The kernel of the evaluation morphism from a presentation object is a zero object. -/
@[source_ref "Chapter9/Problem9.6.5" (role := supporting)]
theorem kernel_presentationEvaluation_isZero (Y : C) :
    IsZero (kernel (presentationEvaluation (k := k) (P := P) Y)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (Preadditive.isSeparator_iff P).1 hp.isSeparator
    (𝟙 (kernel (presentationEvaluation (k := k) (P := P) Y)))
  intro f
  rw [Category.comp_id]
  have hfι : f ≫ kernel.ι (presentationEvaluation (k := k) (P := P) Y) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (hp.fgModuleFunctor.map
        (presentationEvaluation (k := k) (P := P) Y))).1
    change (f ≫ kernel.ι (presentationEvaluation (k := k) (P := P) Y)) ≫
        presentationEvaluation (k := k) (P := P) Y = 0 ≫
          presentationEvaluation (k := k) (P := P) Y
    rw [Category.assoc, kernel.condition, comp_zero, zero_comp]
  apply (cancel_mono (kernel.ι (presentationEvaluation (k := k) (P := P) Y))).1
  rw [hfι, zero_comp]

/-- The evaluation morphism from the reconstructed presentation object is an isomorphism. -/
noncomputable instance presentationEvaluation_isIso (Y : C) :
    IsIso (presentationEvaluation (k := k) (P := P) Y) := by
  haveI : Mono (presentationEvaluation (k := k) (P := P) Y) :=
    Preadditive.mono_of_isZero_kernel _
      (kernel_presentationEvaluation_isZero (k := k) (P := P) Y)
  exact isIso_of_mono_of_epi _

/-- The isomorphism between the reconstructed presentation of an object and the object itself. -/
noncomputable def presentationEvaluationIso (Y : C) :
    modulePresentationObject (k := k) P (hp.fgModuleFunctor.obj Y) ≅ Y := by
  letI : IsIso (presentationEvaluation (k := k) (P := P) Y) :=
    presentationEvaluation_isIso (k := k) (P := P) Y
  exact asIso (presentationEvaluation (k := k) (P := P) Y)

/-- The forward morphism of the presentation evaluation isomorphism is the evaluation morphism. -/
@[simp]
theorem presentationEvaluationIso_hom (Y : C) :
    (presentationEvaluationIso (k := k) (P := P) Y).hom =
      presentationEvaluation (k := k) (P := P) Y := rfl


/-- The natural morphism from the module-presentation composite to the identity functor is an isomorphism. -/
@[source_ref "Chapter9/Problem9.6.5" (role := primary)]
theorem moduleThenPresentationHom_isIso : IsIso (moduleThenPresentationHom (k := k) (P := P)) := by
  let e : hp.fgModuleFunctor ⋙ modulePresentationFunctor (k := k) P ≅ 𝟭 C :=
    NatIso.ofComponents
      (fun Y => presentationEvaluationIso (k := k) (P := P) Y)
      (fun f => (moduleThenPresentationHom (k := k) (P := P)).naturality f)
  have he : e.hom = moduleThenPresentationHom (k := k) (P := P) := by
    ext Y
    exact presentationEvaluationIso_hom (k := k) (P := P) Y
  rw [← he]
  exact e.isIso_hom


/-- The composite of the module-valued functor with the presentation functor is isomorphic to the identity on the original category. -/
noncomputable def moduleThenPresentationIso :
    hp.fgModuleFunctor ⋙ modulePresentationFunctor (k := k) P ≅ 𝟭 C := by
  letI := moduleThenPresentationHom_isIso (k := k) (P := P)
  exact asIso (moduleThenPresentationHom (k := k) (P := P))


/-- An equivalence between the linear category and finite modules over the coefficient type of the chosen object. -/
@[source_ref "Chapter9/Problem9.6.5" (role := supporting)]
noncomputable def finiteModuleEquivalence :
    C ≌ FGModuleCat.{v} (oppositeEnd P) :=
  CategoryTheory.Equivalence.mk hp.fgModuleFunctor
    (modulePresentationFunctor (k := k) P)
    (moduleThenPresentationIso (k := k) (P := P)).symm (presentationThenModuleIso (k := k) (P := P))

end Evaluation

end RepresentationTheory.CategoryTheory.Linear.FiniteModulePresentationEquivalence
