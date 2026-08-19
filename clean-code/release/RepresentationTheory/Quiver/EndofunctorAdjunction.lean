/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.QuiverRepresentationAuxiliaryFunctor
import RepresentationTheory.QuiverRepresentationQuotientFunctor
import RepresentationTheory.CategoryTheory.Abelian.AdditiveAdjunctionAuxiliary
import RepresentationTheory.Quiver.Representation.Reflection
import RepresentationTheory.Alignment.Attribute



noncomputable section

open CategoryTheory

namespace RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData

/-- Transport a morphism between representations along an equality of quiver structures. -/
def quiverEqHom
    {k Q : Type*} [CommSemiring k] {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    {X Y : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ I₁}
    (f : @RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q _ I₁ X Y) :
    @RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q _ I₂ (h ▸ X) (h ▸ Y) := by
  subst h
  exact f

/-- The endofunctor on representations induced by an equality of quiver structures. -/
def quiverEqFunctor
    {k Q : Type*} [CommSemiring k] {I₁ I₂ : Quiver Q} (h : I₁ = I₂) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ I₁ ⥤ @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ I₂ where
  obj X := h ▸ X
  map f := quiverEqHom h f
  map_id X := by subst h; rfl
  map_comp f g := by subst h; rfl

/-- On objects, transport along equality of quiver structures is given by equality recursor transport. -/
@[simp]
theorem quiverEqFunctor_obj
    {k Q : Type*} [CommSemiring k] {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    (X : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ I₁) :
    (quiverEqFunctor h).obj X = h ▸ X := by
  subst h
  rfl

/-- Transporting a mapped morphism along equality of quiver structures agrees pointwise with mapping the transported morphism. -/
theorem quiverEqFunctor_map_apply
    {k Q : Type*} [CommSemiring k] {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    {X Y : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ I₁} (f : X ⟶ Y) (v : Q)
    (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ I₂ ((quiverEqFunctor h).obj X) v) :
    reindex h Y v (((quiverEqFunctor h).map f).app v x) =
      @RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ I₁ X Y f v
        (reindex h X v x) := by
  subst h
  rfl

/-- The representation endofunctor determined by a selected vertex. -/
def vertexEndofunctor
    {k Q : Type*} [CommSemiring k] [DecidableEq Q] [Quiver Q] (i : Q) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i) ⥤
      RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q :=
  quiverEqFunctor (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q i)

/-- The selected-vertex endofunctor has the specified action on objects. -/
@[simp]
theorem vertexEndofunctor_obj
    {k Q : Type*} [CommSemiring k] [DecidableEq Q] [Quiver Q] (i : Q)
    (X : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i)) :
    (vertexEndofunctor i).obj X = auxiliaryAt X :=
  quiverEqFunctor_obj (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q i) X

end RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData

namespace RepresentationTheory.Quiver.EndofunctorAdjunction

variable {k Q : Type*} [CommRing k] [DecidableEq Q] [instQ : Quiver Q]
  {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i) [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]

/-- The representation endofunctor determined by the selected vertex and a finite associated indexing type. -/
abbrev leftEndofunctor :
    RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q ⥤
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) :=
  RepresentationTheory.QuiverRepresentationQuotientFunctor.quotientRepresentationFunctor k Q i hi

/-- The representation endofunctor determined by the selected vertex. -/
abbrev rightEndofunctor :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) ⥤
      RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q :=
  (@RepresentationTheory.QuiverRepresentationAuxiliaryFunctor.auxiliaryRepresentationFunctor k _ Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i
      (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward hi)) ⋙
    RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.vertexEndofunctor i

/-- Away from the selected vertex, evaluation of the right endofunctor is linearly equivalent to evaluation of the original representation. -/
def rightEndofunctorComponentEquiv
    (W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i))
    (v : Q) (hv : v ≠ i) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instQ
        ((rightEndofunctor hi).obj W) v ≃ₗ[k]
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) W v :=
  (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.reflectAt_reindex
      (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i
        (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward hi) W) v).trans
    (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i
      (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward hi) W v hv)

/-- The hom-set equivalence between maps out of the left endofunctor and maps into the right endofunctor. -/
def homEquiv
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    (W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)) :
    ((leftEndofunctor hi).obj V ⟶ W) ≃
      (V ⟶ (rightEndofunctor hi).obj W) :=
  (RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv hi V W).trans
    (RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv_dual hi V W).symm

/-- Away from the selected vertex, the first auxiliary morphism equivalence has the displayed componentwise composite. -/
@[simp]
theorem auxiliaryLeftHomEquiv_apply_component_of_ne
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    (W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i))
    (f : (leftEndofunctor hi).obj V ⟶ W)
    (v : Q) (hv : v ≠ i) :
    ((RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv hi V W) f).map v hv =
      (@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
          _ _ f v).comp
        (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi V v hv).symm.toLinearMap := by
  rfl

/-- Away from the selected vertex, the inverse of the first auxiliary morphism equivalence has the displayed componentwise composite. -/
@[simp]
theorem auxiliaryLeftHomEquiv_symm_apply_component_of_ne
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    (W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i))
    (r : RepresentationTheory.Quiver.Representation.Reflection.ReflectionHom hi V W) (v : Q) (hv : v ≠ i) :
    (@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) _ _
        ((RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv hi V W).symm r) v) =
      (r.map v hv).comp (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi V v hv).toLinearMap := by
  ext x
  simp [RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv, hv]

/-- Away from the selected vertex, the second auxiliary morphism equivalence has the displayed componentwise composite. -/
@[simp]
theorem auxiliaryRightHomEquiv_apply_component_of_ne
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    (W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i))
    (g : V ⟶ (rightEndofunctor hi).obj W)
    (v : Q) (hv : v ≠ i) :
    ((RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv_dual hi V W) g).map v hv =
      (rightEndofunctorComponentEquiv hi W v hv).toLinearMap.comp (g.app v) := by
  rfl

/-- Away from the selected vertex, the inverse of the second auxiliary morphism equivalence has the displayed componentwise composite. -/
@[simp]
theorem auxiliaryRightHomEquiv_symm_apply_component_of_ne
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    (W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i))
    (r : RepresentationTheory.Quiver.Representation.Reflection.ReflectionHom hi V W) (v : Q) (hv : v ≠ i) :
    (((RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv_dual hi V W).symm r).app v) =
      (rightEndofunctorComponentEquiv hi W v hv).symm.toLinearMap.comp (r.map v hv) := by
  ext x
  simp only [RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv_dual, ne_eq, LinearEquiv.trans_symm,
    eq_mpr_eq_cast, cast_eq, Equiv.symm_mk, Equiv.coe_fn_mk, hv, ↓reduceDIte,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply]
  change _ = (rightEndofunctorComponentEquiv hi W v hv).symm (r.map v hv x)
  rfl

omit [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] in
/-- Away from the selected vertex, the right endofunctor maps a morphism compatibly with the component linear equivalences. -/
theorem rightEndofunctor_map_apply_of_ne
    {W W' : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)}
    (g : W ⟶ W') (v : Q) (hv : v ≠ i)
    (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instQ
      ((rightEndofunctor hi).obj W) v) :
    rightEndofunctorComponentEquiv hi W' v hv
        (((rightEndofunctor hi).map g).app v x) =
      (@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        W W' g v) (rightEndofunctorComponentEquiv hi W v hv x) := by
  let hi' := RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward hi
  let h := RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q i
  change (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i hi' W' v hv)
      (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.reindex h _ v
        ((@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ instQ _ _
          ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.quiverEqFunctor h).map
            (@RepresentationTheory.QuiverRepresentationAuxiliaryFunctor.auxiliaryRepresentationMap k _ Q _
              (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i hi' W W' g)) v) x)) =
    (@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      W W' g v)
      ((@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i hi' W v hv)
        (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.reindex h _ v x))
  rw [RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.quiverEqFunctor_map_apply]
  exact @RepresentationTheory.QuiverRepresentationAuxiliaryFunctor.auxiliaryRepresentationMap_of_ne k _ Q _
    (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i
    (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward hi) W W' g v hv _

/-- Away from the selected vertex, the hom-set equivalence acts pointwise through the two displayed component equivalences. -/
theorem homEquiv_apply_component_of_ne
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    (W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i))
    (f : (leftEndofunctor hi).obj V ⟶ W)
    (v : Q) (hv : v ≠ i) (x : V.obj v) :
    rightEndofunctorComponentEquiv hi W v hv
        ((homEquiv hi V W f).app v x) =
      (@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        _ _ f v) ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi V v hv).symm x) := by
  change rightEndofunctorComponentEquiv hi W v hv
      (((RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv_dual hi V W).symm
        ((RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv hi V W) f)).app v x) = _
  rw [auxiliaryRightHomEquiv_symm_apply_component_of_ne hi V W _ v hv]
  rw [auxiliaryLeftHomEquiv_apply_component_of_ne]
  change rightEndofunctorComponentEquiv hi W v hv
      ((rightEndofunctorComponentEquiv hi W v hv).symm
        ((@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
          _ _ f v) ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi V v hv).symm x))) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Away from the selected vertex, the inverse hom-set equivalence acts pointwise through the two displayed component equivalences. -/
theorem homEquiv_symm_apply_component_of_ne
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    (W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i))
    (g : V ⟶ (rightEndofunctor hi).obj W)
    (v : Q) (hv : v ≠ i)
    (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi V) v) :
    (@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) _ _
      ((homEquiv hi V W).symm g) v) x =
      rightEndofunctorComponentEquiv hi W v hv
        (g.app v (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi V v hv x)) := by
  change (@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      _ _ ((RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv hi V W).symm
        ((RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv_dual hi V W) g)) v) x = _
  rw [auxiliaryLeftHomEquiv_symm_apply_component_of_ne hi V W _ v hv]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    auxiliaryRightHomEquiv_apply_component_of_ne]

/-- Away from the selected vertex, the left endofunctor maps a morphism compatibly with the displayed component linear equivalences. -/
theorem leftEndofunctor_map_apply_of_ne
    {V' V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q} (f : V' ⟶ V)
    (v : Q) (hv : v ≠ i)
    (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      ((leftEndofunctor hi).obj V') v) :
    RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi V v hv
        ((@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) _ _
          ((leftEndofunctor hi).map f) v) x) =
      f.app v (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi V' v hv x) :=
  RepresentationTheory.QuiverRepresentationQuotientFunctor.quotientRepresentationMap_of_ne hi f v hv x

/-- The inverse hom-set equivalence sends precomposition to composition with the image under the left endofunctor. -/
theorem homEquiv_symm_comp_left
    {V' V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    {W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)}
    (f : V' ⟶ V) (g : V ⟶ (rightEndofunctor hi).obj W) :
    (homEquiv hi V' W).symm (f ≫ g) =
      (leftEndofunctor hi).map f ≫
      (homEquiv hi V W).symm g := by
  dsimp only [leftEndofunctor]
  apply (RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv hi V' W).injective
  apply RepresentationTheory.Quiver.Representation.Reflection.ReflectionHom.ext
  funext v hv
  apply LinearMap.ext
  intro x
  rw [auxiliaryLeftHomEquiv_apply_component_of_ne hi V' W _ v hv,
    auxiliaryLeftHomEquiv_apply_component_of_ne hi V' W _ v hv]
  simp only [LinearMap.comp_apply,
    RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.comp_component]
  rw [homEquiv_symm_apply_component_of_ne hi V' W (f ≫ g) v hv,
    homEquiv_symm_apply_component_of_ne hi V W g v hv]
  rw [leftEndofunctor_map_apply_of_ne]
  simp

/-- The hom-set equivalence sends postcomposition to composition with the image under the right endofunctor. -/
theorem homEquiv_comp_right
    {V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    {W W' : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)}
    (f : (leftEndofunctor hi).obj V ⟶ W) (g : W ⟶ W') :
    homEquiv hi V W' (f ≫ g) =
      homEquiv hi V W f ≫
        (rightEndofunctor hi).map g := by
  dsimp only [rightEndofunctor]
  apply (RepresentationTheory.Quiver.Representation.Reflection.reflectionHomEquiv_dual hi V W').injective
  apply RepresentationTheory.Quiver.Representation.Reflection.ReflectionHom.ext
  funext v hv
  apply LinearMap.ext
  intro x
  rw [auxiliaryRightHomEquiv_apply_component_of_ne,
    auxiliaryRightHomEquiv_apply_component_of_ne]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.comp_component]
  rw [homEquiv_apply_component_of_ne,
    rightEndofunctor_map_apply_of_ne,
    homEquiv_apply_component_of_ne]
  rfl

/-- Core hom-set equivalence data for the two endofunctors. -/
def coreHomEquiv :
    CategoryTheory.Adjunction.CoreHomEquiv
      (leftEndofunctor (k := k) hi)
      (rightEndofunctor (k := k) hi) where
  homEquiv := homEquiv (k := k) (Q := Q) hi
  homEquiv_naturality_left_symm :=
    homEquiv_symm_comp_left (k := k) (Q := Q) hi
  homEquiv_naturality_right :=
    homEquiv_comp_right (k := k) (Q := Q) hi

/-- The endofunctor requiring finite vertex data is left adjoint to the corresponding endofunctor without that requirement. -/
@[source_ref "Chapter7/Exercise7.9.8" (role := primary)]
def adjunction :
    leftEndofunctor (k := k) hi ⊣
      rightEndofunctor (k := k) hi :=
  CategoryTheory.Adjunction.mkOfHomEquiv
    (coreHomEquiv (k := k) (Q := Q) hi)

/-- The hom-set equivalence of the endofunctor adjunction is the explicitly defined equivalence. -/
@[simp]
theorem adjunction_homEquiv
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    (W : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)) :
    (adjunction (k := k) (Q := Q) hi).homEquiv V W =
      homEquiv (k := k) hi V W := by
  rw [adjunction, CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The left endofunctor satisfies the required auxiliary condition. -/
@[source_ref "Chapter7/Exercise7.9.8" (role := supporting)]
theorem auxiliaryLeftEndofunctorCondition :
    RepresentationTheory.FunctorPredicateLogic.Right (leftEndofunctor (k := k) hi) := by
  haveI := (adjunction (k := k) (Q := Q) hi).leftAdjoint_preservesColimits
  infer_instance

set_option linter.unusedFintypeInType false in
/-- The right endofunctor satisfies the required auxiliary condition when the associated indexing type is finite. -/
@[source_ref "Chapter7/Exercise7.9.8" (role := supporting)]
theorem auxiliaryRightEndofunctorCondition :
    RepresentationTheory.FunctorPredicateLogic.Left (rightEndofunctor (k := k) hi) := by
  haveI := (adjunction (k := k) (Q := Q) hi).rightAdjoint_preservesLimits
  infer_instance

/-- Both auxiliary conditions hold for the two endofunctors determined by the finite vertex data. -/
@[source_ref "Chapter7/Exercise7.9.8" (role := primary)]
theorem auxiliaryEndofunctorConditions :
    RepresentationTheory.FunctorPredicateLogic.Right (leftEndofunctor (k := k) hi) ∧
      RepresentationTheory.FunctorPredicateLogic.Left (rightEndofunctor (k := k) hi) :=
  ⟨auxiliaryLeftEndofunctorCondition (k := k) hi,
    auxiliaryRightEndofunctorCondition (k := k) hi⟩

end RepresentationTheory.Quiver.EndofunctorAdjunction

end
