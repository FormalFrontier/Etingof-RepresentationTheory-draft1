/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Quiver.LinearRepresentationCategory
import RepresentationTheory.QuiverRepresentationQuotientTransform
import RepresentationTheory.Alignment.Attribute






















universe u_k u_V u_obj u_hom

namespace RepresentationTheory.QuiverRepresentationQuotientFunctor

variable {k : Type u_k} [CommRing k] {Q : Type u_V} [Quiver.{u_hom} Q]



/-- The linear map between outgoing direct sums obtained by applying a representation morphism on every summand. -/

noncomputable def outgoingDirectSumMapOfHom
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i : Q) :
    DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1) →ₗ[k]
      DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1) := by
  letI : DecidableEq (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) := Classical.decEq _
  exact DirectSum.toModule k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) _
    (fun a => (DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)
      (fun a => ρ₂.obj a.1) a).comp (f.app a.1))

/-- On an element inserted into one outgoing summand, the componentwise direct-sum map applies the matching morphism component and reinserts it. -/

theorem outgoingDirectSumMapOfHom_lof_apply
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i : Q)
    (d : DecidableEq (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i))
    (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (x : ρ₁.obj a.1) :
    outgoingDirectSumMapOfHom f i
        (@DirectSum.lof k _ (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1) _ _ d a x) =
      @DirectSum.lof k _ (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1) _ _ d a
        (f.app a.1 x) := by
  have hd : d = Classical.decEq _ := Subsingleton.elim _ _
  subst hd
  delta outgoingDirectSumMapOfHom
  erw [DirectSum.toModule_lof]
  simp only [LinearMap.coe_comp, Function.comp_apply]

/-- The outgoing direct-sum map induced by an identity morphism fixes each element. -/
theorem outgoingDirectSumMapOfHom_id_apply
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q) (i : Q)
    (y : DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :
    outgoingDirectSumMapOfHom (RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.id ρ) i y = y := by
  letI : DecidableEq (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i => ρ.obj a.1) b x =
        DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1) b x from rfl,
      outgoingDirectSumMapOfHom_lof_apply]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

/-- The outgoing direct-sum map for a composite morphism acts by the two componentwise maps in succession. -/
theorem outgoingDirectSumMapOfHom_comp_apply
    {ρ₁ ρ₂ ρ₃ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂)
    (g : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₂ ρ₃) (i : Q)
    (y : DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :
    outgoingDirectSumMapOfHom (f.comp g) i y =
      outgoingDirectSumMapOfHom g i (outgoingDirectSumMapOfHom f i y) := by
  letI : DecidableEq (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i => ρ₁.obj a.1) b x =
        DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1) b x from rfl,
      outgoingDirectSumMapOfHom_lof_apply, outgoingDirectSumMapOfHom_lof_apply, outgoingDirectSumMapOfHom_lof_apply]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The componentwise outgoing direct-sum map commutes with the structural maps from the distinguished vertex. -/

theorem outgoingDirectSumMapOfHom_structural
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i : Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] (x : ρ₁.obj i) :
    outgoingDirectSumMapOfHom f i (ρ₁.outgoingDirectSumMap i x) = ρ₂.outgoingDirectSumMap i (f.app i x) := by
  delta RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap
  simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [outgoingDirectSumMapOfHom_lof_apply f i _ a (ρ₁.map a.2 x), f.naturality a.2 x]



/-- The linear map between quotients of outgoing direct sums induced by a morphism of quiver representations. -/


noncomputable def outgoingQuotientMap
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i : Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun _ => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun _ => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) ⧸
        LinearMap.range (ρ₁.outgoingDirectSumMap i)) →ₗ[k]
      ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) ⧸
        LinearMap.range (ρ₂.outgoingDirectSumMap i)) :=
  letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun _ => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun _ => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  Submodule.mapQ _ _ (outgoingDirectSumMapOfHom f i) (by
    rintro y ⟨x, rfl⟩
    exact ⟨f.app i x, (outgoingDirectSumMapOfHom_structural f i x).symm⟩)

/-- The induced map on outgoing quotients sends the class of a direct-sum element to the class of its componentwise image. -/

theorem outgoingQuotientMap_mk
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i : Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (y : DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :
    letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun _ => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun _ => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    outgoingQuotientMap f i (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (outgoingDirectSumMapOfHom f i y) :=
  rfl



/-- The linear map on quotient-based auxiliary vertex spaces induced by a morphism of representations. -/


noncomputable def quotientAuxiliaryVertexMap
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i v : Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] (d : Decidable (v = i)) :
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid.{u_k, u_V, u_obj, u_hom} ρ₁ i v d
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid.{u_k, u_V, u_obj, u_hom} ρ₂ i v d
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule.{u_k, u_V, u_obj, u_hom} ρ₁ i v d
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule.{u_k, u_V, u_obj, u_hom} ρ₂ i v d
    RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ₁ i v d →ₗ[k]
      RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ₂ i v d :=
  @Decidable.casesOn (v = i)
    (fun d =>
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid.{u_k, u_V, u_obj, u_hom} ρ₁ i v d
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid.{u_k, u_V, u_obj, u_hom} ρ₂ i v d
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule.{u_k, u_V, u_obj, u_hom} ρ₁ i v d
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule.{u_k, u_V, u_obj, u_hom} ρ₂ i v d
      RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ₁ i v d →ₗ[k]
        RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ₂ i v d)
    d
    (fun _ => f.app v)
    (fun _ => outgoingQuotientMap f i)

/-- The quotient-based auxiliary vertex map induced by an identity morphism fixes every element. -/
theorem quotientAuxiliaryVertexMap_id_apply
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q) (i v : Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] (d : Decidable (v = i))
    (x : RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ i v d) :
    quotientAuxiliaryVertexMap (RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.id ρ) i v d x = x := by
  cases d with
  | isFalse h => rfl
  | isTrue h =>
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun _ => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (ρ.outgoingDirectSumMap i))
      (show ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) ⧸
        LinearMap.range (ρ.outgoingDirectSumMap i)) from x)
    change Submodule.Quotient.mk (outgoingDirectSumMapOfHom _ i y) = Submodule.Quotient.mk y
    rw [outgoingDirectSumMapOfHom_id_apply]

/-- The auxiliary vertex map associated to a composite acts as the successive auxiliary vertex maps. -/

theorem quotientAuxiliaryVertexMap_comp_apply
    {ρ₁ ρ₂ ρ₃ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂)
    (g : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₂ ρ₃) (i v : Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] (d : Decidable (v = i))
    (x : RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ₁ i v d) :
    quotientAuxiliaryVertexMap (f.comp g) i v d x =
      quotientAuxiliaryVertexMap g i v d (quotientAuxiliaryVertexMap f i v d x) := by
  cases d with
  | isFalse h => rfl
  | isTrue h =>
    letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun _ => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun _ => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : ∀ v, AddCommGroup (ρ₃.obj v) := fun _ => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₃.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (ρ₁.outgoingDirectSumMap i))
      (show ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₁.obj a.1)) ⧸
        LinearMap.range (ρ₁.outgoingDirectSumMap i)) from x)
    change Submodule.Quotient.mk (outgoingDirectSumMapOfHom (f.comp g) i y) =
      Submodule.Quotient.mk (outgoingDirectSumMapOfHom g i (outgoingDirectSumMapOfHom f i y))
    rw [outgoingDirectSumMapOfHom_comp_apply]

/-- The auxiliary vertex maps commute with the linear transition maps determined by a comparison datum. -/

theorem quotientAuxiliaryVertexMap_transition
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (a b : Q) (da : Decidable (a = i)) (db : Decidable (b = i))
    (e : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryHomType i a b da db)
    (x : RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ₁ i a da) :
    quotientAuxiliaryVertexMap f i b db
        (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexTransition.{u_k, u_V, u_obj, u_hom} ρ₁ hi a b da db e x) =
      RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexTransition.{u_k, u_V, u_obj, u_hom} ρ₂ hi a b da db e
        (quotientAuxiliaryVertexMap f i a da x) := by
  cases da with
  | isFalse ha =>
    cases db with
    | isFalse hb => exact f.naturality e x
    | isTrue hb =>
      letI : DecidableEq (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) := Classical.decEq _
      letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun _ => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
      letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ₂.obj a.1)) :=
        RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
      exact congrArg Submodule.Quotient.mk (outgoingDirectSumMapOfHom_lof_apply f i _ ⟨a, e⟩ x)
  | isTrue ha =>
    cases db with
    | isFalse hb => exact ((hi b).false e).elim
    | isTrue hb => exact ((hi a).false (show a ⟶ i by exact hb ▸ e)).elim



/-- Away from the distinguished vertex, the auxiliary vertex map agrees with the original component morphism under the comparison equivalences. -/

theorem quotientAuxiliaryVertexMap_ne_compat
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) {i : Q}
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] (v : Q) (hv : v ≠ i)
    (d : Decidable (v = i))
    (x : RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ₁ i v d) :
    RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivOfNe.{u_k, u_V, u_obj, u_hom} ρ₂ v hv d
        (quotientAuxiliaryVertexMap f i v d x) =
      f.app v (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivOfNe.{u_k, u_V, u_obj, u_hom} ρ₁ v hv d x) := by
  cases d with
  | isFalse h => rfl
  | isTrue h => exact absurd h hv

/-- At the distinguished vertex, the auxiliary vertex map agrees with the induced map on outgoing quotients through the comparison equivalences. -/


theorem quotientAuxiliaryVertexMap_self_compat
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) {i : Q}
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] (d : Decidable (i = i))
    (x : RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ₁ i i d) :
    RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivQuotient.{u_k, u_V, u_obj, u_hom} ρ₂ d
        (quotientAuxiliaryVertexMap f i i d x) =
      outgoingQuotientMap f i
        (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivQuotient.{u_k, u_V, u_obj, u_hom} ρ₁ d x) := by
  cases d with
  | isFalse h => exact absurd rfl h
  | isTrue h => rfl

/-- The morphism between quotient-transformed representations induced by a morphism of the original representations. -/

noncomputable def quotientRepresentationMap
    {k : Type u_k} [CommRing k] {Q : Type u_V} [inst : DecidableEq Q] [Quiver.{u_hom} Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i) [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) :
    @RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₁) (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₂) :=
  @RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.mk k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) _ _
    (fun v => quotientAuxiliaryVertexMap f i v (inst v i))
    (fun {a b} e x =>
      quotientAuxiliaryVertexMap_transition f hi a b (inst a i) (inst b i) e x)

/-- The endofunctor on quiver representations arising from the quotient-based transformation at a distinguished vertex. -/
@[source_ref "Chapter6/Definition6.6.4" (role := supporting),
  source_ref "Chapter7/Example7.2.2" (role := supporting)]


noncomputable def quotientRepresentationFunctor
    (k : Type u_k) [CommRing k] (Q : Type u_V) [inst : DecidableEq Q] [Quiver.{u_hom} Q]
    (i : Q) (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i) [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    @CategoryTheory.Functor
      (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q)
      RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.category
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i))
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.category k _ Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)) where
  obj ρ := RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ
  map f := quotientRepresentationMap hi f
  map_id ρ := by
    refine @RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.ext k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      _ _ _ _ (fun v => LinearMap.ext (fun x => ?_))
    exact quotientAuxiliaryVertexMap_id_apply ρ i v (inst v i) x
  map_comp f g := by
    refine @RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.ext k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      _ _ _ _ (fun v => LinearMap.ext (fun x => ?_))
    exact quotientAuxiliaryVertexMap_comp_apply f g i v (inst v i) x

/-- The object assigned by the quotient functor is the corresponding transformed representation. -/
@[simp] theorem quotientRepresentationFunctor_obj
    {k : Type u_k} [CommRing k] {Q : Type u_V} [DecidableEq Q] [Quiver.{u_hom} Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i) [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q) :
    (quotientRepresentationFunctor.{u_k, u_V, u_obj, u_hom} k Q i hi).obj ρ =
      RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ :=
  rfl

/-- The functorial image of a representation morphism is its induced morphism between the quotient-transformed representations. -/
@[simp] theorem quotientRepresentationFunctor_map
    {k : Type u_k} [CommRing k] {Q : Type u_V} [DecidableEq Q] [Quiver.{u_hom} Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i) [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : ρ₁ ⟶ ρ₂) :
    (quotientRepresentationFunctor.{u_k, u_V, u_obj, u_hom} k Q i hi).map f =
      quotientRepresentationMap hi f :=
  rfl

/-- At any other vertex, the induced transformed morphism agrees with the original component through the comparison equivalences. -/

theorem quotientRepresentationMap_of_ne
    {k : Type u_k} [CommRing k] {Q : Type u_V} [inst : DecidableEq Q] [Quiver.{u_hom} Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i) [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (v : Q) (hv : v ≠ i)
    (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₁) v) :
    RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe.{u_k, u_V, u_hom, u_obj} hi ρ₂ v hv
        (@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
          _ _ (quotientRepresentationMap hi f) v x) =
      f.app v (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe.{u_k, u_V, u_hom, u_obj} hi ρ₁ v hv x) :=
  quotientAuxiliaryVertexMap_ne_compat f v hv (inst v i) x

/-- At the distinguished vertex, the induced transformed morphism is compatible with the quotient comparison and the map on outgoing quotients. -/

theorem quotientRepresentationMap_self
    {k : Type u_k} [CommRing k] {Q : Type u_V} [inst : DecidableEq Q] [Quiver.{u_hom} Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i) [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂)
    (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ₁) i) :
    RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient.{u_k, u_V, u_hom, u_obj} hi ρ₂
        (@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
          _ _ (quotientRepresentationMap hi f) i x) =
      outgoingQuotientMap f i
        (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient.{u_k, u_V, u_hom, u_obj} hi ρ₁ x) :=
  quotientAuxiliaryVertexMap_self_compat f (inst i i) x

end RepresentationTheory.QuiverRepresentationQuotientFunctor
