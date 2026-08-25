/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.QuiverVertexPredicates
import RepresentationTheory.QuiverVertexReversal
import RepresentationTheory.AuxiliaryQuiverRepresentationTransform
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Defs



universe u_k u_V u_obj u_hom


/-- The type indexing arrows whose source is a specified vertex of a quiver. -/
def RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (V : Type*) [Quiver V] (i : V) :=
  Σ (j : V), (i ⟶ j)


/-- A module over a commutative ring carries an additive commutative group structure. -/
@[reducible]
noncomputable def RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing {k : Type*} [CommRing k] {M : Type*}
    [inst : AddCommMonoid M] [Module k M] : AddCommGroup M :=
  Module.addCommMonoidToAddCommGroup k


/-- The linear map from the module at a vertex to the direct sum of the modules reached by its outgoing arrows. -/
noncomputable def RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap
    {k : Type*} [CommRing k] {Q : Type*} [Quiver Q]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) (i : Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    ρ.obj i →ₗ[k] DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1) := by
  classical
  exact ∑ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i,
    (DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1) a).comp
      (ρ.map a.2)


/-- The vertex space used by the quotient-based auxiliary construction, selected according to equality with a distinguished vertex. -/
def RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex
    {k : Type u_k} [CommRing k] {V : Type u_V} [Quiver.{u_hom} V]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k V) (i v : V)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i)] (d : Decidable (v = i)) :
    Type (max u_V u_obj u_hom) :=
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  @Decidable.casesOn _ (fun _ => Type (max u_V u_obj u_hom)) d
    (fun _ => ρ.obj v)
    (fun _ =>
      (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i) (fun a => ρ.obj a.1)) ⧸
        LinearMap.range (ρ.outgoingDirectSumMap i))


/-- The auxiliary vertex space has a canonical additive commutative monoid structure. -/
noncomputable def RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid
    {k : Type u_k} [CommRing k] {V : Type u_V} [Quiver.{u_hom} V]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k V) (i v : V)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i)] (d : Decidable (v = i)) :
    AddCommMonoid (RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ i v d) :=
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  @Decidable.casesOn _
    (fun d => AddCommMonoid (RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ i v d)) d
    (fun _ => ρ.addCommMonoid v)
    (fun _ => Submodule.Quotient.addCommGroup (p := LinearMap.range (ρ.outgoingDirectSumMap i))
      |>.toAddCommMonoid)


/-- The auxiliary vertex space has a canonical module structure over the coefficient ring. -/
noncomputable def RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule
    {k : Type u_k} [CommRing k] {V : Type u_V} [Quiver.{u_hom} V]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k V) (i v : V)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i)] (d : Decidable (v = i)) :
    @Module k (RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ i v d) _
      (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid.{u_k, u_V, u_obj, u_hom} ρ i v d) :=
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  @Decidable.casesOn _
    (fun d => @Module k (RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ i v d) _
      (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ i v d)) d
    (fun _ => ρ.moduleInstance v)
    (fun _ => Submodule.Quotient.module (LinearMap.range (ρ.outgoingDirectSumMap i)))


/-- A comparison datum between vertex cases induces a linear map between the corresponding auxiliary vertex spaces. -/
noncomputable def RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexTransition
    {k : Type u_k} [CommRing k] {V : Type u_V} [Quiver.{u_hom} V]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k V) {i : V}
    (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition V i)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i)] (a b : V)
    (da : Decidable (a = i)) (db : Decidable (b = i)) :
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid.{u_k, u_V, u_obj, u_hom} ρ i a da
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid.{u_k, u_V, u_obj, u_hom} ρ i b db
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule.{u_k, u_V, u_obj, u_hom} ρ i a da
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule.{u_k, u_V, u_obj, u_hom} ρ i b db
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryHomType i a b da db →
      (RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ i a da →ₗ[k]
        RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ i b db) :=
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : DecidableEq (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i) := Classical.decEq _
  @Decidable.casesOn (a = i)
    (fun da =>
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ i a da
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ i b db
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ i a da
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ i b db
      RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryHomType i a b da db →
        (RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ i a da →ₗ[k]
          RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ i b db))
    da
    (fun ha_ne => @Decidable.casesOn (b = i)
      (fun db =>
        letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ i b db
        letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ i b db
        RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryHomType i a b (.isFalse ha_ne) db →
          (ρ.obj a →ₗ[k] RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ i b db))
      db
      (fun _hb_ne => fun e => ρ.map e)
      (fun _hb_eq => fun e =>
        (Submodule.mkQ (LinearMap.range (ρ.outgoingDirectSumMap i))).comp
          (DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i) (fun a => ρ.obj a.1) ⟨a, e⟩)))
    (fun ha_eq => @Decidable.casesOn (b = i)
      (fun db =>
        letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ i a (.isTrue ha_eq)
        letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ i b db
        letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ i a (.isTrue ha_eq)
        letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ i b db
        RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryHomType i a b (.isTrue ha_eq) db →
          (RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ i a (.isTrue ha_eq) →ₗ[k]
            RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ i b db))
      db
      (fun _hb_ne => fun e => ((hi b).false e).elim)
      (fun hb_eq => fun e => ((hi a).false (show a ⟶ i by exact hb_eq ▸ e)).elim))


/-- The quiver representation obtained by replacing the distinguished vertex space with a quotient of the outgoing direct sum. -/
noncomputable def RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation
    {k : Type*} [CommRing k]
    (V : Type*) [inst : DecidableEq V] [Quiver V]
    (i : V) (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition V i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k V)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i)] :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k V _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex V i) :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.mk k V _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex V i)
    (fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex ρ i v (inst v i))
    (fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ i v (inst v i))
    (fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ i v (inst v i))
    (fun {a b} (e : RepresentationTheory.QuiverVertexReversal.reversedAtHom V i a b) =>
      RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexTransition ρ hi a b (inst a i) (inst b i) e)

section ReflectionFunctorMinusAPI




/-- The transformed space at a vertex distinct from the distinguished one is the original representation space there. -/
theorem RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (v : Q) (hv : v ≠ i) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) v = ρ.obj v := by
  unfold RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex
  simp only []
  match hd : (‹DecidableEq Q› v i) with
  | .isTrue hvi => exact absurd hvi hv
  | .isFalse _ => rw [hd]


/-- The transformed space at the distinguished vertex is the outgoing direct sum modulo the range of the outgoing structural map. -/
theorem RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) i =
    ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) ⧸
      LinearMap.range (ρ.outgoingDirectSumMap i)) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  unfold RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex
  simp only []
  match hd : (‹DecidableEq Q› i i) with
  | .isTrue _ => rw [hd]
  | .isFalse hii => exact absurd rfl hii


/-- Away from the distinguished vertex, the auxiliary vertex space is linearly equivalent to the original representation space. -/
noncomputable def RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivOfNe
    {k : Type u_k} [CommRing k] {Q : Type u_V} [Quiver.{u_hom} Q]
    {i : Q} (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (v : Q) (hv : v ≠ i) (d : Decidable (v = i)) :
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid.{u_k, u_V, u_obj, u_hom} ρ i v d
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule.{u_k, u_V, u_obj, u_hom} ρ i v d
    RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ i v d ≃ₗ[k] ρ.obj v :=
  @Decidable.casesOn (v = i)
    (fun d =>
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid.{u_k, u_V, u_obj, u_hom} ρ i v d
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule.{u_k, u_V, u_obj, u_hom} ρ i v d
      RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ i v d ≃ₗ[k] ρ.obj v)
    d
    (fun _ => LinearEquiv.refl k (ρ.obj v))
    (fun hvi => absurd hvi hv)


/-- At every other vertex, the transformed representation is linearly equivalent to the original representation. -/
noncomputable def RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (v : Q) (hv : v ≠ i) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) v ≃ₗ[k] ρ.obj v :=
  RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivOfNe ρ v hv (inst v i)


/-- At the distinguished vertex, the auxiliary vertex space is linearly equivalent to the outgoing direct sum modulo the range of its structural map. -/
noncomputable def RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivQuotient
    {k : Type u_k} [CommRing k] {Q : Type u_V} [Quiver.{u_hom} Q]
    {i : Q} (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] (d : Decidable (i = i)) :
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid.{u_k, u_V, u_obj, u_hom} ρ i i d
    letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule.{u_k, u_V, u_obj, u_hom} ρ i i d
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ i i d ≃ₗ[k]
      (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) ⧸
        LinearMap.range (ρ.outgoingDirectSumMap i) :=
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  @Decidable.casesOn (i = i)
    (fun d =>
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid.{u_k, u_V, u_obj, u_hom} ρ i i d
      letI := RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule.{u_k, u_V, u_obj, u_hom} ρ i i d
      RepresentationTheory.QuiverRepresentationQuotientTransform.AuxiliaryVertex.{u_k, u_V, u_obj, u_hom} ρ i i d ≃ₗ[k]
        (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) ⧸
          LinearMap.range (ρ.outgoingDirectSumMap i))
    d
    (fun hii => absurd rfl hii)
    (fun _ => LinearEquiv.refl k
      ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) ⧸
        LinearMap.range (ρ.outgoingDirectSumMap i)))


/-- The transformed representation at the distinguished vertex is linearly equivalent to the quotient of the outgoing direct sum by the structural range. -/
noncomputable def RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) i ≃ₗ[k]
    (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) ⧸
      LinearMap.range (ρ.outgoingDirectSumMap i) :=
  RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivQuotient ρ (inst i i)


/-- Under the distinguished-vertex hypothesis, the source of an indexed incoming arrow differs from that vertex. -/
theorem RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (a : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i) : a.fst ≠ i := by
  obtain ⟨j, e⟩ := a
  intro heq; dsimp only at heq
  change RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i j i at e
  rw [RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq heq rfl] at e
  exact (hi j).false (show j ⟶ i from e)


/-- Constructs an arrow from the distinguished vertex to the source of an indexed incoming arrow. -/
def RepresentationTheory.QuiverRepresentationQuotientTransform.reverseIndexedIncomingArrow
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (a : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i) : i ⟶ a.fst := by
  obtain ⟨j, e⟩ := a
  change RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i j i at e
  have hne := RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne hi ⟨j, e⟩
  rw [RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq hne rfl] at e; exact e

set_option maxHeartbeats 1600000 in
-- reason: unfolding reflectionFunctorMinus + equivAt_ne + match reduction

/-- For an arrow between vertices distinct from the distinguished one, the transformed action agrees with the original action through the comparison equivalences. -/
theorem RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_of_ne
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    {a b : Q} (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a b)
    (w : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a) :
    (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ b hb)
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a b e w) =
    ρ.map (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom ha hb e)
      ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a ha) w) := by
  have h_da : inst a i = .isFalse ha := by
    cases inst a i with | isTrue h => exact absurd h ha | isFalse _ => rfl
  have h_db : inst b i = .isFalse hb := by
    cases inst b i with | isTrue h => exact absurd h hb | isFalse _ => rfl
  -- (1) Function-level HEq of `mapAt` at the live discriminants vs. at the literal `isFalse`
  -- branch, where the map iota-reduces to `ρ.map`.
  have hmap : HEq
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a b e)
      (ρ.map (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom ha hb e)) := by
    have hf : HEq
        (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexTransition ρ hi a b (inst a i) (inst b i))
        (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexTransition ρ hi a b (.isFalse ha) (.isFalse hb)) := by
      rw [h_da, h_db]
    have he : HEq e (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom ha hb e) := by
      rw [RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom_eq_cast ha hb]; exact (cast_heq _ _).symm
    refine RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_apply (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha hb) ?_ hf he
    rw [h_da, h_db]
  -- (2) `equivAt_ne` is heterogeneously the identity (function level, via the parametrized
  -- `equivAtAt_ne` and `rw` on the discriminant).
  have heqv : ∀ (v : Q) (hv : v ≠ i),
      HEq (⇑(RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv)) (id : ρ.obj v → ρ.obj v) := by
    intro v hv
    have hdv : inst v i = .isFalse hv := by
      cases inst v i with | isTrue h => exact absurd h hv | isFalse _ => rfl
    change HEq (⇑(RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivOfNe ρ v hv (inst v i))) _
    rw [hdv]
    rfl
  -- (3) Instance HEqs relating `hmap` to the HEq of coercions.
  have hac_a : HEq
      (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ i a (inst a i)) (ρ.addCommMonoid a) := by
    rw [h_da]; rfl
  have hac_b : HEq
      (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ i b (inst b i)) (ρ.addCommMonoid b) := by
    rw [h_db]; rfl
  have hmo_a : HEq
      (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ i a (inst a i)) (ρ.moduleInstance a) := by
    rw [h_da]; rfl
  have hmo_b : HEq
      (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ i b (inst b i)) (ρ.moduleInstance b) := by
    rw [h_db]; rfl
  have hmapcoe : HEq
      (⇑(@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a b e))
      (⇑(ρ.map (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom ha hb e))) :=
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_coe_linearMap
      (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ a ha)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ b hb)
      hac_a hac_b hmo_a hmo_b hmap
  -- (4) Assemble via HEq congruence.
  have hwa : HEq ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a ha) w) w :=
    (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_apply (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ a ha) rfl (heqv a ha)
      (cast_heq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ a ha) w).symm).trans
      (cast_heq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ a ha) w)
  have hmapw : HEq
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a b e w)
      (ρ.map (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom ha hb e)
        ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a ha) w)) :=
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_apply (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ a ha)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ b hb) hmapcoe hwa.symm
  have hfinal := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_apply (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ b hb) rfl (heqv b hb)
    (cast_heq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ b hb)
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a b e w)).symm
  exact eq_of_heq (hfinal.trans ((cast_heq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ b hb)
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a b e w)).trans hmapw))


/-- Turns an arrow into a distinguished vertex into an arrow from that vertex to the original source. -/
def RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i a : Q}
    (ha : a ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a i) : i ⟶ a :=
  -- Defined directly as the `cast` along the type-equality lemma; see `reversedArrow_ne_ne`.
  cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq ha rfl) e


/-- The reversed arrow at a distinct vertex is the original arrow transported to the corresponding hom type. -/
theorem RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex_eq_cast
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i a : Q}
    (ha : a ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a i) :
    RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex ha e =
      cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq ha rfl) e :=
  -- `reversedArrow_ne_eq` is now *defined* as this cast.
  rfl


/-- The linear map from the outgoing direct sum to the transformed space at the distinguished vertex. -/
noncomputable def RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1) →ₗ[k]
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) i := by
  -- Need AddCommGroup for Submodule.mkQ
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  -- Build the quotient map via the `equivAt_eq` equivalence (which reduces the
  -- discriminant cleanly), avoiding a discriminant `match` that desyncs the carrier
  -- from its module instances.
  exact (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).symm.toLinearMap ∘ₗ
    Submodule.mkQ (LinearMap.range (ρ.outgoingDirectSumMap i))

open Classical in
set_option maxHeartbeats 800000 in -- unfolding reflFunctorMinus_mkQ + reflectionFunctorMinus + match reduction

/-- The transformed quotient map annihilates the sum of the outgoing-arrow images of an element at the distinguished vertex. -/
theorem RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap_sum_eq_zero
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (v : ρ.obj i) :
    RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ
      (∑ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i,
        (DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1) a)
          (ρ.map a.2 v)) = 0 := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  -- `mkQ = equivAt_eq.symm ∘ₗ Submodule.mkQ`, so it suffices that the quotient class of
  -- the source-map image is zero, i.e. the argument lies in `range (sourceMap i)`.
  have hz : Submodule.mkQ (LinearMap.range (ρ.outgoingDirectSumMap i))
      (∑ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i,
        (DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1) a)
          (ρ.map a.2 v)) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨v, by simp [RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap, LinearMap.sum_apply,
      LinearMap.comp_apply]⟩
  unfold RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap
  rw [LinearMap.comp_apply, hz, map_zero]

open Classical in
set_option maxHeartbeats 1600000 in
-- reason: unfolding reflectionFunctorMinus + equivAt_ne + mkQ + match reduction

/-- The transformed action of an arrow ending at the distinguished vertex is the quotient map applied to the summand determined by the reversed arrow. -/
theorem RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_to_distinguished
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    {a : Q} (ha : a ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a i)
    (w : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a i e w =
    (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ)
      (DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)
        (fun a => ρ.obj a.1) ⟨a, RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex ha e⟩
        ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a ha) w)) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  have h_da : inst a i = .isFalse ha := by
    cases inst a i with | isTrue h => exact absurd h ha | isFalse _ => rfl
  have h_di : inst i i = .isTrue rfl := by
    cases inst i i with | isTrue _ => rfl | isFalse h => exact absurd rfl h
  -- The target linear map of the F⁻ map at (a ≠ i, b = i): injection into the `a`-component
  -- of the direct sum followed by the quotient map `mkQ`.
  set RHSmap :=
    (Submodule.mkQ (LinearMap.range (ρ.outgoingDirectSumMap i))).comp
      (DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)
        ⟨a, RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex ha e⟩) with hRHS
  -- (1) Function-level HEq of `mapAt` at the live discriminants vs. at the literal
  -- `(isFalse, isTrue)` branch, where the map iota-reduces to `RHSmap`.
  have hmap : HEq
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a i e)
      RHSmap := by
    have hf : HEq
        (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexTransition ρ hi a i (inst a i) (inst i i))
        (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexTransition ρ hi a i (.isFalse ha) (.isTrue rfl)) := by
      rw [h_da, h_di]
    have he : HEq e (RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex ha e) := by
      rw [RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex_eq_cast ha]; exact (cast_heq _ _).symm
    refine RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_apply (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq ha rfl) ?_ hf he
    rw [h_da, h_di]
  -- (2) `equivAt_ne` is heterogeneously the identity on `ρ.obj a`.
  have heqv : ∀ (v : Q) (hv : v ≠ i),
      HEq (⇑(RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv)) (id : ρ.obj v → ρ.obj v) := by
    intro v hv
    have hdv : inst v i = .isFalse hv := by
      cases inst v i with | isTrue h => exact absurd h hv | isFalse _ => rfl
    change HEq (⇑(RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivOfNe ρ v hv (inst v i))) _
    rw [hdv]
    rfl
  have hwa : HEq ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a ha) w) w :=
    (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_apply (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ a ha) rfl (heqv a ha)
      (cast_heq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ a ha) w).symm).trans
      (cast_heq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ a ha) w)
  -- (3) Instance HEqs relating `hmap` to the HEq of coercions.
  have hac_a : HEq
      (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ i a (inst a i)) (ρ.addCommMonoid a) := by
    rw [h_da]; rfl
  have hac_i : HEq
      (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexAddCommMonoid ρ i i (inst i i))
      (Submodule.Quotient.addCommGroup (p := LinearMap.range (ρ.outgoingDirectSumMap i))).toAddCommMonoid := by
    rw [h_di]; rfl
  have hmo_a : HEq
      (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ i a (inst a i)) (ρ.moduleInstance a) := by
    rw [h_da]; rfl
  have hmo_i : HEq
      (RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexModule ρ i i (inst i i))
      (Submodule.Quotient.module (LinearMap.range (ρ.outgoingDirectSumMap i))) := by
    rw [h_di]; rfl
  have hmapcoe : HEq
      (⇑(@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a i e))
      (⇑RHSmap) :=
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_coe_linearMap
      (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ a ha)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient hi ρ)
      hac_a hac_i hmo_a hmo_i hmap
  -- (4) Apply the coercion-HEq to the transported input.
  have hmapw : HEq
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a i e w)
      (RHSmap ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a ha) w)) :=
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_apply (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_of_ne_eq hi ρ a ha)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient hi ρ) hmapcoe hwa.symm
  -- (5) `equivAt_eq.symm` is heterogeneously the identity on `coker(sourceMap i)`; combine.
  -- `equivAt_eq` is heterogeneously the identity (forward map, via the parametrized
  -- `equivAtAt_eq` and `rw` on the discriminant). Mirror of `heqve` in the Plus template.
  have hfwd : HEq (⇑(RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ))
      (id : ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) ⧸
        LinearMap.range (ρ.outgoingDirectSumMap i)) →
        ((DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) ⧸
          LinearMap.range (ρ.outgoingDirectSumMap i))) := by
    change HEq (⇑(RepresentationTheory.QuiverRepresentationQuotientTransform.auxiliaryVertexEquivQuotient ρ (inst i i))) _
    rw [h_di]
    rfl
  -- The RHS of the goal, `reflFunctorMinus_mkQ (lof ...)`, equals `equivAt_eq.symm (mkQ (lof ...))`.
  have hRHSeq : (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ)
      (DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)
        ⟨a, RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex ha e⟩
        ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a ha) w)) =
      (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).symm
        (RHSmap ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a ha) w)) := by
    rw [hRHS]
    unfold RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hRHSeq]
  -- `equivAt_eq.symm q ≅ q`, and `mapLinear ... e w ≅ q`; conclude by `eq_of_heq`.
  -- For `x := equivAt_eq.symm q : F⁻ᵢ(ρ).obj i`, the forward map is heterogeneously the
  -- identity, so `equivAt_eq x ≅ x`, i.e. `q ≅ x` (since `equivAt_eq x = q`).
  set x := (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).symm
    (RHSmap ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a ha) w)) with hx
  have hxq : HEq ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ) x) x :=
    (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.heq_apply (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient hi ρ) rfl hfwd
      (cast_heq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient hi ρ) x).symm).trans
      (cast_heq (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertex_self_eq_quotient hi ρ) x)
  have hqx : (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ) x =
      RHSmap ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a ha) w) := by
    rw [hx, LinearEquiv.apply_symm_apply]
  rw [hqx] at hxq
  exact eq_of_heq (hmapw.trans hxq)


end ReflectionFunctorMinusAPI
