/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.QuiverVertexPredicates
import RepresentationTheory.QuiverVertexReversal
import Mathlib.Algebra.DirectSum.Module

/-!
# Auxiliary Quiver Representation Transform

Auxiliary constructions on quiver linear diagrams associated with a selected vertex.
-/

namespace RepresentationTheory.AuxiliaryQuiverRepresentationTransform

/-- An auxiliary type associated with a selected vertex of a quiver. -/
def auxiliaryTypeAt (V : Type*) [Quiver V] (i : V) :=
  Σ (j : V), (j ⟶ i)

end RepresentationTheory.AuxiliaryQuiverRepresentationTransform

namespace RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram

/-- A linear map from the displayed direct sum indexed at a vertex to that vertex's module. -/
noncomputable def auxiliaryDirectSumMap
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : QuiverLinearDiagram k Q) (i : Q) :
    DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i)
      (fun a => ρ.obj a.1) →ₗ[k] ρ.obj i := by
  classical
  exact DirectSum.toModule k
    (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i)
    (ρ.obj i) (fun a => ρ.map a.2)

end RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram

namespace RepresentationTheory.AuxiliaryQuiverRepresentationTransform

/-- Heterogeneously equal functions send heterogeneously equal arguments to heterogeneously equal values when their domain and codomain types agree. -/
theorem heq_apply
    {α α' : Sort u} {β β' : Sort v} (hα : α = α') (hβ : β = β')
    {f : α → β} {g : α' → β'} (hf : HEq f g)
    {a : α} {a' : α'} (ha : HEq a a') : HEq (f a) (g a') := by
  subst hα
  subst hβ
  cases ha
  cases hf
  rfl

/-- Heterogeneously equal linear maps have heterogeneously equal underlying functions under the displayed type and structure equalities. -/
theorem heq_coe_linearMap
    {k : Type*} [CommSemiring k]
    {α α' : Type u} {β β' : Type v}
    {acα : AddCommMonoid α} {acβ : AddCommMonoid β}
    {acα' : AddCommMonoid α'} {acβ' : AddCommMonoid β'}
    {mα : @Module k α _ acα} {mβ : @Module k β _ acβ}
    {mα' : @Module k α' _ acα'} {mβ' : @Module k β' _ acβ'}
    (hα : α = α') (hβ : β = β')
    (hacα : HEq acα acα') (hacβ : HEq acβ acβ')
    (hmα : HEq mα mα') (hmβ : HEq mβ mβ')
    {f : @LinearMap k k _ _ (RingHom.id k) α β acα acβ mα mβ}
    {g : @LinearMap k k _ _ (RingHom.id k) α' β' acα' acβ' mα' mβ'}
    (hf : HEq f g) :
    HEq (⇑f) (⇑g) := by
  subst hα
  subst hβ
  cases hacα
  cases hacβ
  cases hmα
  cases hmβ
  cases hf
  rfl

/-- An auxiliary type attached to a representation, a selected vertex, another vertex, and a decision comparing them. -/
def auxiliarySpace
    {k : Type*} [CommSemiring k] {V : Type*} [Quiver V]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k V)
    (i v : V) (d : Decidable (v = i)) : Type _ :=
  @Decidable.casesOn _ (fun _ => Type _) d (fun _ => ρ.obj v)
    (fun _ => ↥(ρ.auxiliaryDirectSumMap i).ker)

/-- An additive commutative monoid structure on the displayed auxiliary type. -/
noncomputable def auxiliaryAddCommMonoid
    {k : Type*} [CommSemiring k] {V : Type*} [Quiver V]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k V)
    (i v : V) (d : Decidable (v = i)) :
    AddCommMonoid (auxiliarySpace ρ i v d) :=
  @Decidable.casesOn _ (fun d => AddCommMonoid (auxiliarySpace ρ i v d)) d
    (fun _ => ρ.addCommMonoid v)
    (fun _ => Submodule.addCommMonoid (ρ.auxiliaryDirectSumMap i).ker)

/-- A module structure on the displayed auxiliary vertex-dependent type. -/
noncomputable def auxiliaryModule
    {k : Type*} [CommSemiring k] {V : Type*} [Quiver V]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k V)
    (i v : V) (d : Decidable (v = i)) :
    @Module k (auxiliarySpace ρ i v d) _ (auxiliaryAddCommMonoid ρ i v d) :=
  @Decidable.casesOn _
    (fun d => @Module k (auxiliarySpace ρ i v d) _ (auxiliaryAddCommMonoid ρ i v d)) d
    (fun _ => ρ.moduleInstance v) (fun _ => Submodule.module (ρ.auxiliaryDirectSumMap i).ker)

/-- An auxiliary type determined by three quiver vertices and decisions comparing two of them with the selected vertex. -/
def auxiliaryHomType
    {V : Type*} [Quiver V] (i a b : V)
    (da : Decidable (a = i)) (db : Decidable (b = i)) : Type _ :=
  @Decidable.casesOn _ (fun _ => Type _) da
    (fun _ => @Decidable.casesOn _ (fun _ => Type _) db
      (fun _ => (a ⟶ b)) (fun _ => (i ⟶ a)))
    (fun _ => @Decidable.casesOn _ (fun _ => Type _) db
      (fun _ => (b ⟶ i)) (fun _ => (a ⟶ b)))

/-- An auxiliary linear map between the displayed vertex-dependent spaces. -/
noncomputable def auxiliaryLinearMap
    {k : Type*} [CommSemiring k] {V : Type*} [Quiver V]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k V)
    {i : V} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty V i) (a b : V)
    (da : Decidable (a = i)) (db : Decidable (b = i)) :
    letI := auxiliaryAddCommMonoid ρ i a da
    letI := auxiliaryAddCommMonoid ρ i b db
    letI := auxiliaryModule ρ i a da
    letI := auxiliaryModule ρ i b db
    auxiliaryHomType i a b da db →
      (auxiliarySpace ρ i a da →ₗ[k] auxiliarySpace ρ i b db) :=
  @Decidable.casesOn (a = i)
    (fun da =>
      letI := auxiliaryAddCommMonoid ρ i a da
      letI := auxiliaryAddCommMonoid ρ i b db
      letI := auxiliaryModule ρ i a da
      letI := auxiliaryModule ρ i b db
      auxiliaryHomType i a b da db →
        (auxiliarySpace ρ i a da →ₗ[k] auxiliarySpace ρ i b db))
    da
    (fun ha_ne => @Decidable.casesOn (b = i)
      (fun db =>
        letI := auxiliaryAddCommMonoid ρ i b db
        letI := auxiliaryModule ρ i b db
        auxiliaryHomType i a b (.isFalse ha_ne) db →
          (ρ.obj a →ₗ[k] auxiliarySpace ρ i b db))
      db
      (fun _hb_ne => fun e => ρ.map e)
      (fun _hb_eq => fun e => ((hi a).false e).elim))
    (fun ha_eq => @Decidable.casesOn (b = i)
      (fun db =>
        letI := auxiliaryAddCommMonoid ρ i a (.isTrue ha_eq)
        letI := auxiliaryAddCommMonoid ρ i b db
        letI := auxiliaryModule ρ i a (.isTrue ha_eq)
        letI := auxiliaryModule ρ i b db
        auxiliaryHomType i a b (.isTrue ha_eq) db →
          (auxiliarySpace ρ i a (.isTrue ha_eq) →ₗ[k] auxiliarySpace ρ i b db))
      db
      (fun _hb_ne => fun e =>
        letI := auxiliaryAddCommMonoid ρ i a (.isTrue ha_eq)
        letI := auxiliaryModule ρ i a (.isTrue ha_eq)
        (DirectSum.component k (auxiliaryTypeAt V i)
          (fun x => ρ.obj x.1) ⟨b, e⟩).comp
          (LinearMap.ker (ρ.auxiliaryDirectSumMap i)).subtype)
      (fun hb_eq => fun e =>
        ((hi b).false (ha_eq ▸ e)).elim))

/-- An auxiliary quiver representation associated with a selected vertex satisfying the displayed predicate. -/
noncomputable def auxiliaryRepresentation
    {k : Type*} [CommSemiring k]
    (V : Type*) [inst : DecidableEq V] [Quiver V]
    (i : V) (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty V i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k V) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k V _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex V i) :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.mk k V _
    (RepresentationTheory.QuiverVertexReversal.reverseAtVertex V i)
    (fun v => auxiliarySpace ρ i v (inst v i))
    (fun v => auxiliaryAddCommMonoid ρ i v (inst v i))
    (fun v => auxiliaryModule ρ i v (inst v i))
    (fun {a b} (e : RepresentationTheory.QuiverVertexReversal.reversedAtHom V i a b) =>
      auxiliaryLinearMap ρ hi a b (inst a i) (inst b i) e)

section AuxiliaryRepresentationAPI

/-- Away from the selected vertex, the auxiliary representation's object agrees with the original representation's object. -/
theorem auxiliaryRepresentation_obj_of_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    (v : Q) (hv : v ≠ i) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (auxiliaryRepresentation Q i hi ρ) v = ρ.obj v := by
  unfold auxiliaryRepresentation auxiliarySpace
  simp only
  match hd : (‹DecidableEq Q› v i) with
  | .isTrue hvi => exact absurd hvi hv
  | .isFalse _ => rw [hd]

/-- At the selected vertex, the auxiliary representation's object is the kernel of the displayed direct-sum map. -/
theorem auxiliaryRepresentation_obj_at
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (auxiliaryRepresentation Q i hi ρ) i = ↥(ρ.auxiliaryDirectSumMap i).ker := by
  unfold auxiliaryRepresentation auxiliarySpace
  simp only
  match hd : (‹DecidableEq Q› i i) with
  | .isTrue _ => rw [hd]
  | .isFalse hii => exact absurd rfl hii

/-- Away from the selected vertex, the auxiliary space is linearly equivalent to the original vertex module. -/
noncomputable def auxiliaryLinearEquivOfNe
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    (v : Q) (hv : v ≠ i) (d : Decidable (v = i)) :
    letI := auxiliaryAddCommMonoid ρ i v d
    letI := auxiliaryModule ρ i v d
    auxiliarySpace ρ i v d ≃ₗ[k] ρ.obj v :=
  @Decidable.casesOn (v = i)
    (fun d =>
      letI := auxiliaryAddCommMonoid ρ i v d
      letI := auxiliaryModule ρ i v d
      auxiliarySpace ρ i v d ≃ₗ[k] ρ.obj v)
    d
    (fun _ => LinearEquiv.refl k (ρ.obj v))
    (fun hvi => absurd hvi hv)

/-- Away from the selected vertex, the auxiliary representation's vertex module is linearly equivalent to the original one. -/
noncomputable def auxiliaryRepresentationLinearEquivOfNe
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    (v : Q) (hv : v ≠ i) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (auxiliaryRepresentation Q i hi ρ) v ≃ₗ[k] ρ.obj v :=
  auxiliaryLinearEquivOfNe ρ v hv (inst v i)

/-- A linear equivalence from the auxiliary space at the selected vertex to the kernel of the displayed direct-sum map. -/
noncomputable def auxiliaryLinearEquivKernel
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {i : Q} (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    (d : Decidable (i = i)) :
    letI := auxiliaryAddCommMonoid ρ i i d
    letI := auxiliaryModule ρ i i d
    auxiliarySpace ρ i i d ≃ₗ[k] ↥(ρ.auxiliaryDirectSumMap i).ker :=
  @Decidable.casesOn (i = i)
    (fun d =>
      letI := auxiliaryAddCommMonoid ρ i i d
      letI := auxiliaryModule ρ i i d
      auxiliarySpace ρ i i d ≃ₗ[k] ↥(ρ.auxiliaryDirectSumMap i).ker)
    d
    (fun hii => absurd rfl hii)
    (fun _ => LinearEquiv.refl k ↥(ρ.auxiliaryDirectSumMap i).ker)

/-- The selected vertex module of the auxiliary representation is linearly equivalent to the kernel of the displayed direct-sum map. -/
noncomputable def auxiliaryRepresentationLinearEquivAt
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (auxiliaryRepresentation Q i hi ρ) i ≃ₗ[k] ↥(ρ.auxiliaryDirectSumMap i).ker :=
  auxiliaryLinearEquivKernel ρ (inst i i)

/-- Maps a quiver morphism between vertices distinct from the selected vertex to the same displayed morphism type. -/
def auxiliaryPreserveHom
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i a b : Q}
    (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a b) : a ⟶ b :=
  cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha hb) e

/-- The auxiliary morphism away from the selected vertex is the displayed cast of the original morphism. -/
theorem auxiliaryPreserveHom_eq_cast
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i a b : Q}
    (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a b) :
    auxiliaryPreserveHom ha hb e =
      cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha hb) e :=
  rfl

set_option maxHeartbeats 1600000 in
/-- For an arrow whose endpoints differ from the selected vertex, the displayed linear equivalences intertwine the auxiliary and original arrow maps. -/
theorem auxiliary_arrow_map_of_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q) {a b : Q}
    (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a b)
    (w : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (auxiliaryRepresentation Q i hi ρ) a) :
    (auxiliaryRepresentationLinearEquivOfNe hi ρ b hb)
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) a b e w) =
    ρ.map (auxiliaryPreserveHom ha hb e)
      ((auxiliaryRepresentationLinearEquivOfNe hi ρ a ha) w) := by
  have h_da : inst a i = .isFalse ha := by
    cases inst a i with | isTrue h => exact absurd h ha | isFalse _ => rfl
  have h_db : inst b i = .isFalse hb := by
    cases inst b i with | isTrue h => exact absurd h hb | isFalse _ => rfl
  have hmap : HEq
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) a b e)
      (ρ.map (auxiliaryPreserveHom ha hb e)) := by
    have hf : HEq
        (auxiliaryLinearMap ρ hi a b (inst a i) (inst b i))
        (auxiliaryLinearMap ρ hi a b (.isFalse ha) (.isFalse hb)) := by
      rw [h_da, h_db]
    have he : HEq e (auxiliaryPreserveHom ha hb e) := by
      rw [auxiliaryPreserveHom_eq_cast ha hb]; exact (cast_heq _ _).symm
    refine heq_apply
      (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha hb) ?_ hf he
    rw [h_da, h_db]
  have heqv : ∀ (v : Q) (hv : v ≠ i),
      HEq (⇑(auxiliaryRepresentationLinearEquivOfNe hi ρ v hv)) (id : ρ.obj v → ρ.obj v) := by
    intro v hv
    have hdv : inst v i = .isFalse hv := by
      cases inst v i with | isTrue h => exact absurd h hv | isFalse _ => rfl
    change HEq (⇑(auxiliaryLinearEquivOfNe ρ v hv (inst v i))) _
    rw [hdv]
    rfl
  have hwa : HEq ((auxiliaryRepresentationLinearEquivOfNe hi ρ a ha) w) w :=
    (heq_apply (auxiliaryRepresentation_obj_of_ne hi ρ a ha) rfl (heqv a ha)
      (cast_heq (auxiliaryRepresentation_obj_of_ne hi ρ a ha) w).symm).trans
      (cast_heq (auxiliaryRepresentation_obj_of_ne hi ρ a ha) w)
  have hac_a : HEq
      (auxiliaryAddCommMonoid ρ i a (inst a i)) (ρ.addCommMonoid a) := by
    rw [h_da]; rfl
  have hac_b : HEq
      (auxiliaryAddCommMonoid ρ i b (inst b i)) (ρ.addCommMonoid b) := by
    rw [h_db]; rfl
  have hmo_a : HEq
      (auxiliaryModule ρ i a (inst a i)) (ρ.moduleInstance a) := by
    rw [h_da]; rfl
  have hmo_b : HEq
      (auxiliaryModule ρ i b (inst b i)) (ρ.moduleInstance b) := by
    rw [h_db]; rfl
  have hmapcoe : HEq
      (⇑(@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) a b e))
      (⇑(ρ.map (auxiliaryPreserveHom ha hb e))) :=
    heq_coe_linearMap
      (auxiliaryRepresentation_obj_of_ne hi ρ a ha)
      (auxiliaryRepresentation_obj_of_ne hi ρ b hb)
      hac_a hac_b hmo_a hmo_b hmap
  have hmapw : HEq
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) a b e w)
      (ρ.map (auxiliaryPreserveHom ha hb e)
        ((auxiliaryRepresentationLinearEquivOfNe hi ρ a ha) w)) :=
    heq_apply (auxiliaryRepresentation_obj_of_ne hi ρ a ha)
      (auxiliaryRepresentation_obj_of_ne hi ρ b hb) hmapcoe hwa.symm
  have hfinal := heq_apply (auxiliaryRepresentation_obj_of_ne hi ρ b hb) rfl (heqv b hb)
    (cast_heq (auxiliaryRepresentation_obj_of_ne hi ρ b hb)
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) a b e w)).symm
  exact eq_of_heq (hfinal.trans
    ((cast_heq (auxiliaryRepresentation_obj_of_ne hi ρ b hb)
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) a b e w)).trans hmapw))

/-- Maps a quiver morphism from the selected vertex to a distinct vertex to a morphism in the reverse direction. -/
def auxiliaryReverseHom
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i b : Q}
    (hb : b ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i b) : b ⟶ i :=
  cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne rfl hb) e

/-- The auxiliary reverse-direction morphism is the displayed cast of the original morphism. -/
theorem auxiliaryReverseHom_eq_cast
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i b : Q}
    (hb : b ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i b) :
    auxiliaryReverseHom hb e =
      cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne rfl hb) e :=
  rfl

set_option maxHeartbeats 1600000 in
/-- After the displayed linear equivalences, an arrow map from the selected vertex is the indicated direct-sum component of the kernel inclusion. -/
theorem auxiliary_arrow_map_from_selected
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q) {b : Q}
    (hb : b ≠ i)
    (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i b)
    (w : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (auxiliaryRepresentation Q i hi ρ) i) :
    (auxiliaryRepresentationLinearEquivOfNe hi ρ b hb)
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) i b e w) =
    (DirectSum.component k (auxiliaryTypeAt Q i) (fun x => ρ.obj x.1)
      ⟨b, auxiliaryReverseHom hb e⟩)
      ((ρ.auxiliaryDirectSumMap i).ker.subtype
        ((auxiliaryRepresentationLinearEquivAt hi ρ) w)) := by
  have h_da : inst i i = .isTrue rfl := by
    cases inst i i with
    | isTrue _ => rfl
    | isFalse h => exact absurd rfl h
  have h_db : inst b i = .isFalse hb := by
    cases inst b i with
    | isTrue h => exact absurd h hb
    | isFalse _ => rfl
  set RHSmap :=
    (DirectSum.component k (auxiliaryTypeAt Q i) (fun x => ρ.obj x.1)
      ⟨b, auxiliaryReverseHom hb e⟩).comp
      (ρ.auxiliaryDirectSumMap i).ker.subtype with hRHS
  have hmap : HEq
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) i b e)
      RHSmap := by
    have hf : HEq
        (auxiliaryLinearMap ρ hi i b (inst i i) (inst b i))
        (auxiliaryLinearMap ρ hi i b (.isTrue rfl) (.isFalse hb)) := by
      rw [h_da, h_db]
    have he : HEq e (auxiliaryReverseHom hb e) := by
      rw [auxiliaryReverseHom_eq_cast hb]; exact (cast_heq _ _).symm
    refine heq_apply
      (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne rfl hb) ?_ hf he
    rw [h_da, h_db]
  have heqve : HEq (⇑(auxiliaryRepresentationLinearEquivAt hi ρ))
      (id : ↥(ρ.auxiliaryDirectSumMap i).ker → ↥(ρ.auxiliaryDirectSumMap i).ker) := by
    have h_ii : inst i i = .isTrue rfl := by
      cases inst i i with | isTrue _ => rfl | isFalse h => exact absurd rfl h
    change HEq (⇑(auxiliaryLinearEquivKernel ρ (inst i i))) _
    rw [h_ii]
    rfl
  have hwe : HEq ((auxiliaryRepresentationLinearEquivAt hi ρ) w) w :=
    (heq_apply (auxiliaryRepresentation_obj_at hi ρ) rfl (heqve)
      (cast_heq (auxiliaryRepresentation_obj_at hi ρ) w).symm).trans
      (cast_heq (auxiliaryRepresentation_obj_at hi ρ) w)
  have hac_i : HEq
      (auxiliaryAddCommMonoid ρ i i (inst i i))
      (Submodule.addCommMonoid (ρ.auxiliaryDirectSumMap i).ker) := by
    rw [h_da]; rfl
  have hac_b : HEq
      (auxiliaryAddCommMonoid ρ i b (inst b i)) (ρ.addCommMonoid b) := by
    rw [h_db]; rfl
  have hmo_i : HEq
      (auxiliaryModule ρ i i (inst i i))
      (Submodule.module (ρ.auxiliaryDirectSumMap i).ker) := by
    rw [h_da]; rfl
  have hmo_b : HEq
      (auxiliaryModule ρ i b (inst b i)) (ρ.moduleInstance b) := by
    rw [h_db]; rfl
  have hmapcoe : HEq
      (⇑(@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) i b e))
      (⇑RHSmap) :=
    heq_coe_linearMap
      (auxiliaryRepresentation_obj_at hi ρ)
      (auxiliaryRepresentation_obj_of_ne hi ρ b hb)
      hac_i hac_b hmo_i hmo_b hmap
  have hmapw : HEq
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) i b e w)
      (RHSmap ((auxiliaryRepresentationLinearEquivAt hi ρ) w)) :=
    heq_apply (auxiliaryRepresentation_obj_at hi ρ)
      (auxiliaryRepresentation_obj_of_ne hi ρ b hb) hmapcoe hwe.symm
  have heqv : ∀ (v : Q) (hv : v ≠ i),
      HEq (⇑(auxiliaryRepresentationLinearEquivOfNe hi ρ v hv)) (id : ρ.obj v → ρ.obj v) := by
    intro v hv
    have hdv : inst v i = .isFalse hv := by
      cases inst v i with | isTrue h => exact absurd h hv | isFalse _ => rfl
    change HEq (⇑(auxiliaryLinearEquivOfNe ρ v hv (inst v i))) _
    rw [hdv]
    rfl
  have hfinal := heq_apply (auxiliaryRepresentation_obj_of_ne hi ρ b hb) rfl (heqv b hb)
    (cast_heq (auxiliaryRepresentation_obj_of_ne hi ρ b hb)
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) i b e w)).symm
  exact eq_of_heq (hfinal.trans
    ((cast_heq (auxiliaryRepresentation_obj_of_ne hi ρ b hb)
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (auxiliaryRepresentation Q i hi ρ) i b e w)).trans hmapw))

end AuxiliaryRepresentationAPI

end RepresentationTheory.AuxiliaryQuiverRepresentationTransform
