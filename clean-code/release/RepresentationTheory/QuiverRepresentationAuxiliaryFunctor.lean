/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Quiver.LinearRepresentationCategory
import RepresentationTheory.AuxiliaryQuiverRepresentationTransform
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.QuiverRepresentationAuxiliaryFunctor

variable {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]

/-- The linear map between the indexed direct sums obtained by applying a representation morphism on every summand. -/
noncomputable def auxiliaryDirectSumMap {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i : Q) :
    DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₁.obj a.1) →ₗ[k]
      DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₂.obj a.1) := by
  letI : DecidableEq (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) := Classical.decEq _
  exact DirectSum.toModule k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) _
    (fun a => (DirectSum.lof k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i)
      (fun a => ρ₂.obj a.1) a).comp (f.app a.1))

/-- On an element inserted into a single summand, the auxiliary direct-sum map applies the matching component morphism and reinserts the result. -/
theorem auxiliaryDirectSumMap_lof_apply {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i : Q)
    (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (x : ρ₁.obj a.1) :
    letI : DecidableEq (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) := Classical.decEq _
    auxiliaryDirectSumMap f i
        (DirectSum.lof k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₁.obj a.1) a x) =
      DirectSum.lof k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₂.obj a.1) a (f.app a.1 x) := by
  letI : DecidableEq (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) := Classical.decEq _
  delta auxiliaryDirectSumMap
  erw [DirectSum.toModule_lof]
  simp only [LinearMap.coe_comp, Function.comp_apply]

/-- The auxiliary direct-sum map induced by an identity morphism fixes every element. -/
theorem auxiliaryDirectSumMap_id_apply (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) (i : Q)
    (y : DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ.obj a.1)) :
    auxiliaryDirectSumMap (RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.id ρ) i y = y := by
  letI : DecidableEq (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i => ρ.obj a.1) b x =
        DirectSum.lof k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ.obj a.1) b x from rfl,
      auxiliaryDirectSumMap_lof_apply]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

/-- The auxiliary direct-sum map associated to a composite acts by the two induced maps in succession. -/
theorem auxiliaryDirectSumMap_comp_apply {ρ₁ ρ₂ ρ₃ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂)
    (g : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₂ ρ₃) (i : Q)
    (y : DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₁.obj a.1)) :
    auxiliaryDirectSumMap (f.comp g) i y =
      auxiliaryDirectSumMap g i (auxiliaryDirectSumMap f i y) := by
  letI : DecidableEq (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i => ρ₁.obj a.1) b x =
        DirectSum.lof k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₁.obj a.1) b x from rfl,
      auxiliaryDirectSumMap_lof_apply, auxiliaryDirectSumMap_lof_apply, auxiliaryDirectSumMap_lof_apply]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Projecting the auxiliary direct-sum map to one summand amounts to applying the corresponding component of the representation morphism. -/
theorem auxiliaryDirectSumMap_component_apply {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i : Q)
    (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i)
    (y : DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₁.obj a.1)) :
    DirectSum.component k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₂.obj a.1) a
        (auxiliaryDirectSumMap f i y) =
      f.app a.1 (DirectSum.component k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i)
        (fun a => ρ₁.obj a.1) a y) := by
  letI : DecidableEq (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i => ρ₁.obj a.1) b x =
        DirectSum.lof k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₁.obj a.1) b x from rfl,
      auxiliaryDirectSumMap_lof_apply f i b x]
    rcases eq_or_ne b a with rfl | hba
    · rw [DirectSum.component.lof_self, DirectSum.component.lof_self]
    · simp only [DirectSum.component.of, dif_neg hba, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The auxiliary direct-sum map commutes with the structural linear maps and the component of the representation morphism. -/
theorem auxiliaryDirectSumMap_structural {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i : Q)
    (y : DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₁.obj a.1)) :
    ρ₂.auxiliaryDirectSumMap i (auxiliaryDirectSumMap f i y) = f.app i (ρ₁.auxiliaryDirectSumMap i y) := by
  letI : DecidableEq (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i => ρ₁.obj a.1) b x =
        DirectSum.lof k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₁.obj a.1) b x from rfl,
      auxiliaryDirectSumMap_lof_apply f i b x]
    delta RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryDirectSumMap
    erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
    exact (f.naturality b.2 x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The linear map between the kernels of the structural maps induced by a representation morphism at a vertex. -/
noncomputable def auxiliaryKernelMap {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i : Q) :
    ↥(ρ₁.auxiliaryDirectSumMap i).ker →ₗ[k] ↥(ρ₂.auxiliaryDirectSumMap i).ker :=
  LinearMap.restrict (auxiliaryDirectSumMap f i) (q := (ρ₂.auxiliaryDirectSumMap i).ker) (fun x hx => by
    simp only [LinearMap.mem_ker] at hx ⊢
    rw [auxiliaryDirectSumMap_structural f i x, hx, map_zero])

/-- The underlying value of the induced kernel map is the auxiliary direct-sum map applied to the underlying vector. -/
@[simp] theorem auxiliaryKernelMap_coe {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i : Q) (x : ↥(ρ₁.auxiliaryDirectSumMap i).ker) :
    ((auxiliaryKernelMap f i x : ↥(ρ₂.auxiliaryDirectSumMap i).ker) :
        DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ₂.obj a.1)) =
      auxiliaryDirectSumMap f i (x : DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i)
        (fun a => ρ₁.obj a.1)) := rfl

/-- The linear map on an auxiliary vertex module induced by a morphism of quiver representations. -/
noncomputable def auxiliaryVertexMap {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (i v : Q) (d : Decidable (v = i)) :
    letI := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryAddCommMonoid ρ₁ i v d
    letI := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryAddCommMonoid ρ₂ i v d
    letI := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryModule ρ₁ i v d
    letI := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryModule ρ₂ i v d
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliarySpace ρ₁ i v d →ₗ[k] RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliarySpace ρ₂ i v d :=
  @Decidable.casesOn (v = i)
    (fun d =>
      letI := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryAddCommMonoid ρ₁ i v d
      letI := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryAddCommMonoid ρ₂ i v d
      letI := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryModule ρ₁ i v d
      letI := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryModule ρ₂ i v d
      RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliarySpace ρ₁ i v d →ₗ[k] RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliarySpace ρ₂ i v d)
    d
    (fun _ => f.app v)
    (fun _ => auxiliaryKernelMap f i)

/-- The auxiliary vertex map induced by an identity morphism fixes every element. -/
theorem auxiliaryVertexMap_id_apply (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) (i v : Q)
    (d : Decidable (v = i)) (x : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliarySpace ρ i v d) :
    auxiliaryVertexMap (RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.id ρ) i v d x = x := by
  cases d with
  | isFalse h => rfl
  | isTrue h =>
    refine Subtype.ext ?_
    exact auxiliaryDirectSumMap_id_apply ρ i _

/-- The auxiliary vertex map for a composite morphism acts as the successive auxiliary vertex maps. -/
theorem auxiliaryVertexMap_comp_apply {ρ₁ ρ₂ ρ₃ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂)
    (g : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₂ ρ₃) (i v : Q) (d : Decidable (v = i))
    (x : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliarySpace ρ₁ i v d) :
    auxiliaryVertexMap (f.comp g) i v d x =
      auxiliaryVertexMap g i v d (auxiliaryVertexMap f i v d x) := by
  cases d with
  | isFalse h => rfl
  | isTrue h =>
    refine Subtype.ext ?_
    exact auxiliaryDirectSumMap_comp_apply f g i _

/-- Auxiliary vertex maps commute with the transition maps between the associated vertex modules. -/
theorem auxiliaryVertexMap_transition
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (a b : Q) (da : Decidable (a = i)) (db : Decidable (b = i))
    (e : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryHomType i a b da db)
    (x : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliarySpace ρ₁ i a da) :
    auxiliaryVertexMap f i b db (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryLinearMap ρ₁ hi a b da db e x) =
      RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryLinearMap ρ₂ hi a b da db e (auxiliaryVertexMap f i a da x) := by
  cases da with
  | isFalse ha =>
    cases db with
    | isFalse hb => exact f.naturality e x
    | isTrue hb => exact ((hi a).false e).elim
  | isTrue ha =>
    cases db with
    | isFalse hb =>
      exact (auxiliaryDirectSumMap_component_apply f i ⟨b, e⟩ (Subtype.val x)).symm
    | isTrue hb => exact ((hi b).false (ha ▸ e)).elim

/-- Away from the distinguished vertex, the auxiliary vertex map agrees with the corresponding component of the representation morphism under the comparison maps. -/
theorem auxiliaryVertexMap_ne_compat {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) {i : Q} (v : Q) (hv : v ≠ i)
    (d : Decidable (v = i)) (x : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliarySpace ρ₁ i v d) :
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryLinearEquivOfNe ρ₂ v hv d (auxiliaryVertexMap f i v d x) =
      f.app v (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryLinearEquivOfNe ρ₁ v hv d x) := by
  cases d with
  | isFalse h => rfl
  | isTrue h => exact absurd h hv

/-- At the distinguished vertex, the auxiliary vertex map is compatible with the comparison to the induced map between kernels. -/
theorem auxiliaryVertexMap_self_compat {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) {i : Q}
    (d : Decidable (i = i)) (x : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliarySpace ρ₁ i i d) :
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryLinearEquivKernel ρ₂ d (auxiliaryVertexMap f i i d x) =
      auxiliaryKernelMap f i (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryLinearEquivKernel ρ₁ d x) := by
  cases d with
  | isFalse h => exact absurd rfl h
  | isTrue h => rfl

/-- The morphism between auxiliary representations induced by a morphism of the original representations. -/
@[source_ref "Chapter6/Definition6.6.3_maps" (role := supporting)]
noncomputable def auxiliaryRepresentationMap
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) :
    @RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ₁) (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ₂) :=
  @RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.mk k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) _ _
    (fun v => auxiliaryVertexMap f i v (inst v i))
    (fun {a b} e x =>
      auxiliaryVertexMap_transition f hi a b (inst a i) (inst b i) e x)

/-- The endofunctor on quiver representations obtained from the auxiliary construction at a distinguished vertex. -/
@[source_ref "Chapter6/Definition6.6.3" (role := supporting),
  source_ref "Chapter6/Definition6.6.3_maps" (role := primary),
  source_ref "Chapter7/Example7.2.2" (role := primary)]
noncomputable def auxiliaryRepresentationFunctor
    (k : Type*) [CommSemiring k] (Q : Type*) [inst : DecidableEq Q] [Quiver Q]
    (i : Q) (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i) :
    @CategoryTheory.Functor
      (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.category
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i))
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.category k _ Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)) where
  obj ρ := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ
  map f := auxiliaryRepresentationMap hi f
  map_id ρ := by
    refine @RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.ext k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      _ _ _ _ (fun v => LinearMap.ext (fun x => ?_))
    exact auxiliaryVertexMap_id_apply ρ i v (inst v i) x
  map_comp f g := by
    refine @RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.ext k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      _ _ _ _ (fun v => LinearMap.ext (fun x => ?_))
    exact auxiliaryVertexMap_comp_apply f g i v (inst v i) x

/-- The object assigned by the auxiliary functor is the corresponding auxiliary representation. -/
@[simp] theorem auxiliaryRepresentationFunctor_obj
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i) (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) :
    (auxiliaryRepresentationFunctor k Q i hi).obj ρ = RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ :=
  rfl

/-- The functorial action on a representation morphism is the associated auxiliary representation morphism. -/
@[simp] theorem auxiliaryRepresentationFunctor_map
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i) {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : ρ₁ ⟶ ρ₂) :
    (auxiliaryRepresentationFunctor k Q i hi).map f = auxiliaryRepresentationMap hi f :=
  rfl

/-- At any other vertex, the induced auxiliary representation morphism agrees with the original component under the comparison maps. -/
theorem auxiliaryRepresentationMap_of_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i) {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂) (v : Q) (hv : v ≠ i)
    (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ₁) v) :
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ₂ v hv
        (@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
          _ _ (auxiliaryRepresentationMap hi f) v x) =
      f.app v (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ₁ v hv x) := by
  exact auxiliaryVertexMap_ne_compat f v hv (inst v i) x

/-- At the distinguished vertex, the induced auxiliary representation morphism is compatible with the comparison to the kernel map. -/
theorem auxiliaryRepresentationMap_self
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i) {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂)
    (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ₁) i) :
    RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ₂
        (@RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData.app k Q _ (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
          _ _ (auxiliaryRepresentationMap hi f) i x) =
      auxiliaryKernelMap f i (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ₁ x) := by
  exact auxiliaryVertexMap_self_compat f (inst i i) x

end RepresentationTheory.QuiverRepresentationAuxiliaryFunctor
