/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.AuxiliaryPathStructures
import RepresentationTheory.CategoryTheory.QuiverLinearMaps
import RepresentationTheory.Alignment.Attribute
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.DirectSum.Module

open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
open RepresentationTheory.CategoryTheory.QuiverLinearMaps

namespace RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]

/-- The algebra idempotent associated with a vertex. -/
noncomputable def vertexIdempotent (i : Q) : AuxiliaryPathType k Q :=
  auxiliaryOfPath ⟨i, i, Quiver.Path.nil⟩

/-- A vertex idempotent is the unit coefficient supported on the empty path at that vertex. -/
theorem vertexIdempotent_eq_single_nil (i : Q) :
    (vertexIdempotent i : AuxiliaryPathType k Q) = Finsupp.single ⟨i, i, Quiver.Path.nil⟩ 1 :=
  rfl

/-- Left multiplication by a vertex idempotent selects paths starting at that vertex. -/
theorem vertexIdempotent_mul_pathElement (i a b : Q) (p : Quiver.Path a b) :
    (vertexIdempotent i : AuxiliaryPathType k Q) * auxiliaryOfPath ⟨a, b, p⟩
      = if i = a then auxiliaryOfPath ⟨a, b, p⟩ else 0 := by
  change (@HMul.hMul (AuxiliaryPathType k Q) (AuxiliaryPathType k Q) (AuxiliaryPathType k Q) _
      (Finsupp.single ⟨i, i, Quiver.Path.nil⟩ 1) (Finsupp.single ⟨a, b, p⟩ 1)) =
    if i = a then Finsupp.single ⟨a, b, p⟩ 1 else 0
  rw [single_mul_single, one_mul, one_smul, auxiliaryProduct_vertexPath]

/-- Right multiplication of a path element by a vertex idempotent selects its target vertex. -/
theorem pathElement_mul_vertexIdempotent (a b i : Q) (p : Quiver.Path a b) :
    (auxiliaryOfPath ⟨a, b, p⟩ : AuxiliaryPathType k Q) * vertexIdempotent i
      = if b = i then auxiliaryOfPath ⟨a, b, p⟩ else 0 := by
  change (@HMul.hMul (AuxiliaryPathType k Q) (AuxiliaryPathType k Q) (AuxiliaryPathType k Q) _
      (Finsupp.single ⟨a, b, p⟩ 1) (Finsupp.single ⟨i, i, Quiver.Path.nil⟩ 1)) =
    if b = i then Finsupp.single ⟨a, b, p⟩ 1 else 0
  rw [single_mul_single, mul_one, one_smul, auxiliaryProduct_pathVertex]

/-- Each vertex idempotent is idempotent. -/
theorem vertexIdempotent_mul_self (i : Q) :
    (vertexIdempotent i : AuxiliaryPathType k Q) * vertexIdempotent i = vertexIdempotent i := by
  have h := vertexIdempotent_mul_pathElement (k := k) i i i Quiver.Path.nil
  rw [if_pos rfl] at h
  exact h

/-- Idempotents belonging to distinct vertices multiply to zero. -/
theorem vertexIdempotent_mul_eq_zero {i j : Q} (h : i ≠ j) :
    (vertexIdempotent i : AuxiliaryPathType k Q) * vertexIdempotent j = 0 := by
  have h2 := vertexIdempotent_mul_pathElement (k := k) i j j Quiver.Path.nil
  rw [if_neg h] at h2
  exact h2

/-- The product of two vertex idempotents is the first when their vertices agree and zero otherwise. -/
theorem vertexIdempotent_mul (i j : Q) :
    (vertexIdempotent i : AuxiliaryPathType k Q) * vertexIdempotent j = if i = j then vertexIdempotent i else 0 := by
  by_cases h : i = j
  · subst h; rw [vertexIdempotent_mul_self, if_pos rfl]
  · rw [vertexIdempotent_mul_eq_zero h, if_neg h]

/-- The reversed-composition algebra element associated with a quiver arrow. -/
noncomputable def arrowElement {i j : Q} (e : i ⟶ j) : AuxiliaryPathType k Q :=
  auxiliaryOfPath ⟨i, j, e.toPath⟩

/-- Left multiplication of an arrow element by its source idempotent leaves it unchanged. -/
theorem vertexIdempotent_mul_arrowElement {i j : Q} (e : i ⟶ j) :
    (vertexIdempotent i : AuxiliaryPathType k Q) * arrowElement e = arrowElement e := by
  have h := vertexIdempotent_mul_pathElement (k := k) i i j e.toPath
  rw [if_pos rfl] at h
  exact h

/-- An arrow element multiplied on the right by its target idempotent is unchanged. -/
theorem arrowElement_mul_targetIdempotent {i j : Q} (e : i ⟶ j) :
    (arrowElement e : AuxiliaryPathType k Q) * vertexIdempotent j = arrowElement e := by
  have h := pathElement_mul_vertexIdempotent (k := k) i j j e.toPath
  rw [if_pos rfl] at h
  exact h

/-- The sum of all vertex idempotents is one in the reversed-composition algebra. -/
theorem sum_vertexIdempotent_eq_one [Fintype Q] : (∑ i, vertexIdempotent i : AuxiliaryPathType k Q) = 1 := by
  simp only [vertexIdempotent]
  exact sum_vertexPath_eq_one k Q

/-- The vertex elements form a complete orthogonal family of idempotents. -/
theorem vertexIdempotents_completeOrthogonal [Fintype Q] :
    CompleteOrthogonalIdempotents (vertexIdempotent (k := k) (Q := Q)) where
  idem i := vertexIdempotent_mul_self i
  ortho := fun {_i _j} hij => vertexIdempotent_mul_eq_zero hij
  complete := sum_vertexIdempotent_eq_one

section ModuleDecomposition

variable [Fintype Q] {V : Type*} [AddCommMonoid V] [Module k V]
  [Module (AuxiliaryPathType k Q) V] [IsScalarTower k (AuxiliaryPathType k Q) V]

/-- The reversed-composition algebra action as an algebra homomorphism into scalar-linear endomorphisms. -/
noncomputable def actionAlgHom : AuxiliaryPathType k Q →ₐ[k] Module.End k V :=
  Algebra.lsmul k k V

/-- Evaluation of the reversed action homomorphism is scalar multiplication by the algebra element. -/
@[simp] theorem actionAlgHom_apply (a : AuxiliaryPathType k Q) (v : V) :
    (actionAlgHom : AuxiliaryPathType k Q →ₐ[k] Module.End k V) a v = a • v := rfl

/-- The scalar-linear projector obtained by the action of a vertex idempotent. -/
noncomputable def vertexProjector (i : Q) : Module.End k V :=
  (actionAlgHom : AuxiliaryPathType k Q →ₐ[k] Module.End k V) (vertexIdempotent i)

/-- A vertex projector acts by its corresponding vertex idempotent. -/
theorem vertexProjector_apply (i : Q) (v : V) :
    (vertexProjector i : Module.End k V) v = (vertexIdempotent i : AuxiliaryPathType k Q) • v := rfl

/-- The vertex projectors on every module form a complete orthogonal family of idempotents. -/
theorem vertexProjectors_completeOrthogonal :
    CompleteOrthogonalIdempotents (fun i : Q => (vertexProjector i : Module.End k V)) :=
  vertexIdempotents_completeOrthogonal.map
    (f := (actionAlgHom : AuxiliaryPathType k Q →ₐ[k] Module.End k V).toRingHom)

/-- The submodule cut out by the idempotent of a specified vertex. -/
noncomputable def vertexSubmodule (i : Q) : Submodule k V :=
  LinearMap.range (vertexProjector i : Module.End k V)

/-- A vertex submodule is the range of its vertex projector. -/
theorem vertexSubmodule_eq_range_projector (i : Q) :
    (vertexSubmodule i : Submodule k V) = LinearMap.range (vertexProjector i : Module.End k V) := rfl

/-- The image of a vertex projector lies in its vertex submodule. -/
theorem vertexProjector_mem (i : Q) (v : V) :
    (vertexProjector i : Module.End k V) v ∈ (vertexSubmodule i : Submodule k V) :=
  LinearMap.mem_range_self _ v

/-- A vertex projector fixes vectors in its vertex submodule. -/
theorem vertexProjector_eq_self_of_mem {i : Q} {x : V} (hx : x ∈ (vertexSubmodule i : Submodule k V)) :
    (vertexProjector i : Module.End k V) x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [← Module.End.mul_apply, (vertexProjectors_completeOrthogonal.idem i).eq]

/-- Acting by an arrow element sends vectors into the source vertex submodule. -/
theorem arrowElement_smul_mem_source {i j : Q} (e : i ⟶ j) (x : V) :
    (arrowElement e : AuxiliaryPathType k Q) • x ∈ (vertexSubmodule i : Submodule k V) := by
  refine ⟨(arrowElement e : AuxiliaryPathType k Q) • x, ?_⟩
  rw [vertexProjector_apply, ← SemigroupAction.mul_smul, vertexIdempotent_mul_arrowElement]

/-- An arrow induces a linear map from its target vertex part to its source vertex part. -/
noncomputable def arrowMapOnOppositeVertexParts {i j : Q} (e : i ⟶ j) :
    (vertexSubmodule j : Submodule k V) →ₗ[k] (vertexSubmodule i : Submodule k V) :=
  LinearMap.restrict (actionAlgHom (arrowElement e)) (fun x _ => arrowElement_smul_mem_source e x)

/-- The reversed arrow map on vertex parts is given by algebra action. -/
@[simp] theorem arrowMapOnOppositeVertexParts_apply {i j : Q} (e : i ⟶ j) (x : (vertexSubmodule j : Submodule k V)) :
    (arrowMapOnOppositeVertexParts e x : V) = (arrowElement e : AuxiliaryPathType k Q) • (x : V) :=
  LinearMap.coe_restrict_apply _ _

/-- Constructs a representation of the opposite quiver from a module over the reversed-composition algebra. -/
@[source_ref "Chapter2/Discussion_after_Theorem2.1.1/Derived3" (role := supporting)]
noncomputable def oppositeRepresentationOfModule : AuxiliaryQuiverModuleData k Qᵒᵖ where
  obj X := (vertexSubmodule (V := V) X.unop : Submodule k V)
  map {_X _Y} f := arrowMapOnOppositeVertexParts f.unop

/-- A vertex space of the associated opposite-quiver representation is the corresponding vertex submodule. -/
@[simp] theorem oppositeRepresentation_obj (X : Qᵒᵖ) :
    (oppositeRepresentationOfModule (k := k) (Q := Q) (V := V)).obj X = (vertexSubmodule X.unop : Submodule k V) := rfl

/-- The arrow map in the associated opposite-quiver representation is induced by the reversed underlying arrow. -/
@[simp] theorem oppositeRepresentation_arrowMap {X Y : Qᵒᵖ} (f : X ⟶ Y) :
    (oppositeRepresentationOfModule (k := k) (Q := Q) (V := V)).map f = arrowMapOnOppositeVertexParts f.unop := rfl

end ModuleDecomposition

section ReverseDirection

/-- The family of vector spaces indexed by original vertices underlying an opposite-quiver representation. -/
abbrev oppositeVertexFamily (R : AuxiliaryQuiverModuleData k Qᵒᵖ) (i : Q) : Type _ :=
  R.obj (Opposite.op i)

/-- The scalar-linear map in the reverse direction along a path for an opposite-quiver representation. -/
noncomputable def oppositePathLinearMap (R : AuxiliaryQuiverModuleData k Qᵒᵖ) {a b : Q}
    (p : Quiver.Path a b) : oppositeVertexFamily R b →ₗ[k] oppositeVertexFamily R a :=
  Quiver.Path.rec (motive := fun b _ => oppositeVertexFamily R b →ₗ[k] oppositeVertexFamily R a)
    LinearMap.id (fun _ e ih => ih ∘ₗ R.map e.op) p

omit [DecidableEq Q] in
/-- The reverse map along an empty path is the identity. -/
@[simp] theorem oppositePathLinearMap_nil (R : AuxiliaryQuiverModuleData k Qᵒᵖ) (a : Q) :
    oppositePathLinearMap R (Quiver.Path.nil : Quiver.Path a a) = LinearMap.id := rfl

omit [DecidableEq Q] in
/-- The reverse map along a path extended by an arrow composes with the opposite arrow map. -/
@[simp] theorem oppositePathLinearMap_cons (R : AuxiliaryQuiverModuleData k Qᵒᵖ) {a b c : Q}
    (p : Quiver.Path a b) (e : b ⟶ c) :
    oppositePathLinearMap R (p.cons e) = oppositePathLinearMap R p ∘ₗ R.map e.op := rfl

omit [DecidableEq Q] in

/-- The reverse map along a composite path is the corresponding composite of reverse path maps. -/
theorem oppositePathLinearMap_comp (R : AuxiliaryQuiverModuleData k Qᵒᵖ) {a b d : Q}
    (p : Quiver.Path a b) (q : Quiver.Path b d) :
    oppositePathLinearMap R (p.comp q) = oppositePathLinearMap R p ∘ₗ oppositePathLinearMap R q := by
  induction q with
  | nil => simp
  | cons q' e ih => simp only [Quiver.Path.comp_cons, oppositePathLinearMap_cons, ih, LinearMap.comp_assoc]

/-- The endomorphism of an opposite-representation direct sum associated with a path. -/
noncomputable def oppositePathEndomorphism (R : AuxiliaryQuiverModuleData k Qᵒᵖ) :
    AuxiliaryBundledPathType Q → Module.End k (DirectSum Q (oppositeVertexFamily R))
  | ⟨a, b, p⟩ =>
      DirectSum.lof k Q (oppositeVertexFamily R) a ∘ₗ oppositePathLinearMap R p ∘ₗ DirectSum.component k Q (oppositeVertexFamily R) b

/-- An opposite path endomorphism is source inclusion after the reversed path map and target projection. -/
theorem oppositePathEndomorphism_eq_inclusion_comp (R : AuxiliaryQuiverModuleData k Qᵒᵖ) {a b : Q} (p : Quiver.Path a b) :
    oppositePathEndomorphism R ⟨a, b, p⟩ =
      DirectSum.lof k Q (oppositeVertexFamily R) a ∘ₗ oppositePathLinearMap R p ∘ₗ
        DirectSum.component k Q (oppositeVertexFamily R) b :=
  rfl

/-- Composable paths give the product of their opposite direct-sum endomorphisms. -/
theorem oppositePathEndomorphism_comp (R : AuxiliaryQuiverModuleData k Qᵒᵖ) {a b d : Q}
    (p : Quiver.Path a b) (q : Quiver.Path b d) :
    oppositePathEndomorphism R ⟨a, b, p⟩ * oppositePathEndomorphism R ⟨b, d, q⟩ = oppositePathEndomorphism R ⟨a, d, p.comp q⟩ := by
  ext m
  simp only [Module.End.mul_apply, oppositePathEndomorphism_eq_inclusion_comp, LinearMap.comp_apply,
    DirectSum.component.lof_self, oppositePathLinearMap_comp]

/-- Opposite direct-sum path endomorphisms with mismatched intermediate vertices multiply to zero. -/
theorem oppositePathEndomorphism_mul_eq_zero (R : AuxiliaryQuiverModuleData k Qᵒᵖ) {a b c d : Q}
    (p : Quiver.Path a b) (q : Quiver.Path c d) (h : b ≠ c) :
    oppositePathEndomorphism R ⟨a, b, p⟩ * oppositePathEndomorphism R ⟨c, d, q⟩ = 0 := by
  ext m
  simp only [Module.End.mul_apply, oppositePathEndomorphism_eq_inclusion_comp, LinearMap.comp_apply, LinearMap.zero_apply]
  rw [DirectSum.component.of, dif_neg (Ne.symm h), map_zero, map_zero]

/-- The scalar-linear map sending reversed-composition algebra elements to endomorphisms of the opposite direct sum. -/
noncomputable def oppositeDirectSumLinearAction (R : AuxiliaryQuiverModuleData k Qᵒᵖ) :
    AuxiliaryPathType k Q →ₗ[k] Module.End k (DirectSum Q (oppositeVertexFamily R)) :=
  Finsupp.lsum k fun x => (LinearMap.id : k →ₗ[k] k).smulRight (oppositePathEndomorphism R x)

/-- The opposite direct-sum action of a scalar-supported path is the scalar multiple of its path endomorphism. -/
theorem oppositeDirectSumLinearAction_single (R : AuxiliaryQuiverModuleData k Qᵒᵖ) (x : AuxiliaryBundledPathType Q)
    (c : k) : oppositeDirectSumLinearAction R (Finsupp.single x c) = c • oppositePathEndomorphism R x := by



  change (Finsupp.lsum k fun x => (LinearMap.id : k →ₗ[k] k).smulRight (oppositePathEndomorphism R x))
      (Finsupp.single x c) = c • oppositePathEndomorphism R x
  simp only [Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_coe, id_eq]

/-- The opposite direct-sum linear action of a path element is its path endomorphism. -/
theorem oppositeDirectSumLinearAction_path (R : AuxiliaryQuiverModuleData k Qᵒᵖ) (x : AuxiliaryBundledPathType Q) :
    oppositeDirectSumLinearAction R (auxiliaryOfPath x) = oppositePathEndomorphism R x := by
  rw [auxiliaryOfPath, oppositeDirectSumLinearAction_single, one_smul]

/-- The opposite direct-sum linear action sends a path product to the product of path endomorphisms. -/
theorem oppositeDirectSumLinearAction_pathProduct (R : AuxiliaryQuiverModuleData k Qᵒᵖ)
    (x y : AuxiliaryBundledPathType Q) :
    oppositeDirectSumLinearAction R (auxiliaryProduct x y) = oppositePathEndomorphism R x * oppositePathEndomorphism R y := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  by_cases h : b = c
  · subst h
    rw [auxiliaryProduct_of_composable, oppositeDirectSumLinearAction_single, one_smul, oppositePathEndomorphism_comp]
  · rw [auxiliaryProduct_of_not_composable _ _ h, map_zero, oppositePathEndomorphism_mul_eq_zero R p q h]

/-- The opposite direct-sum linear action preserves multiplication. -/
theorem oppositeDirectSumLinearAction_mul (R : AuxiliaryQuiverModuleData k Qᵒᵖ) (f g : AuxiliaryPathType k Q) :
    oppositeDirectSumLinearAction R (f * g) = oppositeDirectSumLinearAction R f * oppositeDirectSumLinearAction R g := by
  induction f using AuxiliaryPathType.induction_on with
  | zero => simp
  | add f1 f2 h1 h2 => rw [add_mul, map_add, map_add, h1, h2, add_mul]
  | single x a =>
    induction g using AuxiliaryPathType.induction_on with
    | zero => simp
    | add g1 g2 h1 h2 => rw [mul_add, map_add, map_add, h1, h2, mul_add]
    | single y b =>
      rw [single_mul_single, map_smul, oppositeDirectSumLinearAction_pathProduct, oppositeDirectSumLinearAction_single, oppositeDirectSumLinearAction_single,
        smul_mul_smul_comm]

/-- The sum of opposite-vertex component projections followed by inclusions is the identity. -/
theorem sum_oppositeInclusion_component_eq_id [Fintype Q] (R : AuxiliaryQuiverModuleData k Qᵒᵖ) :
    (∑ i : Q, DirectSum.lof k Q (oppositeVertexFamily R) i ∘ₗ DirectSum.component k Q (oppositeVertexFamily R) i)
      = LinearMap.id := by
  refine LinearMap.ext fun m => ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
  conv_rhs => rw [← DirectSum.sum_univ_of m]
  exact Finset.sum_congr rfl fun i _ => by
    rw [DirectSum.lof_eq_of, ← DirectSum.apply_eq_component]

/-- The opposite direct-sum linear action sends one to the identity endomorphism. -/
theorem oppositeDirectSumLinearAction_one [Fintype Q] (R : AuxiliaryQuiverModuleData k Qᵒᵖ) :
    oppositeDirectSumLinearAction R 1 = 1 := by
  rw [one_eq_sum_ofPath_vertexPath, map_sum, Module.End.one_eq_id, ← sum_oppositeInclusion_component_eq_id R]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [oppositeDirectSumLinearAction_path, oppositePathEndomorphism_eq_inclusion_comp, oppositePathLinearMap_nil, LinearMap.id_comp]

/-- The reversed-composition algebra action on an opposite-representation direct sum as an algebra homomorphism. -/
noncomputable def oppositeDirectSumActionAlgHom [Fintype Q] (R : AuxiliaryQuiverModuleData k Qᵒᵖ) :
    AuxiliaryPathType k Q →ₐ[k] Module.End k (DirectSum Q (oppositeVertexFamily R)) :=
  AlgHom.ofLinearMap (oppositeDirectSumLinearAction R) (oppositeDirectSumLinearAction_one R) (oppositeDirectSumLinearAction_mul R)

/-- The opposite direct-sum action homomorphism agrees pointwise with its linear construction. -/
@[simp] theorem oppositeDirectSumActionAlgHom_eq_linearAction [Fintype Q] (R : AuxiliaryQuiverModuleData k Qᵒᵖ)
    (a : AuxiliaryPathType k Q) : oppositeDirectSumActionAlgHom R a = oppositeDirectSumLinearAction R a := rfl

/-- The opposite direct-sum action homomorphism sends a path element to its endomorphism. -/
theorem oppositeDirectSumActionAlgHom_path [Fintype Q] (R : AuxiliaryQuiverModuleData k Qᵒᵖ)
    (x : AuxiliaryBundledPathType Q) : oppositeDirectSumActionAlgHom R (auxiliaryOfPath x) = oppositePathEndomorphism R x := by
  rw [oppositeDirectSumActionAlgHom_eq_linearAction, oppositeDirectSumLinearAction_path]

/-- The opposite representation direct sum as a module over the reversed-composition algebra. -/
@[reducible, source_ref "Chapter2/Discussion_after_Theorem2.1.1/Derived3"
  (role := supporting)]
noncomputable def oppositeDirectSumAlgebraModule [Fintype Q]
    (R : AuxiliaryQuiverModuleData k Qᵒᵖ) :
    Module (AuxiliaryPathType k Q) (DirectSum Q (oppositeVertexFamily R)) :=
  Module.compHom _ (oppositeDirectSumActionAlgHom R).toRingHom

/-- Algebra scalar multiplication on the opposite direct sum is evaluation of its action homomorphism. -/
theorem oppositeDirectSumAlgebraModule_smul [Fintype Q] (R : AuxiliaryQuiverModuleData k Qᵒᵖ)
    (a : AuxiliaryPathType k Q) (m : DirectSum Q (oppositeVertexFamily R)) :
    (letI := oppositeDirectSumAlgebraModule R; a • m) = oppositeDirectSumActionAlgHom R a m := rfl

/-- The opposite direct-sum module is compatible with field scalars. -/
theorem oppositeDirectSumAlgebraModule_scalarTower [Fintype Q] (R : AuxiliaryQuiverModuleData k Qᵒᵖ) :
    letI := oppositeDirectSumAlgebraModule R
    IsScalarTower k (AuxiliaryPathType k Q) (DirectSum Q (oppositeVertexFamily R)) := by
  letI := oppositeDirectSumAlgebraModule R
  refine ⟨fun c a m => ?_⟩
  change oppositeDirectSumActionAlgHom R (c • a) m = c • (oppositeDirectSumActionAlgHom R a) m
  rw [map_smul, LinearMap.smul_apply]

end ReverseDirection

section InternalDecomposition

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]
variable [Fintype Q] {V : Type*} [AddCommGroup V] [Module k V]
  [Module (AuxiliaryPathType k Q) V] [IsScalarTower k (AuxiliaryPathType k Q) V]

/-- The family of opposite-oriented vertex submodules is an internal direct sum. -/
theorem oppositeVertexParts_isInternal :
    DirectSum.IsInternal (fun i : Q => (vertexSubmodule i : Submodule k V)) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  ·
    rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hxsup
    have hker : (⨆ (j) (_ : j ≠ i), (vertexSubmodule j : Submodule k V))
        ≤ LinearMap.ker (vertexProjector i : Module.End k V) := by
      refine iSup₂_le fun j hj => ?_
      rw [vertexSubmodule_eq_range_projector, LinearMap.range_le_ker_iff]
      exact vertexProjectors_completeOrthogonal.ortho hj.symm
    have h0 : (vertexProjector i : Module.End k V) x = 0 := by
      rw [← LinearMap.mem_ker]; exact hker hxsup
    rw [← vertexProjector_eq_self_of_mem hx, h0]
  ·
    rw [eq_top_iff]
    intro v _
    have hsum : (∑ i : Q, (vertexProjector i : Module.End k V)) v = v := by
      rw [vertexProjectors_completeOrthogonal.complete, Module.End.one_apply]
    rw [← hsum, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (vertexProjector_mem i v)

end InternalDecomposition

section RoundTripHelpers

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]

/-- Multiplication of path elements agrees with the reversed-composition path product. -/
theorem pathElement_mul (x y : AuxiliaryBundledPathType Q) :
    (auxiliaryOfPath x : AuxiliaryPathType k Q) * auxiliaryOfPath y = auxiliaryProduct x y := by
  rw [auxiliaryOfPath, auxiliaryOfPath, single_mul_single, one_mul, one_smul]

/-- The element of a path extended by an arrow is the path element multiplied by the arrow element. -/
theorem pathElement_cons {a c b : Q} (p : Quiver.Path a c) (e : c ⟶ b) :
    (auxiliaryOfPath ⟨a, b, p.cons e⟩ : AuxiliaryPathType k Q) = auxiliaryOfPath ⟨a, c, p⟩ * arrowElement e := by
  have hidx : (⟨a, b, p.cons e⟩ : AuxiliaryBundledPathType Q) = ⟨a, b, p.comp e.toPath⟩ := by
    rw [Quiver.Hom.toPath, Quiver.Path.comp_cons, Quiver.Path.comp_nil]
  rw [hidx, arrowElement, pathElement_mul, auxiliaryProduct_of_composable, auxiliaryOfPath]

omit [DecidableEq Q] in

/-- The reverse path map of one arrow is the associated opposite-quiver arrow map. -/
@[simp] theorem oppositePathLinearMap_singleArrow (R : AuxiliaryQuiverModuleData k Qᵒᵖ) {a b : Q} (e : a ⟶ b) :
    oppositePathLinearMap R e.toPath = R.map e.op := by
  rw [Quiver.Hom.toPath, oppositePathLinearMap_cons, oppositePathLinearMap_nil, LinearMap.id_comp]

end RoundTripHelpers

section ModuleRoundTrip

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q] [Fintype Q]
variable {V : Type*} [AddCommGroup V] [Module k V]
  [Module (AuxiliaryPathType k Q) V] [IsScalarTower k (AuxiliaryPathType k Q) V]

/-- A linear equivalence of algebra modules induces an equivalence of their opposite-quiver representations. -/
noncomputable def oppositeRepresentationEquivOfModuleEquiv {W : Type*} [AddCommGroup W] [Module k W]
    [Module (AuxiliaryPathType k Q) W] [IsScalarTower k (AuxiliaryPathType k Q) W]
    (e : V ≃ₗ[AuxiliaryPathType k Q] W) :
    AuxiliaryQuiverEquivData k Qᵒᵖ
      (oppositeRepresentationOfModule (k := k) (V := V)) (oppositeRepresentationOfModule (k := k) (V := W)) where
  app v := LinearEquiv.ofLinear
    (LinearMap.codRestrict _
      ((e.restrictScalars k).toLinearMap.comp
        (Submodule.subtype (vertexSubmodule (k := k) (V := V) v.unop)))
      (fun (x : (vertexSubmodule (k := k) (V := V) v.unop : Submodule k V)) => by
        refine ⟨e (x : V), ?_⟩
        rw [vertexProjector_apply, ← e.map_smul, ← vertexProjector_apply,
          vertexProjector_eq_self_of_mem x.2]
        rfl))
    (LinearMap.codRestrict _
      ((e.symm.restrictScalars k).toLinearMap.comp
        (Submodule.subtype (vertexSubmodule (k := k) (V := W) v.unop)))
      (fun (x : (vertexSubmodule (k := k) (V := W) v.unop : Submodule k W)) => by
        refine ⟨e.symm (x : W), ?_⟩
        rw [vertexProjector_apply, ← e.symm.map_smul, ← vertexProjector_apply,
          vertexProjector_eq_self_of_mem x.2]
        rfl))
    (by
      refine LinearMap.ext fun x => ?_
      let xw : (vertexSubmodule (k := k) (V := W) v.unop : Submodule k W) := x
      apply Subtype.ext
      exact e.apply_symm_apply (xw : W))
    (by
      refine LinearMap.ext fun x => ?_
      let xv : (vertexSubmodule (k := k) (V := V) v.unop : Submodule k V) := x
      apply Subtype.ext
      exact e.symm_apply_apply (xv : V))
  naturality {v w} f x := by
    apply Subtype.ext
    let xv : (vertexSubmodule (k := k) (V := V) v.unop : Submodule k V) := x
    change e ((arrowElement f.unop : AuxiliaryPathType k Q) • (xv : V)) =
      (arrowElement f.unop : AuxiliaryPathType k Q) • e (xv : V)
    exact e.map_smul _ _

/-- Path-element action on a target vertex vector agrees with the opposite representation's path map into the source part. -/
theorem pathElement_smul_vertex {a b : Q} (p : Quiver.Path a b) :
    ∀ (y : (vertexSubmodule b : Submodule k V)),
      (auxiliaryOfPath ⟨a, b, p⟩ : AuxiliaryPathType k Q) • (y : V)
        = (vertexSubmodule a : Submodule k V).subtype (oppositePathLinearMap (oppositeRepresentationOfModule (k := k) (V := V)) p y) := by
  induction p with
  | nil =>
    intro y
    rw [oppositePathLinearMap_nil, LinearMap.id_apply]
    change (vertexIdempotent a : AuxiliaryPathType k Q) • (y : V) = (y : V)
    rw [← vertexProjector_apply]
    exact vertexProjector_eq_self_of_mem y.2
  | cons p' e ih =>
    intro y
    rw [pathElement_cons p' e, SemigroupAction.mul_smul, ← arrowMapOnOppositeVertexParts_apply e y, ih (arrowMapOnOppositeVertexParts e y), oppositePathLinearMap_cons,
      LinearMap.comp_apply, oppositeRepresentation_arrowMap]
    rfl

attribute [local instance] oppositeDirectSumAlgebraModule

/-- The opposite direct sum reconstructed from a module inherits the expected scalar tower. -/
local instance reconstructedOppositeScalarTower :
    IsScalarTower k (AuxiliaryPathType k Q) (DirectSum Q (oppositeVertexFamily (oppositeRepresentationOfModule (k := k) (V := V)))) :=
  oppositeDirectSumAlgebraModule_scalarTower (oppositeRepresentationOfModule (k := k) (V := V))

private noncomputable abbrev coeV :
    DirectSum Q (oppositeVertexFamily (oppositeRepresentationOfModule (k := k) (V := V))) →ₗ[k] V :=
  DirectSum.coeLinearMap (fun i => (vertexSubmodule (k := k) (V := V) i : Submodule k V))

private theorem coeV_lof (i : Q) (z : oppositeVertexFamily (oppositeRepresentationOfModule (k := k) (V := V)) i) :
    coeV (k := k) (V := V)
        (DirectSum.lof k Q (oppositeVertexFamily (oppositeRepresentationOfModule (k := k) (V := V))) i z)
      = (vertexSubmodule (k := k) (V := V) i : Submodule k V).subtype z :=
  DirectSum.coeLinearMap_lof (fun i => (vertexSubmodule (k := k) (V := V) i : Submodule k V)) i z

/-- Path action on the reconstructed opposite direct sum agrees with the original module action. -/
theorem pathAction_onOppositeDirectSum (x : AuxiliaryBundledPathType Q)
    (m : DirectSum Q (oppositeVertexFamily (oppositeRepresentationOfModule (k := k) (V := V)))) :
    coeV (k := k) (V := V) (oppositePathEndomorphism (oppositeRepresentationOfModule (k := k) (V := V)) x m)
      = (auxiliaryOfPath x : AuxiliaryPathType k Q) • coeV (k := k) (V := V) m := by
  obtain ⟨a, b, p⟩ := x
  have key : (coeV (k := k) (V := V)).comp (oppositePathEndomorphism (oppositeRepresentationOfModule (k := k) (V := V)) ⟨a, b, p⟩)
      = (actionAlgHom (auxiliaryOfPath ⟨a, b, p⟩)).comp (coeV (k := k) (V := V)) := by
    refine DirectSum.linearMap_ext k fun c => LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, oppositePathEndomorphism_eq_inclusion_comp, actionAlgHom_apply]
    rw [coeV_lof, coeV_lof]
    by_cases h : c = b
    · subst h
      rw [DirectSum.component.lof_self]
      exact (pathElement_smul_vertex p y).symm
    · rw [DirectSum.component.of, dif_neg h]
      have hzero : (vertexSubmodule (k := k) (V := V) a : Submodule k V).subtype
          (oppositePathLinearMap (oppositeRepresentationOfModule (k := k) (V := V)) p
            (0 : (vertexSubmodule (k := k) (V := V) b : Submodule k V))) = 0 := by
        calc
          _ = (vertexSubmodule (k := k) (V := V) a : Submodule k V).subtype 0 :=
            congrArg
              (vertexSubmodule (k := k) (V := V) a : Submodule k V).subtype
              (LinearMap.map_zero (oppositePathLinearMap (oppositeRepresentationOfModule (k := k) (V := V)) p))
          _ = 0 := LinearMap.map_zero _
      calc
        _ = 0 := hzero
        _ = (auxiliaryOfPath ⟨a, b, p⟩ : AuxiliaryPathType k Q) •
            (vertexSubmodule (k := k) (V := V) c : Submodule k V).subtype y := by

          symm
          have hy : (vertexIdempotent c : AuxiliaryPathType k Q) •
                (vertexSubmodule (k := k) (V := V) c : Submodule k V).subtype y
              = (vertexSubmodule (k := k) (V := V) c : Submodule k V).subtype y := by
            rw [← vertexProjector_apply]; exact vertexProjector_eq_self_of_mem y.2
          rw [← hy, ← SemigroupAction.mul_smul, pathElement_mul_vertexIdempotent, if_neg (Ne.symm h), zero_smul]
  have := LinearMap.congr_fun key m
  simpa only [LinearMap.comp_apply, actionAlgHom_apply] using this

/-- The reconstructed opposite direct-sum action agrees with the original algebra action. -/
theorem algebraAction_onOppositeDirectSum (a : AuxiliaryPathType k Q)
    (m : DirectSum Q (oppositeVertexFamily (oppositeRepresentationOfModule (k := k) (V := V)))) :
    coeV (k := k) (V := V) (oppositeDirectSumActionAlgHom (oppositeRepresentationOfModule (k := k) (V := V)) a m)
      = a • coeV (k := k) (V := V) m := by
  induction a using AuxiliaryPathType.induction_on with
  | zero => simp
  | add a1 a2 h1 h2 => rw [map_add, LinearMap.add_apply, map_add, h1, h2, add_smul]
  | single x c =>
    have hs : (Finsupp.single x c : AuxiliaryPathType k Q) = c • auxiliaryOfPath x := by
      exact (smul_single_one (k := k) c x).symm
    have hs_smul := congrArg
      (fun z : AuxiliaryPathType k Q => z • coeV (k := k) (V := V) m) hs
    have htower : (c • (auxiliaryOfPath x : AuxiliaryPathType k Q)) • coeV (k := k) (V := V) m =
        c • ((auxiliaryOfPath x : AuxiliaryPathType k Q) • coeV (k := k) (V := V) m) :=
      smul_assoc c (auxiliaryOfPath x : AuxiliaryPathType k Q) (coeV (k := k) (V := V) m)
    have hs_action := hs_smul.trans htower
    rw [oppositeDirectSumActionAlgHom_eq_linearAction, oppositeDirectSumLinearAction_single, LinearMap.smul_apply, map_smul, pathAction_onOppositeDirectSum]
    exact hs_action.symm

/-- The direct sum reconstructed from the opposite-quiver representation is linearly equivalent to the original module. -/
@[source_ref "Chapter2/Discussion_after_Theorem2.1.1/Derived3" (role := supporting)]
noncomputable def oppositeReconstructionLinearEquiv :
    DirectSum Q (oppositeVertexFamily (oppositeRepresentationOfModule (k := k) (V := V))) ≃ₗ[AuxiliaryPathType k Q] V :=
  let e : DirectSum Q (oppositeVertexFamily (oppositeRepresentationOfModule (k := k) (V := V))) ≃ₗ[k] V :=
    LinearEquiv.ofBijective (coeV (k := k) (V := V)) oppositeVertexParts_isInternal
  { toFun := e
    map_add' := e.map_add
    map_smul' := algebraAction_onOppositeDirectSum
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

end ModuleRoundTrip

section RepRoundTrip

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q] [Fintype Q]
variable (R : AuxiliaryQuiverModuleData k Qᵒᵖ)

attribute [local instance] oppositeDirectSumAlgebraModule

/-- The field, reversed-composition algebra, and opposite representation direct sum form a scalar tower. -/
local instance oppositeDirectSumScalarTower :
    IsScalarTower k (AuxiliaryPathType k Q) (DirectSum Q (oppositeVertexFamily R)) :=
  oppositeDirectSumAlgebraModule_scalarTower R

omit [DecidableEq Q] [Fintype Q] in

/-- An equivalence of opposite-quiver representations commutes with their reverse path maps. -/
theorem oppositeRepresentationEquiv_commutes_path {S : AuxiliaryQuiverModuleData k Qᵒᵖ}
    (e : AuxiliaryQuiverEquivData k Qᵒᵖ R S) {a b : Q}
    (p : Quiver.Path a b) (x : R.obj (Opposite.op b)) :
    e.app (Opposite.op a) (oppositePathLinearMap R p x) =
      oppositePathLinearMap S p (e.app (Opposite.op b) x) := by
  induction p with
  | nil => simp only [oppositePathLinearMap_nil, LinearMap.id_apply]
  | cons p f ih =>
    simp only [oppositePathLinearMap_cons, LinearMap.comp_apply]
    rw [ih, e.naturality f.op]

/-- An opposite-representation equivalence induces a scalar-linear equivalence of the corresponding direct sums. -/
noncomputable def oppositeDirectSumLinearEquiv {S : AuxiliaryQuiverModuleData k Qᵒᵖ}
    (e : AuxiliaryQuiverEquivData k Qᵒᵖ R S) :
    DirectSum Q (oppositeVertexFamily R) ≃ₗ[k] DirectSum Q (oppositeVertexFamily S) :=
  DirectSum.congrLinearEquiv fun i => e.app (Opposite.op i)

omit [Fintype Q] in

/-- The induced opposite direct-sum equivalence intertwines every path endomorphism. -/
theorem oppositeDirectSumLinearEquiv_intertwinesPath {S : AuxiliaryQuiverModuleData k Qᵒᵖ}
    (e : AuxiliaryQuiverEquivData k Qᵒᵖ R S)
    (x : AuxiliaryBundledPathType Q) (m : DirectSum Q (oppositeVertexFamily R)) :
    oppositeDirectSumLinearEquiv R e (oppositePathEndomorphism R x m) =
      oppositePathEndomorphism S x (oppositeDirectSumLinearEquiv R e m) := by
  induction m using DirectSum.induction_on with
  | zero => simp
  | add m n hm hn =>
    rw [map_add, map_add, hm, hn]
    exact (map_add (oppositePathEndomorphism S x) _ _).symm.trans
      (congrArg (oppositePathEndomorphism S x) ((oppositeDirectSumLinearEquiv R e).map_add m n).symm)
  | of i z =>
    rw [← DirectSum.lof_eq_of k]
    obtain ⟨a, b, p⟩ := x
    simp only [oppositePathEndomorphism_eq_inclusion_comp, LinearMap.comp_apply]
    by_cases h : i = b
    · subst h
      rw [DirectSum.component.lof_self]
      simp only [oppositeDirectSumLinearEquiv, DirectSum.coe_congrLinearEquiv,
        DirectSum.lmap_lof]
      rw [DirectSum.component.lof_self]
      exact congrArg (DirectSum.lof k Q (oppositeVertexFamily S) a)
        (oppositeRepresentationEquiv_commutes_path R e p z)
    · rw [DirectSum.component.of, dif_neg h, map_zero, map_zero]
      simp only [oppositeDirectSumLinearEquiv, DirectSum.coe_congrLinearEquiv,
        DirectSum.lmap_lof, DirectSum.component.of, dif_neg h, map_zero]

/-- The induced opposite direct-sum equivalence intertwines the algebra actions. -/
theorem oppositeDirectSumLinearEquiv_intertwinesAlgebra {S : AuxiliaryQuiverModuleData k Qᵒᵖ}
    (e : AuxiliaryQuiverEquivData k Qᵒᵖ R S)
    (a : AuxiliaryPathType k Q) (m : DirectSum Q (oppositeVertexFamily R)) :
    oppositeDirectSumLinearEquiv R e (oppositeDirectSumActionAlgHom R a m) =
      oppositeDirectSumActionAlgHom S a (oppositeDirectSumLinearEquiv R e m) := by
  induction a using AuxiliaryPathType.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, LinearMap.add_apply, map_add, ha, hb]
    exact (congrArg
      (fun f : Module.End k (DirectSum Q (oppositeVertexFamily S)) => f (oppositeDirectSumLinearEquiv R e m))
      (map_add (oppositeDirectSumActionAlgHom S) a b)).symm
  | single x c =>
    rw [oppositeDirectSumActionAlgHom_eq_linearAction, oppositeDirectSumLinearAction_single, LinearMap.smul_apply, map_smul, oppositeDirectSumActionAlgHom_eq_linearAction,
      oppositeDirectSumLinearAction_single, LinearMap.smul_apply, oppositeDirectSumLinearEquiv_intertwinesPath]

/-- An opposite-representation equivalence induces an algebra-linear equivalence of direct sums. -/
noncomputable def oppositeDirectSumAlgebraLinearEquiv {S : AuxiliaryQuiverModuleData k Qᵒᵖ}
    (e : AuxiliaryQuiverEquivData k Qᵒᵖ R S) :
    letI := oppositeDirectSumAlgebraModule R
    letI := oppositeDirectSumAlgebraModule S
    DirectSum Q (oppositeVertexFamily R) ≃ₗ[AuxiliaryPathType k Q] DirectSum Q (oppositeVertexFamily S) := by
  letI := oppositeDirectSumAlgebraModule R
  letI := oppositeDirectSumAlgebraModule S
  let ek := oppositeDirectSumLinearEquiv R e
  exact
    { toFun := ek
      map_add' := ek.map_add
      map_smul' := fun a m => oppositeDirectSumLinearEquiv_intertwinesAlgebra R e a m
      invFun := ek.symm
      left_inv := ek.left_inv
      right_inv := ek.right_inv }

/-- On an opposite representation direct sum, a vertex projector is inclusion after component projection. -/
theorem vertexProjector_onOppositeDirectSum (i : Q) (m : DirectSum Q (oppositeVertexFamily R)) :
    (vertexProjector (k := k) (V := DirectSum Q (oppositeVertexFamily R)) i) m
      = DirectSum.lof k Q (oppositeVertexFamily R) i (DirectSum.component k Q (oppositeVertexFamily R) i m) := by
  rw [vertexProjector_apply, oppositeDirectSumAlgebraModule_smul, vertexIdempotent, oppositeDirectSumActionAlgHom_path, oppositePathEndomorphism_eq_inclusion_comp]
  simp only [LinearMap.comp_apply, oppositePathLinearMap_nil, LinearMap.id_coe, id_eq]

/-- For an opposite representation direct sum, the vertex submodule is the range of its summand inclusion. -/
theorem vertexSubmodule_eq_range_inclusion (i : Q) :
    (vertexSubmodule (k := k) (V := DirectSum Q (oppositeVertexFamily R)) i)
      = LinearMap.range (DirectSum.lof k Q (oppositeVertexFamily R) i) := by
  apply le_antisymm
  · rw [vertexSubmodule_eq_range_projector]
    rintro x ⟨v, rfl⟩
    rw [vertexProjector_onOppositeDirectSum]
    exact LinearMap.mem_range_self _ _
  · rintro x ⟨y, rfl⟩
    rw [vertexSubmodule_eq_range_projector]
    exact ⟨_, by rw [vertexProjector_onOppositeDirectSum, DirectSum.component.lof_self]⟩

/-- Including the component of an element in its opposite-oriented vertex summand recovers it. -/
theorem oppositeVertexInclusion_component (i : Q)
    (y : (vertexSubmodule (k := k) (V := DirectSum Q (oppositeVertexFamily R)) i)) :
    DirectSum.lof k Q (oppositeVertexFamily R) i
        (DirectSum.component k Q (oppositeVertexFamily R) i (y : DirectSum Q (oppositeVertexFamily R)))
      = (y : DirectSum Q (oppositeVertexFamily R)) := by
  rw [← vertexProjector_onOppositeDirectSum]
  exact vertexProjector_eq_self_of_mem y.2

/-- An opposite representation's vertex space is linearly equivalent to its subspace in the reconstructed direct sum. -/
noncomputable def oppositeVertexSpaceEquivVertexPart (i : Q) :
    R.obj (Opposite.op i) ≃ₗ[k] (vertexSubmodule (k := k) (V := DirectSum Q (oppositeVertexFamily R)) i) :=
  LinearEquiv.ofLinear
    (LinearMap.codRestrict _ (DirectSum.lof k Q (oppositeVertexFamily R) i)
      (fun y => by rw [vertexSubmodule_eq_range_inclusion]; exact LinearMap.mem_range_self _ y))
    ((DirectSum.component k Q (oppositeVertexFamily R) i).comp
      (Submodule.subtype (vertexSubmodule (k := k) (V := DirectSum Q (oppositeVertexFamily R)) i)))
    (by
      refine LinearMap.ext fun y => ?_
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        LinearMap.id_coe, id_eq]
      exact oppositeVertexInclusion_component R i y)
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        DirectSum.component.lof_self, LinearMap.id_coe, id_eq])

/-- The opposite vertex-space equivalence includes a vector into its direct-sum summand. -/
@[simp] theorem oppositeVertexSpaceEquivVertexPart_coe (i : Q) (x : R.obj (Opposite.op i)) :
    ((oppositeVertexSpaceEquivVertexPart R i x : (vertexSubmodule (k := k) (V := DirectSum Q (oppositeVertexFamily R)) i))
        : DirectSum Q (oppositeVertexFamily R))
      = DirectSum.lof k Q (oppositeVertexFamily R) i x :=
  rfl

/-- The opposite vertex-space equivalences commute with representation arrow maps. -/
theorem oppositeVertexSpaceEquivVertexPart_naturality {X Y : Qᵒᵖ} (e : X ⟶ Y) (x : R.obj X) :
    oppositeVertexSpaceEquivVertexPart R Y.unop (R.map e x)
      = (oppositeRepresentationOfModule (k := k) (V := DirectSum Q (oppositeVertexFamily R))).map e
          (oppositeVertexSpaceEquivVertexPart R X.unop x) := by
  apply Subtype.ext
  change DirectSum.lof k Q (oppositeVertexFamily R) Y.unop (R.map e x)
      = oppositeDirectSumActionAlgHom R (arrowElement e.unop) (DirectSum.lof k Q (oppositeVertexFamily R) X.unop x)
  rw [arrowElement, oppositeDirectSumActionAlgHom_path, oppositePathEndomorphism_eq_inclusion_comp]
  simp only [LinearMap.comp_apply, DirectSum.component.lof_self, oppositePathLinearMap_singleArrow]
  rfl

/-- An opposite representation is equivalent to the representation recovered from its direct-sum module. -/
@[source_ref "Chapter2/Discussion_after_Theorem2.1.1/Derived3" (role := supporting)]
noncomputable def toModuleOppositeRepresentationEquiv :
    AuxiliaryQuiverEquivData k Qᵒᵖ R
      (oppositeRepresentationOfModule (k := k) (V := DirectSum Q (oppositeVertexFamily R))) where
  app v := oppositeVertexSpaceEquivVertexPart R v.unop
  naturality e x := oppositeVertexSpaceEquivVertexPart_naturality R e x

end RepRoundTrip

universe u v w

section IsoClasses

variable (k : Type u) (Q : Type v) [Field k] [Quiver Q] [DecidableEq Q] [Fintype Q]

/-- An encoded module structure corresponding to a representation of the opposite quiver. -/
structure OppositeModuleModel where

  /-- The carrier type of an opposite-oriented module model. -/
  carrier : Type w

  /-- The additive commutative group carried by an opposite-oriented module model. -/
  instAddCommGroup : AddCommGroup carrier

  /-- The scalar-field module structure on the opposite-oriented model's carrier. -/
  instScalarModule : Module k carrier

  /-- The reversed-composition algebra module structure on the carrier. -/
  instAlgebraModule : Module (AuxiliaryPathType k Q) carrier

  /-- The field, reversed-composition algebra, and carrier form a scalar tower. -/
  instIsScalarTower : IsScalarTower k (AuxiliaryPathType k Q) carrier

/-- The relation comparing two opposite-oriented encoded module structures. -/
def OppositeModuleModel.Related (M N : OppositeModuleModel k Q) : Prop :=
  letI := M.instAddCommGroup
  letI := M.instScalarModule
  letI := M.instAlgebraModule
  letI := M.instIsScalarTower
  letI := N.instAddCommGroup
  letI := N.instScalarModule
  letI := N.instAlgebraModule
  letI := N.instIsScalarTower
  Nonempty (M.carrier ≃ₗ[AuxiliaryPathType k Q] N.carrier)

/-- The setoid identifying equivalent opposite-oriented module models. -/
def oppositeModuleModelSetoid : Setoid (OppositeModuleModel k Q) where
  r := OppositeModuleModel.Related k Q
  iseqv := {
    refl := fun M => by
      letI := M.instAddCommGroup
      letI := M.instScalarModule
      letI := M.instAlgebraModule
      letI := M.instIsScalarTower
      exact ⟨LinearEquiv.refl (AuxiliaryPathType k Q) M.carrier⟩
    symm := fun {M N} h => by
      letI := M.instAddCommGroup
      letI := M.instScalarModule
      letI := M.instAlgebraModule
      letI := M.instIsScalarTower
      letI := N.instAddCommGroup
      letI := N.instScalarModule
      letI := N.instAlgebraModule
      letI := N.instIsScalarTower
      change Nonempty (M.carrier ≃ₗ[AuxiliaryPathType k Q] N.carrier) at h
      obtain ⟨e⟩ := h
      exact ⟨e.symm⟩
    trans := fun {M N P} h₁ h₂ => by
      letI := M.instAddCommGroup
      letI := M.instScalarModule
      letI := M.instAlgebraModule
      letI := M.instIsScalarTower
      letI := N.instAddCommGroup
      letI := N.instScalarModule
      letI := N.instAlgebraModule
      letI := N.instIsScalarTower
      letI := P.instAddCommGroup
      letI := P.instScalarModule
      letI := P.instAlgebraModule
      letI := P.instIsScalarTower
      change Nonempty (M.carrier ≃ₗ[AuxiliaryPathType k Q] N.carrier) at h₁
      change Nonempty (N.carrier ≃ₗ[AuxiliaryPathType k Q] P.carrier) at h₂
      obtain ⟨e⟩ := h₁
      obtain ⟨f⟩ := h₂
      exact ⟨e.trans f⟩ }

/-- The setoid identifying equivalent representations of the opposite quiver. -/
def oppositeRepresentationSetoid :
    Setoid (AuxiliaryQuiverModuleData k Qᵒᵖ) where
  r R S := Nonempty (AuxiliaryQuiverEquivData k Qᵒᵖ R S)
  iseqv := {
    refl := fun R => ⟨{
      app := fun i => LinearEquiv.refl k (R.obj i)
      naturality := fun _ _ => rfl }⟩
    symm := fun {R S} ⟨e⟩ => ⟨{
      app := fun i => (e.app i).symm
      naturality := fun f x => by
        rw [LinearEquiv.symm_apply_eq, e.naturality f, LinearEquiv.apply_symm_apply] }⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨{
      app := fun i => (e.app i).trans (f.app i)
      naturality := fun g x => by
        rw [LinearEquiv.trans_apply, e.naturality g, f.naturality g]
        rfl }⟩ }

/-- The quotient type of opposite-oriented module models. -/
abbrev OppositeModuleModelQuotient := Quotient (oppositeModuleModelSetoid k Q)

/-- The quotient type of representations of the opposite quiver. -/
abbrev OppositeRepresentationQuotient := Quotient (oppositeRepresentationSetoid k Q)

/-- Extracts a representation of the opposite quiver from an encoded module structure. -/
noncomputable def OppositeModuleModel.toOppositeRepresentation (M : OppositeModuleModel k Q) :
    AuxiliaryQuiverModuleData k Qᵒᵖ := by
  letI := M.instAddCommGroup
  letI := M.instScalarModule
  letI := M.instAlgebraModule
  letI := M.instIsScalarTower
  exact oppositeRepresentationOfModule (k := k) (V := M.carrier)

/-- Builds an opposite-oriented module model from a representation of the opposite quiver. -/
noncomputable def OppositeModuleModel.ofOppositeRepresentation
    (R : AuxiliaryQuiverModuleData k Qᵒᵖ) : OppositeModuleModel k Q where
  carrier := DirectSum Q (oppositeVertexFamily R)
  instAddCommGroup := Module.addCommMonoidToAddCommGroup k
  instScalarModule := inferInstance
  instAlgebraModule := oppositeDirectSumAlgebraModule R
  instIsScalarTower := oppositeDirectSumAlgebraModule_scalarTower R

/-- Related module models yield equivalent opposite-quiver representations. -/
theorem OppositeModuleModel.toOppositeRepresentation_respects {M N : OppositeModuleModel k Q}
    (h : (oppositeModuleModelSetoid k Q).r M N) :
    (oppositeRepresentationSetoid k Q).r
      (M.toOppositeRepresentation k Q) (N.toOppositeRepresentation k Q) := by
  letI := M.instAddCommGroup
  letI := M.instScalarModule
  letI := M.instAlgebraModule
  letI := M.instIsScalarTower
  letI := N.instAddCommGroup
  letI := N.instScalarModule
  letI := N.instAlgebraModule
  letI := N.instIsScalarTower
  change Nonempty (M.carrier ≃ₗ[AuxiliaryPathType k Q] N.carrier) at h
  obtain ⟨e⟩ := h
  exact ⟨oppositeRepresentationEquivOfModuleEquiv (k := k) (Q := Q) e⟩

/-- Equivalent opposite-quiver representations yield related module models. -/
theorem OppositeModuleModel.ofOppositeRepresentation_respects
    {R S : AuxiliaryQuiverModuleData k Qᵒᵖ}
    (h : (oppositeRepresentationSetoid k Q).r R S) :
    (oppositeModuleModelSetoid k Q).r
      (OppositeModuleModel.ofOppositeRepresentation k Q R)
      (OppositeModuleModel.ofOppositeRepresentation k Q S) := by
  obtain ⟨e⟩ := h
  letI : AddCommGroup (DirectSum Q (oppositeVertexFamily R)) :=
    Module.addCommMonoidToAddCommGroup k
  letI : Module (AuxiliaryPathType k Q) (DirectSum Q (oppositeVertexFamily R)) := oppositeDirectSumAlgebraModule R
  letI : AddCommGroup (DirectSum Q (oppositeVertexFamily S)) :=
    Module.addCommMonoidToAddCommGroup k
  letI : Module (AuxiliaryPathType k Q) (DirectSum Q (oppositeVertexFamily S)) := oppositeDirectSumAlgebraModule S
  change Nonempty
    (DirectSum Q (oppositeVertexFamily R) ≃ₗ[AuxiliaryPathType k Q] DirectSum Q (oppositeVertexFamily S))
  exact ⟨oppositeDirectSumAlgebraLinearEquiv R e⟩

/-- Maps an opposite-module quotient class to an opposite-representation quotient class. -/
noncomputable def quotientMapToOppositeRepresentations :
    OppositeModuleModelQuotient k Q → OppositeRepresentationQuotient k Q :=
  Quotient.map (OppositeModuleModel.toOppositeRepresentation k Q)
    (fun _ _ => OppositeModuleModel.toOppositeRepresentation_respects k Q)

/-- Maps an opposite-representation quotient class to an opposite-module quotient class. -/
noncomputable def quotientMapToOppositeModules :
    OppositeRepresentationQuotient k Q → OppositeModuleModelQuotient k Q :=
  Quotient.map (OppositeModuleModel.ofOppositeRepresentation k Q)
    (fun _ _ => OppositeModuleModel.ofOppositeRepresentation_respects k Q)

set_option maxHeartbeats 800000 in

/-- The opposite-module quotient is equivalent to the opposite-representation quotient. -/
@[source_ref "Chapter2/Discussion_after_Theorem2.1.1/Derived3" (role := primary)]
noncomputable def oppositeModuleRepresentationQuotientEquiv :
    OppositeModuleModelQuotient k Q ≃ OppositeRepresentationQuotient k Q where
  toFun := quotientMapToOppositeRepresentations k Q
  invFun := quotientMapToOppositeModules k Q
  left_inv := by
    intro x
    refine Quotient.inductionOn x fun M => ?_
    apply Quotient.sound
    letI := M.instAddCommGroup
    letI := M.instScalarModule
    letI := M.instAlgebraModule
    letI := M.instIsScalarTower
    let FR : AuxiliaryQuiverModuleData k Qᵒᵖ :=
      oppositeRepresentationOfModule (k := k) (V := M.carrier)
    letI : AddCommGroup (DirectSum Q (oppositeVertexFamily FR)) :=
      Module.addCommMonoidToAddCommGroup k
    letI : Module (AuxiliaryPathType k Q) (DirectSum Q (oppositeVertexFamily FR)) := oppositeDirectSumAlgebraModule FR
    change Nonempty
      (DirectSum Q (oppositeVertexFamily (oppositeRepresentationOfModule (k := k) (V := M.carrier))) ≃ₗ[AuxiliaryPathType k Q]
        M.carrier)
    exact ⟨oppositeReconstructionLinearEquiv (k := k) (Q := Q) (V := M.carrier)⟩
  right_inv := by
    intro x
    refine Quotient.inductionOn x fun R => ?_
    apply Quotient.sound
    letI : AddCommGroup (DirectSum Q (oppositeVertexFamily R)) :=
      Module.addCommMonoidToAddCommGroup k
    letI : Module (AuxiliaryPathType k Q) (DirectSum Q (oppositeVertexFamily R)) := oppositeDirectSumAlgebraModule R
    letI : IsScalarTower k (AuxiliaryPathType k Q) (DirectSum Q (oppositeVertexFamily R)) :=
      oppositeDirectSumAlgebraModule_scalarTower R
    change (oppositeRepresentationSetoid k Q).r
      (OppositeModuleModel.toOppositeRepresentation k Q (OppositeModuleModel.ofOppositeRepresentation k Q R)) R
    refine ⟨?_⟩
    let e := toModuleOppositeRepresentationEquiv R
    let esymm : AuxiliaryQuiverEquivData k Qᵒᵖ
        (oppositeRepresentationOfModule (k := k) (V := DirectSum Q (oppositeVertexFamily R))) R := {
      app := fun i => (e.app i).symm
      naturality := fun f x => by
        rw [LinearEquiv.symm_apply_eq, e.naturality f, LinearEquiv.apply_symm_apply] }
    exact esymm

end IsoClasses

end RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType

namespace RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType

universe u v w q

section Forward

variable {k : Type u} {Q : Type v} [Field k] [Quiver Q] [DecidableEq Q] [Fintype Q]
variable {V : Type w} [AddCommGroup V] [Module k V]
  [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V]

/-- The algebra element associated with a quiver arrow. -/
noncomputable def arrowElement {i j : Q} (e : i ⟶ j) : AuxiliaryOppositeType k Q :=
  auxiliaryElementOfPath (k := k) ⟨i, j, e.toPath⟩

/-- The algebra action as an algebra homomorphism into scalar-linear endomorphisms. -/
noncomputable def actionAlgHom : AuxiliaryOppositeType k Q →ₐ[k] Module.End k V :=
  Algebra.lsmul k k V

/-- Evaluation of the action algebra homomorphism is scalar multiplication by the algebra element. -/
@[simp] theorem actionAlgHom_apply (a : AuxiliaryOppositeType k Q) (x : V) :
    actionAlgHom (k := k) (V := V) a x = a • x :=
  rfl

/-- The scalar-linear projector onto a module's vertex part. -/
noncomputable def vertexProjector (i : Q) : Module.End k V :=
  actionAlgHom (k := k) (V := V) (auxiliaryVertexElement (k := k) (Q := Q) i)

/-- The submodule of vectors belonging to a specified vertex. -/
@[source_ref "Chapter2/Discussion_quiver_rep_bijection" (role := supporting)]
noncomputable def vertexSubmodule (i : Q) : Submodule k V :=
  LinearMap.range (vertexProjector (k := k) (V := V) i)

/-- A vertex projector acts by the corresponding vertex idempotent. -/
@[simp] theorem vertexProjector_apply (i : Q) (x : V) :
    vertexProjector (k := k) (V := V) i x =
      (auxiliaryVertexElement (k := k) (Q := Q) i : AuxiliaryOppositeType k Q) • x :=
  rfl

/-- Acting by an arrow element sends vectors into the target vertex submodule. -/
theorem arrowElement_smul_mem_target {i j : Q} (e : i ⟶ j) (x : V) :
    (arrowElement (k := k) e : AuxiliaryOppositeType k Q) • x ∈
      vertexSubmodule (k := k) (V := V) j := by
  refine ⟨(arrowElement (k := k) e : AuxiliaryOppositeType k Q) • x, ?_⟩
  rw [vertexProjector_apply, ← mul_smul]
  change (auxiliaryElementOfPath (k := k) ⟨j, j, Quiver.Path.nil⟩ *
      auxiliaryElementOfPath (k := k) ⟨i, j, e.toPath⟩) • x = _
  rw [auxiliaryElement_mul_auxiliaryElement, Quiver.Path.comp_nil]
  rfl

/-- The linear map between vertex submodules induced by a quiver arrow. -/
@[source_ref "Chapter2/Discussion_quiver_rep_bijection" (role := supporting)]
noncomputable def arrowMapOnVertexParts {i j : Q} (e : i ⟶ j) :
    vertexSubmodule (k := k) (V := V) i →ₗ[k] vertexSubmodule (k := k) (V := V) j :=
  LinearMap.restrict (actionAlgHom (k := k) (V := V) (arrowElement (k := k) e))
    (fun x _ => arrowElement_smul_mem_target (k := k) e x)

/-- Constructs a quiver representation from a module over the quiver algebra. -/
@[source_ref "Chapter2/Discussion_quiver_rep_bijection" (role := supporting)]
noncomputable def representationOfModule : AuxiliaryQuiverModuleData k Q where
  obj i := vertexSubmodule (k := k) (V := V) i
  map e := arrowMapOnVertexParts (k := k) (V := V) e

end Forward

section IsoClasses

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{q} Q] [DecidableEq Q] [Fintype Q]

/-- An encoded module structure over the quiver algebra. -/
structure ModuleModel where

  /-- The carrier type of an encoded module structure. -/
  carrier : Type w

  /-- The additive commutative group carried by an encoded module structure. -/
  instAddCommGroup : AddCommGroup carrier

  /-- The scalar-field module structure on the carrier. -/
  instScalarModule : Module k carrier

  /-- The quiver-algebra module structure on the carrier. -/
  instAlgebraModule : Module (AuxiliaryOppositeType k Q) carrier

  /-- The field, quiver algebra, and carrier form a scalar tower. -/
  instIsScalarTower : IsScalarTower k (AuxiliaryOppositeType k Q) carrier

/-- The relation comparing two encoded module structures. -/
def ModuleModel.Related (M N : ModuleModel k Q) : Prop :=
  letI := M.instAddCommGroup
  letI := M.instScalarModule
  letI := M.instAlgebraModule
  letI := M.instIsScalarTower
  letI := N.instAddCommGroup
  letI := N.instScalarModule
  letI := N.instAlgebraModule
  letI := N.instIsScalarTower
  Nonempty (M.carrier ≃ₗ[AuxiliaryOppositeType k Q] N.carrier)

/-- The setoid used to identify equivalent encoded module structures. -/
def moduleModelSetoid : Setoid (ModuleModel k Q) where
  r := ModuleModel.Related k Q
  iseqv := {
    refl := fun M => by
      letI := M.instAddCommGroup
      letI := M.instScalarModule
      letI := M.instAlgebraModule
      letI := M.instIsScalarTower
      exact ⟨LinearEquiv.refl (AuxiliaryOppositeType k Q) M.carrier⟩
    symm := fun {M N} h => by
      letI := M.instAddCommGroup
      letI := M.instScalarModule
      letI := M.instAlgebraModule
      letI := M.instIsScalarTower
      letI := N.instAddCommGroup
      letI := N.instScalarModule
      letI := N.instAlgebraModule
      letI := N.instIsScalarTower
      exact ⟨h.some.symm⟩
    trans := fun {M N R} hMN hNR => by
      letI := M.instAddCommGroup
      letI := M.instScalarModule
      letI := M.instAlgebraModule
      letI := M.instIsScalarTower
      letI := N.instAddCommGroup
      letI := N.instScalarModule
      letI := N.instAlgebraModule
      letI := N.instIsScalarTower
      letI := R.instAddCommGroup
      letI := R.instScalarModule
      letI := R.instAlgebraModule
      letI := R.instIsScalarTower
      exact ⟨hMN.some.trans hNR.some⟩ }

/-- The setoid used to identify equivalent quiver representations. -/
def representationSetoid : Setoid (AuxiliaryQuiverModuleData k Q) where
  r R S := Nonempty (AuxiliaryQuiverEquivData k Q R S)
  iseqv := {
    refl := fun R => ⟨{
      app := fun i => LinearEquiv.refl k (R.obj i)
      naturality := fun _ _ => rfl }⟩
    symm := fun {R S} h => ⟨{
      app := fun i => (h.some.app i).symm
      naturality := fun f x => by
        rw [LinearEquiv.symm_apply_eq, h.some.naturality f, LinearEquiv.apply_symm_apply] }⟩
    trans := fun hRS hST => ⟨{
      app := fun i => (hRS.some.app i).trans (hST.some.app i)
      naturality := fun {i j} f x => by
        simp only [LinearEquiv.trans_apply]
        rw [hRS.some.naturality f, hST.some.naturality f] }⟩ }

/-- The quotient type of encoded module structures. -/
abbrev ModuleModelQuotient := Quotient (moduleModelSetoid k Q)

/-- The quotient type of quiver representations. -/
abbrev RepresentationQuotient := Quotient (representationSetoid k Q)

/-- Extracts a quiver representation from an encoded module structure. -/
noncomputable def ModuleModel.toRepresentation (M : ModuleModel k Q) :
    AuxiliaryQuiverModuleData k Q := by
  letI := M.instAddCommGroup
  letI := M.instScalarModule
  letI := M.instAlgebraModule
  letI := M.instIsScalarTower
  exact representationOfModule (k := k) (Q := Q) (V := M.carrier)

/-- The scalar-linear map along a path in a representation. -/
@[source_ref "Chapter2/Discussion_quiver_rep_bijection" (role := supporting)]
noncomputable def pathLinearMap (R : AuxiliaryQuiverModuleData k Q) {i j : Q}
    (p : Quiver.Path i j) : R.obj i →ₗ[k] R.obj j :=
  Quiver.Path.rec (motive := fun j _ => R.obj i →ₗ[k] R.obj j)
    LinearMap.id (fun _ e ih => R.map e ∘ₗ ih) p

/-- The endomorphism of a representation direct sum associated with a quiver path. -/
@[source_ref "Chapter2/Discussion_quiver_rep_bijection" (role := supporting)]
noncomputable def pathEndomorphism (R : AuxiliaryQuiverModuleData k Q) :
    AuxiliaryBundledPathType Q → Module.End k (DirectSum Q R.obj)
  | ⟨i, j, p⟩ => DirectSum.lof k Q R.obj j ∘ₗ pathLinearMap k Q R p ∘ₗ
      DirectSum.component k Q R.obj i

omit [DecidableEq Q] [Fintype Q] in
/-- The map along an empty path is the identity linear map. -/
@[simp] theorem pathLinearMap_nil (R : AuxiliaryQuiverModuleData k Q) (i : Q) :
    pathLinearMap k Q R (Quiver.Path.nil : Quiver.Path i i) = LinearMap.id :=
  rfl

omit [DecidableEq Q] [Fintype Q] in
/-- The map along a path extended by an arrow is arrow action composed with the path map. -/
@[simp] theorem pathLinearMap_cons (R : AuxiliaryQuiverModuleData k Q) {i j l : Q}
    (p : Quiver.Path i j) (a : j ⟶ l) :
    pathLinearMap k Q R (p.cons a) = R.map a ∘ₗ pathLinearMap k Q R p :=
  rfl

omit [DecidableEq Q] [Fintype Q] in

/-- The map along a composite path is the composite of the two path maps. -/
theorem pathLinearMap_comp (R : AuxiliaryQuiverModuleData k Q) {i j l : Q}
    (p : Quiver.Path i j) (q : Quiver.Path j l) :
    pathLinearMap k Q R (p.comp q) = pathLinearMap k Q R q ∘ₗ pathLinearMap k Q R p := by
  induction q with
  | nil => simp
  | cons q a ih => simp only [Quiver.Path.comp_cons, pathLinearMap_cons, ih, LinearMap.comp_assoc]

omit [DecidableEq Q] [Fintype Q] in
/-- The path map of a single arrow is the representation's arrow map. -/
@[simp] theorem pathLinearMap_singleArrow (R : AuxiliaryQuiverModuleData k Q) {i j : Q} (a : i ⟶ j) :
    pathLinearMap k Q R a.toPath = R.map a := by
  rw [Quiver.Hom.toPath, pathLinearMap_cons, pathLinearMap_nil, LinearMap.comp_id]

omit [Fintype Q] in
/-- A path endomorphism is the target inclusion after the path map and source projection. -/
theorem pathEndomorphism_eq_inclusion_comp (R : AuxiliaryQuiverModuleData k Q) {i j : Q} (p : Quiver.Path i j) :
    pathEndomorphism k Q R ⟨i, j, p⟩ =
      DirectSum.lof k Q R.obj j ∘ₗ pathLinearMap k Q R p ∘ₗ
        DirectSum.component k Q R.obj i :=
  rfl

omit [Fintype Q] in

/-- Composable paths give the product of their direct-sum endomorphisms. -/
theorem pathEndomorphism_comp (R : AuxiliaryQuiverModuleData k Q) {i j l : Q}
    (p : Quiver.Path i j) (q : Quiver.Path j l) :
    pathEndomorphism k Q R ⟨j, l, q⟩ * pathEndomorphism k Q R ⟨i, j, p⟩ =
      pathEndomorphism k Q R ⟨i, l, p.comp q⟩ := by
  ext x
  simp only [Module.End.mul_apply, pathEndomorphism_eq_inclusion_comp, LinearMap.comp_apply,
    DirectSum.component.lof_self, pathLinearMap_comp]

omit [Fintype Q] in
/-- Direct-sum endomorphisms of paths with mismatched intermediate vertices multiply to zero. -/
theorem pathEndomorphism_mul_eq_zero (R : AuxiliaryQuiverModuleData k Q) {i j l m : Q}
    (p : Quiver.Path i j) (q : Quiver.Path l m) (h : j ≠ l) :
    pathEndomorphism k Q R ⟨l, m, q⟩ * pathEndomorphism k Q R ⟨i, j, p⟩ = 0 := by
  ext x
  simp only [Module.End.mul_apply, pathEndomorphism_eq_inclusion_comp, LinearMap.comp_apply, LinearMap.zero_apply]
  rw [DirectSum.component.of, dif_neg h, map_zero, map_zero]

/-- A linear action of the opposite path-composition algebra on the representation direct sum. -/
noncomputable def oppositeLinearAction (R : AuxiliaryQuiverModuleData k Q) :
    AuxiliaryPathType k Q →ₗ[k] Module.End k (DirectSum Q R.obj) :=
  Finsupp.lsum k fun x => (LinearMap.id : k →ₗ[k] k).smulRight (pathEndomorphism k Q R x)

/-- The opposite linear action of a scalar-supported path is scalar multiplication of its path endomorphism. -/
theorem oppositeLinearAction_single (R : AuxiliaryQuiverModuleData k Q) (x : AuxiliaryBundledPathType Q) (c : k) :
    oppositeLinearAction k Q R (Finsupp.single x c) = c • pathEndomorphism k Q R x := by
  change (Finsupp.lsum k fun x => (LinearMap.id : k →ₗ[k] k).smulRight (pathEndomorphism k Q R x))
      (Finsupp.single x c) = c • pathEndomorphism k Q R x
  simp only [Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_coe, id_eq]

/-- The opposite linear action of a path basis element is its path endomorphism. -/
theorem oppositeLinearAction_path (R : AuxiliaryQuiverModuleData k Q) (x : AuxiliaryBundledPathType Q) :
    oppositeLinearAction k Q R (AuxiliaryPathType.auxiliaryOfPath (k := k) x) = pathEndomorphism k Q R x := by
  rw [AuxiliaryPathType.auxiliaryOfPath, oppositeLinearAction_single, one_smul]

/-- The opposite linear action sends a product of paths to the reversed product of endomorphisms. -/
theorem oppositeLinearAction_pathProduct (R : AuxiliaryQuiverModuleData k Q)
    (x y : AuxiliaryBundledPathType Q) :
    oppositeLinearAction k Q R (AuxiliaryPathType.auxiliaryProduct x y) =
      pathEndomorphism k Q R y * pathEndomorphism k Q R x := by
  obtain ⟨i, j, p⟩ := x
  obtain ⟨l, m, q⟩ := y
  by_cases h : j = l
  · subst h
    rw [AuxiliaryPathType.auxiliaryProduct_of_composable, oppositeLinearAction_single, one_smul, pathEndomorphism_comp]
  · rw [AuxiliaryPathType.auxiliaryProduct_of_not_composable _ _ h, map_zero, pathEndomorphism_mul_eq_zero k Q R p q h]

/-- The opposite linear action reverses multiplication. -/
theorem oppositeLinearAction_mul (R : AuxiliaryQuiverModuleData k Q) (f g : AuxiliaryPathType k Q) :
    oppositeLinearAction k Q R (f * g) = oppositeLinearAction k Q R g * oppositeLinearAction k Q R f := by
  induction f using AuxiliaryPathType.induction_on with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, mul_add]
  | single x a =>
    induction g using AuxiliaryPathType.induction_on with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, add_mul]
    | single y b =>
      rw [AuxiliaryPathType.single_mul_single, map_smul, oppositeLinearAction_pathProduct,
        oppositeLinearAction_single, oppositeLinearAction_single, smul_mul_smul_comm]
      ac_rfl

/-- The scalar-linear map sending algebra elements to endomorphisms of the representation direct sum. -/
noncomputable def directSumLinearAction (R : AuxiliaryQuiverModuleData k Q) :
    AuxiliaryOppositeType k Q →ₗ[k] Module.End k (DirectSum Q R.obj) where
  toFun a := oppositeLinearAction k Q R a.unop
  map_add' a b := by rw [MulOpposite.unop_add, map_add]
  map_smul' c a := by simp

/-- The direct-sum linear action of a path element is its path endomorphism. -/
@[simp] theorem directSumLinearAction_path (R : AuxiliaryQuiverModuleData k Q) (x : AuxiliaryBundledPathType Q) :
    directSumLinearAction k Q R (auxiliaryElementOfPath (k := k) x) = pathEndomorphism k Q R x :=
  oppositeLinearAction_path k Q R x

/-- The sum of all component projections followed by inclusions is the identity on the direct sum. -/
theorem sum_inclusion_component_eq_id (R : AuxiliaryQuiverModuleData k Q) :
    (∑ i : Q, DirectSum.lof k Q R.obj i ∘ₗ DirectSum.component k Q R.obj i) =
      LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
  conv_rhs => rw [← DirectSum.sum_univ_of x]
  exact Finset.sum_congr rfl fun i _ => by
    rw [DirectSum.lof_eq_of, ← DirectSum.apply_eq_component]

/-- The direct-sum linear action sends one to the identity endomorphism. -/
theorem directSumLinearAction_one (R : AuxiliaryQuiverModuleData k Q) : directSumLinearAction k Q R 1 = 1 := by
  change oppositeLinearAction k Q R 1 = 1
  rw [AuxiliaryPathType.one_eq_sum_ofPath_vertexPath, map_sum, Module.End.one_eq_id,
    ← sum_inclusion_component_eq_id k Q R]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [oppositeLinearAction_path, pathEndomorphism_eq_inclusion_comp, pathLinearMap_nil, LinearMap.id_comp]

/-- The direct-sum linear action preserves multiplication. -/
theorem directSumLinearAction_mul (R : AuxiliaryQuiverModuleData k Q) (a b : AuxiliaryOppositeType k Q) :
    directSumLinearAction k Q R (a * b) = directSumLinearAction k Q R a * directSumLinearAction k Q R b := by
  change oppositeLinearAction k Q R (b.unop * a.unop) =
    oppositeLinearAction k Q R a.unop * oppositeLinearAction k Q R b.unop
  exact oppositeLinearAction_mul k Q R b.unop a.unop

/-- The quiver-algebra action on a representation direct sum as an algebra homomorphism. -/
noncomputable def directSumActionAlgHom (R : AuxiliaryQuiverModuleData k Q) :
    AuxiliaryOppositeType k Q →ₐ[k] Module.End k (DirectSum Q R.obj) :=
  AlgHom.ofLinearMap (directSumLinearAction k Q R) (directSumLinearAction_one k Q R) (directSumLinearAction_mul k Q R)

/-- The direct-sum action algebra homomorphism agrees pointwise with its underlying linear construction. -/
@[simp] theorem directSumActionAlgHom_eq_linearAction (R : AuxiliaryQuiverModuleData k Q) (a : AuxiliaryOppositeType k Q) :
    directSumActionAlgHom k Q R a = directSumLinearAction k Q R a :=
  rfl

/-- The action algebra homomorphism sends a path element to its direct-sum endomorphism. -/
theorem directSumActionAlgHom_path (R : AuxiliaryQuiverModuleData k Q) (x : AuxiliaryBundledPathType Q) :
    directSumActionAlgHom k Q R (auxiliaryElementOfPath (k := k) x) = pathEndomorphism k Q R x := by
  rw [directSumActionAlgHom_eq_linearAction, directSumLinearAction_path]

/-- The representation direct sum as a module over the quiver algebra. -/
@[reducible] noncomputable def directSumAlgebraModule (R : AuxiliaryQuiverModuleData k Q) :
    Module (AuxiliaryOppositeType k Q) (DirectSum Q R.obj) :=
  Module.compHom _ (directSumActionAlgHom k Q R).toRingHom

/-- Algebra scalar multiplication on the direct sum is evaluation of the action homomorphism. -/
theorem directSumAlgebraModule_smul (R : AuxiliaryQuiverModuleData k Q) (a : AuxiliaryOppositeType k Q)
    (x : DirectSum Q R.obj) :
    (letI := directSumAlgebraModule k Q R; a • x) = directSumActionAlgHom k Q R a x :=
  rfl

/-- The direct-sum algebra-module structure is compatible with field scalars. -/
theorem directSumAlgebraModule_scalarTower (R : AuxiliaryQuiverModuleData k Q) :
    letI := directSumAlgebraModule k Q R
    IsScalarTower k (AuxiliaryOppositeType k Q) (DirectSum Q R.obj) := by
  letI := directSumAlgebraModule k Q R
  refine ⟨fun c a x => ?_⟩
  change directSumActionAlgHom k Q R (c • a) x = c • directSumActionAlgHom k Q R a x
  rw [map_smul, LinearMap.smul_apply]

/-- The arrow map on vertex parts is given by algebra action. -/
@[simp] theorem arrowMapOnVertexParts_apply {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V]
    {i j : Q} (a : i ⟶ j) (x : vertexSubmodule (k := k) (V := V) i) :
    ((arrowMapOnVertexParts (k := k) (V := V) a x : vertexSubmodule (k := k) (V := V) j) : V) =
      (arrowElement (k := k) a : AuxiliaryOppositeType k Q) • (x : V) :=
  rfl

/-- The image of a vertex projector lies in its vertex submodule. -/
theorem vertexProjector_mem {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V]
    (i : Q) (x : V) :
    vertexProjector (k := k) (V := V) i x ∈ vertexSubmodule (k := k) (V := V) i :=
  LinearMap.mem_range_self _ x

/-- A vertex projector fixes every vector in its vertex submodule. -/
theorem vertexProjector_eq_self_of_mem {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V]
    {i : Q} {x : V} (hx : x ∈ vertexSubmodule (k := k) (V := V) i) :
    vertexProjector (k := k) (V := V) i x = x := by
  obtain ⟨y, rfl⟩ := hx
  simp only [vertexProjector_apply, ← mul_smul, auxiliaryVertexElement]
  rw [auxiliaryElement_mul_auxiliaryElement, Quiver.Path.nil_comp]

/-- Projectors at distinct vertices compose to zero. -/
theorem vertexProjector_comp_eq_zero {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V]
    {i j : Q} (h : i ≠ j) :
    (vertexProjector (k := k) (V := V) i).comp (vertexProjector (k := k) (V := V) j) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, vertexProjector_apply, ← mul_smul, LinearMap.zero_apply,
    auxiliaryVertexElement]
  rw [auxiliaryElement_mul_auxiliaryElement_eq_zero Quiver.Path.nil Quiver.Path.nil h.symm, zero_smul]

/-- The sum of all vertex projectors is the identity endomorphism. -/
theorem sum_vertexProjector_eq_one {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V] :
    (∑ i : Q, vertexProjector (k := k) (V := V) i) = 1 := by
  change (∑ i : Q, actionAlgHom (k := k) (V := V) (auxiliaryVertexElement (k := k) (Q := Q) i)) = 1
  rw [← map_sum, sum_auxiliaryVertexElement_eq_one, map_one]

/-- The family of vertex submodules is an internal direct sum. -/
theorem vertexParts_isInternal {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V] :
    DirectSum.IsInternal (fun i : Q => vertexSubmodule (k := k) (V := V) i) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hxsup
    have hker : (⨆ (j) (_ : j ≠ i), vertexSubmodule (k := k) (V := V) j) ≤
        LinearMap.ker (vertexProjector (k := k) (V := V) i) := by
      refine iSup₂_le fun j hj => ?_
      change LinearMap.range (vertexProjector (k := k) (V := V) j) ≤ _
      rw [LinearMap.range_le_ker_iff]
      exact vertexProjector_comp_eq_zero k Q hj.symm
    have hzero : vertexProjector (k := k) (V := V) i x = 0 := by
      rw [← LinearMap.mem_ker]
      exact hker hxsup
    rw [← vertexProjector_eq_self_of_mem k Q hx, hzero]
  · rw [eq_top_iff]
    intro x _
    have hsum : (∑ i : Q, vertexProjector (k := k) (V := V) i) x = x := by
      rw [sum_vertexProjector_eq_one k Q, Module.End.one_apply]
    rw [← hsum, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (vertexProjector_mem k Q i x)

/-- A linear equivalence of algebra modules induces an equivalence of their associated representations. -/
noncomputable def representationEquivOfModuleEquiv {V W : Type*}
    [AddCommGroup V] [Module k V] [Module (AuxiliaryOppositeType k Q) V]
    [IsScalarTower k (AuxiliaryOppositeType k Q) V]
    [AddCommGroup W] [Module k W] [Module (AuxiliaryOppositeType k Q) W]
    [IsScalarTower k (AuxiliaryOppositeType k Q) W]
    (e : V ≃ₗ[AuxiliaryOppositeType k Q] W) :
    AuxiliaryQuiverEquivData k Q (representationOfModule (k := k) (Q := Q) (V := V))
      (representationOfModule (k := k) (Q := Q) (V := W)) where
  app i := LinearEquiv.ofLinear
    (LinearMap.codRestrict _
      ((e.restrictScalars k).toLinearMap.comp
        (Submodule.subtype (vertexSubmodule (k := k) (V := V) i)))
      (fun (x : vertexSubmodule (k := k) (V := V) i) => by
        refine ⟨e (x : V), ?_⟩
        rw [vertexProjector_apply, ← e.map_smul, ← vertexProjector_apply,
          vertexProjector_eq_self_of_mem k Q x.2]
        rfl))
    (LinearMap.codRestrict _
      ((e.symm.restrictScalars k).toLinearMap.comp
        (Submodule.subtype (vertexSubmodule (k := k) (V := W) i)))
      (fun (x : vertexSubmodule (k := k) (V := W) i) => by
        refine ⟨e.symm (x : W), ?_⟩
        rw [vertexProjector_apply, ← e.symm.map_smul, ← vertexProjector_apply,
          vertexProjector_eq_self_of_mem k Q x.2]
        rfl))
    (by
      refine LinearMap.ext fun x => ?_
      let xw : vertexSubmodule (k := k) (V := W) i := x
      apply Subtype.ext
      exact e.apply_symm_apply (xw : W))
    (by
      refine LinearMap.ext fun x => ?_
      let xv : vertexSubmodule (k := k) (V := V) i := x
      apply Subtype.ext
      exact e.symm_apply_apply (xv : V))
  naturality a x := by
    apply Subtype.ext
    let xv : vertexSubmodule (k := k) (V := V) _ := x
    change e ((arrowElement (k := k) a : AuxiliaryOppositeType k Q) • (xv : V)) =
      (arrowElement (k := k) a : AuxiliaryOppositeType k Q) • e (xv : V)
    exact e.map_smul _ _

/-- The algebra element of a path extended by an arrow is the corresponding product. -/
theorem pathElement_cons {i j l : Q} (p : Quiver.Path i j) (a : j ⟶ l) :
    (auxiliaryElementOfPath (k := k) (⟨i, l, p.cons a⟩ : AuxiliaryBundledPathType Q) : AuxiliaryOppositeType k Q) =
      arrowElement (k := k) a * auxiliaryElementOfPath (k := k) (⟨i, j, p⟩ : AuxiliaryBundledPathType Q) := by
  rw [arrowElement, auxiliaryElement_mul_auxiliaryElement, Quiver.Path.comp_toPath_eq_cons]

/-- Path-element action on a source vertex vector agrees with the representation path map into the target vertex part. -/
theorem pathElement_smul_vertex {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V]
    {i j : Q} (p : Quiver.Path i j) :
    ∀ y : vertexSubmodule (k := k) (V := V) i,
      (auxiliaryElementOfPath (k := k) (⟨i, j, p⟩ : AuxiliaryBundledPathType Q) : AuxiliaryOppositeType k Q) • (y : V) =
        (vertexSubmodule (k := k) (V := V) j).subtype
          (pathLinearMap k Q (representationOfModule (k := k) (Q := Q) (V := V)) p y) := by
  induction p with
  | nil =>
      intro y
      rw [pathLinearMap_nil, LinearMap.id_apply]
      change (auxiliaryVertexElement (k := k) (Q := Q) i : AuxiliaryOppositeType k Q) • (y : V) = (y : V)
      rw [← vertexProjector_apply]
      exact vertexProjector_eq_self_of_mem k Q y.2
  | cons p a ih =>
      intro y
      rw [pathElement_cons, mul_smul, ih y]
      let z : vertexSubmodule (k := k) (V := V) _ :=
        pathLinearMap k Q (representationOfModule (k := k) (Q := Q) (V := V)) p y
      change (arrowElement (k := k) a : AuxiliaryOppositeType k Q) • (z : V) =
        (vertexSubmodule (k := k) (V := V) _).subtype (arrowMapOnVertexParts (k := k) (V := V) a z)
      exact (arrowMapOnVertexParts_apply k Q a z).symm

attribute [local instance] directSumAlgebraModule

/-- The direct sum reconstructed from a module representation inherits the expected scalar tower. -/
local instance reconstructedScalarTower {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V] :
    IsScalarTower k (AuxiliaryOppositeType k Q)
      (DirectSum Q (representationOfModule (k := k) (Q := Q) (V := V)).obj) :=
  directSumAlgebraModule_scalarTower k Q (representationOfModule (k := k) (Q := Q) (V := V))

private noncomputable abbrev coeV {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V] :
    DirectSum Q (representationOfModule (k := k) (Q := Q) (V := V)).obj →ₗ[k] V :=
  DirectSum.coeLinearMap (fun i => vertexSubmodule (k := k) (V := V) i)

private theorem coeV_lof {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V]
    (i : Q) (x : (representationOfModule (k := k) (Q := Q) (V := V)).obj i) :
    coeV (k := k) (Q := Q) (V := V)
        (DirectSum.lof k Q (representationOfModule (k := k) (Q := Q) (V := V)).obj i x) =
      (vertexSubmodule (k := k) (V := V) i).subtype x :=
  DirectSum.coeLinearMap_lof (fun i => vertexSubmodule (k := k) (V := V) i) i x

/-- Path action on a reconstructed direct sum agrees with the underlying module action. -/
theorem pathAction_onDirectSum {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V]
    (x : AuxiliaryBundledPathType Q)
    (m : DirectSum Q (representationOfModule (k := k) (Q := Q) (V := V)).obj) :
    coeV (k := k) (Q := Q) (V := V)
        (pathEndomorphism k Q (representationOfModule (k := k) (Q := Q) (V := V)) x m) =
      (auxiliaryElementOfPath (k := k) x : AuxiliaryOppositeType k Q) •
        coeV (k := k) (Q := Q) (V := V) m := by
  obtain ⟨i, j, p⟩ := x
  have key : (coeV (k := k) (Q := Q) (V := V)).comp
        (pathEndomorphism k Q (representationOfModule (k := k) (Q := Q) (V := V)) ⟨i, j, p⟩) =
      (actionAlgHom (k := k) (V := V) (auxiliaryElementOfPath (k := k) ⟨i, j, p⟩)).comp
        (coeV (k := k) (Q := Q) (V := V)) := by
    refine DirectSum.linearMap_ext k fun l => LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, pathEndomorphism_eq_inclusion_comp]
    rw [coeV_lof, coeV_lof]
    by_cases h : l = i
    · subst h
      rw [DirectSum.component.lof_self]
      exact (pathElement_smul_vertex k Q p y).symm
    · rw [DirectSum.component.of, dif_neg h]
      have hzero : (vertexSubmodule (k := k) (V := V) j).subtype
          (pathLinearMap k Q (representationOfModule (k := k) (Q := Q) (V := V)) p
            (0 : vertexSubmodule (k := k) (V := V) i)) = 0 := by
        change (((vertexSubmodule (k := k) (V := V) j).subtype.comp
          (pathLinearMap k Q (representationOfModule (k := k) (Q := Q) (V := V)) p))
            (0 : vertexSubmodule (k := k) (V := V) i)) = 0
        exact LinearMap.map_zero _
      calc
        _ = 0 := hzero
        _ = (auxiliaryElementOfPath (k := k) (⟨i, j, p⟩ : AuxiliaryBundledPathType Q) : AuxiliaryOppositeType k Q) •
            (vertexSubmodule (k := k) (V := V) l).subtype y := by
          symm
          have hy : (auxiliaryVertexElement (k := k) (Q := Q) l : AuxiliaryOppositeType k Q) •
                (vertexSubmodule (k := k) (V := V) l).subtype y =
              (vertexSubmodule (k := k) (V := V) l).subtype y := by
            rw [← vertexProjector_apply]
            exact vertexProjector_eq_self_of_mem k Q y.2
          rw [← hy, ← mul_smul]
          change (auxiliaryElementOfPath (k := k) ⟨i, j, p⟩ *
              auxiliaryElementOfPath (k := k) ⟨l, l, Quiver.Path.nil⟩) • _ = 0
          rw [auxiliaryElement_mul_auxiliaryElement_eq_zero Quiver.Path.nil p h, zero_smul]
  have h := LinearMap.congr_fun key m
  simpa only [LinearMap.comp_apply, actionAlgHom_apply] using h

/-- The reconstructed direct-sum action agrees with the original algebra action. -/
theorem algebraAction_onDirectSum {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V]
    (a : AuxiliaryOppositeType k Q)
    (m : DirectSum Q (representationOfModule (k := k) (Q := Q) (V := V)).obj) :
    coeV (k := k) (Q := Q) (V := V)
        (directSumActionAlgHom k Q (representationOfModule (k := k) (Q := Q) (V := V)) a m) =
      a • coeV (k := k) (Q := Q) (V := V) m := by
  let f := a.unop
  change coeV (k := k) (Q := Q) (V := V)
      (oppositeLinearAction k Q (representationOfModule (k := k) (Q := Q) (V := V)) f m) =
    (MulOpposite.op f : AuxiliaryOppositeType k Q) • coeV (k := k) (Q := Q) (V := V) m
  induction f using AuxiliaryPathType.induction_on with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, map_add, h₁, h₂,
      MulOpposite.op_add, add_smul]
  | single x c =>
      have hs : (MulOpposite.op (Finsupp.single x c : AuxiliaryPathType k Q) :
          AuxiliaryOppositeType k Q) = c • auxiliaryElementOfPath (k := k) x := by
        apply MulOpposite.unop_injective
        exact (AuxiliaryPathType.smul_single_one c x).symm
      rw [oppositeLinearAction_single, LinearMap.smul_apply, map_smul, pathAction_onDirectSum,
        hs, smul_assoc]

/-- The direct sum reconstructed from a module is linearly equivalent to the original module. -/
noncomputable def reconstructionLinearEquiv {V : Type*} [AddCommGroup V] [Module k V]
    [Module (AuxiliaryOppositeType k Q) V] [IsScalarTower k (AuxiliaryOppositeType k Q) V] :
    DirectSum Q (representationOfModule (k := k) (Q := Q) (V := V)).obj ≃ₗ[AuxiliaryOppositeType k Q] V :=
  let e : DirectSum Q (representationOfModule (k := k) (Q := Q) (V := V)).obj ≃ₗ[k] V :=
    LinearEquiv.ofBijective (coeV (k := k) (Q := Q) (V := V))
      (vertexParts_isInternal k Q)
  { toFun := e
    map_add' := e.map_add
    map_smul' := algebraAction_onDirectSum k Q
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

omit [DecidableEq Q] [Fintype Q] in

/-- A representation equivalence commutes with the linear maps assigned to paths. -/
theorem representationEquiv_commutes_path {R S : AuxiliaryQuiverModuleData k Q}
    (e : AuxiliaryQuiverEquivData k Q R S) {i j : Q} (p : Quiver.Path i j)
    (x : R.obj i) :
    e.app j (pathLinearMap k Q R p x) = pathLinearMap k Q S p (e.app i x) := by
  induction p with
  | nil => simp only [pathLinearMap_nil, LinearMap.id_apply]
  | cons p a ih =>
      simp only [pathLinearMap_cons, LinearMap.comp_apply]
      rw [e.naturality a, ih]

/-- A representation equivalence induces a scalar-linear equivalence of the corresponding direct sums. -/
noncomputable def directSumLinearEquiv {R S : AuxiliaryQuiverModuleData k Q}
    (e : AuxiliaryQuiverEquivData k Q R S) :
    DirectSum Q R.obj ≃ₗ[k] DirectSum Q S.obj :=
  DirectSum.congrLinearEquiv fun i => e.app i

omit [Fintype Q] in
/-- The induced direct-sum equivalence intertwines every path endomorphism. -/
theorem directSumLinearEquiv_intertwinesPath {R S : AuxiliaryQuiverModuleData k Q}
    (e : AuxiliaryQuiverEquivData k Q R S) (x : AuxiliaryBundledPathType Q)
    (m : DirectSum Q R.obj) :
    directSumLinearEquiv k Q e (pathEndomorphism k Q R x m) =
      pathEndomorphism k Q S x (directSumLinearEquiv k Q e m) := by
  induction m using DirectSum.induction_on with
  | zero => simp
  | add m n hm hn =>
      rw [map_add, map_add, hm, hn]
      exact (map_add (pathEndomorphism k Q S x) _ _).symm.trans
        (congrArg (pathEndomorphism k Q S x) ((directSumLinearEquiv k Q e).map_add m n).symm)
  | of l z =>
      rw [← DirectSum.lof_eq_of k]
      obtain ⟨i, j, p⟩ := x
      simp only [pathEndomorphism_eq_inclusion_comp, LinearMap.comp_apply]
      by_cases h : l = i
      · subst h
        rw [DirectSum.component.lof_self]
        simp only [directSumLinearEquiv, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
        rw [DirectSum.component.lof_self]
        exact congrArg (DirectSum.lof k Q S.obj j) (representationEquiv_commutes_path k Q e p z)
      · rw [DirectSum.component.of, dif_neg h, map_zero, map_zero]
        simp only [directSumLinearEquiv, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
          DirectSum.component.of, dif_neg h, map_zero]

/-- The induced direct-sum equivalence intertwines the quiver-algebra actions. -/
theorem directSumLinearEquiv_intertwinesAlgebra {R S : AuxiliaryQuiverModuleData k Q}
    (e : AuxiliaryQuiverEquivData k Q R S) (a : AuxiliaryOppositeType k Q)
    (m : DirectSum Q R.obj) :
    directSumLinearEquiv k Q e (directSumActionAlgHom k Q R a m) =
      directSumActionAlgHom k Q S a (directSumLinearEquiv k Q e m) := by
  let f := a.unop
  change directSumLinearEquiv k Q e (oppositeLinearAction k Q R f m) =
    oppositeLinearAction k Q S f (directSumLinearEquiv k Q e m)
  induction f using AuxiliaryPathType.induction_on with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_apply, map_add, h₁, h₂]
      exact (congrArg
        (fun g : Module.End k (DirectSum Q S.obj) => g (directSumLinearEquiv k Q e m))
        (map_add (oppositeLinearAction k Q S) f₁ f₂)).symm
  | single x c =>
      rw [oppositeLinearAction_single, LinearMap.smul_apply, map_smul, oppositeLinearAction_single,
        LinearMap.smul_apply, directSumLinearEquiv_intertwinesPath]

/-- A representation equivalence induces an algebra-linear equivalence of direct sums. -/
noncomputable def directSumAlgebraLinearEquiv {R S : AuxiliaryQuiverModuleData k Q}
    (e : AuxiliaryQuiverEquivData k Q R S) :
    letI := directSumAlgebraModule k Q R
    letI := directSumAlgebraModule k Q S
    DirectSum Q R.obj ≃ₗ[AuxiliaryOppositeType k Q] DirectSum Q S.obj := by
  letI := directSumAlgebraModule k Q R
  letI := directSumAlgebraModule k Q S
  let ek := directSumLinearEquiv k Q e
  exact {
    toFun := ek
    map_add' := ek.map_add
    map_smul' := fun a m => directSumLinearEquiv_intertwinesAlgebra k Q e a m
    invFun := ek.symm
    left_inv := ek.left_inv
    right_inv := ek.right_inv }

/-- The direct sum of the vertex spaces has an additive commutative group structure. -/
local instance directSumAddCommGroup (R : AuxiliaryQuiverModuleData k Q) :
    AddCommGroup (DirectSum Q R.obj) :=
  Module.addCommMonoidToAddCommGroup k

/-- The field, quiver algebra, and representation direct sum form a scalar tower. -/
local instance directSumScalarTower (R : AuxiliaryQuiverModuleData k Q) :
    IsScalarTower k (AuxiliaryOppositeType k Q) (DirectSum Q R.obj) :=
  directSumAlgebraModule_scalarTower k Q R

/-- On a representation direct sum, a vertex projector is inclusion after component projection. -/
theorem vertexProjector_onDirectSum (R : AuxiliaryQuiverModuleData k Q) (i : Q)
    (m : DirectSum Q R.obj) :
    (vertexProjector (k := k) (V := DirectSum Q R.obj) i) m =
      DirectSum.lof k Q R.obj i (DirectSum.component k Q R.obj i m) := by
  rw [vertexProjector_apply, directSumAlgebraModule_smul, auxiliaryVertexElement, directSumActionAlgHom_path, pathEndomorphism_eq_inclusion_comp]
  simp only [LinearMap.comp_apply, pathLinearMap_nil, LinearMap.id_coe, id_eq]

/-- For a representation direct sum, the vertex submodule is the range of its summand inclusion. -/
theorem vertexSubmodule_eq_range_inclusion (R : AuxiliaryQuiverModuleData k Q) (i : Q) :
    vertexSubmodule (k := k) (V := DirectSum Q R.obj) i =
      LinearMap.range (DirectSum.lof k Q R.obj i) := by
  apply le_antisymm
  · change LinearMap.range (vertexProjector (k := k) (V := DirectSum Q R.obj) i) ≤ _
    rintro x ⟨m, rfl⟩
    rw [vertexProjector_onDirectSum]
    exact LinearMap.mem_range_self _ _
  · rintro x ⟨y, rfl⟩
    change _ ∈ LinearMap.range (vertexProjector (k := k) (V := DirectSum Q R.obj) i)
    exact ⟨_, by rw [vertexProjector_onDirectSum, DirectSum.component.lof_self]⟩

/-- Including the component of an element in its vertex summand recovers that element. -/
theorem vertexInclusion_component (R : AuxiliaryQuiverModuleData k Q) (i : Q)
    (y : vertexSubmodule (k := k) (V := DirectSum Q R.obj) i) :
    DirectSum.lof k Q R.obj i (DirectSum.component k Q R.obj i (y : DirectSum Q R.obj)) =
      (y : DirectSum Q R.obj) := by
  rw [← vertexProjector_onDirectSum]
  exact vertexProjector_eq_self_of_mem k Q y.2

/-- A representation's vertex space is linearly equivalent to its corresponding subspace in the reconstructed direct sum. -/
noncomputable def vertexSpaceEquivVertexPart (R : AuxiliaryQuiverModuleData k Q) (i : Q) :
    R.obj i ≃ₗ[k] vertexSubmodule (k := k) (V := DirectSum Q R.obj) i :=
  LinearEquiv.ofLinear
    (LinearMap.codRestrict _ (DirectSum.lof k Q R.obj i)
      (fun y => by rw [vertexSubmodule_eq_range_inclusion]; exact LinearMap.mem_range_self _ y))
    ((DirectSum.component k Q R.obj i).comp
      (Submodule.subtype (vertexSubmodule (k := k) (V := DirectSum Q R.obj) i)))
    (by
      refine LinearMap.ext fun y => ?_
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        LinearMap.id_coe, id_eq]
      exact vertexInclusion_component k Q R i y)
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        DirectSum.component.lof_self, LinearMap.id_coe, id_eq])

/-- The vertex-space equivalence includes a vector into its direct-sum summand. -/
@[simp] theorem vertexSpaceEquivVertexPart_coe (R : AuxiliaryQuiverModuleData k Q) (i : Q) (x : R.obj i) :
    ((vertexSpaceEquivVertexPart k Q R i x : vertexSubmodule (k := k) (V := DirectSum Q R.obj) i) :
      DirectSum Q R.obj) = DirectSum.lof k Q R.obj i x :=
  rfl

/-- The vertex-space equivalences commute with the maps assigned to arrows. -/
theorem vertexSpaceEquivVertexPart_naturality (R : AuxiliaryQuiverModuleData k Q) {i j : Q}
    (a : i ⟶ j) (x : R.obj i) :
    vertexSpaceEquivVertexPart k Q R j (R.map a x) =
      (representationOfModule (k := k) (Q := Q) (V := DirectSum Q R.obj)).map a
        (vertexSpaceEquivVertexPart k Q R i x) := by
  apply Subtype.ext
  change DirectSum.lof k Q R.obj j (R.map a x) =
    directSumActionAlgHom k Q R (arrowElement (k := k) a) (DirectSum.lof k Q R.obj i x)
  rw [arrowElement, directSumActionAlgHom_path, pathEndomorphism_eq_inclusion_comp]
  simp only [LinearMap.comp_apply, DirectSum.component.lof_self, pathLinearMap_singleArrow]

/-- A representation is equivalent to the representation recovered from its direct-sum module. -/
noncomputable def toModuleRepresentationEquiv (R : AuxiliaryQuiverModuleData k Q) :
    AuxiliaryQuiverEquivData k Q R
      (representationOfModule (k := k) (Q := Q) (V := DirectSum Q R.obj)) where
  app i := vertexSpaceEquivVertexPart k Q R i
  naturality a x := vertexSpaceEquivVertexPart_naturality k Q R a x

/-- Builds an encoded module structure from a quiver representation. -/
noncomputable def ModuleModel.ofRepresentation (R : AuxiliaryQuiverModuleData k Q) :
    ModuleModel k Q where
  carrier := DirectSum Q R.obj
  instAddCommGroup := Module.addCommMonoidToAddCommGroup k
  instScalarModule := inferInstance
  instAlgebraModule := directSumAlgebraModule k Q R
  instIsScalarTower := directSumAlgebraModule_scalarTower k Q R

/-- Related encoded module structures yield equivalent representations. -/
theorem ModuleModel.toRepresentation_respects {M N : ModuleModel k Q}
    (h : (moduleModelSetoid k Q).r M N) :
    (representationSetoid k Q).r
      (M.toRepresentation k Q) (N.toRepresentation k Q) := by
  letI := M.instAddCommGroup
  letI := M.instScalarModule
  letI := M.instAlgebraModule
  letI := M.instIsScalarTower
  letI := N.instAddCommGroup
  letI := N.instScalarModule
  letI := N.instAlgebraModule
  letI := N.instIsScalarTower
  change Nonempty (M.carrier ≃ₗ[AuxiliaryOppositeType k Q] N.carrier) at h
  exact ⟨representationEquivOfModuleEquiv k Q h.some⟩

/-- Equivalent representations yield related encoded module structures. -/
theorem ModuleModel.ofRepresentation_respects {R S : AuxiliaryQuiverModuleData k Q}
    (h : (representationSetoid k Q).r R S) :
    (moduleModelSetoid k Q).r
      (ModuleModel.ofRepresentation k Q R)
      (ModuleModel.ofRepresentation k Q S) := by
  letI : AddCommGroup (DirectSum Q R.obj) := Module.addCommMonoidToAddCommGroup k
  letI : Module (AuxiliaryOppositeType k Q) (DirectSum Q R.obj) := directSumAlgebraModule k Q R
  letI : AddCommGroup (DirectSum Q S.obj) := Module.addCommMonoidToAddCommGroup k
  letI : Module (AuxiliaryOppositeType k Q) (DirectSum Q S.obj) := directSumAlgebraModule k Q S
  change Nonempty (DirectSum Q R.obj ≃ₗ[AuxiliaryOppositeType k Q] DirectSum Q S.obj)
  exact ⟨directSumAlgebraLinearEquiv k Q h.some⟩

/-- Maps an encoded-module quotient class to a representation quotient class. -/
noncomputable def quotientMapToRepresentations :
    ModuleModelQuotient k Q → RepresentationQuotient k Q :=
  Quotient.map (ModuleModel.toRepresentation k Q)
    (fun _ _ => ModuleModel.toRepresentation_respects k Q)

/-- Maps a representation quotient class to an encoded-module quotient class. -/
noncomputable def quotientMapToModules :
    RepresentationQuotient k Q → ModuleModelQuotient k Q :=
  Quotient.map (ModuleModel.ofRepresentation k Q)
    (fun _ _ => ModuleModel.ofRepresentation_respects k Q)

set_option maxHeartbeats 800000 in

/-- The module-model quotient is equivalent to the representation quotient. -/
noncomputable def moduleRepresentationQuotientEquiv :
    ModuleModelQuotient k Q ≃ RepresentationQuotient k Q where
  toFun := quotientMapToRepresentations k Q
  invFun := quotientMapToModules k Q
  left_inv := by
    intro x
    refine Quotient.inductionOn x fun M => ?_
    apply Quotient.sound
    letI := M.instAddCommGroup
    letI := M.instScalarModule
    letI := M.instAlgebraModule
    letI := M.instIsScalarTower
    let FR := representationOfModule (k := k) (Q := Q) (V := M.carrier)
    letI : AddCommGroup (DirectSum Q FR.obj) := Module.addCommMonoidToAddCommGroup k
    letI : Module (AuxiliaryOppositeType k Q) (DirectSum Q FR.obj) := directSumAlgebraModule k Q FR
    change Nonempty
      (DirectSum Q (representationOfModule (k := k) (Q := Q) (V := M.carrier)).obj ≃ₗ[AuxiliaryOppositeType k Q]
        M.carrier)
    exact ⟨reconstructionLinearEquiv k Q⟩
  right_inv := by
    intro x
    refine Quotient.inductionOn x fun R => ?_
    apply Quotient.sound
    letI : AddCommGroup (DirectSum Q R.obj) := Module.addCommMonoidToAddCommGroup k
    letI : Module (AuxiliaryOppositeType k Q) (DirectSum Q R.obj) := directSumAlgebraModule k Q R
    letI : IsScalarTower k (AuxiliaryOppositeType k Q) (DirectSum Q R.obj) :=
      directSumAlgebraModule_scalarTower k Q R
    change (representationSetoid k Q).r
      (ModuleModel.toRepresentation k Q (ModuleModel.ofRepresentation k Q R)) R
    have h : (representationSetoid k Q).r R
        (representationOfModule (k := k) (Q := Q) (V := DirectSum Q R.obj)) :=
      ⟨toModuleRepresentationEquiv k Q R⟩
    exact (representationSetoid k Q).iseqv.symm h

/-- States that a representation and an encoded module structure correspond. -/
@[source_ref "Chapter2/Discussion_quiver_rep_bijection" (role := supporting)]
def RealizesRepresentation (R : AuxiliaryQuiverModuleData k Q) (M : ModuleModel k Q) : Prop :=
  letI := M.instAddCommGroup
  letI := M.instScalarModule
  letI := M.instAlgebraModule
  letI := M.instIsScalarTower
  ∃ e : M.carrier ≃ₗ[k] DirectSum Q R.obj,
    ∀ (i j : Q) (p : Quiver.Path i j) (x : M.carrier),
      e ((auxiliaryElementOfPath (k := k) (⟨i, j, p⟩ : AuxiliaryBundledPathType Q) : AuxiliaryOppositeType k Q) • x) =
        pathEndomorphism k Q R ⟨i, j, p⟩ (e x)

/-- There is an equivalence between quotient classes of encoded modules and representations, compatible with both constructions. -/
@[source_ref "Chapter2/Discussion_path_algebra_intro" (role := primary),
  source_ref "Chapter2/Discussion_quiver_rep_bijection" (role := primary)]
theorem existsModuleRepresentationQuotientEquiv :
    ∃ e : ModuleModelQuotient.{u, v, q, max v w} k Q ≃
        RepresentationQuotient.{u, v, q, max v w} k Q,
      (∀ M : ModuleModel.{u, v, max v w, q} k Q,
        e (Quotient.mk _ M) = Quotient.mk _ (M.toRepresentation k Q)) ∧
      (∀ R : AuxiliaryQuiverModuleData.{u, v, max v w, q} k Q,
        ∃ M : ModuleModel.{u, v, max v w, q} k Q,
        RealizesRepresentation k Q R M ∧
          e.symm (Quotient.mk _ R) = Quotient.mk _ M) := by
  refine ⟨moduleRepresentationQuotientEquiv k Q, ?_, ?_⟩
  · intro M
    rfl
  · intro R
    refine ⟨ModuleModel.ofRepresentation k Q R, ?_, ?_⟩
    · change ∃ e : DirectSum Q R.obj ≃ₗ[k] DirectSum Q R.obj,
        ∀ (i j : Q) (p : Quiver.Path i j) (x : DirectSum Q R.obj),
          e (directSumActionAlgHom k Q R (auxiliaryElementOfPath (k := k) (⟨i, j, p⟩ : AuxiliaryBundledPathType Q)) x) =
            pathEndomorphism k Q R ⟨i, j, p⟩ (e x)
      refine ⟨LinearEquiv.refl k _, ?_⟩
      intro i j p x
      simp only [LinearEquiv.refl_apply, directSumActionAlgHom_path]
    · rfl

end IsoClasses

end RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType
