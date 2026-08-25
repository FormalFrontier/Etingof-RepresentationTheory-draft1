/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryQuiverRepresentationTransform
import RepresentationTheory.QuiverRepresentationQuotientTransform
import RepresentationTheory.QuiverRepresentation.Auxiliary
import Mathlib.LinearAlgebra.Dimension.Finrank
import RepresentationTheory.Alignment.Attribute

/-- Takes a finite index type, a map into V, a distinguished element, an integer-valued function on V, and a target element, and returns an integer. -/
def RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt
    {V : Type*} [DecidableEq V]
    {ι : Type*} [Fintype ι] (adj : ι → V)
    (i : V) (d : V → ℤ) : V → ℤ :=
  fun v => if v = i then -d i + ∑ a, d (adj a) else d v

/-- Takes the supplied parameter and a vertex of its quiver, and returns a natural number. -/
noncomputable def RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryNat
    (k : Type*) [CommSemiring k] {Q : Type*} {inst : Quiver Q}
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q _ inst)
    (v : Q) : ℕ :=
  @Module.finrank k (ρ.obj v) _ (ρ.addCommMonoid v) (ρ.moduleInstance v)

/-- If the displayed map is surjective, the integer cast of the conclusion's natural-valued expression equals its other displayed integer-valued expression at every vertex. -/
@[source_ref "Chapter6/Proposition6.6.8" (role := primary)]
theorem RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_surjective
    {k : Type*} [Field k]
    {V : Type*} [DecidableEq V] [Quiver V]
    {i : V} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty V i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k V)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt V i)]
    (hsurj : Function.Surjective (ρ.auxiliaryDirectSumMap i)) :
    ∀ v, ((RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation
      V i hi ρ).auxiliaryNat k v : ℤ) =
      RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt
        (fun (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt V i) =>
          a.1) i (fun w => (Module.finrank k (ρ.obj w) : ℤ)) v := by
  intro v
  unfold RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt
  by_cases hv : v = i
  · subst hv
    simp only [ite_true]
    unfold RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryNat
    rw [(RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt
      hi ρ).finrank_eq]
    · change (Module.finrank k ↥(ρ.auxiliaryDirectSumMap v).ker : ℤ) =
        -(Module.finrank k (ρ.obj v) : ℤ) +
        ∑ x : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt V v,
          (Module.finrank k (ρ.obj x.fst) : ℤ)
      have hrn : Module.finrank k (ρ.obj v) +
          Module.finrank k ↥(ρ.auxiliaryDirectSumMap v).ker =
          ∑ a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt V v,
            Module.finrank k (ρ.obj a.1) := by
        haveI : DecidableEq
            (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt V v) :=
          Classical.decEq _
        letI : AddCommGroup
            (DirectSum
              (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt V v)
              (fun a => ρ.obj a.1)) :=
          RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing
            (k := k)
        letI : AddCommGroup (ρ.obj v) :=
          RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing
            (k := k)
        have h := LinearMap.finrank_range_add_finrank_ker (ρ.auxiliaryDirectSumMap v)
        have hrange : LinearMap.range (ρ.auxiliaryDirectSumMap v) = ⊤ :=
          LinearMap.range_eq_top.mpr hsurj
        rw [hrange, finrank_top] at h
        have hds := Module.finrank_directSum (R := k)
          (fun
            (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt V v) =>
            ρ.obj a.1)
        linarith
      have hrn_z : (Module.finrank k (ρ.obj v) : ℤ) +
          (Module.finrank k ↥(ρ.auxiliaryDirectSumMap v).ker : ℤ) =
          ∑ a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt V v,
            (Module.finrank k (ρ.obj a.fst) : ℤ) := by
        exact_mod_cast hrn
      linarith
  · simp only [hv, ite_false]
    unfold RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryNat
    rw [(RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe
      hi ρ v hv).finrank_eq]

/-- If the displayed map is injective, the integer cast of the conclusion's natural-valued expression equals its other displayed integer-valued expression at every vertex. -/
@[source_ref "Chapter6/Proposition6.6.8" (role := primary)]
theorem RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_injective
    {k : Type*} [Field k]
    {V : Type*} [DecidableEq V] [Quiver V]
    {i : V} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition V i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k V)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i)]
    (hinj : Function.Injective (ρ.outgoingDirectSumMap i)) :
    ∀ v, ((RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation
      V i hi ρ).auxiliaryNat k v : ℤ) =
      RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt
        (fun (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V i) =>
          a.1) i (fun w => (Module.finrank k (ρ.obj w) : ℤ)) v := by
  intro v
  unfold RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt
  by_cases hv : v = i
  · subst hv
    simp only [ite_true]
    haveI : DecidableEq
        (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V v) :=
      Classical.decEq _
    letI : AddCommGroup
        (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V v)
          (fun a => ρ.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (ρ.obj v) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    unfold RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryNat
    rw [(RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient
      hi ρ).finrank_eq]
    · change
        (Module.finrank k
          ((DirectSum
            (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V v)
            (fun a => ρ.obj a.1)) ⧸ LinearMap.range (ρ.outgoingDirectSumMap v)) : ℤ) =
          -(Module.finrank k (ρ.obj v) : ℤ) +
          ∑ x : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V v,
            (Module.finrank k (ρ.obj x.fst) : ℤ)
      have hrn :
          Module.finrank k
              ((DirectSum
                (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V v)
                (fun a => ρ.obj a.1)) ⧸ LinearMap.range (ρ.outgoingDirectSumMap v)) +
            Module.finrank k (ρ.obj v) =
          ∑ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V v,
            Module.finrank k (ρ.obj a.1) := by
        have hquot :=
          Submodule.finrank_quotient_add_finrank (LinearMap.range (ρ.outgoingDirectSumMap v))
        have hrange_rn :=
          LinearMap.finrank_range_add_finrank_ker (ρ.outgoingDirectSumMap v)
        have hker : LinearMap.ker (ρ.outgoingDirectSumMap v) = ⊥ :=
          LinearMap.ker_eq_bot.mpr hinj
        rw [hker, finrank_bot] at hrange_rn
        simp at hrange_rn
        have hds := Module.finrank_directSum (R := k)
          (fun
            (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V v) =>
            ρ.obj a.1)
        linarith
      have hrn_z :
          (Module.finrank k
            ((DirectSum
              (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V v)
              (fun a => ρ.obj a.1)) ⧸ LinearMap.range (ρ.outgoingDirectSumMap v)) : ℤ) +
            (Module.finrank k (ρ.obj v) : ℤ) =
          ∑ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow V v,
            (Module.finrank k (ρ.obj a.fst) : ℤ) := by
        exact_mod_cast hrn
      linarith
  · simp only [hv, ite_false]
    unfold RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryNat
    rw [(RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe
      hi ρ v hv).finrank_eq]
