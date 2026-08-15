/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryQuiverRepresentationTransform
import RepresentationTheory.QuiverRepresentationQuotientTransform
import RepresentationTheory.QuiverRepresentation.Auxiliary
import RepresentationTheory.Quiver.LinearAlgebra.Auxiliary
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

/-- An auxiliary proposition on an object of the displayed type, parameterized by a commutative semiring and a quiver. -/
def RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryProperty
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q) : Prop :=
  ∀ v : Q, Subsingleton (ρ.obj v)

/-- Under the given vertex condition, the first projection of every element of the auxiliary sigma type differs from the selected vertex. -/
theorem RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_sigma_fst_ne_vertex
    {Q : Type*} [Quiver Q] {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) : a.1 ≠ i := by
  intro heq; have := a.2; rw [heq] at this; exact (hi i).false this

/-- Produces a quiver hom from the selected vertex to the first projection of an auxiliary sigma element. -/
def RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_from_vertex
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) :
    @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i a.1 :=

  cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne rfl (RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_sigma_fst_ne_vertex hi a)).symm a.2

set_option maxHeartbeats 800000 in

/-- The two displayed evaluations are equal: the auxiliary composite on the left and the direct-sum component on the right, applied to the displayed value. -/
theorem RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_evaluation_eq_component
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q) (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i)
    (ha : a.1 ≠ i)
    (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) i) :
    (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a.1 ha)
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
        (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
        (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) i a.1
        (RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_from_vertex hi a) x) =
    DirectSum.component k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ.obj a.1) a
      ((RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ x).val) := by

  have harr : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryReverseHom ha (RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_from_vertex hi a) = a.2 := by

    rw [RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryReverseHom_eq_cast ha]
    unfold RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_from_vertex
    rw [cast_cast, cast_eq]
  rw [RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliary_arrow_map_from_selected hi ρ ha (RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_from_vertex hi a) x]

  rw [harr]
  rfl

/-- Under the displayed field, quiver, free, and finite hypotheses, the first auxiliary proposition on ρ implies one of two auxiliary propositions on the result of the displayed construction. -/
@[source_ref "Chapter6/Proposition6.6.7" (role := primary)]
theorem RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.AuxiliaryCondition) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition k _ Q
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) ∨
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryProperty k _ Q
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) := by

  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  rcases RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrSurjective hi hρ with hsimple | hsurj
  ·
    right
    intro v

    by_cases hvi : v = i
    · subst hvi

      refine (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ).symm.toEquiv.subsingleton_congr.mp ?_
      have htrivial : ∀ (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q v), Subsingleton (ρ.obj a.1) := by
        intro ⟨j, e⟩
        have hj : j ≠ v := fun h => (hi j).false (h ▸ e)
        rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
        · exact h
        · exfalso
          have h1 := Module.finrank_pos (R := k) (M := ρ.obj j)
          have h2 := hsimple.2 j hj
          omega

      letI : ∀ (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q v), Subsingleton (ρ.obj a.1) := htrivial
      letI : Subsingleton (DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q v) (fun a => ρ.obj a.1)) := by
        infer_instance
      exact subsingleton_of_forall_eq 0 fun ⟨x, _⟩ =>
        Subtype.ext (Subsingleton.eq_zero x)
    ·
      refine (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hvi).symm.toEquiv.subsingleton_congr.mp ?_
      rcases subsingleton_or_nontrivial (ρ.obj v) with h | h
      · exact h
      · exfalso
        have h1 := Module.finrank_pos (R := k) (M := ρ.obj v)
        have h2 := hsimple.2 v hvi
        omega
  ·
    left

    have sink_no_out : ∀ {a b : Q} (_ : a ⟶ b), a ≠ i :=
      fun {_ b} e h => (hi b).false (h ▸ e)

    have hnotsimple : ¬ρ.AuxiliaryVertexCondition i := by
      intro hs

      have htriv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
        intro j hj; rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
        · exact h
        · exfalso; have h1 := Module.finrank_pos (R := k) (M := ρ.obj j)
          have h2 := hs.2 j hj; omega

      haveI : ∀ a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i, Subsingleton (ρ.obj a.1) := by
        intro ⟨j, e⟩; exact htriv j (sink_no_out e)

      haveI : Subsingleton (DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ.obj a.1)) :=
        subsingleton_of_forall_eq 0 fun x => by
          ext ⟨j, e⟩; exact Subsingleton.eq_zero _
      have hVi : Subsingleton (ρ.obj i) :=
        subsingleton_of_forall_eq 0 fun x => by
          obtain ⟨y, hy⟩ := hsurj x
          rw [← hy, Subsingleton.eq_zero y, map_zero]

      haveI := hVi
      have h1 := hs.1
      have h2 := Module.finrank_zero_of_subsingleton (M := ρ.obj i) (R := k)
      omega
    constructor
    ·

      have ⟨j, hj, hjnt⟩ : ∃ j, j ≠ i ∧ Nontrivial (ρ.obj j) := by
        by_contra hall

        have htriv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
          intro j hji
          rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
          · exact h
          · exact absurd ⟨j, hji, h⟩ hall

        haveI : ∀ a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i, Subsingleton (ρ.obj a.1) := by
          intro ⟨j, e⟩; exact htriv j (sink_no_out e)
        haveI : Subsingleton (DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun a => ρ.obj a.1)) :=
          subsingleton_of_forall_eq 0 fun x => by ext ⟨j, e⟩; exact Subsingleton.eq_zero _

        have hVi : Subsingleton (ρ.obj i) :=
          subsingleton_of_forall_eq 0 fun x => by
            obtain ⟨y, hy⟩ := hsurj x
            rw [← hy, Subsingleton.eq_zero y, map_zero]

        obtain ⟨w, hw⟩ := hρ.1
        rcases eq_or_ne w i with rfl | hwi
        · exact not_subsingleton _ hVi
        · exact not_subsingleton _ (htriv w hwi)

      refine ⟨j, ?_⟩

      exact (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ j hj).toEquiv.nontrivial
    ·

      intro W₁ W₂ hW₁ hW₂ hcompl

      classical
      let φ := ρ.auxiliaryDirectSumMap i

      have arrow_ne : ∀ (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i), a.1 ≠ i :=
        fun ⟨j, e⟩ => sink_no_out e

      let W₁_at : ∀ (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i), Submodule k (ρ.obj a.1) :=
        fun a => Submodule.map
          (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a.1 (arrow_ne a)).toLinearMap
          (W₁ a.1)
      let W₂_at : ∀ (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i), Submodule k (ρ.obj a.1) :=
        fun a => Submodule.map
          (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a.1 (arrow_ne a)).toLinearMap
          (W₂ a.1)

      let U₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
        if hv : v = i then
          hv ▸ Submodule.map φ (⨆ (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i),
            Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₁_at a))
        else
          Submodule.map (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hv).toLinearMap (W₁ v)
      let U₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
        if hv : v = i then
          hv ▸ Submodule.map φ (⨆ (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i),
            Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₂_at a))
        else
          Submodule.map (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hv).toLinearMap (W₂ v)

      have hU₁_subrep : ∀ {a' b' : Q} (e' : a' ⟶ b'), ∀ x ∈ U₁ a', ρ.map e' x ∈ U₁ b' := by
        intro a' b' e' x hx
        have ha' : a' ≠ i := sink_no_out e'
        simp only [U₁, dif_neg ha'] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        by_cases hb' : b' = i
        · cases hb'
          simp only [U₁, dif_pos rfl]
          refine Submodule.mem_map.mpr
            ⟨DirectSum.lof k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun c => ρ.obj c.1) ⟨a', e'⟩
              ((RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a' ha') w), ?_, ?_⟩
          · exact Submodule.mem_iSup_of_mem ⟨a', e'⟩
              (Submodule.mem_map.mpr ⟨(RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a' ha') w,
                ⟨w, hw, rfl⟩, rfl⟩)
          · change (ρ.auxiliaryDirectSumMap i) _ = _
            simp only [RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryDirectSumMap, DirectSum.toModule_lof]
            rfl
        · simp only [U₁, dif_neg hb']

          set ê : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a' b' :=
            cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha' hb').symm e' with hê
          have hêorig : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom ha' hb' ê = e' := by
            rw [RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom_eq_cast ha' hb', hê, cast_cast, cast_eq]
          have hmem : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
              (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ)
              a' b' ê ((RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a' ha').symm
                ((RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a' ha') w)) ∈ W₁ b' := by
            simp only [LinearEquiv.symm_apply_apply]
            exact hW₁ ê _ hw
          refine Submodule.mem_map.mpr ⟨_, hmem, ?_⟩
          rw [LinearEquiv.coe_coe,
            RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliary_arrow_map_of_ne hi ρ ha' hb' ê _,
            LinearEquiv.symm_apply_apply, hêorig]
          rfl
      have hU₂_subrep : ∀ {a' b' : Q} (e' : a' ⟶ b'), ∀ x ∈ U₂ a', ρ.map e' x ∈ U₂ b' := by
        intro a' b' e' x hx
        have ha' : a' ≠ i := sink_no_out e'
        simp only [U₂, dif_neg ha'] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        by_cases hb' : b' = i
        · cases hb'
          simp only [U₂, dif_pos rfl]
          refine Submodule.mem_map.mpr
            ⟨DirectSum.lof k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i) (fun c => ρ.obj c.1) ⟨a', e'⟩
              ((RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a' ha') w), ?_, ?_⟩
          · exact Submodule.mem_iSup_of_mem ⟨a', e'⟩
              (Submodule.mem_map.mpr ⟨(RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a' ha') w,
                ⟨w, hw, rfl⟩, rfl⟩)
          · change (ρ.auxiliaryDirectSumMap i) _ = _
            simp only [RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryDirectSumMap, DirectSum.toModule_lof]
            rfl
        · simp only [U₂, dif_neg hb']

          set ê : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a' b' :=
            cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha' hb').symm e' with hê
          have hêorig : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom ha' hb' ê = e' := by
            rw [RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom_eq_cast ha' hb', hê, cast_cast, cast_eq]
          have hmem : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
              (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ)
              a' b' ê ((RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a' ha').symm
                ((RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a' ha') w)) ∈ W₂ b' := by
            simp only [LinearEquiv.symm_apply_apply]
            exact hW₂ ê _ hw
          refine Submodule.mem_map.mpr ⟨_, hmem, ?_⟩
          rw [LinearEquiv.coe_coe,
            RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliary_arrow_map_of_ne hi ρ ha' hb' ê _,
            LinearEquiv.symm_apply_apply, hêorig]
          rfl
      have hU_compl : ∀ v, IsCompl (U₁ v) (U₂ v) := by
        intro v
        by_cases hv : v = i
        · subst hv
          simp only [U₁, U₂, dif_pos rfl]

          have hW_at_compl : ∀ a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q v,
              IsCompl (W₁_at a) (W₂_at a) := by
            intro a
            have hc := hcompl a.1
            let e := RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a.1 (arrow_ne a)
            exact ⟨by
              rw [Submodule.disjoint_def]; intro x hx₁ hx₂
              obtain ⟨w₁, hw₁, rfl⟩ := Submodule.mem_map.mp hx₁
              obtain ⟨w₂, hw₂, hw₂eq⟩ := Submodule.mem_map.mp hx₂
              have : w₁ ∈ W₁ a.1 ⊓ W₂ a.1 := ⟨hw₁, e.injective hw₂eq ▸ hw₂⟩
              rw [hc.1.eq_bot, Submodule.mem_bot] at this
              rw [this, map_zero], by
              rw [codisjoint_iff, eq_top_iff]; intro x _
              obtain ⟨w, rfl⟩ := e.surjective x
              obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ :=
                Submodule.mem_sup.mp (hc.2.eq_top ▸ (Submodule.mem_top : w ∈ ⊤))
              exact Submodule.mem_sup.mpr
                ⟨_, Submodule.mem_map.mpr ⟨w₁, hw₁, rfl⟩,
                 _, Submodule.mem_map.mpr ⟨w₂, hw₂, rfl⟩,
                 (map_add _ _ _).symm⟩⟩

          have hcomp_of_mem :
              ∀ (W_at : ∀ a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q v, Submodule k (ρ.obj a.1))
                (x : DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q v) (fun a => ρ.obj a.1)),
              x ∈ ⨆ a, Submodule.map
                (DirectSum.lof k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q v) (fun a => ρ.obj a.1) a) (W_at a) →
              ∀ a, DirectSum.component k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q v)
                (fun a => ρ.obj a.1) a x ∈ W_at a := by
            intro W_at x hx a
            refine Submodule.iSup_induction
              (motive := fun x => DirectSum.component k _ (fun a => ρ.obj a.1) a x ∈ W_at a)
              (fun b => Submodule.map
                (DirectSum.lof k _ (fun a => ρ.obj a.1) b) (W_at b)) hx ?_ ?_ ?_
            · intro b y hy
              obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hy
              simp only [DirectSum.component.of]
              split
              · next h => exact h ▸ hm
              · exact Submodule.zero_mem _
            · simp only [map_zero]; exact Submodule.zero_mem _
            · exact fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂

          have hker_comp :
              ∀ (W : ∀ v₁ : Q, Submodule k
                  (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
                    (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q v)
                    (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q v hi ρ) v₁))
                (hW_sub : ∀ {a b} (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q v) a b),
                  ∀ x ∈ W a,
                  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
                    (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q v)
                    (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q v hi ρ) a b e x ∈ W b)
                (z : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
                    (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q v)
                    (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q v hi ρ) v),
              z ∈ W v →
              ∀ a, DirectSum.component k _ (fun a => ρ.obj a.1) a
                ((RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z).val) ∈
                Submodule.map
                  (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a.1 (arrow_ne a)).toLinearMap
                  (W a.1) := by
            intro W hW_sub z hz a
            rw [← RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_evaluation_eq_component hi ρ a (arrow_ne a) z]
            exact Submodule.mem_map.mpr ⟨_, hW_sub (RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_from_vertex hi a) z hz, rfl⟩

          have hker_in_S :
              ∀ (W : ∀ v₁ : Q, Submodule k
                  (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
                    (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q v)
                    (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q v hi ρ) v₁))
                (hW_sub : ∀ {a b} (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q v) a b),
                  ∀ x ∈ W a,
                  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
                    (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q v)
                    (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q v hi ρ) a b e x ∈ W b)
                (W_at : ∀ a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q v, Submodule k (ρ.obj a.1))
                (_ : W_at = fun a => Submodule.map
                  (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ a.1 (arrow_ne a)).toLinearMap
                  (W a.1))
                (z : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
                    (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q v)
                    (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q v hi ρ) v),
              z ∈ W v →
              (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z).val ∈
                ⨆ a, Submodule.map
                  (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W_at a) := by
            intro W hW_sub W_at hW_at_def z hz

            have hdecomp : (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z).val =
                DFinsupp.sum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z).val
                  (fun a m => DirectSum.of _ a m) := (DFinsupp.sum_single).symm
            rw [hdecomp]
            apply Submodule.sum_mem
            intro a _
            apply Submodule.mem_iSup_of_mem a
            apply Submodule.mem_map.mpr
            exact ⟨(RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z).val a,
              hW_at_def ▸ hker_comp W hW_sub z hz a, rfl⟩

          constructor
          ·
            rw [Submodule.disjoint_def]
            intro y hy₁ hy₂
            obtain ⟨x₁, hx₁, rfl⟩ := Submodule.mem_map.mp hy₁
            obtain ⟨x₂, hx₂, hφeq⟩ := Submodule.mem_map.mp hy₂

            have hker : x₁ - x₂ ∈ LinearMap.ker φ := by
              rw [LinearMap.mem_ker, map_sub, sub_eq_zero]; exact hφeq.symm

            set z := (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ).symm ⟨x₁ - x₂, hker⟩
            have hzval : (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z).val = x₁ - x₂ := by
              simp [z, LinearEquiv.apply_symm_apply]
            obtain ⟨z₁, hz₁, z₂, hz₂, hzsum⟩ := Submodule.mem_sup.mp
              ((hcompl v).sup_eq_top ▸ (Submodule.mem_top : z ∈ ⊤))

            have hval_sum :
                (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z₁).val +
                (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z₂).val = x₁ - x₂ := by
              change (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z₁ +
                RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z₂).val = x₁ - x₂
              rw [← map_add, hzsum, hzval]

            have hz₁_S := hker_in_S W₁ hW₁ W₁_at rfl z₁ hz₁
            have hz₂_S := hker_in_S W₂ hW₂ W₂_at rfl z₂ hz₂

            have hS_disj : Disjoint
                (⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₁_at a))
                (⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₂_at a)) := by
              rw [Submodule.disjoint_def]; intro x hx₁' hx₂'
              exact DFunLike.ext x 0 fun a => by
                have hmem : DirectSum.component k _ (fun a => ρ.obj a.1) a x ∈
                    W₁_at a ⊓ W₂_at a :=
                  ⟨hcomp_of_mem W₁_at x hx₁' a, hcomp_of_mem W₂_at x hx₂' a⟩
                rwa [(hW_at_compl a).inf_eq_bot, Submodule.mem_bot] at hmem

            have hdiff_S₁ : x₁ - (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z₁).val ∈
                ⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₁_at a) :=
              Submodule.sub_mem _ hx₁ hz₁_S
            have hdiff_S₂ : x₁ - (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z₁).val ∈
                ⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₂_at a) := by
              have : x₁ - (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z₁).val =
                  x₂ + (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z₂).val :=
                sub_eq_iff_eq_add.mp (by rw [sub_sub, hval_sum, sub_sub_cancel])
              rw [this]; exact Submodule.add_mem _ hx₂ hz₂_S
            have hzero := Submodule.disjoint_def.mp hS_disj _ hdiff_S₁ hdiff_S₂

            have hx₁_eq : x₁ = (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z₁).val :=
              sub_eq_zero.mp hzero
            rw [hx₁_eq, LinearMap.mem_ker.mp (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ z₁).2]
          ·
            rw [codisjoint_iff, ← Submodule.map_sup]

            have hS_top :
                (⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₁_at a)) ⊔
                (⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₂_at a)) = ⊤ := by
              rw [eq_top_iff]; intro x _
              refine DirectSum.induction_on x (Submodule.zero_mem _) ?_ ?_
              · intro a m
                obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp
                  ((hW_at_compl a).sup_eq_top ▸ (Submodule.mem_top : m ∈ ⊤))
                rw [show DirectSum.of _ a (m₁ + m₂) =
                  DirectSum.lof k _ (fun a => ρ.obj a.1) a m₁ +
                  DirectSum.lof k _ (fun a => ρ.obj a.1) a m₂ from map_add _ _ _]
                exact Submodule.add_mem _
                  (Submodule.mem_sup_left (Submodule.mem_iSup_of_mem a
                    (Submodule.mem_map.mpr ⟨m₁, hm₁, rfl⟩)))
                  (Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a
                    (Submodule.mem_map.mpr ⟨m₂, hm₂, rfl⟩)))
              · exact fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂
            rw [hS_top, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
        · simp only [U₁, U₂, dif_neg hv]
          have hc := hcompl v
          let φ' := (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hv).toLinearMap
          exact ⟨by
            rw [Submodule.disjoint_def]
            intro x hx1 hx2
            obtain ⟨w₁, hw₁, rfl⟩ := Submodule.mem_map.mp hx1
            obtain ⟨w₂, hw₂, hw₂eq⟩ := Submodule.mem_map.mp hx2
            have heq := (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hv).injective hw₂eq
            have : w₁ ∈ W₁ v ⊓ W₂ v := ⟨hw₁, heq ▸ hw₂⟩
            rw [hc.1.eq_bot] at this
            simp only [Submodule.mem_bot] at this
            rw [this, map_zero],
          by
            rw [codisjoint_iff, eq_top_iff]; intro x _
            obtain ⟨w, rfl⟩ := (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hv).surjective x
            have hw : w ∈ (⊤ : Submodule k _) := Submodule.mem_top
            rw [← hc.2.eq_top, Submodule.mem_sup] at hw
            obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hw
            exact Submodule.mem_sup.mpr
              ⟨_, Submodule.mem_map.mpr ⟨w₁, hw₁, rfl⟩,
               _, Submodule.mem_map.mpr ⟨w₂, hw₂, rfl⟩,
               (map_add _ _ _).symm⟩⟩

      have hindecomp := hρ.2 U₁ U₂ hU₁_subrep hU₂_subrep hU_compl

      suffices transport : ∀ (W : ∀ v, Submodule k
            (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
              (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
              (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) v)),
            (∀ {a b} (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a b),
              ∀ x ∈ W a,
              @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
                (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
                (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) a b e x ∈ W b) →
            (∀ v (hv : v ≠ i), Submodule.map
              (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hv).toLinearMap
              (W v) = ⊥) →
            (∀ v, W v = ⊥) by
        rcases hindecomp with h1 | h2
        · left; exact transport W₁ hW₁ (fun v hv => by
            have := h1 v; simp only [U₁, dif_neg hv] at this; exact this)
        · right; exact transport W₂ hW₂ (fun v hv => by
            have := h2 v; simp only [U₂, dif_neg hv] at this; exact this)

      intro W hW hW_ne v
      by_cases hv : v = i
      ·
        cases hv
        rw [eq_bot_iff]; intro x hx; rw [Submodule.mem_bot]

        have hW_bot : ∀ j, j ≠ i → W j = ⊥ := by
          intro j hj
          have h := hW_ne j hj
          rw [eq_bot_iff] at h ⊢
          intro z hz
          rw [Submodule.mem_bot]
          have hmem := h ⟨z, hz, rfl⟩
          rw [Submodule.mem_bot] at hmem
          exact (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ j hj).injective
            (hmem.trans (map_zero _).symm)

        suffices hzero : (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ) x = 0 from
          (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ).injective (by rw [hzero, map_zero])

        apply Subtype.ext
        change ((RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt hi ρ) x).val = 0
        refine DFunLike.ext _ _ fun a => ?_

        have ha := RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_sigma_fst_ne_vertex hi a

        have hmem := hW (RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_from_vertex hi a) x hx
        rw [hW_bot a.1 ha, Submodule.mem_bot] at hmem

        have hapi := RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_evaluation_eq_component hi ρ a ha x

        rw [hmem, map_zero] at hapi

        exact hapi.symm
      ·
        specialize hW_ne v hv
        rw [eq_bot_iff]
        intro x hx
        rw [eq_bot_iff] at hW_ne
        have hmem : (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hv) x ∈
            Submodule.map
              (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hv).toLinearMap
              (W v) :=
          ⟨x, hx, rfl⟩
        have h0 := hW_ne hmem
        rw [Submodule.mem_bot] at h0 ⊢
        exact (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe hi ρ v hv).injective
          (by rw [h0, map_zero])

/-- Produces a quiver hom from the first projection of an auxiliary sigma element to the selected vertex. -/
noncomputable def RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_to_vertex
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) :
    @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a.1 i := by
  obtain ⟨j, e⟩ := a
  have ha : j ≠ i := by intro heq; rw [heq] at e; exact (hi i).false e
  exact cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq ha rfl).symm e

/-- The displayed auxiliary construction applied to the quiver hom obtained from a sigma element equals that element's second projection. -/
theorem RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_apply_hom_eq_sigma_snd
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) :
    RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex
      (show a.1 ≠ i from fun heq => by obtain ⟨j, e⟩ := a; exact (hi i).false (heq ▸ e))
      (RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_to_vertex hi a) = a.2 := by
  obtain ⟨j, e⟩ := a
  change RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex _ (RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_to_vertex hi ⟨j, e⟩) = e
  have ha : j ≠ i := fun heq => (hi i).false (heq ▸ e)

  rw [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapTo_eq_cast]
  change cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq ha rfl)
    (RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_to_vertex hi ⟨j, e⟩) = e
  unfold RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_to_vertex
  simp only [cast_cast, cast_eq]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

/-- Under the displayed field, quiver, free, finite, and Fintype hypotheses, the first auxiliary proposition on ρ implies one of two auxiliary propositions on the result of the displayed construction. -/
@[source_ref "Chapter6/Proposition6.6.7" (role := primary)]
theorem RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary_of_fintype
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (hρ : ρ.AuxiliaryCondition) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition k _ Q
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) ∨
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryProperty k _ Q
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  rcases RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrInjective hi hρ with hsimple | hinj
  ·
    right
    intro v

    by_cases hvi : v = i
    · subst hvi

      refine (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).symm.toEquiv.subsingleton_congr.mp ?_
      have htrivial : ∀ (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q v), Subsingleton (ρ.obj a.1) := by
        intro ⟨j, e⟩
        have hj : j ≠ v := by intro heq; rw [heq] at e; exact (hi v).false e
        rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
        · exact h
        · exfalso
          have h1 := Module.finrank_pos (R := k) (M := ρ.obj j)
          have h2 := hsimple.2 j hj
          omega

      haveI : Subsingleton (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q v) (fun a => ρ.obj a.1)) :=
        subsingleton_of_forall_eq 0 fun x => DFunLike.ext x 0 fun a => Subsingleton.eq_zero _

      exact @Subsingleton.intro _ fun a b => by
        induction a using Quotient.ind
        induction b using Quotient.ind
        exact congr_arg (Quotient.mk _) (Subsingleton.elim _ _)
    ·
      refine (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hvi).symm.toEquiv.subsingleton_congr.mp ?_
      rcases subsingleton_or_nontrivial (ρ.obj v) with h | h
      · exact h
      · exfalso
        have h1 := Module.finrank_pos (R := k) (M := ρ.obj v)
        have h2 := hsimple.2 v hvi
        omega
  ·
    left

    have source_no_in : ∀ {a b : Q} (_ : a ⟶ b), b ≠ i :=
      fun {a _} e h => (hi a).false (h ▸ e)

    have hnotsimple : ¬ρ.AuxiliaryVertexCondition i := by
      intro hs
      have htriv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
        intro j hj; rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
        · exact h
        · exfalso; have h1 := Module.finrank_pos (R := k) (M := ρ.obj j)
          have h2 := hs.2 j hj; omega
      haveI : ∀ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i, Subsingleton (ρ.obj a.1) := by
        intro ⟨j, e⟩; exact htriv j (by intro heq; rw [heq] at e; exact (hi i).false e)
      haveI : Subsingleton (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
        subsingleton_of_forall_eq 0 fun x => by
          ext ⟨j, e⟩; exact Subsingleton.eq_zero _
      have hVi : Subsingleton (ρ.obj i) :=
        subsingleton_of_forall_eq 0 fun x =>
          hinj (Subsingleton.elim ((ρ.outgoingDirectSumMap i) x) ((ρ.outgoingDirectSumMap i) 0))
      haveI := hVi
      have h1 := hs.1
      have h2 := Module.finrank_zero_of_subsingleton (M := ρ.obj i) (R := k)
      omega
    constructor
    ·
      have ⟨j, hj, hjnt⟩ : ∃ j, j ≠ i ∧ Nontrivial (ρ.obj j) := by
        by_contra hall
        have htriv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
          intro j hji; rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
          · exact h
          · exact absurd ⟨j, hji, h⟩ hall
        haveI : ∀ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i, Subsingleton (ρ.obj a.1) := by
          intro ⟨j, e⟩; exact htriv j (by intro heq; rw [heq] at e; exact (hi i).false e)
        haveI : Subsingleton (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
          subsingleton_of_forall_eq 0 fun x => by ext ⟨j, e⟩; exact Subsingleton.eq_zero _
        have hVi : Subsingleton (ρ.obj i) :=
          subsingleton_of_forall_eq 0 fun x =>
            hinj (Subsingleton.elim ((ρ.outgoingDirectSumMap i) x) ((ρ.outgoingDirectSumMap i) 0))
        obtain ⟨w, hw⟩ := hρ.1
        rcases eq_or_ne w i with rfl | hwi
        · exact not_subsingleton _ hVi
        · exact not_subsingleton _ (htriv w hwi)
      refine ⟨j, ?_⟩

      exact (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ j hj).toEquiv.nontrivial
    ·

      intro W₁ W₂ hW₁ hW₂ hcompl
      classical
      let ψ := ρ.outgoingDirectSumMap i
      have arrow_ne : ∀ (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i), a.1 ≠ i := by
        intro ⟨j, e⟩; intro heq; exact (hi i).false (heq ▸ e)

      let W₁_at : ∀ (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i), Submodule k (ρ.obj a.1) :=
        fun a => Submodule.map
          (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a.1 (arrow_ne a)).toLinearMap
          (W₁ a.1)
      let W₂_at : ∀ (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i), Submodule k (ρ.obj a.1) :=
        fun a => Submodule.map
          (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a.1 (arrow_ne a)).toLinearMap
          (W₂ a.1)

      let U₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
        if hv : v = i then
          hv ▸ ⨅ (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i),
            Submodule.comap (ρ.map a.2) (W₁_at a)
        else
          Submodule.map (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv).toLinearMap (W₁ v)
      let U₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
        if hv : v = i then
          hv ▸ ⨅ (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i),
            Submodule.comap (ρ.map a.2) (W₂_at a)
        else
          Submodule.map (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv).toLinearMap (W₂ v)

      have hW_at_compl : ∀ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i,
          IsCompl (W₁_at a) (W₂_at a) := by
        intro a
        have hc := hcompl a.1
        let e := RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a.1 (arrow_ne a)
        exact ⟨by
          rw [Submodule.disjoint_def]; intro x hx₁ hx₂
          obtain ⟨w₁, hw₁, rfl⟩ := Submodule.mem_map.mp hx₁
          obtain ⟨w₂, hw₂, hw₂eq⟩ := Submodule.mem_map.mp hx₂
          have : w₁ ∈ W₁ a.1 ⊓ W₂ a.1 := ⟨hw₁, e.injective hw₂eq ▸ hw₂⟩
          rw [hc.1.eq_bot, Submodule.mem_bot] at this
          rw [this, map_zero], by
          rw [codisjoint_iff, eq_top_iff]; intro x _
          obtain ⟨w, rfl⟩ := e.surjective x
          obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ :=
            Submodule.mem_sup.mp (hc.2.eq_top ▸ (Submodule.mem_top : w ∈ ⊤))
          exact Submodule.mem_sup.mpr
            ⟨_, Submodule.mem_map.mpr ⟨w₁, hw₁, rfl⟩,
             _, Submodule.mem_map.mpr ⟨w₂, hw₂, rfl⟩,
             (map_add _ _ _).symm⟩⟩

      have hU₁_subrep : ∀ {a' b' : Q} (e' : a' ⟶ b'),
          ∀ x ∈ U₁ a', ρ.map e' x ∈ U₁ b' := by
        intro a' b' e' x hx
        have hb' : b' ≠ i := source_no_in e'
        by_cases ha' : a' = i
        ·
          cases ha'
          simp only [U₁, dif_pos rfl, dif_neg hb'] at hx ⊢

          rw [Submodule.mem_iInf] at hx
          exact hx ⟨b', e'⟩
        ·
          simp only [U₁, dif_neg ha', dif_neg hb'] at hx ⊢
          obtain ⟨w, hw, rfl⟩ := hx

          set ê : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a' b' :=
            cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha' hb').symm e' with hê
          have hêorig : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom ha' hb' ê = e' := by
            rw [RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom_eq_cast ha' hb', hê, cast_cast, cast_eq]
          have hmem : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
              (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ)
              a' b' ê ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a' ha').symm
                ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a' ha') w)) ∈ W₁ b' := by
            simp only [LinearEquiv.symm_apply_apply]
            exact hW₁ ê _ hw
          refine Submodule.mem_map.mpr ⟨_, hmem, ?_⟩
          rw [LinearEquiv.coe_coe,
            RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_of_ne hi ρ ha' hb' ê _,
            LinearEquiv.symm_apply_apply, hêorig]
          rfl
      have hU₂_subrep : ∀ {a' b' : Q} (e' : a' ⟶ b'),
          ∀ x ∈ U₂ a', ρ.map e' x ∈ U₂ b' := by
        intro a' b' e' x hx
        have hb' : b' ≠ i := source_no_in e'
        by_cases ha' : a' = i
        · cases ha'
          simp only [U₂, dif_pos rfl, dif_neg hb'] at hx ⊢
          rw [Submodule.mem_iInf] at hx; exact hx ⟨b', e'⟩
        · simp only [U₂, dif_neg ha', dif_neg hb'] at hx ⊢
          obtain ⟨w, hw, rfl⟩ := hx

          set ê : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a' b' :=
            cast (RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne ha' hb').symm e' with hê
          have hêorig : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom ha' hb' ê = e' := by
            rw [RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryPreserveHom_eq_cast ha' hb', hê, cast_cast, cast_eq]
          have hmem : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
              (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ)
              a' b' ê ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a' ha').symm
                ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ a' ha') w)) ∈ W₂ b' := by
            simp only [LinearEquiv.symm_apply_apply]
            exact hW₂ ê _ hw
          refine Submodule.mem_map.mpr ⟨_, hmem, ?_⟩
          rw [LinearEquiv.coe_coe,
            RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_of_ne hi ρ ha' hb' ê _,
            LinearEquiv.symm_apply_apply, hêorig]
          rfl
      have hU_compl : ∀ v, IsCompl (U₁ v) (U₂ v) := by
        intro v
        by_cases hv : v = i
        ·
          subst hv
          simp only [U₁, U₂, dif_pos rfl]
          constructor
          ·
            rw [Submodule.disjoint_def]
            intro x hx₁ hx₂

            simp only [Submodule.mem_iInf] at hx₁ hx₂
            have hzero := fun a => by
              have hmem : ρ.map a.2 x ∈ W₁_at a ⊓ W₂_at a :=
                ⟨Submodule.mem_comap.mp (hx₁ a), Submodule.mem_comap.mp (hx₂ a)⟩
              rw [(hW_at_compl a).inf_eq_bot, Submodule.mem_bot] at hmem
              exact hmem

            have hψ : ψ x = 0 := by
              change (ρ.outgoingDirectSumMap _) x = 0
              unfold RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.outgoingDirectSumMap
              simp only [LinearMap.sum_apply, LinearMap.comp_apply]
              exact Finset.sum_eq_zero fun a _ => by
                simp [DirectSum.lof_eq_of, hzero a]
            exact hinj (hψ.trans (map_zero ψ).symm)
          ·
            rw [codisjoint_iff, eq_top_iff]; intro x _

            have hdecomp : ∀ a, ∃ y₁ ∈ W₁_at a, ∃ y₂ ∈ W₂_at a,
                ρ.map a.2 x = y₁ + y₂ := by
              intro a
              obtain ⟨y₁, hy₁, y₂, hy₂, heq⟩ :=
                Submodule.mem_sup.mp ((hW_at_compl a).2.eq_top ▸ Submodule.mem_top)
              exact ⟨y₁, hy₁, y₂, hy₂, heq.symm⟩
            choose y₁ hy₁ y₂ hy₂ hsum using hdecomp

            let DS := DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q v) (fun a => ρ.obj a.1)
            let lof : ∀ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q v, ρ.obj a.1 →ₗ[k] DS :=
              DirectSum.lof k _ _
            let z₁ : DS := ∑ a, lof a (y₁ a)
            let z₂ : DS := ∑ a, lof a (y₂ a)
            let mkQ := RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ

            have hmkQ_sum : mkQ z₁ + mkQ z₂ = 0 := by
              rw [← map_add]
              change mkQ (∑ a, lof a (y₁ a) + ∑ a, lof a (y₂ a)) = 0
              rw [← Finset.sum_add_distrib]
              simp_rw [show ∀ a, lof a (y₁ a) + lof a (y₂ a) =
                lof a (y₁ a + y₂ a) from fun a => (map_add (lof a) _ _).symm,
                show ∀ a, y₁ a + y₂ a = ρ.map a.2 x from fun a => (hsum a).symm]
              exact RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap_sum_eq_zero hi ρ x

            have hmkQ_z₁_W₁ : mkQ z₁ ∈ W₁ v := by
              change mkQ (∑ a, lof a (y₁ a)) ∈ W₁ v
              rw [map_sum]
              exact Submodule.sum_mem _ fun ⟨j, ej⟩ _ => by
                have hj : j ≠ v := arrow_ne ⟨j, ej⟩
                let ea := RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_to_vertex hi ⟨j, ej⟩
                obtain ⟨w, hw_mem, hw_eq⟩ := Submodule.mem_map.mp (hy₁ ⟨j, ej⟩)
                have hmem := hW₁ ea w hw_mem
                rw [RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_to_distinguished hi ρ hj ea w] at hmem
                have hw_val : (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ j hj) w =
                    y₁ ⟨j, ej⟩ := hw_eq
                rw [hw_val] at hmem
                have hrev : RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex hj ea = ej :=
                  RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_apply_hom_eq_sigma_snd hi ⟨j, ej⟩
                exact hrev ▸ hmem

            have hmkQ_z₂_W₂ : mkQ z₂ ∈ W₂ v := by
              change mkQ (∑ a, lof a (y₂ a)) ∈ W₂ v
              rw [map_sum]
              exact Submodule.sum_mem _ fun ⟨j, ej⟩ _ => by
                have hj : j ≠ v := arrow_ne ⟨j, ej⟩
                let ea := RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_to_vertex hi ⟨j, ej⟩
                obtain ⟨w, hw_mem, hw_eq⟩ := Submodule.mem_map.mp (hy₂ ⟨j, ej⟩)
                have hmem := hW₂ ea w hw_mem
                rw [RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_to_distinguished hi ρ hj ea w] at hmem
                have hw_val : (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ j hj) w =
                    y₂ ⟨j, ej⟩ := hw_eq
                rw [hw_val] at hmem
                have hrev : RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex hj ea = ej :=
                  RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_apply_hom_eq_sigma_snd hi ⟨j, ej⟩
                exact hrev ▸ hmem

            have hmkQ_z₁_neg : mkQ z₁ = (-1 : k) • mkQ z₂ :=
              calc mkQ z₁ = mkQ z₁ + 0 := (add_zero _).symm
                _ = mkQ z₁ + ((1 : k) • mkQ z₂ + (-1 : k) • mkQ z₂) := by
                    rw [← add_smul, add_neg_cancel, zero_smul]
                _ = mkQ z₁ + mkQ z₂ + (-1 : k) • mkQ z₂ := by rw [← add_assoc, one_smul]
                _ = 0 + (-1 : k) • mkQ z₂ := by rw [hmkQ_sum]
                _ = (-1 : k) • mkQ z₂ := zero_add _

            have hmkQ_z₁_zero : mkQ z₁ = 0 := by
              have hmem : mkQ z₁ ∈ W₁ v ⊓ W₂ v :=
                ⟨hmkQ_z₁_W₁, hmkQ_z₁_neg ▸ Submodule.smul_mem _ _ hmkQ_z₂_W₂⟩
              rw [(hcompl v).1.eq_bot, Submodule.mem_bot] at hmem
              exact hmem

            have hz₁_range : z₁ ∈ LinearMap.range ψ := by
              have hmkQ_eq : mkQ z₁ = mkQ 0 := by rw [hmkQ_z₁_zero, map_zero]

              letI : ∀ w, AddCommGroup (ρ.obj w) := fun w => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
              letI : AddCommGroup DS := RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
              have hsub : Submodule.mkQ (LinearMap.range (ρ.outgoingDirectSumMap v)) z₁ =
                  Submodule.mkQ (LinearMap.range (ρ.outgoingDirectSumMap v)) 0 := by
                apply (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).symm.injective

                exact hmkQ_eq
              rw [map_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hsub
              exact hsub
            obtain ⟨x₁, hx₁⟩ := hz₁_range

            have hcomp₁ : ∀ a, ρ.map a.2 x₁ = y₁ a := by
              intro a

              have hψ_eq : ψ x₁ = ∑ b, lof b (ρ.map b.2 x₁) := by
                change (ρ.outgoingDirectSumMap v) x₁ = _
                unfold RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.outgoingDirectSumMap
                simp only [LinearMap.sum_apply, LinearMap.comp_apply,
                  DirectSum.lof_eq_of]
                rfl
              have hz₁_eq : z₁ = ∑ b, lof b (y₁ b) := rfl

              have h_eq_ds : ∑ c, lof c (ρ.map c.2 x₁) =
                  ∑ c, lof c (y₁ c) := hψ_eq ▸ hz₁_eq ▸ hx₁

              have h_eq : ∀ b, ρ.map b.2 x₁ = y₁ b := by
                intro b
                have h_apply := DFunLike.congr_fun h_eq_ds b

                change (∑ c, lof c (ρ.map c.2 x₁)) b = (∑ c, lof c (y₁ c)) b at h_apply
                rw [DFinsupp.finsetSum_apply, DFinsupp.finsetSum_apply] at h_apply

                simp_rw [show ∀ (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q v) (x : ρ.obj a.1),
                    (lof a x : DS) b = (DFinsupp.single a x : DS) b from
                    fun a x => by rfl] at h_apply
                simp only [DFinsupp.single_apply, Finset.sum_dite_eq',
                  Finset.mem_univ, ite_true] at h_apply
                exact h_apply
              exact h_eq a

            rw [show x = x₁ + (x - x₁) from by abel]
            refine Submodule.add_mem_sup ?_ ?_
            ·
              rw [Submodule.mem_iInf]
              intro a; rw [Submodule.mem_comap, hcomp₁ a]; exact hy₁ a
            ·
              rw [Submodule.mem_iInf]
              intro a; rw [Submodule.mem_comap, map_sub, hcomp₁ a, hsum a,
                add_sub_cancel_left]
              exact hy₂ a
        ·
          simp only [U₁, U₂, dif_neg hv]
          have hc := hcompl v
          exact ⟨by
            rw [Submodule.disjoint_def]
            intro x hx1 hx2
            obtain ⟨w₁, hw₁, rfl⟩ := Submodule.mem_map.mp hx1
            obtain ⟨w₂, hw₂, hw₂eq⟩ := Submodule.mem_map.mp hx2
            have heq := (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv).injective hw₂eq
            have : w₁ ∈ W₁ v ⊓ W₂ v := ⟨hw₁, heq ▸ hw₂⟩
            rw [hc.1.eq_bot] at this
            simp only [Submodule.mem_bot] at this
            rw [this, map_zero],
          by
            rw [codisjoint_iff, eq_top_iff]; intro x _
            obtain ⟨w, rfl⟩ := (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv).surjective x
            have hw : w ∈ (⊤ : Submodule k _) := Submodule.mem_top
            rw [← hc.2.eq_top, Submodule.mem_sup] at hw
            obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hw
            exact Submodule.mem_sup.mpr
              ⟨_, Submodule.mem_map.mpr ⟨w₁, hw₁, rfl⟩,
               _, Submodule.mem_map.mpr ⟨w₂, hw₂, rfl⟩,
               (map_add _ _ _).symm⟩⟩

      have hindecomp := hρ.2 U₁ U₂ hU₁_subrep hU₂_subrep hU_compl

      suffices transport :
          ∀ (W W' : ∀ v, Submodule k
            (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
              (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
              (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) v)),
            (∀ {a b} (e : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a b),
              ∀ x ∈ W' a,
              @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
                (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
                (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a b e x ∈ W' b) →
            (∀ v, IsCompl (W v) (W' v)) →
            (∀ v (hv : v ≠ i), Submodule.map
              (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv).toLinearMap
              (W v) = ⊥) →
            (∀ v, W v = ⊥) by
        rcases hindecomp with h1 | h2
        · left; exact transport W₁ W₂ hW₂ hcompl (fun v hv => by
            have := h1 v; simp only [U₁, dif_neg hv] at this; exact this)
        · right; exact transport W₂ W₁ hW₁ (fun v => (hcompl v).symm) (fun v hv => by
            have := h2 v; simp only [U₂, dif_neg hv] at this; exact this)

      intro W W' hW' hWW' hW_ne v
      by_cases hv : v = i
      ·

        cases hv

        have hW_bot : ∀ j, j ≠ i → W j = ⊥ := by
          intro j hj
          have h := hW_ne j hj
          rw [eq_bot_iff] at h ⊢
          intro z hz
          rw [Submodule.mem_bot]
          have hmem := h ⟨z, hz, rfl⟩
          rw [Submodule.mem_bot] at hmem
          exact (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ j hj).injective
            (hmem.trans (map_zero _).symm)

        have hW'_top : ∀ j, j ≠ i → W' j = ⊤ := by
          intro j hj
          have hbot := hW_bot j hj
          have hc := hWW' j
          rw [hbot] at hc
          exact eq_top_of_bot_isCompl hc

        have hW'_arrow : ∀ (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)
            (e_a : @Quiver.Hom Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) a.1 i)
            (w : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k Q _
              (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
              (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a.1),
            @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map k Q _
              (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
              (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) a.1 i e_a w ∈ W' i := by
          intro a e_a w
          exact hW' e_a w (by rw [hW'_top a.1 (arrow_ne a)]; exact Submodule.mem_top)

        have hW'_mkQ_lof : ∀ (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (z : ρ.obj a.1),
            (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ)
              ((DirectSum.lof k _ (fun b => ρ.obj b.1) a) z) ∈ W' i := by
          intro ⟨j, ej⟩ z
          have hj : j ≠ i := fun heq => (hi i).false (heq ▸ ej)
          let e_a := RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_hom_to_vertex hi ⟨j, ej⟩
          let w := (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ j hj).symm z

          have hmem := hW'_arrow ⟨j, ej⟩ e_a w

          rw [RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_to_distinguished hi ρ hj e_a w] at hmem

          simp only [w, LinearEquiv.apply_symm_apply] at hmem

          have hrev : RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex hj e_a = ej :=
            RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_apply_hom_eq_sigma_snd hi ⟨j, ej⟩

          exact hrev ▸ hmem

        have hW'i_top : W' i = ⊤ := by
          rw [eq_top_iff]; intro x _

          suffices h : ∀ z, (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ) z ∈ W' i by

            have hsurj : Function.Surjective (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ) := by

              letI : ∀ w, AddCommGroup (ρ.obj w) := fun w => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
              letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
                RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
              have heq : (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ) =
                  (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).symm.toLinearMap ∘ₗ
                    Submodule.mkQ (LinearMap.range (ρ.outgoingDirectSumMap i)) := rfl
              rw [heq]
              exact (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).symm.surjective.comp
                (Submodule.mkQ_surjective _)
            obtain ⟨z, rfl⟩ := hsurj x
            exact h z
          intro z

          rw [show z = ∑ a ∈ Finset.univ, (DirectSum.of (fun a => ρ.obj a.1) a) (z a) from
            (DirectSum.sum_univ_of z).symm]
          rw [map_sum]
          exact Submodule.sum_mem _ fun a _ => by

            change (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ)
              ((DirectSum.lof k _ (fun a => ρ.obj a.1) a) (z a)) ∈ W' i
            exact hW'_mkQ_lof a (z a)

        have hci := hWW' i
        rw [hW'i_top] at hci
        exact eq_bot_of_isCompl_top hci
      ·
        specialize hW_ne v hv
        rw [eq_bot_iff]
        intro x hx
        rw [eq_bot_iff] at hW_ne
        have hmem : (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv) x ∈
            Submodule.map
              (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv).toLinearMap
              (W v) :=
          ⟨x, hx, rfl⟩
        have h0 := hW_ne hmem
        rw [Submodule.mem_bot] at h0 ⊢
        exact (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv).injective
          (by rw [h0, map_zero])
