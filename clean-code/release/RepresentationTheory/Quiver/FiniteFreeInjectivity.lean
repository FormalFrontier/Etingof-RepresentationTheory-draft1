/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.LinearAlgebra.Auxiliary
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false










section Helpers





private theorem RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowsOutOf_ne_source
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) : a.fst ≠ i := by
  obtain ⟨j, e⟩ := a; dsimp; intro heq; subst heq; exact (hi j).false e


private def RepresentationTheory.Quiver.FiniteFreeInjectivity.ReversedAtVertexHom_at_second_def
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i j : Q} (hj : j ≠ i) :
    RepresentationTheory.QuiverVertexReversal.reversedAtHom Q i j i = (i ⟶ j) := by
  unfold RepresentationTheory.QuiverVertexReversal.reversedAtHom
  cases inst j i with
  | isTrue h => exact absurd h hj
  | isFalse _ => cases inst i i with
    | isFalse h => exact absurd rfl h
    | isTrue _ => rfl



private def RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i) :
    RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i ≃
    @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i where
  toFun a := ⟨a.fst, cast (RepresentationTheory.Quiver.FiniteFreeInjectivity.ReversedAtVertexHom_at_second_def
    (RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowsOutOf_ne_source hi a)).symm a.snd⟩
  invFun b := ⟨b.fst, cast (RepresentationTheory.Quiver.FiniteFreeInjectivity.ReversedAtVertexHom_at_second_def
    (RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne hi b)) b.snd⟩
  left_inv a := by
    obtain ⟨j, e⟩ := a; refine Sigma.ext rfl ?_
    exact heq_of_eq (by simp [cast_cast])
  right_inv b := by
    obtain ⟨j, e⟩ := b; refine Sigma.ext rfl ?_
    exact heq_of_eq (by simp [cast_cast])




private theorem RepresentationTheory.Quiver.FiniteFreeInjectivity.reversedArrow_ne_eq_arrowReindexEquivSource_roundtrip
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) :
    RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex
      (RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne hi (RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource hi a))
      (RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource hi a).snd = a.snd := by
  obtain ⟨j, e⟩ := a
  simp only [arrowReindexEquivSource, Equiv.coe_fn_mk]
  rw [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapTo_eq_cast]
  simp [cast_cast]



private theorem RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource_sigma_roundtrip
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) :
    (⟨(RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource hi a).fst,
      RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex
        (RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne hi (RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource hi a))
        (RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource hi a).snd⟩ : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) = a := by
  obtain ⟨j, e⟩ := a
  refine Sigma.ext rfl ?_
  exact heq_of_eq (RepresentationTheory.Quiver.FiniteFreeInjectivity.reversedArrow_ne_eq_arrowReindexEquivSource_roundtrip hi ⟨j, e⟩)



private theorem RepresentationTheory.Quiver.FiniteFreeInjectivity.sigma_out_eq_arrowReindexEquivSource_symm
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (b : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i) :
    (⟨b.fst, RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex
        (RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne hi b) b.snd⟩ : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) =
    (RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource hi).symm b := by
  obtain ⟨j, e⟩ := b
  simp only [arrowReindexEquivSource, Equiv.coe_fn_symm_mk]
  refine Sigma.ext rfl ?_
  exact heq_of_eq (by rw [RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapTo_eq_cast])



private theorem RepresentationTheory.Quiver.FiniteFreeInjectivity.sourceMap_sum_reindex
    {k : Type*} [CommRing k] {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    [Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i)]
    [DecidableEq (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (v : ρ.obj i) :
    (∑ x : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i,
      (DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.fst)
        ⟨x.fst, RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex
          (RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne hi x) x.snd⟩)
        (ρ.map (RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex
          (RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne hi x) x.snd) v)) =
    (∑ a : RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i,
      (DirectSum.lof k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.fst) a)
        (ρ.map a.snd v)) := by
  classical
  rw [← (RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource hi).symm.bijective.sum_comp]
  apply Finset.sum_congr rfl
  intro a _


  obtain ⟨j, e⟩ := a

  simp only [arrowReindexEquivSource, Equiv.coe_fn_symm_mk,
    RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapTo_eq_cast]

open Classical in
set_option maxHeartbeats 3200000 in


private theorem RepresentationTheory.Quiver.FiniteFreeInjectivity.reflFunctorMinus_mkQ_ker
    {k : Type*} [Field k] {Q : Type*} [inst_dec : DecidableEq Q]
    [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (y : DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1))
    (hy : @RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap k _ Q inst_dec inst i hi ρ _
      y = 0) :
    y ∈ LinearMap.range
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap k _ Q inst ρ i _) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) :=
    fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)
      (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)



  have hz : Submodule.mkQ (LinearMap.range
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap k _ Q inst ρ i _)) y = 0 := by
    apply (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient k _ Q inst_dec inst i hi ρ _).symm.injective
    rw [map_zero]
    have := hy
    unfold RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap at this
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    exact this
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  exact hz

open Classical in
set_option maxHeartbeats 3200000 in


private theorem RepresentationTheory.Quiver.FiniteFreeInjectivity.reflFunctorMinus_mkQ_surjective
    {k : Type*} [Field k] {Q : Type*} [inst_dec : DecidableEq Q]
    [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    Function.Surjective
      (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap k _ Q inst_dec inst i hi ρ _) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) :=
    fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)
      (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)


  intro z
  unfold RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap
  obtain ⟨w, hw⟩ := Submodule.mkQ_surjective
    (LinearMap.range (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap k _ Q inst ρ i _))
    ((@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient k _ Q inst_dec inst i hi ρ _) z)
  refine ⟨w, ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hw, LinearEquiv.symm_apply_apply]

set_option maxHeartbeats 12800000 in






private noncomputable def RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source
    {k : Type*} [Field k] {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (hinj : Function.Injective (ρ.outgoingDirectSumMap i)) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i)
      (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i
        (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward Q _ inst i hi)
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ Q _ inst i hi ρ _)) i ≃ₗ[k]
    ρ.obj i := by

  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)




  classical
  let instR := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i
  let ρ_minus := @RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ Q _ inst i hi ρ _

  haveI : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i) :=
    Fintype.ofEquiv _ (@RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource Q _ inst i hi)

  letI acg_comp : ∀ b : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i,
      AddCommGroup (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ_minus b.fst) :=
    fun b => @RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing k _ _ (ρ_minus.addCommMonoid b.fst) (ρ_minus.moduleInstance b.fst)
  letI acg_ds : AddCommGroup (DirectSum (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i)
      (fun b => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ_minus b.fst)) :=
    @RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing k _ _ _ _



  let f_component : (b : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i) →
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ i →ₗ[k]
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ_minus b.fst :=
    fun b =>
      ((@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q _ inst i hi ρ _ b.fst
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b)).symm.toLinearMap).comp
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ inst ρ i b.fst
          (@RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q _ inst i b.fst
            (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b) b.snd))
  let f_ds : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ i →ₗ[k]
      DirectSum (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i)
        (fun b => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ_minus b.fst) :=
    ∑ b, (DirectSum.lof k _ _ b).comp (f_component b)







  have sinkMap_lof : ∀ (b : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i)
      (w : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ_minus b.fst),
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryDirectSumMap k _ Q instR ρ_minus i
        (DirectSum.lof k _ _ b w) =
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ instR ρ_minus b.fst i b.snd w := by
    intro b w
    delta RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryDirectSumMap
    erw [DirectSum.toModule_lof]
  have h_ker : ∀ v, @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryDirectSumMap k _ Q instR ρ_minus i (f_ds v) = 0 := by
    intro v
    simp only [f_ds, f_component]
    rw [LinearMap.sum_apply, map_sum]
    simp_rw [LinearMap.comp_apply]
    simp_rw [sinkMap_lof]

    change ∑ x : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q inst_dec inst i) i,
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q inst_dec inst i)
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ Q inst_dec inst i hi ρ _) x.fst i x.snd
        ((↑(@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q inst_dec inst i hi ρ _ x.fst
            (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q inst_dec inst i hi x)).symm ∘ₗ
          @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ inst ρ i x.fst
            (@RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q inst_dec inst i x.fst
              (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q inst_dec inst i hi x) x.snd)) v) = 0
    simp_rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]


    have h_mapL := fun (x : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i) (w : ρ_minus.obj x.fst) =>
      @RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_to_distinguished k _ Q inst_dec inst i hi ρ _ x.fst
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q inst_dec inst i hi x) x.snd w
    simp_rw [h_mapL, LinearEquiv.apply_symm_apply, ← map_sum]


    have h_sr := @RepresentationTheory.Quiver.FiniteFreeInjectivity.sourceMap_sum_reindex k _ Q inst_dec inst i hi ρ _ _ _ v
    rw [h_sr]
    exact @RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap_sum_eq_zero k _ Q inst_dec inst i hi ρ _ v

  let f : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ i →ₗ[k]
      ↥(LinearMap.ker (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryDirectSumMap k _ Q instR ρ_minus i)) :=
    LinearMap.codRestrict _ f_ds (fun v => LinearMap.mem_ker.mpr (h_ker v))



  have f_inj : Function.Injective f := by
    intro x y hxy
    apply hinj

    have h_eq : f_ds x = f_ds y := congr_arg Subtype.val hxy

    have h_comp : ∀ c : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i,
        f_component c x = f_component c y := by
      intro c
      have h_c := DFunLike.congr_fun h_eq c
      suffices key : ∀ v, (f_ds v : Π₀ _, _) c = f_component c v from
        (key x).symm.trans (h_c.trans (key y))
      intro v
      simp only [f_ds, LinearMap.sum_apply, LinearMap.comp_apply]
      rw [DFinsupp.finsetSum_apply,
        Finset.sum_eq_single c
          (fun b _ hbc => by erw [DFinsupp.single_eq_of_ne (Ne.symm hbc)])
          (fun h => absurd (Finset.mem_univ c) h)]
      erw [DFinsupp.single_eq_same]

    have h_map : ∀ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q inst i,
        @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ inst ρ i a.fst a.snd x =
        @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ inst ρ i a.fst a.snd y := by
      intro a
      let b := @RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource Q inst_dec inst i hi a
      have h_b := h_comp b
      simp only [f_component] at h_b
      have h_ml := (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q _ inst i hi ρ _ b.fst
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b)).symm.injective h_b


      have h_rt := @RepresentationTheory.Quiver.FiniteFreeInjectivity.reversedArrow_ne_eq_arrowReindexEquivSource_roundtrip
        Q inst_dec inst i hi a
      rw [h_rt] at h_ml
      exact h_ml

    change @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap k _ Q inst ρ i _ x =
         @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap k _ Q inst ρ i _ y
    delta RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    exact Finset.sum_congr rfl (fun a _ => congrArg _ (h_map a))



  have f_surj : Function.Surjective f := by
    letI : Quiver Q := instR

    letI : ∀ v, Module k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ v) :=
      fun v => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.moduleInstance k Q _ inst ρ v

    letI dec_out : DecidableEq (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q inst i) := Classical.decEq _

    let Phi : DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i)
          (fun b => ρ_minus.obj b.fst) →ₗ[k]
        DirectSum (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q inst i)
          (fun a => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ a.fst) :=
      DirectSum.toModule k _ _ (fun b =>
        (DirectSum.lof k _ _
          (⟨b.fst, @RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q _ inst i b.fst
            (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b) b.snd⟩ :
            @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q inst i)).comp
        ((@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q _ inst i hi ρ _ b.fst
          (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b)).toLinearMap))

    let β_in : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q i → Type _ := fun c => ρ_minus.obj c.fst
    let β_out : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q inst i → Type _ :=
      fun a => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ a.fst

    have Phi_lof : ∀ (b : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i) (w : β_in b),
        Phi (DirectSum.lof k _ β_in b w) =
        (DirectSum.lof k _ β_out
          ⟨b.fst, @RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q _ inst i b.fst
            (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b) b.snd⟩)
        ((@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q _ inst i hi ρ _ b.fst
          (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b)) w) := by
      intro b w
      change (DirectSum.toModule _ _ _ _) (DirectSum.lof _ _ _ b w) = _
      erw [DirectSum.toModule_lof, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]

    have h_sinkMap_Phi : ∀ x,
        ρ_minus.auxiliaryDirectSumMap i x =
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap k _ Q _ inst i hi ρ _) (Phi x) := by
      intro x

      rw [show x = ∑ b ∈ Finset.univ,
        DirectSum.of _ b ((x : Π₀ _, _) b) from
        (DirectSum.sum_univ_of x).symm]
      simp only [map_sum]
      apply Finset.sum_congr rfl; intro b _

      change ρ_minus.auxiliaryDirectSumMap i (DirectSum.lof k _ _ b ((x : Π₀ _, _) b)) =
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap k _ Q _ inst i hi ρ _)
          (Phi (DirectSum.lof k _ _ b ((x : Π₀ _, _) b)))
      rw [sinkMap_lof, Phi_lof]
      exact @RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_to_distinguished k _ Q _ inst i hi ρ _
        b.fst (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b) b.snd
        ((x : Π₀ _, _) b)

    have h_Phi_f_ds : ∀ v, Phi (f_ds v) =
        @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap k _ Q inst ρ i _ v := by
      intro v

      have h_f_ds_def : ∀ w, f_ds w = ∑ b,
          (DirectSum.lof k _ _ b) (f_component b w) := by
        intro w; simp [f_ds, LinearMap.sum_apply, LinearMap.comp_apply]
      rw [h_f_ds_def, map_sum]

      conv_lhs =>
        arg 2; ext b
        rw [show DirectSum.lof k _ (fun b => ρ_minus.obj b.fst) b =
              DirectSum.lof k _ β_in b from rfl, Phi_lof]

      have h_cancel : ∀ (b : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i),
          (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q _ inst i hi ρ _ b.fst
            (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b)) ((f_component b) v) =
          @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ inst ρ i b.fst
            (@RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q _ inst i b.fst
              (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b) b.snd) v := by
        intro b; simp only [f_component]
        erw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
        exact LinearEquiv.apply_symm_apply _ _
      simp_rw [h_cancel]

      change _ = (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap k _ Q inst ρ i _) v
      delta RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      exact @RepresentationTheory.Quiver.FiniteFreeInjectivity.sourceMap_sum_reindex k _ Q inst_dec inst i hi ρ _ _ _ v


    have Phi_of_ne : ∀ (c d : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i)
        (w : ρ_minus.obj d.fst),
        c ≠ d →
        (Phi (DirectSum.of (fun d => ρ_minus.obj d.fst) d w) : Π₀ _, _)
          ⟨c.fst, @RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q _ inst i c.fst
            (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi c) c.snd⟩ = 0 := by
      intro c d w hcd
      change (Phi (DirectSum.lof k _ β_in d w) : Π₀ _, _) _ = _
      rw [Phi_lof]; erw [DFinsupp.single_eq_of_ne]
      intro h_eq
      exact hcd ((@RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource Q inst_dec inst i hi).symm.injective
        (by rw [← @RepresentationTheory.Quiver.FiniteFreeInjectivity.sigma_out_eq_arrowReindexEquivSource_symm Q _ inst i hi d,
                ← @RepresentationTheory.Quiver.FiniteFreeInjectivity.sigma_out_eq_arrowReindexEquivSource_symm Q _ inst i hi c, h_eq])).symm
    have Phi_of_eq : ∀ (c : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i)
        (w : ρ_minus.obj c.fst),
        (Phi (DirectSum.of (fun d => ρ_minus.obj d.fst) c w) : Π₀ _, _)
          ⟨c.fst, @RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q _ inst i c.fst
            (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi c) c.snd⟩ =
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q _ inst i hi ρ _ c.fst
          (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi c)) w := by
      intro c w
      change (Phi (DirectSum.lof k _ β_in c w) : Π₀ _, _) _ = _
      rw [Phi_lof]; erw [DFinsupp.single_eq_same]
    have Phi_inj : Function.Injective Phi := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      have hPhi := LinearMap.mem_ker.mp hx
      ext c

      have h_decomp : (Phi x : Π₀ _, _)
          ⟨c.fst, @RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q _ inst i c.fst
            (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi c) c.snd⟩ =
          (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q _ inst i hi ρ _ c.fst
            (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi c)) ((x : Π₀ _, _) c) := by
        conv_lhs => rw [(DirectSum.sum_univ_of x).symm]
        rw [map_sum, DFinsupp.finsetSum_apply]
        rw [Finset.sum_eq_single c
          (fun d _ hdc => Phi_of_ne c d _ (Ne.symm hdc))
          (fun h => absurd (Finset.mem_univ c) h)]
        exact Phi_of_eq c _
      rw [hPhi, DFinsupp.coe_zero, Pi.zero_apply] at h_decomp
      exact (LinearEquiv.map_eq_zero_iff _).mp h_decomp.symm

    intro ⟨x, hx_mem⟩
    have hx : ρ_minus.auxiliaryDirectSumMap i x = 0 := LinearMap.mem_ker.mp hx_mem
    have h_Phi_x_mkQ :
        @RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap k _ Q _ inst i hi ρ _ (Phi x) = 0 := by
      rw [← h_sinkMap_Phi]; exact hx
    obtain ⟨v, hv⟩ := @RepresentationTheory.Quiver.FiniteFreeInjectivity.reflFunctorMinus_mkQ_ker k _ Q _ inst i hi ρ _
      (Phi x) h_Phi_x_mkQ
    have h_eq : f_ds v = x := Phi_inj (by rw [h_Phi_f_ds]; exact hv)
    exact ⟨v, Subtype.ext h_eq⟩



  let core : ↥(LinearMap.ker (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryDirectSumMap k _ Q instR ρ_minus i)) ≃ₗ[k]
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ i :=
    (LinearEquiv.ofBijective f ⟨f_inj, f_surj⟩).symm
  exact (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt k _ Q _ instR i
    (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward Q _ inst i hi) ρ_minus).trans core

set_option maxHeartbeats 6400000 in









private theorem RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source_symm_component
    {k : Type*} [Field k] {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (hinj : Function.Injective (ρ.outgoingDirectSumMap i))
    (y : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ i)
    (b : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i) :
    let instR := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i
    let ρ_minus := @RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ Q _ inst i hi ρ _
    let hi' := @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward Q _ inst i hi
    (DirectSum.component k (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i)
        (fun b => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ_minus b.fst) b)
      ((@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryDirectSumMap k _ Q instR ρ_minus i).ker.subtype
        ((@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt k _ Q _ instR i hi' ρ_minus)
          ((@RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source k _ Q inst_dec inst i hi ρ _ _ _ hinj).symm y))) =
    (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q _ inst i hi ρ _ b.fst
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b)).symm
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ inst ρ i b.fst
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.reverseArrowAtVertex Q _ inst i b.fst
          (@RepresentationTheory.QuiverRepresentationQuotientTransform.incomingArrow_source_ne Q _ inst i hi b) b.snd) y) := by
  intro instR ρ_minus hi'
  haveI : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i) :=
    Fintype.ofEquiv _ (@RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource Q _ inst i hi)
  haveI : DecidableEq (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i) := Classical.decEq _





  unfold RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply]
  erw [Submodule.coe_subtype, LinearMap.codRestrict_apply]
  rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single b]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    erw [DirectSum.component.lof_self]
  · intro c _ hcb
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    erw [DirectSum.component.of]
    exact dif_neg hcb
  · intro h
    exact absurd (@Finset.mem_univ _
      (Fintype.ofEquiv _ (@RepresentationTheory.Quiver.FiniteFreeInjectivity.arrowReindexEquivSource Q _ inst i hi)) b) h

set_option maxHeartbeats 6400000 in




private theorem RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source_naturality
    {k : Type*} [Field k] {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (hinj : Function.Injective (ρ.outgoingDirectSumMap i))
    (b : Q) (hb : ¬b = i)
    (e : @Quiver.Hom Q inst i b)
    (x : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i)
      (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i
        (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward Q _ inst i hi)
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ Q _ inst i hi ρ _)) i) :
    let instR := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i
    let ρ_minus := @RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ Q _ inst i hi ρ _
    let hi' := @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward Q _ inst i hi
    let arrow_R : @Quiver.Hom Q
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q inst_dec instR i) i b :=
      (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q _ inst i).symm ▸ e
    let b_idx : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i :=
      ⟨b, @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryReverseHom Q inst_dec instR i b hb arrow_R⟩
    (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q _ inst i hi ρ _ b hb)
      ((DirectSum.component k (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q instR i)
          (fun c => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ_minus c.fst)
          b_idx)
        ((ρ_minus.auxiliaryDirectSumMap i).ker.subtype
          ((@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt k _ Q _ instR i hi' ρ_minus) x))) =
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ inst ρ i b e)
      ((@RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source k _ Q inst_dec inst i hi ρ _ _ _ hinj) x) := by
  intro instR ρ_minus hi' arrow_R b_idx




  have hx : x = (@RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source k _ Q inst_dec inst i hi ρ _ _ _ hinj).symm
      ((@RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source k _ Q inst_dec inst i hi ρ _ _ _ hinj) x) :=
    ((@RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source k _ Q inst_dec inst i hi ρ _ _ _ hinj).symm_apply_apply x).symm

  have hcomp := @RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source_symm_component k _ Q inst_dec inst i hi ρ _ _ _ hinj
    ((@RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source k _ Q inst_dec inst i hi ρ _ _ _ hinj) x) b_idx
  simp only at hcomp
  conv_lhs => rw [show (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt k _ Q _ instR i hi' ρ_minus) x =
      (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt k _ Q _ instR i hi' ρ_minus)
        ((@RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source k _ Q inst_dec inst i hi ρ _ _ _ hinj).symm
          ((@RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source k _ Q inst_dec inst i hi ρ _ _ _ hinj) x))
    from by rw [← hx]]
  rw [hcomp]

  rw [LinearEquiv.apply_symm_apply]

  rw [@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapSecond_apply_auxiliaryMapFirst Q inst_dec inst i hi b hb e]

end Helpers









/-- An injective underlying function of the vertex-indexed map gives an inhabitant of the associated auxiliary construction. -/
@[source_ref "Chapter6/Proposition6.6.6" (role := primary)]
theorem RepresentationTheory.Quiver.FiniteFreeInjectivity.nonemptyAuxiliaryOfInjective
    {k : Type*} [Field k]
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (hinj : Function.Injective (ρ.outgoingDirectSumMap i)) :
    Nonempty (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData
      (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryAt
        (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _
          (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i
          (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward hi)
          (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ)))
      ρ) := by
  let instR := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i
  let instDR := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ instR i
  let ρ_minus := @RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ Q _ inst i hi ρ
  let hi' := @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward Q _ inst i hi
  let ρ_dr := @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ instR i hi' ρ_minus
  exact RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.nonempty_auxiliaryData_ofLinearEquivAt
    (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q _ inst i)
    (fun v => by
      by_cases hv : v = i
      · cases hv
        exact @RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source k _ Q _ inst i hi ρ _ _ _ hinj
      · exact (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _
          instR i hi' ρ_minus v hv).trans
          (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q _ inst i hi ρ _ v hv))
    (fun {a b} e x => by
      by_cases hb : b = i
      ·
        subst hb; exact ((hi a).false e).elim
      · by_cases ha : a = i
        ·
          rw [eq_comm] at ha; subst ha
          simp only [dif_neg hb, LinearEquiv.trans_apply, dite_true]

          rw [@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliary_arrow_map_from_selected k _ Q _ instR i hi' ρ_minus b hb
              ((@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q _ inst i).symm ▸ e) x]

          exact @RepresentationTheory.Quiver.FiniteFreeInjectivity.equivAt_eq_source_naturality k _ Q inst_dec inst i hi ρ
            _ _ _ hinj b hb e x
        ·
          simp only [dif_neg ha, dif_neg hb, LinearEquiv.trans_apply]
          rw [@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliary_arrow_map_of_ne k _ Q _
            instR i hi' ρ_minus a b ha hb
            ((@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q _ inst i).symm ▸ e) x]
          rw [@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_of_ne k _ Q _ inst i hi ρ _ a b ha hb]
          rw [@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapAway_involutive Q _ inst i a b ha hb e])
