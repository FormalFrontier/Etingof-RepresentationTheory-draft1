/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.LinearAlgebra.Auxiliary
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false










section Helpers

set_option maxHeartbeats 800000 in


private theorem RepresentationTheory.Surjective.reflFunctorPlus_finiteDim_i
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i)] :
    @Module.Finite k
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i)
        (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ inst i hi ρ) i)
      (inferInstanceAs (Semiring k))
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.addCommMonoid k Q _
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i)
        (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ inst i hi ρ) i)
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.moduleInstance k Q _
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i)
        (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ inst i hi ρ) i) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  haveI : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q inst i) :=
    Fintype.ofEquiv _ (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryEquiv Q _ inst i hi)
  exact Module.Finite.equiv
    (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt k _ Q _ inst i hi ρ).symm

set_option maxHeartbeats 800000 in


private theorem RepresentationTheory.Surjective.reflFunctorPlus_finiteDim_ne
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i)]
    (a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i) :
    @Module.Finite k
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i)
        (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ inst i hi ρ) a.fst)
      (inferInstanceAs (Semiring k))
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.addCommMonoid k Q _
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i)
        (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ inst i hi ρ) a.fst)
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.moduleInstance k Q _
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i)
        (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ inst i hi ρ) a.fst) :=
  Module.Finite.equiv
    (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _ inst i hi ρ a.fst
      (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne Q _ inst i hi a)).symm

set_option maxHeartbeats 800000 in






private noncomputable def RepresentationTheory.Surjective.equivAt_eq_sink
    {k : Type*} [Field k] {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i)]
    (hsurj : Function.Surjective (ρ.auxiliaryDirectSumMap i)) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i)
      (@RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ Q _
        (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i
        (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryForward Q _ inst i hi)
        (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ inst i hi ρ) _) i ≃ₗ[k]
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ i := by

  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)





  classical


    let instR := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i
    let ρ' := @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ inst i hi ρ

    let Φ_component : ∀ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i,
        @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst →ₗ[k]
        @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ i :=
      fun a => (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ inst ρ a.fst i
        (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom Q _ inst i hi a)).comp
        (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _ inst i hi ρ a.fst
          (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne Q _ inst i hi a)).toLinearMap
    let Φ := DirectSum.toModule k _ _ Φ_component

    letI acg_comp : ∀ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i,
        AddCommGroup (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst) :=
      fun a => @RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing k _ _ (ρ'.addCommMonoid a.fst) (ρ'.moduleInstance a.fst)
    letI acg_ds : AddCommGroup (DirectSum (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i)
        (fun a => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst)) :=
      @RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing k _ _ _ _



    let reindex : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i → @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q inst i :=
      fun a => ⟨a.fst, @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom Q _ inst i hi a⟩



    have hΦsurj : Function.Surjective Φ :=
      @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.LinearMap.surjective_of_auxiliaryPreimages k _ Q _ inst i hi ρ _ hsurj
        (fun a => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst)
        (fun a => ρ'.addCommMonoid a.fst) (fun a => ρ'.moduleInstance a.fst) Φ
        (fun b v => by


          let a := @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMap Q _ inst i hi b
          let hne := @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne Q _ inst i hi a
          let v' := (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _ inst i hi ρ a.fst hne).symm v
          refine ⟨DirectSum.lof k _ _ a v', ?_⟩
          simp only [Φ, Φ_component, DirectSum.toModule_lof, LinearMap.comp_apply,
            LinearEquiv.coe_toLinearMap, v']


          have heq_proof : @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne Q _ inst i hi a =
              @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne Q _ inst i hi
                (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMap Q _ inst i hi b) := rfl
          conv_lhs =>
            rw [show ∀ h, (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _ inst i hi ρ a.fst h)
                ((@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _ inst i hi ρ a.fst hne).symm v) = v
              from fun h => by exact LinearEquiv.apply_symm_apply _ v]
          exact congrArg (fun e => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ inst ρ _ i e v)
            (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom_auxiliaryMap Q _ inst i hi b))


    let ψ := ∑ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i,
        (DirectSum.lof k (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i)
          (fun a => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst) a).comp
          (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ instR ρ' i a.fst a.snd)
    have hker : ψ.range = LinearMap.ker Φ := by
      apply le_antisymm
      ·
        rw [LinearMap.range_le_ker_iff]
        ext w
        simp only [LinearMap.comp_apply, LinearMap.zero_apply]

        simp only [ψ, LinearMap.sum_apply, LinearMap.comp_apply]

        simp only [Φ, map_sum, DirectSum.toModule_lof]

        exact @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliarySum_eq_zero k _ Q _ inst i hi ρ _ w
      ·
        have hfwd : ψ.range ≤ LinearMap.ker Φ := by
          rw [LinearMap.range_le_ker_iff]; ext w
          simp only [LinearMap.comp_apply, LinearMap.zero_apply]
          simp only [ψ, LinearMap.sum_apply, LinearMap.comp_apply]
          simp only [Φ, map_sum, DirectSum.toModule_lof]
          exact @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliarySum_eq_zero k _ Q _ inst i hi ρ _ w

        letI acg_rho'_i : AddCommGroup
            (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' i) :=
          @RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing k _ _
            (ρ'.addCommMonoid i) (ρ'.moduleInstance i)
        haveI fd_i :
            @Module.Finite k
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' i)
              (inferInstanceAs (Semiring k))
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.addCommMonoid k Q _
                instR ρ' i)
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.moduleInstance k Q _
                instR ρ' i) :=
          @RepresentationTheory.Surjective.reflFunctorPlus_finiteDim_i k _ Q _ inst i hi ρ _ _ _
        haveI fd_ne : ∀ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i,
            @Module.Finite k
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst)
              (inferInstanceAs (Semiring k))
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.addCommMonoid k Q _
                instR ρ' a.fst)
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.moduleInstance k Q _
                instR ρ' a.fst) :=
          fun a => @RepresentationTheory.Surjective.reflFunctorPlus_finiteDim_ne k _ Q _ inst i hi ρ _ _ _ a
        haveI : FiniteDimensional k (DirectSum (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i)
            (fun a => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst)) :=
          @Module.Finite.instDirectSum k (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i) _
            inferInstance
            (fun a => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst)
            (fun a => (acg_comp a).toAddCommMonoid)
            (fun a => ρ'.moduleInstance a.fst)
            (fun a => fd_ne a)











        have hψ_inj : Function.Injective ψ := by
          intro w₁ w₂ heq
          rw [← sub_eq_zero]; set w := w₁ - w₂
          have hψ_zero : ψ w = 0 := by rw [map_sub, sub_eq_zero.mpr heq]

          have hcomp : ∀ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i,
              @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ instR ρ' i a.fst a.snd w = 0 := by
            intro a

            have h₀ : (ψ w) a = 0 := by
              have := congr_arg (· a) hψ_zero
              simp only [DirectSum.zero_apply] at this
              exact this

            suffices hψa : (ψ w) a =
                @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ instR ρ' i a.fst a.snd w by
              rw [← hψa]; exact h₀


            have hψ_rfl : ψ = ∑ b : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i,
                (DirectSum.lof k (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i)
                  (fun a => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst) b).comp
                  (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k Q _ instR ρ' i b.fst b.snd) := rfl
            rw [hψ_rfl, LinearMap.sum_apply]
            simp only [LinearMap.comp_apply]
            rw [DFinsupp.finsetSum_apply,
              Finset.sum_eq_single a
                (fun b _ hb => DFinsupp.single_eq_of_ne (Ne.symm hb))
                (fun h => absurd (Finset.mem_univ a) h)]
            exact DFinsupp.single_eq_same

          haveI : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q inst i) :=
            Fintype.ofEquiv _ (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryEquiv Q _ inst i hi)

          set ew := (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt k _ Q _ inst i hi ρ) w
          have hval_zero : (ew : DirectSum (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q inst i)
              (fun a => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ a.fst)) = 0 := by
            apply DFinsupp.ext; intro b
            let a := (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryEquiv Q _ inst i hi).symm b
            have hne := @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne Q _ inst i hi a
            have hapi := @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliary_arrow_map_from_selected k _ Q _ inst i hi ρ
              a.fst hne a.snd w
            rw [hcomp a, map_zero] at hapi
            have hb_eq : (⟨a.fst, @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryReverseHom Q _ inst i a.fst hne a.snd⟩ :
                @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q inst i) = b :=
              Equiv.apply_symm_apply (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryEquiv Q _ inst i hi) b
            simp only [DirectSum.zero_apply]
            exact hb_eq ▸ hapi.symm
          have heq_zero : ew = 0 := Subtype.val_injective hval_zero
          exact (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt k _ Q _ inst i hi ρ).injective
            (by change ew = _; rw [heq_zero, map_zero])



        haveI : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q inst i) :=
          Fintype.ofEquiv _ (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryEquiv Q _ inst i hi)

        haveI : ∀ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i,
            Module.Free k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst) :=
          fun a => Module.Free.of_equiv
            (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _ inst i hi ρ a.fst
              (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne Q _ inst i hi a)).symm
        haveI : Module.Free k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' i) := by


          haveI : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q inst i) :=
            Fintype.ofEquiv _ (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryEquiv Q _ inst i hi)
          exact inferInstance
        have hdim : Module.finrank k
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' i) +
            Module.finrank k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ i) =
            Module.finrank k (DirectSum (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i)
              (fun a => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst)) := by

          set d1 := Module.finrank k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' i)
          set d2 := Module.finrank k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ i)
          set d3 := Module.finrank k (DirectSum (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i)
            (fun a => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst))

          have heq3a : d3 = ∑ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i,
              Module.finrank k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst) :=
            Module.finrank_directSum (R := k) _

          have heq3b : ∀ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i,
              Module.finrank k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ instR ρ' a.fst) =
              Module.finrank k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ a.fst) :=
            fun a => LinearEquiv.finrank_eq
              (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _ inst i hi ρ a.fst
                (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryFst_ne Q _ inst i hi a))

          have heq3 : d3 = ∑ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i,
              Module.finrank k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ a.fst) := by
            rw [heq3a]; exact Finset.sum_congr rfl (fun a _ => heq3b a)

          letI : Quiver Q := inst

          have heq1 : d1 = Module.finrank k ↥(LinearMap.ker (ρ.auxiliaryDirectSumMap i)) :=
            LinearEquiv.finrank_eq (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivAt k _ Q _ inst i hi ρ)

          have h_rn := (ρ.auxiliaryDirectSumMap i).finrank_range_add_finrank_ker
          have h_surj : Module.finrank k ↥(ρ.auxiliaryDirectSumMap i).range = d2 := by
            rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
          have h_ds := Module.finrank_directSum (R := k)
            (fun a : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q inst i => ρ.obj a.fst)


          have h_reindex : ∑ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q instR i,
              Module.finrank k (ρ.obj a.fst) =
              ∑ b : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q inst i, Module.finrank k (ρ.obj b.fst) :=
            (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryEquiv Q _ inst i hi).bijective.sum_comp
              (fun b => Module.finrank k (ρ.obj b.fst))
          linarith [heq1, heq3, h_rn, h_surj, h_ds, h_reindex]
        exact (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.LinearMap.auxiliaryRangeEqKer hfwd hΦsurj hψ_inj hdim).ge



    exact (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient k _ Q _
      (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i) i
      (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryForward Q _ inst i hi)
      (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ inst i hi ρ) _).trans
      ((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective Φ hΦsurj))






private theorem RepresentationTheory.Surjective.reflFunctorMinus_equivAt_eq_mkQ'
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (d : DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ d) =
      Submodule.mkQ (LinearMap.range (ρ.outgoingDirectSumMap i)) d := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  unfold RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]











private theorem RepresentationTheory.Surjective.equivAt_eq_sink_charts_mkQ
    {k : Type*} [Field k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    {W : Type*} [AddCommGroup W] [Module k W]
    (Φ : (letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
          letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
            RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
          DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) →ₗ[k] W)
    (hΦ : Function.Surjective Φ)
    (hker : (letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
             letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
               RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
             LinearMap.range (ρ.outgoingDirectSumMap i)) = LinearMap.ker Φ)
    (d : DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
      RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
    ((RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).trans
        ((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective Φ hΦ)))
      (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedQuotientMap hi ρ d) = Φ d := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    RepresentationTheory.Surjective.reflFunctorMinus_equivAt_eq_mkQ' hi ρ d,
    Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end Helpers

set_option maxHeartbeats 12800000 in









/-- A surjective map has a nonempty codomain. -/
@[source_ref "Chapter6/Proposition6.6.6" (role := primary)]
theorem RepresentationTheory.Surjective.nonempty_of_surjective
    {k : Type*} [Field k]
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i)]
    (hsurj : Function.Surjective (ρ.auxiliaryDirectSumMap i)) :
    Nonempty (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData
      (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryAt
        (@RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ Q _
          (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i) i
          (RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryForward hi)
          (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation Q i hi ρ) _))
      ρ) := by


  let instR := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ inst i
  let instDR := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q _ instR i
  let ρ_plus := @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ Q _ inst i hi ρ
  let hi' := @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryForward Q _ inst i hi
  let ρ_dr := @RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ Q _ instR i hi' ρ_plus _
  exact RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.nonempty_auxiliaryData_ofLinearEquivAt
    (@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q _ inst i)
    (fun v => by
      by_cases hv : v = i
      ·
        cases hv
        exact @RepresentationTheory.Surjective.equivAt_eq_sink k _ Q _ inst i hi ρ _ _ _ hsurj
      ·
        exact (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ Q _
          instR i hi' ρ_plus _ v hv).trans
          (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ Q _ inst i hi ρ v hv))
    (fun {a b} e x => by

      by_cases ha : a = i
      ·
        subst ha; exact ((hi b).false e).elim
      · by_cases hb : b = i
        ·
          rw [eq_comm] at hb; subst hb

          simp only [dif_neg ha, LinearEquiv.trans_apply, dite_true]

          rw [@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_to_distinguished k _ Q inst_dec instR i hi'
            ρ_plus _ a ha]











          letI : AddCommGroup (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k Q _ inst ρ i) :=
            @RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing k _ _
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.addCommMonoid k Q _ inst ρ i)
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.moduleInstance k Q _ inst ρ i)
          unfold RepresentationTheory.Surjective.equivAt_eq_sink
          simp only []
          erw [@RepresentationTheory.Surjective.equivAt_eq_sink_charts_mkQ k _ Q inst_dec instR i hi' ρ_plus _ _ _ _ _ _ _]



          rw [DirectSum.toModule_lof]
          simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
          rw [@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryHom_mk_auxiliaryMapSecond Q inst_dec inst i hi a ha e]
        ·
          simp only [dif_neg ha, dif_neg hb, LinearEquiv.trans_apply]


          rw [@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedMap_of_ne k _ Q _
            instR i hi' ρ_plus _ a b ha hb
            ((@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq Q _ inst i).symm ▸ e) x]

          rw [@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliary_arrow_map_of_ne k _ Q _ inst i hi ρ a b ha hb]

          rw [@RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryMapAway_involutive Q _ inst i a b ha hb e])
