/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.GroupTheory.ConjugacyClassBounds

open MonoidAlgebra

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace RepresentationTheory.ConjugacyClassCardinalityBounds

variable {k G : Type*} [Field k] [Group G] [Fintype G]

/-- The quotient image of the referenced auxiliary monoid-algebra element is nonzero. -/
theorem mkQ_auxiliaryElement_ne_zero [DecidableEq G] :
    (Submodule.mkQ
      (RepresentationTheory.ConjugacyClassTrace.auxiliaryRelationSubmodule k G)
      (RepresentationTheory.SimpleRepresentationModules.groupElementSum k G) :
        RepresentationTheory.ConjugacyClassTrace.AuxiliaryClassQuotient k G) ≠ 0 := by
  intro h
  have hcc : RepresentationTheory.ConjugacyClassTrace.monoidAlgebraToClassFunctions k G
      (RepresentationTheory.SimpleRepresentationModules.groupElementSum k G) = 0 := by
    have hq : RepresentationTheory.ConjugacyClassTrace.auxiliaryToClassFunctions k G
        (Submodule.mkQ
          (RepresentationTheory.ConjugacyClassTrace.auxiliaryRelationSubmodule k G)
          (RepresentationTheory.SimpleRepresentationModules.groupElementSum k G)) = 0 := by
      rw [h, map_zero]
    rwa [RepresentationTheory.ConjugacyClassTrace.auxiliaryToClassFunctions,
      Submodule.mkQ_apply, Submodule.liftQ_apply] at hq
  have hval : RepresentationTheory.ConjugacyClassTrace.monoidAlgebraToClassFunctions k G
      (RepresentationTheory.SimpleRepresentationModules.groupElementSum k G)
      (ConjClasses.mk 1) = 1 := by
    simp only [RepresentationTheory.ConjugacyClassTrace.monoidAlgebraToClassFunctions,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single (1 : G)]
    · rw [if_pos rfl,
        RepresentationTheory.SimpleRepresentationModules.groupElementSum_coeff]
    · intro b _ hb
      rw [if_neg]
      intro hmk
      exact hb (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hmk))
    · intro hb; exact absurd (Finset.mem_univ 1) hb
  rw [hcc, Pi.zero_apply] at hval
  exact zero_ne_one hval

section SimpleModule

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M] [Module.Finite k M]
  [IsSimpleModule (MonoidAlgebra k G) M]

private noncomputable def groupSumEnd : M →ₗ[MonoidAlgebra k G] M where
  toFun m := RepresentationTheory.SimpleRepresentationModules.groupElementSum k G • m
  map_add' a b := smul_add _ _ _
  map_smul' y m := by
    change RepresentationTheory.SimpleRepresentationModules.groupElementSum k G • (y • m) =
      y • (RepresentationTheory.SimpleRepresentationModules.groupElementSum k G • m)
    rw [smul_smul, smul_smul, Subalgebra.mem_center_iff.mp
      RepresentationTheory.SimpleRepresentationModules.groupElementSum_mem_center y]

omit [Module.Finite k M] in
/-- For a simple module, the referenced map sends the referenced auxiliary element to zero when
the group cardinality is zero in the field. -/
theorem auxiliaryMap_auxiliaryElement_eq_zero_of_card_eq_zero
    (hcard : (Fintype.card G : k) = 0) :
    RepresentationTheory.ConjugacyClassTrace.moduleTrace k M
      (RepresentationTheory.SimpleRepresentationModules.groupElementSum k G) = 0 := by
  have hee : ∀ m : M,
      RepresentationTheory.SimpleRepresentationModules.groupElementSum k G •
        (RepresentationTheory.SimpleRepresentationModules.groupElementSum k G • m) = 0 :=
    fun m => by
    rw [smul_smul, RepresentationTheory.SimpleRepresentationModules.groupElementSum_sq hcard,
      zero_smul]
  have hzero : ∀ m : M,
      RepresentationTheory.SimpleRepresentationModules.groupElementSum k G • m = 0 := by
    let e := groupSumEnd (k := k) (G := G) M
    rcases eq_bot_or_eq_top (LinearMap.ker e) with hk | hk
    · have hinj : Function.Injective e := LinearMap.ker_eq_bot.mp hk
      intro m
      have hm : e (e m) = e 0 := by rw [map_zero]; exact hee m
      exact hinj hm
    · intro m
      exact LinearMap.mem_ker.mp (hk ▸ Submodule.mem_top)
  have hend : RepresentationTheory.ConjugacyClassTrace.monoidAlgebraActionHom k M
      (RepresentationTheory.SimpleRepresentationModules.groupElementSum k G) = 0 := by
    ext m
    rw [RepresentationTheory.ConjugacyClassTrace.monoidAlgebraActionHom_apply,
      LinearMap.zero_apply]
    exact hzero m
  rw [RepresentationTheory.ConjugacyClassTrace.moduleTrace_eq_trace_action, hend, map_zero]

end SimpleModule

/-- A finite linearly independent family of linear functionals has cardinality below the ambient
dimension if all functionals vanish on a common nonzero vector. -/
theorem card_lt_finrank_of_linearIndependent_of_common_nonzero_kernel
    {V ι : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] [Fintype ι]
    {f : ι → (V →ₗ[k] k)} (hf : LinearIndependent k f) {v : V} (hv : v ≠ 0)
    (h0 : ∀ i, f i v = 0) :
    Fintype.card ι < Module.finrank k V := by
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero k hv
  set F : Option ι → (V →ₗ[k] k) := fun o => o.elim g f with hF
  have hFind : LinearIndependent k F := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hcv : ∑ o : Option ι, c o * (F o) v = 0 := by
      have h2 : (∑ o : Option ι, c o • F o) v = 0 := by rw [hc, LinearMap.zero_apply]
      simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        using h2
    rw [Fintype.sum_option] at hcv
    simp only [hF, Option.elim_none, Option.elim_some, h0, mul_zero, Finset.sum_const_zero,
      add_zero] at hcv
    have hnone : c none = 0 := by
      rcases mul_eq_zero.mp hcv with h | h
      · exact h
      · exact absurd h hg
    have hsome : ∀ i, c (some i) = 0 := by
      have hsum : ∑ i, c (some i) • f i = 0 := by
        have h3 := hc
        rw [Fintype.sum_option] at h3
        simpa only [hF, Option.elim_none, Option.elim_some, hnone, zero_smul, zero_add]
          using h3
      exact fun i => Fintype.linearIndependent_iff.mp hf (fun i => c (some i)) hsum i
    rintro (_ | i)
    · exact hnone
    · exact hsome i
  have hcard : Fintype.card (Option ι) ≤ Module.finrank k (V →ₗ[k] k) :=
    hFind.fintype_card_le_finrank
  rw [Module.finrank_linearMap_self, Fintype.card_option] at hcard
  omega

/-- A finite linearly independent displayed family has cardinality strictly below the number of
conjugacy classes when the group cardinality vanishes in the field. -/
theorem card_lt_card_conjClasses_of_linearIndependent_of_card_eq_zero [DecidableEq G]
    {ι : Type*} [Fintype ι]
    {S : ι → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module (MonoidAlgebra k G) (S i)] [∀ i, IsScalarTower k (MonoidAlgebra k G) (S i)]
    [∀ i, Module.Finite k (S i)] [∀ i, IsSimpleModule (MonoidAlgebra k G) (S i)]
    (hcard : (Fintype.card G : k) = 0)
    (h : LinearIndependent k (fun i =>
      (RepresentationTheory.ConjugacyClassTrace.auxiliaryModuleTrace k (S i) :
        RepresentationTheory.ConjugacyClassTrace.AuxiliaryClassQuotient k G →ₗ[k] k))) :
    Fintype.card ι < Nat.card (ConjClasses G) := by
  have h0 : ∀ i, (RepresentationTheory.ConjugacyClassTrace.auxiliaryModuleTrace k (S i))
      (Submodule.mkQ
        (RepresentationTheory.ConjugacyClassTrace.auxiliaryRelationSubmodule k G)
        (RepresentationTheory.SimpleRepresentationModules.groupElementSum k G)) = 0 :=
    fun i => by
      rw [RepresentationTheory.ConjugacyClassTrace.auxiliaryModuleTrace_mkQ];
      exact auxiliaryMap_auxiliaryElement_eq_zero_of_card_eq_zero (S i) hcard
  have hlt := card_lt_finrank_of_linearIndependent_of_common_nonzero_kernel h
    (mkQ_auxiliaryElement_ne_zero (k := k) (G := G)) h0
  rwa [RepresentationTheory.ConjugacyClassTrace.finrank_auxiliaryClassQuotient] at hlt

end RepresentationTheory.ConjugacyClassCardinalityBounds
