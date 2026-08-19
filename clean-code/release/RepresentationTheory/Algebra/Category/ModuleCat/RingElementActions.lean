/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.FiniteLength
import RepresentationTheory.ModuleCat.Auxiliary
import RepresentationTheory.Algebra.Module.SimpleQuotient
import RepresentationTheory.RingTheory.ModuleLength
import RepresentationTheory.RingTheory.ElementProperty
import RepresentationTheory.Alignment.Attribute

/-! Actions of ring elements on module-category objects. -/

open CategoryTheory
open RepresentationTheory.ModuleCat.Auxiliary
open RepresentationTheory.Algebra.Module.SimpleQuotient
open RepresentationTheory.RingTheory.ModuleLength
open RepresentationTheory.RingTheory.ElementProperty

namespace RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions

universe v u

variable (R : Type u) [Ring R]

/-- A central idempotent acts either as zero or as the identity on a simple module. -/
theorem centralIdempotent_actsAsZero_or_identity {M : Type*} [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] {e : R} (he : IsIdempotentElem e) (hc : ∀ y : R, e * y = y * e) :
    (∀ m : M, e • m = 0) ∨ (∀ m : M, e • m = m) := by
  classical
  let φ : Module.End R M :=
    { toFun := fun m => e • m
      map_add' := fun m₁ m₂ => smul_add e m₁ m₂
      map_smul' := fun r m => by simp only [RingHom.id_apply, smul_smul, hc r] }
  have hφ : IsIdempotentElem φ := by
    ext m
    change e • e • m = e • m
    rw [smul_smul, he]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hφ with h | h
  · left
    intro m
    exact LinearMap.congr_fun h m
  · right
    intro m
    exact LinearMap.congr_fun h m

/-- An auxiliary type associated with a ring. -/
abbrev ringAuxiliaryType : Type u :=
  {e : R // IsIdempotentElem e ∧ ∀ y : R, e * y = y * e}

open scoped Classical in
/-- A Boolean value associated with a simple module and an element of the auxiliary ring-indexed type. -/
noncomputable def simpleModuleAuxiliaryBool {S : ModuleCat.{v} R} (_hS : IsSimpleModule R S)
    (e : ringAuxiliaryType R) : Bool :=
  decide (∀ m : (S : Type v), e.1 • m = m)

/-- The Boolean value is true exactly when the underlying scalar fixes every vector in the simple module. -/
theorem simpleModuleAuxiliaryBool_eq_true_iff_actsAsIdentity
    {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) (e : ringAuxiliaryType R) :
    simpleModuleAuxiliaryBool R hS e = true ↔ ∀ m : (S : Type v), e.1 • m = m := by
  classical
  unfold simpleModuleAuxiliaryBool
  rw [decide_eq_true_eq]

/-- The Boolean value is false exactly when the underlying scalar annihilates the simple module. -/
theorem simpleModuleAuxiliaryBool_eq_false_iff_actsAsZero
    {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) (e : ringAuxiliaryType R) :
    simpleModuleAuxiliaryBool R hS e = false ↔ ∀ m : (S : Type v), e.1 • m = 0 := by
  classical
  haveI := hS
  haveI : Nontrivial (S : Type v) := IsSimpleModule.nontrivial R (S : Type v)
  rw [← Bool.not_eq_true, simpleModuleAuxiliaryBool_eq_true_iff_actsAsIdentity]
  constructor
  · intro h
    rcases centralIdempotent_actsAsZero_or_identity R (M := (S : Type v)) (e := e.1) e.2.1 e.2.2 with h0 | h1
    · exact h0
    · exact absurd h1 h
  · intro h0 h1
    obtain ⟨x, hx⟩ := exists_ne (0 : (S : Type v))
    exact hx ((h1 x).symm.trans (h0 x))

open scoped ModuleCat.Algebra in
/-- The action of a central scalar commutes with composition of an extension class. -/
theorem centerScalar_ext_comp [Small.{v} R] (z : Subring.center R)
    {X Y : ModuleCat.{v} R} {n : ℕ} (α : Abelian.Ext X Y n) :
    (Abelian.Ext.mk₀ (z • 𝟙 X)).comp α (zero_add n) =
      α.comp (Abelian.Ext.mk₀ (z • 𝟙 Y)) (add_zero n) := by
  simp only [Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp, Abelian.Ext.comp_smul,
    Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id]

open scoped ModuleCat.Algebra in
/-- For simple modules, the identity-action property agrees under the displayed condition. -/
theorem auxiliaryElement_actsAsIdentity_iff_of_condition_of_simpleModules [Small.{v} R]
    (e : ringAuxiliaryType R) {X Y : ModuleCat.{v} R}
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y)
    (hne : auxiliaryModuleRelation' R X Y) :
    (∀ m : (X : Type v), e.1 • m = m) ↔ (∀ m : (Y : Type v), e.1 • m = m) := by
  classical
  haveI := hX
  haveI := hY
  haveI hntX : Nontrivial (X : Type v) := IsSimpleModule.nontrivial R (X : Type v)
  haveI hntY : Nontrivial (Y : Type v) := IsSimpleModule.nontrivial R (Y : Type v)
  haveI hneI : Nontrivial (Abelian.Ext X Y 1) := hne
  set z : Subring.center R :=
    ⟨e.1, Subring.mem_center_iff.mpr (fun g => (e.2.2 g).symm)⟩ with hz
  have hzsmul : ∀ {M : ModuleCat.{v} R} (m : (M : Type v)), z • m = e.1 • m := fun m => rfl
  have hid : ∀ {M : ModuleCat.{v} R}, (∀ m : (M : Type v), e.1 • m = m) → z • 𝟙 M = 𝟙 M := by
    intro M h
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [hzsmul m]
    exact h m
  have hzero : ∀ {M : ModuleCat.{v} R}, (∀ m : (M : Type v), e.1 • m = 0) → z • 𝟙 M = 0 := by
    intro M h
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [hzsmul m]
    exact h m
  have notId : ∀ {M : ModuleCat.{v} R} [Nontrivial (M : Type v)],
      (∀ m : (M : Type v), e.1 • m = 0) → ¬ (∀ m : (M : Type v), e.1 • m = m) := by
    intro M _ h0 h1
    obtain ⟨x, hx⟩ := exists_ne (0 : (M : Type v))
    exact hx ((h1 x).symm.trans (h0 x))
  have keyXY : (∀ m : (X : Type v), e.1 • m = m) → (∀ m : (Y : Type v), e.1 • m = 0) → False := by
    intro hXi hY0
    have hz0 : ∀ α : Abelian.Ext X Y 1, α = 0 := by
      intro α
      have hnat := centerScalar_ext_comp R z α
      rw [hid hXi, hzero hY0] at hnat
      simpa only [Abelian.Ext.mk₀_id_comp, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero] using hnat
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Abelian.Ext X Y 1)
    exact hab ((hz0 a).trans (hz0 b).symm)
  have keyYX : (∀ m : (X : Type v), e.1 • m = 0) → (∀ m : (Y : Type v), e.1 • m = m) → False := by
    intro hX0 hYi
    have hz0 : ∀ α : Abelian.Ext X Y 1, α = 0 := by
      intro α
      have hnat := centerScalar_ext_comp R z α
      rw [hzero hX0, hid hYi] at hnat
      simpa only [Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp, Abelian.Ext.comp_mk₀_id]
        using hnat.symm
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Abelian.Ext X Y 1)
    exact hab ((hz0 a).trans (hz0 b).symm)
  rcases centralIdempotent_actsAsZero_or_identity R (M := (X : Type v)) e.2.1 e.2.2 with hX0 | hXi
  · rcases centralIdempotent_actsAsZero_or_identity R (M := (Y : Type v)) e.2.1 e.2.2 with hY0 | hYi
    · exact iff_of_false (notId hX0) (notId hY0)
    · exact (keyYX hX0 hYi).elim
  · rcases centralIdempotent_actsAsZero_or_identity R (M := (Y : Type v)) e.2.1 e.2.2 with hY0 | hYi
    · exact (keyXY hXi hY0).elim
    · exact iff_of_true hXi hYi

/-- An isomorphism preserves whether the underlying scalar acts as the identity. -/
theorem auxiliaryElement_actsAsIdentity_iff_of_iso (e : ringAuxiliaryType R)
    {X Y : ModuleCat.{v} R} (iso : X ≅ Y) :
    (∀ m : (X : Type v), e.1 • m = m) ↔ (∀ m : (Y : Type v), e.1 • m = m) := by
  set φ := iso.toLinearEquiv with hφ
  refine ⟨fun hX n => ?_, fun hY m => ?_⟩
  · have h1 : φ (e.1 • φ.symm n) = e.1 • n := by rw [map_smul, φ.apply_symm_apply]
    rw [← h1, hX (φ.symm n), φ.apply_symm_apply]
  · have h1 : φ.symm (e.1 • φ m) = e.1 • m := by rw [map_smul, φ.symm_apply_apply]
    rw [← h1, hY (φ m), φ.symm_apply_apply]

/-- The identity-action property agrees across objects under an additional displayed condition. -/
theorem auxiliaryElement_actsAsIdentity_iff_of_auxiliaryCondition [Small.{v} R]
    (e : ringAuxiliaryType R) {X Y : ModuleCat.{v} R} (h : auxiliaryModuleRelation''' R X Y) :
    (∀ m : (X : Type v), e.1 • m = m) ↔ (∀ m : (Y : Type v), e.1 • m = m) := by
  obtain ⟨hX, hY, hor⟩ := h
  rcases hor with hadj | hiso
  · rcases hadj with h1 | h1
    · exact auxiliaryElement_actsAsIdentity_iff_of_condition_of_simpleModules R e hX hY h1
    · exact (auxiliaryElement_actsAsIdentity_iff_of_condition_of_simpleModules R e hY hX h1).symm
  · exact auxiliaryElement_actsAsIdentity_iff_of_iso R e hiso.some

/-- The identity-action property agrees across objects under the displayed condition. -/
theorem auxiliaryElement_actsAsIdentity_iff_of_condition [Small.{v} R]
    (e : ringAuxiliaryType R) {X Y : ModuleCat.{v} R} (h : auxiliaryModuleRelation R X Y) :
    (∀ m : (X : Type v), e.1 • m = m) ↔ (∀ m : (Y : Type v), e.1 • m = m) := by
  induction h with
  | rel X Y hxy =>
      exact auxiliaryElement_actsAsIdentity_iff_of_auxiliaryCondition R e hxy
  | refl X => exact Iff.rfl
  | symm X Y _ ih => exact ih.symm
  | trans X Y Z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The Boolean value is unchanged between simple modules under the displayed condition. -/
theorem simpleModuleAuxiliaryBool_eq_of_condition [Small.{v} R]
    {S T : ModuleCat.{v} R} (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    (e : ringAuxiliaryType R) (h : auxiliaryModuleRelation R S T) :
    simpleModuleAuxiliaryBool R hS e = simpleModuleAuxiliaryBool R hT e := by
  classical
  unfold simpleModuleAuxiliaryBool
  rw [decide_eq_decide]
  exact auxiliaryElement_actsAsIdentity_iff_of_condition R e h

/-- A finite family of central orthogonal idempotents has a unique member fixing a given simple module. -/
theorem existsUnique_index_actsAsIdentity {ι : Type*} [Fintype ι] (e : ι → R)
    (hsum : ∑ i, e i = 1) (hortho : ∀ i j, i ≠ j → e i * e j = 0)
    (hidem : ∀ i, IsIdempotentElem (e i)) (hcentral : ∀ i (y : R), e i * y = y * e i)
    {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    ∃! i, ∀ m : (S : Type v), e i • m = m := by
  classical
  haveI := hS
  haveI : Nontrivial (S : Type v) := IsSimpleModule.nontrivial R (S : Type v)
  have hdicho : ∀ i, (∀ m : (S : Type v), e i • m = 0) ∨ (∀ m : (S : Type v), e i • m = m) :=
    fun i => centralIdempotent_actsAsZero_or_identity R (hidem i) (hcentral i)
  obtain ⟨x, hx⟩ := exists_ne (0 : (S : Type v))
  have hxsum : ∑ i, (e i • x) = x := by rw [← Finset.sum_smul, hsum, one_smul]
  have hex : ∃ i, ∀ m : (S : Type v), e i • m = m := by
    by_contra hcon
    exact hx (by
      rw [← hxsum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      exact (hdicho i).resolve_right (fun h => hcon ⟨i, h⟩) x)
  obtain ⟨i₀, hi₀⟩ := hex
  refine ⟨i₀, hi₀, fun j hj => ?_⟩
  by_contra hne
  apply hx
  have h1 : (e j * e i₀) • x = x := by rw [mul_smul, hi₀ x, hj x]
  rw [hortho j i₀ hne, zero_smul] at h1
  exact h1.symm

/-- A scalar fixing one module fixes another module under the displayed condition. -/
theorem scalar_actsAsIdentity_of_condition {M S : ModuleCat.{v} R} {f : R}
    (hM : ∀ m : (M : Type v), f • m = m) (h : auxiliaryModuleRelationOverRing R M S) :
    ∀ s : (S : Type v), f • s = s := by
  rw [simple_target_iff] at h
  obtain ⟨_, Q, g, hg⟩ := h
  intro s
  obtain ⟨q, rfl⟩ := hg s
  rw [← map_smul]
  congr 1
  exact Subtype.ext (by rw [SetLike.val_smul]; exact hM q.val)

/-- A nonzero central idempotent fixes every element of some simple module. -/
theorem exists_simpleModule_scalarActsAsIdentity [Small.{v} R] {f : R} (hf0 : f ≠ 0)
    (hidem : IsIdempotentElem f) (hcentral : ∀ y : R, f * y = y * f) :
    ∃ S : ModuleCat.{v} R, IsSimpleModule R S ∧ ∀ m : (S : Type v), f • m = m := by
  classical
  set sh := Shrink.linearEquiv.{v} R R with hsh
  set w₀ : Shrink.{v} R := sh.symm f with hw₀
  have hfw : f • w₀ = w₀ := by
    have hmap : f • w₀ = sh.symm (f • f) := (map_smul sh.symm f f).symm
    rw [hmap, smul_eq_mul, hidem.eq]
  set P : Submodule R (Shrink.{v} R) :=
    LinearMap.range (LinearMap.toSpanSingleton R _ w₀) with hP
  have hfP : ∀ p ∈ P, f • p = p := by
    rintro p ⟨r, rfl⟩
    rw [LinearMap.toSpanSingleton_apply, ← mul_smul, hcentral r, mul_smul, hfw]
  have hw₀ne : w₀ ≠ 0 := by
    rw [hw₀, Ne, map_eq_zero_iff _ sh.symm.injective]
    exact hf0
  have hw₀P : w₀ ∈ P := ⟨1, by rw [LinearMap.toSpanSingleton_apply, one_smul]⟩
  haveI hntP : Nontrivial (P : Type v) :=
    ⟨⟨w₀, hw₀P⟩, 0, fun h => hw₀ne (congrArg Subtype.val h)⟩
  obtain ⟨S, hSfac⟩ := exists_target (M := ModuleCat.of R (P : Type v))
  refine ⟨S, hSfac.1,
    scalar_actsAsIdentity_of_condition R (M := ModuleCat.of R (P : Type v)) ?_ hSfac⟩
  intro m
  exact Subtype.ext (by rw [SetLike.val_smul]; exact hfP m.val m.property)

/-- Under the displayed hypotheses, identity scalar actions on two simple modules imply the stated condition. -/
theorem simpleModules_satisfyCondition_of_scalarActsAsIdentity [Small.{v} R] {f : R}
    (hfl : IsFiniteLength R R) (hindec : ElementProperty R f)
    {S T : ModuleCat.{v} R} (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    (hSf : ∀ m : (S : Type v), f • m = m) (hTf : ∀ m : (T : Type v), f • m = m) :
    auxiliaryModuleRelation R S T := by
  classical
  haveI := hS
  haveI := hT
  set sh := Shrink.linearEquiv.{v} R R with hsh
  have hflS : IsFiniteLength R (Shrink.{v} R) := sh.symm.isFiniteLength hfl
  obtain ⟨P₀, Q₀, hCompl, hgood, hbad⟩ :=
    exists_isCompl_with_relation_partition_of_finiteLength (R := R) (S := S) hflS
  have hmapfac : ∀ (T : Shrink.{v} R →ₗ[R] Shrink.{v} R) (N : Submodule R (Shrink.{v} R))
      (U : ModuleCat.{v} R), auxiliaryModuleRelationOverRing R (ModuleCat.of R (N.map T)) U →
      auxiliaryModuleRelationOverRing R (ModuleCat.of R N) U := by
    intro T N U h
    refine auxiliaryModuleRelationOverRing.of_surjective
      ((T.comp N.subtype).codRestrict (N.map T) (fun x => Submodule.mem_map_of_mem x.2)) ?_ h
    rintro ⟨y, hy⟩
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext (by simp [LinearMap.codRestrict])⟩
  have keyP : ∀ N : Submodule R (Shrink.{v} R),
      (∀ U : ModuleCat.{v} R, auxiliaryModuleRelationOverRing R (ModuleCat.of R N) U →
        auxiliaryModuleRelation R S U) → N ≤ P₀ := by
    intro N hN
    have hbot : N.map (Q₀.projection P₀ hCompl.symm) = ⊥ := by
      by_contra hne
      haveI : Nontrivial (N.map (Q₀.projection P₀ hCompl.symm) : Type v) :=
        Submodule.nontrivial_iff_ne_bot.mpr hne
      obtain ⟨U, hU⟩ := exists_target
        (M := ModuleCat.of R (N.map (Q₀.projection P₀ hCompl.symm) : Type v))
      have hUN : auxiliaryModuleRelationOverRing R (ModuleCat.of R N) U :=
        hmapfac (Q₀.projection P₀ hCompl.symm) N U hU
      have hle : N.map (Q₀.projection P₀ hCompl.symm) ≤ Q₀ := by
        have h1 : N.map (Q₀.projection P₀ hCompl.symm) ≤
            (⊤ : Submodule R (Shrink.{v} R)).map (Q₀.projection P₀ hCompl.symm) :=
          Submodule.map_mono le_top
        rwa [Submodule.map_top, Submodule.range_projection] at h1
      have hUQ : auxiliaryModuleRelationOverRing R (ModuleCat.of R Q₀) U :=
        auxiliaryModuleRelationOverRing.of_submodule
          (Submodule.comap Q₀.subtype (N.map (Q₀.projection P₀ hCompl.symm)))
          (auxiliaryModuleRelationOverRing.of_linearEquiv
            (Submodule.comapSubtypeEquivOfLe hle) hU)
      exact hbad U hUQ (hN U hUN)
    intro n hn
    have hmem : (Q₀.projection P₀ hCompl.symm) n ∈ N.map (Q₀.projection P₀ hCompl.symm) :=
      Submodule.mem_map_of_mem hn
    rw [hbot] at hmem
    exact (Submodule.projection_apply_eq_zero_iff hCompl.symm).mp ((Submodule.mem_bot R).mp hmem)
  have keyQ : ∀ N : Submodule R (Shrink.{v} R),
      (∀ V : ModuleCat.{v} R, auxiliaryModuleRelationOverRing R (ModuleCat.of R N) V →
        ¬ auxiliaryModuleRelation R S V) → N ≤ Q₀ := by
    intro N hN
    have hbot : N.map (P₀.projection Q₀ hCompl) = ⊥ := by
      by_contra hne
      haveI : Nontrivial (N.map (P₀.projection Q₀ hCompl) : Type v) :=
        Submodule.nontrivial_iff_ne_bot.mpr hne
      obtain ⟨V, hV⟩ := exists_target
        (M := ModuleCat.of R (N.map (P₀.projection Q₀ hCompl) : Type v))
      have hVN : auxiliaryModuleRelationOverRing R (ModuleCat.of R N) V :=
        hmapfac (P₀.projection Q₀ hCompl) N V hV
      have hle : N.map (P₀.projection Q₀ hCompl) ≤ P₀ := by
        have h1 : N.map (P₀.projection Q₀ hCompl) ≤
            (⊤ : Submodule R (Shrink.{v} R)).map (P₀.projection Q₀ hCompl) :=
          Submodule.map_mono le_top
        rwa [Submodule.map_top, Submodule.range_projection] at h1
      have hVP : auxiliaryModuleRelationOverRing R (ModuleCat.of R P₀) V :=
        auxiliaryModuleRelationOverRing.of_submodule
          (Submodule.comap P₀.subtype (N.map (P₀.projection Q₀ hCompl)))
          (auxiliaryModuleRelationOverRing.of_linearEquiv
            (Submodule.comapSubtypeEquivOfLe hle) hV)
      exact hN V hVN (hgood V hVP)
    intro n hn
    have hmem : (P₀.projection Q₀ hCompl) n ∈ N.map (P₀.projection Q₀ hCompl) :=
      Submodule.mem_map_of_mem hn
    rw [hbot] at hmem
    exact (Submodule.projection_apply_eq_zero_iff hCompl).mp ((Submodule.mem_bot R).mp hmem)
  set Ta : R → (Shrink.{v} R →ₗ[R] Shrink.{v} R) :=
    fun a => sh.symm.toLinearMap.comp ((LinearMap.mulRight R a).comp sh.toLinearMap) with hTa_def
  have hTa : ∀ (a : R) (w : Shrink.{v} R), Ta a w = sh.symm (sh w * a) := by
    intro a w
    simp only [hTa_def, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.mulRight_apply]
  have hstabP : ∀ (a : R) {z : Shrink.{v} R}, z ∈ P₀ → (Ta a) z ∈ P₀ := by
    intro a z hz
    exact keyP (P₀.map (Ta a)) (fun U hU => hgood U (hmapfac (Ta a) P₀ U hU))
      (Submodule.mem_map_of_mem hz)
  have hstabQ : ∀ (a : R) {z : Shrink.{v} R}, z ∈ Q₀ → (Ta a) z ∈ Q₀ := by
    intro a z hz
    exact keyQ (Q₀.map (Ta a)) (fun U hU => hbad U (hmapfac (Ta a) Q₀ U hU))
      (Submodule.mem_map_of_mem hz)
  have hcomm_endo : ∀ (a : R) (z : Shrink.{v} R),
      (P₀.projection Q₀ hCompl) ((Ta a) z) = (Ta a) ((P₀.projection Q₀ hCompl) z) := by
    intro a z
    have hzp : (P₀.projection Q₀ hCompl) z ∈ P₀ := Submodule.projection_apply_mem hCompl z
    have hzq : z - (P₀.projection Q₀ hCompl) z ∈ Q₀ := Submodule.sub_projection_mem hCompl z
    have hsplit : (Ta a) z = (Ta a) ((P₀.projection Q₀ hCompl) z)
        + (Ta a) (z - (P₀.projection Q₀ hCompl) z) := by
      rw [← map_add]
      congr 1
      abel
    rw [hsplit, map_add,
      (Submodule.projection_eq_self_iff hCompl _).mpr (hstabP a hzp),
      (Submodule.projection_apply_eq_zero_iff hCompl).mpr (hstabQ a hzq), add_zero]
  set c : R := sh (P₀.projection Q₀ hCompl (sh.symm 1)) with hc
  have hPiR : ∀ r : R, sh (P₀.projection Q₀ hCompl (sh.symm r)) = r * c := by
    intro r
    have hr : sh.symm r = r • sh.symm (1 : R) := by
      rw [← map_smul]
      congr 1
      rw [smul_eq_mul, mul_one]
    rw [hr, map_smul, map_smul, smul_eq_mul, ← hc]
  have hProjIdem : ∀ y, (P₀.projection Q₀ hCompl) ((P₀.projection Q₀ hCompl) y)
      = (P₀.projection Q₀ hCompl) y :=
    fun y => (Submodule.projection_eq_self_iff hCompl _).mpr
      (Submodule.projection_apply_mem hCompl y)
  have hidem_c : c * c = c := by
    have h := hPiR c
    rw [show sh.symm c = (P₀.projection Q₀ hCompl) (sh.symm 1) by
      rw [hc, sh.symm_apply_apply], hProjIdem, ← hc] at h
    exact h.symm
  have hcomm : ∀ x a : R, sh (P₀.projection Q₀ hCompl (sh.symm (x * a)))
      = sh (P₀.projection Q₀ hCompl (sh.symm x)) * a := by
    intro x a
    have h1 : sh.symm (x * a) = (Ta a) (sh.symm x) := by
      rw [hTa, sh.apply_symm_apply]
    rw [h1, hcomm_endo a (sh.symm x), hTa, sh.apply_symm_apply]
  have hcentral_c : ∀ a : R, a * c = c * a := by
    intro a
    have h := hcomm 1 a
    rw [one_mul, ← hc, hPiR a] at h
    exact h
  have hc_comm : ∀ y : R, c * y = y * c := fun y => (hcentral_c y).symm
  set c' : R := 1 - c with hc'
  have hidem_c' : c' * c' = c' := by
    rw [hc']
    have expand : (1 - c) * (1 - c) = 1 - c - c + c * c := by
      rw [sub_mul, one_mul, mul_sub, mul_one]
      abel
    rw [expand, hidem_c]
    abel
  have hcc' : c * c' = 0 := by
    rw [hc']
    have : c * (1 - c) = c - c * c := by rw [mul_sub, mul_one]
    rw [this, hidem_c, sub_self]
  have hc'_comm : ∀ y : R, c' * y = y * c' := by
    intro y
    rw [hc']
    have e1 : (1 - c) * y = y - c * y := by rw [sub_mul, one_mul]
    have e2 : y * (1 - c) = y - y * c := by rw [mul_sub, mul_one]
    rw [e1, e2, hc_comm y]
  have hcP₀ : ∀ m : (ModuleCat.of R (P₀ : Type v) : Type v), c • m = m := by
    intro m
    apply Subtype.ext
    change c • (m : Shrink.{v} R) = (m : Shrink.{v} R)
    apply sh.injective
    rw [map_smul, smul_eq_mul]
    have hfix : sh (m : Shrink.{v} R) = sh (m : Shrink.{v} R) * c := by
      have h := hPiR (sh (m : Shrink.{v} R))
      rwa [sh.symm_apply_apply, (Submodule.projection_eq_self_iff hCompl _).mpr m.2] at h
    rw [hc_comm (sh (m : Shrink.{v} R))]
    exact hfix.symm
  have hc'Q : ∀ m : (ModuleCat.of R (Q₀ : Type v) : Type v), c' • m = m := by
    intro m
    apply Subtype.ext
    change c' • (m : Shrink.{v} R) = (m : Shrink.{v} R)
    have hkill : c • (m : Shrink.{v} R) = 0 := by
      apply sh.injective
      rw [map_smul, smul_eq_mul, map_zero]
      have h := hPiR (sh (m : Shrink.{v} R))
      rw [sh.symm_apply_apply, (Submodule.projection_apply_eq_zero_iff hCompl).mpr m.2,
        map_zero] at h
      rw [hc_comm (sh (m : Shrink.{v} R))]
      exact h.symm
    rw [hc', sub_smul, one_smul, hkill, sub_zero]
  have factorX : ∀ (U : ModuleCat.{v} R), IsSimpleModule R U →
      auxiliaryModuleRelationOverRing R (ModuleCat.of R (Shrink.{v} R)) U := by
    intro U hU
    haveI := hU
    haveI : Nontrivial (U : Type v) := IsSimpleModule.nontrivial R (U : Type v)
    obtain ⟨u₀, hu₀⟩ := exists_ne (0 : (U : Type v))
    have hspan : Submodule.span R {u₀} = ⊤ := (hU.eq_bot_or_eq_top _).resolve_left (fun h => by
      have : u₀ ∈ (⊥ : Submodule R (U : Type v)) := h ▸ Submodule.mem_span_singleton_self u₀
      exact hu₀ ((Submodule.mem_bot R).mp this))
    refine simple_target_iff.mpr ⟨hU, ⊤,
      (LinearMap.toSpanSingleton R (U : Type v) u₀).comp
        (sh.toLinearMap.comp (⊤ : Submodule R (Shrink.{v} R)).subtype), ?_⟩
    intro y
    have hy : y ∈ Submodule.span R {u₀} := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨⟨sh.symm r, Submodule.mem_top⟩, by simp [LinearMap.toSpanSingleton_apply]⟩
  have hcS : ∀ s : (S : Type v), c • s = s := by
    have hSsplit : auxiliaryModuleRelationOverRing R (ModuleCat.of R P₀) S := by
      rcases auxiliaryModuleRelationOverRing.submodule_or_quotient P₀ (factorX S hS) with h | h
      · exact h
      · exact absurd ((auxiliaryModuleRelation_equivalence R).refl S) (hbad S
          (auxiliaryModuleRelationOverRing.of_linearEquiv
            (Submodule.quotientEquivOfIsCompl P₀ Q₀ hCompl).symm h))
    exact scalar_actsAsIdentity_of_condition R hcP₀ hSsplit
  rcases auxiliaryModuleRelationOverRing.submodule_or_quotient P₀ (factorX T hT) with hTP | hTQ'
  · exact hgood T hTP
  · exfalso
    have hTQ : auxiliaryModuleRelationOverRing R (ModuleCat.of R Q₀) T :=
      auxiliaryModuleRelationOverRing.of_linearEquiv
        (Submodule.quotientEquivOfIsCompl P₀ Q₀ hCompl).symm hTQ'
    have hc'T : ∀ t : (T : Type v), c' • t = t :=
      scalar_actsAsIdentity_of_condition R hc'Q hTQ
    have hf_idem : IsIdempotentElem f := hindec.2.1
    have hf_central : ∀ y, f * y = y * f := hindec.2.2.1
    have g1idem : (f * c) * (f * c) = f * c := by
      rw [mul_assoc f c (f * c), ← mul_assoc c f c, hc_comm f, mul_assoc f c c, hidem_c,
        ← mul_assoc, hf_idem.eq]
    have g2idem : (f * c') * (f * c') = f * c' := by
      rw [mul_assoc f c' (f * c'), ← mul_assoc c' f c', hc'_comm f, mul_assoc f c' c', hidem_c',
        ← mul_assoc, hf_idem.eq]
    have g12 : (f * c) * (f * c') = 0 := by
      rw [mul_assoc f c (f * c'), ← mul_assoc c f c', hc_comm f, mul_assoc f c c', hcc',
        mul_zero, mul_zero]
    have hfc_comm : ∀ y, (f * c) * y = y * (f * c) := by
      intro y
      rw [mul_assoc, hc_comm y, ← mul_assoc, hf_central y, mul_assoc]
    have hfc'_comm : ∀ y, (f * c') * y = y * (f * c') := by
      intro y
      rw [mul_assoc, hc'_comm y, ← mul_assoc, hf_central y, mul_assoc]
    have hfsum : f = f * c + f * c' := by rw [← mul_add, hc', add_sub_cancel, mul_one]
    haveI : Nontrivial (S : Type v) := IsSimpleModule.nontrivial R (S : Type v)
    obtain ⟨s, hs⟩ := exists_ne (0 : (S : Type v))
    have hg1ne : f * c ≠ 0 := fun h0 => hs (by
      have h1 : (f * c) • s = s := by rw [mul_smul, hcS s, hSf s]
      rw [h0, zero_smul] at h1
      exact h1.symm)
    haveI : Nontrivial (T : Type v) := IsSimpleModule.nontrivial R (T : Type v)
    obtain ⟨t, ht⟩ := exists_ne (0 : (T : Type v))
    have hg2ne : f * c' ≠ 0 := fun h0 => ht (by
      have h1 : (f * c') • t = t := by rw [mul_smul, hc'T t, hTf t]
      rw [h0, zero_smul] at h1
      exact h1.symm)
    exact hindec.2.2.2
      ⟨f * c, f * c', hg1ne, hg2ne, g1idem, g2idem, hfc_comm, hfc'_comm, g12, hfsum⟩

/-- Morphisms between modules are subsingleton under the displayed simple-module conditions. -/
@[source_ref "Chapter9/Problem9.5.3" (role := supporting)]
theorem hom_subsingleton_of_simpleModule_conditions [Small.{v} R]
    {S T : ModuleCat.{v} R} (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    {M N : ModuleCat.{v} R} (hM : auxiliaryModuleRelation'''' R S M)
    (hN : auxiliaryModuleRelation'''' R T N) (hST : ¬ auxiliaryModuleRelation R S T) :
    Subsingleton (M ⟶ N) := by
  suffices h0 : ∀ f : M ⟶ N, f = 0 by
    exact ⟨fun f g => by rw [h0 f, h0 g]⟩
  intro f
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  by_contra hfhom
  have hrange : LinearMap.range f.hom ≠ ⊥ := by
    rwa [Ne, LinearMap.range_eq_bot]
  haveI hnt : Nontrivial (LinearMap.range f.hom) :=
    Submodule.nontrivial_iff_ne_bot.mpr hrange
  obtain ⟨U, hU⟩ :=
    exists_target (M := ModuleCat.of R (LinearMap.range f.hom))
  have hUN : auxiliaryModuleRelationOverRing R N U :=
    auxiliaryModuleRelationOverRing.of_submodule (LinearMap.range f.hom) hU
  have hUM : auxiliaryModuleRelationOverRing R M U :=
    auxiliaryModuleRelationOverRing.of_surjective f.hom.rangeRestrict
      (LinearMap.surjective_rangeRestrict _) hU
  have h1 : auxiliaryModuleRelation R U S := hM U hUM
  have h2 : auxiliaryModuleRelation R U T := hN U hUN
  exact hST ((auxiliaryModuleRelation_equivalence R).trans
    ((auxiliaryModuleRelation_equivalence R).symm h1) h2)

/-- For an indecomposable finite-length module, two displayed auxiliary conditions imply another displayed condition. -/
theorem condition_of_indecomposable_of_auxiliaryConditions [Small.{v} R]
    {M : ModuleCat.{v} R} (hM : Indecomposable M) (hfl : IsFiniteLength R M)
    {S T : ModuleCat.{v} R} (hS : auxiliaryModuleRelationOverRing R M S)
    (hT : auxiliaryModuleRelationOverRing R M T) :
    auxiliaryModuleRelation R S T :=
  targets_related_of_sourceRelations_of_indecomposable_finiteLength hM hfl hS hT

/-- An indecomposable finite-length module admits a simple module satisfying the displayed condition. -/
@[source_ref "Chapter9/Problem9.5.3" (role := supporting)]
theorem exists_simpleModule_with_condition_of_indecomposable [Small.{v} R]
    {M : ModuleCat.{v} R} (hM : Indecomposable M) (hfl : IsFiniteLength R M) :
    ∃ S : ModuleCat.{v} R, IsSimpleModule R S ∧ auxiliaryModuleRelation'''' R S M := by
  haveI hnt : Nontrivial (M : Type v) := by
    rw [← not_subsingleton_iff_nontrivial, ← ModuleCat.isZero_iff_subsingleton]
    exact hM.1
  obtain ⟨S, hS⟩ := exists_target (M := M)
  refine ⟨S, hS.1, ?_⟩
  intro T hT
  exact (auxiliaryModuleRelation_equivalence R).symm
    (condition_of_indecomposable_of_auxiliaryConditions R hM hfl hS hT)

end RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.Auxiliary.statement014176 := _root_.RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.centerScalar_ext_comp
