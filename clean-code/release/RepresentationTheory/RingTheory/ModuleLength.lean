/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier
-/

import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection
import RepresentationTheory.Algebra.Module.SimpleQuotient
import RepresentationTheory.CategoryTheory.Abelian.ModuleCat.ExtProperties
import RepresentationTheory.CategoryTheory.Abelian.ModuleCat.ShortExact

/-!
# Finite-length module decompositions

This module develops finite-length decompositions and relation criteria for module objects.
-/

universe v u

open CategoryTheory CategoryTheory.Limits
open RepresentationTheory.ModuleCat.Auxiliary
open RepresentationTheory.CategoryTheory.Abelian.ModuleCat.ExtProperties

namespace RepresentationTheory.RingTheory.ModuleLength

variable {R : Type u} [Ring R] [Small.{v} R]

omit [Small.{v} R] in
/-- Submodules of a finite-length module have finite length. -/
theorem finiteLength_submodule_of_finiteLength {X : Type v} [AddCommGroup X] [Module R X]
    (hX : IsFiniteLength R X) (P : Submodule R X) : IsFiniteLength R P := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hX ⊢
  obtain ⟨hN, hA⟩ := hX
  haveI := hN; haveI := hA
  exact ⟨inferInstance, inferInstance⟩

omit [Small.{v} R] in
/-- Quotients of a finite-length module have finite length. -/
theorem finiteLength_quotient_of_finiteLength {X : Type v} [AddCommGroup X] [Module R X]
    (hX : IsFiniteLength R X) (P : Submodule R X) : IsFiniteLength R (X ⧸ P) := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hX ⊢
  obtain ⟨hN, hA⟩ := hX
  haveI := hN; haveI := hA
  exact ⟨inferInstance, inferInstance⟩

/-- A suitable subsingleton condition supplies a complementary submodule linearly equivalent to the quotient. -/
theorem exists_isCompl_linearEquiv_quotient_of_subsingleton_ext
    {X : Type v} [AddCommGroup X] [Module R X] (Q : Submodule R X)
    (hExt : Subsingleton (Abelian.Ext (ModuleCat.of R (X ⧸ Q)) (ModuleCat.of R Q) 1)) :
    ∃ P : Submodule R X, IsCompl P Q ∧ Nonempty (↥P ≃ₗ[R] (X ⧸ Q)) := by
  set f : ModuleCat.of R Q ⟶ ModuleCat.of R X := ModuleCat.ofHom Q.subtype with hf
  set g : ModuleCat.of R X ⟶ ModuleCat.of R (X ⧸ Q) := ModuleCat.ofHom Q.mkQ with hg
  have hw : f ≫ g = 0 := by ext x; simp [hf, hg]
  have hSES : (ShortComplex.mk f g hw).ShortExact :=
    ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ Q) Q.subtype_injective
      Q.mkQ_surjective
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hSES (ModuleCat.of R Q)
    (Abelian.Ext.mk₀ (𝟙 (ModuleCat.of R Q))) (show (1 : ℕ) + 0 = 1 from rfl)
    (Subsingleton.elim _ 0)
  have hfr : f ≫ Abelian.Ext.homEquiv₀ x₂ = 𝟙 (ModuleCat.of R Q) := by
    apply (Abelian.Ext.mk₀_bijective (ModuleCat.of R Q) (ModuleCat.of R Q)).injective
    rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_homEquiv₀_apply]
    exact hx₂
  set r : X →ₗ[R] ↥Q := (Abelian.Ext.homEquiv₀ x₂).hom with hr
  have hcomp : r ∘ₗ Q.subtype = LinearMap.id := by
    have := congrArg ModuleCat.Hom.hom hfr
    simpa [hf, hr, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id] using this
  have hrf : ∀ q : ↥Q, r (q : X) = q := fun q => by
    have := LinearMap.congr_fun hcomp q; simpa using this
  set proj : X →ₗ[R] X := Q.subtype ∘ₗ r with hproj
  have hisproj : LinearMap.IsProj Q proj :=
    ⟨fun x => (r x).2, fun x hx => by
      simp only [hproj, LinearMap.comp_apply]
      exact congrArg Subtype.val (hrf ⟨x, hx⟩)⟩
  refine ⟨LinearMap.ker proj, hisproj.isCompl.symm,
    ⟨(Submodule.quotientEquivOfIsCompl Q (LinearMap.ker proj) hisproj.isCompl).symm⟩⟩

omit [Small.{v} R] in
/-- A relation out of the indicated quotient yields one out of either a complementary submodule or the quotient by the ambient submodule. -/
theorem relation_or_of_isCompl {X : Type v} [AddCommGroup X] [Module R X] (N : Submodule R X)
    {A B : Submodule R N} (hAB : IsCompl A B) {U : ModuleCat.{v} R}
    (h : auxiliaryModuleRelationOverRing R (ModuleCat.of R (X ⧸ B.map N.subtype)) U) :
    auxiliaryModuleRelationOverRing R (ModuleCat.of R A) U ∨
      auxiliaryModuleRelationOverRing R (ModuleCat.of R (X ⧸ N)) U := by
  set Q : Submodule R X := B.map N.subtype with hQ
  have hle : Q ≤ N := Submodule.map_subtype_le _ _
  rcases auxiliaryModuleRelationOverRing.submodule_or_quotient (K := N.map Q.mkQ) h with hsub | hquot
  · left
    set κ : N →ₗ[R] (X ⧸ Q) := Q.mkQ ∘ₗ N.subtype with hκ
    have hrangeκ : LinearMap.range κ = N.map Q.mkQ := by
      rw [hκ, LinearMap.range_comp, Submodule.range_subtype]
    have hkerκ : LinearMap.ker κ = B := by
      ext n
      simp only [LinearMap.mem_ker, hκ, LinearMap.comp_apply, Submodule.subtype_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hQ, Submodule.mem_map]
      constructor
      · rintro ⟨b, hb, hbeq⟩
        rwa [← N.subtype_injective hbeq]
      · intro hn
        exact ⟨n, hn, rfl⟩
    have e1 : (N ⧸ B) ≃ₗ[R] ↥(N.map Q.mkQ) :=
      (Submodule.quotEquivOfEq B (LinearMap.ker κ) hkerκ.symm).trans
        ((LinearMap.quotKerEquivRange κ).trans (LinearEquiv.ofEq _ _ hrangeκ))
    have e2 : (N ⧸ B) ≃ₗ[R] ↥A := Submodule.quotientEquivOfIsCompl B A hAB.symm
    exact auxiliaryModuleRelationOverRing.of_linearEquiv (e2.symm.trans e1) hsub
  · right
    exact auxiliaryModuleRelationOverRing.of_linearEquiv
      (Submodule.quotientQuotientEquivQuotient Q N hle).symm hquot

/-- A finite-length module has complementary submodules separating two opaque relation conditions. -/
theorem exists_isCompl_with_relation_partition_of_finiteLength {S : ModuleCat.{v} R} :
    ∀ {X : Type v} [AddCommGroup X] [Module R X], IsFiniteLength R X →
      ∃ P Q : Submodule R X, IsCompl P Q ∧
        (∀ U : ModuleCat.{v} R,
          auxiliaryModuleRelationOverRing R (ModuleCat.of R P) U → auxiliaryModuleRelation R S U) ∧
        (∀ V : ModuleCat.{v} R,
          auxiliaryModuleRelationOverRing R (ModuleCat.of R Q) V →
            ¬ auxiliaryModuleRelation R S V) := by
  intro X _ _ hX
  induction hX with
  | @of_subsingleton X _ _ _ =>
      have hns : ∀ (P : Submodule R X) (U : ModuleCat.{v} R),
          auxiliaryModuleRelationOverRing R (ModuleCat.of R P) U → False := fun P U hU =>
        absurd (inferInstanceAs (Subsingleton (ModuleCat.of R P)))
          (not_subsingleton_iff_nontrivial.mpr hU.nontrivial)
      exact ⟨⊤, ⊥, isCompl_top_bot, fun U hU => absurd (hns ⊤ U hU) not_false,
        fun V hV => absurd (hns ⊥ V hV) not_false⟩
  | @of_simple_quotient X _ _ N _ hNfl ih =>
      obtain ⟨P₀, Q₀, hcompl₀, hgood₀, hbad₀⟩ := ih
      have hXfl : IsFiniteLength R X := IsFiniteLength.of_simple_quotient hNfl
      set P₁ : Submodule R X := P₀.map N.subtype with hP₁
      set Q₁ : Submodule R X := Q₀.map N.subtype with hQ₁
      have hmapfac : ∀ (B₀ : Submodule R N) (W : ModuleCat.{v} R),
          auxiliaryModuleRelationOverRing R (ModuleCat.of R (B₀.map N.subtype)) W →
            auxiliaryModuleRelationOverRing R (ModuleCat.of R B₀) W := fun B₀ W h =>
        auxiliaryModuleRelationOverRing.of_linearEquiv
          (Submodule.equivMapOfInjective N.subtype N.subtype_injective B₀) h
      have hQ₁bad : ∀ V : ModuleCat.{v} R,
          auxiliaryModuleRelationOverRing R (ModuleCat.of R Q₁) V → ¬ auxiliaryModuleRelation R S V := fun V hV =>
        hbad₀ V (hmapfac Q₀ V hV)
      have hP₁good : ∀ U : ModuleCat.{v} R,
          auxiliaryModuleRelationOverRing R (ModuleCat.of R P₁) U → auxiliaryModuleRelation R S U := fun U hU =>
        hgood₀ U (hmapfac P₀ U hU)
      by_cases hlink : auxiliaryModuleRelation R S (ModuleCat.of R (X ⧸ N))
      · have hquotgood : ∀ (W : ModuleCat.{v} R),
            auxiliaryModuleRelationOverRing R (ModuleCat.of R (X ⧸ Q₁)) W → auxiliaryModuleRelation R S W := by
          intro W hW
          rcases relation_or_of_isCompl N hcompl₀ hW with hWP | hWN
          · exact hgood₀ W hWP
          · obtain ⟨e⟩ := auxiliaryModuleRelationOverRing.linearEquiv
              ‹IsSimpleModule R (X ⧸ N)› hWN
            refine (auxiliaryModuleRelation_equivalence R).trans hlink ?_
            exact auxiliaryModuleRelation_of_iso R ‹IsSimpleModule R (X ⧸ N)› hWN.1 e.symm.toModuleIso
        have hExt : Subsingleton
            (Abelian.Ext (ModuleCat.of R (X ⧸ Q₁)) (ModuleCat.of R Q₁) 1) := by
          apply extOneSubsingleton_of_finiteLengthModules_of_exclusion
            (finiteLength_quotient_of_finiteLength hXfl Q₁)
            (finiteLength_submodule_of_finiteLength hXfl Q₁)
          intro U V hU hV hUV
          exact hQ₁bad V hV ((auxiliaryModuleRelation_equivalence R).trans (hquotgood U hU) hUV)
        obtain ⟨P, hPcompl, ⟨ePQ⟩⟩ :=
          exists_isCompl_linearEquiv_quotient_of_subsingleton_ext Q₁ hExt
        refine ⟨P, Q₁, hPcompl, fun U hU => ?_, hQ₁bad⟩
        exact hquotgood U (auxiliaryModuleRelationOverRing.of_linearEquiv ePQ.symm hU)
      · have hquotbad : ∀ (W : ModuleCat.{v} R),
            auxiliaryModuleRelationOverRing R (ModuleCat.of R (X ⧸ P₁)) W →
              ¬ auxiliaryModuleRelation R S W := by
          intro W hW
          rcases relation_or_of_isCompl N hcompl₀.symm hW with hWQ | hWN
          · exact hbad₀ W hWQ
          · obtain ⟨e⟩ := auxiliaryModuleRelationOverRing.linearEquiv
              ‹IsSimpleModule R (X ⧸ N)› hWN
            intro hSW
            exact hlink ((auxiliaryModuleRelation_equivalence R).trans hSW
              (auxiliaryModuleRelation_of_iso R hWN.1 ‹IsSimpleModule R (X ⧸ N)› e.toModuleIso))
        have hExt : Subsingleton
            (Abelian.Ext (ModuleCat.of R (X ⧸ P₁)) (ModuleCat.of R P₁) 1) := by
          apply extOneSubsingleton_of_finiteLengthModules_of_exclusion
            (finiteLength_quotient_of_finiteLength hXfl P₁)
            (finiteLength_submodule_of_finiteLength hXfl P₁)
          intro U V hU hV hUV
          exact hquotbad U hU ((auxiliaryModuleRelation_equivalence R).trans (hP₁good V hV)
            ((auxiliaryModuleRelation_equivalence R).symm hUV))
        obtain ⟨Q, hQcompl, ⟨eQP⟩⟩ :=
          exists_isCompl_linearEquiv_quotient_of_subsingleton_ext P₁ hExt
        refine ⟨P₁, Q, hQcompl.symm, hP₁good, fun V hV => ?_⟩
        exact hquotbad V (auxiliaryModuleRelationOverRing.of_linearEquiv eQP.symm hV)

/-- Derives a relation between two targets from two opaque relations out of an indecomposable finite-length module. -/
theorem targets_related_of_sourceRelations_of_indecomposable_finiteLength
    {M : ModuleCat.{v} R} (hM : Indecomposable M) (hfl : IsFiniteLength R M)
    {S T : ModuleCat.{v} R}
    (hS : auxiliaryModuleRelationOverRing R M S) (hT : auxiliaryModuleRelationOverRing R M T) :
    auxiliaryModuleRelation R S T := by
  obtain ⟨P, Q, hcompl, hgood, hbad⟩ :=
    exists_isCompl_with_relation_partition_of_finiteLength (S := S) hfl
  have iso : M ≅ (ModuleCat.of R P) ⊞ (ModuleCat.of R Q) :=
    (LinearEquiv.toModuleIso (Submodule.prodEquivOfIsCompl P Q hcompl)).symm ≪≫
      (ModuleCat.biprodIsoProd (ModuleCat.of R P) (ModuleCat.of R Q)).symm
  rcases hM.2 (ModuleCat.of R P) (ModuleCat.of R Q) iso with hZ | hZ
  · exfalso
    have hPbot : P = ⊥ := by
      have hsub : Subsingleton (P : Type v) := ModuleCat.isZero_iff_subsingleton.mp hZ
      rw [Submodule.eq_bot_iff]
      exact fun x hx => congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : P) 0)
    have hQtop : Q = ⊤ := by rw [← hcompl.sup_eq_top, hPbot, bot_sup_eq]
    have eQ : (Q : Type v) ≃ₗ[R] M :=
      (LinearEquiv.ofEq Q ⊤ hQtop).trans Submodule.topEquiv
    exact hbad S (auxiliaryModuleRelationOverRing.of_linearEquiv eQ hS)
      ((auxiliaryModuleRelation_equivalence R).refl S)
  · have hQbot : Q = ⊥ := by
      have hsub : Subsingleton (Q : Type v) := ModuleCat.isZero_iff_subsingleton.mp hZ
      rw [Submodule.eq_bot_iff]
      exact fun x hx => congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : Q) 0)
    have hPtop : P = ⊤ := by rw [← hcompl.sup_eq_top, hQbot, sup_bot_eq]
    have eP : (P : Type v) ≃ₗ[R] M :=
      (LinearEquiv.ofEq P ⊤ hPtop).trans Submodule.topEquiv
    exact hgood T (auxiliaryModuleRelationOverRing.of_linearEquiv eP hT)

end RepresentationTheory.RingTheory.ModuleLength
