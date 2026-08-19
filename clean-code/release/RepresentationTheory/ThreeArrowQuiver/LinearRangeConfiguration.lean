/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.FinFourLinearData

/-!
# Linear range configuration of a four-vertex quiver
-/


namespace RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration

/-- The distinguished quiver morphism from vertex zero to the sink. -/
def zeroToSink : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA 0 3 := ⟨⟨by decide, by decide⟩⟩
/-- The distinguished quiver morphism from vertex one to the sink. -/
def oneToSink : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA 1 3 := ⟨⟨by decide, by decide⟩⟩
/-- The distinguished quiver morphism from vertex two to the sink. -/
def twoToSink : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA 2 3 := ⟨⟨by decide, by decide⟩⟩

/-- The complex-linear map carried by the arrow from vertex zero to the sink. -/
noncomputable abbrev zeroToSinkLinearMap :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt
    0 3 zeroToSink
/-- The complex-linear map carried by the arrow from vertex one to the sink. -/
noncomputable abbrev oneToSinkLinearMap :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt
    1 3 oneToSink
/-- The complex-linear map carried by the arrow from vertex two to the sink. -/
noncomputable abbrev twoToSinkLinearMap :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt
    2 3 twoToSink

/-- Every morphism in the four-vertex quiver is one of the three distinguished morphisms into the sink. -/
theorem hom_eq_zeroToSink_or_oneToSink_or_twoToSink {a b : Fin 4} (e : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA a b) :
    (a = 0 ∧ b = 3 ∧ HEq e zeroToSink) ∨
    (a = 1 ∧ b = 3 ∧ HEq e oneToSink) ∨
    (a = 2 ∧ b = 3 ∧ HEq e twoToSink) := by
  rcases e with ⟨⟨hadj, hlt⟩⟩
  have hclass : ∀ a b : Fin 4, RepresentationTheory.IntegerMatrices.integerMatrixA a b = 1 → a < b →
      (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 3) ∨ (a = 2 ∧ b = 3) := by
    decide
  rcases hclass a b hadj hlt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩)

/-- Supplies an additive commutative group structure on every vertex space. -/
noncomputable local instance vertexAddCommGroup (v : Fin 4) : AddCommGroup
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt v) :=
  RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := ℂ)

private theorem centre_finrank : Module.finrank ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 3) = 2 := by
  have h := RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt_finrank_eq 3
  have h' : (Module.finrank ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 3) : ℤ) = 2 := by
    simpa using h
  exact_mod_cast h'

private theorem arm_finrank (i : Fin 4) (hi : i ≠ 3) : Module.finrank ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt i) = 1 := by
  have h := RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt_finrank_eq i
  fin_cases i <;> simp_all

private theorem armMap_injective {i : Fin 4} (hi : i ≠ 3)
    (e : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA i 3) : Function.Injective
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt
        i 3 e) := by
  let A := @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
    RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt i 3 e
  obtain ⟨S, hKS⟩ := Submodule.exists_isCompl (LinearMap.ker A)
  let P : ∀ v, Submodule ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt v) :=
    fun v => if h : v = i then h ▸ LinearMap.ker A else ⊥
  let R : ∀ v, Submodule ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt v) :=
    fun v => if h : v = i then h ▸ S else ⊤
  have h3i : (3 : Fin 4) ≠ i := Ne.symm hi
  have hP : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA a b), ∀ x ∈ P a,
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt
        a b f x ∈ P b := by
    intro a b f x hx
    by_cases ha : a = i
    · subst a
      rcases hom_eq_zeroToSink_or_oneToSink_or_twoToSink f with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
      all_goals
        have hf : f = e := Subsingleton.elim _ _
        subst f
        have hxker : x ∈ LinearMap.ker A := by
          simpa only [P, dif_pos rfl] using hx
        have hzero : A x = 0 := LinearMap.mem_ker.mp hxker
        simp [P, A, hzero]
    · have hxzero : x = 0 := by
        have : x ∈ (⊥ : Submodule ℂ
            (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt a)) := by
          simpa [P, ha] using hx
        exact (Submodule.mem_bot (R := ℂ)).mp this
      subst x
      simp [P]
  have hR : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA a b), ∀ x ∈ R a,
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt
        a b f x ∈ R b := by
    intro a b f x hx
    rcases hom_eq_zeroToSink_or_oneToSink_or_twoToSink f with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;>
      simp [R, h3i]
  have hcompl : ∀ v, IsCompl (P v) (R v) := by
    intro v
    by_cases hv : v = i
    · subst v
      simpa [P, R] using hKS
    · simpa [P, R, hv] using isCompl_bot_top
  rcases RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt_hasProperty.2 P R hP hR hcompl with hbot | hbot
  · exact LinearMap.ker_eq_bot.mp (by simpa [P] using hbot i)
  · exfalso
    have htop : (⊤ : Submodule ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 3)) = ⊥ := by
      simpa [R, h3i] using hbot 3
    have hrank := congrArg (fun T : Submodule ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 3) =>
          Module.finrank ℂ T) htop
    simp [centre_finrank] at hrank

/-- Each of the three linear maps entering the sink is injective. -/
theorem incomingLinearMaps_injective :
    Function.Injective zeroToSinkLinearMap ∧
    Function.Injective oneToSinkLinearMap ∧
    Function.Injective twoToSinkLinearMap :=
  ⟨armMap_injective (by decide) zeroToSink,
    armMap_injective (by decide) oneToSink,
    armMap_injective (by decide) twoToSink⟩

/-- The images of the three incoming linear maps jointly generate the sink space. -/
theorem sup_range_eq_top :
    LinearMap.range zeroToSinkLinearMap ⊔ LinearMap.range oneToSinkLinearMap ⊔
      LinearMap.range twoToSinkLinearMap = ⊤ := by
  let A₁ := @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
    RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 0 3 zeroToSink
  let A₂ := @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
    RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 1 3 oneToSink
  let A₃ := @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
    RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 2 3 twoToSink
  let T := LinearMap.range A₁ ⊔ LinearMap.range A₂ ⊔ LinearMap.range A₃
  obtain ⟨S, hTS⟩ := Submodule.exists_isCompl T
  let P : ∀ v, Submodule ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt v) :=
    fun v => if h : v = 3 then h ▸ T else ⊤
  let R : ∀ v, Submodule ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt v) :=
    fun v => if h : v = 3 then h ▸ S else ⊥
  have hP : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA a b), ∀ x ∈ P a,
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt
        a b f x ∈ P b := by
    intro a b f x hx
    rcases hom_eq_zeroToSink_or_oneToSink_or_twoToSink f with ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
    · cases he
      exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (LinearMap.mem_range.mpr ⟨x, rfl⟩))
    · cases he
      exact Submodule.mem_sup_left (Submodule.mem_sup_right
        (LinearMap.mem_range.mpr ⟨x, rfl⟩))
    · cases he
      exact Submodule.mem_sup_right (LinearMap.mem_range.mpr ⟨x, rfl⟩)
  have hR : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA a b), ∀ x ∈ R a,
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt
        a b f x ∈ R b := by
    intro a b f x hx
    rcases hom_eq_zeroToSink_or_oneToSink_or_twoToSink f with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
    all_goals
      have hxzero : x = 0 := by simpa [R] using hx
      subst x
      simp [R]
  have hcompl : ∀ v, IsCompl (P v) (R v) := by
    intro v
    by_cases hv : v = 3
    · subst v
      simpa [P, R] using hTS
    · simpa [P, R, hv] using isCompl_top_bot
  rcases RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt_hasProperty.2 P R hP hR hcompl with hbot | hbot
  · have htop : (⊤ : Submodule ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 0)) = ⊥ := by
      simpa [P] using hbot 0
    have hrank := congrArg (fun U : Submodule ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 0) =>
          Module.finrank ℂ U) htop
    simp [arm_finrank 0 (by decide)] at hrank
  · have hS : S = ⊥ := by simpa [R] using hbot 3
    have htop := hTS.sup_eq_top
    rw [hS, sup_bot_eq] at htop
    simpa [T, A₁, A₂, A₃] using htop

/-- Auxiliary data packaging the compatible linear equivalences used for the incoming maps. -/
structure AuxiliaryRangeEquivData where
  /-- The chosen linear automorphism of the vector space assigned to the sink. -/
  sinkEquiv : (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
    RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 3) ≃ₗ[ℂ]
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 3)
  /-- Identifies the space at vertex zero with the image of its map into the sink. -/
  zeroEquivRange : (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
    RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 0) ≃ₗ[ℂ] LinearMap.range zeroToSinkLinearMap
  /-- Identifies the space at vertex one with the image of its map into the sink. -/
  oneEquivRange : (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
    RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 1) ≃ₗ[ℂ] LinearMap.range oneToSinkLinearMap
  /-- Identifies the space at vertex two with the image of its map into the sink. -/
  twoEquivRange : (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
    RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 2) ≃ₗ[ℂ] LinearMap.range twoToSinkLinearMap
  /-- The sink equivalence and the range equivalence agree along the map from vertex zero. -/
  zero_compatibility : ∀ x, sinkEquiv (zeroToSinkLinearMap x) = (LinearMap.range zeroToSinkLinearMap).subtype (zeroEquivRange x)
  /-- The sink equivalence and the range equivalence agree along the map from vertex one. -/
  one_compatibility : ∀ x, sinkEquiv (oneToSinkLinearMap x) = (LinearMap.range oneToSinkLinearMap).subtype (oneEquivRange x)
  /-- The sink equivalence and the range equivalence agree along the map from vertex two. -/
  two_compatibility : ∀ x, sinkEquiv (twoToSinkLinearMap x) = (LinearMap.range twoToSinkLinearMap).subtype (twoEquivRange x)

/-- Compatible auxiliary range-equivalence data can be chosen. -/
theorem nonempty_auxiliaryRangeEquivData : Nonempty AuxiliaryRangeEquivData := by
  obtain ⟨h₁, h₂, h₃⟩ := incomingLinearMaps_injective
  refine ⟨{
    sinkEquiv := LinearEquiv.refl ℂ _
    zeroEquivRange := LinearEquiv.ofInjective zeroToSinkLinearMap h₁
    oneEquivRange := LinearEquiv.ofInjective oneToSinkLinearMap h₂
    twoEquivRange := LinearEquiv.ofInjective twoToSinkLinearMap h₃
    zero_compatibility := fun _ => rfl
    one_compatibility := fun _ => rfl
    two_compatibility := fun _ => rfl }⟩

/-- The sink has dimension two, every incoming image has dimension one, and the three images span the sink. -/
theorem finrank_ranges_and_sup_eq_top :
    Module.finrank ℂ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj ℂ (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
      RepresentationTheory.Quiver.FinFourLinearData.finFourDiagramAAlt 3) = 2 ∧
    Module.finrank ℂ (LinearMap.range zeroToSinkLinearMap) = 1 ∧
    Module.finrank ℂ (LinearMap.range oneToSinkLinearMap) = 1 ∧
    Module.finrank ℂ (LinearMap.range twoToSinkLinearMap) = 1 ∧
    LinearMap.range zeroToSinkLinearMap ⊔ LinearMap.range oneToSinkLinearMap ⊔
      LinearMap.range twoToSinkLinearMap = ⊤ := by
  obtain ⟨h₁, h₂, h₃⟩ := incomingLinearMaps_injective
  refine ⟨centre_finrank, ?_, ?_, ?_, sup_range_eq_top⟩
  · rw [LinearMap.finrank_range_of_inj h₁]
    exact arm_finrank 0 (by decide)
  · rw [LinearMap.finrank_range_of_inj h₂]
    exact arm_finrank 1 (by decide)
  · rw [LinearMap.finrank_range_of_inj h₃]
    exact arm_finrank 2 (by decide)

end RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration
