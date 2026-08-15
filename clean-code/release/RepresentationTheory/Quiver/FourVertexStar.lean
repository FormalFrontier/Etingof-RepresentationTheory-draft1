import RepresentationTheory.Quiver.FinFourLinearData

/-!
# The intermediate D₄ reflection representation

The first three actual reflections produce the outward D₄ representation with a
one-dimensional space at every vertex and invertible maps along all three arrows.
-/

namespace RepresentationTheory.Quiver.FourVertexStar

open RepresentationTheory.Quiver.FinFourLinearData

/-- A quiver arrow from vertex 3 to vertex 0. -/
noncomputable def arrowToZero : @Quiver.Hom (Fin 4) finFourQuiverD 3 0 :=
  Classical.choice ((finFourQuiverD_hasAuxProperty.2.1 3 0 (by decide)).resolve_right
    (fun h => (finFourQuiverD_hasAuxPropertyAtThree 0).false (Classical.choice h)))

/-- A quiver arrow from vertex 3 to vertex 1. -/
noncomputable def arrowToOne : @Quiver.Hom (Fin 4) finFourQuiverD 3 1 :=
  Classical.choice ((finFourQuiverD_hasAuxProperty.2.1 3 1 (by decide)).resolve_right
    (fun h => (finFourQuiverD_hasAuxPropertyAtThree 1).false (Classical.choice h)))

/-- A quiver arrow from vertex 3 to vertex 2. -/
noncomputable def arrowToTwo : @Quiver.Hom (Fin 4) finFourQuiverD 3 2 :=
  Classical.choice ((finFourQuiverD_hasAuxProperty.2.1 3 2 (by decide)).resolve_right
    (fun h => (finFourQuiverD_hasAuxPropertyAtThree 2).false (Classical.choice h)))

/-- The complex-linear map from the carrier at vertex 3 to the carrier at vertex 0. -/
noncomputable abbrev linearMapToZero :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3 0 arrowToZero
/-- The complex-linear map from the carrier at vertex 3 to the carrier at vertex 1. -/
noncomputable abbrev linearMapToOne :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3 1 arrowToOne
/-- The complex-linear map from the carrier at vertex 3 to the carrier at vertex 2. -/
noncomputable abbrev linearMapToTwo :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3 2 arrowToTwo

private theorem finFourQuiverD_arrow_cases {a b : Fin 4} (e : @Quiver.Hom (Fin 4) finFourQuiverD a b) :
    (a = 3 ∧ b = 0 ∧ HEq e arrowToZero) ∨
    (a = 3 ∧ b = 1 ∧ HEq e arrowToOne) ∨
    (a = 3 ∧ b = 2 ∧ HEq e arrowToTwo) := by
  have hadj : RepresentationTheory.IntegerMatrices.integerMatrixA a b = 1 := by
    by_contra h
    exact (finFourQuiverD_hasAuxProperty.1 a b h).false e
  have hb : b ≠ 3 := by
    intro h
    subst b
    exact (finFourQuiverD_hasAuxPropertyAtThree a).false e
  have hclass : ∀ a b : Fin 4, RepresentationTheory.IntegerMatrices.integerMatrixA a b = 1 → b ≠ 3 →
      (a = 3 ∧ b = 0) ∨ (a = 3 ∧ b = 1) ∨ (a = 3 ∧ b = 2) := by
    decide
  rcases hclass a b hadj hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩)

/-- The additive commutative group structure on the carrier at each of the four vertices. -/
noncomputable local instance vertexAddCommGroup (v : Fin 4) : AddCommGroup
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD v) :=
  RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := ℂ)

private theorem finFourDiagramD_finrank (v : Fin 4) : Module.finrank ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD v) = 1 := by
  have h := finFourDiagramD_invariant_eq v
  unfold RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryNat at h
  fin_cases v <;> simp_all

private theorem linearMap_surjective {j : Fin 4} (hj : j ≠ 3)
    (e : @Quiver.Hom (Fin 4) finFourQuiverD 3 j) : Function.Surjective
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3 j e) := by
  let A := @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3 j e
  obtain ⟨S, hRS⟩ := Submodule.exists_isCompl (LinearMap.range A)
  let P : ∀ v, Submodule ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD v) :=
    fun v => if h : v = j then h ▸ LinearMap.range A else ⊤
  let R : ∀ v, Submodule ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD v) :=
    fun v => if h : v = j then h ▸ S else ⊥
  have hP : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) finFourQuiverD a b), ∀ x ∈ P a,
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map ℂ (Fin 4) _ finFourQuiverD finFourDiagramD a b f x ∈ P b := by
    intro a b f x hx
    by_cases hb : b = j
    · subst b
      rcases finFourQuiverD_arrow_cases f with ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
      · cases he
        have hf : arrowToZero = e := Subsingleton.elim _ _
        subst e
        simpa only [P, dif_pos rfl, A] using
          (LinearMap.mem_range.mpr ⟨x, rfl⟩ :
            linearMapToZero x ∈ LinearMap.range linearMapToZero)
      · cases he
        have hf : arrowToOne = e := Subsingleton.elim _ _
        subst e
        simpa only [P, dif_pos rfl, A] using
          (LinearMap.mem_range.mpr ⟨x, rfl⟩ :
            linearMapToOne x ∈ LinearMap.range linearMapToOne)
      · cases he
        have hf : arrowToTwo = e := Subsingleton.elim _ _
        subst e
        simpa only [P, dif_pos rfl, A] using
          (LinearMap.mem_range.mpr ⟨x, rfl⟩ :
            linearMapToTwo x ∈ LinearMap.range linearMapToTwo)
    · simp [P, hb]
  have hR : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) finFourQuiverD a b), ∀ x ∈ R a,
      @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.map ℂ (Fin 4) _ finFourQuiverD finFourDiagramD a b f x ∈ R b := by
    intro a b f x hx
    rcases finFourQuiverD_arrow_cases f with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
    all_goals
      have h3j : (3 : Fin 4) ≠ j := Ne.symm hj
      have hxzero : x = 0 := by simpa [R, h3j] using hx
      subst x
      simp [R]
  have hcompl : ∀ v, IsCompl (P v) (R v) := by
    intro v
    by_cases hv : v = j
    · subst v
      simpa [P, R] using hRS
    · simpa [P, R, hv] using isCompl_top_bot
  rcases finFourDiagramD_hasProperty.2 P R hP hR hcompl with hbot | hbot
  · exfalso
    have h3j : (3 : Fin 4) ≠ j := Ne.symm hj
    have htop : (⊤ : Submodule ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3)) = ⊥ := by
      simpa [P, h3j] using hbot 3
    have hrank := congrArg (fun U : Submodule ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3) =>
          Module.finrank ℂ U) htop
    simp [finFourDiagramD_finrank 3] at hrank
  · have hS : S = ⊥ := by simpa [R] using hbot j
    have htop := hRS.sup_eq_top
    rw [hS, sup_bot_eq] at htop
    exact LinearMap.range_eq_top.mp htop

/-- The three linear maps from vertex 3 to vertices 0, 1, and 2 are bijective. -/
theorem linearMaps_bijective :
    Function.Bijective linearMapToZero ∧ Function.Bijective linearMapToOne ∧
      Function.Bijective linearMapToTwo := by
  have hs₁ := linearMap_surjective (by decide) arrowToZero
  have hs₂ := linearMap_surjective (by decide) arrowToOne
  have hs₃ := linearMap_surjective (by decide) arrowToTwo
  have hi₁ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finFourDiagramD_finrank 3, finFourDiagramD_finrank 0])).mpr hs₁
  have hi₂ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finFourDiagramD_finrank 3, finFourDiagramD_finrank 1])).mpr hs₂
  have hi₃ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finFourDiagramD_finrank 3, finFourDiagramD_finrank 2])).mpr hs₃
  exact ⟨⟨hi₁, hs₁⟩, ⟨hi₂, hs₂⟩, ⟨hi₃, hs₃⟩⟩

/-- A complex-valued model on the four vertices of the star quiver. -/
noncomputable def complexModel :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ (Fin 4) _ finFourQuiverD :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.mk ℂ (Fin 4) _ finFourQuiverD
    (fun _ => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun {_ _} (_ : @Quiver.Hom (Fin 4) finFourQuiverD _ _) => LinearMap.id)

/-- The comparison between the four-vertex object and its complex-valued model. -/
noncomputable def comparisonWithComplexModel :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ℂ _ (Fin 4) finFourQuiverD
      finFourDiagramD complexModel := by
  obtain ⟨hb₁, hb₂, hb₃⟩ := linearMaps_bijective
  let e₁ := LinearEquiv.ofBijective linearMapToZero hb₁
  let e₂ := LinearEquiv.ofBijective linearMapToOne hb₂
  let e₃ := LinearEquiv.ofBijective linearMapToTwo hb₃
  refine @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData.mk ℂ _ (Fin 4) finFourQuiverD finFourDiagramD
    complexModel (fun v => match v with
      | 0 => e₁.symm
      | 1 => e₂.symm
      | 2 => e₃.symm
      | 3 => LinearEquiv.refl ℂ _) ?_
  intro a b e x
  rcases finFourQuiverD_arrow_cases e with ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
  · cases he
    exact e₁.symm_apply_apply x
  · cases he
    exact e₂.symm_apply_apply x
  · cases he
    exact e₃.symm_apply_apply x

end RepresentationTheory.Quiver.FourVertexStar
