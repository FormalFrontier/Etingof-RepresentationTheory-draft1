import RepresentationTheory.IntegerMatrices
import RepresentationTheory.Quiver.MatrixOrientation
import RepresentationTheory.AuxiliaryQuiverConstructions
import RepresentationTheory.AuxiliaryQuiverRepresentationDimensions
import RepresentationTheory.QuiverRepresentation.VertexCompositionSeries


namespace RepresentationTheory.Quiver.FinFourLinearData

/-- A quiver structure on the four-element vertex type. -/
abbrev finFourQuiverA : Quiver (Fin 4) := RepresentationTheory.Quiver.MatrixOrientation.quiverOfAdjacencyMatrix RepresentationTheory.IntegerMatrices.integerMatrixA
/-- A second quiver structure whose vertices are indexed by `Fin 4`. -/
noncomputable abbrev finFourQuiverB : Quiver (Fin 4) := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin 4) _ finFourQuiverA 0
/-- An additional quiver carried by the type `Fin 4`. -/
noncomputable abbrev finFourQuiverC : Quiver (Fin 4) := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin 4) _ finFourQuiverB 1
/-- A quiver with four finitely indexed vertices. -/
noncomputable abbrev finFourQuiverD : Quiver (Fin 4) := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin 4) _ finFourQuiverC 2
/-- A quiver presentation on `Fin 4` equal to `finFourQuiverA`. -/
noncomputable abbrev finFourQuiverACopy : Quiver (Fin 4) := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin 4) _ finFourQuiverD 3

/-- There is at most one arrow between any ordered pair of vertices in `finFourQuiverB`. -/
local instance finFourQuiverB_hom_subsingleton (a b : Fin 4) :
    Subsingleton (@Quiver.Hom (Fin 4) finFourQuiverB a b) :=
  @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_quiverHom_subsingleton 4 _ finFourQuiverA
    (fun x y => RepresentationTheory.Quiver.MatrixOrientation.quiverOfAdjacencyMatrix_hom_subsingleton RepresentationTheory.IntegerMatrices.integerMatrixA x y) 0 a b

/-- Every hom type of `finFourQuiverC` contains at most one arrow. -/
local instance finFourQuiverC_hom_subsingleton (a b : Fin 4) :
    Subsingleton (@Quiver.Hom (Fin 4) finFourQuiverC a b) :=
  @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_quiverHom_subsingleton 4 _ finFourQuiverB (fun x y => finFourQuiverB_hom_subsingleton x y) 1 a b

/-- Parallel arrows in `finFourQuiverD` are unique whenever they exist. -/
instance finFourQuiverD_hom_subsingleton (a b : Fin 4) :
    Subsingleton (@Quiver.Hom (Fin 4) finFourQuiverD a b) :=
  @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_quiverHom_subsingleton 4 _ finFourQuiverC (fun x y => finFourQuiverC_hom_subsingleton x y) 2 a b

/-- A finite type structure on the auxiliary type attached to vertex zero of `finFourQuiverA`. -/
noncomputable local instance finFourQuiverA_auxFintypeAtZero :
    Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin 4) finFourQuiverA 0) := by
  haveI : ∀ b : Fin 4, Fintype (@Quiver.Hom (Fin 4) finFourQuiverA 0 b) :=
    fun b => @RepresentationTheory.AuxiliaryQuiverConstructions.quiverHomFintypeOfSubsingleton (Fin 4) finFourQuiverA
      (fun x y => RepresentationTheory.Quiver.MatrixOrientation.quiverOfAdjacencyMatrix_hom_subsingleton RepresentationTheory.IntegerMatrices.integerMatrixA x y) 0 b
  exact Sigma.instFintype

/-- A finite type structure on the auxiliary type associated with vertex one of `finFourQuiverB`. -/
noncomputable local instance finFourQuiverB_auxFintypeAtOne :
    Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin 4) finFourQuiverB 1) := by
  haveI : ∀ b : Fin 4, Fintype (@Quiver.Hom (Fin 4) finFourQuiverB 1 b) :=
    fun b => @RepresentationTheory.AuxiliaryQuiverConstructions.quiverHomFintypeOfSubsingleton (Fin 4) finFourQuiverB
      (fun x y => finFourQuiverB_hom_subsingleton x y) 1 b
  exact Sigma.instFintype

/-- A finite type structure for the auxiliary type at vertex two of `finFourQuiverC`. -/
noncomputable local instance finFourQuiverC_auxFintypeAtTwo :
    Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin 4) finFourQuiverC 2) := by
  haveI : ∀ b : Fin 4, Fintype (@Quiver.Hom (Fin 4) finFourQuiverC 2 b) :=
    fun b => @RepresentationTheory.AuxiliaryQuiverConstructions.quiverHomFintypeOfSubsingleton (Fin 4) finFourQuiverC
      (fun x y => finFourQuiverC_hom_subsingleton x y) 2 b
  exact Sigma.instFintype

/-- A finite type structure for the auxiliary type at vertex three of `finFourQuiverD`. -/
noncomputable local instance finFourQuiverD_auxFintypeAtThree :
    Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin 4) finFourQuiverD 3) := by
  haveI : ∀ b : Fin 4, Fintype (@Quiver.Hom (Fin 4) finFourQuiverD 3 b) :=
    fun b => @RepresentationTheory.AuxiliaryQuiverConstructions.quiverHomFintypeOfSubsingleton (Fin 4) finFourQuiverD
      (fun x y => finFourQuiverD_hom_subsingleton x y) 3 b
  exact Sigma.instFintype

private theorem source₀ : @RepresentationTheory.QuiverVertexPredicates.vertexCondition (Fin 4) finFourQuiverA 0 := by
  intro j
  constructor
  rintro ⟨⟨_, hj⟩⟩
  omega

private theorem source₁ : @RepresentationTheory.QuiverVertexPredicates.vertexCondition (Fin 4) finFourQuiverB 1 := by
  intro j
  constructor
  intro e
  change @RepresentationTheory.QuiverVertexReversal.reversedAtHom (Fin 4) _ finFourQuiverA 0 j 1 at e
  by_cases hj : j = 0
  · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne (Fin 4) _ finFourQuiverA 0 j 1 hj
      (by decide : (1 : Fin 4) ≠ 0)] at e
    exact (source₀ 1).false e
  · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne (Fin 4) _ finFourQuiverA 0 j 1 hj
      (by decide : (1 : Fin 4) ≠ 0)] at e
    rcases e with ⟨⟨_, hlt⟩⟩
    omega

private theorem source₂ : @RepresentationTheory.QuiverVertexPredicates.vertexCondition (Fin 4) finFourQuiverC 2 := by
  intro j
  constructor
  intro e
  change @RepresentationTheory.QuiverVertexReversal.reversedAtHom (Fin 4) _ finFourQuiverB 1 j 2 at e
  by_cases hj : j = 1
  · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne (Fin 4) _ finFourQuiverB 1 j 2 hj
      (by decide : (2 : Fin 4) ≠ 1)] at e
    exact (source₁ 2).false e
  · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne (Fin 4) _ finFourQuiverB 1 j 2 hj
      (by decide : (2 : Fin 4) ≠ 1)] at e
    change @RepresentationTheory.QuiverVertexReversal.reversedAtHom (Fin 4) _ finFourQuiverA 0 j 2 at e
    by_cases hj0 : j = 0
    · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne (Fin 4) _ finFourQuiverA 0 j 2 hj0
        (by decide : (2 : Fin 4) ≠ 0)] at e
      exact (source₀ 2).false e
    · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne (Fin 4) _ finFourQuiverA 0 j 2 hj0
        (by decide : (2 : Fin 4) ≠ 0)] at e
      rcases e with ⟨⟨_, hlt⟩⟩
      omega

/-- Vertex three of `finFourQuiverD` satisfies the relevant auxiliary predicate. -/
theorem finFourQuiverD_hasAuxPropertyAtThree : @RepresentationTheory.QuiverVertexPredicates.vertexCondition (Fin 4) finFourQuiverD 3 := by
  intro j
  constructor
  intro e
  change @RepresentationTheory.QuiverVertexReversal.reversedAtHom (Fin 4) _ finFourQuiverC 2 j 3 at e
  by_cases hj : j = 2
  · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne (Fin 4) _ finFourQuiverC 2 j 3 hj
      (by decide : (3 : Fin 4) ≠ 2)] at e
    exact (source₂ 3).false e
  · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne (Fin 4) _ finFourQuiverC 2 j 3 hj
      (by decide : (3 : Fin 4) ≠ 2)] at e
    change @RepresentationTheory.QuiverVertexReversal.reversedAtHom (Fin 4) _ finFourQuiverB 1 j 3 at e
    by_cases hj1 : j = 1
    · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne (Fin 4) _ finFourQuiverB 1 j 3 hj1
        (by decide : (3 : Fin 4) ≠ 1)] at e
      exact (source₁ 3).false e
    · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne (Fin 4) _ finFourQuiverB 1 j 3 hj1
        (by decide : (3 : Fin 4) ≠ 1)] at e
      change @RepresentationTheory.QuiverVertexReversal.reversedAtHom (Fin 4) _ finFourQuiverA 0 j 3 at e
      by_cases hj0 : j = 0
      · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne (Fin 4) _ finFourQuiverA 0 j 3 hj0
          (by decide : (3 : Fin 4) ≠ 0)] at e
        exact (source₀ 3).false e
      · rw [@RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne (Fin 4) _ finFourQuiverA 0 j 3 hj0
          (by decide : (3 : Fin 4) ≠ 0)] at e
        rcases e with ⟨⟨_, hlt⟩⟩
        omega

/-- An auxiliary complex-valued construction indexed by the vertices of `finFourQuiverA`. -/
noncomputable abbrev finFourDiagramA : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ (Fin 4) _ finFourQuiverA :=
  RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation ℂ 3

/-- An auxiliary complex-valued construction associated with `finFourQuiverB`. -/
noncomputable abbrev finFourDiagramB : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ (Fin 4) _ finFourQuiverB :=
  @RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation ℂ _ (Fin 4) _ finFourQuiverA 0 source₀ finFourDiagramA finFourQuiverA_auxFintypeAtZero

/-- An auxiliary complex-valued construction associated with `finFourQuiverC`. -/
noncomputable abbrev finFourDiagramC : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ (Fin 4) _ finFourQuiverC :=
  @RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation ℂ _ (Fin 4) _ finFourQuiverB 1 source₁ finFourDiagramB finFourQuiverB_auxFintypeAtOne

/-- An auxiliary complex-valued construction associated with `finFourQuiverD`. -/
noncomputable abbrev finFourDiagramD : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ (Fin 4) _ finFourQuiverD :=
  @RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation ℂ _ (Fin 4) _ finFourQuiverC 2 source₂ finFourDiagramC finFourQuiverC_auxFintypeAtTwo

/-- An auxiliary complex-valued construction based on `finFourQuiverACopy`. -/
noncomputable abbrev finFourDiagramACopy : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ (Fin 4) _ finFourQuiverACopy :=
  @RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation ℂ _ (Fin 4) _ finFourQuiverD 3 finFourQuiverD_hasAuxPropertyAtThree finFourDiagramD finFourQuiverD_auxFintypeAtThree

private lemma reflected_free_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ Q)
    [∀ v, Module.Free ℂ (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (v : Q) (hv : v ≠ i) :
    Module.Free ℂ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) v) :=
  Module.Free.of_equiv (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv).symm

private lemma reflected_finite_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ Q)
    [∀ v, Module.Finite ℂ (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (v : Q) (hv : v ≠ i) :
    Module.Finite ℂ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) v) :=
  Module.Finite.equiv (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv).symm

set_option linter.unusedFintypeInType false in
private lemma reflected_free_eq
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ Q)
    [∀ v, Module.Free ℂ (ρ.obj v)] [∀ v, Module.Finite ℂ (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    Module.Free ℂ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) i) := by
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := ℂ)
  exact Module.Free.of_equiv (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).symm

set_option linter.unusedFintypeInType false in
private lemma reflected_finite_eq
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ Q)
    [∀ v, Module.Free ℂ (ρ.obj v)] [∀ v, Module.Finite ℂ (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    Module.Finite ℂ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) i) := by
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := ℂ)
  exact Module.Finite.equiv (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).symm

/-- The complex module attached to each vertex of `finFourDiagramB` is free. -/
noncomputable local instance finFourDiagramB_free (v : Fin 4) : Module.Free ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverB finFourDiagramB v) := by
  by_cases hv : v = 0
  · subst v
    exact @reflected_free_eq (Fin 4) _ finFourQuiverA 0 source₀ finFourDiagramA
      (fun w => inferInstance) (fun w => inferInstance) finFourQuiverA_auxFintypeAtZero
  · exact @reflected_free_ne (Fin 4) _ finFourQuiverA 0 source₀ finFourDiagramA
      (fun w => inferInstance) finFourQuiverA_auxFintypeAtZero v hv

/-- Every vertex object of `finFourDiagramB` is finite as a complex module. -/
noncomputable local instance finFourDiagramB_finite (v : Fin 4) : Module.Finite ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverB finFourDiagramB v) := by
  by_cases hv : v = 0
  · subst v
    exact @reflected_finite_eq (Fin 4) _ finFourQuiverA 0 source₀ finFourDiagramA
      (fun w => inferInstance) (fun w => inferInstance) finFourQuiverA_auxFintypeAtZero
  · exact @reflected_finite_ne (Fin 4) _ finFourQuiverA 0 source₀ finFourDiagramA
      (fun w => inferInstance) finFourQuiverA_auxFintypeAtZero v hv

/-- At every vertex, `finFourDiagramC` supplies a free module over the complex numbers. -/
noncomputable local instance finFourDiagramC_free (v : Fin 4) : Module.Free ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverC finFourDiagramC v) := by
  by_cases hv : v = 1
  · subst v
    exact @reflected_free_eq (Fin 4) _ finFourQuiverB 1 source₁ finFourDiagramB
      (fun w => finFourDiagramB_free w) (fun w => finFourDiagramB_finite w) finFourQuiverB_auxFintypeAtOne
  · exact @reflected_free_ne (Fin 4) _ finFourQuiverB 1 source₁ finFourDiagramB
      (fun w => finFourDiagramB_free w) finFourQuiverB_auxFintypeAtOne v hv

/-- Each vertex object belonging to `finFourDiagramC` is a finite complex module. -/
noncomputable local instance finFourDiagramC_finite (v : Fin 4) : Module.Finite ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverC finFourDiagramC v) := by
  by_cases hv : v = 1
  · subst v
    exact @reflected_finite_eq (Fin 4) _ finFourQuiverB 1 source₁ finFourDiagramB
      (fun w => finFourDiagramB_free w) (fun w => finFourDiagramB_finite w) finFourQuiverB_auxFintypeAtOne
  · exact @reflected_finite_ne (Fin 4) _ finFourQuiverB 1 source₁ finFourDiagramB
      (fun w => finFourDiagramB_finite w) finFourQuiverB_auxFintypeAtOne v hv

/-- Every complex module occurring at a vertex of `finFourDiagramD` is free. -/
noncomputable instance finFourDiagramD_free (v : Fin 4) : Module.Free ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD v) := by
  by_cases hv : v = 2
  · subst v
    exact @reflected_free_eq (Fin 4) _ finFourQuiverC 2 source₂ finFourDiagramC
      (fun w => finFourDiagramC_free w) (fun w => finFourDiagramC_finite w) finFourQuiverC_auxFintypeAtTwo
  · exact @reflected_free_ne (Fin 4) _ finFourQuiverC 2 source₂ finFourDiagramC
      (fun w => finFourDiagramC_free w) finFourQuiverC_auxFintypeAtTwo v hv

/-- All vertex objects of `finFourDiagramD` are finite as modules over the complex numbers. -/
noncomputable instance finFourDiagramD_finite (v : Fin 4) : Module.Finite ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD v) := by
  by_cases hv : v = 2
  · subst v
    exact @reflected_finite_eq (Fin 4) _ finFourQuiverC 2 source₂ finFourDiagramC
      (fun w => finFourDiagramC_free w) (fun w => finFourDiagramC_finite w) finFourQuiverC_auxFintypeAtTwo
  · exact @reflected_finite_ne (Fin 4) _ finFourQuiverC 2 source₂ finFourDiagramC
      (fun w => finFourDiagramC_finite w) finFourQuiverC_auxFintypeAtTwo v hv

/-- The complex modules at the vertices of `finFourDiagramACopy` are free. -/
noncomputable local instance finFourDiagramACopy_free (v : Fin 4) : Module.Free ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverACopy finFourDiagramACopy v) := by
  by_cases hv : v = 3
  · subst v
    exact @reflected_free_eq (Fin 4) _ finFourQuiverD 3 finFourQuiverD_hasAuxPropertyAtThree finFourDiagramD
      (fun w => finFourDiagramD_free w) (fun w => finFourDiagramD_finite w) finFourQuiverD_auxFintypeAtThree
  · exact @reflected_free_ne (Fin 4) _ finFourQuiverD 3 finFourQuiverD_hasAuxPropertyAtThree finFourDiagramD
      (fun w => finFourDiagramD_free w) finFourQuiverD_auxFintypeAtThree v hv

/-- Each vertex object of `finFourDiagramACopy` is finite over the complex numbers. -/
noncomputable local instance finFourDiagramACopy_finite (v : Fin 4) : Module.Finite ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverACopy finFourDiagramACopy v) := by
  by_cases hv : v = 3
  · subst v
    exact @reflected_finite_eq (Fin 4) _ finFourQuiverD 3 finFourQuiverD_hasAuxPropertyAtThree finFourDiagramD
      (fun w => finFourDiagramD_free w) (fun w => finFourDiagramD_finite w) finFourQuiverD_auxFintypeAtThree
  · exact @reflected_finite_ne (Fin 4) _ finFourQuiverD 3 finFourQuiverD_hasAuxPropertyAtThree finFourDiagramD
      (fun w => finFourDiagramD_finite w) finFourQuiverD_auxFintypeAtThree v hv

private lemma reflectionDim_eq_cartan
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hsymm : adj.IsSymm) (hzeroone : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    {Q : Quiver (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [hSS : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (p : Fin n) (hp : @RepresentationTheory.QuiverVertexPredicates.vertexCondition (Fin n) Q p)
    (d : Fin n → ℤ) [hArrows : Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q p)] :
    RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt
        (fun (a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q p) => a.1) p d =
      RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) p d := by
  haveI : ∀ (a b : Fin n), Fintype (@Quiver.Hom (Fin n) Q a b) :=
    fun a b => RepresentationTheory.AuxiliaryQuiverConstructions.quiverHomFintypeOfSubsingleton a b
  ext v
  unfold RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform
  by_cases hv : v = p
  · subst v
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one,
      if_true]
    have hdot : dotProduct d
        ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec (Pi.single p 1)) =
          2 * d p - ∑ j : Fin n, adj p j * d j := by
      simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp only [RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp_rw [mul_comm (d _) (adj _ _)]
      simp_rw [show ∀ x, adj x p = adj p x from fun x => by
        exact congr_fun (congr_fun hsymm p) x]
      ring
    have hcard : ∀ j : Fin n,
        (Fintype.card (@Quiver.Hom (Fin n) Q p j) : ℤ) = adj p j := by
      intro j
      rcases hzeroone p j with h0 | h1
      · haveI : IsEmpty (@Quiver.Hom (Fin n) Q p j) := hOrient.1 p j (by omega)
        rw [Fintype.card_eq_zero]
        omega
      · rcases hOrient.2.1 p j h1 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
        · haveI : Unique (@Quiver.Hom (Fin n) Q p j) :=
            { default := e, uniq := fun a => Subsingleton.elim a e }
          simp [Fintype.card_unique, h1]
        · exact ((hp j).false e).elim
    have hsum : (∑ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q p, d a.fst) =
        ∑ j : Fin n, adj p j * d j := by
      letI sigmaFT : Fintype (Σ j : Fin n, @Quiver.Hom (Fin n) Q p j) := Sigma.instFintype
      have h_unfold : (∑ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q p, d a.fst) =
          @Finset.sum _ _ _ (@Finset.univ _ sigmaFT) (fun a => d a.fst) := by
        apply Finset.sum_congr
        · ext x
          exact iff_of_true (Finset.mem_univ x) (@Finset.mem_univ _ sigmaFT x)
        · intros
          rfl
      rw [h_unfold, Fintype.sum_sigma]
      congr 1
      ext j
      change (∑ _ : @Quiver.Hom (Fin n) Q p j, d j) = adj p j * d j
      rw [Finset.sum_const, nsmul_eq_mul]
      have h : (Finset.univ (α := @Quiver.Hom (Fin n) Q p j)).card = Fintype.card _ := rfl
      rw [h, show (Fintype.card (@Quiver.Hom (Fin n) Q p j) : ℤ) = adj p j from hcard j]
    have hsame : ∀ (inst1 inst2 : Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q p)),
        @Finset.sum _ _ _ (@Finset.univ _ inst1) (fun x => d x.fst) =
          @Finset.sum _ _ _ (@Finset.univ _ inst2) (fun x => d x.fst) := by
      intro i1 i2
      apply Finset.sum_congr
      · ext x
        exact iff_of_true (@Finset.mem_univ _ i1 x) (@Finset.mem_univ _ i2 x)
      · intros
        rfl
    linarith [hsame hArrows inferInstance, hsum, hdot]
  · simp only [hv, ite_false, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_zero, sub_zero]

private theorem adj_symm : RepresentationTheory.IntegerMatrices.integerMatrixA.IsSymm := by decide
private theorem adj_diag : ∀ i, RepresentationTheory.IntegerMatrices.integerMatrixA i i = 0 := by decide
private theorem adj_zero_one : ∀ i j, RepresentationTheory.IntegerMatrices.integerMatrixA i j = 0 ∨ RepresentationTheory.IntegerMatrices.integerMatrixA i j = 1 := by
  decide

private theorem orient₀ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation finFourQuiverA RepresentationTheory.IntegerMatrices.integerMatrixA :=
  RepresentationTheory.Quiver.MatrixOrientation.quiverOfAdjacencyMatrix_isMatrixOrientation RepresentationTheory.IntegerMatrices.integerMatrixA adj_symm adj_diag

private theorem orient₁ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation finFourQuiverB RepresentationTheory.IntegerMatrices.integerMatrixA :=
  RepresentationTheory.Quiver.MatrixOrientation.isMatrixOrientation_vertexReorientation adj_symm adj_diag orient₀ 0

private theorem orient₂ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation finFourQuiverC RepresentationTheory.IntegerMatrices.integerMatrixA :=
  RepresentationTheory.Quiver.MatrixOrientation.isMatrixOrientation_vertexReorientation adj_symm adj_diag orient₁ 1

/-- The supplied auxiliary object satisfies the designated predicate relative to `finFourQuiverD`. -/
theorem finFourQuiverD_hasAuxProperty : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation finFourQuiverD RepresentationTheory.IntegerMatrices.integerMatrixA :=
  RepresentationTheory.Quiver.MatrixOrientation.isMatrixOrientation_vertexReorientation adj_symm adj_diag orient₂ 2

private theorem sourceMap₀_injective : Function.Injective
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.outgoingDirectSumMap ℂ _ (Fin 4) finFourQuiverA finFourDiagramA 0 finFourQuiverA_auxFintypeAtZero) := by
  intro x y _
  change (Fin 0 → ℂ) at x y
  exact funext fun z => z.elim0

private theorem sourceMap₁_injective : Function.Injective
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.outgoingDirectSumMap ℂ _ (Fin 4) finFourQuiverB finFourDiagramB 1 finFourQuiverB_auxFintypeAtOne) := by
  intro x y _
  apply (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe ℂ _ (Fin 4) _ finFourQuiverA 0 source₀ finFourDiagramA
    finFourQuiverA_auxFintypeAtZero 1 (by decide)).injective
  have hsub : Subsingleton
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramA 1) := by
    change Subsingleton (Fin 0 → ℂ)
    infer_instance
  exact hsub.elim _ _

private theorem sourceMap₂_injective : Function.Injective
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.outgoingDirectSumMap ℂ _ (Fin 4) finFourQuiverC finFourDiagramC 2 finFourQuiverC_auxFintypeAtTwo) := by
  intro x y _
  apply (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe ℂ _ (Fin 4) _ finFourQuiverB 1 source₁ finFourDiagramB
    finFourQuiverB_auxFintypeAtOne 2 (by decide)).injective
  apply (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe ℂ _ (Fin 4) _ finFourQuiverA 0 source₀ finFourDiagramA
    finFourQuiverA_auxFintypeAtZero 2 (by decide)).injective
  have hsub : Subsingleton
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramA 2) := by
    change Subsingleton (Fin 0 → ℂ)
    infer_instance
  exact hsub.elim _ _

private theorem V₀_dimensionVector (v : Fin 4) :
    (Module.finrank ℂ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramA v) : ℤ) =
      RepresentationTheory.IntegerMatrices.integerVector v := by
  change (Module.finrank ℂ (Fin (if v = 3 then 1 else 0) → ℂ) : ℤ) = _
  rw [Module.finrank_pi_fintype]
  by_cases hv : v = 3
  · subst v
    simp [RepresentationTheory.IntegerMatrices.integerVector, RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue]
  · simp [RepresentationTheory.IntegerMatrices.integerVector, RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, hv]

/-- The vertexwise numerical invariant of `finFourDiagramB` has values one, zero, zero, and one. -/
theorem finFourDiagramB_invariant_eq (v : Fin 4) :
    ((@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryNat ℂ _ (Fin 4) finFourQuiverB finFourDiagramB v : ℕ) : ℤ) =
      ![1, 0, 0, 1] v := by
  have h := @RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_injective ℂ _ (Fin 4) _ finFourQuiverA 0 source₀ finFourDiagramA
    (fun w => inferInstance) (fun w => inferInstance) finFourQuiverA_auxFintypeAtZero sourceMap₀_injective v
  rw [reflectionDim_eq_cartan adj_symm adj_zero_one orient₀ 0 source₀] at h
  have hd : (fun w => (Module.finrank ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramA w) : ℤ)) = RepresentationTheory.IntegerMatrices.integerVector := by
    ext w
    exact V₀_dimensionVector w
  rw [hd] at h
  have href : RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform 4
      (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform 4 RepresentationTheory.IntegerMatrices.integerMatrixA) 0 RepresentationTheory.IntegerMatrices.integerVector =
      ![1, 0, 0, 1] := by decide
  rw [href] at h
  exact h

/-- The vertexwise numerical invariant of `finFourDiagramC` has values one, one, zero, and one. -/
theorem finFourDiagramC_invariant_eq (v : Fin 4) :
    ((@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryNat ℂ _ (Fin 4) finFourQuiverC finFourDiagramC v : ℕ) : ℤ) =
      ![1, 1, 0, 1] v := by
  have h := @RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_injective ℂ _ (Fin 4) _ finFourQuiverB 1 source₁ finFourDiagramB
    (fun w => finFourDiagramB_free w) (fun w => finFourDiagramB_finite w) finFourQuiverB_auxFintypeAtOne sourceMap₁_injective v
  rw [reflectionDim_eq_cartan adj_symm adj_zero_one orient₁ 1 source₁] at h
  have hd : (fun w => (Module.finrank ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverB finFourDiagramB w) : ℤ)) = ![1, 0, 0, 1] := by
    ext w
    exact finFourDiagramB_invariant_eq w
  rw [hd] at h
  have href : RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform 4
      (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform 4 RepresentationTheory.IntegerMatrices.integerMatrixA) 1 ![1, 0, 0, 1] =
      ![1, 1, 0, 1] := by decide
  rw [href] at h
  exact h

/-- The numerical invariant of `finFourDiagramD` is one at each of its four vertices. -/
theorem finFourDiagramD_invariant_eq (v : Fin 4) :
    ((@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryNat ℂ _ (Fin 4) finFourQuiverD finFourDiagramD v : ℕ) : ℤ) =
      ![1, 1, 1, 1] v := by
  have h := @RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_injective ℂ _ (Fin 4) _ finFourQuiverC 2 source₂ finFourDiagramC
    (fun w => finFourDiagramC_free w) (fun w => finFourDiagramC_finite w) finFourQuiverC_auxFintypeAtTwo sourceMap₂_injective v
  rw [reflectionDim_eq_cartan adj_symm adj_zero_one orient₂ 2 source₂] at h
  have hd : (fun w => (Module.finrank ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverC finFourDiagramC w) : ℤ)) = ![1, 1, 0, 1] := by
    ext w
    exact finFourDiagramC_invariant_eq w
  rw [hd] at h
  have href : RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform 4
      (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform 4 RepresentationTheory.IntegerMatrices.integerMatrixA) 2 ![1, 1, 0, 1] =
      ![1, 1, 1, 1] := by decide
  rw [href] at h
  exact h

set_option maxHeartbeats 400000 in
private theorem simpleRepresentation_indecomposable_local
    (k : Type*) [Field k] {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} :
    (RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).AuxiliaryCondition := by
  refine ⟨⟨p, ?_⟩, fun W₁ W₂ _ _ hcompl => ?_⟩
  · change Nontrivial (Fin (if p = p then 1 else 0) → k)
    simp only [ite_true]
    exact Pi.nontrivial
  · have hbot : ∀ v, v ≠ p → W₁ v = ⊥ ∧ W₂ v = ⊥ := by
      intro v hv
      have hempty : IsEmpty (Fin (if v = p then 1 else 0)) := by
        simp only [hv, ite_false]
        exact Fin.isEmpty
      haveI : Subsingleton ((RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).obj v) :=
        show Subsingleton (Fin (if v = p then 1 else 0) → k) from inferInstance
      exact ⟨Submodule.eq_bot_of_subsingleton, Submodule.eq_bot_of_subsingleton⟩
    have hdim : Module.finrank k (Fin (if p = p then 1 else 0) → k) = 1 := by simp
    have hcompl_p := hcompl p
    have hcentre : W₁ p = ⊥ ∨ W₂ p = ⊥ := by
      letI : ∀ v, AddCommGroup ((RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).obj v) :=
        fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
      by_contra h
      push Not at h
      obtain ⟨h₁, h₂⟩ := h
      have hr₁ := Submodule.one_le_finrank_iff.mpr h₁
      have hr₂ := Submodule.one_le_finrank_iff.mpr h₂
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq (W₁ p) (W₂ p)
      rw [hcompl_p.sup_eq_top, hcompl_p.inf_eq_bot, finrank_top, finrank_bot] at hsum
      have hdim' : Module.finrank k
          ((RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).obj p) = 1 := hdim
      omega
    rcases hcentre with h | h
    · left
      intro v
      by_cases hv : v = p
      · subst v
        exact h
      · exact (hbot v hv).1
    · right
      intro v
      by_cases hv : v = p
      · subst v
        exact h
      · exact (hbot v hv).2

private theorem V₀_indecomposable :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition ℂ _ (Fin 4) finFourQuiverA finFourDiagramA :=
  simpleRepresentation_indecomposable_local ℂ 3

/-- The construction `finFourDiagramB` satisfies its designated auxiliary predicate. -/
theorem finFourDiagramB_hasProperty :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition ℂ _ (Fin 4) finFourQuiverB finFourDiagramB := by
  rcases @RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary_of_fintype ℂ _ (Fin 4) _ finFourQuiverA 0 source₀ finFourDiagramA
      (fun w => inferInstance) (fun w => inferInstance) finFourQuiverA_auxFintypeAtZero V₀_indecomposable with h | hz
  · exact h
  · exfalso
    have hsub₁ := hz 3
    let e := @RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe ℂ _ (Fin 4) _ finFourQuiverA 0 source₀ finFourDiagramA
      finFourQuiverA_auxFintypeAtZero 3 (by decide)
    have hsub₀ : Subsingleton
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramA 3) :=
      ⟨fun x y => e.symm.injective (hsub₁.elim _ _)⟩
    letI : Nontrivial (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramA 3) := by
      change Nontrivial (Fin 1 → ℂ)
      infer_instance
    obtain ⟨x, hx⟩ := exists_ne (0 : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramA 3)
    exact hx (hsub₀.elim x 0)

/-- The auxiliary predicate for `finFourDiagramC` is satisfied. -/
theorem finFourDiagramC_hasProperty :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition ℂ _ (Fin 4) finFourQuiverC finFourDiagramC := by
  rcases @RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary_of_fintype ℂ _ (Fin 4) _ finFourQuiverB 1 source₁ finFourDiagramB
      (fun w => finFourDiagramB_free w) (fun w => finFourDiagramB_finite w) finFourQuiverB_auxFintypeAtOne finFourDiagramB_hasProperty with h | hz
  · exact h
  · exfalso
    have hsub₂ := hz 3
    let e₁ := @RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe ℂ _ (Fin 4) _ finFourQuiverB 1 source₁ finFourDiagramB
      finFourQuiverB_auxFintypeAtOne 3 (by decide)
    let e₀ := @RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe ℂ _ (Fin 4) _ finFourQuiverA 0 source₀ finFourDiagramA
      finFourQuiverA_auxFintypeAtZero 3 (by decide)
    have hsub₀ : Subsingleton
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramA 3) :=
      ⟨fun x y => e₀.symm.injective (e₁.symm.injective (hsub₂.elim _ _))⟩
    letI : Nontrivial (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramA 3) := by
      change Nontrivial (Fin 1 → ℂ)
      infer_instance
    obtain ⟨x, hx⟩ := exists_ne (0 : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramA 3)
    exact hx (hsub₀.elim x 0)

/-- The designated auxiliary predicate holds for `finFourDiagramD`. -/
theorem finFourDiagramD_hasProperty :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition ℂ _ (Fin 4) finFourQuiverD finFourDiagramD := by
  rcases @RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary_of_fintype ℂ _ (Fin 4) _ finFourQuiverC 2 source₂ finFourDiagramC
      (fun w => finFourDiagramC_free w) (fun w => finFourDiagramC_finite w) finFourQuiverC_auxFintypeAtTwo finFourDiagramC_hasProperty with h | hz
  · exact h
  · exfalso
    have hdim := finFourDiagramD_invariant_eq 3
    letI : Subsingleton
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3) := hz 3
    have hzero : Module.finrank ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3) = 0 :=
      Module.finrank_zero_of_subsingleton
    unfold RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryNat at hdim
    have hone : Module.finrank ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3) = 1 := by
      have hdim' : (Module.finrank ℂ
          (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 3) : ℤ) = 1 := by
        simpa using hdim
      exact_mod_cast hdim'
    omega

private theorem sourceMap₃_injective : Function.Injective
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.outgoingDirectSumMap ℂ _ (Fin 4) finFourQuiverD finFourDiagramD 3 finFourQuiverD_auxFintypeAtThree) := by
  rcases @RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrInjective ℂ _ (Fin 4) _ finFourQuiverD finFourDiagramD 3
      (fun w => finFourDiagramD_free w) (fun w => finFourDiagramD_finite w) finFourQuiverD_auxFintypeAtThree finFourQuiverD_hasAuxPropertyAtThree finFourDiagramD_hasProperty with
    hsimple | hinj
  · have hzero := hsimple.2 0 (by decide)
    have hone := finFourDiagramD_invariant_eq 0
    unfold RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryNat at hone
    norm_num at hone
    have hone' : Module.finrank ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD 0) = 1 := by
      exact_mod_cast hone
    omega
  · exact hinj

/-- The vertexwise numerical invariant of `finFourDiagramACopy` has values one, one, one, and two. -/
theorem finFourDiagramACopy_invariant_eq (v : Fin 4) :
    ((@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryNat ℂ _ (Fin 4) finFourQuiverACopy finFourDiagramACopy v : ℕ) : ℤ) =
      ![1, 1, 1, 2] v := by
  have h := @RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_injective ℂ _ (Fin 4) _ finFourQuiverD 3 finFourQuiverD_hasAuxPropertyAtThree finFourDiagramD
    (fun w => finFourDiagramD_free w) (fun w => finFourDiagramD_finite w) finFourQuiverD_auxFintypeAtThree sourceMap₃_injective v
  rw [reflectionDim_eq_cartan adj_symm adj_zero_one finFourQuiverD_hasAuxProperty 3 finFourQuiverD_hasAuxPropertyAtThree] at h
  have hd : (fun w => (Module.finrank ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverD finFourDiagramD w) : ℤ)) = ![1, 1, 1, 1] := by
    ext w
    exact finFourDiagramD_invariant_eq w
  rw [hd] at h
  have href : RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform 4
      (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform 4 RepresentationTheory.IntegerMatrices.integerMatrixA) 3 ![1, 1, 1, 1] =
      ![1, 1, 1, 2] := by decide
  rw [href] at h
  exact h

/-- The construction `finFourDiagramACopy` fulfills its associated auxiliary predicate. -/
theorem finFourDiagramACopy_hasProperty :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition ℂ _ (Fin 4) finFourQuiverACopy finFourDiagramACopy := by
  rcases @RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary_of_fintype ℂ _ (Fin 4) _ finFourQuiverD 3 finFourQuiverD_hasAuxPropertyAtThree finFourDiagramD
      (fun w => finFourDiagramD_free w) (fun w => finFourDiagramD_finite w) finFourQuiverD_auxFintypeAtThree finFourDiagramD_hasProperty with h | hz
  · exact h
  · exfalso
    have hdim := finFourDiagramACopy_invariant_eq 3
    letI : Subsingleton
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverACopy finFourDiagramACopy 3) := hz 3
    have hzero : Module.finrank ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverACopy finFourDiagramACopy 3) = 0 :=
      Module.finrank_zero_of_subsingleton
    unfold RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryNat at hdim
    have htwo : Module.finrank ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverACopy finFourDiagramACopy 3) = 2 := by
      have hdim' : (Module.finrank ℂ
          (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverACopy finFourDiagramACopy 3) : ℤ) = 2 := by
        simpa using hdim
      exact_mod_cast hdim'
    omega

/-- The copied quiver presentation agrees with `finFourQuiverA`. -/
theorem finFourQuiverACopy_eq : finFourQuiverACopy = finFourQuiverA := by
  change RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryListMap finFourQuiverA [0, 1, 2, 3] = finFourQuiverA
  apply RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryListMap_eq_self_of_perm
  decide

private theorem transport_finrank
    {inst₁ inst₂ : Quiver (Fin 4)} (h : inst₁ = inst₂)
    (X : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ (Fin 4) _ inst₁) (v : Fin 4) :
    Module.finrank ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ inst₂ (h ▸ X) v) =
      Module.finrank ℂ
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ inst₁ X v) := by
  cases h
  rfl

private theorem transport_free
    {inst₁ inst₂ : Quiver (Fin 4)} (h : inst₁ = inst₂)
    (X : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ (Fin 4) _ inst₁)
    (hfree : ∀ v, Module.Free ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ inst₁ X v)) (v : Fin 4) :
    Module.Free ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ inst₂ (h ▸ X) v) := by
  cases h
  exact hfree v

private theorem transport_finite
    {inst₁ inst₂ : Quiver (Fin 4)} (h : inst₁ = inst₂)
    (X : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ (Fin 4) _ inst₁)
    (hfinite : ∀ v, Module.Finite ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ inst₁ X v)) (v : Fin 4) :
    Module.Finite ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ inst₂ (h ▸ X) v) := by
  cases h
  exact hfinite v

private theorem transport_indecomposable
    {inst₁ inst₂ : Quiver (Fin 4)} (h : inst₁ = inst₂)
    (X : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ (Fin 4) _ inst₁)
    (hind : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition ℂ _ (Fin 4) inst₁ X) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition ℂ _ (Fin 4) inst₂ (h ▸ X) := by
  cases h
  exact hind

/-- Another auxiliary complex-valued construction associated with `finFourQuiverA`. -/
noncomputable abbrev finFourDiagramAAlt :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram ℂ (Fin 4) _ finFourQuiverA := finFourQuiverACopy_eq ▸ finFourDiagramACopy

/-- Each vertex object in `finFourDiagramAAlt` is free as a module over the complex numbers. -/
noncomputable instance finFourDiagramAAlt_free (v : Fin 4) : Module.Free ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramAAlt v) :=
  transport_free finFourQuiverACopy_eq finFourDiagramACopy (fun w => finFourDiagramACopy_free w) v

/-- Every vertex object in `finFourDiagramAAlt` is a finite complex module. -/
noncomputable instance finFourDiagramAAlt_finite (v : Fin 4) : Module.Finite ℂ
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramAAlt v) :=
  transport_finite finFourQuiverACopy_eq finFourDiagramACopy (fun w => finFourDiagramACopy_finite w) v

/-- The complex finranks of `finFourDiagramAAlt` at its vertices are one, one, one, and two. -/
theorem finFourDiagramAAlt_finrank_eq (v : Fin 4) :
    (Module.finrank ℂ
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj ℂ (Fin 4) _ finFourQuiverA finFourDiagramAAlt v) : ℤ) =
      ![1, 1, 1, 2] v := by
  rw [transport_finrank finFourQuiverACopy_eq finFourDiagramACopy v]
  exact finFourDiagramACopy_invariant_eq v

/-- The auxiliary predicate associated with `finFourDiagramAAlt` holds. -/
theorem finFourDiagramAAlt_hasProperty :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition ℂ _ (Fin 4) finFourQuiverA
      finFourDiagramAAlt := by
  exact transport_indecomposable finFourQuiverACopy_eq finFourDiagramACopy finFourDiagramACopy_hasProperty

end RepresentationTheory.Quiver.FinFourLinearData
