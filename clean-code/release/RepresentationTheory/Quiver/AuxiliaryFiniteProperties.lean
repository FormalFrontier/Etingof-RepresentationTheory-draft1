/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.CategoryTheory.QuiverLinearMaps
import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.IntegerMatrixVectorPredicates
import RepresentationTheory.QuiverRepresentation.Auxiliary
import RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion
import RepresentationTheory.Quiver.DimensionVectorClassification
import RepresentationTheory.AuxiliaryQuiverConstructions
import RepresentationTheory.Quiver.FiniteOrbits
import RepresentationTheory.Quiver.FiniteOrbitDimensionBounds
import RepresentationTheory.Quiver.AdjacencyQuadraticForm
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Quiver.AuxiliaryFiniteProperties

/-- An auxiliary type associated with a quiver on a finite vertex type over a commutative
semiring. -/
@[source_ref "Chapter2/Discussion_after_Theorem2.1.1" (role := supporting)]
abbrev AuxiliaryQuiverType (k : Type) [CommSemiring k] (n : ℕ) [Quiver.{0} (Fin n)] :=
  RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{0, 0, 0, 0}
    k (Fin n)

/-- An auxiliary proposition associated with a finite quiver over a field. -/
@[source_ref "Chapter2/Discussion_after_Theorem2.1.1/Derived4" (role := supporting)]
def AuxiliaryQuiverProperty (k : Type) [Field k] (n : ℕ)
    [Quiver.{0} (Fin n)] : Prop :=
  ∃ (m : ℕ) (reps : Fin m → AuxiliaryQuiverType k n),
    (∀ i, ∀ v, Module.Finite k ((reps i).obj v)) ∧
    (∀ i, (reps i).AuxiliaryCondition) ∧
    (∀ (ρ : AuxiliaryQuiverType k n),
      (∀ v, Module.Finite k (ρ.obj v)) →
      ρ.AuxiliaryCondition →
      ∃ i, Nonempty
        (RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverEquivData
          k (Fin n) ρ (reps i)))

/-- An auxiliary integer matrix associated with a finite quiver having decidable arrow
existence. -/
noncomputable def auxiliaryMatrix (n : ℕ) [Quiver.{0} (Fin n)]
    [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))] :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i ≠ j ∧ (Nonempty (i ⟶ j) ∨ Nonempty (j ⟶ i)) then 1 else 0

/-- An auxiliary proposition determined by a finite quiver with decidable arrow existence. -/
def AuxiliaryQuiverCondition (n : ℕ) [Quiver.{0} (Fin n)]
    [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))] : Prop :=
  ∀ i j : Fin n, ∃ path : List (Fin n),
    path.head? = some i ∧ path.getLast? = some j ∧
    ∀ k, (h : k + 1 < path.length) →
      (auxiliaryMatrix n)
        (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1

variable {n : ℕ} [Quiver.{0} (Fin n)] [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]

/-- The auxiliary matrix is symmetric. -/
lemma auxiliaryMatrix_isSymm : (auxiliaryMatrix n).IsSymm := by
  ext i j
  simp only [auxiliaryMatrix, Matrix.transpose_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp only [hij, Ne.symm hij, ne_eq, not_false_eq_true, true_and, Or.comm]

/-- Every diagonal entry of the auxiliary matrix is zero. -/
lemma auxiliaryMatrix_diagonal (i : Fin n) : auxiliaryMatrix n i i = 0 := by
  simp [auxiliaryMatrix]

/-- Every entry of the auxiliary matrix is either zero or one. -/
lemma auxiliaryMatrix_entry_eq_zero_or_one (i j : Fin n) :
    auxiliaryMatrix n i j = 0 ∨ auxiliaryMatrix n i j = 1 := by
  simp only [auxiliaryMatrix]
  split <;> simp

omit [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))] in
/-- Under the auxiliary quiver property, the functions realized by objects with finite vertex
modules, the displayed auxiliary condition, and the specified vertexwise linear equivalences form
a finite set. -/
lemma AuxiliaryQuiverProperty.finite_auxiliary_dimension_functions (k : Type) [Field k]
    (hfrt : AuxiliaryQuiverProperty k n) :
    Set.Finite
      {d : Fin n → ℕ |
        ∃ (V : AuxiliaryQuiverType k n),
          (∀ v, Module.Finite k (V.obj v)) ∧
          V.AuxiliaryCondition ∧ ∀ v, Nonempty (V.obj v ≃ₗ[k] (Fin (d v) → k))} := by
  obtain ⟨m, reps, hfin, hindec, hcover⟩ := hfrt
  apply Set.Finite.subset (Set.finite_range (fun i v => Module.finrank k ((reps i).obj v)))
  intro d ⟨V, hV_fin, hV_indec, hV_equiv⟩
  simp only [Set.mem_range]
  obtain ⟨i, ⟨e⟩⟩ := hcover V hV_fin hV_indec
  use i
  ext v
  have h1 : Module.finrank k (V.obj v) = d v := by
    haveI : Module.Free k (V.obj v) := Module.Free.of_equiv (hV_equiv v).some.symm
    rw [(hV_equiv v).some.finrank_eq, Module.finrank_fin_fun]
  have h2 : Module.finrank k (V.obj v) = Module.finrank k ((reps i).obj v) :=
    (e.app v).finrank_eq
  linarith

/-- An auxiliary map from the displayed source type to the displayed target type. -/
noncomputable def _root_.RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData.auxiliaryMap
    {k : Type*} [CommSemiring k] {Q : Quiver (Fin n)}
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData
      k (Fin n)}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData
      ρ₁ ρ₂) :
    RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverEquivData
      k (Fin n) ρ₁ ρ₂ where
  app := f.linearEquivAt
  naturality e x := f.linearEquivAt_map e x

private lemma not_posdef_not_HasFiniteRepresentationType
    (k : Type) [Field k] [IsAlgClosed k]
    (n : ℕ) [Quiver.{0} (Fin n)] [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]
    [∀ a b : Fin n, Subsingleton (a ⟶ b)]
    (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation
      ‹Quiver (Fin n)› (auxiliaryMatrix n))
    (hconn : AuxiliaryQuiverCondition n)
    (h_not_posdef : ∃ x : Fin n → ℤ, x ≠ 0 ∧
      ¬ (0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
        auxiliaryMatrix n).mulVec x))) :
    ¬ AuxiliaryQuiverProperty k n := by
  intro hfrt
  obtain ⟨x, hx_ne, hx_not_pd⟩ := h_not_posdef
  classical
  haveI hfin : ∀ a b : Fin n, Fintype (a ⟶ b) := fun a b =>
    if h : Nonempty (a ⟶ b) then Fintype.ofSubsingleton h.some
    else @Fintype.ofIsEmpty _ (not_nonempty_iff.mp h)
  obtain ⟨_m, reps, _hrfin, _hrindec, hrcover⟩ := hfrt
  have hcover : ∀ (W :
      RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{0, 0, 0, 0}
        k (Fin n)),
      (∀ v, Module.Free k (W.obj v)) → (∀ v, Module.Finite k (W.obj v)) →
      W.AuxiliaryCondition → ∃ V ∈ Set.range reps, W.Related V := by
    intro W _ hWfin hWindec
    obtain ⟨i, ⟨e⟩⟩ := hrcover W hWfin hWindec
    exact ⟨reps i, ⟨i, rfl⟩, e.app,
      fun {a b} f => by ext y; simpa using e.naturality f y⟩
  haveI horb : ∀ m' : Fin n → ℕ,
      Finite (MulAction.orbitRel.Quotient
        (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m')
        (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m')) :=
    fun m' =>
      RepresentationTheory.Quiver.FiniteOrbits.Quiver.Rep.finite_orbitQuotient_of_finite_indecomposable_representatives
        m' (Set.range reps) (Set.finite_range reps) hcover
  have hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix
      n (auxiliaryMatrix n) :=
    RepresentationTheory.Quiver.AdjacencyQuadraticForm.is_simply_laced_dynkin_of_representation_finrank_lt_vertex_endomorphism_finrank
      k (auxiliaryMatrix n)
      auxiliaryMatrix_isSymm auxiliaryMatrix_diagonal
      auxiliaryMatrix_entry_eq_zero_or_one hconn hOrient
      (fun m' hm' =>
        RepresentationTheory.Quiver.FiniteOrbitDimensionBounds.Quiver.finrank_representation_space_lt_finrank_vertex_endomorphisms_of_finite_orbits
          (k := k) m' hm')
  exact hx_not_pd (hDynkin.2.2.2.2 x hx_ne)

private lemma isDynkinDiagram_HasFiniteRepresentationType
    (k : Type) [Field k]
    (n : ℕ) [Quiver.{0} (Fin n)] [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]
    [∀ a b : Fin n, Subsingleton (a ⟶ b)]
    (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation
      ‹Quiver (Fin n)› (auxiliaryMatrix n))
    (_hconn : AuxiliaryQuiverCondition n)
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix
      n (auxiliaryMatrix n)) :
    AuxiliaryQuiverProperty k n := by
  set adj := auxiliaryMatrix n with hadj
  have h_fin_roots :=
    RepresentationTheory.Quiver.DimensionVectorClassification.finite_setOf_vectorPredicate hDynkin
  haveI : Fintype
      {d : Fin n → ℤ |
        RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d} :=
    h_fin_roots.fintype
  have h_exist : ∀
      (r : {d : Fin n → ℤ |
        RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d}),
      ∃ (ρ : AuxiliaryQuiverType k n),
        (∀ v, Module.Free k (ρ.obj v)) ∧
        (∀ v, Module.Finite k (ρ.obj v)) ∧
        ρ.AuxiliaryCondition ∧
        (∀ v, (r.val v : ℤ) = ↑(Module.finrank k (ρ.obj v))) := by
    intro ⟨α, hα⟩
    obtain ⟨ρ, hFree, hFin, hIndec, hDim⟩ :=
      (RepresentationTheory.Quiver.DimensionVectorClassification.Quiver.exists_finrankVector_and_related_of_vectorPredicate
        hDynkin k hOrient α hα).1
    exact ⟨ρ, hFree, hFin, hIndec, hDim⟩
  choose rep hRep_free hRep_fin hRep_indec hRep_dim using h_exist
  set m := Fintype.card
    {d : Fin n → ℤ |
      RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d}
  obtain ⟨rootEnum⟩ := Fintype.truncEquivFin
    {d : Fin n → ℤ |
      RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d}
  refine ⟨m, fun i => rep (rootEnum.symm i),
    fun i => hRep_fin _, fun i => hRep_indec _, ?_⟩
  intro ρ hρ_fin hρ_indec
  set d_ρ := fun v => (Module.finrank k (ρ.obj v) : ℤ)
  haveI hρ_free : ∀ v, Module.Free k (ρ.obj v) := fun v =>
    @Module.Free.of_divisionRing k (ρ.obj v) _
      (RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing
        (k := k)) _
  have hBdd :=
    RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_finrank_quadratic_form_eq_two
      hDynkin hOrient ρ hρ_indec
  have hd_pos : ∀ i, 0 ≤ d_ρ i := fun i => Int.natCast_nonneg _
  have hd_nonzero : d_ρ ≠ 0 := by
    obtain ⟨v, hv⟩ := hρ_indec.1
    intro heq
    have hfr := congr_fun heq v
    simp only [d_ρ, Pi.zero_apply, Int.natCast_eq_zero] at hfr
    haveI : Subsingleton (ρ.obj v) :=
      @Module.finrank_zero_iff k (ρ.obj v) _
        (RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing
          (k := k)) _ _ |>.mp hfr
    exact absurd hv (not_nontrivial (ρ.obj v))
  have hd_root :
      RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d_ρ :=
    ⟨⟨hd_nonzero, by
      rwa [RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform] at hBdd⟩,
      hd_pos⟩
  set root :
      {d : Fin n → ℤ |
        RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d} :=
    ⟨d_ρ, hd_root⟩
  use rootEnum root
  have hrw : rootEnum.symm (rootEnum root) = root := rootEnum.symm_apply_apply root
  have h_unique :=
    (RepresentationTheory.Quiver.DimensionVectorClassification.Quiver.exists_finrankVector_and_related_of_vectorPredicate
      hDynkin k hOrient d_ρ hd_root).2
  haveI : ∀ v, Module.Free k ((rep root).obj v) := hRep_free root
  haveI : ∀ v, Module.Finite k ((rep root).obj v) := hRep_fin root
  have hρ_dimv : ∀ v, (d_ρ v : ℤ) = ↑(Module.finrank k (ρ.obj v)) := fun _ => rfl
  have hrep_dimv : ∀ v, (d_ρ v : ℤ) = ↑(Module.finrank k ((rep root).obj v)) :=
    hRep_dim root
  obtain ⟨iso⟩ := h_unique ρ (rep root) hρ_indec (hRep_indec root) hρ_dimv hrep_dimv
  exact ⟨by
    change RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverEquivData
      k (Fin n) ρ (rep (rootEnum.symm (rootEnum root)))
    rw [hrw]; exact iso.auxiliaryMap⟩

/-- Under the displayed quiver and auxiliary hypotheses, the auxiliary matrix property implies the
auxiliary quiver property over a field. -/
theorem auxiliaryQuiverProperty_of_auxiliaryMatrixProperty
    (k : Type) [Field k]
    (n : ℕ) [Quiver.{0} (Fin n)] [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]
    [∀ a b : Fin n, Subsingleton (a ⟶ b)]
    (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation
      ‹Quiver (Fin n)› (auxiliaryMatrix n))
    (hconn : AuxiliaryQuiverCondition n)
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix
      n (auxiliaryMatrix n)) :
    AuxiliaryQuiverProperty k n :=
  isDynkinDiagram_HasFiniteRepresentationType k n hOrient hconn hDynkin

/-- Under the displayed quiver and auxiliary hypotheses, the auxiliary quiver property is
equivalent to the auxiliary property of the associated matrix. -/
theorem auxiliaryQuiverProperty_iff_auxiliaryMatrixProperty
    (k : Type) [Field k] [IsAlgClosed k]
    (n : ℕ) [Quiver.{0} (Fin n)] [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]
    [∀ a b : Fin n, Subsingleton (a ⟶ b)]
    (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation
      ‹Quiver (Fin n)› (auxiliaryMatrix n))
    (hconn : AuxiliaryQuiverCondition n) :
    AuxiliaryQuiverProperty k n ↔
      RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix
        n (auxiliaryMatrix n) := by
  constructor
  ·
    intro hfrt
    refine ⟨auxiliaryMatrix_isSymm, auxiliaryMatrix_diagonal,
      auxiliaryMatrix_entry_eq_zero_or_one, hconn, fun x hx => ?_⟩
    by_contra h_not_pos
    exact absurd hfrt
      (not_posdef_not_HasFiniteRepresentationType
        k n hOrient hconn ⟨x, hx, h_not_pos⟩)
  ·
    exact isDynkinDiagram_HasFiniteRepresentationType k n hOrient hconn

end RepresentationTheory.Quiver.AuxiliaryFiniteProperties
