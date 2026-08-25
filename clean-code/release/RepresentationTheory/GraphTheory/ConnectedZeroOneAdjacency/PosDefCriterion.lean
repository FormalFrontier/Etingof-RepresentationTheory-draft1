/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.AuxiliaryQuiverRepresentationDimensions
import RepresentationTheory.QuiverRepresentation.Auxiliary
import RepresentationTheory.Quiver.DimensionVectorClassification
import RepresentationTheory.Matrix.BinaryAdjacencyClassification
import RepresentationTheory.Quiver.Finite
import RepresentationTheory.Quiver.MatrixOrientation
import RepresentationTheory.Quiver.AdjacencyQuadraticForm
import RepresentationTheory.Quiver.FiniteOrbitDimensionBounds
import RepresentationTheory.Quiver.FiniteOrbits
import RepresentationTheory.Alignment.Attribute

open _root_.RepresentationTheory in

/-- For a symmetric zero-one adjacency matrix in which every pair of vertices is joined by a walk, the two specified matrix conditions are equivalent. -/
theorem RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.iff_of_symmetric_zeroOne_walkConnected
    (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) :
    RepresentationTheory.Quiver.Finite.IsAdjacencyMatrix n adj ↔
      RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj := by
  constructor
  ·
    intro hft
    have hdiag : ∀ i, adj i i = 0 :=
      hft.diagonal_eq_zero_of_entries_eq_zero_or_one h01
    letI Q : Quiver.{0} (Fin n) :=
      RepresentationTheory.Quiver.MatrixOrientation.quiverOfAdjacencyMatrix adj
    haveI hfin : ∀ a b : Fin n, Fintype (@Quiver.Hom (Fin n) Q a b) := by
      intro a b
      classical
      exact if h : Nonempty (@Quiver.Hom (Fin n) Q a b)
        then Fintype.ofSubsingleton h.some
        else @Fintype.ofIsEmpty _ (not_nonempty_iff.mp h)
    have hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj :=
      RepresentationTheory.Quiver.MatrixOrientation.quiverOfAdjacencyMatrix_isMatrixOrientation
        adj hsymm hdiag
    haveI horb : ∀ m : Fin n → ℕ,
        Finite (MulAction.orbitRel.Quotient
          (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup ℂ m)
          (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := ℂ) m)) := fun m =>
      RepresentationTheory.Quiver.FiniteOrbits.Quiver.Rep.finite_orbitQuotient_of_adjacencyMatrix_conditions
        (k := ℂ) adj hQ hft m
    exact
      RepresentationTheory.Quiver.AdjacencyQuadraticForm.is_simply_laced_dynkin_of_representation_finrank_lt_vertex_endomorphism_finrank
        ℂ adj hsymm hdiag h01 hconn hQ
        (fun m hm =>
          RepresentationTheory.Quiver.FiniteOrbitDimensionBounds.Quiver.finrank_representation_space_lt_finrank_vertex_endomorphisms_of_finite_orbits
            (k := ℂ) m hm)
  ·
    intro hDynkin
    refine ⟨⟨RepresentationTheory.Quiver.MatrixOrientation.quiverOfAdjacencyMatrix adj,
      fun _ _ => inferInstance,
      RepresentationTheory.Quiver.MatrixOrientation.quiverOfAdjacencyMatrix_isMatrixOrientation
        adj hDynkin.1 hDynkin.2.1⟩, ?_⟩
    intro k _inst_field _inst_algclosed Q _inst_ss hOrient
    classical
    have hPR_fin : Set.Finite
        {α : Fin n → ℤ |
          RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition
            n adj α} :=
      RepresentationTheory.Quiver.DimensionVectorClassification.finite_setOf_vectorPredicate
        hDynkin
    have hex : ∀ α : Fin n → ℤ,
        RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj α →
        ∃ ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{0, 0, 0, 0}
            k (Fin n) _ Q,
          (∀ v, Module.Free k (ρ.obj v)) ∧ (∀ v, Module.Finite k (ρ.obj v)) ∧
            ρ.AuxiliaryCondition ∧ ∀ v, α v = (Module.finrank k (ρ.obj v) : ℤ) := by
      intro α hα
      obtain ⟨ρ, hfree, hfin, hindec, hdim⟩ :=
        (RepresentationTheory.Quiver.DimensionVectorClassification.Quiver.exists_finrankVector_and_related_of_vectorPredicate
          hDynkin k hOrient α hα).1
      exact ⟨ρ, hfree, hfin, hindec, hdim⟩
    choose! g hg_free hg_fin hg_indec hg_dim using hex
    refine ⟨_, hPR_fin.dependent_image (fun α hα => g α hα), ?_, ?_⟩
    ·
      rintro V ⟨α, hα, rfl⟩
      exact hg_indec α hα
    ·
      intro W hWfree hWfin hWindec
      haveI : ∀ v, Module.Free k (W.obj v) := hWfree
      haveI : ∀ v, Module.Finite k (W.obj v) := hWfin
      set dW : Fin n → ℤ := fun v => (Module.finrank k (W.obj v) : ℤ) with hdW
      have hdW_root :
          RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition
            n adj dW := by
        refine
          RepresentationTheory.Quiver.DimensionVectorClassification.vectorPredicate_of_nonneg_of_dot_mulVec_eq_two
            hDynkin dW (fun i => Int.natCast_nonneg _) ?_ ?_
        ·
          obtain ⟨v, hv⟩ := hWindec.1
          intro heq
          have hv0 : Module.finrank k (W.obj v) = 0 := by
            have h := congr_fun heq v
            simpa [hdW] using h
          letI : AddCommGroup (W.obj v) :=
            RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing
              (k := k)
          haveI : Subsingleton (W.obj v) := Module.finrank_zero_iff.mp hv0
          exact not_nontrivial (W.obj v) hv
        ·
          exact
            RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_finrank_quadratic_form_eq_two
              hDynkin hOrient W hWindec
      refine ⟨g dW hdW_root, ⟨dW, hdW_root, rfl⟩, ?_⟩
      haveI : ∀ v, Module.Free k ((g dW hdW_root).obj v) := hg_free dW hdW_root
      haveI : ∀ v, Module.Finite k ((g dW hdW_root).obj v) := hg_fin dW hdW_root
      have huniq :=
        (RepresentationTheory.Quiver.DimensionVectorClassification.Quiver.exists_finrankVector_and_related_of_vectorPredicate
          hDynkin k hOrient dW hdW_root).2
          W (g dW hdW_root) hWindec (hg_indec dW hdW_root) (fun _ => rfl)
          (hg_dim dW hdW_root)
      obtain ⟨iso⟩ := huniq
      exact ⟨iso.linearEquivAt, fun {a b} f => by ext x; simpa using iso.linearEquivAt_map f x⟩

/-- Under the stated condition on a connected symmetric zero-one adjacency matrix, the quadratic form of twice the identity minus the adjacency matrix is positive on every nonzero rational vector. -/
theorem RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.quadraticForm_twoIdentity_sub_adjacency_pos
    {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (hsymm : adj.IsSymm)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (hft : RepresentationTheory.Quiver.Finite.IsAdjacencyMatrix n adj) :
    ∀ x : Fin n → ℚ, x ≠ 0 →
      0 < dotProduct x
        (((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).map
          (Int.castRingHom ℚ)).mulVec x) := by
  apply RepresentationTheory.AdjacencyMatrixQuadraticForms.rat_quadratic_pos_of_int_quadratic_pos adj
  exact
    ((RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.iff_of_symmetric_zeroOne_walkConnected
      n adj hsymm h01 hconn).mp hft).2.2.2.2

/-- Under the stated condition on a connected symmetric zero-one adjacency matrix, twice the identity minus the real adjacency matrix is positive definite. -/
theorem RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.posDef_twoIdentity_sub_adjacency
    {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (hsymm : adj.IsSymm)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (hft : RepresentationTheory.Quiver.Finite.IsAdjacencyMatrix n adj) :
    ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).map
      (Int.castRingHom ℝ)).PosDef :=
  RepresentationTheory.AdjacencyMatrixQuadraticForms.real_posDef_of_rat_quadratic_pos adj hsymm
    (RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.quadraticForm_twoIdentity_sub_adjacency_pos
      adj hsymm h01 hconn hft)

/-- For a connected symmetric zero-one adjacency matrix, failure of the first specified condition forces failure of the second. -/
theorem RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.not_of_not_related_condition
    {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_not_dynkin :
      ¬ RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    ¬ RepresentationTheory.Quiver.Finite.IsAdjacencyMatrix n adj := by
  intro hft
  exact h_not_dynkin
    ((RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.iff_of_symmetric_zeroOne_walkConnected
      n adj hsymm h01 hconn).mp hft)

/-- A nonempty connected symmetric zero-one adjacency matrix admitting no map that preserves the displayed adjacency entries of the indicated rank-indexed structure fails the specified condition. -/
theorem RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.not_of_no_adjacencyPreservingMap
    {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n)
    (hsymm : adj.IsSymm)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_not_ade : ¬ ∃ t : RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel,
      ∃ σ : Fin t.rank ≃ Fin n,
        ∀ i j, adj (σ i) (σ j) = t.matrix i j) :
    ¬ RepresentationTheory.Quiver.Finite.IsAdjacencyMatrix n adj := by
  apply
    RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.not_of_not_related_condition
      adj hsymm h01 hconn
  intro hD
  exact h_not_ade
    ((RepresentationTheory.Matrix.BinaryAdjacencyClassification.Matrix.exists_adjacency_reindexing_iff
      n adj hn).mp hD)

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.Auxiliary.statement016733 := _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.iff_of_symmetric_zeroOne_walkConnected

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.Auxiliary.statement021720 := _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.not_of_no_adjacencyPreservingMap

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.Auxiliary.statement021721 := _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.not_of_not_related_condition

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.Auxiliary.statement024130 := _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.quadraticForm_twoIdentity_sub_adjacency_pos

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.Auxiliary.statement024139 := _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.posDef_twoIdentity_sub_adjacency

attribute [source_ref "Chapter6/Problem6.1.5" (role := supporting)] _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.Auxiliary.statement016733

attribute [source_ref "Chapter6/Problem6.1.5_parts" (role := supporting)] _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.Auxiliary.statement016733

attribute [source_ref "Chapter6/Problem6.1.5_theorem" (role := primary)] _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.Auxiliary.statement016733

attribute [source_ref "Chapter6/Problem6.1.5_parts" (role := primary)] _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.Auxiliary.statement024130

attribute [source_ref "Chapter6/Problem6.1.5_parts" (role := primary)] _root_.RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.Auxiliary.statement024139
