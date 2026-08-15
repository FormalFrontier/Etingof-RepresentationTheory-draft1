/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.Representation.MatrixModel
import RepresentationTheory.AuxiliaryQuiverRepresentationOperations
import RepresentationTheory.Quiver.Finite
import RepresentationTheory.QuiverRepresentationQuotientTransform
import Mathlib































set_option backward.isDefEq.respectTransparency false

namespace RepresentationTheory.Quiver.FiniteOrbits

open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram MulAction

variable {k : Type} [Field k] {n : ℕ} [Quiver.{0} (Fin n)]





/-- Pairwise isomorphic lists of quiver representations have isomorphic finite direct sums. -/
theorem Quiver.Rep.listDirectSum_isomorphic_of_forall2
    {L₁ L₂ : List (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n))}
    (h : List.Forall₂ RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.Related L₁ L₂) :
    (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L₁).Related (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L₂) := by
  induction h with
  | nil => exact RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.Related.refl _
  | cons hab _ ih =>
      rw [RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct_cons, RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct_cons]
      exact RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.Related.prod hab ih



/-- Replacing every member of a finite list of quiver representations by an isomorphic representation preserves the isomorphism class of its direct sum. -/
theorem Quiver.Rep.listDirectSum_isomorphic_map
    {L : List (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n))}
    {R : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n) → RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n)}
    (hR : ∀ W ∈ L, W.Related (R W)) :
    (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L).Related (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct (L.map R)) := by
  apply Quiver.Rep.listDirectSum_isomorphic_of_forall2
  induction L with
  | nil => exact List.Forall₂.nil
  | cons a L' ih =>
      refine List.Forall₂.cons (hR a (List.mem_cons_self ..)) (ih ?_)
      intro W hW
      exact hR W (List.mem_cons_of_mem _ hW)





/-- A quiver representation whose space at each vertex is linearly equivalent to the coordinate space prescribed by a dimension vector is isomorphic to the representation determined by some point of the corresponding representation space. -/
theorem Quiver.Rep.exists_pointRepresentation_isomorphic (m : Fin n → ℕ)
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n))
    (h : ∀ i, Nonempty (V.obj i ≃ₗ[k] (Fin (m i) → k))) :
    ∃ x : RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m, (RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation m x).Related V := by
  classical

  let e : ∀ i, V.obj i ≃ₗ[k] (Fin (m i) → k) := fun i => (h i).some

  refine ⟨fun i j f =>
      LinearMap.toMatrix' ((e j).toLinearMap ∘ₗ V.map f ∘ₗ (e i).symm.toLinearMap), ?_⟩
  refine ⟨fun i => (e i).symm, ?_⟩
  intro a b f
  ext y
  simp [RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation_map, Matrix.toLin'_toMatrix']




/-- Every summand has a finite-dimensional space at a fixed vertex when the direct sum has a finite-dimensional space there. -/
theorem Quiver.Rep.finite_obj_of_mem_listDirectSum {v : Fin n}
    {L : List (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n))}
    (hfin : Module.Finite k ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L).obj v))
    {W : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n)} (hW : W ∈ L) :
    Module.Finite k (W.obj v) := by
  induction L with
  | nil => exact absurd hW (List.not_mem_nil)
  | cons a L' ih =>
      rw [RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct_cons] at hfin

      have hprod : Module.Finite k (a.obj v × (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L').obj v) := hfin
      haveI ha : Module.Finite k (a.obj v) :=
        Module.Finite.of_surjective (LinearMap.fst k (a.obj v) ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L').obj v))
          Prod.fst_surjective
      haveI hrest : Module.Finite k ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L').obj v) :=
        Module.Finite.of_surjective (LinearMap.snd k (a.obj v) ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L').obj v))
          Prod.snd_surjective
      rcases List.mem_cons.mp hW with h | h
      · subst h; exact ha
      · exact ih hrest h


/-- The space at a fixed vertex of a finite direct sum is finite-dimensional when the corresponding space of every summand is finite-dimensional. -/
theorem Quiver.Rep.finite_obj_listDirectSum {v : Fin n}
    {L : List (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n))}
    (hfin : ∀ W ∈ L, Module.Finite k (W.obj v)) :
    Module.Finite k ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L).obj v) := by
  induction L with
  | nil =>
      rw [RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct_nil]
      have : Subsingleton ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryZero : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n)).obj v) := by
        change Subsingleton PUnit; infer_instance
      rw [Module.finite_def, Subsingleton.elim (⊤ : Submodule k _) ⊥]
      exact Submodule.fg_bot
  | cons a L' ih =>
      rw [RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct_cons]
      haveI : Module.Finite k (a.obj v) := hfin a (List.mem_cons_self ..)
      haveI : Module.Finite k ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L').obj v) :=
        ih (fun W hW => hfin W (List.mem_cons_of_mem _ hW))
      exact inferInstanceAs (Module.Finite k (a.obj v × _))


/-- For componentwise finite-dimensional summands, the sum of the vertexwise finranks of their finite direct sum equals the sum of their individual total vertexwise finranks. -/
theorem Quiver.Rep.sum_finrank_obj_listDirectSum
    {L : List (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n))}
    (hfin : ∀ W ∈ L, ∀ v, Module.Finite k (W.obj v)) :
    (∑ i, Module.finrank k ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L).obj i))
      = (L.map (fun W => ∑ i, Module.finrank k (W.obj i))).sum := by
  induction L with
  | nil =>
      simp only [RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct_nil, List.map_nil, List.sum_nil]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have : Subsingleton ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryZero : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n)).obj i) := by
        change Subsingleton PUnit; infer_instance
      exact Module.finrank_zero_of_subsingleton
  | cons a L' ih =>
      have hfin' : ∀ W ∈ L', ∀ v, Module.Finite k (W.obj v) :=
        fun W hW => hfin W (List.mem_cons_of_mem _ hW)
      have ha : ∀ v, Module.Finite k (a.obj v) := hfin a (List.mem_cons_self ..)
      have hrest : ∀ v, Module.Finite k ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L').obj v) :=
        fun v => Quiver.Rep.finite_obj_listDirectSum (fun W hW => hfin' W hW v)
      letI : ∀ v, AddCommGroup (a.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
      letI : ∀ v, AddCommGroup ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L').obj v) :=
        fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
      rw [RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct_cons, List.map_cons, List.sum_cons, ← ih hfin']
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      haveI := ha i
      haveI := hrest i
      exact Module.finrank_prod



/-- A componentwise finite-dimensional indecomposable quiver representation has positive total vertexwise finrank. -/
theorem Quiver.Rep.one_le_sum_finrank_obj_of_indecomposable
    {W : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n)}
    (hfin : ∀ v, Module.Finite k (W.obj v)) (hW : W.AuxiliaryCondition) :
    1 ≤ ∑ i, Module.finrank k (W.obj i) := by
  obtain ⟨v, hv⟩ := hW.1
  letI : ∀ w, AddCommGroup (W.obj w) := fun w => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  haveI := hfin v
  have hpos : 0 < Module.finrank k (W.obj v) := by
    rw [Module.finrank_pos_iff_of_free]; exact hv
  calc 1 ≤ Module.finrank k (W.obj v) := hpos
    _ ≤ ∑ i, Module.finrank k (W.obj i) :=
        Finset.single_le_sum (f := fun i => Module.finrank k (W.obj i))
          (fun i _ => Nat.zero_le _) (Finset.mem_univ v)





/-- If a direct sum of indecomposable quiver representations is isomorphic to a representation with a prescribed dimension vector, then the number of summands is at most the sum of the entries of that vector. -/
theorem Quiver.Rep.length_le_sum_dimension_of_listDirectSum_isomorphic_pointRepresentation (m : Fin n → ℕ)
    (x : RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m) {L : List (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n))}
    (hiso : (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L).Related (RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation m x))
    (hind : ∀ W ∈ L, W.AuxiliaryCondition) :
    L.length ≤ ∑ i, m i := by
  obtain ⟨e, -⟩ := hiso

  have hfinDS : ∀ v, Module.Finite k ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L).obj v) := by
    intro v
    haveI : Module.Finite k ((RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation m x).obj v) := by
      change Module.Finite k (Fin (m v) → k); infer_instance
    exact Module.Finite.equiv (e v).symm
  have hfinW : ∀ W ∈ L, ∀ v, Module.Finite k (W.obj v) :=
    fun W hW v => Quiver.Rep.finite_obj_of_mem_listDirectSum (hfinDS v) hW

  have htd : (∑ i, Module.finrank k ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L).obj i)) = ∑ i, m i := by
    have h1 : ∀ i, Module.finrank k ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L).obj i)
        = Module.finrank k ((RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation m x).obj i) := fun i => LinearEquiv.finrank_eq (e i)
    have h2 : ∀ i, Module.finrank k ((RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation m x).obj i) = m i := by
      intro i; change Module.finrank k (Fin (m i) → k) = m i; exact Module.finrank_fin_fun (R := k)
    simp_rw [h1, h2]
  rw [Quiver.Rep.sum_finrank_obj_listDirectSum hfinW] at htd

  have hge : L.length ≤ (L.map (fun W => ∑ i, Module.finrank k (W.obj i))).sum := by
    have h1 : (L.map (fun W => ∑ i, Module.finrank k (W.obj i))).length
        ≤ (L.map (fun W => ∑ i, Module.finrank k (W.obj i))).sum := by
      refine List.length_le_sum_of_one_le _ ?_
      intro y hy
      obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hy
      exact Quiver.Rep.one_le_sum_finrank_obj_of_indecomposable (hfinW W hW) (hind W hW)
    rwa [List.length_map] at h1
  rw [htd] at hge
  exact hge



open Classical in


/-- Associates a point of the representation space for a dimension vector to a quiver representation. -/
noncomputable def Quiver.Rep.toRepresentationSpace (m : Fin n → ℕ) (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n)) :
    RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m :=
  if h : ∀ i, Nonempty (V.obj i ≃ₗ[k] (Fin (m i) → k))
  then (Quiver.Rep.exists_pointRepresentation_isomorphic m V h).choose
  else fun _ _ _ => 0

/-- If every vertex space of a quiver representation is linearly equivalent to the coordinate space prescribed by a dimension vector, then the representation reconstructed from its associated point is isomorphic to the original representation. -/
theorem Quiver.Rep.pointRepresentation_toRepresentationSpace_isomorphic (m : Fin n → ℕ) (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n))
    (h : ∀ i, Nonempty (V.obj i ≃ₗ[k] (Fin (m i) → k))) :
    (RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation m (Quiver.Rep.toRepresentationSpace m V)).Related V := by
  rw [Quiver.Rep.toRepresentationSpace, dif_pos h]
  exact (Quiver.Rep.exists_pointRepresentation_isomorphic m V h).choose_spec






/-- If a finite set contains an isomorphic representative of every componentwise free, finite-dimensional, indecomposable quiver representation, then the base-change orbit quotient of the representation space for any fixed dimension vector is finite. -/
theorem Quiver.Rep.finite_orbitQuotient_of_finite_indecomposable_representatives (m : Fin n → ℕ)
    (reps : Set (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.{0, 0, 0, 0} k (Fin n)))
    (hrepsfin : reps.Finite)
    (hreps : ∀ (W : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.{0, 0, 0, 0} k (Fin n)),
        (∀ v, Module.Free k (W.obj v)) → (∀ v, Module.Finite k (W.obj v)) →
        W.AuxiliaryCondition → ∃ V ∈ reps, W.Related V) :
    Finite (orbitRel.Quotient (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m)) := by
  classical
  haveI : Finite reps := hrepsfin.to_subtype
  set Mtot := ∑ i, m i with hMtot

  haveI hIdx : Finite {l : List reps | l.length ≤ Mtot} :=
    (List.finite_length_le reps Mtot).to_subtype

  refine Finite.of_surjective
    (β := orbitRel.Quotient (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m))
    (fun l : {l : List reps | l.length ≤ Mtot} =>
      Quotient.mk'' (Quiver.Rep.toRepresentationSpace m (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct (l.1.map Subtype.val)))) ?_

  intro q
  induction q using Quotient.inductionOn' with
  | _ x =>

    haveI : ∀ v, Module.Finite k ((RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation m x).obj v) := fun v => by
      change Module.Finite k (Fin (m v) → k); infer_instance
    obtain ⟨L, hLind, hLiso⟩ := RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliary_exists_list_of_property (RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation m x)

    obtain ⟨e, -⟩ := id hLiso
    have hfinW : ∀ W ∈ L, ∀ v, Module.Finite k (W.obj v) := by
      intro W hW v
      have hfinDS : Module.Finite k ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct L).obj v) := Module.Finite.equiv (e v)
      exact Quiver.Rep.finite_obj_of_mem_listDirectSum hfinDS hW

    have hpick : ∀ W ∈ L, ∃ R ∈ reps, W.Related R := by
      intro W hW
      letI : ∀ v, AddCommGroup (W.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
      exact hreps W (fun v => inferInstance) (hfinW W hW) (hLind W hW)
    choose! R hRmem hRiso using hpick

    let L' : List reps := L.pmap (fun W hW => (⟨R W, hRmem W hW⟩ : reps)) (fun _ h => h)
    have hL'val : L'.map Subtype.val = L.map R := by
      rw [List.map_pmap]; exact List.pmap_eq_map _
    have hlen' : L'.length = L.length := List.length_pmap

    have hbig : (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct (L'.map Subtype.val)).Related (RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation m x) := by
      rw [hL'val]
      exact (Quiver.Rep.listDirectSum_isomorphic_map hRiso).symm.trans hLiso.symm

    have hlen : L'.length ≤ Mtot := by
      rw [hlen', hMtot]
      exact Quiver.Rep.length_le_sum_dimension_of_listDirectSum_isomorphic_pointRepresentation m x hLiso.symm hLind
    refine ⟨⟨L', hlen⟩, ?_⟩

    have hH : ∀ i, Nonempty ((RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct (L'.map Subtype.val)).obj i ≃ₗ[k] (Fin (m i) → k)) := by
      obtain ⟨e', -⟩ := id hbig
      exact fun i => ⟨e' i⟩

    have hiso2 : (RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation m x).Related
        (RepresentationTheory.Quiver.Representation.MatrixModel.matrixDataToRepresentation m (Quiver.Rep.toRepresentationSpace m (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct (L'.map Subtype.val)))) :=
      hbig.symm.trans (Quiver.Rep.pointRepresentation_toRepresentationSpace_isomorphic m _ hH).symm
    obtain ⟨g, hg⟩ := (RepresentationTheory.Quiver.Representation.MatrixModel.matrixData_sameOrbit_iff_isomorphicRepresentations m x
      (Quiver.Rep.toRepresentationSpace m (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct (L'.map Subtype.val)))).mpr hiso2
    change Quotient.mk'' (Quiver.Rep.toRepresentationSpace m (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.auxiliaryListProduct (L'.map Subtype.val))) = Quotient.mk'' x
    exact Quotient.sound' (hg ▸ MulAction.mem_orbit x g)










/-- Over an algebraically closed field, an integer matrix that encodes a quiver with at most one arrow between each ordered pair and satisfies the supplied matrix predicate gives a finite base-change orbit quotient for every dimension vector. -/
theorem Quiver.Rep.finite_orbitQuotient_of_adjacencyMatrix_conditions [IsAlgClosed k]
    (adj : Matrix (Fin n) (Fin n) ℤ) [∀ a b : Fin n, Subsingleton (a ⟶ b)]
    (hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation ‹Quiver.{0} (Fin n)› adj)
    (hFT : RepresentationTheory.Quiver.Finite.IsAdjacencyMatrix n adj) (m : Fin n → ℕ) :
    Finite (orbitRel.Quotient (RepresentationTheory.Quiver.Representation.MatrixModel.BaseChangeGroup k m) (RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m)) := by
  obtain ⟨reps, hfin, _, hcov⟩ := hFT.2 k _ hQ
  exact Quiver.Rep.finite_orbitQuotient_of_finite_indecomposable_representatives m reps hfin hcov

end RepresentationTheory.Quiver.FiniteOrbits
