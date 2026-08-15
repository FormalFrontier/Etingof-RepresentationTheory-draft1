/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryQuiverRepresentationDimensions
import RepresentationTheory.AuxiliaryQuiverConstructions
import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.AuxiliaryIntegerMatrixTransform
import RepresentationTheory.AuxiliaryFiniteDimensionalFamily
import RepresentationTheory.QuiverRepresentation.Auxiliary
import RepresentationTheory.Surjective
import RepresentationTheory.Quiver.AuxiliaryAtVertex
import RepresentationTheory.Quiver.AuxiliaryNatInt
import RepresentationTheory.Quiver.LinearAlgebra.Auxiliary
import RepresentationTheory.LinearAlgebra.IntegerMatrixReflections
import RepresentationTheory.IntegerMatrix.ReflectionDynamics
import Mathlib.LinearAlgebra.Dimension.Free
import RepresentationTheory.Alignment.Attribute

open scoped Matrix

section Helpers

private lemma RepresentationTheory.AuxiliaryQuiverRepresentationRelations.noSelfLoop_of_dynkin_orientation
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {Q : Quiver (Fin n)}
    (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    (p : Fin n) :
    IsEmpty (@Quiver.Hom (Fin n) Q p p) :=
  hOrient.1 p p (by rw [hDynkin.2.1 p]; omega)

end Helpers

section IsoComposition

/-- Reverses an auxiliary relation between two quiver representations. -/
noncomputable def RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData.symm
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₁ ρ₂) :
    RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₂ ρ₁ :=
  ⟨fun v => (f.linearEquivAt v).symm,
   fun e x => by
     apply (f.linearEquivAt _).injective
     rw [LinearEquiv.apply_symm_apply, f.linearEquivAt_map, LinearEquiv.apply_symm_apply]⟩

/-- Composes two auxiliary relations between quiver representations. -/
noncomputable def RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData.trans
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {ρ₁ ρ₂ ρ₃ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q}
    (f : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₁ ρ₂)
    (g : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₂ ρ₃) :
    RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₁ ρ₃ :=
  ⟨fun v => (f.linearEquivAt v).trans (g.linearEquivAt v),
   fun e x => by
     simp only [LinearEquiv.trans_apply, f.linearEquivAt_map, g.linearEquivAt_map]⟩

/-- Transports an auxiliary relation across an equality of quiver structures. -/
noncomputable def RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData.castQuiver
    {k : Type*} [CommSemiring k] {Q : Type} [DecidableEq Q]
    {inst₁ inst₂ : @Quiver.{0, 0} Q} (h : inst₁ = inst₂)
    {ρ₁ ρ₂ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q _ inst₁}
    (f : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData k _ Q inst₁ ρ₁ ρ₂) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData k _ Q inst₂ (h ▸ ρ₁) (h ▸ ρ₂) := by
  subst h; exact f

end IsoComposition

section SimpleAtIso

private lemma RepresentationTheory.AuxiliaryQuiverRepresentationRelations.simpleAt_iso
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    (ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (p : Q)
    (hNoSelfLoop : IsEmpty (p ⟶ p))
    (h₁ : ρ₁.AuxiliaryVertexCondition p)
    (h₂ : ρ₂.AuxiliaryVertexCondition p) :
    Nonempty (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData ρ₁ ρ₂) := by
  have hdim : ∀ v, Module.finrank k (ρ₁.obj v) = Module.finrank k (ρ₂.obj v) := by
    intro v
    by_cases hv : v = p
    · subst hv; rw [h₁.1, h₂.1]
    · rw [h₁.2 v hv, h₂.2 v hv]
  refine ⟨⟨fun v => LinearEquiv.ofFinrankEq _ _ (hdim v), fun {a b} e x => ?_⟩⟩
  by_cases ha : a = p <;> by_cases hb : b = p
  · subst ha; subst hb; exact (hNoSelfLoop.false e).elim
  · haveI : Subsingleton (ρ₂.obj b) := by
      have hfr := h₂.2 b hb
      exact Module.subsingleton_of_rank_zero
        (by rw [← @Module.finrank_eq_rank k]; exact_mod_cast hfr)
    exact Subsingleton.elim _ _
  · haveI : Subsingleton (ρ₁.obj a) := by
      have hfr := h₁.2 a ha
      exact Module.subsingleton_of_rank_zero
        (by rw [← @Module.finrank_eq_rank k]; exact_mod_cast hfr)
    have : x = 0 := Subsingleton.elim _ _
    subst this
    simp [map_zero]
  · haveI : Subsingleton (ρ₂.obj b) := by
      have hfr := h₂.2 b hb
      exact Module.subsingleton_of_rank_zero
        (by rw [← @Module.finrank_eq_rank k]; exact_mod_cast hfr)
    exact Subsingleton.elim _ _

private lemma RepresentationTheory.AuxiliaryQuiverRepresentationRelations.indecomposable_simpleRoot_iso
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)}
    (hOrient : @RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation n Q adj)
    (ρ₁ ρ₂ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (p : Fin n)
    (hd₁ : ∀ v, (Module.finrank k (ρ₁.obj v) : ℤ) = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p v)
    (hd₂ : ∀ v, (Module.finrank k (ρ₂.obj v) : ℤ) = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p v) :
    Nonempty (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData k _ (Fin n) Q ρ₁ ρ₂) := by
  have hNoSelfLoop := RepresentationTheory.AuxiliaryQuiverRepresentationRelations.noSelfLoop_of_dynkin_orientation hDynkin hOrient p
  have h₁s : ρ₁.AuxiliaryVertexCondition p := by
    refine ⟨?_, fun j hj => ?_⟩
    · have := hd₁ p; simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue] at this; omega
    · have := hd₁ j; simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, show p ≠ j from Ne.symm hj] at this; omega
  have h₂s : ρ₂.AuxiliaryVertexCondition p := by
    refine ⟨?_, fun j hj => ?_⟩
    · have := hd₂ p; simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue] at this; omega
    · have := hd₂ j; simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, show p ≠ j from Ne.symm hj] at this; omega
  exact RepresentationTheory.AuxiliaryQuiverRepresentationRelations.simpleAt_iso ρ₁ ρ₂ p hNoSelfLoop h₁s h₂s

end SimpleAtIso

section ReflectionFunctorChain

private lemma RepresentationTheory.AuxiliaryQuiverRepresentationRelations.parallel_reduce_and_recover
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {k : Type*} [Field k]
    (remaining : List (Fin n))
    {Q_cur : @Quiver.{0, 0} (Fin n)}
    (hOrient_cur : @RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation n Q_cur adj)
    (hSS_cur : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_cur a b))
    (hSinks : ∀ m (hm : m < remaining.length),
        @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
          (@RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryListMap _ _ Q_cur (remaining.take m))
          (remaining.get ⟨m, hm⟩))
    (ρ₁ ρ₂ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k (Fin n) _ Q_cur)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (h₁ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition k _ _ Q_cur ρ₁)
    (h₂ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition k _ _ Q_cur ρ₂)
    (d_cur : Fin n → ℤ)
    (hDim₁ : ∀ v, (Module.finrank k (ρ₁.obj v) : ℤ) = d_cur v)
    (hDim₂ : ∀ v, (Module.finrank k (ρ₂.obj v) : ℤ) = d_cur v)
    (p : Fin n)
    (hreflect : RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) remaining
        d_cur = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p) :
    Nonempty (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData k _ (Fin n) Q_cur ρ₁ ρ₂) := by
  induction remaining generalizing Q_cur d_cur with
  | nil =>
    simp only [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection, List.foldl_nil] at hreflect
    exact RepresentationTheory.AuxiliaryQuiverRepresentationRelations.indecomposable_simpleRoot_iso hDynkin hOrient_cur ρ₁ ρ₂ p
      (fun v => by rw [hDim₁]; exact congr_fun hreflect v)
      (fun v => by rw [hDim₂]; exact congr_fun hreflect v)
  | cons i rest ih =>

    have hi_sink : @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n) Q_cur i := by
      have := hSinks 0 (by simp)

      exact this

    haveI : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_cur a b) := hSS_cur
    haveI : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q_cur i) :=
      RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryFintypeAt i

    rcases @RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrSurjective k _ _ _ Q_cur ρ₁ i _ _ hi_sink h₁ with
      h₁_simple | h₁_surj
    ·

      have hd_simple : d_cur = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i := by
        funext v
        by_cases hv : v = i
        · subst hv; rw [← hDim₁]; simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue]
          exact_mod_cast h₁_simple.1
        · have h := hDim₁ v; have h2 := h₁_simple.2 v hv
          simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, Ne.symm hv] at h ⊢; omega

      exact RepresentationTheory.AuxiliaryQuiverRepresentationRelations.indecomposable_simpleRoot_iso hDynkin hOrient_cur ρ₁ ρ₂ i
        (fun v => by rw [hDim₁, hd_simple])
        (fun v => by rw [hDim₂, hd_simple])
    ·

      rcases @RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrSurjective k _ _ _ Q_cur ρ₂ i _ _ hi_sink h₂ with
        h₂_simple | h₂_surj
      ·
        have hd_simple₂ : d_cur = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i := by
          funext v
          by_cases hv : v = i
          · subst hv; rw [← hDim₂]; simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue]
            exact_mod_cast h₂_simple.1
          · have h := hDim₂ v; have h2 := h₂_simple.2 v hv
            simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, Ne.symm hv] at h ⊢; omega
        exact RepresentationTheory.AuxiliaryQuiverRepresentationRelations.indecomposable_simpleRoot_iso hDynkin hOrient_cur ρ₁ ρ₂ i
          (fun v => by rw [hDim₁, hd_simple₂])
          (fun v => by rw [hDim₂, hd_simple₂])
      ·

        have h₁_sink_ss_of_src :
            (∀ (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) i), Subsingleton (ρ₁.obj a.1)) →
            Subsingleton (ρ₁.obj i) := by
          intro hsrc_ss
          refine ⟨fun a b => ?_⟩
          obtain ⟨x, rfl⟩ := h₁_surj a
          obtain ⟨y, rfl⟩ := h₁_surj b
          suffices x = y by rw [this]
          have : ∀ z : DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) i) (fun a => ρ₁.obj a.1), z = 0 :=
            fun z => DFinsupp.ext (fun j => @Subsingleton.elim _ (hsrc_ss j) _ _)
          exact (this x).trans (this y).symm
        have h₂_sink_ss_of_src :
            (∀ (a : RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) i), Subsingleton (ρ₂.obj a.1)) →
            Subsingleton (ρ₂.obj i) := by
          intro hsrc_ss
          refine ⟨fun a b => ?_⟩
          obtain ⟨x, rfl⟩ := h₂_surj a
          obtain ⟨y, rfl⟩ := h₂_surj b
          suffices x = y by rw [this]
          have : ∀ z : DirectSum (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) i) (fun a => ρ₂.obj a.1), z = 0 :=
            fun z => DFinsupp.ext (fun j => @Subsingleton.elim _ (hsrc_ss j) _ _)
          exact (this x).trans (this y).symm
        let Q_rev := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q_cur i
        let ρ₁_plus := @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ (Fin n) _ Q_cur i hi_sink ρ₁
        let ρ₂_plus := @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ (Fin n) _ Q_cur i hi_sink ρ₂

        haveI hSS_rev : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_rev a b) :=
          fun a b => RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_quiverHom_subsingleton i a b
        haveI : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q_rev i) :=
          @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryFintypeAt _ Q_rev hSS_rev i
        haveI : ∀ (j : Fin n), Fintype (@Quiver.Hom (Fin n) Q_rev i j) :=
          fun j => @RepresentationTheory.AuxiliaryQuiverConstructions.quiverHomFintypeOfSubsingleton _ Q_rev hSS_rev i j
        haveI : Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q_rev i) := Sigma.instFintype

        haveI : ∀ v, Module.Free k (ρ₁_plus.obj v) := fun v => by
          by_cases hv : v = i
          · rw [hv]; exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_free_at k _ (Fin n) _ Q_cur i hi_sink ρ₁ _ _ _
          · exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_free_of_ne k _ (Fin n) _ Q_cur i hi_sink ρ₁ _ v hv
        haveI : ∀ v, Module.Finite k (ρ₁_plus.obj v) := fun v => by
          by_cases hv : v = i
          · rw [hv]; exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_finite_at k _ (Fin n) _ Q_cur i hi_sink ρ₁ _ _ _
          · exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_finite_of_ne k _ (Fin n) _ Q_cur i hi_sink ρ₁ _ v hv
        haveI : ∀ v, Module.Free k (ρ₂_plus.obj v) := fun v => by
          by_cases hv : v = i
          · rw [hv]; exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_free_at k _ (Fin n) _ Q_cur i hi_sink ρ₂ _ _ _
          · exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_free_of_ne k _ (Fin n) _ Q_cur i hi_sink ρ₂ _ v hv
        haveI : ∀ v, Module.Finite k (ρ₂_plus.obj v) := fun v => by
          by_cases hv : v = i
          · rw [hv]; exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_finite_at k _ (Fin n) _ Q_cur i hi_sink ρ₂ _ _ _
          · exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_finite_of_ne k _ (Fin n) _ Q_cur i hi_sink ρ₂ _ v hv

        have h₁_ind : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition k _ _ Q_rev ρ₁_plus := by
          rcases @RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary k _ _ _ Q_cur i hi_sink ρ₁ _ _ h₁ with h | h_zero
          · exact h
          · exfalso
            obtain ⟨⟨v, hv⟩, _⟩ := h₁
            suffices hs : ∀ j, Subsingleton
                (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k (Fin n) _ Q_cur ρ₁ j) from
              absurd (hs v) (not_subsingleton_iff_nontrivial.mpr hv)
            intro j
            by_cases hj : j = i
            · rw [hj]; exact h₁_sink_ss_of_src (fun ⟨m, e⟩ =>
                (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ (Fin n) _ Q_cur i hi_sink ρ₁ m
                  (fun h => (hi_sink m).false (h ▸ e))).toEquiv.subsingleton_congr.mp (h_zero m))
            · exact (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ (Fin n) _
                Q_cur i hi_sink ρ₁ j hj).toEquiv.subsingleton_congr.mp
                (h_zero j)
        have h₂_ind :
            @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryCondition
              k _ _ Q_rev ρ₂_plus := by
          rcases @RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary k _ _ _
            Q_cur i hi_sink ρ₂ _ _ h₂ with h | h_zero
          · exact h
          · exfalso
            obtain ⟨⟨v, hv⟩, _⟩ := h₂
            suffices hs : ∀ j, Subsingleton
                (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.obj k (Fin n)
                  _ Q_cur ρ₂ j) from
              absurd (hs v)
                (not_subsingleton_iff_nontrivial.mpr hv)
            intro j
            by_cases hj : j = i
            · rw [hj]; exact h₂_sink_ss_of_src fun ⟨m, e⟩ =>
                let eq := @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe
                  k _ (Fin n) _ Q_cur i hi_sink ρ₂ m
                  (fun h => (hi_sink m).false (h ▸ e))
                eq.toEquiv.subsingleton_congr.mp (h_zero m)
            · have eq := @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe
                k _ (Fin n) _ Q_cur i hi_sink ρ₂ j hj
              exact eq.toEquiv.subsingleton_congr.mp
                (h_zero j)

        have hOrient_rev : @RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation n Q_rev adj :=
          RepresentationTheory.Quiver.MatrixOrientation.isMatrixOrientation_vertexReorientation hDynkin.1 hDynkin.2.1 hOrient_cur i

        set d_new := RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) i d_cur
        have hDim₁_plus : ∀ v, (Module.finrank k (ρ₁_plus.obj v) : ℤ) = d_new v := by
          intro v
          have h668 := @RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_surjective k _
            (Fin n) _ Q_cur i hi_sink ρ₁ _ _ _ h₁_surj v
          change (ρ₁_plus.auxiliaryNat k v : ℤ) = d_new v
          rw [h668]
          have hd_eq := funext hDim₁
          rw [hd_eq]
          have hbridge := @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_vector_maps_eq _ _
            hDynkin Q_cur hOrient_cur hSS_cur i hi_sink d_cur
          convert congr_fun hbridge v
        have hDim₂_plus : ∀ v, (Module.finrank k (ρ₂_plus.obj v) : ℤ) = d_new v := by
          intro v
          have h668 := @RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_surjective k _
            (Fin n) _ Q_cur i hi_sink ρ₂ _ _ _ h₂_surj v
          change (ρ₂_plus.auxiliaryNat k v : ℤ) = d_new v
          rw [h668]
          have hd_eq := funext hDim₂
          rw [hd_eq]
          have hbridge := @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_vector_maps_eq _ _
            hDynkin Q_cur hOrient_cur hSS_cur i hi_sink d_cur
          convert congr_fun hbridge v

        have hSinks_rest : ∀ m (hm : m < rest.length),
            @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
              (@RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryListMap _ _ Q_rev (rest.take m))
              (rest.get ⟨m, hm⟩) := by
          intro m hm
          exact hSinks (m + 1) (by simp [List.length_cons]; omega)

        have hreflect_rest : RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n
            (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) rest d_new = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p := by
          rw [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection_cons] at hreflect
          exact hreflect

        have h_iso_plus := @ih Q_rev hOrient_rev
          hSS_rev hSinks_rest ρ₁_plus ρ₂_plus _ _ _ _
          h₁_ind h₂_ind d_new hDim₁_plus hDim₂_plus
          hreflect_rest

        obtain ⟨iso_plus⟩ := h_iso_plus

        have hi' := @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryForward (Fin n) _ Q_cur i hi_sink
        obtain ⟨iso_dr⟩ := @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryDataNonemptyAfterOperation k _ (Fin n) _ Q_rev i hi'
          ρ₁_plus ρ₂_plus iso_plus _

        let h_eq := @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq (Fin n) _ Q_cur i
        let iso_transported := iso_dr.castQuiver h_eq

        obtain ⟨iso_rt₁⟩ := @RepresentationTheory.Surjective.nonempty_of_surjective
          k _ (Fin n) _ Q_cur i hi_sink ρ₁ _ _ _ h₁_surj
        obtain ⟨iso_rt₂⟩ := @RepresentationTheory.Surjective.nonempty_of_surjective
          k _ (Fin n) _ Q_cur i hi_sink ρ₂ _ _ _ h₂_surj

        exact ⟨@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData.trans k _ (Fin n) Q_cur _ _ _
          (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData.symm k _ (Fin n) Q_cur _ _ iso_rt₁)
          (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData.trans k _ (Fin n) Q_cur _ _ _
            iso_transported iso_rt₂)⟩

end ReflectionFunctorChain

section TitsFormBound

private lemma RepresentationTheory.AuxiliaryQuiverRepresentationRelations.indecomposable_titsForm_le_two
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {k : Type*} [Field k]
    {Q : @Quiver.{0, 0} (Fin n)}
    (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.{_, 0, 0, 0} k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.AuxiliaryCondition) :
    dotProduct (fun v => (Module.finrank k (ρ.obj v) : ℤ))
      ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec (fun v => (Module.finrank k (ρ.obj v) : ℤ))) ≤ 2 :=
  le_of_eq (RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_finrank_quadratic_form_eq_two hDynkin hOrient ρ hρ)

end TitsFormBound

set_option maxHeartbeats 800000 in

/-- Under the displayed matrix and quiver hypotheses, two auxiliary representations with matching vertexwise dimensions admit an auxiliary relation. -/
@[source_ref "Chapter6/Corollary6.8.3" (role := primary)]
theorem RepresentationTheory.AuxiliaryQuiverRepresentationRelations.auxiliary_nonempty_of_finrank_eq
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {k : Type*} [Field k]
    {Q : @Quiver.{0, 0} (Fin n)}
    (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (ρ₁ ρ₂ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.{_, 0, 0, 0} k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (h₁ : ρ₁.AuxiliaryCondition)
    (h₂ : ρ₂.AuxiliaryCondition)
    (hdim : ∀ v, Module.finrank k (ρ₁.obj v) = Module.finrank k (ρ₂.obj v)) :
    Nonempty (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData k _ (Fin n) Q ρ₁ ρ₂) := by

  obtain ⟨σ, hσ⟩ := RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_exists_list_property hDynkin hOrient
  set A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj
  set d := fun v => (Module.finrank k (ρ₁.obj v) : ℤ) with hd_def
  set c := fun v => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A σ v

  have hd_nonneg : ∀ i, 0 ≤ d i := fun i => Int.natCast_nonneg _
  have hd_nonzero : d ≠ 0 := by
    obtain ⟨⟨v, hv⟩, _⟩ := h₁
    intro h; have : d v = 0 := congr_fun h v
    simp only [d, Int.natCast_eq_zero] at this
    rw [Module.finrank_eq_zero_iff_of_free (R := k)] at this
    exact not_nontrivial_iff_subsingleton.mpr this hv

  obtain ⟨N, i₀, hNeg⟩ := RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_iterate_exists_apply_neg hDynkin σ hσ.perm_finRange d hd_nonneg hd_nonzero

  suffices ∀ (M : ℕ),
      Nonempty (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.AuxiliaryData k _ (Fin n) Q ρ₁ ρ₂) ∨
      ((∀ j, 0 ≤ c^[M] d j) ∧
       ∃ (ρ_M : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram.{_, 0, 0, 0} k (Fin n) _ Q),
         (∀ v, Module.Free k (ρ_M.obj v)) ∧
         (∀ v, Module.Finite k (ρ_M.obj v)) ∧
         ρ_M.AuxiliaryCondition ∧
         (∀ v, (Module.finrank k (ρ_M.obj v) : ℤ) = c^[M] d v)) by
    rcases this N with ⟨iso⟩ | ⟨hNN, _⟩
    · exact iso
    · exact absurd (hNN i₀) (not_le.mpr hNeg)
  intro M
  induction M with
  | zero =>
    right
    exact ⟨fun j => by simp only [Function.iterate_zero, id_eq]; exact hd_nonneg j,
           ρ₁, ‹_›, ‹_›, h₁,
           fun v => by simp only [Function.iterate_zero, id_eq, hd_def]⟩
  | succ M ih =>
    rcases ih with ⟨iso⟩ | ⟨hM_nonneg, ρ_M, hFree_M, hFinite_M, hIndecomp_M, hDimVec_M⟩
    · left; exact iso
    ·
      haveI : ∀ v, Module.Free k (ρ_M.obj v) := hFree_M
      haveI : ∀ v, Module.Finite k (ρ_M.obj v) := hFinite_M
      have hd_M : c^[M] d = fun v => (Module.finrank k (ρ_M.obj v) : ℤ) := by
        ext v; exact (hDimVec_M v).symm
      rcases RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_prefix_or_full_list hDynkin hOrient σ hσ ρ_M hIndecomp_M
        (c^[M] d) hd_M with
        ⟨j, p₀, hj_le, hp₀, _⟩ | ⟨hnonneg, _, ρ', hFree', hFinite', hIndecomp', hDimVec'⟩
      ·
        left

        set vertices := (List.replicate M σ).flatten ++ σ.take j with hvertices_def
        have hSinks := RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_property_get_replicate_append_take Q σ hσ M j hj_le
        have hreflect : RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vertices d =
            RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p₀ := by
          rw [hvertices_def, RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryVectorMap_append,
              RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryVectorMap_replicate]
          exact hp₀
        exact RepresentationTheory.AuxiliaryQuiverRepresentationRelations.parallel_reduce_and_recover hDynkin vertices hOrient
          ‹∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)› hSinks
          ρ₁ ρ₂ h₁ h₂ d (fun v => rfl)
          (fun v => by simp only [hd_def]; exact_mod_cast (hdim v).symm)
          p₀ hreflect
      ·
        right
        refine ⟨fun j => ?_, ρ', hFree', hFinite', hIndecomp', fun v => ?_⟩
        · rw [Function.iterate_succ', Function.comp_apply]; exact hnonneg j
        · rw [Function.iterate_succ', Function.comp_apply]; exact hDimVec' v
