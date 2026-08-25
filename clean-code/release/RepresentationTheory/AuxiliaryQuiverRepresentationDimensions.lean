/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.AuxiliaryIntegerMatrixTransform
import RepresentationTheory.IntegerMatrixVectorPredicates
import RepresentationTheory.AuxiliaryIntegerVectorTransforms
import RepresentationTheory.AuxiliaryFiniteDimensionalFamily
import RepresentationTheory.Quiver.MatrixOrientation
import RepresentationTheory.AuxiliaryQuiverConstructions
import RepresentationTheory.QuiverRepresentation.Auxiliary
import RepresentationTheory.Quiver.AuxiliaryAtVertex
import RepresentationTheory.Quiver.AuxiliaryNatInt
import RepresentationTheory.LinearAlgebra.IntegerMatrixReflections
import RepresentationTheory.IntegerMatrix.ReflectionDynamics
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false











































open scoped Matrix

section SimpleRepresentation



/-- An auxiliary quiver representation over a commutative semiring associated with a selected vertex. -/
noncomputable def RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation
    (k : Type*) [CommSemiring k]
    {n : ℕ} (p : Fin n)
    {Q : Quiver (Fin n)} :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k (Fin n) _ Q where
  obj v := Fin (if v = p then 1 else 0) → k
  map _ := 0


/-- Every vertex module of the auxiliary representation is free over the coefficient semiring. -/
instance RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation_free
    (k : Type*) [CommSemiring k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    Module.Free k ((RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).obj v) :=
  Module.Free.pi _ _


/-- Every vertex module of the auxiliary representation is finite over the coefficient semiring. -/
instance RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation_finite
    (k : Type*) [CommSemiring k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    Module.Finite k ((RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).obj v) :=
  Module.Finite.pi

private lemma RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.simpleRepresentation_finrank
    (k : Type*) [Field k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    Module.finrank k ((RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).obj v) =
      if v = p then 1 else 0 := by
  change Module.finrank k (Fin (if v = p then 1 else 0) → k) = _
  split_ifs with h <;> simp_all

private lemma RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.simpleRepresentation_finrank_eq_simpleRoot
    (k : Type*) [Field k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p v : ℤ) =
      ↑(Module.finrank k ((RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).obj v)) := by
  rw [RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.simpleRepresentation_finrank]
  simp only [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, Pi.single_apply]
  split_ifs <;> simp_all

set_option maxHeartbeats 400000 in



private lemma RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.simpleRepresentation_indecomposable
    (k : Type*) [Field k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} :
    (RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).AuxiliaryCondition := by
  refine ⟨⟨p, ?_⟩, fun W₁ W₂ _ _ hcompl => ?_⟩
  ·
    change Nontrivial (Fin (if p = p then 1 else 0) → k)
    simp only [ite_true]
    exact Pi.nontrivial
  ·
    have hbot : ∀ v, v ≠ p → W₁ v = ⊥ ∧ W₂ v = ⊥ := by
      intro v hv
      have hempty : IsEmpty (Fin (if v = p then 1 else 0)) := by
        simp only [hv, ite_false]; exact Fin.isEmpty
      haveI : Subsingleton ((RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).obj v) :=
        show Subsingleton (Fin (if v = p then 1 else 0) → k) from inferInstance
      exact ⟨Submodule.eq_bot_of_subsingleton, Submodule.eq_bot_of_subsingleton⟩

    have hdim_p : Module.finrank k (Fin (if p = p then 1 else 0) → k) = 1 := by
      simp

    have hcompl_p := hcompl p


    have : W₁ p = ⊥ ∨ W₂ p = ⊥ := by

      letI : ∀ v, AddCommGroup ((RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).obj v) :=
        fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
      by_contra h
      push Not at h
      obtain ⟨h1, h2⟩ := h
      have hr1 := Submodule.one_le_finrank_iff.mpr h1
      have hr2 := Submodule.one_le_finrank_iff.mpr h2
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq (W₁ p) (W₂ p)
      rw [hcompl_p.sup_eq_top, hcompl_p.inf_eq_bot] at hsum
      rw [finrank_top, finrank_bot] at hsum

      have hdim_p' : Module.finrank k ((RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p (Q := Q)).obj p) = 1 :=
        hdim_p
      omega
    rcases this with h | h
    · left; intro v; by_cases hv : v = p
      · subst hv; exact h
      · exact (hbot v hv).1
    · right; intro v; by_cases hv : v = p
      · subst hv; exact h
      · exact (hbot v hv).2

end SimpleRepresentation

universe u in



/-- For a selected finite index, there exists an auxiliary quiver representation whose vertexwise finranks equal the displayed auxiliary values. -/
theorem RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliary_exists_representation_finrank_eq_auxiliary_value
    {n : ℕ} (p : Fin n)
    (k : Type u) [Field k]
    {Q : Quiver (Fin n)} :
    ∃ (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, u, _} k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v))
      (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.AuxiliaryCondition ∧
      ∀ v, (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p v : ℤ) = ↑(Module.finrank k (ρ.obj v)) :=
  ⟨RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation k p,
   fun v => RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation_free k p v,
   fun v => RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliaryRepresentation_finite k p v,
   RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.simpleRepresentation_indecomposable k p,
   fun v => RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.simpleRepresentation_finrank_eq_simpleRoot k p v⟩

open RepresentationTheory.AuxiliaryQuiverRepresentationDimensions in






private lemma RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.positive_root_cartan_bound
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (α : Fin n → ℤ) (hα_nonneg : ∀ i, 0 ≤ α i)
    (hα_root : dotProduct α ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec α) = 2)
    (hα_sum : 2 ≤ ∑ i, α i)
    (k : Fin n) :
    (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec α k ≤ α k := by
  set A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj
  have hAsymm := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.matrixTransform_isSymm hDynkin.1
  by_contra h; push Not at h

  have hαk_pos : 1 ≤ α k := by
    by_contra h'; push Not at h'
    have hαk0 : α k = 0 := le_antisymm (by omega) (hα_nonneg k)
    have : A.mulVec α k ≤ 0 := by
      change (∑ j : Fin n, A k j * α j) ≤ 0
      have hdiag : A k k = 2 := by
        change (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) k k = 2
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
        norm_num; have := hDynkin.2.1 k; omega
      calc ∑ j, A k j * α j = A k k * α k + ∑ j ∈ Finset.univ.erase k, A k j * α j := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
            _ = ∑ j ∈ Finset.univ.erase k, A k j * α j := by rw [hαk0, mul_zero, zero_add]
            _ ≤ 0 := by
                apply Finset.sum_nonpos; intro j hj
                have hne : j ≠ k := Finset.ne_of_mem_erase hj
                have : A k j ≤ 0 := by
                  change (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) k j ≤ 0
                  simp only [Matrix.sub_apply, Matrix.smul_apply,
                    Matrix.one_apply_ne (Ne.symm hne)]
                  norm_num; have := hDynkin.2.2.1 k j; omega
                exact mul_nonpos_of_nonpos_of_nonneg this (hα_nonneg j)
    linarith

  set β : Fin n → ℤ := α - Pi.single k 1
  have hβ_nonneg : ∀ i, 0 ≤ β i := by
    intro i; simp only [β, Pi.sub_apply, Pi.single_apply]
    split_ifs with heq
    · subst heq; omega
    · simp only [sub_zero]; exact hα_nonneg i
  have hβ_nonzero : β ≠ 0 := by
    intro h0; apply_fun (fun f => ∑ i, f i) at h0
    simp only [β, Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply,
      Finset.sum_const_zero] at h0
    omega

  have symm_k : ∀ j, A j k = A k j := fun j => congr_fun (congr_fun hAsymm k) j
  have hBde : dotProduct α (A.mulVec (Pi.single k (1 : ℤ))) = A.mulVec α k := by
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => by rw [symm_k j]; ring
  have hBed : dotProduct (Pi.single k (1 : ℤ)) (A.mulVec α) = A.mulVec α k := by
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hBee : dotProduct (Pi.single k (1 : ℤ)) (A.mulVec (Pi.single k (1 : ℤ))) = 2 := by
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) k k = 2
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    norm_num; have := hDynkin.2.1 k; omega
  have hBβ : dotProduct β (A.mulVec β) = 4 - 2 * A.mulVec α k := by
    change dotProduct (α - Pi.single k 1) (A.mulVec (α - Pi.single k 1)) = _
    simp only [Matrix.mulVec_sub]
    simp only [sub_dotProduct, dotProduct_sub]
    rw [hα_root, hBde, hBed, hBee]; ring
  have hBβ_nonpos : dotProduct β (A.mulVec β) ≤ 0 := by linarith

  have hpos := hDynkin.2.2.2.2 β hβ_nonzero
  rw [show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) = A from rfl] at hpos
  linarith

section BackwardConstruction






open RepresentationTheory.AuxiliaryQuiverRepresentationDimensions in


private noncomputable def fintypeArrowsOutOfOfSubsingleton
    {n : ℕ} {Q : Quiver (Fin n)}
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (i : Fin n) : Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q i) := by
  haveI : ∀ (b : Fin n), Fintype (@Quiver.Hom (Fin n) Q i b) :=
    fun b => RepresentationTheory.AuxiliaryQuiverConstructions.quiverHomFintypeOfSubsingleton i b
  exact Sigma.instFintype

open RepresentationTheory.AuxiliaryQuiverRepresentationDimensions in


private lemma reflFunctorMinus_free_ne
    {k₀ : Type*} [CommRing k₀] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k₀ Q)
    [∀ v, Module.Free k₀ (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (v : Q) (hv : v ≠ i) :
    Module.Free k₀ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k₀ Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) v) :=
  Module.Free.of_equiv (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv).symm

open RepresentationTheory.AuxiliaryQuiverRepresentationDimensions in

private lemma reflFunctorMinus_finite_ne
    {k₀ : Type*} [CommRing k₀] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k₀ Q)
    [∀ v, Module.Finite k₀ (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (v : Q) (hv : v ≠ i) :
    Module.Finite k₀ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k₀ Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) v) :=
  Module.Finite.equiv (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe hi ρ v hv).symm

set_option linter.unusedFintypeInType false in
open RepresentationTheory.AuxiliaryQuiverRepresentationDimensions in

private lemma reflFunctorMinus_free_eq
    {k₀ : Type*} [Field k₀] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k₀ Q)
    [∀ v, Module.Free k₀ (ρ.obj v)] [∀ v, Module.Finite k₀ (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    Module.Free k₀ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k₀ Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) i) := by
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k₀)
  exact Module.Free.of_equiv (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).symm

set_option linter.unusedFintypeInType false in
open RepresentationTheory.AuxiliaryQuiverRepresentationDimensions in

private lemma reflFunctorMinus_finite_eq
    {k₀ : Type*} [Field k₀] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k₀ Q)
    [∀ v, Module.Free k₀ (ρ.obj v)] [∀ v, Module.Finite k₀ (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)] :
    Module.Finite k₀ (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k₀ Q _
      (RepresentationTheory.QuiverVertexReversal.reverseAtVertex Q i)
      (RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation Q i hi ρ) i) := by
  letI : AddCommGroup (DirectSum (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i) (fun a => ρ.obj a.1)) :=
    RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k₀)
  exact Module.Finite.equiv (RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivQuotient hi ρ).symm

open RepresentationTheory.AuxiliaryQuiverRepresentationDimensions in



private lemma simpleReflectionDimVector_eq_simpleReflection_source
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {Q : Quiver (Fin n)} (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [hSS : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (p : Fin n) (hp : @RepresentationTheory.QuiverVertexPredicates.vertexCondition (Fin n) Q p)
    (d : Fin n → ℤ) :
    haveI := fintypeArrowsOutOfOfSubsingleton (Q := Q) p
    RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt (fun (a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q p) => a.1) p d =
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) p d := by
  haveI := fintypeArrowsOutOfOfSubsingleton (Q := Q) p
  haveI : ∀ (a b : Fin n), Fintype (@Quiver.Hom (Fin n) Q a b) :=
    fun a b => RepresentationTheory.AuxiliaryQuiverConstructions.quiverHomFintypeOfSubsingleton a b
  ext v
  unfold RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform
  by_cases hv : v = p
  · subst hv
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, if_true]


    have hdot : d ⬝ᵥ RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj *ᵥ Pi.single v 1 =
        2 * d v - ∑ j : Fin n, adj v j * d j := by
      simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp only [RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp_rw [mul_comm (d _) (adj _ _)]

      have hSymm := hDynkin.1
      simp_rw [show ∀ x, adj x v = adj v x from fun x => by
        exact congr_fun (congr_fun hSymm v) x]
      ring

    have hcard : ∀ j : Fin n, (Fintype.card (@Quiver.Hom (Fin n) Q v j) : ℤ) = adj v j := by
      intro j
      rcases hDynkin.2.2.1 v j with h0 | h1
      ·
        haveI : IsEmpty (@Quiver.Hom (Fin n) Q v j) := hOrient.1 v j (by omega)
        rw [Fintype.card_eq_zero]; omega
      ·
        rcases hOrient.2.1 v j h1 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
        ·
          haveI : Unique (@Quiver.Hom (Fin n) Q v j) :=
            { default := e, uniq := fun a => Subsingleton.elim a e }
          simp [Fintype.card_unique, h1]
        ·
          exact ((hp j).false e).elim

    have hsum : (∑ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q v, d a.fst) =
        ∑ j : Fin n, adj v j * d j := by
      letI sigmaFT : Fintype (Σ j : Fin n, @Quiver.Hom (Fin n) Q v j) := Sigma.instFintype
      have h_unfold : (∑ a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q v, d a.fst) =
          @Finset.sum _ _ _ (@Finset.univ _ sigmaFT) (fun a => d a.fst) := by
        apply Finset.sum_congr
        · ext x; simp [Finset.mem_univ]
        · intros; rfl
      rw [h_unfold, Fintype.sum_sigma]
      congr 1; ext j
      change (∑ _ : @Quiver.Hom (Fin n) Q v j, d j) = adj v j * d j
      rw [Finset.sum_const, nsmul_eq_mul]
      have : (Finset.univ (α := @Quiver.Hom (Fin n) Q v j)).card = Fintype.card _ := rfl
      rw [this, show (Fintype.card (@Quiver.Hom (Fin n) Q v j) : ℤ) = adj v j from hcard j]

    have : ∀ (inst1 inst2 : Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q v)),
        @Finset.sum _ _ _ (@Finset.univ _ inst1) (fun x => d x.fst) =
        @Finset.sum _ _ _ (@Finset.univ _ inst2) (fun x => d x.fst) := by
      intro i1 i2
      apply Finset.sum_congr
      · ext x; simp [Finset.mem_univ]
      · intros; rfl
    linarith [this (fintypeArrowsOutOfOfSubsingleton v) inferInstance, hsum, hdot]
  · simp only [hv, ite_false, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_zero, sub_zero]

open RepresentationTheory.AuxiliaryQuiverRepresentationDimensions in





private lemma exists_prefix_to_simpleRoot
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    {Q : @Quiver.{0, 0} (Fin n)}
    (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (σ : List (Fin n)) (hσ : RepresentationTheory.AuxiliaryQuiverConstructions.AuxiliaryListProperty Q σ)
    (α : Fin n → ℤ) (hα_nonneg : ∀ i, 0 ≤ α i)
    (hα_nonzero : α ≠ 0)
    (hα_B : dotProduct α ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec α) = 2) :
    ∃ (vertices : List (Fin n)) (p : Fin n),
      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) vertices α =
        RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p ∧
      (∀ m (hm : m < vertices.length),
        @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
          (@RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryListMap _ _ Q (vertices.take m))
          (vertices.get ⟨m, hm⟩)) := by
  set A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj with hA_def

  obtain ⟨N, v_neg, hN⟩ := RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_iterate_exists_apply_neg hDynkin σ hσ.perm_finRange α hα_nonneg hα_nonzero

  set fullList := (List.replicate N σ).flatten with hfullList_def

  have hSinks_full : ∀ m (hm : m < fullList.length),
      @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
        (@RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryListMap _ _ Q (fullList.take m))
        (fullList.get ⟨m, hm⟩) := by
    intro m hm
    have hm' : m < ((List.replicate N σ).flatten ++ σ.take 0).length := by
      simp only [List.take_zero, List.append_nil, ← hfullList_def]; exact hm
    have h := RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_property_get_replicate_append_take Q σ hσ N 0 (Nat.zero_le _) m hm'
    have htake_eq : ((List.replicate N σ).flatten ++ σ.take 0).take m =
        fullList.take m := by
      congr 1; simp [hfullList_def]
    rw [htake_eq] at h
    have helem_eq : ((List.replicate N σ).flatten ++ σ.take 0).get ⟨m, hm'⟩ =
        fullList.get ⟨m, hm⟩ := by
      simp only [List.get_eq_getElem, List.take_zero,
        List.append_nil, hfullList_def]
    rw [helem_eq] at h
    exact h

  have hfull_eq : RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A fullList α =
      (fun w => RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A σ w)^[N] α := by
    rw [hfullList_def, RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryVectorMap_replicate]




  have hAsymm : A.IsSymm := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.matrixTransform_isSymm hDynkin.1


  have hprefix_nonneg_B : ∀ k ≤ fullList.length,
      (∀ j < k, 2 ≤ ∑ i, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (fullList.take j) α i) →
      (∀ i, 0 ≤ RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (fullList.take k) α i) ∧
      dotProduct (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (fullList.take k) α)
        (A.mulVec (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (fullList.take k) α)) = 2 := by
    intro k hk hall
    induction k with
    | zero => simp only [List.take_zero]; exact ⟨hα_nonneg, hα_B⟩
    | succ k ih =>
      have hk' : k ≤ fullList.length := by omega
      obtain ⟨ih_nn, ih_B⟩ := ih hk' (fun j hj => hall j (by omega))
      have hk_sum := hall k (by omega)
      set dk := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (fullList.take k) α
      have hcartan := RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.positive_root_cartan_bound hDynkin dk ih_nn ih_B hk_sum
      have hk1 : k + 1 ≤ fullList.length := hk
      have hk_lt : k < fullList.length := by omega
      have htake : fullList.take (k + 1) =
          fullList.take k ++ [fullList.get ⟨k, hk_lt⟩] := by
        apply List.ext_getElem
        · simp [List.length_take, Nat.min_eq_left (by omega : k + 1 ≤ _)]
        · intro i hi1 hi2
          simp only [List.getElem_append]
          split
          · next hi => simp [List.getElem_take]
          · next hi =>
            simp [List.length_take] at hi1 hi
            have : i = k := by omega
            subst this
            simp [List.get_eq_getElem]
      rw [htake, RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryVectorMap_append]
      simp only [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection, List.foldl]
      set vk := fullList.get ⟨k, by omega⟩
      constructor
      · exact RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_nonneg hAsymm dk vk ih_nn (hcartan vk)
      · exact (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.quadraticForm_coordinateReflection hDynkin dk vk).trans ih_B

  have hbad : ¬(∀ j < fullList.length,
      2 ≤ ∑ i, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (fullList.take j) α i) := by
    intro hall
    obtain ⟨hnn, _⟩ := hprefix_nonneg_B fullList.length le_rfl hall
    rw [List.take_length] at hnn
    rw [hfull_eq] at hnn
    exact not_le.mpr (hN) (hnn v_neg)

  push Not at hbad
  obtain ⟨k₀, hk₀_lt, hk₀_sum⟩ := hbad

  have hexists : ∃ m, m < fullList.length ∧
      ∑ i, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (fullList.take m) α i < 2 :=
    ⟨k₀, hk₀_lt, hk₀_sum⟩

  have hexists' : ∃ m, (m < fullList.length ∧
      ∑ i, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (fullList.take m) α i < 2) := hexists
  set m := Nat.find hexists' with hm_def
  have hm_spec := Nat.find_spec hexists'
  have hm_lt := hm_spec.1
  have hm_sum : ∑ i, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (fullList.take m) α i < 2 :=
    hm_spec.2
  have hm_min : ∀ j < m,
      2 ≤ ∑ i, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (fullList.take j) α i := by
    intro j hj
    by_contra h; push Not at h
    exact Nat.find_min hexists' hj ⟨by omega, h⟩

  obtain ⟨hm_nn, hm_B⟩ := hprefix_nonneg_B m (by omega) hm_min
  set dm := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A (fullList.take m) α

  have hm_nonzero : dm ≠ 0 := by
    intro h0
    have : dotProduct dm (A.mulVec dm) = 0 := by rw [h0]; simp [dotProduct, Matrix.mulVec]
    linarith
  have hm_sum_pos := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.one_le_sum_of_nonneg_of_ne_zero dm hm_nn hm_nonzero
  have hm_sum1 : ∑ i, dm i = 1 := by omega
  obtain ⟨p, hp⟩ := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.eq_single_of_nonneg_of_sum_eq_one dm hm_nn hm_nonzero hm_sum1

  refine ⟨fullList.take m, p, hp, ?_⟩

  intro j hj
  have hj_lt_m : j < m := by
    rw [List.length_take] at hj; exact lt_of_lt_of_le hj (min_le_left _ _)
  have hj_lt : j < fullList.length := by omega
  rw [List.take_take, min_eq_left (by omega : j ≤ m)]
  have : (fullList.take m).get ⟨j, hj⟩ = fullList.get ⟨j, hj_lt⟩ := by
    simp [List.get_eq_getElem, List.getElem_take]
  rw [this]
  exact hSinks_full j hj_lt

universe u in
set_option maxHeartbeats 800000 in







private lemma backward_construct_rep
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (k : Type u) [Field k]
    (vertices : List (Fin n))
    {Q : @Quiver.{0, 0} (Fin n)}
    (hOrient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    (hSS : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b))
    (hSinks : ∀ m (hm : m < vertices.length),
      @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
        (@RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryListMap _ _ Q (vertices.take m))
        (vertices.get ⟨m, hm⟩))
    (d : Fin n → ℤ)
    (hd_nonneg : ∀ v, 0 ≤ d v)
    (hd_nonzero : d ≠ 0)
    (hd_B : dotProduct d ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec d) = 2)
    (p : Fin n)
    (hreduce : RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) vertices d =
      RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p) :
    ∃ (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, u, 0} k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v))
      (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.AuxiliaryCondition ∧ ∀ v, (d v : ℤ) = ↑(Module.finrank k (ρ.obj v)) := by
  set A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj with hA_def
  have hAsymm : A.IsSymm := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.matrixTransform_isSymm hDynkin.1
  induction vertices generalizing Q d with
  | nil =>

    simp [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection] at hreduce
    subst hreduce
    exact RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliary_exists_representation_finrank_eq_auxiliary_value p k
  | cons v rest ih =>

    by_cases hle : ∑ j : Fin n, d j ≤ 1
    ·
      have hsum_pos := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.one_le_sum_of_nonneg_of_ne_zero d hd_nonneg hd_nonzero
      have hd_sum1 : ∑ j, d j = 1 := by omega
      obtain ⟨q, hq⟩ := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.eq_single_of_nonneg_of_sum_eq_one d hd_nonneg hd_nonzero hd_sum1
      subst hq
      exact RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliary_exists_representation_finrank_eq_auxiliary_value q k
    ·
      push Not at hle
      have hd_sum2 : 2 ≤ ∑ j, d j := by omega

      have hv_sink : @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n) Q v := by
        have := hSinks 0 (by simp)

        exact this

      let Q_rev := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q v
      have hv_source : @RepresentationTheory.QuiverVertexPredicates.vertexCondition (Fin n) Q_rev v :=
        @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryForward (Fin n) _ Q v hv_sink
      have hOrient_rev : @RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation n Q_rev adj :=
        RepresentationTheory.Quiver.MatrixOrientation.isMatrixOrientation_vertexReorientation hDynkin.1 hDynkin.2.1 hOrient v
      have hSS_rev : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_rev a b) :=
        fun a b => RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_quiverHom_subsingleton v a b

      set d₁ := RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A v d with hd₁_def
      have hd₁_nonneg : ∀ j, 0 ≤ d₁ j :=
        RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_nonneg hAsymm d v hd_nonneg
          (RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.positive_root_cartan_bound hDynkin d hd_nonneg hd_B hd_sum2 v)
      have hd₁_nonzero : d₁ ≠ 0 := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_ne_zero_of_quadraticForm_eq_two hDynkin d v hd_B
      have hd₁_B : dotProduct d₁ (A.mulVec d₁) = 2 :=
        (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.quadraticForm_coordinateReflection hDynkin d v).trans hd_B

      have hreduce_rest : RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A rest d₁ =
          RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p := by
        rw [← hreduce]; rfl

      have hSinks_rest : ∀ m (hm : m < rest.length),
          @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
            (@RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryListMap _ _ Q_rev (rest.take m))
            (rest.get ⟨m, hm⟩) := by
        intro m hm
        have hm1 : m + 1 < (v :: rest).length := by simp; omega
        have h := hSinks (m + 1) hm1

        have htake : (v :: rest).take (m + 1) = v :: rest.take m := by
          rfl

        have hget : (v :: rest).get ⟨m + 1, hm1⟩ = rest.get ⟨m, hm⟩ := by
          simp [List.get_eq_getElem]
        rw [htake, hget] at h


        change @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n)
          (@RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryListMap _ _ Q_rev (rest.take m))
          (rest.get ⟨m, hm⟩)
        convert h using 2

      obtain ⟨ρ₁, hFree₁, hFinite₁, hIndec₁, hDim₁⟩ :=
        ih hOrient_rev hSS_rev hSinks_rest d₁ hd₁_nonneg hd₁_nonzero hd₁_B hreduce_rest

      have hd₁_ne_ev : d₁ ≠ RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n v := by
        intro heq
        have hinv : d = RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A v (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n v) := by
          rw [← heq, hd₁_def]
          exact (RepresentationTheory.IntegerMatrix.ReflectionDynamics.coordinateReflection_involutive hAsymm
            (RepresentationTheory.IntegerMatrix.ReflectionDynamics.standardBasis_selfPairing_eq_two hDynkin) v d).symm
        have hd_sum_eq : ∑ j, d j =
            (∑ j, RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n v j) -
            (A.mulVec (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n v)) v := by
          conv_lhs => rw [hinv]
          exact RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.sum_coordinateReflection hAsymm (RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n v) v
        simp only [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, Finset.sum_pi_single', Finset.mem_univ, ite_true] at hd_sum_eq
        have hAev : (A.mulVec (Pi.single v (1 : ℤ))) v = 2 := by
          simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          change (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) v v = 2
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
          norm_num; have := hDynkin.2.1 v; omega
        rw [hAev] at hd_sum_eq
        linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hd_nonneg j)]

      have hρ₁_not_simple : ¬ρ₁.AuxiliaryVertexCondition v := by
        intro ⟨h1, h2⟩
        apply hd₁_ne_ev; ext j
        simp only [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, Pi.single_apply]
        by_cases hj : j = v
        · simp only [hj, ite_true]
          have := (hDim₁ v).symm; rw [h1] at this; exact_mod_cast this.symm
        · simp only [hj, ite_false]
          have := (hDim₁ j).symm; rw [h2 j hj] at this; exact_mod_cast this.symm
      classical

      haveI hFT_out : Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q_rev v) :=
        fintypeArrowsOutOfOfSubsingleton (Q := Q_rev) v

      have h_inj : Function.Injective (ρ₁.outgoingDirectSumMap v) := by
        haveI : ∀ w, Module.Free k (ρ₁.obj w) := hFree₁
        haveI : ∀ w, Module.Finite k (ρ₁.obj w) := hFinite₁
        rcases @RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrInjective k _ (Fin n) _ Q_rev
          ρ₁ v _ _ _ hv_source hIndec₁ with hsimple | hinj
        · exact absurd hsimple hρ₁_not_simple
        · exact hinj

      set fm := @RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ (Fin n) _ Q_rev v hv_source ρ₁ _

      have hinvol : @RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _
          (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q v) v = Q :=
        @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq (Fin n) _ Q v

      set d' := fun w => (@Module.finrank k (ρ₁.obj w)
          _ (ρ₁.addCommMonoid w) (ρ₁.moduleInstance w) : ℤ)
      have hd_eq : d' = fun w => (d₁ w : ℤ) := by
        ext w; simp only [d']; exact (hDim₁ w).symm
      have hbridge :=
        @simpleReflectionDimVector_eq_simpleReflection_source _ _
          hDynkin Q_rev hOrient_rev hSS_rev v hv_source d'

      have hinvol_d : RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A v d₁ = d := by
        rw [hd₁_def]
        exact RepresentationTheory.IntegerMatrix.ReflectionDynamics.coordinateReflection_involutive hAsymm
          (RepresentationTheory.IntegerMatrix.ReflectionDynamics.standardBasis_selfPairing_eq_two hDynkin) v d

      have hIndec_or_zero :
          @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ _
            (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q_rev v) fm ∨
          @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryProperty k _ _
            (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q_rev v) fm := by
        haveI : ∀ w, Module.Free k (ρ₁.obj w) := hFree₁
        haveI : ∀ w, Module.Finite k (ρ₁.obj w) := hFinite₁
        exact @RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary_of_fintype k _ _ _ Q_rev v hv_source ρ₁ _ _ _ hIndec₁

      have h668 : ∀ w,
          (fm.auxiliaryNat k w : ℤ) =
          RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt
            (fun (a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q_rev v) => a.1) v d' w := by
        haveI : ∀ w, Module.Free k (ρ₁.obj w) := hFree₁
        haveI : ∀ w, Module.Finite k (ρ₁.obj w) := hFinite₁
        exact @RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_injective k _ (Fin n) _ Q_rev v hv_source ρ₁ _ _ _ h_inj

      have hFree_fm : ∀ w, Module.Free k
          (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin n) _
            (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q_rev v) fm w) := by
        intro w
        haveI : ∀ w, Module.Free k (ρ₁.obj w) := hFree₁
        haveI : ∀ w, Module.Finite k (ρ₁.obj w) := hFinite₁
        by_cases hw : w = v
        · rw [hw]; exact @reflFunctorMinus_free_eq k _ (Fin n) _ Q_rev v hv_source ρ₁ _ _ _
        · exact @reflFunctorMinus_free_ne k _ (Fin n) _ Q_rev v hv_source ρ₁ _ _ w hw

      have hFinite_fm : ∀ w, Module.Finite k
          (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin n) _
            (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q_rev v) fm w) := by
        intro w
        haveI : ∀ w, Module.Free k (ρ₁.obj w) := hFree₁
        haveI : ∀ w, Module.Finite k (ρ₁.obj w) := hFinite₁
        by_cases hw : w = v
        · rw [hw]; exact @reflFunctorMinus_finite_eq k _ (Fin n) _ Q_rev v hv_source ρ₁ _ _ _
        · exact @reflFunctorMinus_finite_ne k _ (Fin n) _ Q_rev v hv_source ρ₁ _ _ w hw

      have hIndec_fm : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ _
          (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q_rev v) fm := by
        rcases hIndec_or_zero with h | h_zero
        · exact h
        · exfalso
          obtain ⟨⟨w, hw⟩, _⟩ := hIndec₁
          suffices hs : ∀ w, Subsingleton (ρ₁.obj w) from
            absurd (hs w) (not_subsingleton_iff_nontrivial.mpr hw)
          intro w
          by_cases hw : w = v
          · rw [hw]
            refine ⟨fun a b => ?_⟩
            have hsub : ∀ (a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q_rev v),
                Subsingleton (ρ₁.obj a.1) :=
              fun ⟨m, hm⟩ => (Equiv.subsingleton_congr
                (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ (Fin n) _ Q_rev
                  v hv_source ρ₁ _ m (fun h => (hv_source m).false (h ▸ hm))).toEquiv).mp
                (h_zero m)
            haveI h_ds_ss : Subsingleton (DirectSum (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q_rev v)
                (fun a => ρ₁.obj a.1)) :=
              ⟨fun x y => DFinsupp.ext (fun a => @Subsingleton.elim _ (hsub a) _ _)⟩
            exact @Subsingleton.elim _ h_inj.subsingleton a b
          · exact (Equiv.subsingleton_congr
              (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ (Fin n) _ Q_rev
                v hv_source ρ₁ _ w hw).toEquiv).mp (h_zero w)

      have hDim_fm : ∀ w, (d w : ℤ) = ↑(fm.auxiliaryNat k w) := by
        intro w; rw [h668 w]
        show (d w : ℤ) = RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt
          (fun (a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q_rev v) => a.1) v d' w
        have hgoal : (d w : ℤ) =
            RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) v d' w := by
          rw [← hA_def, hd_eq]; exact (congr_fun hinvol_d w).symm
        rw [hgoal]; convert (congr_fun hbridge w).symm using 2

      exact hinvol ▸
        ⟨fm, hFree_fm, hFinite_fm, hIndec_fm, fun w => by
         change (d w : ℤ) = _; rw [hDim_fm w]; rfl⟩

end BackwardConstruction

universe u in








/-- Under the displayed matrix and quiver hypotheses, there exists an auxiliary representation whose vertexwise finranks realize the prescribed integer-valued function. -/
@[source_ref "Chapter6/Corollary6.8.4" (role := primary)]
theorem RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliary_exists_representation_finrank_eq
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (α : Fin n → ℤ) (hα : RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj α)
    (k : Type u) [Field k]
    {Q : @Quiver.{0, 0} (Fin n)} (hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)] :
    ∃ (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, u, 0} k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v))
      (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.AuxiliaryCondition ∧
      ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v)) := by




  set A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj with hA_def
  have hAsymm : A.IsSymm := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.matrixTransform_isSymm hDynkin.1
  suffices h : ∀ (m : ℕ) (α : Fin n → ℤ) (Q : @Quiver.{0, 0} (Fin n)),
      (∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)) →
      (∑ j, α j).toNat = m →
      RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj α →
      RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj →
      ∃ (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, u, 0} k (Fin n) _ Q)
        (_ : ∀ v, Module.Free k (ρ.obj v))
        (_ : ∀ v, Module.Finite k (ρ.obj v)),
        ρ.AuxiliaryCondition ∧ ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v)) from
    h _ α Q ‹_› rfl hα hQ
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro α Q hSS hm hα_pos hQ_orient
    letI : Quiver (Fin n) := Q
    haveI : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b) := hSS
    have hα_nonneg := hα_pos.2
    have hα_nonzero := hα_pos.1.1
    have hα_root := hα_pos.1.2
    have hsum_pos := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.one_le_sum_of_nonneg_of_ne_zero α hα_nonneg hα_nonzero
    by_cases hle : ∑ j : Fin n, α j ≤ 1
    ·
      have hα_sum : ∑ j : Fin n, α j = 1 := by omega
      obtain ⟨p, hp⟩ := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.eq_single_of_nonneg_of_sum_eq_one α hα_nonneg hα_nonzero hα_sum
      subst hp
      exact RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliary_exists_representation_finrank_eq_auxiliary_value p k
    ·
      push Not at hle
      have hd_sum2 : 2 ≤ ∑ j : Fin n, α j := by omega

      obtain ⟨i, hi_pos, hi_le⟩ :=
        RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.exists_pos_matrixMulVec_le_of_quadraticForm_eq_two hDynkin α hα_nonneg hα_nonzero hα_root hd_sum2

      set α' := RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i α with hα'_def
      have hα'_nonneg : ∀ j, 0 ≤ α' j :=
        RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_nonneg hAsymm α i hα_nonneg hi_le
      have hα'_nonzero : α' ≠ 0 :=
        RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_ne_zero_of_quadraticForm_eq_two hDynkin α i hα_root
      have hα'_B : dotProduct α' (A.mulVec α') = 2 :=
        (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.quadraticForm_coordinateReflection hDynkin α i).trans hα_root
      have hα'_positive : RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj α' :=
        ⟨⟨hα'_nonzero, hα'_B⟩, hα'_nonneg⟩
      have hα'_sum : ∑ j, α' j = (∑ j, α j) - (A.mulVec α) i :=
        RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.sum_coordinateReflection hAsymm α i
      have hα'_sum_lt : (∑ j, α' j).toNat < m := by
        have h1 : ∑ j, α' j < ∑ j, α j := by linarith
        have h2 : 0 ≤ ∑ j, α' j := Finset.sum_nonneg fun i _ => hα'_nonneg i
        omega

      let Q' := @RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q i
      have hQ'_orient : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q' adj :=
        RepresentationTheory.Quiver.MatrixOrientation.isMatrixOrientation_vertexReorientation hDynkin.1 hDynkin.2.1 hQ_orient _
      have hSS' : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q' a b) :=
        fun a b => RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_quiverHom_subsingleton i a b

      obtain ⟨ρ', hfree', hfinite', hindec', hdim'⟩ :=
        ih _ hα'_sum_lt α' Q' hSS' rfl hα'_positive hQ'_orient







      have hα'_ne_ei : α' ≠ RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n i := by
        intro heq

        have hα'j : ∀ j, j ≠ i → α' j = 0 := by
          intro j hj; rw [heq]; simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, hj]

        have hαj : ∀ j, j ≠ i → α j = 0 := by
          intro j hj
          have := hα'j j hj
          rw [hα'_def, RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_apply_of_ne α i j hj] at this
          exact this

        have hα'_sum1 : ∑ j, α' j = 1 := by
          rw [heq]; simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, Finset.sum_pi_single']
        have hAαi : (A.mulVec α) i = (∑ j, α j) - 1 := by linarith [hα'_sum]

        have hα'i : α' i = α i - (A.mulVec α) i := by
          rw [hα'_def]; exact RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_apply_self hAsymm α i
        have hα'i1 : α' i = 1 := by rw [heq]; simp [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue]
        have hαi_eq_sum : α i = ∑ j, α j := by linarith

        have hαi_ge2 : 2 ≤ α i := by linarith






        have hB_direct : dotProduct α (A.mulVec α) = 2 * α i ^ 2 := by

          have h1 : ∀ j, j ≠ i → α j * A.mulVec α j = 0 := fun j hj => by
            rw [hαj j hj, zero_mul]
          have h2 : A.mulVec α i = 2 * α i := by
            simp only [Matrix.mulVec, dotProduct]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
            have : ∀ k ∈ Finset.univ.erase i, A i k * α k = 0 :=
              fun k hk => by rw [hαj k (Finset.ne_of_mem_erase hk), mul_zero]
            rw [Finset.sum_eq_zero this, add_zero]
            have hAii : A i i = 2 := by
              change (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i i = 2
              simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
              norm_num; have := hDynkin.2.1 i; omega
            rw [hAii]
          simp only [dotProduct]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          have : ∀ j ∈ Finset.univ.erase i, α j * A.mulVec α j = 0 :=
            fun j hj => h1 j (Finset.ne_of_mem_erase hj)
          rw [Finset.sum_eq_zero this, add_zero, h2]; ring


        have hα_root_A : α ⬝ᵥ A *ᵥ α = 2 := hα_root
        have : α i ^ 2 = 1 := by linarith
        have : α i = 1 := by
          have := hα_nonneg i
          nlinarith [sq_nonneg (α i - 1)]
        omega


      have hρ'_not_simple : ¬ρ'.AuxiliaryVertexCondition i := by
        haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
        haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
        intro ⟨h1, h2⟩
        apply hα'_ne_ei; ext j
        simp only [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue, Pi.single_apply]
        by_cases hj : j = i
        · simp only [hj, ite_true]
          have := (hdim' i).symm
          rw [h1] at this; exact_mod_cast this.symm
        · simp only [hj, ite_false]
          have := (hdim' j).symm
          rw [h2 j hj] at this; exact_mod_cast this.symm






      classical

      have hinvol : @RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _
          (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q i) i = Q :=
        @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryQuiver_eq (Fin n) _ Q i

      have hinvol_α : RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i α' = α := by
        rw [hα'_def]
        exact RepresentationTheory.IntegerMatrix.ReflectionDynamics.coordinateReflection_involutive
          (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.matrixTransform_isSymm hDynkin.1)
          (RepresentationTheory.IntegerMatrix.ReflectionDynamics.standardBasis_selfPairing_eq_two hDynkin) i α




      by_cases hi_source : @RepresentationTheory.QuiverVertexPredicates.vertexCondition (Fin n) Q i
      ·
        have hi_sink_Q' : @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n) Q' i :=
          @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryBackward (Fin n) _ Q i hi_source
        haveI hFT_into : Fintype (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q' i) :=
          @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryFintypeAt _ Q' hSS' i

        have h_surj : Function.Surjective (ρ'.auxiliaryDirectSumMap i) := by
          haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
          haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
          rcases @RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrSurjective k _ (Fin n) _ Q'
            ρ' i _ _ hi_sink_Q' hindec' with hsimple | hsurj
          · exact absurd hsimple hρ'_not_simple
          · exact hsurj


        set d' := fun v => (@Module.finrank k (ρ'.obj v)
          _ (ρ'.addCommMonoid v) (ρ'.moduleInstance v) : ℤ)
        have hd_eq : d' = fun v => (α' v : ℤ) := by
          ext v; simp only [d']; exact (hdim' v).symm
        have hbridge :=
          @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_vector_maps_eq _ _
            hDynkin Q' hQ'_orient hSS' i hi_sink_Q' d'

        have hIndec_or_zero :
            @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ _
              (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q' i)
              (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ (Fin n) _ Q' i hi_sink_Q' ρ') ∨
            @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryProperty k _ _
              (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q' i)
              (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ (Fin n) _ Q' i hi_sink_Q' ρ') := by
          haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
          haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
          exact @RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary k _ _ _ Q' i hi_sink_Q' ρ' _ _ hindec'

        have h668 : ∀ v,
            ((@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ (Fin n) _ Q' i hi_sink_Q' ρ').auxiliaryNat k v : ℤ) =
            RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt (fun (a : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q' i) => a.1)
              i (fun w => (@Module.finrank k (ρ'.obj w) _ (ρ'.addCommMonoid w) (ρ'.moduleInstance w) : ℤ)) v := by
          haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
          haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
          exact @RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_surjective k _ (Fin n) _ Q' i hi_sink_Q' ρ' _ _ _ h_surj

        have hFree_fp : ∀ v, Module.Free k
            (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin n) _
              (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q' i)
              (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ (Fin n) _ Q' i hi_sink_Q' ρ') v) := by
          intro v
          haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
          haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
          by_cases hv : v = i
          · rw [hv]; exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_free_at k _ (Fin n) _ Q' i hi_sink_Q' ρ' _ _ _
          · exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_free_of_ne k _ (Fin n) _ Q' i hi_sink_Q' ρ' _ v hv

        have hFinite_fp : ∀ v, Module.Finite k
            (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin n) _
              (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q' i)
              (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ (Fin n) _ Q' i hi_sink_Q' ρ') v) := by
          intro v
          haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
          haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
          by_cases hv : v = i
          · rw [hv]; exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_finite_at k _ (Fin n) _ Q' i hi_sink_Q' ρ' _ _ _
          · exact @RepresentationTheory.AuxiliaryQuiverConstructions.auxiliaryRepresentation_finite_of_ne k _ (Fin n) _ Q' i hi_sink_Q' ρ' _ v hv

        have hIndec_fp : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ _
            (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q' i)
            (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ (Fin n) _ Q' i hi_sink_Q' ρ') := by
          rcases hIndec_or_zero with h | h_zero
          · exact h
          · exfalso
            obtain ⟨⟨v, hv⟩, _⟩ := hindec'
            suffices hs : ∀ w, Subsingleton (ρ'.obj w) from
              absurd (hs v) (not_subsingleton_iff_nontrivial.mpr hv)
            intro w
            by_cases hw : w = i
            · rw [hw]

              refine ⟨fun a b => ?_⟩
              obtain ⟨x, rfl⟩ := h_surj a
              obtain ⟨y, rfl⟩ := h_surj b
              suffices x = y by rw [this]
              have hds : ∀ z : DirectSum (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q' i)
                  (fun a => ρ'.obj a.1), z = 0 :=
                fun z => DFinsupp.ext (fun ⟨m, hm⟩ =>
                  @Subsingleton.elim _
                    (Equiv.subsingleton_congr
                      (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ (Fin n) _ Q'
                        i hi_sink_Q' ρ' m (fun h => (hi_sink_Q' m).false (h ▸ hm))).toEquiv
                      |>.mp (h_zero m)) _ _)
              exact (hds x).trans (hds y).symm
            · exact (Equiv.subsingleton_congr
                (@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentationLinearEquivOfNe k _ (Fin n) _ Q'
                  i hi_sink_Q' ρ' w hw).toEquiv).mp (h_zero w)

        have hDim_fp : ∀ v, (α v : ℤ) =
            ↑((@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ (Fin n) _ Q' i hi_sink_Q' ρ').auxiliaryNat k v) := by
          intro v; rw [h668 v]
          change (α v : ℤ) = RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt
            (fun (a : @RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt (Fin n) Q' i) => a.1) i d' v

          have hgoal : (α v : ℤ) = RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) i d' v := by
            rw [← hA_def, hd_eq]; exact (congr_fun hinvol_α v).symm
          rw [hgoal]; convert (congr_fun hbridge v).symm using 2

        exact hinvol ▸
          ⟨@RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryRepresentation k _ (Fin n) _ Q' i hi_sink_Q' ρ',
           hFree_fp, hFinite_fp, hIndec_fp, fun v => by
           change (α v : ℤ) = _; rw [hDim_fp v]; rfl⟩
      ·
        by_cases hi_sink : @RepresentationTheory.QuiverVertexPredicates.vertexProperty (Fin n) Q i
        ·
          have hi_source_Q' : @RepresentationTheory.QuiverVertexPredicates.vertexCondition (Fin n) Q' i :=
            @RepresentationTheory.Quiver.LinearAlgebra.Auxiliary.Quiver.auxiliaryForward (Fin n) _ Q i hi_sink
          haveI hFT_out : Fintype (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q' i) :=
            fintypeArrowsOutOfOfSubsingleton (Q := Q') i

          have h_inj : Function.Injective (ρ'.outgoingDirectSumMap i) := by
            haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
            haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
            rcases @RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrInjective k _ (Fin n) _ Q'
              ρ' i _ _ _ hi_source_Q' hindec' with hsimple | hinj
            · exact absurd hsimple hρ'_not_simple
            · exact hinj

          set d' := fun v => (@Module.finrank k (ρ'.obj v)
            _ (ρ'.addCommMonoid v) (ρ'.moduleInstance v) : ℤ)
          have hd_eq : d' = fun v => (α' v : ℤ) := by
            ext v; simp only [d']; exact (hdim' v).symm
          have hbridge :=
            simpleReflectionDimVector_eq_simpleReflection_source
              hDynkin hQ'_orient i hi_source_Q' d'

          let fm := @RepresentationTheory.QuiverRepresentationQuotientTransform.quotientTransformedRepresentation k _ (Fin n) _ Q' i hi_source_Q' ρ' hFT_out

          have hIndec_or_zero :
              @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ _
                (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q' i) fm ∨
              @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryProperty k _ _
                (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q' i) fm := by
            haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
            haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
            exact @RepresentationTheory.Quiver.AuxiliaryAtVertex.Quiver.auxiliary_or_after_auxiliary_of_fintype k _ _ _ Q' i hi_source_Q' ρ' _ _ _ hindec'

          have h668 : ∀ v,
              (fm.auxiliaryNat k v : ℤ) =
              RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt (fun (a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q' i) => a.1)
                i (fun w => (@Module.finrank k (ρ'.obj w) _ (ρ'.addCommMonoid w) (ρ'.moduleInstance w) : ℤ)) v := by
            haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
            haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
            exact @RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_injective k _ (Fin n) _ Q' i hi_source_Q' ρ' _ _ _ h_inj

          have hFree_fm : ∀ v, Module.Free k
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin n) _
                (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q' i) fm v) := by
            intro v
            haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
            haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
            by_cases hv : v = i
            · rw [hv]; exact @reflFunctorMinus_free_eq k _ (Fin n) _ Q' i hi_source_Q' ρ' _ _ _
            · exact @reflFunctorMinus_free_ne k _ (Fin n) _ Q' i hi_source_Q' ρ' _ _ v hv

          have hFinite_fm : ∀ v, Module.Finite k
              (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin n) _
                (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q' i) fm v) := by
            intro v
            haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
            haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
            by_cases hv : v = i
            · rw [hv]; exact @reflFunctorMinus_finite_eq k _ (Fin n) _ Q' i hi_source_Q' ρ' _ _ _
            · exact @reflFunctorMinus_finite_ne k _ (Fin n) _ Q' i hi_source_Q' ρ' _ _ v hv

          have hIndec_fm : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ _
              (@RepresentationTheory.QuiverVertexReversal.reverseAtVertex (Fin n) _ Q' i) fm := by
            rcases hIndec_or_zero with h | h_zero
            · exact h
            · exfalso
              obtain ⟨⟨v, hv⟩, _⟩ := hindec'
              suffices hs : ∀ w, Subsingleton (ρ'.obj w) from
                absurd (hs v) (not_subsingleton_iff_nontrivial.mpr hv)
              intro w
              by_cases hw : w = i
              · rw [hw]

                have hsub : ∀ (a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q' i), Subsingleton (ρ'.obj a.1) :=
                  fun ⟨m, hm⟩ => (Equiv.subsingleton_congr
                    (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ (Fin n) _ Q'
                      i hi_source_Q' ρ' _ m (fun h => (hi_source_Q' m).false (h ▸ hm))).toEquiv).mp
                    (h_zero m)
                haveI h_ds_ss : Subsingleton (DirectSum (@RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q' i)
                    (fun a => ρ'.obj a.1)) :=
                  ⟨fun x y => DFinsupp.ext (fun a => @Subsingleton.elim _ (hsub a) _ _)⟩
                exact h_inj.subsingleton
              · exact (Equiv.subsingleton_congr
                  (@RepresentationTheory.QuiverRepresentationQuotientTransform.transformedVertexEquivOfNe k _ (Fin n) _ Q'
                    i hi_source_Q' ρ' _ w hw).toEquiv).mp (h_zero w)

          have hDim_fm : ∀ v, (α v : ℤ) = ↑(fm.auxiliaryNat k v) := by
            intro v; rw [h668 v]
            change (α v : ℤ) = RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryInt
              (fun (a : @RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow (Fin n) Q' i) => a.1) i d' v
            have hgoal : (α v : ℤ) = RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) i d' v := by
              rw [← hA_def, hd_eq]; exact (congr_fun hinvol_α v).symm
            rw [hgoal]; convert (congr_fun hbridge v).symm using 2

          exact hinvol ▸
            ⟨fm, hFree_fm, hFinite_fm, hIndec_fm, fun v => by
             change (α v : ℤ) = _; rw [hDim_fm v]; rfl⟩
        ·

          obtain ⟨σ, hσ⟩ := RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_exists_list_property hDynkin hQ_orient
          obtain ⟨vertices, p, hreduce, hSinks_v⟩ :=
            exists_prefix_to_simpleRoot hDynkin hQ_orient σ hσ α hα_nonneg hα_nonzero hα_root
          exact backward_construct_rep hDynkin k vertices hQ_orient hSS hSinks_v
            α hα_nonneg hα_nonzero hα_root p hreduce
