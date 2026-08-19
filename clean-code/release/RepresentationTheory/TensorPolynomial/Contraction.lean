/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Algebra.MvPolynomial.WeightedComponents
import RepresentationTheory.Auxiliary.MutualCentralizers
import RepresentationTheory.TensorPower

/-!
# Tensor-polynomial contraction
-/

noncomputable section

namespace RepresentationTheory.TensorPolynomial.Contraction

open scoped TensorProduct
open MvPolynomial Module

variable (k N n : ℕ)

/-- An auxiliary type family indexed by natural numbers. -/
abbrev TensorPolynomial.AuxiliaryIndexType : Type := Fin N → ℂ

/-- A basis of the indexed tensor power whose vectors are indexed by functions between finite types. -/
noncomputable def TensorPolynomial.piTensorProductBasis :
    Basis (Fin n → Fin N) ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n) :=
  Basis.piTensorProduct (fun _ : Fin n => Pi.basisFun ℂ (Fin N))

/-- The polynomial-valued matrix indexed by pairs of tensor coordinates and determined by a slot assignment. -/
noncomputable def TensorPolynomial.contractionMatrix (slot : Fin n → Fin k) :
    Matrix (Fin n → Fin N) (Fin n → Fin N) (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N) :=
  fun f g => ∏ j : Fin n, MvPolynomial.X (slot j, f j, g j)

/-- The complex-linear contraction map from matrices indexed by tensor coordinates to matrix-entry polynomials. -/
noncomputable def TensorPolynomial.matrixToPolynomial (slot : Fin n → Fin k) :
    Matrix (Fin n → Fin N) (Fin n → Fin N) ℂ →ₗ[ℂ] RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N where
  toFun M := ∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
    algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N) (M f g) * TensorPolynomial.contractionMatrix k N n slot g f
  map_add' M M' := by
    simp only [Matrix.add_apply, map_add, add_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Algebra.smul_def, mul_assoc]

/-- The complex-linear map from endomorphisms of an indexed tensor power to matrix-entry polynomials determined by a slot assignment. -/
noncomputable def TensorPolynomial.endomorphismToPolynomial (slot : Fin n → Fin k) :
    Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n) →ₗ[ℂ] RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N :=
  TensorPolynomial.matrixToPolynomial k N n slot ∘ₗ
    (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)).toLinearMap

/-- The polynomial attached to an endomorphism is the sum of its matrix coefficients multiplied by the corresponding entries of the polynomial-valued matrix. -/
theorem TensorPolynomial.endomorphismToPolynomial_apply (slot : Fin n → Fin k)
    (M : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n)) :
    TensorPolynomial.endomorphismToPolynomial k N n slot M =
      ∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
        algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N)
            (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) M f g)
          * TensorPolynomial.contractionMatrix k N n slot g f := by
  rfl

/-- The contraction of an endomorphism equals the matrix contraction applied to its matrix in the indexed tensor-product basis. -/
theorem TensorPolynomial.endomorphismToPolynomial_eq_matrixToPolynomial (slot : Fin n → Fin k)
    (M : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n)) :
    TensorPolynomial.endomorphismToPolynomial k N n slot M
      = TensorPolynomial.matrixToPolynomial k N n slot (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) M) :=
  rfl

/-- Matrix contraction is the trace of the scalar-extended input matrix multiplied by the polynomial-valued contraction matrix. -/
theorem TensorPolynomial.matrixToPolynomial_apply (slot : Fin n → Fin k)
    (A : Matrix (Fin n → Fin N) (Fin n → Fin N) ℂ) :
    TensorPolynomial.matrixToPolynomial k N n slot A
      = Matrix.trace ((A.map (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N)))
          * TensorPolynomial.contractionMatrix k N n slot) := by
  change (∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
      algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N) (A f g) * TensorPolynomial.contractionMatrix k N n slot g f) = _
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.map_apply]

/-- A matrix entry of the tensor-power map is the product of the corresponding entries of the original matrix over all tensor positions. -/
theorem TensorPolynomial.toMatrix_piTensorProduct_map_apply (h : Matrix (Fin N) (Fin N) ℂ) (p q : Fin n → Fin N) :
    LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
        (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin h)) p q
      = ∏ j : Fin n, h (p j) (q j) := by
  rw [LinearMap.toMatrix_apply, TensorPolynomial.piTensorProductBasis, Basis.piTensorProduct_apply,
    PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← LinearMap.toMatrix_apply (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))
        (Matrix.mulVecLin h) (p j) (q j), LinearMap.toMatrix_eq_toMatrix',
      ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

/-- The action on a matrix coordinate is the sum obtained by multiplying the variable matrix on the left by the given invertible matrix and on the right by its inverse. -/
theorem TensorPolynomial.matrixVariable_action_apply (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) (i : Fin k) (r c : Fin N) :
    RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g (MvPolynomial.X (i, r, c))
      = ∑ s : Fin N, ∑ t : Fin N,
          algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N) ((↑g : Matrix (Fin N) (Fin N) ℂ) r s)
            * MvPolynomial.X (i, s, t)
            * algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N) ((↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ) t c) := by
  rw [RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom, MvPolynomial.aeval_X]
  simp only [Matrix.mul_apply, Matrix.map_apply, RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.finIndexedMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Acting on every entry of the contraction matrix agrees with multiplication by the scalar-extended tensor-power matrices on the left and right. -/
theorem TensorPolynomial.contractionMatrix_map_matrixAction (slot : Fin n → Fin k)
    (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) :
    (TensorPolynomial.contractionMatrix k N n slot).map (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g)
      = (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
            (PiTensorProduct.map (fun _ : Fin n =>
              Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)))).map
              (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))
        * TensorPolynomial.contractionMatrix k N n slot
        * (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
            (PiTensorProduct.map (fun _ : Fin n =>
              Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ)))).map
              (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N)) := by
  classical
  refine Matrix.ext fun e f => ?_

  rw [Matrix.map_apply]
  change RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g (∏ j : Fin n, MvPolynomial.X (slot j, e j, f j)) = _
  rw [map_prod]
  simp_rw [TensorPolynomial.matrixVariable_action_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_

  simp only [Matrix.map_apply, TensorPolynomial.toMatrix_piTensorProduct_map_apply, TensorPolynomial.contractionMatrix]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← map_prod, ← map_prod]

/-- Applying the contraction map after conjugating an endomorphism by tensor powers agrees with the induced matrix action on its polynomial. -/
theorem TensorPolynomial.endomorphismToPolynomial_conjugate (slot : Fin n → Fin k) (g : (Matrix (Fin N) (Fin N) ℂ)ˣ)
    (M : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n)) :
    TensorPolynomial.endomorphismToPolynomial k N n slot
        (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
          * M
          * PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)))
      = RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g (TensorPolynomial.endomorphismToPolynomial k N n slot M) := by
  set G : Matrix (Fin n → Fin N) (Fin n → Fin N) ℂ :=
    LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
      (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)))
    with hG
  set G' : Matrix (Fin n → Fin N) (Fin n → Fin N) ℂ :=
    LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
      (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ)))
    with hG'
  set A : Matrix (Fin n → Fin N) (Fin n → Fin N) ℂ :=
    LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) M with hA

  have hlhs : TensorPolynomial.endomorphismToPolynomial k N n slot
      (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
        * M
        * PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)))
      = Matrix.trace ((G'.map (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))
            * A.map (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))
            * G.map (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))) * TensorPolynomial.contractionMatrix k N n slot) := by
    rw [TensorPolynomial.endomorphismToPolynomial_eq_matrixToPolynomial, LinearMap.toMatrix_mul, LinearMap.toMatrix_mul,
      TensorPolynomial.matrixToPolynomial_apply, ← hG, ← hG', ← hA, Matrix.map_mul, Matrix.map_mul]

  have hrhs : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g (TensorPolynomial.endomorphismToPolynomial k N n slot M)
      = Matrix.trace ((G'.map (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))
            * A.map (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))
            * G.map (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))) * TensorPolynomial.contractionMatrix k N n slot) := by
    rw [TensorPolynomial.endomorphismToPolynomial_eq_matrixToPolynomial, ← hA, TensorPolynomial.matrixToPolynomial_apply,
      AddMonoidHom.map_trace (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g), Matrix.map_mul,
      TensorPolynomial.contractionMatrix_map_matrixAction, ← hG, ← hG']

    have hAfix : (A.map (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))).map (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g)
        = A.map (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N)) := by
      rw [Matrix.map_map]
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Function.comp_apply, AlgHom.commutes]
    rw [hAfix, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [hlhs, hrhs]

private lemma exists_fun_sum_single {ι β : Type*} [Nonempty β] (S : Finset ι) :
    ∀ m : β →₀ ℕ, m.sum (fun _ x => x) = S.card →
      ∃ h : ι → β, ∑ j ∈ S, Finsupp.single (h j) 1 = m := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.card_empty] at hm
    refine ⟨fun _ => Classical.arbitrary β, ?_⟩
    rw [Finset.sum_empty]
    symm
    rw [← Finsupp.support_eq_empty]
    by_contra hne
    obtain ⟨v, hv⟩ := Finset.nonempty_of_ne_empty hne
    have hpos : 0 < m.sum (fun _ x => x) := by
      rw [Finsupp.sum]
      exact Finset.sum_pos' (fun i _ => Nat.zero_le _)
        ⟨v, hv, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hv)⟩
    omega
  | insert a S' ha ih =>
    intro m hm
    rw [Finset.card_insert_of_notMem ha] at hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [Finsupp.sum_zero_index] at hm
      omega
    obtain ⟨b, hb⟩ := Finsupp.support_nonempty_iff.mpr hm0
    have hmb : 1 ≤ m b := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.1 hb)
    have hle : Finsupp.single b 1 ≤ m := by
      rw [Finsupp.le_iff]
      intro i hi
      have hi' : i = b := Finset.mem_singleton.1 (Finsupp.support_single_subset hi)
      subst hi'
      rw [Finsupp.single_eq_same]
      exact hmb
    set m' := m - Finsupp.single b 1 with hm'def
    have hsplit : m = Finsupp.single b 1 + m' := by
      rw [hm'def, add_tsub_cancel_of_le hle]
    have hm'sum : m'.sum (fun _ x => x) = S'.card := by
      have hadd : m.sum (fun _ x => x)
          = (Finsupp.single b 1).sum (fun _ x => x) + m'.sum (fun _ x => x) := by
        conv_lhs => rw [hsplit]
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      rw [Finsupp.sum_single_index rfl] at hadd
      omega
    obtain ⟨h', hh'⟩ := ih m' hm'sum
    refine ⟨Function.update h' a b, ?_⟩
    rw [Finset.sum_insert ha, Function.update_self]
    have hcong : ∑ j ∈ S', Finsupp.single (Function.update h' a b j) 1
        = ∑ j ∈ S', Finsupp.single (h' j) 1 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (by rintro rfl; exact ha hj)]
    rw [hcong, hh']
    exact hsplit.symm

private lemma curry_sum_eq_weight (u : (Fin k × Fin N × Fin N) →₀ ℕ) (i : Fin k) :
    (u.curry i).sum (fun _ x => x) = (Finsupp.weight (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) u) i := by
  classical
  induction u using Finsupp.induction_linear with
  | zero =>
    have hz : (0 : (Fin k × Fin N × Fin N) →₀ ℕ).curry = 0 := by
      rw [← Finsupp.coe_curryAddEquiv]; exact map_zero _
    rw [hz, Finsupp.zero_apply, Finsupp.sum_zero_index, map_zero, Finsupp.zero_apply]
  | add x y ihx ihy =>
    have hc : (x + y).curry i = x.curry i + y.curry i := by
      have h := map_add Finsupp.curryAddEquiv x y
      simp only [Finsupp.coe_curryAddEquiv] at h
      rw [h, Finsupp.add_apply]
    rw [hc, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ihx, ihy,
      map_add, Finsupp.add_apply]
  | single v c =>
    rw [Finsupp.curry_single, Finsupp.weight_single]
    simp only [RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight]
    by_cases h : v.1 = i
    · rw [Finsupp.single_apply, if_pos h, Finsupp.sum_single_index rfl,
        Finsupp.smul_apply, Finsupp.single_apply, if_pos h, smul_eq_mul, mul_one]
    · rw [Finsupp.single_apply, if_neg h, Finsupp.sum_zero_index,
        Finsupp.smul_apply, Finsupp.single_apply, if_neg h, smul_zero]

private lemma exists_fg_realizes (slot : Fin n → Fin k) (u : (Fin k × Fin N × Fin N) →₀ ℕ)
    (hcard : ∀ i : Fin k,
      (u.curry i).sum (fun _ x => x) = (Finset.univ.filter fun j => slot j = i).card) :
    ∃ f g : Fin n → Fin N, ∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1 = u := by
  classical
  rcases isEmpty_or_nonempty (Fin N × Fin N) with hE | hNE
  ·
    have hemptyProd : IsEmpty (Fin k × Fin N × Fin N) := ⟨fun p => hE.false p.2⟩
    have hu0 : u = 0 := by ext v; exact (hemptyProd.false v).elim
    have hn : IsEmpty (Fin n) := by
      refine ⟨fun j => ?_⟩
      have hmem : j ∈ Finset.univ.filter fun j' => slot j' = slot j := by simp
      have hpos : 0 < (Finset.univ.filter fun j' => slot j' = slot j).card :=
        Finset.card_pos.mpr ⟨j, hmem⟩
      have hz : (u.curry (slot j)).sum (fun _ x => x) = 0 := by
        have : u.curry (slot j) = 0 := by ext b; exact (hE.false b).elim
        rw [this]; simp
      rw [hcard (slot j)] at hz
      omega
    haveI := hn
    exact ⟨fun j => (hn.false j).elim, fun j => (hn.false j).elim, by rw [hu0]; simp⟩
  · haveI := hNE
    have perfib : ∀ i : Fin k, ∃ h : Fin n → Fin N × Fin N,
        ∑ j ∈ Finset.univ.filter (fun j => slot j = i), Finsupp.single (h j) 1 = u.curry i :=
      fun i => exists_fun_sum_single _ _ (hcard i)
    choose h hh using perfib
    refine ⟨fun j => (h (slot j) j).2, fun j => (h (slot j) j).1, ?_⟩
    have key : ∑ j : Fin n, Finsupp.single (slot j) (Finsupp.single (h (slot j) j) (1 : ℕ))
        = u.curry := by
      refine Finsupp.ext fun i => ?_
      rw [Finsupp.finsetSum_apply]
      simp only [Finsupp.single_apply]
      rw [← Finset.sum_filter]
      have hrw : ∑ j ∈ Finset.univ.filter (fun j => slot j = i),
            Finsupp.single (h (slot j) j) 1
          = ∑ j ∈ Finset.univ.filter (fun j => slot j = i), Finsupp.single (h i j) 1 := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_filter] at hj
        rw [hj.2]
      rw [hrw]
      exact hh i
    apply Finsupp.curryAddEquiv.injective
    rw [map_sum]
    simp only [Finsupp.coe_curryAddEquiv, Finsupp.curry_single]
    exact key

private lemma prod_monomial_single {ι : Type*} (s : Finset ι)
    (v : ι → (Fin k × Fin N × Fin N)) :
    (∏ j ∈ s, MvPolynomial.monomial (Finsupp.single (v j) 1) (1 : ℂ))
      = MvPolynomial.monomial (∑ j ∈ s, Finsupp.single (v j) 1) (1 : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact MvPolynomial.one_def
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, MvPolynomial.monomial_mul, one_mul]

/-- Every weighted-homogeneous polynomial whose multidegree records the slot multiplicities lies in the range of the endomorphism contraction map. -/
theorem TensorPolynomial.weightedHomogeneous_mem_range_endomorphismToPolynomial
    (d : Fin k →₀ ℕ) (slot : Fin n → Fin k)
    (hslot : ∀ i : Fin k, (Finset.univ.filter fun j => slot j = i).card = d i)
    {p : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N}
    (hhom : IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) p d) :
    p ∈ LinearMap.range (TensorPolynomial.endomorphismToPolynomial k N n slot) := by
  classical

  have hmono : ∀ f g : Fin n → Fin N,
      (∏ j : Fin n, (MvPolynomial.X (slot j, g j, f j) : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))
        ∈ LinearMap.range (TensorPolynomial.endomorphismToPolynomial k N n slot) := by
    intro f g
    refine ⟨(LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)).symm (Matrix.single f g 1), ?_⟩
    rw [TensorPolynomial.endomorphismToPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    change ∑ a : Fin n → Fin N, ∑ b : Fin n → Fin N,
        algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N) (Matrix.single f g 1 a b)
          * TensorPolynomial.contractionMatrix k N n slot b a
      = ∏ j : Fin n, MvPolynomial.X (slot j, g j, f j)
    rw [Finset.sum_eq_single_of_mem f (Finset.mem_univ f)]
    · rw [Finset.sum_eq_single_of_mem g (Finset.mem_univ g)]
      · rw [Matrix.single_apply_same, map_one, one_mul]
        rfl
      · intro b _ hb
        rw [Matrix.single_apply_of_col_ne f f (Ne.symm hb) 1, map_zero, zero_mul]
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Matrix.single_apply_of_row_ne (Ne.symm ha) g b 1, map_zero, zero_mul]

  rw [← MvPolynomial.support_sum_monomial_coeff p]
  refine Submodule.sum_mem _ fun u hu => ?_
  have hwt : Finsupp.weight (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) u = d := hhom (MvPolynomial.mem_support_iff.1 hu)
  obtain ⟨f, g, hfg⟩ := exists_fg_realizes k N n slot u fun i => by
    rw [curry_sum_eq_weight, hwt]; exact (hslot i).symm
  have hmem : MvPolynomial.monomial u (1 : ℂ) ∈ LinearMap.range (TensorPolynomial.endomorphismToPolynomial k N n slot) := by
    have hX : ∀ j : Fin n, (MvPolynomial.X (slot j, g j, f j) : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N)
        = MvPolynomial.monomial (Finsupp.single (slot j, g j, f j) 1) 1 := fun j => by
      rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
    have hprod : (∏ j : Fin n, (MvPolynomial.X (slot j, g j, f j) : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))
        = MvPolynomial.monomial u 1 := by
      simp_rw [hX]
      rw [prod_monomial_single, hfg]
    rw [← hprod]
    exact hmono f g
  rw [show MvPolynomial.monomial u (MvPolynomial.coeff u p)
      = MvPolynomial.coeff u p • MvPolynomial.monomial u (1 : ℂ) by
    rw [← LinearMap.map_smul, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ hmem

open scoped Classical in

/-- The finite set of permutations associated with an assignment between finite index types. -/
noncomputable def TensorPolynomial.slotPermutations (slot : Fin n → Fin k) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun τ => slot ∘ τ = slot

/-- The identity permutation belongs to the finite set associated with every slot assignment. -/
theorem TensorPolynomial.one_mem_slotPermutations (slot : Fin n → Fin k) : (1 : Equiv.Perm (Fin n)) ∈ TensorPolynomial.slotPermutations k n slot := by
  classical
  rw [TensorPolynomial.slotPermutations, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by ext j; rfl⟩

/-- The finite set of permutations associated with any slot assignment has nonzero cardinality. -/
theorem TensorPolynomial.slotPermutations_card_ne_zero (slot : Fin n → Fin k) : (TensorPolynomial.slotPermutations k n slot).card ≠ 0 := by
  exact Finset.card_ne_zero.mpr ⟨1, TensorPolynomial.one_mem_slotPermutations k n slot⟩

/-- An endomorphism-valued symmetrization operation determined by a slot assignment. -/
noncomputable def TensorPolynomial.symmetrizeEndomorphism (slot : Fin n → Fin k)
    (M : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n)) :
    Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n) :=
  ((TensorPolynomial.slotPermutations k n slot).card : ℂ)⁻¹ • ∑ τ ∈ TensorPolynomial.slotPermutations k n slot,
    (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ).toLinearMap * M
      * (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ⁻¹).toLinearMap

/-- The matrix entry of a tensor-factor permutation is one exactly when the row index is the inverse-permuted column index, and zero otherwise. -/
theorem TensorPolynomial.toMatrix_tensorPermutation_apply (σ : Equiv.Perm (Fin n)) (p q : Fin n → Fin N) :
    LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
        (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n σ).toLinearMap p q
      = if p = q ∘ (σ⁻¹ : Equiv.Perm (Fin n)) then 1 else 0 := by
  classical
  rw [LinearMap.toMatrix_apply]
  change (TensorPolynomial.piTensorProductBasis N n).repr
      ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n σ) (TensorPolynomial.piTensorProductBasis N n q)) p = _
  rw [TensorPolynomial.piTensorProductBasis, Basis.piTensorProduct_apply, RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv, PiTensorProduct.reindex_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  simp only [Basis.repr_self, Finsupp.single_apply]
  by_cases h : p = q ∘ (σ⁻¹ : Equiv.Perm (Fin n))
  · rw [if_pos h]
    refine Finset.prod_eq_one fun i _ => if_pos ?_
    subst h; rfl
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) (if_neg fun heq => ?_)
    exact hi heq.symm

/-- A permutation preserving the slot assignment leaves the contraction matrix fixed under multiplication by the associated inverse and forward permutation matrices. -/
theorem TensorPolynomial.permutationMatrix_mul_contractionMatrix_mul (slot : Fin n → Fin k)
    {τ : Equiv.Perm (Fin n)} (hτ : slot ∘ τ = slot) :
    (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
          (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ⁻¹).toLinearMap).map
          (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))
        * TensorPolynomial.contractionMatrix k N n slot
        * (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
          (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ).toLinearMap).map
          (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N))
      = TensorPolynomial.contractionMatrix k N n slot := by
  classical
  refine Matrix.ext fun e f => ?_

  have hpermL : ∀ a : Fin n → Fin N,
      (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
          (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ).toLinearMap).map
          (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N)) a f
        = if a = f ∘ (τ⁻¹ : Equiv.Perm (Fin n)) then (1 : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N) else 0 := by
    intro a
    rw [Matrix.map_apply, TensorPolynomial.toMatrix_tensorPermutation_apply]
    by_cases h : a = f ∘ (τ⁻¹ : Equiv.Perm (Fin n)) <;> simp [h]
  have hpermR : ∀ b : Fin n → Fin N,
      (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
          (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ⁻¹).toLinearMap).map
          (algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N)) e b
        = if e = b ∘ (τ : Equiv.Perm (Fin n)) then (1 : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N) else 0 := by
    intro b
    rw [Matrix.map_apply, TensorPolynomial.toMatrix_tensorPermutation_apply, inv_inv]
    by_cases h : e = b ∘ (τ : Equiv.Perm (Fin n)) <;> simp [h]
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (f ∘ (τ⁻¹ : Equiv.Perm (Fin n)))]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e ∘ (τ⁻¹ : Equiv.Perm (Fin n)))]
    · rw [hpermR (e ∘ (τ⁻¹ : Equiv.Perm (Fin n))), hpermL (f ∘ (τ⁻¹ : Equiv.Perm (Fin n))),
        if_pos (show e = (e ∘ (τ⁻¹ : Equiv.Perm (Fin n))) ∘ (τ : Equiv.Perm (Fin n)) by
          funext j; simp),
        if_pos rfl, one_mul, mul_one]

      simp only [TensorPolynomial.contractionMatrix]
      rw [← Equiv.prod_comp τ (fun j => MvPolynomial.X
        (slot j, (e ∘ (τ⁻¹ : Equiv.Perm (Fin n))) j, (f ∘ (τ⁻¹ : Equiv.Perm (Fin n))) j))]
      have hinv : ∀ x : Fin n, (τ⁻¹ : Equiv.Perm (Fin n)) (τ x) = x :=
        fun x => Equiv.symm_apply_apply τ x
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Function.comp_apply, hinv, show slot (τ j) = slot j from congrFun hτ j]
    · intro b _ hbne
      rw [hpermR b, if_neg (fun he => hbne (by
        funext j; have := congrFun he ((τ⁻¹ : Equiv.Perm (Fin n)) j); simpa using this.symm)),
        zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ hane
    rw [hpermL a, if_neg hane, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Conjugation by the tensor-factor maps of an admissible permutation leaves the associated polynomial unchanged. -/
theorem TensorPolynomial.endomorphismToPolynomial_perm_conjugate (slot : Fin n → Fin k)
    {τ : Equiv.Perm (Fin n)} (hτ : τ ∈ TensorPolynomial.slotPermutations k n slot)
    (M : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n)) :
    TensorPolynomial.endomorphismToPolynomial k N n slot
        ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ).toLinearMap * M
          * (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ⁻¹).toLinearMap)
      = TensorPolynomial.endomorphismToPolynomial k N n slot M := by
  classical
  have hslotτ : slot ∘ τ = slot := by
    rw [TensorPolynomial.slotPermutations, Finset.mem_filter] at hτ; exact hτ.2
  rw [TensorPolynomial.endomorphismToPolynomial_eq_matrixToPolynomial, TensorPolynomial.endomorphismToPolynomial_eq_matrixToPolynomial,
    LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, TensorPolynomial.matrixToPolynomial_apply, TensorPolynomial.matrixToPolynomial_apply,
    Matrix.map_mul, Matrix.map_mul]
  set C := algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N)
  set PL := (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
    (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ).toLinearMap).map C with hPL
  set PR := (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
    (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ⁻¹).toLinearMap).map C with hPR
  set A := (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) M).map C with hA
  set G := TensorPolynomial.contractionMatrix k N n slot with hG

  have key : PR * G * PL = G := TensorPolynomial.permutationMatrix_mul_contractionMatrix_mul k N n slot hslotτ
  have hassoc : PL * A * PR * G = PL * (A * PR * G) := by
    rw [mul_assoc (PL * A) PR G, mul_assoc PL A (PR * G), ← mul_assoc A PR G]
  rw [hassoc, Matrix.trace_mul_comm,
    show A * PR * G * PL = A * (PR * G * PL) from by
      rw [mul_assoc (A * PR) G PL, mul_assoc A PR (G * PL), ← mul_assoc PR G PL],
    key]

/-- Slot symmetrization does not change the polynomial obtained from an endomorphism. -/
theorem TensorPolynomial.endomorphismToPolynomial_symmetrize (slot : Fin n → Fin k)
    (M : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n)) :
    TensorPolynomial.endomorphismToPolynomial k N n slot (TensorPolynomial.symmetrizeEndomorphism k N n slot M) = TensorPolynomial.endomorphismToPolynomial k N n slot M := by
  classical
  rw [TensorPolynomial.symmetrizeEndomorphism, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun τ hτ => TensorPolynomial.endomorphismToPolynomial_perm_conjugate k N n slot hτ M]
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast TensorPolynomial.slotPermutations_card_ne_zero k n slot), one_smul]

/-- Slot symmetrization commutes with conjugation by tensor powers of an invertible matrix. -/
theorem TensorPolynomial.symmetrizeEndomorphism_conjugate (slot : Fin n → Fin k) (g : (Matrix (Fin N) (Fin N) ℂ)ˣ)
    (M : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n)) :
    TensorPolynomial.symmetrizeEndomorphism k N n slot
        (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
          * M
          * PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)))
      = PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
        * TensorPolynomial.symmetrizeEndomorphism k N n slot M
        * PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)) := by
  classical
  set Q := PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
    with hQ
  set P := PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ))
    with hP
  rw [TensorPolynomial.symmetrizeEndomorphism, TensorPolynomial.symmetrizeEndomorphism, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ hτ => ?_
  set Pτ := (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ).toLinearMap with hPτ
  set Pτ' := (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ⁻¹).toLinearMap with hPτ'
  have hcQ : Commute Pτ Q := by
    rw [Commute, SemiconjBy, hPτ, hQ, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv_comp_factorwiseMap ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ
      (Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
  have hcP' : Commute Pτ' P := by
    rw [Commute, SemiconjBy, hPτ', hP, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv_comp_factorwiseMap ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ⁻¹
      (Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ))

  simp only [mul_assoc]
  rw [show P * Pτ' = Pτ' * P from hcP'.symm.eq, ← mul_assoc Pτ Q,
    show Pτ * Q = Q * Pτ from hcQ.eq, mul_assoc Q Pτ]

private theorem reynolds_sub (slot : Fin n → Fin k)
    (M M' : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n)) :
    TensorPolynomial.symmetrizeEndomorphism k N n slot (M - M') = TensorPolynomial.symmetrizeEndomorphism k N n slot M - TensorPolynomial.symmetrizeEndomorphism k N n slot M' := by
  classical
  rw [TensorPolynomial.symmetrizeEndomorphism, TensorPolynomial.symmetrizeEndomorphism, TensorPolynomial.symmetrizeEndomorphism, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_sub, sub_mul]

private theorem toMatrix_reynolds_summand (slot : Fin n → Fin k)
    (M : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n)) (τ : Equiv.Perm (Fin n))
    (a b : Fin n → Fin N) :
    LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
        ((RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ).toLinearMap * M
          * (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ⁻¹).toLinearMap) a b
      = LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) M (a ∘ τ) (b ∘ τ) := by
  classical
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul]
  set A := LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) M with hA
  have hPLval : ∀ p : Fin n → Fin N,
      LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
          (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ).toLinearMap a p
        = if a = p ∘ (τ⁻¹ : Equiv.Perm (Fin n)) then (1 : ℂ) else 0 := by
    intro p; rw [TensorPolynomial.toMatrix_tensorPermutation_apply]
  have hPRval : ∀ q : Fin n → Fin N,
      LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)
          (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv ℂ (TensorPolynomial.AuxiliaryIndexType N) n τ⁻¹).toLinearMap q b
        = if q = b ∘ (τ : Equiv.Perm (Fin n)) then (1 : ℂ) else 0 := by
    intro q; rw [TensorPolynomial.toMatrix_tensorPermutation_apply, inv_inv]
  rw [Matrix.mul_apply, Finset.sum_eq_single (b ∘ (τ : Equiv.Perm (Fin n)))]
  · rw [hPRval, if_pos rfl, mul_one, Matrix.mul_apply,
      Finset.sum_eq_single (a ∘ (τ : Equiv.Perm (Fin n)))]
    · rw [hPLval, if_pos (show a = (a ∘ (τ : Equiv.Perm (Fin n))) ∘ (τ⁻¹ : Equiv.Perm (Fin n)) by
          funext j; simp), one_mul]
    · intro p _ hp
      rw [hPLval, if_neg (fun he => hp (by
        funext j; have := congrFun he ((τ : Equiv.Perm (Fin n)) j); simpa using this.symm)),
        zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro q _ hq
    rw [hPRval, if_neg hq, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem toMatrix_reynolds (slot : Fin n → Fin k)
    (M : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n)) (a b : Fin n → Fin N) :
    LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.symmetrizeEndomorphism k N n slot M) a b
      = ((TensorPolynomial.slotPermutations k n slot).card : ℂ)⁻¹
        • ∑ τ ∈ TensorPolynomial.slotPermutations k n slot,
            LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) M (a ∘ τ) (b ∘ τ) := by
  classical
  rw [TensorPolynomial.symmetrizeEndomorphism, map_smul, map_sum, Matrix.smul_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact toMatrix_reynolds_summand k N n slot M τ a b

private theorem reynolds_block_symmetric (slot : Fin n → Fin k)
    (M : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n)) {ρ : Equiv.Perm (Fin n)}
    (hρ : ρ ∈ TensorPolynomial.slotPermutations k n slot) (a b : Fin n → Fin N) :
    LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.symmetrizeEndomorphism k N n slot M)
        (a ∘ ρ) (b ∘ ρ)
      = LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.symmetrizeEndomorphism k N n slot M) a b := by
  classical
  have hslotρ : slot ∘ ρ = slot := by rw [TensorPolynomial.slotPermutations, Finset.mem_filter] at hρ; exact hρ.2
  have hmem : ∀ σ : Equiv.Perm (Fin n), σ ∈ TensorPolynomial.slotPermutations k n slot →
      ρ * σ ∈ TensorPolynomial.slotPermutations k n slot := by
    intro σ hσ
    rw [TensorPolynomial.slotPermutations, Finset.mem_filter] at hσ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    funext j
    change slot (ρ (σ j)) = slot j
    have h1 : slot (ρ (σ j)) = slot (σ j) := congrFun hslotρ (σ j)
    have h2 : slot (σ j) = slot j := congrFun hσ.2 j
    rw [h1, h2]
  have hslotρinv : slot ∘ (ρ⁻¹ : Equiv.Perm (Fin n)) = slot := by
    funext j
    have h1 : slot (ρ (ρ⁻¹ j)) = slot (ρ⁻¹ j) := congrFun hslotρ (ρ⁻¹ j)
    have hρρ : ρ (ρ⁻¹ j) = j := Equiv.apply_symm_apply ρ j
    rw [hρρ] at h1
    exact h1.symm
  have hmemInv : ∀ σ : Equiv.Perm (Fin n), σ ∈ TensorPolynomial.slotPermutations k n slot →
      ρ⁻¹ * σ ∈ TensorPolynomial.slotPermutations k n slot := by
    intro σ hσ
    rw [TensorPolynomial.slotPermutations, Finset.mem_filter] at hσ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    funext j
    change slot (ρ⁻¹ (σ j)) = slot j
    have h1 : slot (ρ⁻¹ (σ j)) = slot (σ j) := congrFun hslotρinv (σ j)
    have h2 : slot (σ j) = slot j := congrFun hσ.2 j
    rw [h1, h2]
  have hsum : (∑ τ ∈ TensorPolynomial.slotPermutations k n slot,
        LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) M ((a ∘ ρ) ∘ τ) ((b ∘ ρ) ∘ τ))
      = ∑ τ ∈ TensorPolynomial.slotPermutations k n slot,
        LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) M (a ∘ τ) (b ∘ τ) := by
    refine Finset.sum_nbij' (fun τ => ρ * τ) (fun τ => ρ⁻¹ * τ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ; exact hmem σ hσ
    · intro σ hσ; exact hmemInv σ hσ
    · intro σ _; rw [← mul_assoc, inv_mul_cancel, one_mul]
    · intro σ _; rw [← mul_assoc, mul_inv_cancel, one_mul]
    · intro σ _
      congr 1 <;>
        · funext j; simp only [Function.comp_apply, Equiv.Perm.mul_apply]
  rw [toMatrix_reynolds, toMatrix_reynolds, hsum]

private theorem genericTensorMatrix_eq_monomial (slot : Fin n → Fin k) (g f : Fin n → Fin N) :
    TensorPolynomial.contractionMatrix k N n slot g f
      = MvPolynomial.monomial (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) (1 : ℂ) := by
  classical
  rw [TensorPolynomial.contractionMatrix]
  have hX : ∀ j : Fin n, (MvPolynomial.X (slot j, g j, f j) : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N)
      = MvPolynomial.monomial (Finsupp.single (slot j, g j, f j) 1) 1 := fun j => by
    rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
  simp_rw [hX]
  rw [prod_monomial_single]

private noncomputable def matchingPerm {α : Type*} [DecidableEq α] :
    ∀ {m : ℕ} (f g : Fin m → α),
      Multiset.map f (Finset.univ : Finset (Fin m)).val =
        Multiset.map g (Finset.univ : Finset (Fin m)).val →
      {σ : Equiv.Perm (Fin m) // g = f ∘ σ}
  | 0, _, g, _ => ⟨Equiv.refl _, funext fun i => i.elim0⟩
  | m + 1, f, g, h =>
      let hg0_mem : g 0 ∈ Multiset.map f (Finset.univ : Finset (Fin (m+1))).val := by
        rw [h]; exact Multiset.mem_map.mpr ⟨0, Finset.mem_univ_val _, rfl⟩
      let l₀ : Fin (m+1) := Classical.choose (Multiset.mem_map.mp hg0_mem)
      let l₀_spec :
        l₀ ∈ (Finset.univ : Finset (Fin (m+1))).val ∧ f l₀ = g 0 :=
        Classical.choose_spec (Multiset.mem_map.mp hg0_mem)
      let hl₀ : f l₀ = g 0 := l₀_spec.2
      let f' : Fin m → α := f ∘ l₀.succAbove
      let g' : Fin m → α := g ∘ Fin.succ
      let hpeel_f : Multiset.map f (Finset.univ : Finset (Fin (m+1))).val =
          f l₀ ::ₘ Multiset.map f' (Finset.univ : Finset (Fin m)).val := by
        conv_lhs => rw [Fin.univ_succAbove m l₀]
        simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val,
          Multiset.map_map, Fin.coe_succAboveEmb]
        rfl
      let hpeel_g : Multiset.map g (Finset.univ : Finset (Fin (m+1))).val =
          g 0 ::ₘ Multiset.map g' (Finset.univ : Finset (Fin m)).val := by
        conv_lhs => rw [Fin.univ_succAbove m 0]
        simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val,
          Multiset.map_map, Fin.coe_succAboveEmb, Fin.succAbove_zero]
        rfl
      let hms : Multiset.map f' (Finset.univ : Finset (Fin m)).val =
          Multiset.map g' (Finset.univ : Finset (Fin m)).val := by
        have hh : f l₀ ::ₘ Multiset.map f' (Finset.univ : Finset (Fin m)).val =
            f l₀ ::ₘ Multiset.map g' (Finset.univ : Finset (Fin m)).val := by
          rw [← hpeel_f, h, hpeel_g, hl₀]
        exact (Multiset.cons_inj_right _).mp hh
      let σ'_pkg := matchingPerm f' g' hms
      let σ' : Equiv.Perm (Fin m) := σ'_pkg.1
      let hσ' : g' = f' ∘ σ' := σ'_pkg.2
      let σ_fn : Fin (m+1) → Fin (m+1) :=
        Fin.cases l₀ (fun j => l₀.succAbove (σ' j))
      let hinj : Function.Injective σ_fn := by
        intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => rfl
          | succ b =>
            exfalso
            change l₀ = l₀.succAbove (σ' b) at hij
            exact (Fin.succAbove_ne l₀ (σ' b)) hij.symm
        | succ a =>
          induction j using Fin.cases with
          | zero =>
            exfalso
            change l₀.succAbove (σ' a) = l₀ at hij
            exact (Fin.succAbove_ne l₀ (σ' a)) hij
          | succ b =>
            change l₀.succAbove (σ' a) = l₀.succAbove (σ' b) at hij
            have h1 : σ' a = σ' b := l₀.succAbove_right_injective hij
            have h2 : a = b := σ'.injective h1
            exact congrArg Fin.succ h2
      let hbij : Function.Bijective σ_fn :=
        Finite.injective_iff_bijective.mp hinj
      ⟨Equiv.ofBijective σ_fn hbij, by
        funext i
        induction i using Fin.cases with
        | zero =>
          change g 0 = f (σ_fn 0)
          change g 0 = f l₀
          exact hl₀.symm
        | succ j =>
          change g (Fin.succ j) = f (σ_fn (Fin.succ j))
          change g (Fin.succ j) = f (l₀.succAbove (σ' j))
          have := congrFun hσ' j
          change g' j = f' (σ' j)
          exact this⟩

private theorem toMultiset_sum_single_fn {α : Type*} [DecidableEq α] (g : Fin n → α) :
    Finsupp.toMultiset (∑ l : Fin n, Finsupp.single (g l) (1 : ℕ)) =
      Multiset.map g (Finset.univ : Finset (Fin n)).val := by
  classical
  rw [Finsupp.toMultiset_sum]
  simp only [Finsupp.toMultiset_single, one_smul]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, Finset.insert_val, Multiset.ndinsert_of_notMem ha,
      Multiset.map_cons, Multiset.singleton_add]

private theorem exists_blockPerm_of_sum_single_eq (slot : Fin n → Fin k)
    (f g f₀ g₀ : Fin n → Fin N)
    (h : ∑ j : Fin n, Finsupp.single (slot j, g j, f j) (1 : ℕ)
        = ∑ j : Fin n, Finsupp.single (slot j, g₀ j, f₀ j) (1 : ℕ)) :
    ∃ σ ∈ TensorPolynomial.slotPermutations k n slot, f = f₀ ∘ σ ∧ g = g₀ ∘ σ := by
  classical
  have hmulti : Multiset.map (fun j => ((slot j, g₀ j, f₀ j) : Fin k × Fin N × Fin N))
        (Finset.univ : Finset (Fin n)).val
      = Multiset.map (fun j => ((slot j, g j, f j) : Fin k × Fin N × Fin N))
        (Finset.univ : Finset (Fin n)).val := by
    rw [← toMultiset_sum_single_fn, ← toMultiset_sum_single_fn, h]
  obtain ⟨σ, hσ⟩ := matchingPerm
    (fun j => ((slot j, g₀ j, f₀ j) : Fin k × Fin N × Fin N))
    (fun j => ((slot j, g j, f j) : Fin k × Fin N × Fin N)) hmulti
  refine ⟨σ, ?_, ?_, ?_⟩
  · rw [TensorPolynomial.slotPermutations, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    funext j
    have hj := congrFun hσ j
    simp only [Function.comp_apply, Prod.mk.injEq] at hj
    change slot (σ j) = slot j
    exact hj.1.symm
  · funext j
    have hj := congrFun hσ j
    simp only [Function.comp_apply, Prod.mk.injEq] at hj
    exact hj.2.2
  · funext j
    have hj := congrFun hσ j
    simp only [Function.comp_apply, Prod.mk.injEq] at hj
    exact hj.2.1

private theorem reynolds_eq_zero_of_endTensorEval_zero (slot : Fin n → Fin k)
    (W₀ : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n))
    (hW : TensorPolynomial.endomorphismToPolynomial k N n slot (TensorPolynomial.symmetrizeEndomorphism k N n slot W₀) = 0) :
    TensorPolynomial.symmetrizeEndomorphism k N n slot W₀ = 0 := by
  classical
  set W := TensorPolynomial.symmetrizeEndomorphism k N n slot W₀ with hWdef
  suffices hzero : ∀ f g : Fin n → Fin N,
      LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W f g = 0 by
    have hmat : LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W = 0 := by
      ext f g; exact hzero f g
    have hsymm : (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)).symm
          (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W)
        = (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n)).symm 0 := by rw [hmat]
    rwa [LinearEquiv.symm_apply_apply, map_zero] at hsymm
  intro f₀ g₀
  set u₀ : (Fin k × Fin N × Fin N) →₀ ℕ :=
    ∑ j : Fin n, Finsupp.single (slot j, g₀ j, f₀ j) 1 with hu₀

  have hEval : TensorPolynomial.endomorphismToPolynomial k N n slot W
      = ∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
          MvPolynomial.monomial (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1)
            (LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W f g) := by
    rw [TensorPolynomial.endomorphismToPolynomial_apply]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
    rw [genericTensorMatrix_eq_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.C_mul_monomial,
      mul_one]

  have hcoeff : (∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
      (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
          LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W f g else 0)) = 0 := by
    have hc : MvPolynomial.coeff u₀ (TensorPolynomial.endomorphismToPolynomial k N n slot W) = 0 := by
      rw [hW, MvPolynomial.coeff_zero]
    rw [hEval] at hc
    simp_rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hc
    exact hc

  have hconst : ∀ f g : Fin n → Fin N,
      (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
          LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W f g else 0)
        = (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
          LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W f₀ g₀ else 0) := by
    intro f g
    by_cases hfg : (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀
    · rw [if_pos hfg, if_pos hfg]
      obtain ⟨σ, hσbp, hfσ, hgσ⟩ :=
        exists_blockPerm_of_sum_single_eq k N n slot f g f₀ g₀ (by rw [hfg, hu₀])
      have hbs := reynolds_block_symmetric k N n slot W₀ hσbp f₀ g₀
      rw [← hWdef] at hbs
      rw [hfσ, hgσ]
      exact hbs
    · rw [if_neg hfg, if_neg hfg]
  have hcoeff2 : (∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
      (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
          LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W f₀ g₀ else 0)) = 0 := by
    rw [show (∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
          (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
            LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W f₀ g₀ else 0))
        = ∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
          (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
            LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W f g else 0) from
      Finset.sum_congr rfl fun f _ =>
        Finset.sum_congr rfl fun g _ => (hconst f g).symm]
    exact hcoeff

  have hcombine : (∑ p : (Fin n → Fin N) × (Fin n → Fin N),
        (if (∑ j : Fin n, Finsupp.single (slot j, p.2 j, p.1 j) 1) = u₀ then
          LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W f₀ g₀ else 0))
      = ∑ f : Fin n → Fin N, ∑ g : Fin n → Fin N,
          (if (∑ j : Fin n, Finsupp.single (slot j, g j, f j) 1) = u₀ then
            LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W f₀ g₀ else 0) :=
    Fintype.sum_prod_type _
  have hpc : (∑ p : (Fin n → Fin N) × (Fin n → Fin N),
        (if (∑ j : Fin n, Finsupp.single (slot j, p.2 j, p.1 j) 1) = u₀ then
          LinearMap.toMatrix (TensorPolynomial.piTensorProductBasis N n) (TensorPolynomial.piTensorProductBasis N n) W f₀ g₀ else 0)) = 0 := by
    rw [hcombine]; exact hcoeff2
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hpc
  have hmemfilter : (f₀, g₀) ∈
      (Finset.univ.filter fun p : (Fin n → Fin N) × (Fin n → Fin N) =>
        (∑ j : Fin n, Finsupp.single (slot j, p.2 j, p.1 j) 1) = u₀) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hu₀.symm⟩
  have hcard_ne : ((Finset.univ.filter fun p : (Fin n → Fin N) × (Fin n → Fin N) =>
        (∑ j : Fin n, Finsupp.single (slot j, p.2 j, p.1 j) 1) = u₀).card : ℂ) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero, Finset.card_eq_zero]
    exact Finset.nonempty_iff_ne_empty.mp ⟨(f₀, g₀), hmemfilter⟩
  exact (mul_eq_zero.mp hpc).resolve_left hcard_ne

/-- Two symmetrized endomorphisms are equal whenever their contracted polynomials are equal. -/
theorem TensorPolynomial.symmetrizeEndomorphism_eq_of_contraction_eq (slot : Fin n → Fin k)
    (M M' : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n))
    (h : TensorPolynomial.endomorphismToPolynomial k N n slot (TensorPolynomial.symmetrizeEndomorphism k N n slot M)
          = TensorPolynomial.endomorphismToPolynomial k N n slot (TensorPolynomial.symmetrizeEndomorphism k N n slot M')) :
    TensorPolynomial.symmetrizeEndomorphism k N n slot M = TensorPolynomial.symmetrizeEndomorphism k N n slot M' := by

  classical
  have hz : TensorPolynomial.endomorphismToPolynomial k N n slot (TensorPolynomial.symmetrizeEndomorphism k N n slot (M - M')) = 0 := by
    rw [reynolds_sub, map_sub, h, sub_self]
  have hzero : TensorPolynomial.symmetrizeEndomorphism k N n slot (M - M') = 0 :=
    reynolds_eq_zero_of_endTensorEval_zero k N n slot (M - M') hz
  rw [reynolds_sub, sub_eq_zero] at hzero
  exact hzero

/-- The matrix action preserves weighted homogeneity and its multidegree. -/
theorem TensorPolynomial.IsWeightedHomogeneous.map_matrixAction (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) (d : Fin k →₀ ℕ)
    {p : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N} (hp : IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) p d) :
    IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g p) d := by
  classical

  have hgen : ∀ v : Fin k × Fin N × Fin N,
      IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g (X v)) (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N v) := by
    rintro ⟨i, r, c⟩
    rw [TensorPolynomial.matrixVariable_action_apply]
    refine IsWeightedHomogeneous.sum _ _ _ (fun s _ =>
      IsWeightedHomogeneous.sum _ _ _ (fun t _ => ?_))
    have hXst : IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) (X (i, s, t) : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N)
        (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N (i, s, t)) := isWeightedHomogeneous_X ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) (i, s, t)
    have hw : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N (i, s, t) = RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N (i, r, c) := rfl
    rw [← hw, show algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N) ((↑g : Matrix (Fin N) (Fin N) ℂ) r s)
          * X (i, s, t)
          * algebraMap ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N) ((↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ) t c)
        = MvPolynomial.C ((↑g : Matrix (Fin N) (Fin N) ℂ) r s
            * (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ) t c) * X (i, s, t) by
      rw [map_mul, MvPolynomial.algebraMap_eq]; ring]
    exact hXst.C_mul _

  have hpow : ∀ (φ : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N) (m : Fin k →₀ ℕ) (e : ℕ),
      IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) φ m →
      IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) (φ ^ e) (e • m) := by
    intro φ m e hφ
    induction e with
    | zero => simpa using isWeightedHomogeneous_one ℂ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N)
    | succ e ih => rw [pow_succ, succ_nsmul]; exact ih.mul hφ

  have hmon : ∀ (u : (Fin k × Fin N × Fin N) →₀ ℕ) (c : ℂ),
      Finsupp.weight (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) u = d →
      IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g (monomial u c)) d := by
    intro u c hwu
    rw [MvPolynomial.monomial_eq, map_mul,
      show RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g (C c) = C c from by
        rw [← MvPolynomial.algebraMap_eq]; exact AlgHom.commutes _ c]
    simp only [Finsupp.prod, map_prod, map_pow]
    have hdeg : ∑ v ∈ u.support, (u v) • RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N v = d := by
      rw [← hwu, Finsupp.weight_apply]; rfl
    have hprod := IsWeightedHomogeneous.prod u.support
      (fun v => RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g (X v) ^ (u v))
      (fun v => (u v) • RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N v)
      (fun v _ => hpow (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g (X v)) (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N v) (u v) (hgen v))
    rw [hdeg] at hprod
    exact hprod.C_mul c
  rw [p.as_sum, map_sum]
  exact IsWeightedHomogeneous.sum _ _ _ (fun u hu =>
    hmon u _ (hp (MvPolynomial.mem_support_iff.mp hu)))

/-- When slot multiplicities realize a multidegree, there is a right inverse to the endomorphism contraction map on weighted-homogeneous polynomials that intertwines the matrix actions. -/
theorem TensorPolynomial.exists_equivariant_weightedHomogeneous_rightInverse
    (d : Fin k →₀ ℕ) (slot : Fin n → Fin k)
    (hslot : ∀ i : Fin k, (Finset.univ.filter fun j => slot j = i).card = d i) :
    ∃ σ : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N → Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n),
      (∀ p : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N, IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) p d →
          TensorPolynomial.endomorphismToPolynomial k N n slot (σ p) = p) ∧
      (∀ (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) (p : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N),
          IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) p d →
          σ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g p)
            = PiTensorProduct.map
                  (fun _ : Fin n => Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ))
              * σ p
              * PiTensorProduct.map
                  (fun _ : Fin n => Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ))) := by
  classical

  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N → Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n),
      ∀ p : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N, IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) p d →
        TensorPolynomial.endomorphismToPolynomial k N n slot (σ₀ p) = p := by
    refine ⟨fun p => if h : IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) p d
      then (LinearMap.mem_range.mp
        (TensorPolynomial.weightedHomogeneous_mem_range_endomorphismToPolynomial k N n d slot hslot h)).choose else 0, ?_⟩
    intro p hp
    simp only [dif_pos hp]
    exact (LinearMap.mem_range.mp
      (TensorPolynomial.weightedHomogeneous_mem_range_endomorphismToPolynomial k N n d slot hslot hp)).choose_spec

  refine ⟨fun p => TensorPolynomial.symmetrizeEndomorphism k N n slot (σ₀ p), ?_, ?_⟩
  ·
    intro p hp
    rw [TensorPolynomial.endomorphismToPolynomial_symmetrize]
    exact hσ₀ p hp
  ·
    intro g p hp
    rw [← TensorPolynomial.symmetrizeEndomorphism_conjugate]
    refine TensorPolynomial.symmetrizeEndomorphism_eq_of_contraction_eq k N n slot _ _ ?_
    rw [TensorPolynomial.endomorphismToPolynomial_symmetrize, TensorPolynomial.endomorphismToPolynomial_symmetrize, TensorPolynomial.endomorphismToPolynomial_conjugate,
      hσ₀ p hp, hσ₀ (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g p) (TensorPolynomial.IsWeightedHomogeneous.map_matrixAction k N g d hp)]

/-- A weighted-homogeneous polynomial in the specified polynomial set has a contraction preimage belonging to the specified endomorphism set. -/
theorem TensorPolynomial.exists_auxiliaryEndomorphism_preimage
    (d : Fin k →₀ ℕ) (slot : Fin n → Fin k)
    (hslot : ∀ i : Fin k, (Finset.univ.filter fun j => slot j = i).card = d i)
    {p : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType k N}
    (hhom : IsWeightedHomogeneous (RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.variableWeight k N) p d)
    (hinv : p ∈ RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.complexSubalgebra k N) :
    ∃ M ∈ RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra ℂ (TensorPolynomial.AuxiliaryIndexType N) n, TensorPolynomial.endomorphismToPolynomial k N n slot M = p := by
  classical
  obtain ⟨σ, hsec, hequiv⟩ :=
    TensorPolynomial.exists_equivariant_weightedHomogeneous_rightInverse k N n d slot hslot
  refine ⟨σ p, ?_, hsec p hhom⟩

  have key : ∀ g' : (Module.End ℂ (TensorPolynomial.AuxiliaryIndexType N))ˣ,
      Commute (PiTensorProduct.map (fun _ : Fin n => (g' : Module.End ℂ (TensorPolynomial.AuxiliaryIndexType N)))) (σ p) := by
    intro g'

    set A : Matrix (Fin N) (Fin N) ℂ :=
      LinearMap.toMatrix' (↑g' : Module.End ℂ (Fin N → ℂ)) with hA
    set A' : Matrix (Fin N) (Fin N) ℂ :=
      LinearMap.toMatrix' (↑g'⁻¹ : Module.End ℂ (Fin N → ℂ)) with hA'
    have hAA' : A * A' = 1 := by
      rw [hA, hA', ← LinearMap.toMatrix'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        LinearMap.toMatrix'_one]
    have hA'A : A' * A = 1 := by
      rw [hA, hA', ← LinearMap.toMatrix'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        LinearMap.toMatrix'_one]
    set g : (Matrix (Fin N) (Fin N) ℂ)ˣ := ⟨A, A', hAA', hA'A⟩ with hg
    have hP : Matrix.mulVecLin (↑g : Matrix (Fin N) (Fin N) ℂ)
        = (↑g' : Module.End ℂ (TensorPolynomial.AuxiliaryIndexType N)) := by
      change Matrix.mulVecLin A = _
      rw [hA, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
    have hPinv : Matrix.mulVecLin (↑g⁻¹ : Matrix (Fin N) (Fin N) ℂ)
        = (↑g'⁻¹ : Module.End ℂ (TensorPolynomial.AuxiliaryIndexType N)) := by
      change Matrix.mulVecLin A' = _
      rw [hA', ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

    have hpinv : RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.matrixUnitsAlgHom k N g p = p := by
      rw [RepresentationTheory.Algebra.MvPolynomial.WeightedComponents.NatPairIndexedType.complexSubalgebra, Algebra.mem_iInf] at hinv
      have hg' := hinv g
      rwa [AlgHom.mem_equalizer, AlgHom.id_apply] at hg'

    have heq := hequiv g p hhom
    rw [hpinv] at heq
    simp only [hP, hPinv] at heq
    set P : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n) :=
      PiTensorProduct.map (fun _ : Fin n => (g' : Module.End ℂ (TensorPolynomial.AuxiliaryIndexType N))) with hPdef
    set Q : Module.End ℂ (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace ℂ (TensorPolynomial.AuxiliaryIndexType N) n) :=
      PiTensorProduct.map (fun _ : Fin n => (↑g'⁻¹ : Module.End ℂ (TensorPolynomial.AuxiliaryIndexType N))) with hQdef

    have hPQ : P * Q = 1 := by
      rw [hPdef, hQdef, ← PiTensorProduct.map_mul]
      have hid : (fun _ : Fin n =>
            (↑g' : Module.End ℂ (TensorPolynomial.AuxiliaryIndexType N)) * (↑g'⁻¹ : Module.End ℂ (TensorPolynomial.AuxiliaryIndexType N)))
          = fun _ : Fin n => (1 : Module.End ℂ (TensorPolynomial.AuxiliaryIndexType N)) := by
        funext _
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hid, PiTensorProduct.map_one]

    change Commute P (σ p)
    rw [Commute, SemiconjBy]
    nth_rewrite 1 [heq]
    rw [← mul_assoc, ← mul_assoc, hPQ, one_mul]

  rw [(RepresentationTheory.Auxiliary.MutualCentralizers.mutual_centralizer_algebras ℂ (TensorPolynomial.AuxiliaryIndexType N) n).1, Subalgebra.mem_centralizer_iff]
  intro y hy
  rw [← RepresentationTheory.TensorPower.adjoin_piTensorProductMaps_eq_auxiliary (V := TensorPolynomial.AuxiliaryIndexType N) ℂ n] at hy
  have hcomm : Commute (σ p) y :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy (by
      rintro _ ⟨g', rfl⟩
      exact (key g').symm)
  exact hcomm.symm

end RepresentationTheory.TensorPolynomial.Contraction
