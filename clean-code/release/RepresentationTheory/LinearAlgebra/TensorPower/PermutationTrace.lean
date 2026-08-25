/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Auxiliary.MutualCentralizers

/-! # Permutation traces on tensor powers -/

open scoped TensorProduct

open RepresentationTheory.Auxiliary.MutualCentralizers

namespace RepresentationTheory.LinearAlgebra.TensorPower.PermutationTrace

universe u v

variable (k : Type u) [Field k]
  (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- The endomorphism of a tensor power obtained from factorwise endomorphisms and a permutation of the factors. -/
noncomputable def LinearMap.permutedTensorEndomorphism (σ : Equiv.Perm (Fin n)) (A : Fin n → Module.End k V) :
    Module.End k (auxiliarySpace k V n) :=
  (auxiliarySpacePermutationEquiv k V n σ).toLinearMap ∘ₗ PiTensorProduct.map A

/-- A chosen basis of a finite module over a field. -/
noncomputable abbrev Module.Finite.chosenBasis : Module.Basis (Module.Free.ChooseBasisIndex k V) k V :=
  Module.Free.chooseBasis k V

/-- The trace of a permuted tensor endomorphism is a sum of products of matrix entries in a chosen basis. -/
theorem LinearMap.trace_permutedTensorEndomorphism_eq_sum (σ : Equiv.Perm (Fin n)) (A : Fin n → Module.End k V) :
    LinearMap.trace k _ (LinearMap.permutedTensorEndomorphism k V n σ A)
      = ∑ p : Fin n → Module.Free.ChooseBasisIndex k V,
          ∏ i : Fin n,
            LinearMap.toMatrix (Module.Finite.chosenBasis k V) (Module.Finite.chosenBasis k V) (A i) (p (σ i)) (p i) := by
  classical
  set b : Module.Basis (Module.Free.ChooseBasisIndex k V) k V := Module.Finite.chosenBasis k V with hb
  set B : Module.Basis (Fin n → Module.Free.ChooseBasisIndex k V) k (auxiliarySpace k V n) :=
    Basis.piTensorProduct (fun _ : Fin n => b) with hB
  rw [LinearMap.trace_eq_matrix_trace k B, Matrix.trace]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  -- the `p`-diagonal entry of the operator in the basis `B`
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  -- compute the operator on the basis vector `B p`
  have hBp : B p = ⨂ₜ[k] i, b (p i) := Basis.piTensorProduct_apply (fun _ => b) p
  have hop : LinearMap.permutedTensorEndomorphism k V n σ A (B p)
      = ⨂ₜ[k] j, (A (σ.symm j)) (b (p (σ.symm j))) := by
    rw [hBp, LinearMap.permutedTensorEndomorphism, LinearMap.comp_apply, PiTensorProduct.map_tprod]
    change auxiliarySpacePermutationEquiv k V n σ (⨂ₜ[k] i, (A i) (b (p i))) = _
    rw [auxiliarySpacePermutationEquiv, PiTensorProduct.reindex_tprod]
  rw [hop, hB, Basis.piTensorProduct_repr_tprod_apply]
  -- reindex the product `∏ j` by `j = σ i`
  rw [← Equiv.prod_comp σ
        (fun j => b.repr ((A (σ.symm j)) (b (p (σ.symm j)))) (p j))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Equiv.symm_apply_apply, LinearMap.toMatrix_apply]

/-! ## The cycle structure of `σ` -/

/-- The length of the cycle of a permutation containing a given index. -/
noncomputable def Equiv.Perm.cycleLengthAt {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) : ℕ :=
  Function.minimalPeriod (⇑σ) i

/-- The finite set of least representatives of the cycles of a permutation. -/
noncomputable def Equiv.Perm.cycleRepresentatives {m : ℕ} (σ : Equiv.Perm (Fin m)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => ∀ j : Fin m, σ.SameCycle i j → i ≤ j)

/-! ## The combinatorial core (matrix side) -/

/-! ## Walk-sum expansion of a matrix product

An ordered product of matrices, evaluated at an entry, expands as a sum over "walks": tuples of
intermediate indices, weighted by the product of the traversed matrix entries. Setting the two
endpoints equal and summing recovers the trace as a sum over closed walks. This underlies the
single-orbit telescoping. -/

section WalkSum

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product, in index order, of a finite family of square matrices. -/
def Matrix.orderedProduct {ℓ : ℕ} (N : Fin ℓ → Matrix ι ι R) : Matrix ι ι R := (List.ofFn N).prod

/-- The ordered product of an empty family of matrices is the identity matrix. -/
@[simp] lemma Matrix.orderedProduct_zero (N : Fin 0 → Matrix ι ι R) : Matrix.orderedProduct N = 1 := by
  simp [Matrix.orderedProduct]

/-- Prepending a matrix to a family multiplies it on the left of the ordered product. -/
lemma Matrix.orderedProduct_cons {ℓ : ℕ} (M : Matrix ι ι R) (N : Fin ℓ → Matrix ι ι R) :
    Matrix.orderedProduct (Fin.cons M N) = M * Matrix.orderedProduct N := by
  simp [Matrix.orderedProduct, List.ofFn_succ]

/-- The product of entries selected by consecutive vertices of a path through a family of matrices. -/
def Matrix.pathWeight {ℓ : ℕ} (N : Fin ℓ → Matrix ι ι R) (v : Fin (ℓ + 1) → ι) : R :=
  ∏ t : Fin ℓ, N t (v t.castSucc) (v t.succ)

omit [Fintype ι] [DecidableEq ι] in
/-- The weight of a path through a prepended matrix factors into its first edge weight and the remaining path weight. -/
lemma Matrix.pathWeight_cons {ℓ : ℕ} (N : Fin (ℓ + 1) → Matrix ι ι R) (z : ι)
    (v : Fin (ℓ + 1) → ι) :
    Matrix.pathWeight N (Fin.cons z v) = N 0 z (v 0) * Matrix.pathWeight (Fin.tail N) v := by
  unfold Matrix.pathWeight
  rw [Fin.prod_univ_succ]
  congr 1

/-- An entry of an ordered matrix product is the sum of the weights of paths with the prescribed endpoints. -/
theorem Matrix.orderedProduct_apply (ℓ : ℕ) (N : Fin ℓ → Matrix ι ι R) (x y : ι) :
    (Matrix.orderedProduct N) x y
      = ∑ v : Fin (ℓ + 1) → ι,
          (if v 0 = x ∧ v (Fin.last ℓ) = y then Matrix.pathWeight N v else 0) := by
  induction ℓ generalizing x with
  | zero =>
    rw [Matrix.orderedProduct_zero, Matrix.one_apply]
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _
      (fun z => if z = x ∧ z = y then (1 : R) else 0)]
    · by_cases hxy : x = y
      · subst hxy
        rw [Finset.sum_eq_single x]
        · simp
        · intro z _ hz; simp [hz]
        · simp
      · rw [Finset.sum_eq_zero]
        · simp [hxy]
        · intro z _; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hxy rfl
    · intro v
      simp only [Matrix.pathWeight, Finset.univ_eq_empty, Finset.prod_empty, Equiv.funUnique_apply,
        Fin.last_zero, Fin.default_eq_zero]
  | succ ℓ ih =>
    -- peel the first matrix
    have hsplit : Matrix.orderedProduct N = N 0 * Matrix.orderedProduct (Fin.tail N) := by
      conv_lhs => rw [← Fin.cons_self_tail N]
      rw [Matrix.orderedProduct_cons]
    rw [hsplit, Matrix.mul_apply]
    -- expand each inner entry by the induction hypothesis (start vertex = z)
    simp_rw [ih (Fin.tail N)]
    -- RHS: reindex the vertex sum by splitting off the first vertex via `Fin.cons`
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (ℓ + 2) => ι)),
      Fintype.sum_prod_type]
    have hlast : (Fin.last (ℓ + 1) : Fin (ℓ + 2)) = (Fin.last ℓ).succ := (Fin.succ_last ℓ).symm
    have hce : ∀ (z : ι) (w : Fin (ℓ + 1) → ι),
        (Fin.consEquiv (fun _ : Fin (ℓ + 2) => ι)) (z, w) = Fin.cons z w := fun _ _ => rfl
    simp only [hce, Fin.cons_zero, hlast, Fin.cons_succ, Matrix.pathWeight_cons]
    -- both sides equal a common form summed over `v : Fin (ℓ+1) → ι`
    trans (∑ v : Fin (ℓ + 1) → ι,
        if v (Fin.last ℓ) = y then N 0 x (v 0) * Matrix.pathWeight (Fin.tail N) v else 0)
    · -- left side = common
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have h0 : ∀ z ∈ (Finset.univ : Finset ι), z ≠ v 0 →
          N 0 x z * (if v 0 = z ∧ v (Fin.last ℓ) = y then Matrix.pathWeight (Fin.tail N) v else 0)
            = 0 := by
        intro z _ hz; rw [if_neg (by rintro ⟨h, _⟩; exact hz h.symm), mul_zero]
      rw [Finset.sum_eq_single_of_mem (v 0) (Finset.mem_univ _) h0]
      by_cases hd : v (Fin.last ℓ) = y <;> simp [hd]
    · -- right side = common
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have h0 : ∀ z ∈ (Finset.univ : Finset ι), z ≠ x →
          (if z = x ∧ v (Fin.last ℓ) = y then N 0 z (v 0) * Matrix.pathWeight (Fin.tail N) v else 0)
            = 0 := by
        intro z _ hz; rw [if_neg (by rintro ⟨h, _⟩; exact hz h)]
      rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _) h0]
      by_cases hd : v (Fin.last ℓ) = y <;> simp [hd]

/-- The trace of an ordered matrix product is the sum of the weights of paths whose endpoints agree. -/
theorem Matrix.trace_orderedProduct_eq_sum_pathWeights (ℓ : ℕ) (N : Fin ℓ → Matrix ι ι R) :
    Matrix.trace (Matrix.orderedProduct N)
      = ∑ v : Fin (ℓ + 1) → ι, (if v (Fin.last ℓ) = v 0 then Matrix.pathWeight N v else 0) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  simp_rw [Matrix.orderedProduct_apply ℓ N]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have h0 : ∀ x ∈ (Finset.univ : Finset ι), x ≠ v 0 →
      (if v 0 = x ∧ v (Fin.last ℓ) = x then Matrix.pathWeight N v else 0) = 0 := by
    intro x _ hx; rw [if_neg (by rintro ⟨h, _⟩; exact hx h.symm)]
  rw [Finset.sum_eq_single_of_mem (v 0) (Finset.mem_univ _) h0]
  by_cases hd : v (Fin.last ℓ) = v 0 <;> simp [hd]

omit [Fintype ι] [DecidableEq ι] in

/-- Appending the first entry to a finite sequence agrees with the shifted original sequence at successor indices. -/
lemma Fin.snoc_head_apply_succ {ℓ' : ℕ} (a : Fin (ℓ' + 1) → ι) (t : Fin (ℓ' + 1)) :
    (Fin.snoc a (a 0) : Fin (ℓ' + 2) → ι) t.succ = a (t + 1) := by
  rcases eq_or_ne t (Fin.last ℓ') with h | h
  · subst h
    rw [Fin.succ_last, Fin.snoc_last, Fin.last_add_one]
  · obtain ⟨s, rfl⟩ := Fin.eq_castSucc_of_ne_last h
    rw [Fin.succ_castSucc, Fin.snoc_castSucc]
    congr 1
    ext
    rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last s), Fin.val_castSucc, Fin.val_succ]

/-- For a nonempty family, the trace of its ordered product is a sum of products of entries around closed index paths. -/
theorem Matrix.trace_orderedProduct_eq_sum_cycleWeights {ℓ : ℕ} [NeZero ℓ] (N : Fin ℓ → Matrix ι ι R) :
    Matrix.trace (Matrix.orderedProduct N)
      = ∑ a : Fin ℓ → ι, ∏ t : Fin ℓ, N t (a t) (a (t + 1)) := by
  obtain ⟨ℓ', rfl⟩ : ∃ k, ℓ = k + 1 :=
    ⟨ℓ - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne ℓ))).symm⟩
  rw [Matrix.trace_orderedProduct_eq_sum_pathWeights, ← Finset.sum_filter]
  refine (Finset.sum_bij' (fun a _ => Fin.snoc a (a 0)) (fun v _ t => v t.castSucc)
    ?_ ?_ ?_ ?_ ?_).symm
  · -- forward map lands in the closed-walk filter
    intro a _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.snoc_last]
    conv_rhs => rw [show (0 : Fin (ℓ' + 2)) = Fin.castSucc (0 : Fin (ℓ' + 1)) from
      (Fin.castSucc_zero).symm, Fin.snoc_castSucc]
  · -- backward map lands in univ
    intro v _; exact Finset.mem_univ _
  · -- left inverse
    intro a _; funext t; rw [Fin.snoc_castSucc]
  · -- right inverse
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    funext i
    change (Fin.snoc (fun t => v t.castSucc) (v (Fin.castSucc 0)) : Fin (ℓ' + 2) → ι) i = v i
    rw [Fin.castSucc_zero, ← hv]
    exact congrFun (Fin.snoc_init_self v) i
  · -- summands agree
    intro a _
    unfold Matrix.pathWeight
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [Fin.snoc_castSucc, Fin.snoc_head_apply_succ]

end WalkSum

section MatrixCombinatorics

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- The ordered product of a matrix family along the permutation cycle through an index. -/
noncomputable def Matrix.permutationCycleProduct (σ : Equiv.Perm (Fin m)) (M : Fin m → Matrix ι ι R) (i : Fin m) :
    Matrix ι ι R :=
  (((List.range (Equiv.Perm.cycleLengthAt σ i)).map (fun t => M ((σ⁻¹ ^ t) i)))).prod

/-! ### Orbit-representative infrastructure

Each `σ`-orbit is tagged by its `≤`-minimal element, the *representative*. `Equiv.Perm.cycleRepresentative σ x` is the
representative of `x`'s orbit; it is constant along cycles, lands in `Equiv.Perm.cycleRepresentatives σ`, and fixes the
elements of `Equiv.Perm.cycleRepresentatives σ`. `Equiv.Perm.cycleFiberSuccessor σ r` is the action of `σ` on the fiber (orbit) of `r`. -/

open scoped Classical in

/-- The least index in the cycle of a permutation containing a given index. -/
noncomputable def Equiv.Perm.cycleRepresentative (σ : Equiv.Perm (Fin m)) (x : Fin m) : Fin m :=
  (Finset.univ.filter (fun j => σ.SameCycle x j)).min'
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.refl σ x⟩⟩

/-- Every index lies in the same permutation cycle as its least representative. -/
lemma Equiv.Perm.sameCycle_cycleRepresentative (σ : Equiv.Perm (Fin m)) (x : Fin m) : σ.SameCycle x (Equiv.Perm.cycleRepresentative σ x) := by
  classical
  have h := Finset.min'_mem (Finset.univ.filter (fun j => σ.SameCycle x j))
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.refl σ x⟩⟩
  exact (Finset.mem_filter.mp h).2

/-- The least representative of a cycle is no greater than any index in that cycle. -/
lemma Equiv.Perm.cycleRepresentative_le_of_sameCycle (σ : Equiv.Perm (Fin m)) (x : Fin m) {j : Fin m} (h : σ.SameCycle x j) :
    Equiv.Perm.cycleRepresentative σ x ≤ j :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

/-- Indices in the same permutation cycle have the same least representative. -/
lemma Equiv.Perm.cycleRepresentative_eq_of_sameCycle (σ : Equiv.Perm (Fin m)) {x y : Fin m} (h : σ.SameCycle x y) :
    Equiv.Perm.cycleRepresentative σ x = Equiv.Perm.cycleRepresentative σ y := by
  classical
  unfold Equiv.Perm.cycleRepresentative
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hj => h.symm.trans hj, fun hj => h.trans hj⟩

/-- An index represents a permutation cycle exactly when it is no greater than every index in that cycle. -/
lemma Equiv.Perm.mem_cycleRepresentatives_iff (σ : Equiv.Perm (Fin m)) {r : Fin m} :
    r ∈ Equiv.Perm.cycleRepresentatives σ ↔ ∀ j, σ.SameCycle r j → r ≤ j := by
  simp [Equiv.Perm.cycleRepresentatives]

/-- The least representative of the cycle containing an index belongs to the set of cycle representatives. -/
lemma Equiv.Perm.cycleRepresentative_mem (σ : Equiv.Perm (Fin m)) (x : Fin m) : Equiv.Perm.cycleRepresentative σ x ∈ Equiv.Perm.cycleRepresentatives σ := by
  rw [Equiv.Perm.mem_cycleRepresentatives_iff]
  exact fun j hj => Equiv.Perm.cycleRepresentative_le_of_sameCycle σ x ((Equiv.Perm.sameCycle_cycleRepresentative σ x).trans hj)

/-- A selected cycle representative is its own least representative. -/
lemma Equiv.Perm.cycleRepresentative_eq_self_of_mem (σ : Equiv.Perm (Fin m)) {r : Fin m} (hr : r ∈ Equiv.Perm.cycleRepresentatives σ) :
    Equiv.Perm.cycleRepresentative σ r = r := by
  rw [Equiv.Perm.mem_cycleRepresentatives_iff] at hr
  exact le_antisymm (Equiv.Perm.cycleRepresentative_le_of_sameCycle σ r (Equiv.Perm.SameCycle.refl σ r)) (hr _ (Equiv.Perm.sameCycle_cycleRepresentative σ r))

/-- The cycle representative is unchanged after applying the permutation once. -/
lemma Equiv.Perm.cycleRepresentative_apply (σ : Equiv.Perm (Fin m)) (x : Fin m) : Equiv.Perm.cycleRepresentative σ (σ x) = Equiv.Perm.cycleRepresentative σ x :=
  Equiv.Perm.cycleRepresentative_eq_of_sameCycle σ ((Equiv.Perm.SameCycle.refl σ x).apply_left)

/-- The successor map induced by a permutation on a fiber of its cycle-representative map. -/
def Equiv.Perm.cycleFiberSuccessor (σ : Equiv.Perm (Fin m)) (r : Fin m) (x : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r}) :
    {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} :=
  ⟨σ x.1, by rw [Equiv.Perm.cycleRepresentative_apply]; exact x.2⟩

/-! ### Orbit period arithmetic

The single-orbit telescoping parametrizes the fiber of `r` by `t ↦ σ⁻¹^t r`, `t : Fin ℓ`,
`ℓ = Equiv.Perm.cycleLengthAt σ r`. The lemmas below supply the facts this parametrization needs: positivity of
the period, that `σ^ℓ` and `σ⁻¹^ℓ` fix `r`, and that `σ⁻¹` has the same minimal period at `r` as
`σ`. -/

/-- The cycle length of a permutation at any index is positive. -/
lemma Equiv.Perm.cycleLengthAt_pos (σ : Equiv.Perm (Fin m)) (i : Fin m) : 0 < Equiv.Perm.cycleLengthAt σ i :=
  Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts i)

/-- Applying a permutation for one full cycle returns an index to itself. -/
lemma Equiv.Perm.pow_cycleLengthAt_apply (σ : Equiv.Perm (Fin m)) (r : Fin m) :
    (σ ^ Equiv.Perm.cycleLengthAt σ r) r = r := by
  have h : (⇑σ)^[Equiv.Perm.cycleLengthAt σ r] r = r := Function.isPeriodicPt_minimalPeriod (⇑σ) r
  rwa [← Equiv.Perm.coe_pow] at h

/-- Applying the inverse permutation for one full cycle returns an index to itself. -/
lemma Equiv.Perm.inv_pow_cycleLengthAt_apply (σ : Equiv.Perm (Fin m)) (r : Fin m) :
    (σ⁻¹ ^ Equiv.Perm.cycleLengthAt σ r) r = r := by
  have h := Equiv.Perm.pow_cycleLengthAt_apply σ r
  rw [inv_pow]
  exact (Equiv.symm_apply_eq (σ ^ Equiv.Perm.cycleLengthAt σ r)).mpr h.symm

/-- A permutation and its inverse have the same minimal period at every index. -/
lemma Equiv.Perm.minimalPeriod_inv_eq (σ : Equiv.Perm (Fin m)) (r : Fin m) :
    Function.minimalPeriod (⇑σ⁻¹) r = Function.minimalPeriod (⇑σ) r := by
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro n
  have e : ∀ τ : Equiv.Perm (Fin m), Function.IsPeriodicPt (⇑τ) n r ↔ (τ ^ n) r = r := by
    intro τ
    change (⇑τ)^[n] r = r ↔ (τ ^ n) r = r
    rw [← Equiv.Perm.coe_pow]
  rw [e σ⁻¹, e σ, inv_pow]
  constructor
  · intro h; exact ((Equiv.symm_apply_eq (σ ^ n)).mp h).symm
  · intro h; exact (Equiv.symm_apply_eq (σ ^ n)).mpr h.symm

/-- In a nonempty finite type, the value of zero minus one is one less than the cardinality. -/
lemma Fin.zero_sub_one_val {ℓ : ℕ} [NeZero ℓ] : ((0 : Fin ℓ) - 1).val = ℓ - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 :=
    ⟨ℓ - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne ℓ))).symm⟩
  simp [zero_sub, Fin.coe_neg_one]

/-- A matrix product around a permutation cycle is the ordered product indexed by inverse iterates. -/
lemma Matrix.permutationCycleProduct_eq_orderedProduct (σ : Equiv.Perm (Fin m)) (M : Fin m → Matrix ι ι R) (r : Fin m) :
    Matrix.permutationCycleProduct σ M r
      = Matrix.orderedProduct (fun t : Fin (Equiv.Perm.cycleLengthAt σ r) => M ((σ⁻¹ ^ (t : ℕ)) r)) := by
  rw [Matrix.permutationCycleProduct, Matrix.orderedProduct]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_ofFn, List.getElem_map, List.getElem_range]

/-- The sum of edge weights on a represented permutation cycle equals the trace of its matrix product. -/
theorem Matrix.sum_cycleFiberWeights_eq_trace (σ : Equiv.Perm (Fin m)) (M : Fin m → Matrix ι ι R)
    {r : Fin m} (hr : r ∈ Equiv.Perm.cycleRepresentatives σ) :
    ∑ q : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} → ι,
        ∏ x : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r}, M x.1 (q (Equiv.Perm.cycleFiberSuccessor σ r x)) (q x)
      = Matrix.trace (Matrix.permutationCycleProduct σ M r) := by
  classical
  haveI : NeZero (Equiv.Perm.cycleLengthAt σ r) := ⟨(Equiv.Perm.cycleLengthAt_pos σ r).ne'⟩
  -- same-cycle witnesses for the backward orbit parametrization `t ↦ σ⁻¹^t r`
  have hsame : ∀ k : ℕ, σ.SameCycle ((σ⁻¹ ^ k) r) r := fun k =>
    ⟨(k : ℤ), by
      rw [zpow_natCast, ← Equiv.Perm.mul_apply, inv_pow, mul_inv_cancel, Equiv.Perm.one_apply]⟩
  -- the orbit bijection `φ : Fin ℓ ≃ fiber r`
  let φf : Fin (Equiv.Perm.cycleLengthAt σ r) → {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} :=
    fun t => ⟨(σ⁻¹ ^ (t : ℕ)) r, by
      rw [Equiv.Perm.cycleRepresentative_eq_of_sameCycle σ (hsame (t : ℕ)), Equiv.Perm.cycleRepresentative_eq_self_of_mem σ hr]⟩
  have hφf_inj : Function.Injective φf := by
    intro t1 t2 h
    have h1 : (σ⁻¹ ^ (t1 : ℕ)) r = (σ⁻¹ ^ (t2 : ℕ)) r := Subtype.ext_iff.mp h
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := ⇑σ⁻¹) (x := r)
    rw [Equiv.Perm.minimalPeriod_inv_eq σ r] at hinj
    exact Fin.ext (hinj (Set.mem_Iio.mpr t1.isLt) (Set.mem_Iio.mpr t2.isLt)
      (by simpa only [Equiv.Perm.coe_pow] using h1))
  have hφf_surj : Function.Surjective φf := by
    rintro ⟨x, hx⟩
    have hsc : σ.SameCycle x r := by have h := Equiv.Perm.sameCycle_cycleRepresentative σ x; rwa [hx] at h
    have hsc' : (σ⁻¹).SameCycle r x := by rw [Equiv.Perm.sameCycle_inv]; exact hsc.symm
    obtain ⟨i, _, hi⟩ := hsc'.exists_pow_eq'
    refine ⟨⟨i % Equiv.Perm.cycleLengthAt σ r, Nat.mod_lt _ (Equiv.Perm.cycleLengthAt_pos σ r)⟩, ?_⟩
    apply Subtype.ext
    change (σ⁻¹ ^ (i % Equiv.Perm.cycleLengthAt σ r)) r = x
    have hmod : (⇑σ⁻¹)^[i % Function.minimalPeriod (⇑σ⁻¹) r] r = (⇑σ⁻¹)^[i] r :=
      Function.iterate_mod_minimalPeriod_eq
    rw [Equiv.Perm.minimalPeriod_inv_eq σ r] at hmod
    calc (σ⁻¹ ^ (i % Equiv.Perm.cycleLengthAt σ r)) r
        = (⇑σ⁻¹)^[i % Equiv.Perm.cycleLengthAt σ r] r := by rw [Equiv.Perm.coe_pow]
      _ = (⇑σ⁻¹)^[i] r := hmod
      _ = (σ⁻¹ ^ i) r := by rw [Equiv.Perm.coe_pow]
      _ = x := hi
  let φ : Fin (Equiv.Perm.cycleLengthAt σ r) ≃ {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} :=
    Equiv.ofBijective φf ⟨hφf_inj, hφf_surj⟩
  have hφ : ∀ t, (φ t).1 = (σ⁻¹ ^ (t : ℕ)) r := fun _ => rfl
  -- the backward telescoping step: `σ · σ⁻¹^(k+1) = σ⁻¹^k`
  have hstep : ∀ k : ℕ, σ ((σ⁻¹ ^ (k + 1)) r) = (σ⁻¹ ^ k) r := by
    intro k; rw [pow_succ', Equiv.Perm.mul_apply]; simp
  -- the shift relation: applying `σ` on the fiber is `φ` of the predecessor index
  have hfib : ∀ t, Equiv.Perm.cycleFiberSuccessor σ r (φ t) = φ (t - 1) := by
    intro t
    apply Subtype.ext
    change σ ((φ t).1) = (φ (t - 1)).1
    rw [hφ, hφ]
    by_cases ht : t = 0
    · subst ht
      simp only [Fin.val_zero, pow_zero, Equiv.Perm.one_apply, Fin.zero_sub_one_val]
      have h := hstep (Equiv.Perm.cycleLengthAt σ r - 1)
      rwa [Nat.sub_add_cancel (Equiv.Perm.cycleLengthAt_pos σ r), Equiv.Perm.inv_pow_cycleLengthAt_apply] at h
    · rw [Fin.val_sub_one_of_ne_zero ht]
      have hv : t.val ≠ 0 := by rwa [Ne, Fin.val_eq_zero_iff]
      have h := hstep (t.val - 1)
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv)] at h
  -- the sum-level shift `a ↦ a ∘ (· - 1)`
  let shift : (Fin (Equiv.Perm.cycleLengthAt σ r) → ι) ≃ (Fin (Equiv.Perm.cycleLengthAt σ r) → ι) :=
    { toFun := fun a s => a (s - 1)
      invFun := fun a s => a (s + 1)
      left_inv := fun a => by funext s; simp
      right_inv := fun a => by funext s; simp }
  -- the abbreviation `E` for the arrow reindexing `a ↦ a ∘ φ.symm`
  set E : (Fin (Equiv.Perm.cycleLengthAt σ r) → ι) ≃ ({x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} → ι) :=
    Equiv.arrowCongr φ (Equiv.refl ι) with hE
  calc
    (∑ q : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} → ι,
        ∏ x : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r}, M x.1 (q (Equiv.Perm.cycleFiberSuccessor σ r x)) (q x))
        = ∑ a : Fin (Equiv.Perm.cycleLengthAt σ r) → ι,
            ∏ t : Fin (Equiv.Perm.cycleLengthAt σ r), M ((σ⁻¹ ^ (t : ℕ)) r) (a (t - 1)) (a t) := by
          rw [← Equiv.sum_comp E (fun q : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} → ι =>
            ∏ x, M x.1 (q (Equiv.Perm.cycleFiberSuccessor σ r x)) (q x))]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [← Equiv.prod_comp φ (fun x => M x.1 (E a (Equiv.Perm.cycleFiberSuccessor σ r x)) (E a x))]
          refine Finset.prod_congr rfl (fun t _ => ?_)
          rw [hfib]
          simp only [hE, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq,
            Equiv.symm_apply_apply]
          rw [hφ]
      _ = ∑ a : Fin (Equiv.Perm.cycleLengthAt σ r) → ι,
            ∏ t : Fin (Equiv.Perm.cycleLengthAt σ r), M ((σ⁻¹ ^ (t : ℕ)) r) (a t) (a (t + 1)) := by
          rw [← Equiv.sum_comp shift (fun a : Fin (Equiv.Perm.cycleLengthAt σ r) → ι =>
            ∏ t : Fin (Equiv.Perm.cycleLengthAt σ r), M ((σ⁻¹ ^ (t : ℕ)) r) (a t) (a (t + 1)))]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.prod_congr rfl (fun t _ => ?_)
          simp only [shift, Equiv.coe_fn_mk, add_sub_cancel_right]
      _ = Matrix.trace (Matrix.orderedProduct (fun t : Fin (Equiv.Perm.cycleLengthAt σ r) => M ((σ⁻¹ ^ (t : ℕ)) r))) :=
          (Matrix.trace_orderedProduct_eq_sum_cycleWeights _).symm
      _ = Matrix.trace (Matrix.permutationCycleProduct σ M r) := by rw [Matrix.permutationCycleProduct_eq_orderedProduct]

/-- A sum of matrix-entry weights associated with a permutation factors as a product of traces over its cycles. -/
theorem Matrix.sum_permutationWeights_eq_prod_cycleTraces (σ : Equiv.Perm (Fin m)) (M : Fin m → Matrix ι ι R) :
    ∑ p : Fin m → ι, ∏ i : Fin m, M i (p (σ i)) (p i)
      = ∏ i ∈ Equiv.Perm.cycleRepresentatives σ, Matrix.trace (Matrix.permutationCycleProduct σ M i) := by
  classical
  -- The reindexing between colorings `p` and orbitwise colorings `g`.
  let E : (Fin m → ι) ≃ (∀ r : Fin m, {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} → ι) :=
    { toFun := fun p r x => p x.1
      invFun := fun g i => g (Equiv.Perm.cycleRepresentative σ i) ⟨i, rfl⟩
      left_inv := fun p => rfl
      right_inv := fun g => by funext r x; obtain ⟨i, rfl⟩ := x; rfl }
  -- The product over `Fin m` splits as a product over orbit fibers.
  have hpart : ∀ h : Fin m → R,
      ∏ i : Fin m, h i = ∏ r : Fin m, ∏ x : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r}, h x.1 := by
    intro h
    rw [← Equiv.prod_comp (Equiv.sigmaFiberEquiv (Equiv.Perm.cycleRepresentative σ)) h, Fintype.prod_sigma]
    rfl
  calc
    ∑ p : Fin m → ι, ∏ i : Fin m, M i (p (σ i)) (p i)
        = ∑ p : Fin m → ι, ∏ r : Fin m,
            ∏ x : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r}, M x.1 (p (σ x.1)) (p x.1) := by
          exact Finset.sum_congr rfl (fun p _ => hpart (fun i => M i (p (σ i)) (p i)))
      _ = ∑ g : (∀ r : Fin m, {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} → ι), ∏ r : Fin m,
            ∏ x : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r}, M x.1 (g r (Equiv.Perm.cycleFiberSuccessor σ r x)) (g r x) := by
          rw [← Equiv.sum_comp E (fun g => ∏ r : Fin m,
            ∏ x : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r}, M x.1 (g r (Equiv.Perm.cycleFiberSuccessor σ r x)) (g r x))]
          exact Finset.sum_congr rfl (fun p _ => rfl)
      _ = ∏ r : Fin m, ∑ q : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} → ι,
            ∏ x : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r}, M x.1 (q (Equiv.Perm.cycleFiberSuccessor σ r x)) (q x) :=
          (Fintype.prod_sum (fun (r : Fin m) (q : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} → ι) =>
            ∏ x : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r}, M x.1 (q (Equiv.Perm.cycleFiberSuccessor σ r x)) (q x))).symm
      _ = ∏ r ∈ Equiv.Perm.cycleRepresentatives σ, ∑ q : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} → ι,
            ∏ x : {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r}, M x.1 (q (Equiv.Perm.cycleFiberSuccessor σ r x)) (q x) := by
          refine (Finset.prod_subset (Finset.subset_univ _) (fun r _ hr => ?_)).symm
          have hempty : IsEmpty {x : Fin m // Equiv.Perm.cycleRepresentative σ x = r} :=
            ⟨fun x => hr (x.2 ▸ Equiv.Perm.cycleRepresentative_mem σ x.1)⟩
          simp [Finset.prod_of_isEmpty]
      _ = ∏ r ∈ Equiv.Perm.cycleRepresentatives σ, Matrix.trace (Matrix.permutationCycleProduct σ M r) :=
          Finset.prod_congr rfl (fun r hr => Matrix.sum_cycleFiberWeights_eq_trace σ M hr)

end MatrixCombinatorics

/-! ## The cycle-trace identity -/

/-- The ordered product of a family of endomorphisms around the permutation cycle through an index. -/
noncomputable def LinearMap.cycleProduct (σ : Equiv.Perm (Fin n)) (A : Fin n → Module.End k V)
    (i : Fin n) : Module.End k V :=
  (((List.range (Equiv.Perm.cycleLengthAt σ i)).map (fun t => A ((σ⁻¹ ^ t) i)))).prod

/-- The trace of an endomorphism product around a permutation cycle equals the matrix trace of the corresponding cycle product. -/
theorem LinearMap.trace_cycleProduct_eq_matrixTrace (σ : Equiv.Perm (Fin n)) (A : Fin n → Module.End k V) (i : Fin n) :
    LinearMap.trace k V (LinearMap.cycleProduct k V n σ A i)
      = Matrix.trace (Matrix.permutationCycleProduct σ
          (fun j => LinearMap.toMatrix (Module.Finite.chosenBasis k V) (Module.Finite.chosenBasis k V) (A j)) i) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k (Module.Finite.chosenBasis k V)]
  congr 1
  rw [LinearMap.cycleProduct, Matrix.permutationCycleProduct]
  change LinearMap.toMatrixAlgEquiv (Module.Finite.chosenBasis k V) (List.prod _) = _
  rw [map_list_prod, List.map_map]
  rfl

/-- The trace of a permuted tensor endomorphism factors into traces of endomorphism products over the permutation cycles. -/
theorem LinearMap.trace_permutedTensorEndomorphism_eq_prod (σ : Equiv.Perm (Fin n)) (A : Fin n → Module.End k V) :
    LinearMap.trace k _ (LinearMap.permutedTensorEndomorphism k V n σ A)
      = ∏ i ∈ Equiv.Perm.cycleRepresentatives σ, LinearMap.trace k V (LinearMap.cycleProduct k V n σ A i) := by
  rw [LinearMap.trace_permutedTensorEndomorphism_eq_sum, Matrix.sum_permutationWeights_eq_prod_cycleTraces]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [LinearMap.trace_cycleProduct_eq_matrixTrace]

end RepresentationTheory.LinearAlgebra.TensorPower.PermutationTrace
