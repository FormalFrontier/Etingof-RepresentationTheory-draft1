/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.LinearAlgebra.SymmetricTensors
import RepresentationTheory.Infrastructure.Triangularization
import RepresentationTheory.Alignment.Attribute

/-! # Triangular bases and induced traces -/

namespace RepresentationTheory.LinearAlgebra.Triangularization

open Finset

/-- Two pointwise ordered finite index maps are equal when their associated index data agree. -/
lemma eq_of_le_of_indexData_eq {N n : ℕ} {f g : Fin n → Fin N}
    (hsym : RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux3 f =
      RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux3 g)
    (hle : ∀ i, f i ≤ g i) : f = g := by
  obtain ⟨σ, rfl⟩ :=
    RepresentationTheory.LinearAlgebra.SymmetricTensors.exists_witness_aux1.1 hsym
  have hsum : ∑ i, ((g (σ i) : ℕ)) = ∑ i, ((g i : ℕ)) :=
    Fintype.sum_equiv σ (fun i => ((g (σ i) : ℕ))) (fun i => ((g i : ℕ))) fun _ => rfl
  have hle' : ∀ i ∈ (Finset.univ : Finset (Fin n)), ((g (σ i) : ℕ)) ≤ ((g i : ℕ)) :=
    fun i _ => Fin.le_def.mp (hle i)
  have key := (Finset.sum_eq_sum_iff_of_le hle').1 hsum
  funext i
  exact Fin.ext (key i (Finset.mem_univ i))

/-- Reindexes a product over a finite ordered set by its order embedding from a finite type. -/
lemma prod_orderEmbOfFin {α M : Type*} [LinearOrder α] [CommMonoid M] (t : Finset α) {n : ℕ}
    (ht : t.card = n) (f : α → M) : ∏ i, f (t.orderEmbOfFin ht i) = ∏ x ∈ t, f x := by
  rw [← Finset.prod_coe_sort t f]
  exact Fintype.prod_equiv (t.orderIsoOfFin ht).toEquiv _ _ fun i => by
    rw [OrderIso.coe_toEquiv, Finset.coe_orderIsoOfFin_apply]

section Triangular

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- A predicate relating an endomorphism, a finite basis, and an indexed scalar family through
triangularization data. -/
structure HasTriangularBasis {N : ℕ} (A : V →ₗ[k] V) (b : Module.Basis (Fin N) k V)
    (lam : Fin N → k) : Prop where
  /-- The matrix of an endomorphism in such a basis is block triangular with respect to the index
  order. -/
  blockTriangular : (LinearMap.toMatrix b b A).BlockTriangular id
  /-- Identifies each diagonal matrix entry with its corresponding indexed scalar. -/
  diagonal_eq : ∀ i, LinearMap.toMatrix b b A i i = lam i

variable {N : ℕ} {A : V →ₗ[k] V} {b : Module.Basis (Fin N) k V} {lam : Fin N → k}

/-- A block triangular matrix gives the triangularity predicate for its associated linear map,
standard basis, and diagonal entries. -/
lemma hasTriangularBasis_of_blockTriangular {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (hM : M.BlockTriangular id) :
    HasTriangularBasis (Matrix.toLin (Pi.basisFun k (Fin N)) (Pi.basisFun k (Fin N)) M)
      (Pi.basisFun k (Fin N)) (fun i => M i i) :=
  ⟨by rwa [LinearMap.toMatrix_toLin], fun i => by rw [LinearMap.toMatrix_toLin]⟩

/-- Expresses the characteristic polynomial as the product formed from the indexed scalars. -/
theorem HasTriangularBasis.charpoly_eq (h : HasTriangularBasis A b lam) :
    letI := Module.Finite.of_basis b
    letI := Module.Free.of_basis b
    LinearMap.charpoly A = ∏ i, (Polynomial.X - Polynomial.C (lam i)) := by
  letI := Module.Finite.of_basis b
  letI := Module.Free.of_basis b
  rw [← LinearMap.charpoly_toMatrix A b, Matrix.charpoly_of_upperTriangular _ h.blockTriangular]
  exact Finset.prod_congr rfl fun i _ => by rw [h.diagonal_eq]

/-- A product of selected matrix entries vanishes for distinct index maps satisfying the stated
condition. -/
lemma matrixEntryProduct_eq_zero_of_ne (h : HasTriangularBasis A b lam) {n : ℕ}
    {f g : Fin n → Fin N}
    (hsym : RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux3 f =
      RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux3 g)
    (hfg : f ≠ g) : ∏ i, LinearMap.toMatrix b b A (f i) (g i) = 0 := by
  by_contra hne
  refine hfg (eq_of_le_of_indexData_eq hsym fun i => ?_)
  by_contra hlt
  exact hne (Finset.prod_eq_zero (Finset.mem_univ i) (h.blockTriangular (not_le.1 hlt)))

end Triangular

section Exterior

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {N : ℕ} {A : V →ₗ[k] V} {b : Module.Basis (Fin N) k V} {lam : Fin N → k}

/-- The displayed map on an exterior-power subspace commutes with the induced endomorphism. -/
lemma exteriorPowerMap_commutes (A : V →ₗ[k] V) (n : ℕ) (x : ⋀[k]^n V) :
    RepresentationTheory.LinearAlgebra.TensorOperations.linearMap A n
        (RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv (V := V) n x) =
      RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv (V := V) n
        (exteriorPower.map n A x) :=
  LinearMap.congr_fun
    (RepresentationTheory.LinearAlgebra.TensorOperations.linearMap_comp_eq_aux1 A n) x

/-- A diagonal entry of the induced exterior-power matrix equals the determinant of the
corresponding minor. -/
lemma exteriorPowerMatrix_diag_eq_minorDet (A : V →ₗ[k] V)
    (b : Module.Basis (Fin N) k V) {n : ℕ} (s : Set.powersetCard (Fin N) n) :
    LinearMap.toMatrix
        (RepresentationTheory.LinearAlgebra.TensorOperations.distinguishedElement b n)
        (RepresentationTheory.LinearAlgebra.TensorOperations.distinguishedElement b n)
        (RepresentationTheory.LinearAlgebra.TensorOperations.linearMap A n) s s =
      ((LinearMap.toMatrix b b A).submatrix
          (Finset.orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s))
          (Finset.orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s))).det := by
  classical
  rw [LinearMap.toMatrix_apply,
    RepresentationTheory.LinearAlgebra.TensorOperations.distinguishedElement,
    Module.Basis.map_apply, exteriorPowerMap_commutes, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.basis_repr_apply,
    exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti,
    ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.transpose_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.coord_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]

/-- Computes the trace of the indicated exterior-power endomorphism as a sum of products of
indexed scalars. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
theorem trace_exteriorPower_eq_subsetSum (h : HasTriangularBasis A b lam) (n : ℕ) :
    LinearMap.trace k
        (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType k V n)
        (RepresentationTheory.LinearAlgebra.TensorOperations.linearMap A n) =
      ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), ∏ i ∈ s, lam i := by
  classical
  have hconv :
      ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), ∏ i ∈ s, lam i =
        ∑ s : Set.powersetCard (Fin N) n, ∏ i ∈ (s : Finset (Fin N)), lam i :=
    Finset.sum_subtype _ (fun x => by simp [Finset.mem_powersetCard]) _
  rw [LinearMap.trace_eq_matrix_trace k
    (RepresentationTheory.LinearAlgebra.TensorOperations.distinguishedElement b n)
    (RepresentationTheory.LinearAlgebra.TensorOperations.linearMap A n), Matrix.trace, hconv]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.diag_apply, exteriorPowerMatrix_diag_eq_minorDet]
  have hmono : StrictMono
      (Finset.orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s)) :=
    OrderEmbedding.strictMono _
  have htri : ((LinearMap.toMatrix b b A).submatrix
      (Finset.orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s))
      (Finset.orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s))).BlockTriangular
      id := fun _ _ hij => h.blockTriangular (hmono hij)
  rw [Matrix.det_of_upperTriangular htri]
  simpa [Matrix.submatrix_apply, h.diagonal_eq] using
    prod_orderEmbOfFin (s : Finset (Fin N)) (Set.powersetCard.card_eq s) lam

/-- Computes the top exterior-power trace as the product of the indexed scalars. -/
theorem trace_exteriorPower_top_eq_prod (h : HasTriangularBasis A b lam) :
    LinearMap.trace k
        (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType k V N)
        (RepresentationTheory.LinearAlgebra.TensorOperations.linearMap A N) = ∏ i, lam i := by
  classical
  have hself : Finset.powersetCard N (Finset.univ : Finset (Fin N)) = {Finset.univ} := by
    have hself := Finset.powersetCard_self (Finset.univ : Finset (Fin N))
    rwa [Finset.card_univ, Fintype.card_fin] at hself
  rw [trace_exteriorPower_eq_subsetSum h N, hself, Finset.sum_singleton]

/-- Computes the degree-one exterior-power trace as the sum of the indexed scalars. -/
theorem trace_exteriorPower_one_eq_sum (h : HasTriangularBasis A b lam) :
    LinearMap.trace k
        (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType k V 1)
        (RepresentationTheory.LinearAlgebra.TensorOperations.linearMap A 1) = ∑ i, lam i := by
  classical
  rw [trace_exteriorPower_eq_subsetSum h 1, Finset.powersetCard_one, Finset.sum_map]
  simp

end Exterior

section Symmetric

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {N : ℕ} {A : V →ₗ[k] V} {b : Module.Basis (Fin N) k V} {lam : Fin N → k}

/-- Computes the coordinates of the specified vector in the constructed basis as a single
supported function. -/
lemma repr_auxiliaryBasisVector_eq_single {I : Type*} (b : Module.Basis I k V) (n : ℕ)
    (g : Fin n → I) :
    (RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux1 b n).repr
        (RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap k V n
          fun i => b (g i)) =
      Finsupp.single
        (RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux3 g) 1 :=
  RepresentationTheory.LinearAlgebra.SymmetricTensors.map_apply_aux4 b n g

/-- Computes the trace of the indicated symmetric-power endomorphism by a sum over multisets. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
theorem trace_symmetricPower_eq_multisetSum (h : HasTriangularBasis A b lam) (n : ℕ) :
    LinearMap.trace k
        (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n)
        (RepresentationTheory.LinearAlgebra.TensorOperations.linearMap_aux2 A n) =
      ∑ s : Sym (Fin N) n, ((s : Multiset (Fin N)).map lam).prod := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k
    (RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux1 b n)
    (RepresentationTheory.LinearAlgebra.TensorOperations.linearMap_aux2 A n), Matrix.trace]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨g, rfl⟩ : ∃ g : Fin n → Fin N,
      RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux3 g = s :=
    ⟨RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement n s,
      RepresentationTheory.LinearAlgebra.SymmetricTensors.displayed_eq_aux2 n s⟩
  have hprod :
      ((RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux3 g :
          Multiset (Fin N)).map lam).prod = ∏ i, lam (g i) := by
    rw [RepresentationTheory.LinearAlgebra.SymmetricTensors.displayed_eq_aux1,
      Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  have hA : ∀ j, A (b j) = ∑ p, LinearMap.toMatrix b b A p j • b p := fun j => by
    conv_lhs => rw [← b.sum_repr (A (b j))]
    exact Finset.sum_congr rfl fun p _ => by rw [LinearMap.toMatrix_apply]
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    RepresentationTheory.LinearAlgebra.SymmetricTensors.map_apply_aux2 b n _ g rfl,
    RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux5]
  simp_rw [hA]
  rw [MultilinearMap.map_sum]
  simp_rw [MultilinearMap.map_smul_univ]
  rw [map_sum, Finsupp.finsetSum_apply]
  simp_rw [map_smul, Finsupp.smul_apply, repr_auxiliaryBasisVector_eq_single, smul_eq_mul]
  rw [Finset.sum_eq_single g]
  · rw [Finsupp.single_eq_same, mul_one, hprod]
    exact Finset.prod_congr rfl fun i _ => h.diagonal_eq (g i)
  · intro f _ hfg
    by_cases hfs :
      RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux3 f =
        RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux3 g
    · rw [matrixEntryProduct_eq_zero_of_ne h hfs hfg, zero_mul]
    · rw [Finsupp.single_eq_of_ne' hfs, mul_zero]
  · exact fun hg => absurd (Finset.mem_univ g) hg

/-- Computes the degree-one symmetric-power trace as the sum of the indexed scalars. -/
theorem trace_symmetricPower_one_eq_sum (h : HasTriangularBasis A b lam) :
    LinearMap.trace k
        (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V 1)
        (RepresentationTheory.LinearAlgebra.TensorOperations.linearMap_aux2 A 1) = ∑ i, lam i := by
  classical
  rw [trace_symmetricPower_eq_multisetSum h 1]
  exact (Fintype.sum_equiv Sym.oneEquiv lam
    (fun s => ((s : Multiset (Fin N)).map lam).prod) fun i => by simp).symm

end Symmetric

section Charpoly

open Polynomial

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- A splitting characteristic polynomial and the stated dimension yield a basis and scalar family
satisfying the triangularity predicate. -/
theorem exists_hasTriangularBasis {N : ℕ} (A : V →ₗ[k] V) (hN : Module.finrank k V = N)
    (hsplit : (LinearMap.charpoly A).Splits) :
    ∃ (b : Module.Basis (Fin N) k V) (lam : Fin N → k), HasTriangularBasis A b lam := by
  obtain ⟨b, lam, hb, hdiag, -⟩ :=
    RepresentationTheory.Infrastructure.Triangularization.exists_basis_diagonal_charpoly_of_splits
      A hN hsplit
  exact ⟨b, lam, hb, hdiag⟩

/-- Derives the exterior-power trace formula from a factorization of the characteristic
polynomial. -/
@[source_ref "Chapter2/Problem2.11.3" (role := primary)]
theorem trace_exteriorPower_eq_subsetSum_of_charpoly {N : ℕ} (A : V →ₗ[k] V)
    (hN : Module.finrank k V = N) (lam : Fin N → k)
    (hlam : LinearMap.charpoly A = ∏ i, (X - C (lam i))) (n : ℕ) :
    LinearMap.trace k
        (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType k V n)
        (RepresentationTheory.LinearAlgebra.TensorOperations.linearMap A n) =
      ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), ∏ i ∈ s, lam i := by
  obtain ⟨b, e, hb, hdiag⟩ :=
    RepresentationTheory.Infrastructure.Triangularization.exists_basis_diagonal_comp_perm_of_charpoly_eq_prod
      A hN lam hlam
  rw [trace_exteriorPower_eq_subsetSum
    (⟨hb, hdiag⟩ : HasTriangularBasis A b fun i => lam (e i)) n]
  exact
    RepresentationTheory.Infrastructure.Triangularization.sum_powersetCard_prod_comp_perm
      lam e n

/-- Derives the symmetric-power trace formula from the displayed characteristic-polynomial
factorization. -/
@[source_ref "Chapter2/Problem2.11.3" (role := primary)]
theorem trace_symmetricPower_eq_multisetSum_of_charpoly {N : ℕ} (A : V →ₗ[k] V)
    (hN : Module.finrank k V = N) (lam : Fin N → k)
    (hlam : LinearMap.charpoly A = ∏ i, (X - C (lam i))) (n : ℕ) :
    LinearMap.trace k
        (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n)
        (RepresentationTheory.LinearAlgebra.TensorOperations.linearMap_aux2 A n) =
      ∑ s : Sym (Fin N) n, ((s : Multiset (Fin N)).map lam).prod := by
  obtain ⟨b, e, hb, hdiag⟩ :=
    RepresentationTheory.Infrastructure.Triangularization.exists_basis_diagonal_comp_perm_of_charpoly_eq_prod
      A hN lam hlam
  rw [trace_symmetricPower_eq_multisetSum
    (⟨hb, hdiag⟩ : HasTriangularBasis A b fun i => lam (e i)) n]
  exact RepresentationTheory.Infrastructure.Triangularization.sum_sym_prod_map_comp_perm lam e n

end Charpoly

end RepresentationTheory.LinearAlgebra.Triangularization
