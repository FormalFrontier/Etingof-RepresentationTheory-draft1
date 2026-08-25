/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Cardinality
import RepresentationTheory.RingPredicateBounds
import RepresentationTheory.LinearAlgebra.ModuleDecompositions
import RepresentationTheory.Algebra.Module.IndependentSpanningFamilies
import RepresentationTheory.ModuleFamilyNatMatrix
import RepresentationTheory.Auxiliary.RingData
import RepresentationTheory.Algebra.Module.CompositionSeries
import RepresentationTheory.InvolutiveSquareZeroAlgebra
import RepresentationTheory.Algebra.FieldIndexedType
import RepresentationTheory.Alignment.Attribute

/-! # Projective modules -/



universe u

open scoped Polynomial

open CategoryTheory


/-- Identifies the displayed value with top when every indexed condition fails. -/
theorem RepresentationTheory.LinearAlgebra.Module.Projective.value_eq_top_of_forall_not_indexedProperty {R : Type u} [Ring R]
    (h : ∀ d, ¬ RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty R d) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant R = ⊤ := by
  refine le_antisymm le_top ?_
  unfold RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant
  exact le_iInf₂ (fun d hd => absurd hd (h d))

namespace RepresentationTheory.LinearAlgebra.Module.Projective


/-- The formal statement of this theorem was not rendered in the packet. -/
theorem unrenderedTheorem
    {ι : Type*} [Fintype ι] [DecidableEq ι] (C D : Matrix ι ι ℤ) (h : C * D = 1) :
    C.det = 1 ∨ C.det = -1 :=
  Int.eq_one_or_neg_one_of_mul_eq_one (by rw [← Matrix.det_mul, h, Matrix.det_one])


/-- Constructs a right inverse for a square integer matrix from solutions on every standard basis vector. -/
theorem existsRightInverse_of_mulVec_eq_single
    {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℤ)
    (h : ∀ j, ∃ d : ι → ℤ, C.mulVec d = Pi.single j 1) :
    ∃ D : Matrix ι ι ℤ, C * D = 1 := by
  choose d hd using h
  refine ⟨Matrix.of fun i j => d j i, ?_⟩
  ext i j
  have hcol : (C * Matrix.of fun i j => d j i) i j = C.mulVec (d j) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, Matrix.of_apply, dotProduct]
  rw [hcol, hd j]
  simp [Pi.single_apply, Matrix.one_apply]


/-- Records the integer-valued ranks of linear maps from the members of a module family. -/
noncomputable def linearMapFinranks
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    (N : Type*) [AddCommGroup N] [Module A N] [Module k N] [SMulCommClass A k N] : ι → ℤ :=
  fun i => (Module.finrank k (P i →ₗ[A] N) : ℤ)


/-- Identifies a rank-vector coordinate on a family member with the corresponding matrix entry. -/
theorem linearMapFinranks_apply_family
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, SMulCommClass A k (P i)] (i j : ι) :
    linearMapFinranks (k := k) (A := A) P (P j) i =
      ((RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)) i j := by
  simp [linearMapFinranks, RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix]


/-- Computes the rank vector on a reference family from a Kronecker-delta rank condition. -/
theorem linearMapFinranks_eq_single_of_finrank_eq_ite
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} [DecidableEq ι] (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] [∀ i, Module k (M i)]
    [∀ i, SMulCommClass A k (M i)]
    (hP_cover : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0) (j : ι) :
    linearMapFinranks (k := k) (A := A) P (M j) = Pi.single j 1 := by
  funext i
  simp only [linearMapFinranks, hP_cover i j, Pi.single_apply]
  split <;> simp_all [eq_comm]


/-- Splits the rank vector across a submodule and its quotient under the given finiteness hypotheses. -/
theorem linearMapFinranks_quotient
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)] [∀ i, Module.Finite k (P i)]
    (N : Type*) [AddCommGroup N] [Module A N] [Module k N]
    [IsScalarTower k A N] [SMulCommClass A k N] [Module.Finite k N]
    (N' : Submodule A N) :
    linearMapFinranks (k := k) (A := A) P N =
      linearMapFinranks (k := k) (A := A) P N' + linearMapFinranks (k := k) (A := A) P (N ⧸ N') := by
  funext i
  simp only [linearMapFinranks, Pi.add_apply]
  rw [RepresentationTheory.Algebra.Module.CompositionSeries.Module.finrank_hom_eq_finrank_hom_submodule_add_quotient (P := P i) N']
  push_cast
  ring

section DirectSum

open scoped DirectSum

attribute [local instance] Module.Free.of_divisionRing


/-- Shows that the rank vector is unchanged by a linear equivalence of target modules. -/
theorem linearMapFinranks_linearEquiv
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [SMulCommClass A k M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    [SMulCommClass A k N]
    (e : M ≃ₗ[A] N) :
    linearMapFinranks (k := k) (A := A) P M = linearMapFinranks (k := k) (A := A) P N := by
  funext i
  simp only [linearMapFinranks]
  congr 1
  refine LinearEquiv.finrank_eq
    { toFun := fun f => e.toLinearMap.comp f
      invFun := fun f => e.symm.toLinearMap.comp f
      map_add' := fun f g => by ext x; simp
      map_smul' := fun c f => by
        ext x; simpa using LinearMapClass.map_smul_of_tower e c (f x)
      left_inv := fun f => by ext x; simp
      right_inv := fun f => by ext x; simp }


/-- Computes the rank vector of a finite dependent product as the sum of its component vectors. -/
theorem linearMapFinranks_pi
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k A (P i)] [∀ i, Module.Finite k (P i)]
    {σ : Type*} [Fintype σ] (Q : σ → Type*)
    [∀ s, AddCommGroup (Q s)] [∀ s, Module A (Q s)] [∀ s, Module k (Q s)]
    [∀ s, IsScalarTower k A (Q s)] [∀ s, SMulCommClass A k (Q s)] [∀ s, Module.Finite k (Q s)] :
    linearMapFinranks (k := k) (A := A) P (∀ s, Q s) =
      ∑ s, linearMapFinranks (k := k) (A := A) P (Q s) := by
  funext l
  rw [Finset.sum_apply]
  simp only [linearMapFinranks]
  rw [← Nat.cast_sum]
  congr 1
  rw [LinearEquiv.finrank_eq
    (show (P l →ₗ[A] ∀ s, Q s) ≃ₗ[k] ∀ s, (P l →ₗ[A] Q s) from
      { toFun := fun f s => (LinearMap.proj s).comp f
        invFun := fun g => LinearMap.pi g
        map_add' := fun f g => by funext s; ext x; simp
        map_smul' := fun c f => by funext s; ext x; simp
        left_inv := fun f => by
          refine LinearMap.ext fun x => ?_; funext s; simp
        right_inv := fun g => by funext s; ext x; simp })]
  exact Module.finrank_pi_fintype k


/-- Computes the rank vector of a finite direct sum as the sum of the individual vectors. -/
theorem linearMapFinranks_directSum
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k A (P i)] [∀ i, Module.Finite k (P i)]
    {σ : Type*} [Fintype σ] (Q : σ → Type*)
    [∀ s, AddCommGroup (Q s)] [∀ s, Module A (Q s)] [∀ s, Module k (Q s)]
    [∀ s, IsScalarTower k A (Q s)] [∀ s, SMulCommClass A k (Q s)] [∀ s, Module.Finite k (Q s)] :
    linearMapFinranks (k := k) (A := A) P (⨁ s, Q s) =
      ∑ s, linearMapFinranks (k := k) (A := A) P (Q s) := by
  rw [linearMapFinranks_linearEquiv P (DirectSum.linearEquivFunOnFintype A σ Q)]
  exact linearMapFinranks_pi P Q


/-- The formal statement of this theorem was not rendered in the packet. -/
theorem linearMapFinranks_matrixAuxiliaryTwo
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)] [∀ i, Module.Finite k (P i)]
    (a : ι → ℕ) :
    linearMapFinranks (k := k) (A := A) P (⨁ p : (Σ i, Fin (a i)), P p.1) =
      ((RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).mulVec
        (fun i => (a i : ℤ)) := by
  rw [linearMapFinranks_directSum P (fun p : (Σ i, Fin (a i)) => P p.1)]
  funext l
  rw [Finset.sum_apply, Fintype.sum_sigma]
  simp only [linearMapFinranks_apply_family, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul, mul_comm]


/-- The formal statement of this theorem was not rendered in the packet. -/
theorem linearMapFinranks_matrixAuxiliary
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)] [∀ i, Module.Finite k (P i)]
    (a : ι → ℕ) {N : Type*} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    [SMulCommClass A k N] (e : N ≃ₗ[A] ⨁ p : (Σ i, Fin (a i)), P p.1) :
    linearMapFinranks (k := k) (A := A) P N =
      ((RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).mulVec
        (fun i => (a i : ℤ)) := by
  rw [linearMapFinranks_linearEquiv P e, linearMapFinranks_matrixAuxiliaryTwo]


/-- Classifies modules with the displayed property up to linear equivalence with a member of the given family. -/
theorem exists_linearEquiv_of_moduleProperty
    {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)] [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM_complete : ∀ (S : Type u) [AddCommGroup S] [Module A S], IsSimpleModule A S →
        ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (P i))
    (hP_cover : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (Q : Type u) [AddCommGroup Q] [Module A Q] [Module k Q] [IsScalarTower k A Q]
    [SMulCommClass A k Q] [Module.Projective A Q] [Module.Finite A Q]
    (hQ_indec : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A Q) :
    ∃ i, Nonempty (Q ≃ₗ[A] P i) := by
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  haveI : Nontrivial Q := hQ_indec.1
  haveI : Module.Finite k Q := Module.Finite.trans A Q
  haveI : FiniteDimensional k Q := ‹Module.Finite k Q›
  
  obtain ⟨N, hN_coatom⟩ := RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.exists_isCoatom_submodule (R := A) (M := Q)
  haveI : IsSimpleModule A (Q ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN_coatom
  obtain ⟨j₀, ⟨e⟩⟩ := hM_complete (Q ⧸ N) inferInstance
  refine ⟨j₀, ?_⟩
  
  set φ : Q →ₗ[A] M j₀ := e.toLinearMap.comp N.mkQ with hφdef
  have hφ : φ ≠ 0 := by
    intro h
    apply hN_coatom.1
    rw [Submodule.eq_top_iff']
    intro q
    have h1 : e (N.mkQ q) = 0 := by
      have := LinearMap.congr_fun h q; simpa [hφdef] using this
    have h2 : N.mkQ q = 0 := e.injective (by rw [h1, map_zero])
    exact (Submodule.Quotient.mk_eq_zero N).mp h2
  
  haveI : FiniteDimensional k (P j₀) := Module.Finite.trans A (P j₀)
  haveI : Module.Finite A (M j₀) := Module.Finite.equiv e
  haveI : Module.Finite k (M j₀) := Module.Finite.trans A (M j₀)
  haveI : Module.Finite k (P j₀ →ₗ[A] M j₀) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A (P j₀) (M j₀) k)
      (LinearMap.restrictScalars_injective k)
  have hPdim : Module.finrank k (P j₀ →ₗ[A] M j₀) = 1 := by
    have := hP_cover j₀ j₀; simpa using this
  have hP_nt : Nontrivial (P j₀ →ₗ[A] M j₀) := by
    rw [← Module.finrank_pos_iff (R := k)]; omega
  obtain ⟨ψ, hψ⟩ := exists_ne (0 : P j₀ →ₗ[A] M j₀)
  exact RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.nonempty_linearEquiv_of_nonzero_maps_to_simple (k := k) hQ_indec (hP_indec j₀) φ hφ ψ hψ


/-- Expresses a rank vector as a matrix-vector product under the stated projectivity and simplicity assumptions. -/
theorem exists_linearMapFinranks_eq_matrix_mulVec
    {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)] [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM_complete : ∀ (S : Type u) [AddCommGroup S] [Module A S], IsSimpleModule A S →
        ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (P i))
    (hP_cover : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (N : Type u) [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    [SMulCommClass A k N] [Module.Projective A N] [Module.Finite A N] :
    ∃ a : ι → ℕ,
      linearMapFinranks (k := k) (A := A) P N =
        ((RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).mulVec
          (fun i => (a i : ℤ)) := by
  classical
  set C := (RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ) with hC
  haveI : ∀ i, Module.Finite k (P i) := fun i => Module.Finite.trans A (P i)
  haveI : Module.Finite k N := Module.Finite.trans A N
  haveI : FiniteDimensional k N := ‹Module.Finite k N›
  
  obtain ⟨n, W, hW_indec, hW_sup, hW_indep⟩ := RepresentationTheory.Algebra.Module.IndependentSpanningFamilies.exists_iSupIndep_eq_top k A N
  have hInt : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hW_indep hW_sup
  
  let e : N ≃ₗ[A] ⨁ i, (W i) := (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hInt).symm
  
  haveI : Module.Projective A (⨁ i, (W i)) := Module.Projective.of_equiv e
  haveI hWproj : ∀ i, Module.Projective A (W i) := fun i =>
    Module.Projective.of_split
      (DirectSum.lof A (Fin n) (fun j => (W j)) i)
      (DirectSum.component A (Fin n) (fun j => (W j)) i)
      (DirectSum.component_comp_lof_same A i)
  
  haveI hWfin : ∀ i, Module.Finite k (W i) := fun i =>
    Module.Finite.of_injective ((W i).restrictScalars k).subtype Subtype.val_injective
  haveI hWfinA : ∀ i, Module.Finite A (W i) := fun i =>
    Module.Finite.of_restrictScalars_finite k A (W i)
  
  have hWiso : ∀ i, ∃ j, Nonempty ((W i) ≃ₗ[A] P j) := fun i =>
    exists_linearEquiv_of_moduleProperty M hM_complete P hP_indec hP_cover (W i) (hW_indec i)
  choose g hg using hWiso
  refine ⟨fun j => (Finset.univ.filter (fun i => g i = j)).card, ?_⟩
  rw [linearMapFinranks_linearEquiv P e, linearMapFinranks_directSum P (fun i => (W i))]
  funext l
  rw [Finset.sum_apply]
  have step : ∀ i, linearMapFinranks (k := k) (A := A) P (W i) l = C l (g i) := by
    intro i
    rw [linearMapFinranks_linearEquiv P (hg i).some, linearMapFinranks_apply_family]
  simp_rw [step]
  
  simp only [Matrix.mulVec, dotProduct]
  have hRHS : ∀ j : ι,
      C l j * ((Finset.univ.filter (fun i => g i = j)).card : ℤ)
        = ∑ i ∈ Finset.univ.filter (fun i => g i = j), C l (g i) := by
    intro j
    rw [Finset.sum_congr rfl
      (fun i hi => (by rw [(Finset.mem_filter.mp hi).2] : C l (g i) = C l j))]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  simp_rw [hRHS]
  rw [Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (g i)) (fun i => C l (g i))]

end DirectSum


private theorem simpleModule_finite {A : Type*} [Ring A] (N : Type*) [AddCommGroup N]
    [Module A N] [IsSimpleModule A N] : Module.Finite A N := by
  haveI := IsSimpleModule.nontrivial A N
  obtain ⟨x, hx⟩ := exists_ne (0 : N)
  have hspan : Submodule.span A {x} = ⊤ := by
    rcases eq_bot_or_eq_top (Submodule.span A {x}) with h | h
    · rw [Submodule.span_singleton_eq_bot] at h; exact absurd h hx
    · exact h
  exact Module.finite_def.mpr ⟨{x}, by rw [Finset.coe_singleton]; exact hspan⟩


private theorem homClassVector_eq_mulVec_of_projectiveDimensionLE
    {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)] [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM_complete : ∀ (S : Type u) [AddCommGroup S] [Module A S], IsSimpleModule A S →
        ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (P i))
    (hP_cover : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (d : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
      [SMulCommClass A k N] [Module.Finite k N],
      HasProjectiveDimensionLE (ModuleCat.of A N) d →
      ∃ e : ι → ℤ,
        linearMapFinranks (k := k) (A := A) P N =
          ((RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).mulVec e := by
  haveI : ∀ i, Module.Finite k (P i) := fun i => Module.Finite.trans A (P i)
  induction d with
  | zero =>
    intro N _ _ _ _ _ _ hpd
    haveI hproj : Projective (ModuleCat.of A N) :=
      (projective_iff_hasProjectiveDimensionLE_zero _).mpr hpd
    haveI : Module.Projective A N := ModuleCat.projective_of_module_projective (ModuleCat.of A N)
    haveI : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
    obtain ⟨a, ha⟩ := exists_linearMapFinranks_eq_matrix_mulVec M hM_complete P hP_indec hP_cover N
    exact ⟨fun i => (a i : ℤ), ha⟩
  | succ d ih =>
    intro N _ _ _ _ _ _ hpd
    haveI : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A N
    
    haveI : Module.Projective A (Fin n → A) := Module.Projective.of_basis (Pi.basisFun A (Fin n))
    haveI : Module.Finite k (Fin n → A) := inferInstance
    haveI : Module.Finite k (LinearMap.ker f) :=
      Module.Finite.of_injective ((LinearMap.ker f).subtype.restrictScalars k)
        (LinearMap.ker f).injective_subtype
    have hSE := LinearMap.shortExact_shortComplexKer hf
    have hKpd : HasProjectiveDimensionLE (ModuleCat.of A (LinearMap.ker f)) d :=
      (hSE.hasProjectiveDimensionLT_X₃_iff d (inferInstance : Projective (ModuleCat.of A _))).mp hpd
    obtain ⟨eK, hKvec⟩ := ih (LinearMap.ker f) hKpd
    obtain ⟨a0, ha0⟩ :=
      exists_linearMapFinranks_eq_matrix_mulVec M hM_complete P hP_indec hP_cover (Fin n → A)
    
    have hadd := linearMapFinranks_quotient (k := k) (A := A) P (Fin n → A) (LinearMap.ker f)
    rw [linearMapFinranks_linearEquiv P (f.quotKerEquivOfSurjective hf)] at hadd
    refine ⟨(fun i => (a0 i : ℤ)) - eK, ?_⟩
    rw [Matrix.mulVec_sub, ← ha0, ← hKvec, hadd]
    abel


/-- The formal statement of this theorem was not rendered in the packet. -/
theorem unrenderedMatrixTheorem
    {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)] [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM_distinct : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_complete : ∀ (S : Type u) [AddCommGroup S] [Module A S], IsSimpleModule A S →
        ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)] [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (P i))
    (hP_cover : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (hfin : RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant A ≠ ⊤) :
    ((RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).det = 1 ∨
      ((RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ)).det = -1 := by
  set C := (RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix (k := k) (A := A) P).map (Nat.cast : ℕ → ℤ) with hC
  
  suffices h : ∃ D : Matrix ι ι ℤ, C * D = 1 by
    obtain ⟨D, hD⟩ := h
    exact unrenderedTheorem C D hD
  
  
  
  
  
  refine existsRightInverse_of_mulVec_eq_single C (fun j => ?_)
  
  
  suffices hEuler : ∃ d : ι → ℤ, C.mulVec d = linearMapFinranks (k := k) (A := A) P (M j) by
    obtain ⟨d, hd⟩ := hEuler
    exact ⟨d, by rw [hd, linearMapFinranks_eq_single_of_finrank_eq_ite P M hP_cover j]⟩
  
  
  
  
  
  
  
  
  
  
  
  obtain ⟨d₀, hd₀⟩ : ∃ d, RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty A d := by
    by_contra h
    rw [not_exists] at h
    exact hfin (RepresentationTheory.RingPredicateBounds.eq_top_of_forall_not_predicate h)
  haveI : Module.Finite A (M j) := simpleModule_finite (M j)
  haveI : Module.Finite k (M j) := Module.Finite.trans A (M j)
  obtain ⟨e, he⟩ := homClassVector_eq_mulVec_of_projectiveDimensionLE M hM_complete P hP_indec
    hP_cover d₀ (M j) (hd₀ (ModuleCat.of A (M j)))
  exact ⟨e, he.symm⟩


/-- Shows that the displayed value on a polynomial quotient is top when the exponent is greater than one. -/
@[source_ref "Chapter9/Problem9.4.5" (role := primary)]
theorem quotientPolynomialXPower_value_eq_top
    (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant (k[X] ⧸ Ideal.span {(Polynomial.X : k[X]) ^ n}) = ⊤ :=
  RepresentationTheory.Algebra.FieldIndexedType.fieldNatType_construction_eq_top_of_one_lt k n hn

open RepresentationTheory.InvolutiveSquareZeroAlgebra in

private theorem ext_extClass_comp_ne_zero
    {S : ShortComplex (ModuleCat.{0} RepresentationTheory.InvolutiveSquareZeroAlgebra.Algebra)} (hS : S.ShortExact)
    (hP : Projective S.X₂) {Y : ModuleCat.{0} RepresentationTheory.InvolutiveSquareZeroAlgebra.Algebra} {i : ℕ} (hi : 1 ≤ i)
    (e : Abelian.Ext S.X₁ Y i) (he : e ≠ 0) {n : ℕ} (hn : 1 + i = n) :
    hS.extClass.comp e hn ≠ 0 := by
  haveI := hP
  intro hzero
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y e hn hzero
  have hx₂0 : x₂ = 0 := Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT x₂ 1 hi
  rw [hx₂0, Abelian.Ext.comp_zero] at hx₂
  exact he hx₂.symm

open RepresentationTheory.InvolutiveSquareZeroAlgebra in

private theorem ext_odd_ne_zero (j : ℕ) :
    ∃ e : Abelian.Ext (ModuleCat.of RepresentationTheory.InvolutiveSquareZeroAlgebra.Algebra RepresentationTheory.InvolutiveSquareZeroAlgebra.PositiveSimple)
      (ModuleCat.of RepresentationTheory.InvolutiveSquareZeroAlgebra.Algebra RepresentationTheory.InvolutiveSquareZeroAlgebra.NegativeSimple) (2 * j + 1), e ≠ 0 := by
  induction j with
  | zero => exact ⟨firstShortComplex_shortExact.extClass, firstShortComplex_extClass_ne_zero⟩
  | succ j ih =>
    obtain ⟨e, he⟩ := ih
    have hPm : Projective secondShortComplex.X₂ := secondShortComplex_right_projective
    have hPp : Projective firstShortComplex.X₂ := firstShortComplex_right_projective
    have h1 := ext_extClass_comp_ne_zero secondShortComplex_shortExact hPm (i := 2 * j + 1) (by omega) e he
      (n := 2 * j + 2) (by ring)
    exact ⟨_, ext_extClass_comp_ne_zero firstShortComplex_shortExact hPp (i := 2 * j + 2) (by omega) _ h1
      (n := 2 * (j + 1) + 1) (by ring)⟩


/-- Establishes the top value of the displayed construction on the designated ring. -/
@[source_ref "Chapter9/Problem9.4.5" (role := primary)]
theorem designatedRing_value_eq_top :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant RepresentationTheory.InvolutiveSquareZeroAlgebra.Algebra = ⊤ := by
  refine RepresentationTheory.LinearAlgebra.Module.Projective.value_eq_top_of_forall_not_indexedProperty (fun d hd => ?_)
  obtain ⟨e, he⟩ := ext_odd_ne_zero d
  haveI hpd : HasProjectiveDimensionLE
      (ModuleCat.of RepresentationTheory.InvolutiveSquareZeroAlgebra.Algebra RepresentationTheory.InvolutiveSquareZeroAlgebra.PositiveSimple) d := hd _
  exact he (Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT e (d + 1) (by omega))

end RepresentationTheory.LinearAlgebra.Module.Projective

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.LinearAlgebra.Module.Projective.Auxiliary.statement013909 := _root_.RepresentationTheory.LinearAlgebra.Module.Projective.unrenderedMatrixTheorem

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.LinearAlgebra.Module.Projective.Auxiliary.statement013910 := _root_.RepresentationTheory.LinearAlgebra.Module.Projective.unrenderedTheorem

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.LinearAlgebra.Module.Projective.Auxiliary.statement013918 := _root_.RepresentationTheory.LinearAlgebra.Module.Projective.linearMapFinranks_matrixAuxiliary

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.LinearAlgebra.Module.Projective.Auxiliary.statement013919 := _root_.RepresentationTheory.LinearAlgebra.Module.Projective.linearMapFinranks_matrixAuxiliaryTwo

attribute [source_ref "Chapter9/Problem9.4.5" (role := supporting)] _root_.RepresentationTheory.LinearAlgebra.Module.Projective.Auxiliary.statement013909
