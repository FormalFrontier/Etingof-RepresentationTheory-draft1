/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Lean.Elab.Tactic.Omega

/-! # Triangularization of linear endomorphisms -/

open Polynomial Module

namespace RepresentationTheory.Infrastructure.Triangularization

section Criterion

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The matrix of an endomorphism in a basis is block triangular with respect to the identity
order if and only if each basis vector is mapped into the span of the basis vectors indexed at
most by it. -/
theorem toMatrix_blockTriangular_iff {N : ℕ} (b : Basis (Fin N) k V) (A : V →ₗ[k] V) :
    (LinearMap.toMatrix b b A).BlockTriangular id ↔
      ∀ j, A (b j) ∈ Submodule.span k (b '' Set.Iic j) := by
  constructor
  · intro h j
    refine b.mem_span_image.2 fun i hi => ?_
    by_contra hij
    exact Finsupp.mem_support_iff.1 hi ((LinearMap.toMatrix_apply b b A i j) ▸ h (not_le.1 hij))
  · intro h i j hij
    rw [LinearMap.toMatrix_apply]
    by_contra hne
    exact absurd (b.mem_span_image.1 (h j) (Finsupp.mem_support_iff.2 hne)) (not_le.2 hij)

/-- If every basis vector is mapped into the span of the basis vectors indexed at most by it,
then the matrix of the endomorphism in that basis is block triangular with respect to the identity
order. -/
theorem toMatrix_blockTriangular_of_mem_span_Iic {N : ℕ} (b : Basis (Fin N) k V)
    (A : V →ₗ[k] V) (h : ∀ j, A (b j) ∈ Submodule.span k (b '' Set.Iic j)) :
    (LinearMap.toMatrix b b A).BlockTriangular id :=
  (toMatrix_blockTriangular_iff b A).2 h

end Criterion

section Existence

variable {k : Type u} [Field k]

/-- If the minimal polynomial of an endomorphism splits and the module has the specified finite
rank, then some basis gives the endomorphism a block-triangular matrix. -/
theorem exists_basis_blockTriangular_of_minpoly_splits (k : Type u) [Field k] :
    ∀ (N : ℕ) {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V] (A : V →ₗ[k] V),
      Module.finrank k V = N → (minpoly k A).Splits →
      ∃ b : Basis (Fin N) k V, (LinearMap.toMatrix b b A).BlockTriangular id := by
  intro N
  induction N with
  | zero =>
      intro V _ _ _ A hN _
      have : Subsingleton V := by
        have := Module.finrank_zero_iff (R := k) (M := V) |>.mp hN
        exact this
      exact ⟨Basis.empty V, fun i _ _ => i.elim0⟩
  | succ N ih =>
      intro V _ _ _ A hN hsplit
      haveI : Nontrivial V :=
        Module.nontrivial_of_finrank_pos (R := k) (M := V) (by rw [hN]; omega)
      have hint : IsIntegral k A := Algebra.IsIntegral.isIntegral (R := k) A
      obtain ⟨μ, hμ⟩ : ∃ μ : k, Module.End.HasEigenvalue A μ := by
        obtain ⟨a, ha⟩ := hsplit.exists_eval_eq_zero (ne_of_gt (minpoly.degree_pos hint))
        exact ⟨a, Module.End.hasEigenvalue_iff_isRoot.2 ha⟩
      obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
      have hv0 : v ≠ 0 := hv.2
      have hAv : A v = μ • v := hv.apply_eq_smul
      set S : Submodule k V := k ∙ v with hSdef
      have hvS : v ∈ S := Submodule.mem_span_singleton_self v
      have hcomap : S ≤ S.comap A := by
        rw [hSdef, Submodule.span_le]
        rintro x hx
        obtain rfl : x = v := hx
        simpa [hAv] using Submodule.smul_mem S μ hvS
      set A' : (V ⧸ S) →ₗ[k] (V ⧸ S) := S.mapQ S A hcomap with hA'def
      have hstep : ∀ x : V, A' (S.mkQ x) = S.mkQ (A x) := fun x => rfl
      have hpow : ∀ (n : ℕ) (x : V), (A' ^ n) (S.mkQ x) = S.mkQ ((A ^ n) x) := by
        intro n
        induction n with
        | zero => intro x; simp
        | succ n ihn => intro x; simp only [pow_succ, Module.End.mul_apply, hstep, ihn]
      have haeval : ∀ (q : k[X]) (x : V),
          (Polynomial.aeval A' q) (S.mkQ x) = S.mkQ ((Polynomial.aeval A q) x) := by
        intro q
        induction q using Polynomial.induction_on' with
        | add p q hp hq => intro x; simp only [map_add, LinearMap.add_apply, hp, hq, map_add]
        | monomial n a =>
            intro x
            simp only [Polynomial.aeval_monomial, Module.algebraMap_end_eq_smul_id,
              Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, hpow, map_smul]
      have hA'zero : Polynomial.aeval A' (minpoly k A) = 0 := by
        refine LinearMap.ext fun w => ?_
        obtain ⟨x, rfl⟩ := S.mkQ_surjective w
        rw [haeval, minpoly.aeval]
        simp
      have hsplit' : (minpoly k A').Splits :=
        hsplit.of_dvd (minpoly.ne_zero hint) (minpoly.dvd k A' hA'zero)
      have hrank : Module.finrank k (V ⧸ S) = N := by
        have h1 := S.finrank_quotient_add_finrank (R := k)
        have h2 : Module.finrank k S = 1 := by rw [hSdef]; exact finrank_span_singleton hv0
        omega
      obtain ⟨c, hc⟩ := ih A' hrank hsplit'
      obtain ⟨σ, hσ⟩ := S.mkQ.exists_rightInverse_of_surjective S.range_mkQ
      have hσ' : ∀ w : V ⧸ S, S.mkQ (σ w) = w := fun w => by
        simpa using LinearMap.congr_fun hσ w
      have hσinj : Function.Injective σ := Function.LeftInverse.injective hσ'
      have hrange : Submodule.span k (Set.range (σ ∘ c)) = LinearMap.range σ := by
        rw [Set.range_comp, Submodule.span_image, c.span_eq, Submodule.map_top]
      have hvnot : v ∉ Submodule.span k (Set.range (σ ∘ c)) := by
        rw [hrange]
        rintro ⟨y, hy⟩
        refine hv0 ?_
        have hzero : S.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero S).2 hvS
        rw [← hy, hσ'] at hzero
        rw [← hy, hzero, map_zero]
      have hli : LinearIndependent k (Fin.cons v (σ ∘ c) : Fin (N + 1) → V) :=
        (c.linearIndependent.map' σ (LinearMap.ker_eq_bot.2 hσinj)).finCons hvnot
      have hcard : Fintype.card (Fin (N + 1)) = Module.finrank k V := by simp [hN]
      refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_⟩
      set b := basisOfLinearIndependentOfCardEqFinrank hli hcard with hbdef
      have hb : ⇑b = Fin.cons v (σ ∘ c) :=
        coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
      have hb0 : b 0 = v := by rw [hb]; simp
      have hbs : ∀ l : Fin N, b l.succ = σ (c l) := fun l => by rw [hb]; simp
      refine toMatrix_blockTriangular_of_mem_span_Iic b A fun j => ?_
      induction j using Fin.cases with
      | zero =>
          rw [hb0, hAv]
          exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨0, Set.mem_Iic.2 le_rfl, hb0⟩)
      | succ i =>
          have hvmem : v ∈ Submodule.span k (b '' Set.Iic i.succ) :=
            Submodule.subset_span ⟨0, Set.mem_Iic.2 (Fin.zero_le _), hb0⟩
          have hlift : σ (A' (c i)) ∈ Submodule.span k (b '' Set.Iic i.succ) := by
            have hci : A' (c i) ∈ Submodule.span k (c '' Set.Iic i) :=
              (toMatrix_blockTriangular_iff c A').1 hc i
            have hmem : σ (A' (c i)) ∈ Submodule.span k ((fun l => σ (c l)) '' Set.Iic i) := by
              rw [← Set.image_image, Submodule.span_image]
              exact Submodule.mem_map_of_mem hci
            refine Submodule.span_le.2 ?_ hmem
            rintro _ ⟨l, hl, rfl⟩
            exact Submodule.subset_span
              ⟨l.succ, Set.mem_Iic.2 (Fin.succ_le_succ_iff.2 (Set.mem_Iic.1 hl)), hbs l⟩
          have hdiff : A (σ (c i)) - σ (A' (c i)) ∈ S := by
            have hker : A (σ (c i)) - σ (A' (c i)) ∈ LinearMap.ker S.mkQ := by
              rw [LinearMap.mem_ker, map_sub,
                show S.mkQ (A (σ (c i))) = A' (c i) by rw [← hstep, hσ'], hσ', sub_self]
            rwa [Submodule.ker_mkQ] at hker
          rw [hbs i, ← sub_add_cancel (A (σ (c i))) (σ (A' (c i)))]
          refine Submodule.add_mem _ ?_ hlift
          obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hdiff
          rw [← ht]
          exact Submodule.smul_mem _ _ hvmem

variable {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- If an endomorphism has split characteristic polynomial and the specified finite rank, then
some basis indexed by that rank gives it a block-triangular matrix. -/
theorem exists_basis_blockTriangular_of_charpoly_splits {N : ℕ} (A : V →ₗ[k] V)
    (hN : Module.finrank k V = N) (hsplit : (LinearMap.charpoly A).Splits) :
    ∃ b : Basis (Fin N) k V, (LinearMap.toMatrix b b A).BlockTriangular id :=
  exists_basis_blockTriangular_of_minpoly_splits k N A hN
    (hsplit.of_dvd A.charpoly_monic.ne_zero (LinearMap.minpoly_dvd_charpoly A))

/-- If an endomorphism has split characteristic polynomial and the specified finite rank, then it
has a block-triangular matrix whose diagonal entries give a linear-factor decomposition of its
characteristic polynomial. -/
theorem exists_basis_diagonal_charpoly_of_splits {N : ℕ} (A : V →ₗ[k] V)
    (hN : Module.finrank k V = N) (hsplit : (LinearMap.charpoly A).Splits) :
    ∃ (b : Basis (Fin N) k V) (lam : Fin N → k),
      (LinearMap.toMatrix b b A).BlockTriangular id ∧
        (∀ i, LinearMap.toMatrix b b A i i = lam i) ∧
        LinearMap.charpoly A = ∏ i, (X - C (lam i)) := by
  obtain ⟨b, hb⟩ := exists_basis_blockTriangular_of_charpoly_splits A hN hsplit
  refine ⟨b, fun i => LinearMap.toMatrix b b A i i, hb, fun _ => rfl, ?_⟩
  rw [← LinearMap.charpoly_toMatrix A b, Matrix.charpoly_of_upperTriangular _ hb]

/-- Over an algebraically closed field, an endomorphism of the specified finite rank has a basis
in which its matrix is block triangular. -/
theorem exists_basis_blockTriangular_of_isAlgClosed [IsAlgClosed k] {N : ℕ}
    (A : V →ₗ[k] V) (hN : Module.finrank k V = N) :
    ∃ b : Basis (Fin N) k V, (LinearMap.toMatrix b b A).BlockTriangular id :=
  exists_basis_blockTriangular_of_charpoly_splits A hN (IsAlgClosed.splits _)

end Existence

section Perm

variable {k : Type*} [Field k]

/-- The roots of the product of the linear factors associated to a finite family are exactly the
multiset of values of that family. -/
theorem roots_prod_X_sub_C {ι : Type*} [Fintype ι] (f : ι → k) :
    (∏ i, (X - C (f i))).roots = Finset.univ.val.map f := by
  have h : (∏ i, (X - C (f i))) = ((Finset.univ.val.map f).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [h, Polynomial.roots_multiset_prod_X_sub_C]

omit [Field k] in
/-- If two functions on a finite index type have equal multisets of values, then one is obtained
from the other by a permutation of the indices. -/
theorem exists_perm_eq_comp_of_map_univ_eq {N : ℕ} {lam mu : Fin N → k}
    (h : Finset.univ.val.map lam = Finset.univ.val.map mu) :
    ∃ e : Equiv.Perm (Fin N), ∀ i, lam i = mu (e i) := by
  classical
  have hcard : ∀ a : k, Fintype.card {i // lam i = a} = Fintype.card {i // mu i = a} := by
    intro a
    have hc := congrArg (Multiset.count a) h
    rw [Multiset.count_map, Multiset.count_map] at hc
    simpa [Fintype.card_subtype, Finset.card_def, Finset.filter_val, eq_comm] using hc
  let fib : ∀ a : k, {i // lam i = a} ≃ {i // mu i = a} := fun a =>
    Fintype.equivOfCardEq (hcard a)
  refine ⟨((Equiv.sigmaFiberEquiv lam).symm.trans (Equiv.sigmaCongrRight fib)).trans
    (Equiv.sigmaFiberEquiv mu), fun i => ?_⟩
  exact ((fib (lam i)) ⟨i, rfl⟩).2.symm

/-- If two indexed products of monic linear factors are equal, then their roots agree after a
permutation of the indices. -/
theorem exists_perm_eq_comp_of_prod_X_sub_C_eq {N : ℕ} {lam mu : Fin N → k}
    (h : (∏ i, (X - C (lam i))) = ∏ i, (X - C (mu i))) :
    ∃ e : Equiv.Perm (Fin N), ∀ i, lam i = mu (e i) := by
  refine exists_perm_eq_comp_of_map_univ_eq ?_
  rw [← roots_prod_X_sub_C lam, ← roots_prod_X_sub_C mu, h]

/-- The sum of products over subsets of a fixed cardinality is invariant under permuting the
indices of the factors. -/
theorem sum_powersetCard_prod_comp_perm {N : ℕ} (lam : Fin N → k)
    (e : Equiv.Perm (Fin N)) (n : ℕ) :
    ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), ∏ i ∈ s, lam (e i)
      = ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), ∏ i ∈ s, lam i := by
  classical
  refine Finset.sum_equiv e.finsetCongr (fun s => ?_) (fun s _ => ?_)
  · simp
  · simp [Finset.prod_map]

/-- The sum over fixed-cardinality multisets of products of an indexed family is invariant under
permuting its indices. -/
theorem sum_sym_prod_map_comp_perm {N : ℕ} (lam : Fin N → k)
    (e : Equiv.Perm (Fin N)) (n : ℕ) :
    ∑ s : Sym (Fin N) n, ((s : Multiset (Fin N)).map (fun i => lam (e i))).prod
      = ∑ s : Sym (Fin N) n, ((s : Multiset (Fin N)).map lam).prod :=
  Fintype.sum_equiv (Sym.equivCongr e) _ _ fun s => by
    simp [Sym.equivCongr, Sym.coe_map, Multiset.map_map]

end Perm

section Bridge

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
  [Module.Finite k V]

/-- A prescribed linear-factor decomposition of the characteristic polynomial can be realized,
up to a permutation, as the diagonal of a block-triangular matrix for the endomorphism. -/
theorem exists_basis_diagonal_comp_perm_of_charpoly_eq_prod {N : ℕ} (A : V →ₗ[k] V)
    (hN : Module.finrank k V = N) (lam : Fin N → k)
    (hlam : LinearMap.charpoly A = ∏ i, (X - C (lam i))) :
    ∃ (b : Basis (Fin N) k V) (e : Equiv.Perm (Fin N)),
      (LinearMap.toMatrix b b A).BlockTriangular id ∧
        ∀ i, LinearMap.toMatrix b b A i i = lam (e i) := by
  have hsplit : (LinearMap.charpoly A).Splits :=
    hlam ▸ Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C (lam i)
  obtain ⟨b, mu, hb, hdiag, hmu⟩ :=
    exists_basis_diagonal_charpoly_of_splits A hN hsplit
  obtain ⟨e, he⟩ := exists_perm_eq_comp_of_prod_X_sub_C_eq (hmu.symm.trans hlam)
  exact ⟨b, e, hb, fun i => (hdiag i).trans (he i)⟩

end Bridge

end RepresentationTheory.Infrastructure.Triangularization
