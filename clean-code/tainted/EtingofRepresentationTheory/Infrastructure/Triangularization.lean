import Mathlib

/-!
# Triangularization of an operator whose characteristic polynomial splits

Mathlib knows that a split characteristic polynomial makes an operator *triangularizable* in the
sense of `Module.End.iSup_maxGenEigenspace_eq_top`, but it has no statement producing an actual
basis in which the matrix is upper triangular. This file fills that gap.

The argument is the classical induction on the dimension: a split minimal polynomial has a root,
so `A` has an eigenvector `v`; the operator descends to `V ⧸ k ∙ v`, whose minimal polynomial
divides that of `A` and hence still splits; a triangularizing basis of the quotient lifts along a
section of `V ↠ V ⧸ k ∙ v` and, with `v` prepended, triangularizes `A`.

We run the induction on the *minimal* polynomial rather than the characteristic polynomial,
because "the minimal polynomial of an induced operator on a quotient divides the minimal
polynomial upstairs" is immediate, whereas the corresponding multiplicativity statement for
characteristic polynomials is not in Mathlib. The characteristic-polynomial form is recovered at
the end from `minpoly_dvd_charpoly`.

## Main results

* `Etingof.exists_basis_blockTriangular` : if `A : V →ₗ[k] V` has split characteristic polynomial
  and `finrank k V = N`, there is a basis `b : Basis (Fin N) k V` in which the matrix of `A` is
  upper triangular.
* `Etingof.exists_basis_blockTriangular_charpoly` : the same, packaged with the diagonal `lam` and
  the identity `charpoly A = ∏ i, (X - C (lam i))`, so that `lam` is literally the eigenvalue list
  of `A` with multiplicity.
* `Etingof.exists_basis_blockTriangular_of_isAlgClosed` : the algebraically closed special case.
* `Etingof.exists_perm_of_prod_X_sub_C_eq` : two families with the same `∏ (X - C ·)` differ by a
  permutation. This is what lets one transport a statement proved for the diagonal produced above
  to an arbitrary root list of the characteristic polynomial.
* `Etingof.exists_basis_blockTriangular_diag_perm` : combining the two, the book's hypothesis
  "the eigenvalues of `A` are `λ_1, …, λ_N`" yields a triangularizing basis whose diagonal is
  `lam ∘ e` for some permutation `e`.
* `Etingof.sum_powersetCard_prod_comp` and `Etingof.sum_sym_prod_comp` : the elementary symmetric
  and complete homogeneous sums are invariant under that permutation, so it can be discarded.

Together the last two turn the triangularizing-basis hypothesis of the Problem 2.11.3(f) trace
formulas into the literal hypothesis `charpoly A = ∏ i, (X - C (lam i))` of the book.
-/

open Polynomial Module

namespace Etingof

section Criterion

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- A basis puts `A` in upper-triangular form exactly when each `A (b j)` lies in the span of the
basis vectors up to and including `b j` — that is, when the flag of the basis is `A`-invariant. -/
theorem blockTriangular_toMatrix_iff {N : ℕ} (b : Basis (Fin N) k V) (A : V →ₗ[k] V) :
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

/-- A basis puts `A` in upper-triangular form as soon as each `A (b j)` lies in the span of the
basis vectors up to and including `b j`. -/
theorem blockTriangular_toMatrix_of_mem_span {N : ℕ} (b : Basis (Fin N) k V) (A : V →ₗ[k] V)
    (h : ∀ j, A (b j) ∈ Submodule.span k (b '' Set.Iic j)) :
    (LinearMap.toMatrix b b A).BlockTriangular id :=
  (blockTriangular_toMatrix_iff b A).2 h

end Criterion

section Existence

variable {k : Type u} [Field k]

/-- **Triangularization, minimal-polynomial form.** If the minimal polynomial of `A` splits over
`k` then `V` has a basis in which the matrix of `A` is upper triangular. -/
theorem exists_basis_blockTriangular_of_splits_minpoly (k : Type u) [Field k] :
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
      -- `V` is nontrivial, so `minpoly k A` is nonconstant and, being split, has a root, which is
      -- therefore an eigenvalue of `A`.
      haveI : Nontrivial V :=
        Module.nontrivial_of_finrank_pos (R := k) (M := V) (by rw [hN]; omega)
      have hint : IsIntegral k A := Algebra.IsIntegral.isIntegral (R := k) A
      obtain ⟨μ, hμ⟩ : ∃ μ : k, Module.End.HasEigenvalue A μ := by
        obtain ⟨a, ha⟩ := hsplit.exists_eval_eq_zero (ne_of_gt (minpoly.degree_pos hint))
        exact ⟨a, Module.End.hasEigenvalue_iff_isRoot.2 ha⟩
      obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
      have hv0 : v ≠ 0 := hv.2
      have hAv : A v = μ • v := hv.apply_eq_smul
      -- The eigenline and the induced operator on the quotient.
      set S : Submodule k V := k ∙ v with hSdef
      have hvS : v ∈ S := Submodule.mem_span_singleton_self v
      have hcomap : S ≤ S.comap A := by
        rw [hSdef, Submodule.span_le]
        rintro x hx
        obtain rfl : x = v := hx
        simpa [hAv] using Submodule.smul_mem S μ hvS
      set A' : (V ⧸ S) →ₗ[k] (V ⧸ S) := S.mapQ S A hcomap with hA'def
      have hstep : ∀ x : V, A' (S.mkQ x) = S.mkQ (A x) := fun x => rfl
      -- `minpoly k A` annihilates `A'`, so `minpoly k A'` divides it and therefore splits too.
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
      -- The quotient has dimension `N`, so the inductive hypothesis triangularizes `A'`.
      have hrank : Module.finrank k (V ⧸ S) = N := by
        have h1 := S.finrank_quotient_add_finrank (R := k)
        have h2 : Module.finrank k S = 1 := by rw [hSdef]; exact finrank_span_singleton hv0
        omega
      obtain ⟨c, hc⟩ := ih A' hrank hsplit'
      -- Lift that basis along a linear section of `V ↠ V ⧸ S` and prepend the eigenvector.
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
      refine blockTriangular_toMatrix_of_mem_span b A fun j => ?_
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
              (blockTriangular_toMatrix_iff c A').1 hc i
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

/-- **Triangularization.** If the characteristic polynomial of `A` splits over `k` and
`Module.finrank k V = N`, then `V` has a basis in which the matrix of `A` is upper triangular.

Mathlib has no such statement: `Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` is about
`iSup_maxGenEigenspace_eq_top`, not about bases. -/
theorem exists_basis_blockTriangular {N : ℕ} (A : V →ₗ[k] V) (hN : Module.finrank k V = N)
    (hsplit : (LinearMap.charpoly A).Splits) :
    ∃ b : Basis (Fin N) k V, (LinearMap.toMatrix b b A).BlockTriangular id :=
  exists_basis_blockTriangular_of_splits_minpoly k N A hN
    (hsplit.of_dvd A.charpoly_monic.ne_zero (LinearMap.minpoly_dvd_charpoly A))

/-- **Triangularization, with the eigenvalue list.** The triangularizing basis of
`exists_basis_blockTriangular` comes with a diagonal `lam`, and that diagonal is exactly the list
of eigenvalues of `A` with multiplicity: `charpoly A = ∏ i, (X - C (lam i))`.

This is the form the book's Problem 2.11.3(f) needs: it turns the hypothesis "the eigenvalues of
`A` are `λ_1, …, λ_N`" into a triangularizing basis. -/
theorem exists_basis_blockTriangular_charpoly {N : ℕ} (A : V →ₗ[k] V)
    (hN : Module.finrank k V = N) (hsplit : (LinearMap.charpoly A).Splits) :
    ∃ (b : Basis (Fin N) k V) (lam : Fin N → k),
      (LinearMap.toMatrix b b A).BlockTriangular id ∧
        (∀ i, LinearMap.toMatrix b b A i i = lam i) ∧
        LinearMap.charpoly A = ∏ i, (X - C (lam i)) := by
  obtain ⟨b, hb⟩ := exists_basis_blockTriangular A hN hsplit
  refine ⟨b, fun i => LinearMap.toMatrix b b A i i, hb, fun _ => rfl, ?_⟩
  rw [← LinearMap.charpoly_toMatrix A b, Matrix.charpoly_of_upperTriangular _ hb]

/-- Over an algebraically closed field every operator on a finite-dimensional space is
triangularizable. -/
theorem exists_basis_blockTriangular_of_isAlgClosed [IsAlgClosed k] {N : ℕ} (A : V →ₗ[k] V)
    (hN : Module.finrank k V = N) :
    ∃ b : Basis (Fin N) k V, (LinearMap.toMatrix b b A).BlockTriangular id :=
  exists_basis_blockTriangular A hN (IsAlgClosed.splits _)

end Existence

section Perm

variable {k : Type*} [Field k]

/-- The roots of `∏ i, (X - C (f i))`, with multiplicity, are the values of `f`. -/
theorem roots_prod_X_sub_C_comp {ι : Type*} [Fintype ι] (f : ι → k) :
    (∏ i, (X - C (f i))).roots = Finset.univ.val.map f := by
  have h : (∏ i, (X - C (f i))) = ((Finset.univ.val.map f).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [h, Polynomial.roots_multiset_prod_X_sub_C]

omit [Field k] in
/-- Two families of scalars with the same multiset of values differ by a permutation. -/
theorem exists_perm_of_map_univ_eq {N : ℕ} {lam mu : Fin N → k}
    (h : Finset.univ.val.map lam = Finset.univ.val.map mu) :
    ∃ e : Equiv.Perm (Fin N), ∀ i, lam i = mu (e i) := by
  classical
  -- Equal multisets of values means each value is attained equally often.
  have hcard : ∀ a : k, Fintype.card {i // lam i = a} = Fintype.card {i // mu i = a} := by
    intro a
    have hc := congrArg (Multiset.count a) h
    rw [Multiset.count_map, Multiset.count_map] at hc
    simpa [Fintype.card_subtype, Finset.card_def, Finset.filter_val, eq_comm] using hc
  -- Matching the fibres of `lam` and `mu` one by one assembles the permutation.
  let fib : ∀ a : k, {i // lam i = a} ≃ {i // mu i = a} := fun a =>
    Fintype.equivOfCardEq (hcard a)
  refine ⟨((Equiv.sigmaFiberEquiv lam).symm.trans (Equiv.sigmaCongrRight fib)).trans
    (Equiv.sigmaFiberEquiv mu), fun i => ?_⟩
  exact ((fib (lam i)) ⟨i, rfl⟩).2.symm

/-- Two families of scalars with the same `∏ (X - C ·)` differ by a permutation: a split monic
polynomial determines its root list up to reordering. -/
theorem exists_perm_of_prod_X_sub_C_eq {N : ℕ} {lam mu : Fin N → k}
    (h : (∏ i, (X - C (lam i))) = ∏ i, (X - C (mu i))) :
    ∃ e : Equiv.Perm (Fin N), ∀ i, lam i = mu (e i) := by
  refine exists_perm_of_map_univ_eq ?_
  rw [← roots_prod_X_sub_C_comp lam, ← roots_prod_X_sub_C_comp mu, h]

/-! ### Reindexing invariance of the two symmetric sums

The right-hand sides of Problem 2.11.3(f) — the elementary symmetric function `e_n` for
`Tr(⋀^n A)` and the complete homogeneous function `h_n` for `Tr(S^n A)` — are symmetric, so
`exists_perm_of_prod_X_sub_C_eq` transports them between any two root lists of `charpoly A`. -/

/-- `e_n` is invariant under reindexing the family: the exterior-power trace formula does not
depend on the order in which the eigenvalues are listed. -/
theorem sum_powersetCard_prod_comp {N : ℕ} (lam : Fin N → k) (e : Equiv.Perm (Fin N)) (n : ℕ) :
    ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), ∏ i ∈ s, lam (e i)
      = ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), ∏ i ∈ s, lam i := by
  classical
  refine Finset.sum_equiv e.finsetCongr (fun s => ?_) (fun s _ => ?_)
  · simp
  · simp [Finset.prod_map]

/-- `h_n` is invariant under reindexing the family: the symmetric-power trace formula does not
depend on the order in which the eigenvalues are listed. -/
theorem sum_sym_prod_comp {N : ℕ} (lam : Fin N → k) (e : Equiv.Perm (Fin N)) (n : ℕ) :
    ∑ s : Sym (Fin N) n, ((s : Multiset (Fin N)).map (fun i => lam (e i))).prod
      = ∑ s : Sym (Fin N) n, ((s : Multiset (Fin N)).map lam).prod :=
  Fintype.sum_equiv (Sym.equivCongr e) _ _ fun s => by
    simp [Sym.equivCongr, Sym.coe_map, Multiset.map_map]

end Perm

section Bridge

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- **The book's hypothesis produces a triangularizing basis.** Given only "the eigenvalues of `A`,
with multiplicity, are `lam 0, …, lam (N-1)`" — that is, `charpoly A = ∏ i, (X - C (lam i))` —
there is a basis triangularizing `A` whose diagonal is `lam` *up to a permutation* of `Fin N`.

The permutation is unavoidable: `lam` is only determined by `charpoly A` up to reordering. Since
the elementary symmetric and complete homogeneous sums are symmetric
(`sum_powersetCard_prod_comp`, `sum_sym_prod_comp`), it does no harm. -/
theorem exists_basis_blockTriangular_diag_perm {N : ℕ} (A : V →ₗ[k] V)
    (hN : Module.finrank k V = N) (lam : Fin N → k)
    (hlam : LinearMap.charpoly A = ∏ i, (X - C (lam i))) :
    ∃ (b : Basis (Fin N) k V) (e : Equiv.Perm (Fin N)),
      (LinearMap.toMatrix b b A).BlockTriangular id ∧
        ∀ i, LinearMap.toMatrix b b A i i = lam (e i) := by
  have hsplit : (LinearMap.charpoly A).Splits :=
    hlam ▸ Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C (lam i)
  obtain ⟨b, mu, hb, hdiag, hmu⟩ := exists_basis_blockTriangular_charpoly A hN hsplit
  obtain ⟨e, he⟩ := exists_perm_of_prod_X_sub_C_eq (hmu.symm.trans hlam)
  exact ⟨b, e, hb, fun i => (hdiag i).trans (he i)⟩

end Bridge

end Etingof
