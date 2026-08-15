/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.PermutationPolynomials
import RepresentationTheory.Combinatorics.PermutationPowerSeries

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MvPolynomial Finset

set_option linter.flexible false in
section

namespace RepresentationTheory.FinsuppPermutationAuxiliary

noncomputable section

open RepresentationTheory.Auxiliary.PermutationPolynomials
open RepresentationTheory.Combinatorics.PermutationPowerSeries
open RepresentationTheory.LinearAlgebra.AuxiliaryPowerSeriesMatrix
open RepresentationTheory.PermutationPolynomialAuxiliary

variable (N : ℕ) {n : ℕ}

/-! ### Generalized cycle colorings -/

/-- An auxiliary type indexed by a natural number, a finitely supported function on `Fin N`,
and a permutation of `Fin n`. -/
def FinsuppPermAuxiliary (α : Fin N →₀ ℕ) (σ : Equiv.Perm (Fin n)) : Type :=
  { f : Fin (permutationNatMultiset n σ).toList.length → Fin N //
    ∀ j : Fin N, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => ((permutationNatMultiset n σ).toList[↑i])) = α j }

/-- A `Fintype` structure on `FinsuppPermAuxiliary` indexed by `N`, implicit `n`, `α`, and `σ`. -/
instance finsuppPermAuxiliaryFintype (α : Fin N →₀ ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype (FinsuppPermAuxiliary N α σ) := by
  unfold FinsuppPermAuxiliary
  exact Subtype.fintype _

/-- The finsupp sum condition is equivalent to the pointwise condition for generalized
cycle colorings. -/
private lemma finsupp_sum_single_iff_gen (α : Fin N →₀ ℕ) (σ : Equiv.Perm (Fin n))
    (f : Fin (permutationNatMultiset n σ).toList.length → Fin N) :
    (∑ i, Finsupp.single (f i) ((permutationNatMultiset n σ).toList[(↑i : ℕ)]) = α) ↔
    (∀ j : Fin N, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => (permutationNatMultiset n σ).toList[(↑i : ℕ)]) = α j) := by
  constructor
  · intro heq j
    have hj := DFunLike.congr_fun heq j
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply] at hj
    rw [← hj, Finset.sum_filter]
  · intro hall
    ext j
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    rw [← Finset.sum_filter]
    exact hall j

/-- Each psum polynomial in N variables over ℚ equals a sum of monomials. -/
private theorem psum_eq_sum_monomial_gen (m : ℕ) :
    MvPolynomial.psum (Fin N) ℚ m =
    ∑ i : Fin N, MvPolynomial.monomial (Finsupp.single i m) 1 := by
  simp only [MvPolynomial.psum, MvPolynomial.X_pow_eq_monomial]

/-- The specified multivariate-polynomial coefficient equals the cardinality of the auxiliary type
indexed by the finitely supported function and permutation. -/
theorem coeff_eq_card_FinsuppPermAuxiliary (α : Fin N →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.coeff α (auxiliaryPermutationPolynomial' N σ) =
    ↑(Fintype.card (FinsuppPermAuxiliary N α σ)) := by
  unfold auxiliaryPermutationPolynomial'
  rw [← Multiset.prod_map_toList, ← List.ofFn_getElem_eq_map, List.prod_ofFn]
  simp_rw [psum_eq_sum_monomial_gen]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_one]
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial, Finset.sum_boole, Fintype.piFinset_univ]
  norm_cast
  have equiv : FinsuppPermAuxiliary N α σ ≃
      { f : Fin (permutationNatMultiset n σ).toList.length → Fin N //
        (∑ i, Finsupp.single (f i) ((permutationNatMultiset n σ).toList[(↑i : ℕ)])) = α } := by
    unfold FinsuppPermAuxiliary
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun f => (finsupp_sum_single_iff_gen N α σ f).symm)
  rw [show Fintype.card (FinsuppPermAuxiliary N α σ) = Fintype.card
      { f : Fin (permutationNatMultiset n σ).toList.length → Fin N //
        (∑ i, Finsupp.single (f i) ((permutationNatMultiset n σ).toList[(↑i : ℕ)])) = α }
    from Fintype.card_congr equiv]
  simp only [Fintype.card_subtype, Finset.card_filter]

/-! ### Generalized non-negative integer matrices -/

/-- An auxiliary type indexed by a natural number `N`, an implicit natural number `n`, and two
functions from `Fin N` to natural numbers. -/
def FinNatFunctionPairAuxiliary (α β : Fin N → ℕ) : Type :=
  { K : Fin N → Fin N → Fin (n + 1) //
    (∀ i, ∑ j, (K i j : ℕ) = α i) ∧ (∀ j, ∑ i, (K i j : ℕ) = β j) }

/-- A `Fintype` structure on `FinNatFunctionPairAuxiliary` indexed by `N`, implicit `n`, `α`,
and `β`. -/
instance finNatFunctionPairAuxiliaryFintype (α β : Fin N → ℕ) :
    Fintype (FinNatFunctionPairAuxiliary N (n := n) α β) :=
  Subtype.fintype _

/-! ### Generalized double counting infrastructure -/

/-- Element bicoloring with prescribed marginals (generalized). -/
private def ElemBicolGen (α β : Fin N →₀ ℕ) : Type :=
  { h : Fin n → Fin N × Fin N //
    (∀ i : Fin N, (Finset.univ.filter fun x => (h x).1 = i).card = α i) ∧
    (∀ j : Fin N, (Finset.univ.filter fun x => (h x).2 = j).card = β j) }

private instance (α β : Fin N →₀ ℕ) : Fintype (ElemBicolGen N (n := n) α β) :=
  Subtype.fintype _

/-- Permutation preserving fibers of h (generalized). -/
private def FiberPermGen (h : Fin n → Fin N × Fin N) : Type :=
  { σ : Equiv.Perm (Fin n) // ∀ x, h (σ x) = h x }

private instance (h : Fin n → Fin N × Fin N) : Fintype (FiberPermGen N h) :=
  Subtype.fintype _

/-- Construct a generalized element bicoloring from cycle colorings. -/
private def cycleColToBicolGen (α β : Fin N →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) (fg : FinsuppPermAuxiliary N α σ × FinsuppPermAuxiliary N β σ) :
    ElemBicolGen N (n := n) α β :=
  let π := (exists_sameCycle_class_indexing σ).choose
  have hπ := (exists_sameCycle_class_indexing σ).choose_spec
  ⟨fun x => (fg.1.val (π x), fg.2.val (π x)),
   ⟨fun i => by
      rw [show (Finset.univ.filter fun x : Fin n => fg.1.val (π x) = i) =
          (Finset.univ.filter fun j => fg.1.val j = i).biUnion
            (fun j => Finset.univ.filter fun x => π x = j) from by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        exact ⟨fun h => ⟨π x, h, rfl⟩, fun ⟨j, hj, hjx⟩ => hjx ▸ hj⟩]
      rw [Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
        Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hij (h₁ ▸ h₂)))]
      conv_lhs => arg 2; ext j; rw [hπ.2 j]
      exact fg.1.prop i,
    fun j => by
      rw [show (Finset.univ.filter fun x : Fin n => fg.2.val (π x) = j) =
          (Finset.univ.filter fun k => fg.2.val k = j).biUnion
            (fun k => Finset.univ.filter fun x => π x = k) from by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        exact ⟨fun h => ⟨π x, h, rfl⟩, fun ⟨k, hk, hkx⟩ => hkx ▸ hk⟩]
      rw [Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
        Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hij (h₁ ▸ h₂)))]
      conv_lhs => arg 2; ext k; rw [hπ.2 k]
      exact fg.2.prop j⟩⟩

/-- The permutation σ preserves the bicoloring constructed from its cycle colorings. -/
private lemma cycleColToBicolGen_compat (α β : Fin N →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) (fg : FinsuppPermAuxiliary N α σ × FinsuppPermAuxiliary N β σ) :
    ∀ x, (cycleColToBicolGen N α β σ fg).val (σ x) = (cycleColToBicolGen N α β σ fg).val x := by
  intro x
  simp only [cycleColToBicolGen]
  let π := (exists_sameCycle_class_indexing σ).choose
  have hπ := (exists_sameCycle_class_indexing σ).choose_spec
  change (fg.1.val (π (σ x)), fg.2.val (π (σ x))) = (fg.1.val (π x), fg.2.val (π x))
  have hkey : π (σ x) = π x := (hπ.1 (σ x) x).mpr ⟨-1, by simp⟩
  rw [hkey]

/-- **Part A (generalized)**: Bijection between (σ, CycleCol pairs) and (h, FiberPerm). -/
private lemma card_sigma_CycleCol_eq_card_sigma_fiberPermGen (α β : Fin N →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    Fintype.card (Σ σ : Equiv.Perm (Fin n),
      FinsuppPermAuxiliary N α σ × FinsuppPermAuxiliary N β σ) =
    Fintype.card (Σ hb : ElemBicolGen N (n := n) α β, FiberPermGen N hb.val) := by
  classical
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨σ, fg⟩ =>
      ⟨cycleColToBicolGen N α β σ fg,
       ⟨σ, cycleColToBicolGen_compat N α β σ fg⟩⟩
    invFun := fun p =>
      let h := p.1.val
      let σ := p.2.val
      let hcompat : ∀ x, h (σ x) = h x := p.2.property
      let π := (exists_sameCycle_class_indexing σ).choose
      have hπ := (exists_sameCycle_class_indexing σ).choose_spec
      have hne : ∀ i : Fin (permutationNatMultiset n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := permutationNatMultiset_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      let rep := fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)
      have hrep : ∀ i, π (rep i) = i := fun i =>
        (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2
      have hiter : ∀ (m : ℕ) (y : Fin n), h ((σ ^ m) y) = h y := by
        intro m; induction m with
        | zero => intro y; simp
        | succ m ih => intro y; rw [pow_succ, Equiv.Perm.mul_apply, ih, hcompat]
      have hconst : ∀ k₁ k₂, π k₁ = π k₂ → h k₁ = h k₂ := by
        intro k₁ k₂ hk
        obtain ⟨m, -, hm⟩ := ((hπ.1 k₁ k₂).mp hk).exists_pow_eq'
        exact (hiter m k₁).symm.trans (congrArg h hm)
      ⟨σ,
        ⟨fun i => (h (rep i)).1, fun j => by
          dsimp only
          trans (Finset.univ.filter (fun i => (h (rep i)).1 = j)).sum
            (fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).card)
          · exact Finset.sum_congr rfl (fun i _ => (hπ.2 i).symm)
          rw [← Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
            Finset.disjoint_filter.mpr (fun k _ h₁ h₂ => hij (h₁ ▸ h₂)))]
          suffices heq : (Finset.univ.filter (fun i => (h (rep i)).1 = j)).biUnion
              (fun i => Finset.univ.filter (fun k : Fin n => π k = i)) =
              Finset.univ.filter (fun x => (h x).1 = j) by rw [heq]; exact p.1.2.1 j
          ext k; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, hk⟩
            rw [← hk] at hi; rwa [hconst _ _ (hrep (π k))] at hi
          · intro hk; exact ⟨π k, by rwa [← hconst k (rep (π k)) (hrep (π k)).symm], rfl⟩⟩,
        ⟨fun i => (h (rep i)).2, fun j => by
          dsimp only
          trans (Finset.univ.filter (fun i => (h (rep i)).2 = j)).sum
            (fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).card)
          · exact Finset.sum_congr rfl (fun i _ => (hπ.2 i).symm)
          rw [← Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
            Finset.disjoint_filter.mpr (fun k _ h₁ h₂ => hij (h₁ ▸ h₂)))]
          suffices heq : (Finset.univ.filter (fun i => (h (rep i)).2 = j)).biUnion
              (fun i => Finset.univ.filter (fun k : Fin n => π k = i)) =
              Finset.univ.filter (fun x => (h x).2 = j) by rw [heq]; exact p.1.2.2 j
          ext k; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, hk⟩
            rw [← hk] at hi; rwa [hconst _ _ (hrep (π k))] at hi
          · intro hk; exact ⟨π k, by rwa [← hconst k (rep (π k)) (hrep (π k)).symm], rfl⟩⟩⟩
    left_inv := fun ⟨σ, fg⟩ => by
      let π := (exists_sameCycle_class_indexing σ).choose
      have hπ := (exists_sameCycle_class_indexing σ).choose_spec
      have hne : ∀ i : Fin (permutationNatMultiset n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := permutationNatMultiset_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      have hrep : ∀ i, π ((Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)) = i :=
        fun i => (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2
      refine Sigma.ext rfl (heq_of_eq ?_)
      simp only [cycleColToBicolGen]
      apply Prod.ext
      · apply Subtype.ext; funext i; exact congrArg fg.1.val (hrep i)
      · apply Subtype.ext; funext i; exact congrArg fg.2.val (hrep i)
    right_inv := fun ⟨⟨h, hrow, hcol⟩, ⟨σ, hcompat⟩⟩ => by
      simp only [cycleColToBicolGen]
      let π := (exists_sameCycle_class_indexing σ).choose
      have hπ := (exists_sameCycle_class_indexing σ).choose_spec
      have hne : ∀ i : Fin (permutationNatMultiset n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := permutationNatMultiset_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      have hrep : ∀ i, π ((Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)) = i :=
        fun i => (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2
      have hiter : ∀ (m : ℕ) (y : Fin n), h ((σ ^ m) y) = h y := by
        intro m; induction m with
        | zero => intro y; simp
        | succ m ih =>
          intro y; rw [pow_succ, Equiv.Perm.mul_apply]
          exact (ih (σ y)).trans (hcompat y)
      have hconst : ∀ k₁ k₂, π k₁ = π k₂ → h k₁ = h k₂ := by
        intro k₁ k₂ hk
        obtain ⟨m, -, hm⟩ := ((hπ.1 k₁ k₂).mp hk).exists_pow_eq'
        exact (hiter m k₁).symm.trans (congrArg h hm)
      ext1
      · apply Subtype.ext; funext x
        have key := hconst _ x (hrep (π x))
        simp only [Prod.mk.eta]; exact key
      · rfl
  }

/-! ### MulAction on generalized element bicolorings -/

private noncomputable def permSmulElemBicolGen {α β : Fin N →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicolGen N (n := n) α β) : ElemBicolGen N (n := n) α β :=
  ⟨hb.val ∘ ⇑σ⁻¹, by
    constructor
    · intro i
      have h1 : (Finset.univ.filter (fun x => ((hb.val ∘ ⇑σ⁻¹) x).1 = i)).card =
          (Finset.univ.filter (fun x => (hb.val x).1 = i)).card := by
        apply Finset.card_bij' (fun x _ => σ⁻¹ x) (fun x _ => σ x)
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Function.comp] at hx ⊢; convert hx using 1; simp
        · intro x _; simp
        · intro x _; simp
      rw [h1]; exact hb.2.1 i
    · intro j
      have h1 : (Finset.univ.filter (fun x => ((hb.val ∘ ⇑σ⁻¹) x).2 = j)).card =
          (Finset.univ.filter (fun x => (hb.val x).2 = j)).card := by
        apply Finset.card_bij' (fun x _ => σ⁻¹ x) (fun x _ => σ x)
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Function.comp] at hx ⊢; convert hx using 1; simp
        · intro x _; simp
        · intro x _; simp
      rw [h1]; exact hb.2.2 j⟩

@[simp]
private lemma permSmulElemBicolGen_val {α β : Fin N →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicolGen N (n := n) α β) :
    (permSmulElemBicolGen N σ hb).val = hb.val ∘ ⇑σ⁻¹ := rfl

private noncomputable instance permMulActionElemBicolGen {α β : Fin N →₀ ℕ} :
    MulAction (Equiv.Perm (Fin n)) (ElemBicolGen N (n := n) α β) where
  smul := permSmulElemBicolGen N
  one_smul hb := Subtype.ext (funext fun _ => by
    change (permSmulElemBicolGen N 1 hb).val _ = hb.val _
    simp [permSmulElemBicolGen_val, Function.comp])
  mul_smul σ τ hb := Subtype.ext (funext fun x => by
    change (permSmulElemBicolGen N (σ * τ) hb).val x =
      (permSmulElemBicolGen N σ (permSmulElemBicolGen N τ hb)).val x
    simp [permSmulElemBicolGen_val, Function.comp, mul_inv_rev, Equiv.Perm.mul_apply])

private lemma mem_stabilizer_iff_fiberPermGen {α β : Fin N →₀ ℕ}
    (hb : ElemBicolGen N (n := n) α β) (σ : Equiv.Perm (Fin n)) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) hb ↔ ∀ x, hb.val (σ x) = hb.val x := by
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    have h1 := congr_arg Subtype.val h
    rw [show (σ • hb).val = hb.val ∘ ⇑σ⁻¹ from permSmulElemBicolGen_val N σ hb] at h1
    have := congr_fun h1 (σ x); simp at this; exact this.symm
  · intro h; apply Subtype.ext
    rw [show (σ • hb).val = hb.val ∘ ⇑σ⁻¹ from permSmulElemBicolGen_val N σ hb]
    funext x; have := h (σ⁻¹ x); simp at this; exact this.symm

/-- Fiber size matrix for generalized bicolorings. -/
private noncomputable def fiberSizesGen {α β : Fin N →₀ ℕ}
    (hb : ElemBicolGen N (n := n) α β) : FinNatFunctionPairAuxiliary N (n := n) (⇑α) (⇑β) :=
  ⟨fun i j => ⟨(Finset.univ.filter fun x => hb.val x = (i, j)).card,
    Nat.lt_succ_of_le <| (Finset.card_filter_le _ _).trans <| by simp [Fintype.card_fin]⟩,
   fun i => by
     simp only [Fin.val_natCast]
     rw [← hb.2.1 i]
     rw [← Finset.card_biUnion (fun j₁ _ j₂ _ hj =>
       Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hj (by
         have := h₁.symm.trans h₂; exact Prod.ext_iff.mp this |>.2)))]
     congr 1; ext x
     simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
     exact ⟨fun ⟨j, ⟨h1, h2⟩⟩ => h1, fun h => ⟨(hb.val x).2, ⟨h, rfl⟩⟩⟩,
   fun j => by
     simp only [Fin.val_natCast]
     rw [← hb.2.2 j]
     rw [← Finset.card_biUnion (fun i₁ _ i₂ _ hi =>
       Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hi (by
         have := h₁.symm.trans h₂; exact Prod.ext_iff.mp this |>.1)))]
     congr 1; ext x
     simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
     exact ⟨fun ⟨i, ⟨h1, h2⟩⟩ => h2, fun h => ⟨(hb.val x).1, ⟨rfl, h⟩⟩⟩⟩

private lemma fiberSizesGen_smul_eq {α β : Fin N →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicolGen N (n := n) α β) :
    fiberSizesGen N (σ • hb) = fiberSizesGen N hb := by
  apply Subtype.ext; funext i; funext j; apply Fin.ext
  simp only [fiberSizesGen]
  have : (Finset.univ.filter (fun x => (hb.val ∘ ⇑σ⁻¹) x = (i, j))).card =
      (Finset.univ.filter (fun x => hb.val x = (i, j))).card := by
    apply Finset.card_bij' (fun x _ => σ⁻¹ x) (fun x _ => σ x)
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Function.comp] at hx ⊢; convert hx using 1; simp
    · intro x _; simp
    · intro x _; simp
  exact this

private lemma same_fiberSizes_same_orbitGen {α β : Fin N →₀ ℕ}
    (h₁ h₂ : ElemBicolGen N (n := n) α β) (heq : fiberSizesGen N h₁ = fiberSizesGen N h₂) :
    h₁ ∈ MulAction.orbit (Equiv.Perm (Fin n)) h₂ := by
  classical
  have hcard : ∀ p : Fin N × Fin N,
      Fintype.card { x // h₁.val x = p } = Fintype.card { x // h₂.val x = p } := by
    intro ⟨i, j⟩
    simp only [Fintype.card_subtype, Finset.card_filter]
    have := congr_arg (fun K => (K.1 i j : ℕ)) heq
    simpa [fiberSizesGen] using this
  let σ : Equiv.Perm (Fin n) :=
    Equiv.ofFiberEquiv (f := h₁.val) (g := h₂.val)
      (fun p => Fintype.equivOfCardEq (hcard p))
  have hσ : ∀ x, h₂.val (σ x) = h₁.val x := Equiv.ofFiberEquiv_map _
  refine ⟨σ⁻¹, Subtype.ext (funext fun x => ?_)⟩
  simp only [permSmulElemBicolGen_val]
  exact hσ x

/-- Helper for counting sigma-types over filter. -/
private lemma sigma_filter_fst_card_gen (K : Fin N → Fin N → ℕ) (i : Fin N) :
    (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K ij.1 ij.2)) =>
      s.1.1 = i)).card = ∑ j, K i j := by
  rw [← Fintype.card_subtype,
      show ∑ j, K i j = Fintype.card (Σ j : Fin N, Fin (K i j)) from
        by simp [Fintype.card_sigma, Fintype.card_fin]]
  exact Fintype.card_congr {
    toFun := fun ⟨⟨⟨i', j⟩, k⟩, (hi : i' = i)⟩ => ⟨j, hi ▸ k⟩
    invFun := fun ⟨j, k⟩ => ⟨⟨(i, j), k⟩, rfl⟩
    left_inv := fun ⟨⟨⟨i', j⟩, k⟩, hi⟩ => by subst hi; rfl
    right_inv := fun ⟨j, k⟩ => rfl }

private lemma sigma_filter_snd_card_gen (K : Fin N → Fin N → ℕ) (j : Fin N) :
    (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K ij.1 ij.2)) =>
      s.1.2 = j)).card = ∑ i, K i j := by
  rw [← Fintype.card_subtype,
      show ∑ i, K i j = Fintype.card (Σ i : Fin N, Fin (K i j)) from
        by simp [Fintype.card_sigma, Fintype.card_fin]]
  exact Fintype.card_congr {
    toFun := fun ⟨⟨⟨i, j'⟩, k⟩, (hj : j' = j)⟩ => ⟨i, hj ▸ k⟩
    invFun := fun ⟨i, k⟩ => ⟨⟨(i, j), k⟩, rfl⟩
    left_inv := fun ⟨⟨⟨i, j'⟩, k⟩, hj⟩ => by subst hj; rfl
    right_inv := fun ⟨i, k⟩ => rfl }

private lemma sigma_filter_pair_card_gen (K : Fin N → Fin N → ℕ) (i j : Fin N) :
    (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K ij.1 ij.2)) =>
      s.1 = (i, j))).card = K i j := by
  have : Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K ij.1 ij.2)) =>
      s.1 = (i, j)) =
    (Finset.univ : Finset (Fin (K i j))).map
      ⟨fun k => ⟨(i, j), k⟩, fun k₁ k₂ h => by simpa using h⟩ := by
    ext ⟨⟨i', j'⟩, k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨k, rfl⟩
    · rintro ⟨k', hk'⟩; exact (congr_arg Sigma.fst hk').symm
  rw [this, Finset.card_map, Finset.card_fin]

private noncomputable def elemBicolOfMatrixGen_equiv {α β : Fin N →₀ ℕ}
    (hα : ∑ i, α i = n) (K : FinNatFunctionPairAuxiliary N (n := n) (⇑α) (⇑β)) :
    Fin n ≃ (Σ ij : Fin N × Fin N, Fin (K.1 ij.1 ij.2 : ℕ)) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_sigma, Fintype.card_fin, Fintype.sum_prod_type]
    simp_rw [K.2.1]; rw [hα])

private noncomputable def elemBicolOfMatrixGen {α β : Fin N →₀ ℕ}
    (hα : ∑ i, α i = n) (K : FinNatFunctionPairAuxiliary N (n := n) (⇑α) (⇑β)) :
    ElemBicolGen N (n := n) α β :=
  ⟨fun x => (elemBicolOfMatrixGen_equiv N hα K x).1,
   ⟨fun i => by
      classical
      have h1 : (Finset.univ.filter (fun x =>
          (elemBicolOfMatrixGen_equiv N hα K x).1.1 = i)).card =
          (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K.1 ij.1 ij.2 : ℕ)) =>
            s.1.1 = i)).card := by
        apply Finset.card_bij' (fun x _ => elemBicolOfMatrixGen_equiv N hα K x)
          (fun s _ => (elemBicolOfMatrixGen_equiv N hα K).symm s)
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
        · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          convert hs using 1; simp
        · intro x _; simp
        · intro s _; simp
      rw [h1]
      have h2 := sigma_filter_fst_card_gen N (fun i j => (K.1 i j : ℕ)) i
      convert h2 using 1
      exact (K.2.1 i).symm,
    fun j => by
      classical
      have h1 : (Finset.univ.filter (fun x =>
          (elemBicolOfMatrixGen_equiv N hα K x).1.2 = j)).card =
          (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K.1 ij.1 ij.2 : ℕ)) =>
            s.1.2 = j)).card := by
        apply Finset.card_bij' (fun x _ => elemBicolOfMatrixGen_equiv N hα K x)
          (fun s _ => (elemBicolOfMatrixGen_equiv N hα K).symm s)
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
        · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          convert hs using 1; simp
        · intro x _; simp
        · intro s _; simp
      rw [h1]
      have h2 := sigma_filter_snd_card_gen N (fun i j => (K.1 i j : ℕ)) j
      convert h2 using 1
      exact (K.2.2 j).symm⟩⟩

private lemma fiberSizesGen_elemBicolOfMatrixGen {α β : Fin N →₀ ℕ}
    (hα : ∑ i, α i = n) (K : FinNatFunctionPairAuxiliary N (n := n) (⇑α) (⇑β)) :
    fiberSizesGen N (elemBicolOfMatrixGen N hα K) = K := by
  classical
  apply Subtype.ext; funext i; funext j; apply Fin.ext
  simp only [fiberSizesGen, elemBicolOfMatrixGen]
  have h1 : (Finset.univ.filter (fun x =>
      (elemBicolOfMatrixGen_equiv N hα K x).1 = (i, j))).card =
      (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K.1 ij.1 ij.2 : ℕ)) =>
        s.1 = (i, j))).card := by
    apply Finset.card_bij' (fun x _ => elemBicolOfMatrixGen_equiv N hα K x)
      (fun s _ => (elemBicolOfMatrixGen_equiv N hα K).symm s)
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
    · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      convert hs using 1; simp
    · intro x _; simp
    · intro s _; simp
  rw [h1]; exact sigma_filter_pair_card_gen N (fun i j => (K.1 i j : ℕ)) i j

/-- **Part B (generalized)**: orbit-stabilizer gives n! × card(matrices). -/
private lemma card_sigma_fiberPerm_eq_factorial_mulGen (α β : Fin N →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    Fintype.card (Σ hb : ElemBicolGen N (n := n) α β, FiberPermGen N hb.val) =
    n.factorial * Fintype.card (FinNatFunctionPairAuxiliary N (n := n) (⇑α) (⇑β)) := by
  classical
  -- Step 1: FiberPermGen ≃ stabilizer
  have step1 : Fintype.card (Σ hb : ElemBicolGen N (n := n) α β, FiberPermGen N hb.val) =
      Fintype.card (Σ hb : ElemBicolGen N (n := n) α β,
        MulAction.stabilizer (Equiv.Perm (Fin n)) hb) := by
    apply Fintype.card_congr
    exact Equiv.sigmaCongrRight (fun hb =>
      Equiv.subtypeEquiv (Equiv.refl _) (fun σ =>
        (mem_stabilizer_iff_fiberPermGen N hb σ).symm))
  rw [step1]
  -- Step 2: Swap sigma
  have step2 : Fintype.card (Σ hb : ElemBicolGen N (n := n) α β,
      MulAction.stabilizer (Equiv.Perm (Fin n)) hb) =
    Fintype.card (Σ σ : Equiv.Perm (Fin n),
      MulAction.fixedBy (ElemBicolGen N (n := n) α β) σ) := by
    apply Fintype.card_congr
    calc (Σ hb : ElemBicolGen N (n := n) α β,
            MulAction.stabilizer (Equiv.Perm (Fin n)) hb)
      ≃ { p : ElemBicolGen N (n := n) α β × Equiv.Perm (Fin n) //
            p.2 ∈ MulAction.stabilizer _ p.1 } :=
        (Equiv.subtypeProdEquivSigmaSubtype
          (fun (hb : ElemBicolGen N (n := n) α β) (σ : Equiv.Perm (Fin n)) =>
            σ ∈ MulAction.stabilizer _ hb)).symm
      _ ≃ { p : Equiv.Perm (Fin n) × ElemBicolGen N (n := n) α β //
            p.1 ∈ MulAction.stabilizer _ p.2 } :=
        (Equiv.prodComm _ _).subtypeEquiv (fun ⟨_, _⟩ => Iff.rfl)
      _ ≃ { p : Equiv.Perm (Fin n) × ElemBicolGen N (n := n) α β //
            p.2 ∈ MulAction.fixedBy _ p.1 } :=
        Equiv.subtypeEquivRight (fun ⟨σ, hb⟩ => by
          simp [MulAction.mem_stabilizer_iff, MulAction.mem_fixedBy])
      _ ≃ (Σ σ : Equiv.Perm (Fin n),
            MulAction.fixedBy (ElemBicolGen N (n := n) α β) σ) :=
        Equiv.subtypeProdEquivSigmaSubtype
          (fun (σ : Equiv.Perm (Fin n)) (hb : ElemBicolGen N (n := n) α β) =>
            hb ∈ MulAction.fixedBy _ σ)
  rw [step2]
  -- Step 3: Burnside's lemma
  rw [show Fintype.card (Σ σ : Equiv.Perm (Fin n),
        MulAction.fixedBy (ElemBicolGen N (n := n) α β) σ) =
    ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (MulAction.fixedBy (ElemBicolGen N (n := n) α β) σ) from
    Fintype.card_sigma]
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  rw [Fintype.card_perm, Fintype.card_fin, mul_comm]
  congr 1
  -- Step 4: Orbits ≃ FinNatFunctionPairAuxiliary via fiberSizesGen
  apply Fintype.card_congr
  letI := MulAction.orbitRel (Equiv.Perm (Fin n)) (ElemBicolGen N (n := n) α β)
  exact Equiv.ofBijective
    (Quotient.lift (fiberSizesGen N) (fun a b (hab : a ∈ MulAction.orbit _ b) => by
      obtain ⟨g, rfl⟩ := hab; exact fiberSizesGen_smul_eq N g b))
    ⟨fun q₁ q₂ => Quotient.inductionOn₂ q₁ q₂ (fun a b heq =>
        Quotient.sound (same_fiberSizes_same_orbitGen N a b heq)),
     fun K => ⟨Quotient.mk' (elemBicolOfMatrixGen N hα K),
              fiberSizesGen_elemBicolOfMatrixGen N hα K⟩⟩

/-- If the coordinate sums of `α` and `β` both equal `n`, the sum over permutations of the
products of the two `FinsuppPermAuxiliary` cardinalities equals `n!` times the cardinality of
`FinNatFunctionPairAuxiliary`. -/
theorem
    sum_FinsuppPermAuxiliary_card_mul_card_eq_factorial_mul_FinNatFunctionPairAuxiliary_card
    (α β : Fin N →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (FinsuppPermAuxiliary N α σ) * Fintype.card (FinsuppPermAuxiliary N β σ) =
    n.factorial * Fintype.card (FinNatFunctionPairAuxiliary N (n := n) (⇑α) (⇑β)) := by
  have h1 : ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (FinsuppPermAuxiliary N α σ) * Fintype.card (FinsuppPermAuxiliary N β σ) =
    Fintype.card (Σ σ : Equiv.Perm (Fin n),
      FinsuppPermAuxiliary N α σ × FinsuppPermAuxiliary N β σ) := by
    simp_rw [← Fintype.card_prod]; exact Fintype.card_sigma.symm
  rw [h1, card_sigma_CycleCol_eq_card_sigma_fiberPermGen N α β hα hβ]
  exact card_sigma_fiberPerm_eq_factorial_mulGen N α β hα hβ

/-! ### Generalized auxiliaryPowerSeries coefficient = matrix count -/

/-- Naturality of `auxiliaryPowerSeries` under ring homomorphisms. -/
private theorem map_invOfUnit_one_sub_xy {k k' : Type*} [CommRing k] [CommRing k']
    (f : k →+* k') (i j : Fin N) :
    MvPowerSeries.map f
      (MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl i : AuxiliaryIndex N) *
             MvPowerSeries.X (Sum.inr j : AuxiliaryIndex N) :
          MvPowerSeries (AuxiliaryIndex N) k) 1) =
    MvPowerSeries.invOfUnit
      (1 - MvPowerSeries.X (Sum.inl i : AuxiliaryIndex N) *
           MvPowerSeries.X (Sum.inr j : AuxiliaryIndex N) :
        MvPowerSeries (AuxiliaryIndex N) k') 1 := by
  set g : MvPowerSeries (AuxiliaryIndex N) k :=
    1 - MvPowerSeries.X (Sum.inl i) * MvPowerSeries.X (Sum.inr j)
  have hmapped : MvPowerSeries.map f g =
      (1 - MvPowerSeries.X (Sum.inl i : AuxiliaryIndex N) *
           MvPowerSeries.X (Sum.inr j) : MvPowerSeries _ k') := by
    simp [g, map_sub, map_one, map_mul, MvPowerSeries.map_X]
  have h1 := MvPowerSeries.mul_invOfUnit g 1
    (by simp [g, MvPowerSeries.constantCoeff_X])
  have h2 : MvPowerSeries.map f (g * g.invOfUnit 1) = MvPowerSeries.map f 1 := by rw [h1]
  rw [map_mul, hmapped, map_one] at h2
  set g' : MvPowerSeries (AuxiliaryIndex N) k' :=
    1 - MvPowerSeries.X (Sum.inl i) * MvPowerSeries.X (Sum.inr j)
  have h3 := MvPowerSeries.mul_invOfUnit g' 1
    (by simp [g', MvPowerSeries.constantCoeff_X])
  have hU : IsUnit g' :=
    ⟨⟨_, _, h3, by rw [mul_comm]; exact h3⟩, rfl⟩
  exact hU.mul_left_cancel (h2.trans h3.symm)

/-- Mapping the auxiliary multivariate power series along a ring homomorphism gives the
corresponding auxiliary power series. -/
theorem map_auxiliaryPowerSeries {k k' : Type*} [CommRing k] [CommRing k'] (f : k →+* k') :
    MvPowerSeries.map f (auxiliaryPowerSeries N k) = auxiliaryPowerSeries N k' := by
  unfold auxiliaryPowerSeries
  rw [map_prod (MvPowerSeries.map f)]
  apply Finset.prod_congr rfl; intro i _
  rw [map_prod (MvPowerSeries.map f)]
  apply Finset.prod_congr rfl; intro j _
  exact map_invOfUnit_one_sub_xy N f i j

/-- FinNatFunctionPairAuxiliary and FunctionPairIndexedAuxiliary have the same cardinality when
the entry bounds are both sufficient. -/
private theorem card_NNMatrixWithMarginsGen_eq_card_NNMatrixWithMargins
    (α β : Fin N → ℕ) (hα : ∀ i, α i ≤ n)
    (hα' : ∀ i, α i ≤ N) :
    Fintype.card (FinNatFunctionPairAuxiliary N (n := n) α β) =
    Fintype.card (FunctionPairIndexedAuxiliary N α β) := by
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨K, hrow, hcol⟩ => ⟨fun i j => ⟨(K i j : ℕ),
      Nat.lt_succ_of_le ((hrow i ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)).trans (hα' i))⟩, hrow, hcol⟩
    invFun := fun ⟨K, hrow, hcol⟩ => ⟨fun i j => ⟨(K i j : ℕ),
      Nat.lt_succ_of_le ((hrow i ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)).trans (hα i))⟩, hrow, hcol⟩
    left_inv := fun ⟨K, _, _⟩ => by
      refine Subtype.ext (funext fun i => funext fun j => Fin.ext ?_); simp
    right_inv := fun ⟨K, _, _⟩ => by
      refine Subtype.ext (funext fun i => funext fun j => Fin.ext ?_); simp
  }

/-- Coefficient of invOfUnit(1-xy, 1) over ℚ, transferred from the ℂ version. -/
private theorem coeff_invOfUnit_one_sub_xy_rat (i j : Fin N) (e : AuxiliaryIndex N →₀ ℕ) :
    MvPowerSeries.coeff e
      (MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl i : AuxiliaryIndex N) *
             MvPowerSeries.X (Sum.inr j : AuxiliaryIndex N) :
          MvPowerSeries (AuxiliaryIndex N) ℚ) 1) =
    if e = e (Sum.inl i) • (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1)
    then 1 else 0 := by
  have h_inj : Function.Injective (algebraMap ℚ ℂ) := Rat.cast_injective
  apply h_inj
  rw [show (algebraMap ℚ ℂ) (MvPowerSeries.coeff e (MvPowerSeries.invOfUnit _ _)) =
      MvPowerSeries.coeff e (MvPowerSeries.map (algebraMap ℚ ℂ)
        (MvPowerSeries.invOfUnit _ _)) from by rw [MvPowerSeries.coeff_map]]
  rw [map_invOfUnit_one_sub_xy]
  rw [coeff_invOfUnit_one_sub_variable_product_eq_indicator]
  split <;> simp [*]

/-- The full Cauchy product over ℚ as a product over pairs. -/
private theorem fullCauchyProd_eq_prod_pairs_gen :
    auxiliaryPowerSeries N ℚ = ∏ p : Fin N × Fin N,
      MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl p.1 : AuxiliaryIndex N) *
             MvPowerSeries.X (Sum.inr p.2 : AuxiliaryIndex N) : MvPowerSeries (AuxiliaryIndex N) ℚ)
        (1 : ℚˣ) := by
  unfold auxiliaryPowerSeries
  rw [Fintype.prod_prod_type]

/-- If every coordinate of `α` is at most `n`, the specified multivariate-power-series coefficient
equals the cardinality of `FinNatFunctionPairAuxiliary` indexed by `α` and `β`. -/
theorem auxiliaryPowerSeriesCoeff_eq_card_FinNatFunctionPairAuxiliary (α β : Fin N → ℕ)
    (hα : ∀ i, α i ≤ n) :
    MvPowerSeries.coeff (auxiliaryFinsupp N α β) (auxiliaryPowerSeries N ℚ) =
    ↑(Fintype.card (FinNatFunctionPairAuxiliary N (n := n) α β)) := by
  rw [fullCauchyProd_eq_prod_pairs_gen]
  rw [MvPowerSeries.coeff_prod]
  simp_rw [coeff_invOfUnit_one_sub_xy_rat, Finset.prod_boole,
    Finset.mem_univ, forall_true_left, Finset.sum_boole]
  norm_cast
  -- Bijection: valid antidiag elements ↔ FinNatFunctionPairAuxiliary
  set xyMon : Fin N × Fin N → AuxiliaryIndex N →₀ ℕ :=
    fun p => Finsupp.single (Sum.inl p.1) 1 + Finsupp.single (Sum.inr p.2) 1
  -- Extract row/col sum lemmas from antidiag membership
  have extract_row : ∀ (x : (Fin N × Fin N) →₀ (AuxiliaryIndex N →₀ ℕ)),
      x ∈ Finset.univ.finsuppAntidiag (auxiliaryFinsupp N α β) →
      (∀ p, x p = (x p) (Sum.inl p.1) • xyMon p) →
      ∀ i, ∑ j, (x (i, j)) (Sum.inl i) = α i := by
    intro x hx hvalid i
    have h := DFunLike.congr_fun (Finset.mem_finsuppAntidiag.mp hx).1 (Sum.inl i)
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, auxiliaryFinsupp_apply_inl] at h
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i _ _] at h
    · exact h
    · intro i' _ hi'
      exact Finset.sum_eq_zero fun j _ => by
        have := DFunLike.congr_fun (hvalid (i', j)) (Sum.inl i)
        simp [xyMon, hi'] at this; exact this
    · exact fun h' => absurd (Finset.mem_univ i) h'
  have extract_col : ∀ (x : (Fin N × Fin N) →₀ (AuxiliaryIndex N →₀ ℕ)),
      x ∈ Finset.univ.finsuppAntidiag (auxiliaryFinsupp N α β) →
      (∀ p, x p = (x p) (Sum.inl p.1) • xyMon p) →
      ∀ j, ∑ i, (x (i, j)) (Sum.inl i) = β j := by
    intro x hx hvalid j
    have h := DFunLike.congr_fun (Finset.mem_finsuppAntidiag.mp hx).1 (Sum.inr j)
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, auxiliaryFinsupp_apply_inr] at h
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single j _ _] at h
    · rwa [show (∑ i, (x (i, j)) (Sum.inr j)) = ∑ i, (x (i, j)) (Sum.inl i) from
        Finset.sum_congr rfl fun i _ => by
          have := DFunLike.congr_fun (hvalid (i, j)) (Sum.inr j)
          simp [xyMon] at this; exact this] at h
    · intro j' _ hj'
      exact Finset.sum_eq_zero fun i _ => by
        have := DFunLike.congr_fun (hvalid (i, j')) (Sum.inr j)
        simp [xyMon, hj'] at this; exact this
    · exact fun h' => absurd (Finset.mem_univ j) h'
  have entry_bound : ∀ (x : (Fin N × Fin N) →₀ (AuxiliaryIndex N →₀ ℕ)),
      x ∈ Finset.univ.finsuppAntidiag (auxiliaryFinsupp N α β) →
      (∀ p, x p = (x p) (Sum.inl p.1) • xyMon p) →
      ∀ i j, (x (i, j)) (Sum.inl i) < n + 1 := by
    intro x hx hvalid i j
    apply Nat.lt_succ_of_le; apply le_trans _ (hα i)
    calc (x (i, j)) (Sum.inl i)
        ≤ ∑ j' : Fin N, (x (i, j')) (Sum.inl i) :=
          Finset.single_le_sum (f := fun j' => (x (i, j')) (Sum.inl i))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ = α i := extract_row x hx hvalid i
  change #_ = #(Finset.univ : Finset (FinNatFunctionPairAuxiliary N (n := n) α β))
  apply Finset.card_bij'
    (fun x hx =>
      let hmem := (Finset.mem_filter.mp hx).1
      let hvalid := (Finset.mem_filter.mp hx).2
      ⟨fun i j => ⟨(x (i, j)) (Sum.inl i), entry_bound x hmem hvalid i j⟩,
       extract_row x hmem hvalid, extract_col x hmem hvalid⟩)
    (fun K _ =>
      Finsupp.equivFunOnFinite.symm (fun p => (K.1 p.1 p.2 : ℕ) • xyMon p))
    (fun _ _ => Finset.mem_univ _)
    (fun K _ => by
      apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_finsuppAntidiag]
        constructor
        · apply DFunLike.ext; intro v
          simp only [Finsupp.coe_finsetSum, Finset.sum_apply,
            Finsupp.coe_equivFunOnFinite_symm]
          cases v with
          | inl i =>
            rw [auxiliaryFinsupp_apply_inl, Fintype.sum_prod_type]
            simp only [xyMon, Finsupp.smul_apply, smul_eq_mul,
              Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
            simp [Finset.sum_ite_eq']
            exact K.2.1 i
          | inr j =>
            rw [auxiliaryFinsupp_apply_inr, Fintype.sum_prod_type, Finset.sum_comm]
            simp only [xyMon, Finsupp.smul_apply, smul_eq_mul,
              Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
            simp [Finset.sum_ite_eq']
            exact K.2.2 j
        · exact Finset.subset_univ _
      · intro p; simp [xyMon]
      )
    (fun x hx => by
      apply DFunLike.ext; intro ⟨i, j⟩
      simp only [Finsupp.coe_equivFunOnFinite_symm, xyMon]
      exact ((Finset.mem_filter.mp hx).2 (i, j)).symm)
    (fun K _ => by
      refine Subtype.ext (funext fun i => funext fun j => Fin.ext ?_)
      simp [xyMon])

/-- If the coordinate sums of `α` and `β` both equal `n`, the sum over permutations of the
products of their displayed polynomial coefficients equals `n!` times the displayed
multivariate-power-series coefficient. -/
theorem sum_coeff_mul_coeff_eq_factorial_mul_auxiliaryPowerSeriesCoeff (α β : Fin N →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    (∑ σ : Equiv.Perm (Fin n),
      (MvPolynomial.coeff α (auxiliaryPermutationPolynomial' N σ) : ℚ) *
      (MvPolynomial.coeff β (auxiliaryPermutationPolynomial' N σ) : ℚ)) =
    (Nat.factorial n : ℚ) * MvPowerSeries.coeff (auxiliaryFinsupp N (⇑α) (⇑β))
      (auxiliaryPowerSeries N ℚ) := by
  -- Rewrite each MvPolynomial coefficient as card of FinsuppPermAuxiliary
  simp_rw [coeff_eq_card_FinsuppPermAuxiliary]
  -- Rewrite Cauchy product coefficient as card of FinNatFunctionPairAuxiliary
  have hα' : ∀ i, (α : Fin N → ℕ) i ≤ n := by
    intro i
    have := Finset.single_le_sum (f := (⇑α : Fin N → ℕ)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    omega
  rw [auxiliaryPowerSeriesCoeff_eq_card_FinNatFunctionPairAuxiliary N α β hα']
  -- Both sides are natural number casts; reduce to ℕ equality
  simp only [← Nat.cast_mul, ← Nat.cast_sum]
  congr 1
  exact
    sum_FinsuppPermAuxiliary_card_mul_card_eq_factorial_mul_FinNatFunctionPairAuxiliary_card
      N α β hα hβ

end

end RepresentationTheory.FinsuppPermutationAuxiliary

end
