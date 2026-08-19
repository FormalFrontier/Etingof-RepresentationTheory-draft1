/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteFieldMatrixCharacterValues
import RepresentationTheory.Alignment.Attribute

/-! # Conjugacy classes in dimension two over a finite field -/

namespace RepresentationTheory.FiniteGroups.GL2Conjugacy

/-! ## A class-count identity -/

section ConjClassCount

open scoped Classical

variable {G : Type*} [Group G] [Fintype G]


private lemma fiber_card_mul_centralizerCard (c : ConjClasses G) :
    (Finset.univ.filter (fun a : G => ConjClasses.mk a = c)).card
      * Nat.card (Subgroup.centralizer ({Quotient.out c} : Set G)) = Fintype.card G := by
  classical
  have hcarrier :
      (Finset.univ.filter (fun a : G => ConjClasses.mk a = c)) = c.carrier.toFinset := by
    ext a; simp [ConjClasses.mem_carrier_iff_mk_eq]
  have hmk : ConjClasses.mk (Quotient.out c) = c := by
    rw [← ConjClasses.quotient_mk_eq_mk]; exact Quotient.out_eq c
  have horb : MulAction.orbit (ConjAct G) (Quotient.out c) = c.carrier := by
    rw [ConjAct.orbit_eq_carrier_conjClasses, hmk]
  have hstab : Nat.card (Subgroup.centralizer ({Quotient.out c} : Set G))
      = Fintype.card (MulAction.stabilizer (ConjAct G) (Quotient.out c)) := by
    rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, Nat.card_eq_fintype_card]
  rw [hcarrier, Set.toFinset_card, Fintype.card_congr (Equiv.setCongr horb.symm), hstab,
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) (Quotient.out c),
    ConjAct.card]


/-- For a conjugation-stable subset whose elements have a common centralizer cardinality, the number of represented conjugacy classes times their common class size equals the subset cardinality. -/
theorem ncard_conjClasses_image_mul_classSize_eq {S : Set G}
    (hclosed : ∀ g ∈ S, ∀ x : G, x * g * x⁻¹ ∈ S)
    {d : ℕ} (hd : ∀ g ∈ S, Nat.card (Subgroup.centralizer ({g} : Set G)) = d) :
    (ConjClasses.mk '' S).ncard * (Fintype.card G / d) = S.ncard := by
  classical
  haveI : Fintype S := Fintype.ofFinite _
  -- Membership transfers along conjugacy: a conjugate of an element of `S` is in `S`.
  have hmem : ∀ {a b : G}, b ∈ S → IsConj a b → a ∈ S := by
    intro a b hb hconj
    rw [isConj_iff] at hconj
    obtain ⟨x, hx⟩ := hconj
    have hmemx : x⁻¹ * b * (x⁻¹)⁻¹ ∈ S := hclosed b hb x⁻¹
    have hax : a = x⁻¹ * b * (x⁻¹)⁻¹ := by rw [← hx]; group
    rw [hax]; exact hmemx
  set t : Finset (ConjClasses G) := S.toFinset.image ConjClasses.mk with ht
  have himg : ConjClasses.mk '' S = (↑t : Set (ConjClasses G)) := by
    rw [ht, Finset.coe_image, Set.coe_toFinset]
  -- Every fiber over a class in `t` has exactly `|G| / d` elements.
  have hfiber : ∀ c ∈ t, (S.toFinset.filter (fun a => ConjClasses.mk a = c)).card
      = Fintype.card G / d := by
    intro c hc
    rw [ht, Finset.mem_image] at hc
    obtain ⟨b, hbf, hbc⟩ := hc
    rw [Set.mem_toFinset] at hbf
    -- The fiber inside `S` is the whole fiber, since `S` is conjugation-closed.
    have hfe : S.toFinset.filter (fun a => ConjClasses.mk a = c)
        = Finset.univ.filter (fun a => ConjClasses.mk a = c) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, Set.mem_toFinset, true_and]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      have hconj : IsConj a b := ConjClasses.mk_eq_mk_iff_isConj.mp (h.trans hbc.symm)
      exact hmem hbf hconj
    have hout : Quotient.out c ∈ S := by
      have hmkc : ConjClasses.mk (Quotient.out c) = c := by
        rw [← ConjClasses.quotient_mk_eq_mk]; exact Quotient.out_eq c
      have hconj : IsConj (Quotient.out c) b :=
        ConjClasses.mk_eq_mk_iff_isConj.mp (hmkc.trans hbc.symm)
      exact hmem hbf hconj
    have hkey := fiber_card_mul_centralizerCard c
    rw [hd _ hout] at hkey
    have hdpos : 0 < d := by
      have hpos : 0 < Nat.card (Subgroup.centralizer ({Quotient.out c} : Set G)) := Nat.card_pos
      rw [hd _ hout] at hpos; exact hpos
    rw [hfe, ← hkey, Nat.mul_div_cancel _ hdpos]
  -- Sum the fiber cardinalities over the classes.
  have hH : ∀ a ∈ S.toFinset, ConjClasses.mk a ∈ t := by
    intro a ha; rw [ht]; exact Finset.mem_image_of_mem _ ha
  have hsum : S.toFinset.card = t.card * (Fintype.card G / d) := by
    rw [Finset.card_eq_sum_card_fiberwise hH, Finset.sum_congr rfl hfiber,
      Finset.sum_const, smul_eq_mul]
  rw [himg, Set.ncard_coe_finset, Set.ncard_eq_toFinset_card', hsum]

end ConjClassCount

/-! ## Commutants of non-scalar two-by-two matrices -/

section MatrixCommutant

variable {F : Type*} [Field F]


private lemma exists_smul_add_smul_of_commute {A M : Matrix (Fin 2) (Fin 2) F}
    (hns : ¬ (A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1))
    (hcomm : M * A = A * M) :
    ∃ α β : F, M = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A := by
  -- Entrywise commutation equations.
  have E00 := congrFun (congrFun hcomm 0) 0
  have E01 := congrFun (congrFun hcomm 0) 1
  have E10 := congrFun (congrFun hcomm 1) 0
  have E11 := congrFun (congrFun hcomm 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at E00 E01 E10 E11
  -- Given a chosen `α β`, reduce `M = α•1+β•A` to the four entry equations.
  have fin4 : ∀ α β : F,
      M 0 0 = α + β * A 0 0 → M 0 1 = β * A 0 1 →
      M 1 0 = β * A 1 0 → M 1 1 = α + β * A 1 1 →
      M = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A := by
    intro α β h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.one_apply] using h00
    · simpa [Matrix.one_apply] using h01
    · simpa [Matrix.one_apply] using h10
    · simpa [Matrix.one_apply] using h11
  by_cases hb : A 0 1 = 0
  · by_cases hc : A 1 0 = 0
    · -- Diagonal non-scalar case: `A 0 0 ≠ A 1 1`.
      have had : A 0 0 ≠ A 1 1 := fun h => hns ⟨hb, hc, h⟩
      have hne : A 0 0 - A 1 1 ≠ 0 := sub_ne_zero.mpr had
      set β := (M 0 0 - M 1 1) / (A 0 0 - A 1 1) with hβ
      refine ⟨M 1 1 - β * A 1 1, β, fin4 _ _ ?_ ?_ ?_ ?_⟩
      · rw [hβ]; field_simp; ring
      · -- M 0 1 = β * A 0 1 = 0
        rw [hb, mul_zero]
        have hz : M 0 1 * (A 1 1 - A 0 0) = 0 := by rw [hb] at E01; linear_combination E01
        exact (mul_eq_zero.mp hz).resolve_right (fun h => (Ne.symm had) (sub_eq_zero.mp h))
      · rw [hc, mul_zero]
        have hz : M 1 0 * (A 0 0 - A 1 1) = 0 := by rw [hc] at E10; linear_combination E10
        exact (mul_eq_zero.mp hz).resolve_right (fun h => hne h)
      · ring
    · -- `A 0 1 = 0`, `A 1 0 ≠ 0`.
      set β := M 1 0 / A 1 0 with hβ
      refine ⟨M 1 1 - β * A 1 1, β, fin4 _ _ ?_ ?_ ?_ ?_⟩
      · -- M 0 0 = α + β * A 0 0
        rw [hβ]
        have hM00 : M 0 0 - M 1 1 = M 1 0 / A 1 0 * (A 0 0 - A 1 1) := by
          rw [div_mul_eq_mul_div, eq_div_iff hc]; linear_combination -E10
        linear_combination hM00
      · -- M 0 1 = β * A 0 1 = 0
        rw [hb, mul_zero]
        have hz : M 0 1 * A 1 0 = 0 := by rw [hb] at E00; linear_combination E00
        exact (mul_eq_zero.mp hz).resolve_right hc
      · rw [hβ]; field_simp
      · ring
  · -- `A 0 1 ≠ 0`.
    set β := M 0 1 / A 0 1 with hβ
    refine ⟨M 1 1 - β * A 1 1, β, fin4 _ _ ?_ ?_ ?_ ?_⟩
    · -- M 0 0 = α + β * A 0 0
      rw [hβ]
      have hM00 : M 0 0 - M 1 1 = M 0 1 / A 0 1 * (A 0 0 - A 1 1) := by
        rw [div_mul_eq_mul_div, eq_div_iff hb]; linear_combination E01
      linear_combination hM00
    · rw [hβ]; field_simp
    · -- M 1 0 = β * A 1 0
      rw [hβ]
      have hM10 : M 1 0 * A 0 1 = M 0 1 * A 1 0 := by linear_combination E11
      rw [div_mul_eq_mul_div, eq_div_iff hb]; linear_combination hM10
    · ring


private lemma smul_one_add_smul_injective {A : Matrix (Fin 2) (Fin 2) F}
    (hns : ¬ (A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1)) :
    Function.Injective
      (fun ab : F × F => ab.1 • (1 : Matrix (Fin 2) (Fin 2) F) + ab.2 • A) := by
  rintro ⟨α, β⟩ ⟨α', β'⟩ h
  simp only at h
  have e00 : α + β * A 0 0 = α' + β' * A 0 0 := by
    simpa [Matrix.one_apply] using congrFun (congrFun h 0) 0
  have e01 : β * A 0 1 = β' * A 0 1 := by
    simpa [Matrix.one_apply] using congrFun (congrFun h 0) 1
  have e10 : β * A 1 0 = β' * A 1 0 := by
    simpa [Matrix.one_apply] using congrFun (congrFun h 1) 0
  have e11 : α + β * A 1 1 = α' + β' * A 1 1 := by
    simpa [Matrix.one_apply] using congrFun (congrFun h 1) 1
  have hβ : β = β' := by
    by_contra hne
    have hd : β - β' ≠ 0 := sub_ne_zero.mpr hne
    have hA01 : A 0 1 = 0 := by
      have hz : (β - β') * A 0 1 = 0 := by linear_combination e01
      exact (mul_eq_zero.mp hz).resolve_left hd
    have hA10 : A 1 0 = 0 := by
      have hz : (β - β') * A 1 0 = 0 := by linear_combination e10
      exact (mul_eq_zero.mp hz).resolve_left hd
    have hAd : A 0 0 = A 1 1 := by
      have hz : (β - β') * (A 0 0 - A 1 1) = 0 := by linear_combination e00 - e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hd)
    exact hns ⟨hA01, hA10, hAd⟩
  have hα : α = α' := by rw [hβ] at e00; linear_combination e00
  exact Prod.ext hα hβ


private lemma det_smul_one_add_smul (A : Matrix (Fin 2) (Fin 2) F) (α β : F) :
    Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A)
      = α ^ 2 + (A 0 0 + A 1 1) * (α * β)
        + (A 0 0 * A 1 1 - A 0 1 * A 1 0) * β ^ 2 := by
  have h00 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) 0 0 = α + β * A 0 0 := by
    simp
  have h01 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) 0 1 = β * A 0 1 := by
    simp
  have h10 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) 1 0 = β * A 1 0 := by
    simp
  have h11 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) 1 1 = α + β * A 1 1 := by
    simp
  rw [Matrix.det_fin_two, h00, h01, h10, h11]; ring

variable [Fintype F] [DecidableEq F]


private lemma card_detZero_pairs {A : Matrix (Fin 2) (Fin 2) F} {r : ℕ}
    (hr : ∀ β : F, β ≠ 0 →
      (Finset.univ.filter (fun α : F =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) = 0)).card = r) :
    (Finset.univ.filter (fun ab : F × F =>
        Matrix.det (ab.1 • (1 : Matrix (Fin 2) (Fin 2) F) + ab.2 • A) = 0)).card
      = 1 + (Fintype.card F - 1) * r := by
  -- Fiber over the second coordinate `β`.
  have key : (Finset.univ.filter (fun ab : F × F =>
        Matrix.det (ab.1 • (1 : Matrix (Fin 2) (Fin 2) F) + ab.2 • A) = 0)).card
      = ∑ β : F, (Finset.univ.filter (fun α : F =>
          Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) = 0)).card := by
    simp_rw [Finset.card_filter]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [key, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F))]
  -- `β = 0` row: `det (α•1) = α² = 0` iff `α = 0`.
  have hf0 : (Finset.univ.filter (fun α : F =>
      Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + (0 : F) • A) = 0)).card = 1 := by
    have hrw : (Finset.univ.filter (fun α : F =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + (0 : F) • A) = 0))
        = {(0 : F)} := by
      ext α
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [det_smul_one_add_smul]
      constructor
      · intro h
        have hα : α ^ 2 = 0 := by linear_combination h
        exact pow_eq_zero_iff (by norm_num) |>.mp hα
      · intro h; rw [h]; ring
    rw [hrw, Finset.card_singleton]
  -- Nonzero rows: each contributes `r`.
  have hsum : ∑ β ∈ Finset.univ.erase (0 : F),
      (Finset.univ.filter (fun α : F =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) = 0)).card
      = (Fintype.card F - 1) * r := by
    rw [Finset.sum_congr rfl (fun β hβ => hr β (Finset.ne_of_mem_erase hβ))]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  rw [hf0, hsum]

end MatrixCommutant

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2' := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

section Invariance

variable {p n}


/-- The underlying matrix of an element satisfying the third auxiliary predicate commutes with that of every unit. -/
lemma val_mul_comm_of_auxiliaryThree {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g)
    (c : GL2' p n) : (c * g).val = (g * c).val := by
  rw [RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries] at hg
  obtain ⟨h01, h10, h00⟩ := hg
  simp only [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h00, mul_comm]


/-- Conjugating an element satisfying the third auxiliary predicate does not change its underlying matrix. -/
lemma val_conjugate_eq_self_of_auxiliaryThree {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g) (c : GL2' p n) :
    (c * g * c⁻¹).val = g.val := by
  have hcomm := val_mul_comm_of_auxiliaryThree hg c
  have hstep : (c * g * c⁻¹).val = (g * c * c⁻¹).val := by
    simp only [Units.val_mul] at hcomm ⊢; rw [hcomm]
  rw [hstep]
  simp only [mul_inv_cancel_right]


/-- The third auxiliary predicate is invariant under conjugation. -/
lemma auxiliaryThree_conjugate_iff (g x : GL2' p n) :
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (x⁻¹ * g * x) ↔ RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g := by
  constructor
  · intro h
    -- If `x⁻¹gx` is scalar it is central, so `g = x (x⁻¹gx) x⁻¹ = x⁻¹gx`.
    have hval : g.val = (x⁻¹ * g * x).val := by
      have h2 := val_conjugate_eq_self_of_auxiliaryThree h x
      have hrw : (x * (x⁻¹ * g * x) * x⁻¹) = g := by group
      rw [hrw] at h2; exact h2
    rw [RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries, hval, ← RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries]; exact h
  · intro h
    -- Conjugating a scalar gives back the same value, hence still scalar.
    have hval : (x⁻¹ * g * x).val = g.val := by
      have h2 := val_conjugate_eq_self_of_auxiliaryThree h x⁻¹
      simpa using h2
    rw [RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries, hval, ← RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries]; exact h


/-- The auxiliary value is unchanged by conjugation. -/
lemma auxiliaryInvariant_conjugate (g x : GL2' p n) :
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.entryDiscriminant (x⁻¹ * g * x) = RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.entryDiscriminant g :=
  RepresentationTheory.FiniteFieldMatrixCharacterValues.matrixInvariant_conj p n g x


/-- The second auxiliary predicate is invariant under conjugation. -/
lemma auxiliaryTwo_conjugate_iff (g x : GL2' p n) :
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta (x⁻¹ * g * x) ↔ RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g := by
  unfold RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta
  rw [auxiliaryInvariant_conjugate, auxiliaryThree_conjugate_iff]


/-- The fourth auxiliary predicate is invariant under conjugation. -/
lemma auxiliaryFour_conjugate_iff (g x : GL2' p n) :
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta (x⁻¹ * g * x) ↔ RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g := by
  unfold RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta
  rw [auxiliaryInvariant_conjugate]


/-- The first auxiliary predicate is invariant under conjugation. -/
lemma auxiliaryOne_conjugate_iff (g x : GL2' p n) :
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (x⁻¹ * g * x) ↔ RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha g := by
  unfold RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha
  rw [auxiliaryInvariant_conjugate]

end Invariance

section Counts

variable {p n}


/-- A third auxiliary natural number associated with a finite-field parameter pair. -/
noncomputable def auxiliaryCountThree : ℕ :=
  (ConjClasses.mk '' {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g}).ncard


/-- A second auxiliary natural number associated with a finite-field parameter pair. -/
noncomputable def auxiliaryCountTwo : ℕ :=
  (ConjClasses.mk '' {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g}).ncard


/-- A fourth auxiliary natural number associated with a finite-field parameter pair. -/
noncomputable def auxiliaryCountFour : ℕ :=
  (ConjClasses.mk '' {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g}).ncard


/-- A first auxiliary natural number associated with a finite-field parameter pair. -/
noncomputable def auxiliaryCountOne : ℕ :=
  (ConjClasses.mk '' {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha g}).ncard


/-- Conjugate elements satisfying the third auxiliary predicate are equal. -/
lemma eq_of_auxiliaryThree_of_isConj {g h : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g)
    (hconj : IsConj g h) : g = h := by
  rw [isConj_iff] at hconj
  obtain ⟨c, hc⟩ := hconj
  -- `c * g * c⁻¹ = g` because `g` is central; but that conjugate is `h`.
  have : (c * g * c⁻¹).val = g.val := val_conjugate_eq_self_of_auxiliaryThree hg c
  have hgh : g = c * g * c⁻¹ := Units.ext this.symm
  rw [hgh, hc]


/-- The third auxiliary predicate transfers between conjugate elements. -/
lemma auxiliaryThree_of_isConj {g h : GL2' p n} (hc : IsConj g h) (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g) :
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma h := by
  rw [isConj_iff] at hc
  obtain ⟨c, rfl⟩ := hc
  simpa using (auxiliaryThree_conjugate_iff g c⁻¹).mpr hg


/-- The second auxiliary predicate transfers between conjugate elements. -/
lemma auxiliaryTwo_of_isConj {g h : GL2' p n} (hc : IsConj g h) (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g) :
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta h := by
  rw [isConj_iff] at hc
  obtain ⟨c, rfl⟩ := hc
  simpa using (auxiliaryTwo_conjugate_iff g c⁻¹).mpr hg


/-- The fourth auxiliary predicate transfers between conjugate elements. -/
lemma auxiliaryFour_of_isConj {g h : GL2' p n} (hc : IsConj g h)
    (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g) : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta h := by
  rw [isConj_iff] at hc
  obtain ⟨c, rfl⟩ := hc
  simpa using (auxiliaryFour_conjugate_iff g c⁻¹).mpr hg


/-- Two predicates whose elements are never mutually conjugate have disjoint images in the set of conjugacy classes. -/
lemma disjoint_conjClasses_image_of_cross_disjoint {P Q : GL2' p n → Prop}
    (hPQ : ∀ g h, IsConj g h → P g → Q h → False) :
    Disjoint (ConjClasses.mk '' {g : GL2' p n | P g})
      (ConjClasses.mk '' {g : GL2' p n | Q g}) := by
  rw [Set.disjoint_left]
  rintro c ⟨g, hg, rfl⟩ ⟨h, hh, hmk⟩
  exact hPQ g h ((ConjClasses.mk_eq_mk_iff_isConj.mp hmk).symm) hg hh

variable [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)]


private lemma centralizerCard_eq_card_units {g : GL2' p n} (hns : ¬ RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = (Finset.univ.filter (fun ab : GaloisField p n × GaloisField p n =>
          Matrix.det (ab.1 • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n))
            + ab.2 • g.val) ≠ 0)).card := by
  have hns' : ¬ (g.val 0 1 = 0 ∧ g.val 1 0 = 0 ∧ g.val 0 0 = g.val 1 1) :=
    fun h => hns ((RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries g).mpr h)
  -- `α•1+β•g` commutes with `g`.
  have hcomm_mat : ∀ α β : GaloisField p n,
      (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) * g.val
        = g.val * (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) := by
    intro α β
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  -- Value of `mkOfDetNeZero`.
  have hvalMk : ∀ (α β : GaloisField p n)
      (h : Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) ≠ 0),
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
        (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) h).val
        = α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val := by
    intro α β h
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible]
  -- The bijection between good pairs and the centralizer.
  let f : {ab : GaloisField p n × GaloisField p n //
      Matrix.det (ab.1 • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + ab.2 • g.val) ≠ 0}
      → ↥(Subgroup.centralizer ({g} : Set (GL2' p n))) := fun ab =>
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
        (ab.1.1 • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + ab.1.2 • g.val) ab.2, by
      rw [Subgroup.mem_centralizer_iff]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy; subst hy
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hvalMk]
      exact (hcomm_mat ab.1.1 ab.1.2).symm⟩
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨α, β⟩, hab⟩ ⟨⟨α', β'⟩, hab'⟩ heq
      have hvv : α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val
          = α' • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β' • g.val := by
        have h1 := congrArg
          (fun u : ↥(Subgroup.centralizer ({g} : Set (GL2' p n))) => (u : GL2' p n).val) heq
        simpa [f, hvalMk] using h1
      exact Subtype.ext (smul_one_add_smul_injective hns' (A := g.val) hvv)
    · rintro ⟨M, hM⟩
      rw [Subgroup.mem_centralizer_iff] at hM
      have hcomm : M.val * g.val = g.val * M.val := by
        have hgm := hM g (Set.mem_singleton g)
        have h2 := congrArg (fun u : GL2' p n => u.val) hgm
        rw [Units.val_mul, Units.val_mul] at h2
        exact h2.symm
      obtain ⟨α, β, hαβ⟩ := exists_smul_add_smul_of_commute hns' hcomm
      have hMdet : Matrix.det M.val ≠ 0 := by
        have hu := M.isUnit
        rw [Matrix.isUnit_iff_isUnit_det] at hu
        exact hu.ne_zero
      have hdet : Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n))
          + β • g.val) ≠ 0 := by rw [← hαβ]; exact hMdet
      refine ⟨⟨(α, β), hdet⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      change (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet).val = M.val
      rw [hvalMk]; exact hαβ.symm
  rw [(Nat.card_congr (Equiv.ofBijective f hbij)).symm, Nat.card_eq_fintype_card,
    Fintype.card_subtype]


private lemma centralizerCard_of_nonscalar {g : GL2' p n} (hns : ¬ RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g)
    {r : ℕ} (hr : ∀ β : GaloisField p n, β ≠ 0 →
      (Finset.univ.filter (fun α : GaloisField p n =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) = 0)).card
        = r) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GaloisField p n) ^ 2
        - (1 + (Fintype.card (GaloisField p n) - 1) * r) := by
  rw [centralizerCard_eq_card_units hns]
  have hz := card_detZero_pairs (A := g.val) hr
  simp only [ne_eq]
  rw [Finset.filter_not, Finset.card_univ_sdiff, Fintype.card_prod, hz, ← pow_two]


private lemma quadDisc_eq (g : GL2' p n) (β : GaloisField p n) :
    ((g.val 0 0 + g.val 1 1) * β) ^ 2
      - 4 * 1 * ((g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) * β ^ 2)
      = β ^ 2 * RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.entryDiscriminant g := by
  rw [RepresentationTheory.FiniteFieldUnitClassDecomposition.entryDiscriminant_eq]; ring


private lemma alphaFiber_eq (g : GL2' p n) (β : GaloisField p n) :
    (Finset.univ.filter (fun α : GaloisField p n =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) = 0))
      = (Finset.univ.filter (fun α : GaloisField p n =>
        (1 : GaloisField p n) * α ^ 2 + ((g.val 0 0 + g.val 1 1) * β) * α
          + (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) * β ^ 2 = 0)) := by
  apply Finset.filter_congr
  intro α _
  rw [det_smul_one_add_smul]
  constructor <;> intro h <;> linear_combination h


private lemma centralizerCard_parabolic {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) := by
  obtain ⟨hdisc, hns⟩ := hg
  have hr : ∀ β : GaloisField p n, β ≠ 0 →
      (Finset.univ.filter (fun α : GaloisField p n =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) = 0)).card
        = 1 := by
    intro β _
    rw [alphaFiber_eq]
    apply RepresentationTheory.FiniteFieldMatrixCharacterValues.card_quadratic_roots_eq_one_of_discriminant_eq_zero _ _ _ one_ne_zero
    rw [quadDisc_eq, hdisc, mul_zero]
  rw [centralizerCard_of_nonscalar hns hr]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := GaloisField p n))
  rw [hm]
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one, mul_one]
  have e1 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
  have e2 : (m + 1) * m = m ^ 2 + m := by ring
  omega


private lemma two_ne_zero_galoisField (hp2 : p ≠ 2) : (2 : GaloisField p n) ≠ 0 := by
  intro h
  have hchar2 : CharP (GaloisField p n) 2 :=
    (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h
  have hp_char : CharP (GaloisField p n) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (GaloisField p n)).injective p
  exact hp2 (CharP.eq (GaloisField p n) hp_char hchar2)


private lemma centralizerCard_splitSemisimple (hp2 : p ≠ 2) {g : GL2' p n}
    (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = (Fintype.card (GaloisField p n) - 1) ^ 2 := by
  obtain ⟨hdne, hsq⟩ := hg
  have hns : ¬ RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g := fun hsc => RepresentationTheory.FiniteFieldUnitClassDecomposition.not_classPredicateDelta_of_classPredicateGamma g hsc ⟨hdne, hsq⟩
  haveI : NeZero (2 : GaloisField p n) := ⟨two_ne_zero_galoisField hp2⟩
  have hr : ∀ β : GaloisField p n, β ≠ 0 →
      (Finset.univ.filter (fun α : GaloisField p n =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) = 0)).card
        = 2 := by
    intro β hβ
    rw [alphaFiber_eq]
    refine RepresentationTheory.FiniteFieldMatrixCharacterValues.card_quadratic_roots_eq_two_of_discriminant_isSquare _ _ _ one_ne_zero ?_ ?_
    · rw [quadDisc_eq]; exact mul_ne_zero (pow_ne_zero 2 hβ) hdne
    · rw [quadDisc_eq]; exact IsSquare.mul ⟨β, by ring⟩ hsq
  rw [centralizerCard_of_nonscalar hns hr]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := GaloisField p n))
  rw [hm]
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  have e1 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
  omega


private lemma centralizerCard_elliptic {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GaloisField p n) ^ 2 - 1 := by
  have hns : ¬ RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g := fun hsc => RepresentationTheory.FiniteFieldUnitClassDecomposition.not_classPredicateAlpha_of_classPredicateGamma g hsc hg
  have hr : ∀ β : GaloisField p n, β ≠ 0 →
      (Finset.univ.filter (fun α : GaloisField p n =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) = 0)).card
        = 0 := by
    intro β hβ
    rw [alphaFiber_eq]
    refine RepresentationTheory.FiniteFieldMatrixCharacterValues.card_quadratic_roots_eq_zero_of_discriminant_not_isSquare _ _ _ one_ne_zero ?_
    rw [quadDisc_eq]
    rintro ⟨s, hs⟩
    exact hg ⟨s * β⁻¹, by field_simp; linear_combination hs⟩
  rw [centralizerCard_of_nonscalar hns hr]
  simp

omit [DecidableEq (GaloisField p n)] in

private lemma card_GL2_eq :
    Fintype.card (GL2' p n)
      = (Fintype.card (GaloisField p n) ^ 2 - 1)
        * (Fintype.card (GaloisField p n) ^ 2 - Fintype.card (GaloisField p n)) := by
  have h := Matrix.card_GL_field (𝔽 := GaloisField p n) 2
  rw [Nat.card_eq_fintype_card] at h
  rw [h]; simp [Fin.prod_univ_two, pow_zero, pow_one]

omit [DecidableEq (GaloisField p n)] in
omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] in

/-- The cardinality of the general linear group in dimension two over a finite field is `(q ^ 2 - 1) * (q ^ 2 - q)`. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem card_generalLinearGroup_fin_two :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))
      = (Nat.card (GaloisField p n) ^ 2 - 1)
        * (Nat.card (GaloisField p n) ^ 2 - Nat.card (GaloisField p n)) := by
  letI := Fintype.ofFinite (GaloisField p n)
  simpa [Fin.prod_univ_two, pow_zero, pow_one] using
    (Matrix.card_GL_field (𝔽 := GaloisField p n) 2)

omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] in

/-- The cardinality of the general linear group in dimension two over a finite field is `q * (q + 1) * (q - 1) ^ 2`. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem card_generalLinearGroup_fin_two_factored :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))
      = Nat.card (GaloisField p n) * (Nat.card (GaloisField p n) + 1)
        * (Nat.card (GaloisField p n) - 1) ^ 2 := by
  rw [card_generalLinearGroup_fin_two]
  have hsq : Nat.card (GaloisField p n) ^ 2 - 1
      = (Nat.card (GaloisField p n) - 1) * (Nat.card (GaloisField p n) + 1) := by
    rw [Nat.sub_mul]
    have hmul : Nat.card (GaloisField p n) * (Nat.card (GaloisField p n) + 1)
        = Nat.card (GaloisField p n) ^ 2 + Nat.card (GaloisField p n) := by ring
    rw [hmul, one_mul]
    omega
  have hlin : Nat.card (GaloisField p n) ^ 2 - Nat.card (GaloisField p n)
      = Nat.card (GaloisField p n) * (Nat.card (GaloisField p n) - 1) := by
    rw [Nat.mul_sub_left_distrib]
    simp only [mul_one, pow_two]
  rw [hsq, hlin]
  ring


private lemma card_ge_three (hp2 : p ≠ 2) (hn : n ≠ 0) :
    3 ≤ Fintype.card (GaloisField p n) := by
  rw [Fintype.card_eq_nat_card, GaloisField.card p n hn]
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  calc 3 ≤ p := hp3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hn)


private lemma count_from_bridge {P : GL2' p n → Prop}
    (hclosed : ∀ g ∈ {g : GL2' p n | P g}, ∀ x : GL2' p n,
      x * g * x⁻¹ ∈ {g : GL2' p n | P g})
    {d : ℕ}
    (hd : ∀ g ∈ {g : GL2' p n | P g},
      Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n))) = d)
    {cardS target classSize : ℕ}
    (hSncard : {g : GL2' p n | P g}.ncard = cardS)
    (hclass : Fintype.card (GL2' p n) / d = classSize)
    (hpos : 0 < classSize)
    (harith : target * classSize = cardS) :
    (ConjClasses.mk '' {g : GL2' p n | P g}).ncard = target := by
  have hbridge := ncard_conjClasses_image_mul_classSize_eq hclosed hd
  rw [hSncard, hclass] at hbridge
  exact Nat.eq_of_mul_eq_mul_right hpos (hbridge.trans harith.symm)


private lemma half_mul (a b : ℕ) (h : 2 ∣ a) : a / 2 * b = a * b / 2 := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 2),
    show 2 * k * b = 2 * (k * b) by ring, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]


/-- The third auxiliary count is `q - 1` for nonzero extension degree. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem auxiliaryCountThree_eq (hn : n ≠ 0) :
    auxiliaryCountThree (p := p) (n := n) = Fintype.card (GaloisField p n) - 1 := by
  -- `ConjClasses.mk` is injective on the scalar elements (each scalar class is a
  -- singleton), so the number of scalar classes equals the number of scalar
  -- elements, which is `q − 1` by `RepresentationTheory.FiniteFieldUnitClassDecomposition.card_classPredicateGamma`.
  have hinj : Set.InjOn ConjClasses.mk {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g} := by
    intro g hg _ _ hgh
    simp only [Set.mem_setOf_eq] at hg
    exact eq_of_auxiliaryThree_of_isConj hg (ConjClasses.mk_eq_mk_iff_isConj.mp hgh)
  rw [auxiliaryCountThree, Set.InjOn.ncard_image hinj]
  -- Rewrite the scalar set as the coercion of the scalar filter, then count.
  have hset : {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g}
      = ↑(Finset.univ.filter fun g : GL2' p n => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g) := by
    ext g; simp
  rw [hset, Set.ncard_coe_finset, RepresentationTheory.FiniteFieldUnitClassDecomposition.card_classPredicateGamma (p := p) hn]


/-- The second auxiliary count is `q - 1` when the characteristic is not two and the extension degree is nonzero. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem auxiliaryCountTwo_eq (hp2 : p ≠ 2) (hn : n ≠ 0) :
    auxiliaryCountTwo (p := p) (n := n) = Fintype.card (GaloisField p n) - 1 := by
  simp only [auxiliaryCountTwo]
  have hq3 := card_ge_three (p := p) (n := n) hp2 hn
  have hqe : Fintype.card (GaloisField p n) ^ 2 - Fintype.card (GaloisField p n)
      = Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) := by
    obtain ⟨m, hm⟩ :=
      Nat.exists_eq_succ_of_ne_zero (show Fintype.card (GaloisField p n) ≠ 0 by omega)
    rw [hm]; simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    have : (m + 1) ^ 2 = (m + 1) * m + (m + 1) := by ring
    omega
  apply count_from_bridge (P := fun g => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g)
    (cardS := (Fintype.card (GaloisField p n) - 1) * (Fintype.card (GaloisField p n) ^ 2 - 1))
    (target := Fintype.card (GaloisField p n) - 1)
    (classSize := Fintype.card (GaloisField p n) ^ 2 - 1)
  case hclosed =>
    intro g hg x
    simp only [Set.mem_setOf_eq] at hg ⊢
    exact auxiliaryTwo_of_isConj (isConj_iff.mpr ⟨x, rfl⟩) hg
  case hd =>
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    exact centralizerCard_parabolic hg
  case hSncard =>
    rw [show {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g}
        = ↑(Finset.univ.filter (fun g : GL2' p n => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g)) from by ext g; simp,
      Set.ncard_coe_finset, RepresentationTheory.FiniteFieldUnitClassDecomposition.card_classPredicateBeta hp2 hn]
  case hclass =>
    rw [card_GL2_eq, hqe]
    exact Nat.mul_div_cancel _ (Nat.mul_pos (by omega) (by omega))
  case hpos =>
    have : 1 < Fintype.card (GaloisField p n) ^ 2 := by nlinarith [hq3]
    omega
  case harith => ring


/-- The fourth auxiliary count is `(q - 1) * (q - 2) / 2` when the characteristic is not two and the extension degree is nonzero. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem auxiliaryCountFour_eq (hp2 : p ≠ 2) (hn : n ≠ 0) :
    auxiliaryCountFour (p := p) (n := n) =
      (Fintype.card (GaloisField p n) - 1) * (Fintype.card (GaloisField p n) - 2) / 2 := by
  simp only [auxiliaryCountFour]
  have hq3 := card_ge_three (p := p) (n := n) hp2 hn
  have hqodd : Odd (Fintype.card (GaloisField p n)) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p n hn]
    exact (Nat.Prime.odd_of_ne_two hp.out hp2).pow
  obtain ⟨m, hm⟩ := hqodd
  have hq1 : Fintype.card (GaloisField p n) - 1 = 2 * m := by omega
  have hGLfact : Fintype.card (GL2' p n)
      = (Fintype.card (GaloisField p n) - 1) ^ 2
        * (Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) + 1)) := by
    rw [card_GL2_eq]
    obtain ⟨k, hk⟩ :=
      Nat.exists_eq_succ_of_ne_zero (show Fintype.card (GaloisField p n) ≠ 0 by omega)
    rw [hk]; simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    have h1 : (k + 1) ^ 2 - 1 = k ^ 2 + 2 * k := by
      have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      omega
    have h2 : (k + 1) ^ 2 - (k + 1) = (k + 1) * k := by
      have : (k + 1) ^ 2 = (k + 1) * k + (k + 1) := by ring
      omega
    rw [h1, h2]; ring
  apply count_from_bridge (P := fun g => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g)
    (cardS := (Fintype.card (GaloisField p n) - 1) * (Fintype.card (GaloisField p n) - 2)
      * Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) + 1) / 2)
    (target := (Fintype.card (GaloisField p n) - 1) * (Fintype.card (GaloisField p n) - 2) / 2)
    (classSize := Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) + 1))
  case hclosed =>
    intro g hg x
    simp only [Set.mem_setOf_eq] at hg ⊢
    exact auxiliaryFour_of_isConj (isConj_iff.mpr ⟨x, rfl⟩) hg
  case hd =>
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    exact centralizerCard_splitSemisimple hp2 hg
  case hSncard =>
    rw [show {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g}
        = ↑(Finset.univ.filter (fun g : GL2' p n => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g)) from by ext g; simp,
      Set.ncard_coe_finset, RepresentationTheory.FiniteFieldUnitClassDecomposition.card_classPredicateDelta hp2 hn]
  case hclass =>
    rw [hGLfact]
    exact Nat.mul_div_cancel_left _ (pow_pos (by omega) 2)
  case hpos => exact Nat.mul_pos (by omega) (by omega)
  case harith =>
    rw [half_mul _ _
      ⟨m * (Fintype.card (GaloisField p n) - 2), by rw [hq1]; ring⟩]
    congr 1; ring


/-- The first auxiliary count is `q * (q - 1) / 2` when the characteristic is not two and the extension degree is nonzero. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem auxiliaryCountOne_eq (hp2 : p ≠ 2) (hn : n ≠ 0) :
    auxiliaryCountOne (p := p) (n := n) =
      Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2 := by
  simp only [auxiliaryCountOne]
  have hq3 := card_ge_three (p := p) (n := n) hp2 hn
  have hqodd : Odd (Fintype.card (GaloisField p n)) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p n hn]
    exact (Nat.Prime.odd_of_ne_two hp.out hp2).pow
  obtain ⟨m, hm⟩ := hqodd
  have hq1 : Fintype.card (GaloisField p n) - 1 = 2 * m := by omega
  have hq9 : 9 ≤ Fintype.card (GaloisField p n) ^ 2 := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_left hq3 2
  apply count_from_bridge (P := fun g => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha g)
    (cardS := Fintype.card (GaloisField p n) ^ 2 * (Fintype.card (GaloisField p n) - 1) ^ 2 / 2)
    (target := Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2)
    (classSize := Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1))
  case hclosed =>
    intro g hg x
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h := (auxiliaryOne_conjugate_iff g x⁻¹).mpr hg
    rwa [inv_inv] at h
  case hd =>
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    exact centralizerCard_elliptic hg
  case hSncard =>
    rw [show {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha g}
        = ↑(Finset.univ.filter (fun g : GL2' p n => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha g)) from by ext g; simp,
      Set.ncard_coe_finset, RepresentationTheory.FiniteFieldUnitClassDecomposition.card_classPredicateAlpha hp2 hn]
  case hclass =>
    rw [card_GL2_eq,
      Nat.mul_div_cancel_left _
        (by omega : 0 < Fintype.card (GaloisField p n) ^ 2 - 1)]
    obtain ⟨k, hk⟩ :=
      Nat.exists_eq_succ_of_ne_zero (show Fintype.card (GaloisField p n) ≠ 0 by omega)
    rw [hk]; simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    have : (k + 1) ^ 2 = (k + 1) * k + (k + 1) := by ring
    omega
  case hpos => exact Nat.mul_pos (by omega) (by omega)
  case harith =>
    rw [half_mul _ _ ⟨Fintype.card (GaloisField p n) * m, by rw [hq1]; ring⟩]
    congr 1; ring


/-- The number of conjugacy classes is the sum of the four associated auxiliary counts. -/
theorem card_conjClasses_eq_sum_auxiliaryCounts :
    Nat.card (ConjClasses (GL2' p n)) =
      auxiliaryCountThree (p := p) (n := n) + auxiliaryCountTwo (p := p) (n := n) +
        auxiliaryCountFour (p := p) (n := n) + auxiliaryCountOne (p := p) (n := n) := by
  haveI : Finite (GL2' p n) := Finite.of_fintype _
  haveI : Finite (ConjClasses (GL2' p n)) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  simp only [auxiliaryCountThree, auxiliaryCountTwo, auxiliaryCountFour, auxiliaryCountOne]
  set CS := ConjClasses.mk '' {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g} with hCS
  set CP := ConjClasses.mk '' {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g} with hCP
  set CSS := ConjClasses.mk '' {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g} with hCSS
  set CE := ConjClasses.mk '' {g : GL2' p n | RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha g} with hCE
  -- The four type-images cover every conjugacy class.
  have hcover : (Set.univ : Set (ConjClasses (GL2' p n))) = CS ∪ CP ∪ CSS ∪ CE := by
    ext c
    simp only [Set.mem_univ, Set.mem_union, true_iff]
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    rcases RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicates_exhaustive g with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Set.mem_image_of_mem _ h)))
    · exact Or.inl (Or.inl (Or.inr (Set.mem_image_of_mem _ h)))
    · exact Or.inl (Or.inr (Set.mem_image_of_mem _ h))
    · exact Or.inr (Set.mem_image_of_mem _ h)
  -- Pairwise disjointness of the four type-images, from element-level disjointness.
  have dSP : Disjoint CS CP := disjoint_conjClasses_image_of_cross_disjoint
    (fun g h hc hg hh => hh.2 (auxiliaryThree_of_isConj hc hg))
  have dSSS : Disjoint CS CSS := disjoint_conjClasses_image_of_cross_disjoint
    (fun g h hc hg hh => RepresentationTheory.FiniteFieldUnitClassDecomposition.not_classPredicateDelta_of_classPredicateGamma h (auxiliaryThree_of_isConj hc hg) hh)
  have dSE : Disjoint CS CE := disjoint_conjClasses_image_of_cross_disjoint
    (fun g h hc hg hh => RepresentationTheory.FiniteFieldUnitClassDecomposition.not_classPredicateAlpha_of_classPredicateGamma h (auxiliaryThree_of_isConj hc hg) hh)
  have dPSS : Disjoint CP CSS := disjoint_conjClasses_image_of_cross_disjoint
    (fun g h hc hg hh =>
      RepresentationTheory.FiniteFieldUnitClassDecomposition.not_classPredicateDelta_of_classPredicateBeta h (auxiliaryTwo_of_isConj hc hg) hh)
  have dPE : Disjoint CP CE := disjoint_conjClasses_image_of_cross_disjoint
    (fun g h hc hg hh => RepresentationTheory.FiniteFieldUnitClassDecomposition.not_classPredicateAlpha_of_classPredicateBeta h (auxiliaryTwo_of_isConj hc hg) hh)
  have dSSE : Disjoint CSS CE := disjoint_conjClasses_image_of_cross_disjoint
    (fun g h hc hg hh =>
      RepresentationTheory.FiniteFieldUnitClassDecomposition.not_classPredicateAlpha_of_classPredicateDelta h (auxiliaryFour_of_isConj hc hg) hh)
  have hSPuSS : Disjoint (CS ∪ CP) CSS := disjoint_sup_left.mpr ⟨dSSS, dPSS⟩
  have hSPSSuE : Disjoint (CS ∪ CP ∪ CSS) CE :=
    disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨dSE, dPE⟩, dSSE⟩
  rw [← Set.ncard_univ, hcover, Set.ncard_union_eq hSPSSuE, Set.ncard_union_eq hSPuSS,
    Set.ncard_union_eq dSP]


/-- The number of conjugacy classes is one less than the square of the finite-field cardinality when the characteristic is not two and the extension degree is nonzero. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := supporting),
  source_ref "Chapter5/Discussion_complementary_series_summary/Derived01" (role := supporting)]
theorem card_conjClasses_eq_fieldCard_sq_sub_one (hp2 : p ≠ 2) (hn : n ≠ 0) :
    Nat.card (ConjClasses (GL2' p n)) =
      Fintype.card (GaloisField p n) ^ 2 - 1 := by
  rw [card_conjClasses_eq_sum_auxiliaryCounts, auxiliaryCountThree_eq hn, auxiliaryCountTwo_eq hp2 hn,
    auxiliaryCountFour_eq hp2 hn, auxiliaryCountOne_eq hp2 hn]
  set q := Fintype.card (GaloisField p n) with hq
  -- `q = pⁿ` is odd and at least 3, so the two `/2` divisions are exact.
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hqval : q = p ^ n := by
    rw [hq, ← Nat.card_eq_fintype_card]; exact GaloisField.card p n hn
  have hqodd : Odd q := by
    rw [hqval]; exact (Nat.Prime.odd_of_ne_two hp.out hp2).pow
  have hq3 : 3 ≤ q := by
    rw [hqval]
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨m, hm⟩ := hqodd
  have hm1 : 1 ≤ m := by omega
  have hq1 : q - 1 = 2 * m := by omega
  have hq2 : q - 2 = 2 * m - 1 := by omega
  have hdiv1 : (q - 1) * (q - 2) / 2 = m * (q - 2) := by
    rw [hq1, show 2 * m * (q - 2) = 2 * (m * (q - 2)) from by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hdiv2 : q * (q - 1) / 2 = q * m := by
    rw [hq1, show q * (2 * m) = 2 * (q * m) from by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hkey : m * (q - 2) + q * m = 4 * m ^ 2 := by
    rw [hq2, hm]
    have h4 : (2 * m - 1) + (2 * m + 1) = 4 * m := by omega
    calc m * (2 * m - 1) + (2 * m + 1) * m
        = m * ((2 * m - 1) + (2 * m + 1)) := by ring
      _ = m * (4 * m) := by rw [h4]
      _ = 4 * m ^ 2 := by ring
  have hRHS : q ^ 2 - 1 = 4 * m ^ 2 + 4 * m := by
    have : q ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by rw [hm]; ring
    omega
  rw [hdiv1, hdiv2, hq1]
  omega

/-! ## Per-type counts, centralizers, and conjugation orbits -/


/-- The product of the cardinalities of the conjugation orbit and centralizer of an element equals the cardinality of the ambient finite group. -/
theorem card_conjOrbit_mul_card_centralizer (g : GL2' p n) :
    Nat.card (MulAction.orbit (ConjAct (GL2' p n)) g)
        * Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GL2' p n) := by
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct (GL2' p n)) g),
    ← Nat.card_eq_fintype_card,
    Nat.card_congr (ConjAct.toConjAct (G := GL2' p n)).toEquiv]
  exact (MulAction.stabilizer (ConjAct (GL2' p n)) g).index_mul_card


/-- Under the third auxiliary predicate, the centralizer has cardinality `(q ^ 2 - 1) * (q ^ 2 - q)`. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem card_centralizer_eq_generalLinearFactors_of_auxiliaryThree {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = (Fintype.card (GaloisField p n) ^ 2 - 1)
        * (Fintype.card (GaloisField p n) ^ 2 - Fintype.card (GaloisField p n)) := by
  have htop : Subgroup.centralizer ({g} : Set (GL2' p n)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    exact Units.ext (val_mul_comm_of_auxiliaryThree hg x).symm
  rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, card_GL2_eq]


/-- Under the second auxiliary predicate, the centralizer has cardinality `q * (q - 1)`. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem card_centralizer_eq_fieldCard_mul_pred_of_auxiliaryTwo {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) :=
  centralizerCard_parabolic hg


/-- Under the fourth auxiliary predicate, the centralizer has cardinality `(q - 1) ^ 2` when the characteristic is not two. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem card_centralizer_eq_fieldCard_pred_sq_of_auxiliaryFour (hp2 : p ≠ 2) {g : GL2' p n}
    (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = (Fintype.card (GaloisField p n) - 1) ^ 2 :=
  centralizerCard_splitSemisimple hp2 hg


/-- Under the first auxiliary predicate, the centralizer has cardinality `q ^ 2 - 1`. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem card_centralizer_eq_fieldCard_sq_sub_one_of_auxiliaryOne {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GaloisField p n) ^ 2 - 1 :=
  centralizerCard_elliptic hg


private lemma card_ge_two (hn : n ≠ 0) : 2 ≤ Fintype.card (GaloisField p n) := by
  rw [Fintype.card_eq_nat_card, GaloisField.card p n hn]
  calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right (by have := hp.out.two_le; omega)
      (Nat.one_le_iff_ne_zero.mpr hn)


private lemma sq_sub_self (q : ℕ) : q ^ 2 - q = q * (q - 1) := by
  cases q with
  | zero => rfl
  | succ k =>
    simp only [Nat.succ_sub_one]
    have : (k + 1) ^ 2 = (k + 1) * k + (k + 1) := by ring
    omega


/-- Under the third auxiliary predicate, the conjugation orbit is a singleton. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem card_conjOrbit_eq_one_of_auxiliaryThree {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g) :
    Nat.card (MulAction.orbit (ConjAct (GL2' p n)) g) = 1 := by
  have hmul := card_conjOrbit_mul_card_centralizer g
  rw [card_centralizer_eq_generalLinearFactors_of_auxiliaryThree hg, ← card_GL2_eq] at hmul
  exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos (by rw [one_mul]; exact hmul)


/-- Under the second auxiliary predicate, the conjugation orbit has cardinality `q ^ 2 - 1` for nonzero extension degree. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem card_conjOrbit_eq_fieldCard_sq_sub_one_of_auxiliaryTwo (hn : n ≠ 0) {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g) :
    Nat.card (MulAction.orbit (ConjAct (GL2' p n)) g)
      = Fintype.card (GaloisField p n) ^ 2 - 1 := by
  have hq2 := card_ge_two (p := p) (n := n) hn
  have hmul := card_conjOrbit_mul_card_centralizer g
  rw [card_centralizer_eq_fieldCard_mul_pred_of_auxiliaryTwo hg, card_GL2_eq,
    sq_sub_self (Fintype.card (GaloisField p n))] at hmul
  have hpos : 0 < Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) :=
    Nat.mul_pos (by omega) (by omega)
  exact Nat.eq_of_mul_eq_mul_right hpos hmul


/-- Under the fourth auxiliary predicate, the conjugation orbit has cardinality `q ^ 2 + q` when the characteristic is not two and the extension degree is nonzero. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem card_conjOrbit_eq_fieldCard_sq_add_self_of_auxiliaryFour (hp2 : p ≠ 2) (hn : n ≠ 0) {g : GL2' p n}
    (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g) :
    Nat.card (MulAction.orbit (ConjAct (GL2' p n)) g)
      = Fintype.card (GaloisField p n) ^ 2 + Fintype.card (GaloisField p n) := by
  have hq2 := card_ge_two (p := p) (n := n) hn
  have hmul := card_conjOrbit_mul_card_centralizer g
  rw [card_centralizer_eq_fieldCard_pred_sq_of_auxiliaryFour hp2 hg, card_GL2_eq] at hmul
  have hpos : 0 < (Fintype.card (GaloisField p n) - 1) ^ 2 := pow_pos (by omega) 2
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hmul]
  -- `(q²−1)(q²−q) = (q²+q)(q−1)²`
  obtain ⟨k, hk⟩ :=
    Nat.exists_eq_succ_of_ne_zero (show Fintype.card (GaloisField p n) ≠ 0 by omega)
  rw [hk]; simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  have h1 : (k + 1) ^ 2 - 1 = k ^ 2 + 2 * k := by
    have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    omega
  have h2 : (k + 1) ^ 2 - (k + 1) = (k + 1) * k := by
    have : (k + 1) ^ 2 = (k + 1) * k + (k + 1) := by ring
    omega
  rw [h1, h2]; ring


/-- Under the first auxiliary predicate, the conjugation orbit has cardinality `q ^ 2 - q` for nonzero extension degree. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem card_conjOrbit_eq_fieldCard_sq_sub_self_of_auxiliaryOne (hn : n ≠ 0) {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha g) :
    Nat.card (MulAction.orbit (ConjAct (GL2' p n)) g)
      = Fintype.card (GaloisField p n) ^ 2 - Fintype.card (GaloisField p n) := by
  have hq2 := card_ge_two (p := p) (n := n) hn
  have hmul := card_conjOrbit_mul_card_centralizer g
  rw [card_centralizer_eq_fieldCard_sq_sub_one_of_auxiliaryOne hg, card_GL2_eq] at hmul
  have hq4 : 4 ≤ Fintype.card (GaloisField p n) ^ 2 := by nlinarith [hq2]
  have hpos : 0 < Fintype.card (GaloisField p n) ^ 2 - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hmul, mul_comm]

end Counts

/-! ## Representatives and normal forms -/

section Representatives

open scoped Matrix

variable {p n}


/-- An invertible matrix intertwining the underlying matrices of two units exhibits them as conjugate. -/
lemma isConj_of_val_mul_eq_mul_val {g r : GL2' p n} (P : GL2' p n)
    (h : g.val * P.val = P.val * r.val) : IsConj g r := by
  refine isConj_iff.mpr ⟨P⁻¹, Units.ext ?_⟩
  have hPP : (P⁻¹ : GL2' p n).val * P.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, inv_inv]
  calc (P⁻¹ : GL2' p n).val * g.val * P.val
      = (P⁻¹ : GL2' p n).val * (g.val * P.val) := by rw [mul_assoc]
    _ = (P⁻¹ : GL2' p n).val * (P.val * r.val) := by rw [h]
    _ = (P⁻¹ : GL2' p n).val * P.val * r.val := by rw [mul_assoc]
    _ = r.val := by rw [hPP, one_mul]


private lemma detval_ne_zero (g : GL2' p n) : Matrix.det g.val ≠ 0 := by
  intro h0
  have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  rw [h0, zero_mul] at hdet1; exact one_ne_zero hdet1.symm


/-- A scalar invertible two-by-two matrix constructed from a nonzero finite-field element. -/
noncomputable def scalarUnit (x : GaloisField p n) (hx : x ≠ 0) : GL2' p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (x • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)))
    (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
        exact pow_ne_zero 2 hx)

/-- The underlying matrix of `scalarUnit x` is `x` times the identity matrix. -/
@[simp] lemma val_scalarUnit (x : GaloisField p n) (hx : x ≠ 0) :
    (scalarUnit x hx).val = x • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) := by
  simp [scalarUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]


/-- An element satisfying the third auxiliary predicate is conjugate to a scalar unit. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem exists_isConj_scalarUnit_of_auxiliaryThree {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g) :
    ∃ (x : GaloisField p n) (hx : x ≠ 0), IsConj g (scalarUnit x hx) := by
  obtain ⟨h01, h10, h00⟩ := (RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries g).mp hg
  have hdet : Matrix.det g.val = g.val 0 0 * g.val 0 0 := by
    rw [Matrix.det_fin_two, h01, h10, ← h00]; ring
  have hx : g.val 0 0 ≠ 0 := by
    intro h0
    have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [hdet, h0, mul_zero, zero_mul] at hdet1
    exact one_ne_zero hdet1.symm
  refine ⟨g.val 0 0, hx, ?_⟩
  have heq : scalarUnit (g.val 0 0) hx = g := by
    apply Units.ext
    rw [val_scalarUnit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h01, h10, h00]
  rw [heq]


/-- An invertible two-by-two matrix constructed from a nonzero finite-field element. -/
noncomputable def upperTriangularUnit (x : GaloisField p n) (hx : x ≠ 0) : GL2' p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![x, 1; 0, x]
    (by rw [Matrix.det_fin_two_of]; simpa using mul_ne_zero hx hx)

/-- The underlying matrix of `upperTriangularUnit x` has rows `(x, 1)` and `(0, x)`. -/
@[simp] lemma val_upperTriangularUnit (x : GaloisField p n) (hx : x ≠ 0) :
    (upperTriangularUnit x hx).val = !![x, 1; 0, x] := by
  simp [upperTriangularUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]


private lemma mkOfDetNeZero_val (M : Matrix (Fin 2) (Fin 2) (GaloisField p n))
    (h : M.det ≠ 0) : (Matrix.GeneralLinearGroup.mkOfDetNeZero M h).val = M := by
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible]


/-- In characteristic other than two, an element satisfying the second auxiliary predicate is conjugate to an upper-triangular unit of the specified form. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem exists_isConj_upperTriangularUnit_of_auxiliaryTwo (hp2 : p ≠ 2) {g : GL2' p n} (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g) :
    ∃ (x : GaloisField p n) (hx : x ≠ 0), IsConj g (upperTriangularUnit x hx) := by
  obtain ⟨hdisc, hns⟩ := hg
  rw [RepresentationTheory.FiniteFieldUnitClassDecomposition.entryDiscriminant_eq] at hdisc
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h
    have hchar2 : CharP (GaloisField p n) 2 :=
      (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h
    have hp_char : CharP (GaloisField p n) p :=
      charP_of_injective_algebraMap (algebraMap (ZMod p) (GaloisField p n)).injective p
    exact hp2 (CharP.eq (GaloisField p n) hp_char hchar2)
  set a := g.val 0 0 with ha
  set b := g.val 0 1 with hb
  set c := g.val 1 0 with hc'
  set d := g.val 1 1 with hd
  -- The repeated eigenvalue `x = tr/2`.
  set x := (a + d) / 2 with hxdef
  have hx2 : a + d = 2 * x := by rw [hxdef]; field_simp
  -- `det g = x²`, hence `x ≠ 0`.
  have hkey : (a - x) ^ 2 + b * c = 0 := by
    have h4 : (4 : GaloisField p n) ≠ 0 := by
      have : (4 : GaloisField p n) = 2 * 2 := by ring
      rw [this]; exact mul_ne_zero h2 h2
    apply mul_left_cancel₀ h4
    rw [mul_zero]
    linear_combination hdisc + (3 * a - d - 2 * x) * hx2
  have hdetx : Matrix.det g.val = x * x := by
    rw [Matrix.det_fin_two, ← ha, ← hb, ← hc', ← hd]
    linear_combination -hkey + a * hx2
  have hx : x ≠ 0 := by
    intro h0
    have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [hdetx, h0, mul_zero, zero_mul] at hdet1
    exact one_ne_zero hdet1.symm
  refine ⟨x, hx, ?_⟩
  by_cases hc0 : c = 0
  · -- `c = 0` forces `a = d = x`; representative conjugator `!![b,0;0,1]`.
    have hax : a = x := by
      have hk : (a - x) ^ 2 = 0 := by rw [← hkey, hc0, mul_zero, add_zero]
      have : a - x = 0 := by
        exact pow_eq_zero_iff (by norm_num) |>.mp hk
      linear_combination this
    have hdx : d = x := by linear_combination hx2 - hax
    have hbne : b ≠ 0 := by
      intro hb0
      exact hns ((RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries g).mpr ⟨hb0, hc0, by rw [← ha, ← hd, hax, hdx]⟩)
    have hPdet : Matrix.det (!![b, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField p n)) ≠ 0 := by
      rw [Matrix.det_fin_two_of]; simpa using hbne
    refine isConj_of_val_mul_eq_mul_val (Matrix.GeneralLinearGroup.mkOfDetNeZero !![b, 0; 0, 1] hPdet) ?_
    rw [mkOfDetNeZero_val, val_upperTriangularUnit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hc', ← hd, hc0, hax, hdx] ;
      ring
  · -- `c ≠ 0`: representative conjugator `!![a-x,1;c,0]`, det `-c ≠ 0`.
    have hPdet : Matrix.det (!![a - x, 1; c, 0] : Matrix (Fin 2) (Fin 2) (GaloisField p n)) ≠ 0 := by
      rw [Matrix.det_fin_two_of]; simpa using hc0
    refine isConj_of_val_mul_eq_mul_val (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a - x, 1; c, 0] hPdet) ?_
    rw [mkOfDetNeZero_val, val_upperTriangularUnit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hc', ← hd] <;>
      first
        | linear_combination hkey
        | linear_combination c * hx2


/-- An invertible two-by-two matrix constructed from two nonzero finite-field elements. -/
noncomputable def diagonalUnit (x y : GaloisField p n) (hx : x ≠ 0) (hy : y ≠ 0) : GL2' p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![x, 0; 0, y]
    (by rw [Matrix.det_fin_two_of]; simpa using mul_ne_zero hx hy)

/-- The underlying matrix of `diagonalUnit x y` has diagonal entries `x` and `y` and zero off-diagonal entries. -/
@[simp] lemma val_diagonalUnit (x y : GaloisField p n) (hx : x ≠ 0) (hy : y ≠ 0) :
    (diagonalUnit x y hx hy).val = !![x, 0; 0, y] := by
  simp [diagonalUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]


/-- In characteristic other than two, an element satisfying the fourth auxiliary predicate is conjugate to a diagonal unit with distinct nonzero diagonal entries. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem exists_isConj_diagonalUnit_of_auxiliaryFour (hp2 : p ≠ 2) {g : GL2' p n}
    (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g) :
    ∃ (x y : GaloisField p n) (hx : x ≠ 0) (hy : y ≠ 0),
      x ≠ y ∧ IsConj g (diagonalUnit x y hx hy) := by
  obtain ⟨hdne, hsq⟩ := hg
  rw [RepresentationTheory.FiniteFieldUnitClassDecomposition.entryDiscriminant_eq] at hdne hsq
  set a := g.val 0 0 with ha
  set b := g.val 0 1 with hb
  set c := g.val 1 0 with hc'
  set d := g.val 1 1 with hd
  obtain ⟨s, hs⟩ := hsq
  -- `s` is a square root of the discriminant; nonzero since `disc ≠ 0`.
  have hsne : s ≠ 0 := by
    intro h0; apply hdne; rw [hs, h0, mul_zero]
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h
    have hchar2 : CharP (GaloisField p n) 2 :=
      (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h
    have hp_char : CharP (GaloisField p n) p :=
      charP_of_injective_algebraMap (algebraMap (ZMod p) (GaloisField p n)).injective p
    exact hp2 (CharP.eq (GaloisField p n) hp_char hchar2)
  have h4 : (4 : GaloisField p n) ≠ 0 := by
    have : (4 : GaloisField p n) = 2 * 2 := by ring
    rw [this]; exact mul_ne_zero h2 h2
  -- The two eigenvalues `x = (tr+s)/2`, `y = (tr-s)/2`.
  set x := (a + d + s) / 2 with hxdef
  set y := (a + d - s) / 2 with hydef
  have hx2 : 2 * x = a + d + s := by rw [hxdef]; field_simp
  have hy2 : 2 * y = a + d - s := by rw [hydef]; field_simp
  clear_value x y
  have hxysub : x - y = s := by
    have h2s : 2 * (x - y) = 2 * s := by linear_combination hx2 - hy2
    exact mul_left_cancel₀ h2 h2s
  -- Both eigenvalues satisfy the characteristic equation.
  have hxroot : x * x - (a + d) * x + (a * d - b * c) = 0 := by
    apply mul_left_cancel₀ h4; rw [mul_zero]
    linear_combination -hs + (2 * x - (a + d) + s) * hx2
  have hyroot : y * y - (a + d) * y + (a * d - b * c) = 0 := by
    apply mul_left_cancel₀ h4; rw [mul_zero]
    linear_combination -hs + (2 * y - (a + d) - s) * hy2
  -- `det g = x·y`, so both eigenvalues are nonzero.
  have hxy : x * y = a * d - b * c := by
    apply mul_left_cancel₀ h4
    linear_combination hs + (2 * y) * hx2 + (a + d + s) * hy2
  have hdetv : Matrix.det g.val = a * d - b * c := by
    rw [Matrix.det_fin_two, ← ha, ← hb, ← hc', ← hd]
  have hdet_ne : Matrix.det g.val ≠ 0 := by
    intro h0
    have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [h0, zero_mul] at hdet1; exact one_ne_zero hdet1.symm
  have hxyne : x * y ≠ 0 := by rw [hxy, ← hdetv]; exact hdet_ne
  have hx0 : x ≠ 0 := fun h => hxyne (by rw [h, zero_mul])
  have hy0 : y ≠ 0 := fun h => hxyne (by rw [h, mul_zero])
  have hxney : x ≠ y := by
    intro h; apply hsne; rw [← hxysub, h, sub_self]
  by_cases hb0 : b = 0
  · by_cases hc0 : c = 0
    · -- Diagonal case `b = c = 0`: `g = diag(a,d)`; witnesses `a, d`.
      have hdetad : Matrix.det g.val = a * d := by rw [hdetv, hb0, zero_mul, sub_zero]
      have ha0 : a ≠ 0 := by
        intro h; apply hdet_ne; rw [hdetad, h, zero_mul]
      have hd0 : d ≠ 0 := by
        intro h; apply hdet_ne; rw [hdetad, h, mul_zero]
      have hane : a ≠ d := by
        intro h; apply hdne; rw [h, hb0]; ring
      refine ⟨a, d, ha0, hd0, hane, ?_⟩
      have heq : diagonalUnit a d ha0 hd0 = g := by
        apply Units.ext
        rw [val_diagonalUnit]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [← ha, ← hb, ← hc', ← hd, hb0, hc0]
      rw [heq]
    · -- `b = 0`, `c ≠ 0`: conjugator `!![x-d,y-d;c,c]`, det `c·s`.
      have hPdet : (!![x - d, y - d; c, c] :
          Matrix (Fin 2) (Fin 2) (GaloisField p n)).det ≠ 0 := by
        rw [Matrix.det_fin_two_of]
        have : (x - d) * c - (y - d) * c = c * s := by rw [← hxysub]; ring
        rw [this]; exact mul_ne_zero hc0 hsne
      refine ⟨x, y, hx0, hy0, hxney, ?_⟩
      refine isConj_of_val_mul_eq_mul_val
        (Matrix.GeneralLinearGroup.mkOfDetNeZero !![x - d, y - d; c, c] hPdet) ?_
      rw [mkOfDetNeZero_val, val_diagonalUnit]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hc', ← hd] <;>
        (try ring) <;> (try linear_combination -hxroot) ; (try linear_combination -hyroot)
  · -- `b ≠ 0`: conjugator `!![b,b;x-a,y-a]`, det `-b·s`.
    have hPdet : (!![b, b; x - a, y - a] :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      have : b * (y - a) - b * (x - a) = -(b * s) := by rw [← hxysub]; ring
      rw [this]; simpa using mul_ne_zero hb0 hsne
    refine ⟨x, y, hx0, hy0, hxney, ?_⟩
    refine isConj_of_val_mul_eq_mul_val
      (Matrix.GeneralLinearGroup.mkOfDetNeZero !![b, b; x - a, y - a] hPdet) ?_
    rw [mkOfDetNeZero_val, val_diagonalUnit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hc', ← hd] <;>
      (try ring) <;> (try linear_combination -hxroot) ; (try linear_combination -hyroot)


private lemma isConj_companion {g : GL2' p n} (hns : ¬ RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g)
    (t dt : GaloisField p n) (hdt : dt ≠ 0)
    (ht : t = g.val 0 0 + g.val 1 1) (hdtv : dt = Matrix.det g.val) :
    IsConj g (Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -dt; 1, t]
      (by rw [Matrix.det_fin_two_of]; simpa using hdt)) := by
  subst ht hdtv
  set a := g.val 0 0 with ha
  set b := g.val 0 1 with hb
  set c := g.val 1 0 with hc'
  set d := g.val 1 1 with hd
  -- The companion relation `g·P = P·companion` for `P = !![v0, a·v0+b·v1; v1, c·v0+d·v1]`.
  have key : ∀ v0 v1 : GaloisField p n,
      ∀ h : (!![v0, a * v0 + b * v1; v1, c * v0 + d * v1] :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)).det ≠ 0,
      IsConj g (Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(0 : GaloisField p n), -Matrix.det g.val; 1, a + d]
        (by rw [Matrix.det_fin_two_of]; simpa using detval_ne_zero g)) := by
    intro v0 v1 h
    refine isConj_of_val_mul_eq_mul_val
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![v0, a * v0 + b * v1; v1, c * v0 + d * v1] h) ?_
    simp only [mkOfDetNeZero_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
        ← ha, ← hb, ← hc', ← hd] <;> ring
  by_cases hc0 : c = 0
  · by_cases hb0 : b = 0
    · -- Diagonal non-scalar (`a ≠ d`): cyclic vector `(1,1)`.
      have hane : a ≠ d := fun h => hns ((RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries g).mpr ⟨hb0, hc0, h⟩)
      refine key 1 1 ?_
      have hval : (!![(1 : GaloisField p n), a * 1 + b * 1; 1, c * 1 + d * 1]).det = d - a := by
        rw [Matrix.det_fin_two_of, hb0, hc0]; ring
      rw [hval]; exact sub_ne_zero.mpr (Ne.symm hane)
    · -- `c = 0`, `b ≠ 0`: cyclic vector `(0,1)`.
      refine key 0 1 ?_
      have hval : (!![(0 : GaloisField p n), a * 0 + b * 1; 1, c * 0 + d * 1]).det = -b := by
        rw [Matrix.det_fin_two_of]; ring
      rw [hval]; exact neg_ne_zero.mpr hb0
  · -- `c ≠ 0`: cyclic vector `(1,0)`.
    refine key 1 0 ?_
    have hval : (!![(1 : GaloisField p n), a * 1 + b * 0; 0, c * 1 + d * 0]).det = c := by
      rw [Matrix.det_fin_two_of]; ring
    rw [hval]; exact hc0


private lemma isConj_of_nonscalar_tr_det {g h : GL2' p n}
    (hg : ¬ RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g) (hh : ¬ RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma h)
    (htr : g.val 0 0 + g.val 1 1 = h.val 0 0 + h.val 1 1)
    (hdet : Matrix.det g.val = Matrix.det h.val) : IsConj g h := by
  have h1 := isConj_companion hg (g.val 0 0 + g.val 1 1) (Matrix.det g.val)
    (detval_ne_zero g) rfl rfl
  have h2 := isConj_companion hh (g.val 0 0 + g.val 1 1) (Matrix.det g.val)
    (detval_ne_zero g) htr hdet
  exact h1.trans h2.symm


/-- An invertible two-by-two matrix constructed from a nonsquare parameter and a nonzero coefficient. -/
noncomputable def nonsquareExtensionUnit (ε x y : GaloisField p n) (hε : ¬ IsSquare ε) (hy : y ≠ 0) :
    GL2' p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![x, ε * y; y, x] (by
    rw [Matrix.det_fin_two_of]
    intro h0
    apply hε
    refine ⟨x * y⁻¹, ?_⟩
    field_simp
    linear_combination -h0)

/-- The underlying matrix of `nonsquareExtensionUnit ε x y` has rows `(x, ε * y)` and `(y, x)`. -/
@[simp] lemma val_nonsquareExtensionUnit (ε x y : GaloisField p n) (hε : ¬ IsSquare ε) (hy : y ≠ 0) :
    (nonsquareExtensionUnit ε x y hε hy).val = !![x, ε * y; y, x] := by
  simp [nonsquareExtensionUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]


/-- An element satisfying the first auxiliary predicate is conjugate to a `nonsquareExtensionUnit` for every nonsquare parameter, provided the characteristic is not two and the extension degree is nonzero. -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem exists_isConj_nonsquareExtensionUnit_of_auxiliaryOne (hp2 : p ≠ 2) (hn : n ≠ 0) {g : GL2' p n}
    (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha g) {ε : GaloisField p n} (hε : ¬ IsSquare ε) :
    ∃ (x y : GaloisField p n) (hy : y ≠ 0),
      IsConj g (nonsquareExtensionUnit ε x y hε hy) := by
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : DecidableEq (GaloisField p n) := Classical.decEq _
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h
    have hchar2 : CharP (GaloisField p n) 2 :=
      (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h
    have hp_char : CharP (GaloisField p n) p :=
      charP_of_injective_algebraMap (algebraMap (ZMod p) (GaloisField p n)).injective p
    exact hp2 (CharP.eq (GaloisField p n) hp_char hchar2)
  have h4 : (4 : GaloisField p n) ≠ 0 := by
    have : (4 : GaloisField p n) = 2 * 2 := by ring
    rw [this]; exact mul_ne_zero h2 h2
  set a := g.val 0 0 with ha
  set b := g.val 0 1 with hb
  set c := g.val 1 0 with hc'
  set d := g.val 1 1 with hd
  set D := RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.entryDiscriminant g with hDdef
  have hDsq : ¬ IsSquare D := hg
  have hDne : D ≠ 0 := fun h => hDsq (h ▸ ⟨0, by ring⟩)
  have hεne : ε ≠ 0 := fun h => hε (h ▸ ⟨0, by ring⟩)
  -- `disc · ε` is a square: product of two non-squares.
  have hχD : quadraticChar (GaloisField p n) D = -1 :=
    (quadraticChar_neg_one_iff_not_isSquare).mpr hDsq
  have hχε : quadraticChar (GaloisField p n) ε = -1 :=
    (quadraticChar_neg_one_iff_not_isSquare).mpr hε
  have hDεne : D * ε ≠ 0 := mul_ne_zero hDne hεne
  have hχDε : quadraticChar (GaloisField p n) (D * ε) = 1 := by
    rw [map_mul, hχD, hχε]; ring
  obtain ⟨z, hz⟩ := (quadraticChar_one_iff_isSquare hDεne).mp hχDε
  have hzne : z ≠ 0 := by
    intro h; apply hDεne; rw [hz, h, mul_zero]
  set x := (a + d) / 2 with hxdef
  set y := z * (2 * ε)⁻¹ with hydef
  have hx2 : 2 * x = a + d := by rw [hxdef]; field_simp
  have hy : y ≠ 0 := by
    rw [hydef]; exact mul_ne_zero hzne (inv_ne_zero (mul_ne_zero h2 hεne))
  -- `ε·y² = disc/4`, from `z² = disc·ε`.
  have hεyy : ε * y * y = D / 4 := by
    rw [hydef, eq_div_iff h4]
    field_simp
    linear_combination (-4 : GaloisField p n) * hz
  clear_value x y
  refine ⟨x, y, hy, ?_⟩
  -- `g` and the elliptic representative are non-scalar with equal trace and determinant.
  apply isConj_of_nonscalar_tr_det
  · exact fun hsc => RepresentationTheory.FiniteFieldUnitClassDecomposition.not_classPredicateAlpha_of_classPredicateGamma g hsc hg
  · intro hsc
    have hy0 : (nonsquareExtensionUnit ε x y hε hy).val 1 0 = 0 := ((RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries _).mp hsc).2.1
    rw [val_nonsquareExtensionUnit] at hy0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.empty_val'] at hy0
    exact hy hy0
  · rw [val_nonsquareExtensionUnit]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.empty_val', ← ha, ← hd]
    linear_combination -hx2
  · rw [val_nonsquareExtensionUnit, Matrix.det_fin_two, Matrix.det_fin_two_of, ← ha, ← hb, ← hc', ← hd]
    have hDval : D = (a - d) ^ 2 + 4 * b * c := by rw [hDdef, RepresentationTheory.FiniteFieldUnitClassDecomposition.entryDiscriminant_eq, ← ha, ← hb, ← hc', ← hd]
    have hx2' : a * d - b * c = x * x - D / 4 := by
      rw [hDval]; field_simp
      linear_combination -(2 * x + a + d) * hx2
    rw [hx2', ← hεyy]

end Representatives

end RepresentationTheory.FiniteGroups.GL2Conjugacy
