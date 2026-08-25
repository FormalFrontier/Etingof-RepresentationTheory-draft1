/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.FiniteFieldUnitClassDecomposition

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2' := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

section Predicates

variable {p n}

private abbrev GL2.mat (g : GL2' p n) : Matrix (Fin 2) (Fin 2) (GaloisField p n) := g

/-- Auxiliary finite-field value associated with a unit's matrix entries -/
noncomputable def Auxiliary.entryDiscriminant (g : GL2' p n) : GaloisField p n :=
  (GL2.mat g 0 0 - GL2.mat g 1 1) ^ 2 + 4 * GL2.mat g 0 1 * GL2.mat g 1 0

/-- Entry discriminant formula (g00 - g11)^2 + 4 * g01 * g10 -/
@[simp] lemma entryDiscriminant_eq (g : GL2' p n) :
    Auxiliary.entryDiscriminant g = (g.val 0 0 - g.val 1 1) ^ 2 + 4 * g.val 0 1 * g.val 1 0 := rfl

/-- Auxiliary gamma-class predicate on finite-field units -/
def Auxiliary.classPredicateGamma (g : GL2' p n) : Prop :=
  GL2.mat g 0 1 = 0 ∧ GL2.mat g 1 0 = 0 ∧ GL2.mat g 0 0 = GL2.mat g 1 1

/-- Auxiliary beta-class predicate on finite-field units -/
def Auxiliary.classPredicateBeta (g : GL2' p n) : Prop :=
  Auxiliary.entryDiscriminant g = 0 ∧ ¬Auxiliary.classPredicateGamma g

/-- Auxiliary delta-class predicate on finite-field units -/
def Auxiliary.classPredicateDelta (g : GL2' p n) : Prop :=
  Auxiliary.entryDiscriminant g ≠ 0 ∧ IsSquare (Auxiliary.entryDiscriminant g)

/-- Auxiliary alpha-class predicate on finite-field units -/
def Auxiliary.classPredicateAlpha (g : GL2' p n) : Prop :=
  ¬IsSquare (Auxiliary.entryDiscriminant g)

/-- Gamma-class characterization by zero off-diagonal entries and equal diagonal entries -/
@[simp] lemma classPredicateGamma_iff_matrixEntries (g : GL2' p n) :
    Auxiliary.classPredicateGamma g ↔ g.val 0 1 = 0 ∧ g.val 1 0 = 0 ∧ g.val 0 0 = g.val 1 1 := Iff.rfl

/-- Decidability of the auxiliary gamma-class predicate -/
noncomputable instance Auxiliary.decidableClassPredicateGamma [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2' p n) : Decidable (Auxiliary.classPredicateGamma g) := by
  unfold Auxiliary.classPredicateGamma; infer_instance

/-- Decidability of the auxiliary beta-class predicate -/
noncomputable instance Auxiliary.decidableClassPredicateBeta [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2' p n) : Decidable (Auxiliary.classPredicateBeta g) := by
  unfold Auxiliary.classPredicateBeta; infer_instance

/-- Decidability of the auxiliary delta-class predicate -/
noncomputable instance Auxiliary.decidableClassPredicateDelta [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2' p n) : Decidable (Auxiliary.classPredicateDelta g) := by
  unfold Auxiliary.classPredicateDelta; infer_instance

/-- Decidability of the auxiliary alpha-class predicate -/
noncomputable instance Auxiliary.decidableClassPredicateAlpha [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2' p n) : Decidable (Auxiliary.classPredicateAlpha g) := by
  unfold Auxiliary.classPredicateAlpha; infer_instance

end Predicates

section Partition

variable {p n}

/-- Vanishing entry discriminant for the gamma class -/
lemma entryDiscriminant_eq_zero_of_classPredicateGamma (g : GL2' p n) (h : Auxiliary.classPredicateGamma g) :
    Auxiliary.entryDiscriminant g = 0 := by
  obtain ⟨h01, h10, h00⟩ := h
  unfold Auxiliary.entryDiscriminant; rw [h01, h10, h00]; ring

/-- Exhaustive four-way auxiliary-class decomposition -/
theorem classPredicates_exhaustive (g : GL2' p n) :
    Auxiliary.classPredicateGamma g ∨ Auxiliary.classPredicateBeta g ∨
    Auxiliary.classPredicateDelta g ∨ Auxiliary.classPredicateAlpha g := by
  by_cases hscalar : Auxiliary.classPredicateGamma g
  · exact Or.inl hscalar
  · by_cases hsq : IsSquare (Auxiliary.entryDiscriminant g)
    ·
      by_cases hdisc : Auxiliary.entryDiscriminant g = 0
      ·
        exact Or.inr (Or.inl ⟨hdisc, hscalar⟩)
      ·
        exact Or.inr (Or.inr (Or.inl ⟨hdisc, hsq⟩))
    ·
      exact Or.inr (Or.inr (Or.inr hsq))

/-- Exclusion of the beta class by the gamma class -/
theorem not_classPredicateBeta_of_classPredicateGamma (g : GL2' p n) :
    Auxiliary.classPredicateGamma g → ¬Auxiliary.classPredicateBeta g := by
  intro hs hp; exact hp.2 hs

/-- Exclusion of the delta class by the gamma class -/
theorem not_classPredicateDelta_of_classPredicateGamma (g : GL2' p n) :
    Auxiliary.classPredicateGamma g → ¬Auxiliary.classPredicateDelta g := by
  intro hs hss
  exact hss.1 (entryDiscriminant_eq_zero_of_classPredicateGamma g hs)

/-- Exclusion of the alpha class by the gamma class -/
theorem not_classPredicateAlpha_of_classPredicateGamma (g : GL2' p n) :
    Auxiliary.classPredicateGamma g → ¬Auxiliary.classPredicateAlpha g := by
  intro hs he
  apply he
  rw [entryDiscriminant_eq_zero_of_classPredicateGamma g hs]
  exact IsSquare.zero

/-- Exclusion of the delta class by the beta class -/
theorem not_classPredicateDelta_of_classPredicateBeta (g : GL2' p n) :
    Auxiliary.classPredicateBeta g → ¬Auxiliary.classPredicateDelta g := by
  intro hp hss; exact hss.1 hp.1

/-- Exclusion of the alpha class by the beta class -/
theorem not_classPredicateAlpha_of_classPredicateBeta (g : GL2' p n) :
    Auxiliary.classPredicateBeta g → ¬Auxiliary.classPredicateAlpha g := by
  intro hp he
  apply he
  rw [hp.1]
  exact IsSquare.zero

/-- Exclusion of the alpha class by the delta class -/
theorem not_classPredicateAlpha_of_classPredicateDelta (g : GL2' p n) :
    Auxiliary.classPredicateDelta g → ¬Auxiliary.classPredicateAlpha g := by
  intro hss he; exact he hss.2

/-- Mutual exclusivity of the four auxiliary class predicates -/
theorem classPredicates_mutuallyExclusive (g : GL2' p n) :
    (Auxiliary.classPredicateGamma g → ¬Auxiliary.classPredicateBeta g ∧ ¬Auxiliary.classPredicateDelta g ∧ ¬Auxiliary.classPredicateAlpha g) ∧
    (Auxiliary.classPredicateBeta g → ¬Auxiliary.classPredicateGamma g ∧ ¬Auxiliary.classPredicateDelta g ∧ ¬Auxiliary.classPredicateAlpha g) ∧
    (Auxiliary.classPredicateDelta g → ¬Auxiliary.classPredicateGamma g ∧ ¬Auxiliary.classPredicateBeta g ∧ ¬Auxiliary.classPredicateAlpha g) ∧
    (Auxiliary.classPredicateAlpha g → ¬Auxiliary.classPredicateGamma g ∧ ¬Auxiliary.classPredicateBeta g ∧ ¬Auxiliary.classPredicateDelta g) :=
  ⟨fun h => ⟨not_classPredicateBeta_of_classPredicateGamma g h,
             not_classPredicateDelta_of_classPredicateGamma g h,
             not_classPredicateAlpha_of_classPredicateGamma g h⟩,
   fun h => ⟨h.2, not_classPredicateDelta_of_classPredicateBeta g h,
             not_classPredicateAlpha_of_classPredicateBeta g h⟩,
   fun h => ⟨fun hs => not_classPredicateDelta_of_classPredicateGamma g hs h,
             fun hp => not_classPredicateDelta_of_classPredicateBeta g hp h,
             not_classPredicateAlpha_of_classPredicateDelta g h⟩,
   fun h => ⟨fun hs => not_classPredicateAlpha_of_classPredicateGamma g hs h,
             fun hp => not_classPredicateAlpha_of_classPredicateBeta g hp h,
             fun hss => not_classPredicateAlpha_of_classPredicateDelta g hss h⟩⟩

/-- Exactly-one form of the four-way auxiliary-class decomposition -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := primary)]
theorem classPredicates_exactlyOne (g : GL2' p n) :
    (Auxiliary.classPredicateGamma g ∧ ¬Auxiliary.classPredicateBeta g ∧ ¬Auxiliary.classPredicateDelta g ∧ ¬Auxiliary.classPredicateAlpha g) ∨
    (Auxiliary.classPredicateBeta g ∧ ¬Auxiliary.classPredicateGamma g ∧ ¬Auxiliary.classPredicateDelta g ∧ ¬Auxiliary.classPredicateAlpha g) ∨
    (Auxiliary.classPredicateDelta g ∧ ¬Auxiliary.classPredicateGamma g ∧ ¬Auxiliary.classPredicateBeta g ∧ ¬Auxiliary.classPredicateAlpha g) ∨
    (Auxiliary.classPredicateAlpha g ∧ ¬Auxiliary.classPredicateGamma g ∧ ¬Auxiliary.classPredicateBeta g ∧ ¬Auxiliary.classPredicateDelta g) := by
  rcases classPredicates_exhaustive g with h | h | h | h
  · exact Or.inl ⟨h, (classPredicates_mutuallyExclusive g).1 h⟩
  · exact Or.inr (Or.inl ⟨h, (classPredicates_mutuallyExclusive g).2.1 h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, (classPredicates_mutuallyExclusive g).2.2.1 h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h, (classPredicates_mutuallyExclusive g).2.2.2 h⟩))

end Partition

section SumDecomposition

variable {p n}

/-- Membership in at least one of the four auxiliary class filters -/
theorem mem_one_classPredicateFilter [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2' p n)] (g : GL2' p n) :
    g ∈ Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateGamma g) ∨
    g ∈ Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateBeta g) ∨
    g ∈ Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateDelta g) ∨
    g ∈ Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateAlpha g) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact classPredicates_exhaustive g

/-- Finite sum decomposition across the four auxiliary class filters -/
theorem sum_eq_sum_classPredicateFilters [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2' p n)] (f : GL2' p n → ℂ) :
    ∑ g : GL2' p n, f g =
    (∑ g ∈ Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateGamma g), f g) +
    (∑ g ∈ Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateBeta g), f g) +
    (∑ g ∈ Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateDelta g), f g) +
    (∑ g ∈ Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateAlpha g), f g) := by

  set S := Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateGamma g)
  set P := Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateBeta g)
  set SS := Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateDelta g)
  set E := Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateAlpha g)
  have hSP : Disjoint S P := Finset.disjoint_filter.mpr
    fun g _ hs hp => (not_classPredicateBeta_of_classPredicateGamma g hs) hp
  have hSSS : Disjoint S SS := Finset.disjoint_filter.mpr
    fun g _ hs hss => (not_classPredicateDelta_of_classPredicateGamma g hs) hss
  have hSE : Disjoint S E := Finset.disjoint_filter.mpr
    fun g _ hs he => (not_classPredicateAlpha_of_classPredicateGamma g hs) he
  have hPSS : Disjoint P SS := Finset.disjoint_filter.mpr
    fun g _ hp hss => (not_classPredicateDelta_of_classPredicateBeta g hp) hss
  have hPE : Disjoint P E := Finset.disjoint_filter.mpr
    fun g _ hp he => (not_classPredicateAlpha_of_classPredicateBeta g hp) he
  have hSSE : Disjoint SS E := Finset.disjoint_filter.mpr
    fun g _ hss he => (not_classPredicateAlpha_of_classPredicateDelta g hss) he

  have hSPuSS : Disjoint (S ∪ P) SS :=
    disjoint_sup_left.mpr ⟨hSSS, hPSS⟩
  have hSPSSuE : Disjoint (S ∪ P ∪ SS) E :=
    disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨hSE, hPE⟩, hSSE⟩

  have hunion : Finset.univ = S ∪ P ∪ SS ∪ E := by
    ext g; simp only [S, P, SS, E]
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    rcases classPredicates_exhaustive g with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  conv_lhs => rw [hunion]
  rw [Finset.sum_union hSPSSuE, Finset.sum_union hSPuSS, Finset.sum_union hSP]

end SumDecomposition

section Cardinalities

variable {p n}

/-- Gamma-class cardinality q - 1 for q = |GaloisField p n| -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := supporting)]
theorem card_classPredicateGamma [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateGamma g)).card =
    Fintype.card (GaloisField p n) - 1 := by


  let scalarMat : (GaloisField p n)ˣ → GL2' p n := fun x =>
    ⟨Matrix.diagonal (fun _ => (x : GaloisField p n)),
     Matrix.diagonal (fun _ => (↑x⁻¹ : GaloisField p n)),
     by rw [Matrix.diagonal_mul_diagonal]; simp [Matrix.diagonal_one],
     by rw [Matrix.diagonal_mul_diagonal]; simp [Matrix.diagonal_one]⟩

  have scalarMat_inj : Function.Injective scalarMat := by
    intro a b hab
    have h := congr_arg (fun g => (g : GL2' p n).val 0 0) hab
    simp only [scalarMat, Matrix.diagonal_apply, ite_true] at h
    exact Units.ext h

  have scalarMat_image : (Finset.univ.image scalarMat) =
      Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateGamma g) := by
    ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨?_, ?_, ?_⟩ <;> simp [GL2.mat, scalarMat, Matrix.diagonal]
    · intro hg
      obtain ⟨h01, h10, h00⟩ := hg

      have h00_ne : g.val 0 0 ≠ 0 := by
        intro h0
        have hdet : Matrix.det g.val = 0 := by
          simp only [GL2.mat] at h01 h10 h00
          rw [Matrix.det_fin_two, h01, h10, ← h00, h0]; ring
        have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
          rw [← Matrix.det_mul, hmul, Matrix.det_one]
        rw [hdet, zero_mul] at hdet1; exact one_ne_zero hdet1.symm
      refine ⟨Units.mk0 (g.val 0 0) h00_ne, Units.ext (Matrix.ext fun i j => ?_)⟩
      fin_cases i <;> fin_cases j <;>
        simp [scalarMat, h01, h10, h00]

  rw [← scalarMat_image, Finset.card_image_of_injective _ scalarMat_inj,
      Finset.card_univ, Fintype.card_units]

private lemma GaloisField.two_ne_zero (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (2 : GaloisField p n) ≠ 0 := by
  intro h
  apply hp2
  have h2' : (Nat.cast 2 : GaloisField p n) = 0 := h
  rw [CharP.cast_eq_zero_iff (GaloisField p n) p 2] at h2'
  exact Nat.le_antisymm (Nat.le_of_dvd (by omega) h2') hp.out.two_le

private lemma GaloisField.four_ne_zero (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (4 : GaloisField p n) ≠ 0 := by
  intro h
  have h2 := GaloisField.two_ne_zero hp2 hn
  apply h2
  have : (4 : GaloisField p n) = 2 * 2 := by ring
  rw [this] at h
  exact (mul_self_eq_zero.mp h)

private lemma GL2.disc_eq_zero_of_g01_zero {g : GL2' p n}
    (hdisc : Auxiliary.entryDiscriminant g = 0) (h01 : g.val 0 1 = 0) :
    g.val 0 0 = g.val 1 1 := by
  simp only [Auxiliary.entryDiscriminant, GL2.mat] at hdisc
  rw [h01] at hdisc
  simp only [mul_zero, zero_mul, add_zero] at hdisc
  rwa [sq_eq_zero_iff, sub_eq_zero] at hdisc

private lemma GL2.g10_of_disc_zero_g01_ne {g : GL2' p n}
    (hp2 : p ≠ 2) (hn : n ≠ 0)
    (hdisc : Auxiliary.entryDiscriminant g = 0) (h01 : g.val 0 1 ≠ 0) :
    g.val 1 0 = -((g.val 0 0 - g.val 1 1) ^ 2) / (4 * g.val 0 1) := by
  simp only [Auxiliary.entryDiscriminant, GL2.mat] at hdisc
  have h4 : (4 : GaloisField p n) ≠ 0 := GaloisField.four_ne_zero hp2 hn
  have h4c : (4 * g.val 0 1) ≠ 0 := mul_ne_zero h4 h01
  rw [eq_div_iff h4c]
  linear_combination hdisc

private lemma GL2.det_of_disc_zero_g01_ne {g : GL2' p n}
    (hp2 : p ≠ 2) (hn : n ≠ 0)
    (hdisc : Auxiliary.entryDiscriminant g = 0) (h01 : g.val 0 1 ≠ 0) :
    Matrix.det g.val = ((g.val 0 0 + g.val 1 1) / 2) ^ 2 := by
  have h2 : (2 : GaloisField p n) ≠ 0 := GaloisField.two_ne_zero hp2 hn
  have h4 : (4 : GaloisField p n) ≠ 0 := GaloisField.four_ne_zero hp2 hn
  have hg10 := GL2.g10_of_disc_zero_g01_ne hp2 hn hdisc h01
  rw [Matrix.det_fin_two]
  rw [hg10]
  field_simp
  ring

private lemma GL2.card_disc_zero_g01_zero (hp2 : p ≠ 2) (hn : n ≠ 0)
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2' p n)] :
    (Finset.univ.filter (fun g : GL2' p n =>
      Auxiliary.entryDiscriminant g = 0 ∧ g.val 0 1 = 0)).card =
    (Fintype.card (GaloisField p n) - 1) * Fintype.card (GaloisField p n) := by

  let F := GaloisField p n

  have det_ne_zero : ∀ g : GL2' p n, Matrix.det g.val ≠ 0 := by
    intro g hdet
    have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [hdet, zero_mul] at hdet1; exact one_ne_zero hdet1.symm

  let toMat : Fˣ → F → Matrix (Fin 2) (Fin 2) F := fun a b =>
    !![↑a, 0; b, ↑a]
  have toMat_det : ∀ (a : Fˣ) (b : F), Matrix.det (toMat a b) ≠ 0 := by
    intro a b; simp [toMat, Matrix.det_fin_two]
  let toGL : Fˣ × F → GL2' p n := fun ⟨a, b⟩ =>
    Matrix.GeneralLinearGroup.mkOfDetNeZero (toMat a b) (toMat_det a b)

  have toGL_val : ∀ (a : Fˣ) (b : F), (toGL ⟨a, b⟩).val = toMat a b := by
    intro a b; simp [toGL]
  have toGL_disc : ∀ (a : Fˣ) (b : F), Auxiliary.entryDiscriminant (toGL ⟨a, b⟩) = 0 := by
    intro a b
    simp only [Auxiliary.entryDiscriminant, GL2.mat, toGL_val, toMat]; simp
  have toGL_01 : ∀ (a : Fˣ) (b : F), (toGL ⟨a, b⟩).val 0 1 = 0 := by
    intro a b; simp [toGL_val, toMat]

  have toGL_inj : Function.Injective toGL := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    have hval : toMat a₁ b₁ = toMat a₂ b₂ := by
      have := congr_arg Units.val h
      rwa [toGL_val, toGL_val] at this
    have ha : (a₁ : F) = (a₂ : F) := by
      have := congr_fun (congr_fun hval 0) 0
      simp [toMat] at this; exact this
    have hb : b₁ = b₂ := by
      have := congr_fun (congr_fun hval 1) 0
      simp [toMat] at this; exact this
    exact Prod.ext (Units.ext ha) hb

  have toGL_surj : ∀ g ∈ Finset.univ.filter (fun g : GL2' p n =>
      Auxiliary.entryDiscriminant g = 0 ∧ g.val 0 1 = 0), ∃ ab : Fˣ × F, toGL ab = g := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hdisc, h01⟩ := hg
    have h00_eq : g.val 0 0 = g.val 1 1 := GL2.disc_eq_zero_of_g01_zero hdisc h01
    have h00_ne : g.val 0 0 ≠ 0 := by
      intro h0
      apply det_ne_zero g
      rw [Matrix.det_fin_two, h01, ← h00_eq, h0]; ring
    refine ⟨⟨Units.mk0 (g.val 0 0) h00_ne, g.val 1 0⟩,
      Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
    simp only [toGL_val, toMat]
    fin_cases i <;> fin_cases j <;> simp [h01, h00_eq]

  have himage : (Finset.univ.image toGL) =
      Finset.univ.filter (fun g : GL2' p n => Auxiliary.entryDiscriminant g = 0 ∧ g.val 0 1 = 0) := by
    ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩; exact ⟨toGL_disc a b, toGL_01 a b⟩
    · intro hg
      exact toGL_surj g (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hg)
  rw [← himage, Finset.card_image_of_injective _ toGL_inj, Finset.card_univ,
      Fintype.card_prod, Fintype.card_units]

private lemma GL2.card_disc_zero_g01_ne (hp2 : p ≠ 2) (hn : n ≠ 0)
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2' p n)] :
    (Finset.univ.filter (fun g : GL2' p n =>
      Auxiliary.entryDiscriminant g = 0 ∧ g.val 0 1 ≠ 0)).card =
    (Fintype.card (GaloisField p n) - 1) ^ 2 * Fintype.card (GaloisField p n) := by




  let F := GaloisField p n
  have h2 : (2 : F) ≠ 0 := GaloisField.two_ne_zero hp2 hn
  have h4 : (4 : F) ≠ 0 := GaloisField.four_ne_zero hp2 hn

  have det_ne_zero : ∀ g : GL2' p n, Matrix.det g.val ≠ 0 := by
    intro g hdet
    have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [hdet, zero_mul] at hdet1; exact one_ne_zero hdet1.symm
  have cancel_inv : ∀ (a b : F), a ≠ 0 → a * (b * a⁻¹) = b := by
    intros a b ha; rw [← mul_assoc, mul_comm a b, mul_assoc, mul_inv_cancel₀ ha, mul_one]

  let toMat : Fˣ → Fˣ → F → Matrix (Fin 2) (Fin 2) F := fun c s d =>
    !![↑s + d, ↑c; -(d ^ 2 * (↑c : F)⁻¹), ↑s - d]
  have toMat_det : ∀ (c : Fˣ) (s : Fˣ) (d : F), Matrix.det (toMat c s d) ≠ 0 := by
    intro c s d
    have hc_ne : (↑c : F) ≠ 0 := c.ne_zero
    have : (toMat c s d).det = (↑s : F) ^ 2 := by

      simp only [toMat, Matrix.det_fin_two]; simp

      rw [mul_neg, sub_neg_eq_add, cancel_inv _ _ hc_ne]; ring
    rw [this]; exact pow_ne_zero 2 s.ne_zero
  let toGL : Fˣ × Fˣ × F → GL2' p n := fun ⟨c, s, d⟩ =>
    Matrix.GeneralLinearGroup.mkOfDetNeZero (toMat c s d) (toMat_det c s d)
  have toGL_val : ∀ (c : Fˣ) (s : Fˣ) (d : F), (toGL ⟨c, s, d⟩).val = toMat c s d := by
    intro c s d; simp [toGL]

  have toGL_disc : ∀ (c : Fˣ) (s : Fˣ) (d : F), Auxiliary.entryDiscriminant (toGL ⟨c, s, d⟩) = 0 := by
    intro c s d
    have hc_ne : (↑c : F) ≠ 0 := c.ne_zero
    simp only [Auxiliary.entryDiscriminant, GL2.mat, toGL_val]

    simp [toMat]

    rw [show 4 * (↑c : F) * (d ^ 2 * (↑c : F)⁻¹) =
      4 * ((↑c : F) * (d ^ 2 * (↑c : F)⁻¹)) from by ring,
      cancel_inv _ _ hc_ne]; ring

  have toGL_01 : ∀ (c : Fˣ) (s : Fˣ) (d : F), (toGL ⟨c, s, d⟩).val 0 1 ≠ 0 := by
    intro c s d
    simp [toGL_val, toMat, c.ne_zero]

  have toGL_inj : Function.Injective toGL := by
    intro ⟨c₁, s₁, d₁⟩ ⟨c₂, s₂, d₂⟩ h
    have hval : toMat c₁ s₁ d₁ = toMat c₂ s₂ d₂ := by
      have := congr_arg Units.val h; rwa [toGL_val, toGL_val] at this
    have hc : (c₁ : F) = (c₂ : F) := by
      have := congr_fun (congr_fun hval 0) 1
      simp [toMat] at this; exact this
    have hsd_sum : (↑s₁ : F) + d₁ = ↑s₂ + d₂ := by
      have := congr_fun (congr_fun hval 0) 0
      simp [toMat] at this; exact this
    have hsd_diff : (↑s₁ : F) - d₁ = ↑s₂ - d₂ := by
      have := congr_fun (congr_fun hval 1) 1
      simp [toMat] at this; exact this
    have hs : (s₁ : F) = (s₂ : F) := by
      have h_sum := hsd_sum; have h_diff := hsd_diff
      have : 2 * (↑s₁ : F) = 2 * ↑s₂ := by linear_combination h_sum + h_diff
      exact mul_left_cancel₀ h2 this
    have hd : d₁ = d₂ := by
      have h1 := hsd_sum
      rw [hs] at h1
      exact add_left_cancel h1
    exact Prod.ext (Units.ext hc) (Prod.ext (Units.ext hs) hd)

  have toGL_surj : ∀ g ∈ Finset.univ.filter (fun g : GL2' p n =>
      Auxiliary.entryDiscriminant g = 0 ∧ g.val 0 1 ≠ 0), ∃ csd : Fˣ × Fˣ × F, toGL csd = g := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hdisc, h01⟩ := hg


    set c := Units.mk0 (g.val 0 1) h01
    set s_val := (g.val 0 0 + g.val 1 1) / 2
    set d_val := (g.val 0 0 - g.val 1 1) / 2

    have hdet := det_ne_zero g
    have hg10 := GL2.g10_of_disc_zero_g01_ne hp2 hn hdisc h01
    have hdet_eq := GL2.det_of_disc_zero_g01_ne hp2 hn hdisc h01
    have hs_ne : s_val ≠ 0 := by
      intro h0
      apply hdet
      rw [hdet_eq]; change s_val ^ 2 = 0; rw [h0, sq, zero_mul]
    set s := Units.mk0 s_val hs_ne

    have h00 : g.val 0 0 = s_val + d_val := by
      change g.val 0 0 = (g.val 0 0 + g.val 1 1) / 2 + (g.val 0 0 - g.val 1 1) / 2
      field_simp; ring
    have h11 : g.val 1 1 = s_val - d_val := by
      change g.val 1 1 = (g.val 0 0 + g.val 1 1) / 2 - (g.val 0 0 - g.val 1 1) / 2
      field_simp; ring

    have h10 : g.val 1 0 = -(d_val ^ 2 * (g.val 0 1)⁻¹) := by
      rw [hg10]



      simp only [d_val]
      field_simp; ring
    refine ⟨⟨c, s, d_val⟩, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
    simp only [toGL_val, toMat]
    fin_cases i <;> fin_cases j <;> simp [s, s_val, d_val, c]
    · exact h00.symm
    · exact h10.symm
    · exact h11.symm

  have himage : (Finset.univ.image toGL) =
      Finset.univ.filter (fun g : GL2' p n => Auxiliary.entryDiscriminant g = 0 ∧ g.val 0 1 ≠ 0) := by
    ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨⟨c, s, d⟩, rfl⟩; exact ⟨toGL_disc c s d, toGL_01 c s d⟩
    · intro hg
      exact toGL_surj g (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hg)
  rw [← himage, Finset.card_image_of_injective _ toGL_inj, Finset.card_univ,
      Fintype.card_prod, Fintype.card_prod]


  change Fintype.card (GaloisField p n)ˣ * (Fintype.card (GaloisField p n)ˣ *
    Fintype.card (GaloisField p n)) =
    (Fintype.card (GaloisField p n) - 1) ^ 2 * Fintype.card (GaloisField p n)
  rw [Fintype.card_units]
  set q := Fintype.card (GaloisField p n)
  have hq1 : 1 ≤ q := Fintype.card_pos

  zify [hq1]; ring

private lemma GL2.card_disc_eq_zero (hp2 : p ≠ 2) (hn : n ≠ 0)
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2' p n)] :
    (Finset.univ.filter (fun g : GL2' p n => Auxiliary.entryDiscriminant g = 0)).card =
    (Fintype.card (GaloisField p n) - 1) * Fintype.card (GaloisField p n) ^ 2 := by

  have hsplit : Finset.univ.filter (fun g : GL2' p n => Auxiliary.entryDiscriminant g = 0) =
      Finset.univ.filter (fun g : GL2' p n => Auxiliary.entryDiscriminant g = 0 ∧ g.val 0 1 = 0) ∪
      Finset.univ.filter (fun g : GL2' p n => Auxiliary.entryDiscriminant g = 0 ∧ g.val 0 1 ≠ 0) := by
    ext g; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · intro h; by_cases h01 : g.val 0 1 = 0
      · exact Or.inl ⟨h, h01⟩
      · exact Or.inr ⟨h, h01⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint
      (Finset.univ.filter (fun g : GL2' p n => Auxiliary.entryDiscriminant g = 0 ∧ g.val 0 1 = 0))
      (Finset.univ.filter (fun g : GL2' p n => Auxiliary.entryDiscriminant g = 0 ∧ g.val 0 1 ≠ 0)) := by
    apply Finset.disjoint_filter.mpr
    intro g _ ⟨_, h0⟩ ⟨_, h1⟩; exact h1 h0
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  rw [GL2.card_disc_zero_g01_zero hp2 hn, GL2.card_disc_zero_g01_ne hp2 hn]
  set q := Fintype.card (GaloisField p n)
  have hq1 : 1 ≤ q := Fintype.card_pos

  zify [hq1]; ring

/-- Beta-class cardinality (q - 1) * (q^2 - 1) for q = |GaloisField p n| -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := supporting)]
theorem card_classPredicateBeta [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateBeta g)).card =
    (Fintype.card (GaloisField p n) - 1) *
    (Fintype.card (GaloisField p n) ^ 2 - 1) := by

  have h_sub : Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateGamma g) ⊆
      Finset.univ.filter (fun g : GL2' p n => Auxiliary.entryDiscriminant g = 0) := by
    intro g; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact entryDiscriminant_eq_zero_of_classPredicateGamma g
  have h_eq : Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateBeta g) =
      Finset.univ.filter (fun g => Auxiliary.entryDiscriminant g = 0) \
      Finset.univ.filter (fun g => Auxiliary.classPredicateGamma g) := by
    ext g; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · exact fun ⟨h1, h2⟩ => ⟨h1, h2⟩
    · exact fun ⟨h1, h2⟩ => ⟨h1, h2⟩
  rw [h_eq]
  have h_card := Finset.card_sdiff_add_card_eq_card h_sub
  have h_disc := GL2.card_disc_eq_zero hp2 hn
  have h_scalar := card_classPredicateGamma (p := p) hn
  set q := Fintype.card (GaloisField p n)

  have hq1 : 1 ≤ q := Fintype.card_pos
  suffices h : (q - 1) * (q ^ 2 - 1) + (q - 1) = (q - 1) * q ^ 2 by omega
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  zify [hq1, hq2]; ring

private lemma GL2.isSquare_disc_of_g01_zero {g : GL2' p n} (h : g.val 0 1 = 0) :
    IsSquare (Auxiliary.entryDiscriminant g) := by
  simp only [Auxiliary.entryDiscriminant, GL2.mat, h, mul_zero, zero_mul, add_zero]
  exact ⟨g.val 0 0 - g.val 1 1, by ring⟩

private lemma GL2.card_partition [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] :
    (Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateGamma g)).card +
    (Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateBeta g)).card +
    (Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateDelta g)).card +
    (Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateAlpha g)).card =
    Fintype.card (GL2' p n) := by
  rw [← Finset.card_univ]
  set S := Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateGamma g)
  set P := Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateBeta g)
  set SS := Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateDelta g)
  set E := Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateAlpha g)

  have hSP : Disjoint S P := Finset.disjoint_filter.mpr
    fun g _ hs hp => (not_classPredicateBeta_of_classPredicateGamma g hs) hp
  have hSSS : Disjoint S SS := Finset.disjoint_filter.mpr
    fun g _ hs hss => (not_classPredicateDelta_of_classPredicateGamma g hs) hss
  have hSE : Disjoint S E := Finset.disjoint_filter.mpr
    fun g _ hs he => (not_classPredicateAlpha_of_classPredicateGamma g hs) he
  have hPSS : Disjoint P SS := Finset.disjoint_filter.mpr
    fun g _ hp hss => (not_classPredicateDelta_of_classPredicateBeta g hp) hss
  have hPE : Disjoint P E := Finset.disjoint_filter.mpr
    fun g _ hp he => (not_classPredicateAlpha_of_classPredicateBeta g hp) he
  have hSSE : Disjoint SS E := Finset.disjoint_filter.mpr
    fun g _ hss he => (not_classPredicateAlpha_of_classPredicateDelta g hss) he
  have hSPuSS : Disjoint (S ∪ P) SS := disjoint_sup_left.mpr ⟨hSSS, hPSS⟩
  have hSPSSuE : Disjoint (S ∪ P ∪ SS) E :=
    disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨hSE, hPE⟩, hSSE⟩

  have hunion : Finset.univ = S ∪ P ∪ SS ∪ E := by
    ext g; simp only [S, P, SS, E]
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    rcases classPredicates_exhaustive g with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  rw [hunion, Finset.card_union_of_disjoint hSPSSuE,
      Finset.card_union_of_disjoint hSPuSS,
      Finset.card_union_of_disjoint hSP]

private lemma GL2.card_GL2
    [Fintype (GaloisField p n)] [Fintype (GL2' p n)] :
    Fintype.card (GL2' p n) =
    (Fintype.card (GaloisField p n) ^ 2 - 1) *
    (Fintype.card (GaloisField p n) ^ 2 - Fintype.card (GaloisField p n)) := by
  have h := Matrix.card_GL_field (𝔽 := GaloisField p n) 2
  rw [Nat.card_eq_fintype_card] at h
  rw [h]
  simp [Fin.prod_univ_two, pow_zero, pow_one]

private lemma GaloisField.card_ge_three (hp2 : p ≠ 2) (hn : n ≠ 0)
    [Fintype (GaloisField p n)] :
    3 ≤ Fintype.card (GaloisField p n) := by
  rw [Fintype.card_eq_nat_card, GaloisField.card p n hn]
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le; omega
  calc p ^ n ≥ p ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    _ = p := pow_one p
    _ ≥ 3 := hp3

private lemma GaloisField.ringChar_eq_prime :
    ringChar (GaloisField p n) = p := ringChar.eq (GaloisField p n) p

private lemma GaloisField.ringChar_ne_two (hp2 : p ≠ 2) :
    ringChar (GaloisField p n) ≠ 2 := by
  rw [GaloisField.ringChar_eq_prime]; exact hp2

private lemma two_mul_card_nonsquare (hp2 : p ≠ 2) (hn : n ≠ 0)
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] :
    2 * (Finset.univ.filter (fun a : GaloisField p n => ¬IsSquare a)).card =
    Fintype.card (GaloisField p n) - 1 := by
  have hF : ringChar (GaloisField p n) ≠ 2 := GaloisField.ringChar_ne_two hp2

  set NSq := Finset.univ.filter (fun a : GaloisField p n => ¬IsSquare a) with NSq_def
  let NZSq := Finset.univ.filter (fun a : GaloisField p n => a ≠ 0 ∧ IsSquare a)

  have hunion : NZSq ∪ NSq = Finset.univ.filter (fun a : GaloisField p n => a ≠ 0) := by
    ext a; simp only [NZSq, NSq, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨ha, _⟩ | hna)
      · exact ha
      · exact fun h => hna (h ▸ ⟨0, by ring⟩)
    · intro ha; by_cases hsq : IsSquare a
      · exact Or.inl ⟨ha, hsq⟩
      · exact Or.inr hsq
  have hdisj : Disjoint NZSq NSq :=
    Finset.disjoint_filter.mpr (fun a _ ⟨_, hsq⟩ hnsq => hnsq hsq)
  have hsum : NZSq.card + NSq.card = Fintype.card (GaloisField p n) - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.filter_ne']
    simp

  have hχ_sum := quadraticChar_sum_zero hF

  have hχ_NZSq : ∀ a ∈ NZSq, quadraticChar (GaloisField p n) a = 1 := by
    intro a ha
    simp only [NZSq, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact (quadraticChar_one_iff_isSquare ha.1).mpr ha.2
  have hχ_NSq : ∀ a ∈ NSq, quadraticChar (GaloisField p n) a = -1 := by
    intro a ha
    simp only [NSq, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact quadraticChar_neg_one_iff_not_isSquare.mpr ha

  have hpart : Finset.univ = ({0} : Finset (GaloisField p n)) ∪ NZSq ∪ NSq := by
    ext a; simp only [Finset.mem_univ, true_iff, Finset.mem_union, Finset.mem_singleton,
      NZSq, NSq, Finset.mem_filter, true_and]
    by_cases ha : a = 0
    · exact Or.inl (Or.inl ha)
    · by_cases hsq : IsSquare a
      · exact Or.inl (Or.inr ⟨ha, hsq⟩)
      · exact Or.inr hsq
  have hdisj2 : Disjoint ({0} : Finset (GaloisField p n)) NZSq := by
    simp only [Finset.disjoint_left, Finset.mem_singleton, NZSq, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro a ha; rw [ha]; exact fun ⟨h, _⟩ => h rfl
  have hdisj3 : Disjoint (({0} : Finset (GaloisField p n)) ∪ NZSq) NSq :=
    disjoint_sup_left.mpr ⟨by
      simp only [Finset.disjoint_left, Finset.mem_singleton, NSq, Finset.mem_filter,
        Finset.mem_univ, true_and]
      intro a ha hna; rw [ha] at hna; exact hna ⟨0, by ring⟩, hdisj⟩
  rw [hpart, Finset.sum_union hdisj3, Finset.sum_union hdisj2] at hχ_sum
  simp only [Finset.sum_singleton, MulChar.map_zero] at hχ_sum
  simp only [Finset.sum_congr rfl hχ_NZSq, Finset.sum_congr rfl hχ_NSq,
      Finset.sum_const, nsmul_eq_mul] at hχ_sum


  have hequal : NZSq.card = NSq.card := by omega
  omega

private lemma GL2.det_ne_zero (g : GL2' p n) : Matrix.det g.val ≠ 0 := by
  intro hdet
  have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  rw [hdet, zero_mul] at hdet1; exact one_ne_zero hdet1.symm

private lemma card_elliptic_fiber (hp2 : p ≠ 2) (hn : n ≠ 0)
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (a b c : GaloisField p n) (hc : c ≠ 0) :
    (Finset.univ.filter (fun d : GaloisField p n =>
      a * b - c * d ≠ 0 ∧ ¬IsSquare ((a - b) ^ 2 + 4 * c * d))).card =
    (Finset.univ.filter (fun x : GaloisField p n => ¬IsSquare x)).card := by
  have h4c : (4 : GaloisField p n) * c ≠ 0 :=
    mul_ne_zero (GaloisField.four_ne_zero hp2 hn) hc

  let φ : GaloisField p n → GaloisField p n := fun d => (a - b) ^ 2 + 4 * c * d
  have hφ_inj : Function.Injective φ := by
    intro d₁ d₂ h
    have : 4 * c * d₁ = 4 * c * d₂ := add_left_cancel (show φ d₁ = φ d₂ from h)
    exact mul_left_cancel₀ h4c this
  have hφ_surj : Function.Surjective φ := by
    intro y
    refine ⟨(y - (a - b) ^ 2) / (4 * c), ?_⟩
    change (a - b) ^ 2 + 4 * c * ((y - (a - b) ^ 2) / (4 * c)) = y
    rw [mul_div_cancel₀ _ h4c, add_sub_cancel]

  set d₀ := a * b / c

  have hφ_d₀ : φ d₀ = (a + b) ^ 2 := by
    simp only [φ, d₀]
    field_simp
    ring

  have hφ_d₀_sq : IsSquare (φ d₀) := by
    rw [hφ_d₀]; exact ⟨a + b, by ring⟩

  have hdet_iff : ∀ d, (a * b - c * d ≠ 0) ↔ d ≠ d₀ := by
    intro d
    constructor
    · intro h hd; apply h; rw [hd]; simp [d₀]; field_simp; ring
    · intro hd h
      have hcd : c * d = a * b := (sub_eq_zero.mp h).symm
      exact hd (show d = d₀ by simp only [d₀]; rw [← hcd, mul_div_cancel_left₀ d hc])

  have hlhs : (Finset.univ.filter (fun d : GaloisField p n =>
      a * b - c * d ≠ 0 ∧ ¬IsSquare ((a - b) ^ 2 + 4 * c * d))) =
      (Finset.univ.filter (fun d : GaloisField p n =>
      d ≠ d₀ ∧ ¬IsSquare (φ d))) := by
    ext d; simp only [Finset.mem_filter, Finset.mem_univ, true_and, φ]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(hdet_iff d).mp h1, h2⟩,
           fun ⟨h1, h2⟩ => ⟨(hdet_iff d).mpr h1, h2⟩⟩
  rw [hlhs]

  apply Finset.card_nbij φ
  ·
    intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    exact hd.2
  ·
    intro d₁ _ d₂ _ h
    exact hφ_inj h
  ·
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨d, rfl⟩ := hφ_surj x
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨d, ⟨fun h => by rw [h] at hx; exact hx hφ_d₀_sq, hx⟩, rfl⟩

/-- Alpha-class cardinality q^2 * (q - 1)^2 / 2 for q = |GaloisField p n| -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := supporting)]
theorem card_classPredicateAlpha [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateAlpha g)).card =
    Fintype.card (GaloisField p n) ^ 2 *
    (Fintype.card (GaloisField p n) - 1) ^ 2 / 2 := by


  let F := GaloisField p n
  have h4_ne : (4 : F) ≠ 0 := GaloisField.four_ne_zero hp2 hn
  set q := Fintype.card F with q_def
  set NSq := (Finset.univ.filter (fun x : F => ¬IsSquare x)).card with NSq_def
  have hNSq : 2 * NSq = q - 1 := two_mul_card_nonsquare hp2 hn
  have hq1 : 1 ≤ q := Fintype.card_pos

  set T := (Finset.univ : Finset F) ×ˢ ((Finset.univ : Finset F) ×ˢ
    (Finset.univ.filter (fun c : F => c ≠ 0) ×ˢ
     Finset.univ.filter (fun x : F => ¬IsSquare x))) with T_def

  suffices hbij : (Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateAlpha g)).card = T.card by
    rw [hbij]

    have hne_card : (Finset.univ.filter (fun c : F => c ≠ 0)).card = q - 1 := by
      rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp only [T, Finset.card_product, Finset.card_univ, hne_card]

    change q * (q * ((q - 1) * NSq)) = q ^ 2 * (q - 1) ^ 2 / 2
    have hmul : 2 * (q * (q * ((q - 1) * NSq))) = q ^ 2 * (q - 1) ^ 2 := by
      calc 2 * (q * (q * ((q - 1) * NSq)))
          = q * q * ((q - 1) * (2 * NSq)) := by ring
        _ = q * q * ((q - 1) * (q - 1)) := by rw [hNSq]
        _ = q ^ 2 * (q - 1) ^ 2 := by ring
    omega
  apply Finset.card_nbij (fun g : GL2' p n =>
    (g.val 0 0, (g.val 1 1, (g.val 0 1, Auxiliary.entryDiscriminant g))))
  ·
    intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [T, Finset.mem_coe, Finset.mem_product, Finset.mem_univ, Finset.mem_filter,
      true_and]
    exact ⟨fun h01 => hg (GL2.isSquare_disc_of_g01_zero h01), hg⟩
  ·
    intro g₁ hg₁ g₂ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h00, h11, h01, hdisc⟩ := h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg₁
    have h01_ne : g₁.val 0 1 ≠ 0 :=
      fun hz => hg₁ (GL2.isSquare_disc_of_g01_zero hz)
    have h10 : g₁.val 1 0 = g₂.val 1 0 := by
      simp only [Auxiliary.entryDiscriminant, GL2.mat] at hdisc
      rw [h00, h11] at hdisc
      have h_cancel := add_left_cancel hdisc
      rw [h01] at h_cancel
      exact mul_left_cancel₀ (mul_ne_zero h4_ne (h01 ▸ h01_ne)) h_cancel
    exact Matrix.GeneralLinearGroup.ext fun i j => by
      fin_cases i <;> fin_cases j
      · exact h00
      · exact h01
      · exact h10
      · exact h11
  ·
    intro t ht
    simp only [T, Finset.mem_coe, Finset.mem_product, Finset.mem_univ, Finset.mem_filter,
      true_and] at ht
    obtain ⟨hc, hx⟩ := ht
    set a := t.1; set b := t.2.1; set c := t.2.2.1; set x := t.2.2.2
    set d := (x - (a - b) ^ 2) / (4 * c) with d_def
    have h4c : (4 : F) * c ≠ 0 := mul_ne_zero h4_ne hc
    have hdisc : (a - b) ^ 2 + 4 * c * d = x := by
      simp only [d_def]; field_simp; ring
    have hdet : a * b - c * d ≠ 0 := by
      intro h
      apply hx
      have hcd : a * b = c * d := by rwa [sub_eq_zero] at h
      have : x = (a + b) ^ 2 :=
        calc x = (a - b) ^ 2 + 4 * c * d := hdisc.symm
          _ = (a - b) ^ 2 + 4 * (c * d) := by ring_nf
          _ = (a - b) ^ 2 + 4 * (a * b) := by rw [← hcd]
          _ = (a + b) ^ 2 := by ring
      rw [this]; exact ⟨a + b, by ring⟩
    have hdet' : Matrix.det !![a, c; d, b] ≠ 0 := by
      simp only [Matrix.det_fin_two_of, ne_eq]; exact hdet
    set g := Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, c; d, b] hdet'

    have hg00 : g.val 0 0 = a := by simp [g, Matrix.cons_val_zero]
    have hg11 : g.val 1 1 = b := by simp [g, Matrix.cons_val_one]
    have hg01 : g.val 0 1 = c := by simp [g, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.vecHead]
    have hg10 : g.val 1 0 = d := by simp [g, Matrix.cons_val_one]
    have hdisc_g : Auxiliary.entryDiscriminant g = x := by
      change (g.val 0 0 - g.val 1 1) ^ 2 + 4 * g.val 0 1 * g.val 1 0 = x
      rw [hg00, hg11, hg01, hg10]; exact hdisc
    refine ⟨g, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Auxiliary.classPredicateAlpha]
      rw [hdisc_g]; exact hx
    · exact Prod.ext hg00 (Prod.ext hg11 (Prod.ext hg01 hdisc_g))

/-- Delta-class cardinality (q - 1) * (q - 2) * q * (q + 1) / 2 for q = |GaloisField p n| -/
@[source_ref "Chapter5/Discussion_5.25.1" (role := supporting)]
theorem card_classPredicateDelta [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateDelta g)).card =
    (Fintype.card (GaloisField p n) - 1) *
    (Fintype.card (GaloisField p n) - 2) *
    Fintype.card (GaloisField p n) *
    (Fintype.card (GaloisField p n) + 1) / 2 := by

  have hpart := GL2.card_partition (p := p) (n := n)
  have hS := card_classPredicateGamma (p := p) hn
  have hP := card_classPredicateBeta hp2 hn
  have hE := card_classPredicateAlpha hp2 hn
  have hGL := GL2.card_GL2 (p := p) (n := n)
  rw [hS, hP, hGL, hE] at hpart
  set q := Fintype.card (GaloisField p n)
  set SS := (Finset.univ.filter (fun g : GL2' p n => Auxiliary.classPredicateDelta g)).card
  have hq3 : 3 ≤ q := GaloisField.card_ge_three hp2 hn
  have hq_odd : q % 2 = 1 := by
    rw [show q = Fintype.card (GaloisField p n) from rfl,
        Fintype.card_eq_nat_card, GaloisField.card p n hn]
    rw [Nat.pow_mod]
    have hp_odd : p % 2 = 1 := by
      have : ¬ 2 ∣ p := by
        intro h
        exact hp2 (hp.out.eq_one_or_self_of_dvd 2 h |>.resolve_left (by omega) |>.symm)
      omega
    rw [hp_odd]; simp



  suffices htarget : (q - 1) + (q - 1) * (q ^ 2 - 1) +
      (q - 1) * (q - 2) * q * (q + 1) / 2 + q ^ 2 * (q - 1) ^ 2 / 2 =
      (q ^ 2 - 1) * (q ^ 2 - q) by omega

  have hE_dvd : 2 ∣ q ^ 2 * (q - 1) ^ 2 := by
    have : 2 ∣ (q - 1) := by omega
    exact dvd_mul_of_dvd_right (Dvd.dvd.pow this (by omega)) _
  have hSS_dvd : 2 ∣ (q - 1) * (q - 2) * q * (q + 1) := by
    have : 2 ∣ (q + 1) := by omega
    exact dvd_mul_of_dvd_right this _

  obtain ⟨a, ha⟩ := hSS_dvd
  obtain ⟨b, hb⟩ := hE_dvd

  rw [ha, hb, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2)]



  have hq1 : 1 ≤ q := by omega
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hq2q : q ≤ q ^ 2 := le_self_pow₀ (by omega) (by omega)
  zify [hq1, hq2, hq2q, show 2 ≤ q from by omega] at ha hb ⊢
  nlinarith [ha, hb]

end Cardinalities

end RepresentationTheory.FiniteFieldUnitClassDecomposition
