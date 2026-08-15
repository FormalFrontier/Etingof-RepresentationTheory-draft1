/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.GeneralLinearGroup.Auxiliary
import RepresentationTheory.MvPolynomial.Vanishing

set_option linter.style.longLine false

namespace RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization

variable {k : Type*} [Field k] {N : ℕ}

/-- An auxiliary multivariable polynomial over a field with variables indexed by pairs of finite matrix indices. -/
noncomputable def auxiliary_matrix_polynomial (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (Fin N × Fin N) k :=
  Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)

/-- The auxiliary polynomial in matrix-entry variables is nonzero. -/
theorem auxiliary_matrix_polynomial_ne_zero : auxiliary_matrix_polynomial k N ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin N) k

/-- Every power of the auxiliary matrix polynomial is a non-zero-divisor. -/
theorem powers_auxiliary_polynomial_le_nonZeroDivisors :
    Submonoid.powers (auxiliary_matrix_polynomial k N) ≤ nonZeroDivisors (MvPolynomial (Fin N × Fin N) k) := by
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n auxiliary_matrix_polynomial_ne_zero)

/-- The ring homomorphism evaluating a polynomial in matrix-entry variables on general linear matrices. -/
noncomputable def matrix_polynomial_evaluation_ringHom :
    MvPolynomial (Fin N × Fin N) k →+* (Matrix.GeneralLinearGroup (Fin N) k → k) :=
  RingHom.pi fun g =>
    MvPolynomial.eval (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)

/-- Applying matrix-polynomial evaluation is ordinary multivariable evaluation at the entries of the given general linear matrix. -/
@[simp]
theorem matrix_polynomial_evaluation_apply (p : MvPolynomial (Fin N × Fin N) k)
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    matrix_polynomial_evaluation_ringHom p g =
      MvPolynomial.eval (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) p :=
  rfl

/-- The auxiliary matrix polynomial evaluates on a general linear matrix to its determinant. -/
theorem matrix_polynomial_evaluation_auxiliary_apply (g : Matrix.GeneralLinearGroup (Fin N) k) :
    matrix_polynomial_evaluation_ringHom (auxiliary_matrix_polynomial k N) g = (g : Matrix (Fin N) (Fin N) k).det := by
  rw [matrix_polynomial_evaluation_apply, auxiliary_matrix_polynomial,
    (MvPolynomial.eval
      (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)).map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

/-- Over an infinite field, evaluating matrix-entry polynomials on all general linear matrices is injective. -/
theorem matrix_polynomial_evaluation_injective [Infinite k] :
    Function.Injective (matrix_polynomial_evaluation_ringHom (k := k) (N := N)) := by
  intro p q h
  apply MvPolynomial.eq_of_eval_eq_on_gl
  intro g
  exact congrFun h g

/-- The evaluation function of the auxiliary matrix polynomial on the general linear group is a unit. -/
theorem matrix_polynomial_evaluation_auxiliary_isUnit :
    IsUnit (matrix_polynomial_evaluation_ringHom (auxiliary_matrix_polynomial k N)) := by
  rw [Pi.isUnit_iff]
  intro g
  rw [matrix_polynomial_evaluation_auxiliary_apply]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)

/-- The ring homomorphism that evaluates localized matrix-entry polynomials on general linear matrices. -/
noncomputable def localization_evaluation_ringHom :
    Localization.Away (auxiliary_matrix_polynomial k N) →+* (Matrix.GeneralLinearGroup (Fin N) k → k) :=
  IsLocalization.Away.lift (g := matrix_polynomial_evaluation_ringHom) (auxiliary_matrix_polynomial k N) matrix_polynomial_evaluation_auxiliary_isUnit

/-- Composing localization evaluation with the canonical algebra map gives matrix-polynomial evaluation. -/
@[simp]
theorem localization_evaluation_comp_algebraMap :
    (localization_evaluation_ringHom (k := k) (N := N)).comp
        (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (auxiliary_matrix_polynomial k N)))
      = matrix_polynomial_evaluation_ringHom :=
  IsLocalization.Away.lift_comp _ _

/-- Evaluating the canonical localized image of a matrix-entry polynomial agrees with polynomial evaluation on general linear matrices. -/
@[simp]
theorem localization_evaluation_algebraMap (a : MvPolynomial (Fin N × Fin N) k) :
    localization_evaluation_ringHom (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) a) = matrix_polynomial_evaluation_ringHom a :=
  IsLocalization.Away.lift_eq _ _ _

/-- Over an infinite field, evaluation of localized matrix-entry polynomials on general linear matrices is injective. -/
theorem localization_evaluation_injective [Infinite k] :
    Function.Injective (localization_evaluation_ringHom (k := k) (N := N)) := by
  have key : ∀ x y : MvPolynomial (Fin N × Fin N) k,
      algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) x
          = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) y
        ↔ matrix_polynomial_evaluation_ringHom x = matrix_polynomial_evaluation_ringHom y := fun x y => by
    rw [(IsLocalization.injective (Localization.Away (auxiliary_matrix_polynomial k N))
          powers_auxiliary_polynomial_le_nonZeroDivisors).eq_iff,
        matrix_polynomial_evaluation_injective.eq_iff]
  exact (IsLocalization.lift_injective_iff _).mpr key

/-- An auxiliary ring homomorphism from a multivariable polynomial ring to the localization of the matrix-entry polynomial ring. -/
noncomputable def auxiliary_localization_ringHom :
    MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k →+* Localization.Away (auxiliary_matrix_polynomial k N) :=
  MvPolynomial.eval₂Hom (algebraMap k (Localization.Away (auxiliary_matrix_polynomial k N)))
    (Sum.elim
      (fun ij : Fin N × Fin N =>
        algebraMap (MvPolynomial (Fin N × Fin N) k) _ (MvPolynomial.X ij))
      (fun _ : Unit => IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N)))

/-- The auxiliary localization homomorphism sends a constant polynomial to its canonical image in the localization. -/
@[simp]
theorem auxiliary_localization_ringHom_C (r : k) :
    auxiliary_localization_ringHom (MvPolynomial.C r : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k)
      = algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (auxiliary_matrix_polynomial k N))
          (MvPolynomial.C r) := by
  rw [auxiliary_localization_ringHom, MvPolynomial.eval₂Hom_C,
    IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k)
      (Localization.Away (auxiliary_matrix_polynomial k N)),
    MvPolynomial.algebraMap_eq]

/-- On a variable from the left summand, the auxiliary localization homomorphism gives the corresponding matrix-entry variable in the localization. -/
@[simp]
theorem auxiliary_localization_ringHom_X_inl (ij : Fin N × Fin N) :
    auxiliary_localization_ringHom (MvPolynomial.X (Sum.inl ij) : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k)
      = algebraMap (MvPolynomial (Fin N × Fin N) k) _ (MvPolynomial.X ij) := by
  rw [auxiliary_localization_ringHom, MvPolynomial.eval₂Hom_X', Sum.elim_inl]

/-- On a variable from the right summand, the auxiliary localization homomorphism gives the distinguished inverse of the localized polynomial. -/
@[simp]
theorem auxiliary_localization_ringHom_X_inr (u : Unit) :
    auxiliary_localization_ringHom (MvPolynomial.X (Sum.inr u) : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k)
      = IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) := by
  rw [auxiliary_localization_ringHom, MvPolynomial.eval₂Hom_X', Sum.elim_inr]

/-- The distinguished inverse in the localization evaluates at a general linear matrix to the inverse of its determinant. -/
theorem localization_evaluation_invSelf_apply (g : Matrix.GeneralLinearGroup (Fin N) k) :
    localization_evaluation_ringHom (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N)) g
      = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ := by
  have hg_det : (g : Matrix (Fin N) (Fin N) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero
  have hmul : localization_evaluation_ringHom (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N))
      * localization_evaluation_ringHom (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N)) = 1 := by
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hmul_g := congrFun hmul g
  rw [Pi.mul_apply, Pi.one_apply, localization_evaluation_algebraMap, matrix_polynomial_evaluation_auxiliary_apply] at hmul_g
  calc localization_evaluation_ringHom (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N)) g
      = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹
          * ((g : Matrix (Fin N) (Fin N) k).det
              * localization_evaluation_ringHom (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N)) g) := by
        rw [← mul_assoc, inv_mul_cancel₀ hg_det, one_mul]
    _ = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ := by rw [hmul_g, mul_one]

/-- The displayed transformation of a polynomial agrees with evaluating its image under the auxiliary localization homomorphism at the given general linear matrix. -/
theorem auxiliary_localization_ringHom_action_apply
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g p = localization_evaluation_ringHom (auxiliary_localization_ringHom p) g := by
  have hΦΨ :
      (MvPolynomial.eval (Sum.elim
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (fun _ : Unit => ((g : Matrix (Fin N) (Fin N) k).det)⁻¹)) :
        MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k →+* k)
        = (Pi.evalRingHom (fun _ : Matrix.GeneralLinearGroup (Fin N) k => k) g).comp
            ((localization_evaluation_ringHom).comp auxiliary_localization_ringHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval_C, Pi.evalRingHom_apply,
        auxiliary_localization_ringHom_C, localization_evaluation_algebraMap, matrix_polynomial_evaluation_apply]
    · intro s
      rcases s with ij | u
      · simp only [RingHom.comp_apply, MvPolynomial.eval_X, Sum.elim_inl,
          Pi.evalRingHom_apply, auxiliary_localization_ringHom_X_inl, localization_evaluation_algebraMap, matrix_polynomial_evaluation_apply]
      · simp only [RingHom.comp_apply, MvPolynomial.eval_X, Sum.elim_inr,
          Pi.evalRingHom_apply, auxiliary_localization_ringHom_X_inr, localization_evaluation_invSelf_apply]
  have := RingHom.congr_fun hΦΨ p
  simpa [RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation] using this

/-- The canonical map from the matrix-entry polynomial ring into the localization away from the auxiliary polynomial is injective. -/
theorem matrix_polynomial_algebraMap_injective :
    Function.Injective
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (auxiliary_matrix_polynomial k N))) :=
  IsLocalization.injective _ powers_auxiliary_polynomial_le_nonZeroDivisors

/-- The product of equal powers of the localized auxiliary polynomial and its distinguished inverse is one. -/
theorem algebraMap_pow_mul_invSelf_pow (n : ℕ) :
    (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (auxiliary_matrix_polynomial k N))
          (auxiliary_matrix_polynomial k N)) ^ n
        * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ n = 1 := by
  rw [← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]

/-- Every element localized away from the auxiliary polynomial is a polynomial numerator times a power of the distinguished inverse. -/
theorem exists_localization_presentation (f : Localization.Away (auxiliary_matrix_polynomial k N)) :
    ∃ (r : ℕ) (Q : MvPolynomial (Fin N × Fin N) k),
      f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (auxiliary_matrix_polynomial k N) f
  refine ⟨n, a, ?_⟩
  have key := algebraMap_pow_mul_invSelf_pow (k := k) (N := N) n
  calc
    f = f * ((algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N)) ^ n
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ n) := by rw [key, mul_one]
    _ = (f * (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N)) ^ n)
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ n := by ring
    _ = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) a
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ n := by rw [h]

open Classical in
/-- The least exponent needed to represent an element of the localization using a power of the distinguished inverse. -/
noncomputable def localization_denominator_order (f : Localization.Away (auxiliary_matrix_polynomial k N)) : ℕ :=
  Nat.find (exists_localization_presentation f)

open Classical in
/-- Every localized element has a numerator presentation whose inverse exponent is its denominator order. -/
theorem exists_numerator_at_denominator_order (f : Localization.Away (auxiliary_matrix_polynomial k N)) :
    ∃ Q : MvPolynomial (Fin N × Fin N) k,
      f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ localization_denominator_order f :=
  Nat.find_spec (exists_localization_presentation f)

open Classical in
/-- Any presentation with inverse exponent `r` bounds the denominator order above by `r`. -/
theorem denominator_order_le_of_exists_presentation {f : Localization.Away (auxiliary_matrix_polynomial k N)} {r : ℕ}
    (h : ∃ Q : MvPolynomial (Fin N × Fin N) k,
          f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r) :
    localization_denominator_order f ≤ r :=
  Nat.find_min' (exists_localization_presentation f) h

/-- A presentation of a localized element using a power of the distinguished inverse yields the corresponding denominator-clearing identity. -/
theorem algebraMap_eq_mul_pow_of_eq_mul_invSelf_pow {f : Localization.Away (auxiliary_matrix_polynomial k N)} {r : ℕ}
    {Q : MvPolynomial (Fin N × Fin N) k}
    (hQ : f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r) :
    algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
      = f * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N) ^ r := by
  rw [hQ, mul_assoc,
    show IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r
        * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N) ^ r = 1
      from by rw [mul_comm]; exact algebraMap_pow_mul_invSelf_pow r,
    mul_one]

/-- Two polynomial numerators representing the same localized element with the same inverse exponent are equal. -/
theorem numerator_unique_of_fixed_denominator {f : Localization.Away (auxiliary_matrix_polynomial k N)} {r : ℕ}
    {Q₁ Q₂ : MvPolynomial (Fin N × Fin N) k}
    (h₁ : f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q₁
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r)
    (h₂ : f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q₂
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r) :
    Q₁ = Q₂ :=
  matrix_polynomial_algebraMap_injective (by rw [algebraMap_eq_mul_pow_of_eq_mul_invSelf_pow h₁, algebraMap_eq_mul_pow_of_eq_mul_invSelf_pow h₂])

/-- If a presentation uses an exponent larger than the denominator order, then the auxiliary polynomial divides its numerator. -/
theorem auxiliary_polynomial_dvd_numerator_of_order_lt {f : Localization.Away (auxiliary_matrix_polynomial k N)} {r : ℕ}
    {Q : MvPolynomial (Fin N × Fin N) k}
    (hQ : f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r)
    (hlt : localization_denominator_order f < r) : auxiliary_matrix_polynomial k N ∣ Q := by
  obtain ⟨Qs, hs⟩ := exists_numerator_at_denominator_order f
  obtain ⟨s, hsdef⟩ : ∃ s, localization_denominator_order f = s := ⟨_, rfl⟩
  rw [hsdef] at hs hlt
  have hQeq : algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
      = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (Qs * auxiliary_matrix_polynomial k N ^ (r - s)) := by
    rw [algebraMap_eq_mul_pow_of_eq_mul_invSelf_pow hQ, hs, map_mul, map_pow,
      show algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N) ^ r
          = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N) ^ s
            * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N) ^ (r - s)
        from by rw [← pow_add]; congr 1; omega]
    calc
      (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Qs
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ s)
          * (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N) ^ s
            * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N) ^ (r - s))
        = (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ s
            * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N) ^ s)
          * (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Qs
            * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N) ^ (r - s)) := by
          ring
      _ = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Qs
            * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N) ^ (r - s) := by
          rw [show IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ s
                * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N) ^ s = 1
              from by rw [mul_comm]; exact algebraMap_pow_mul_invSelf_pow _, one_mul]
  have hQ2 : Q = Qs * auxiliary_matrix_polynomial k N ^ (r - s) := matrix_polynomial_algebraMap_injective hQeq
  rw [hQ2]
  exact (dvd_pow_self (auxiliary_matrix_polynomial k N) (by omega : r - s ≠ 0)).mul_left Qs

/-- In a presentation at positive denominator order, the auxiliary polynomial does not divide the numerator. -/
theorem auxiliary_polynomial_not_dvd_numerator_at_order {f : Localization.Away (auxiliary_matrix_polynomial k N)}
    {Q : MvPolynomial (Fin N × Fin N) k}
    (hQ : f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ localization_denominator_order f)
    (hpos : 1 ≤ localization_denominator_order f) : ¬ auxiliary_matrix_polynomial k N ∣ Q := by
  intro hd
  obtain ⟨Q', rfl⟩ := hd
  obtain ⟨s, hsdef⟩ : ∃ s, localization_denominator_order f = s := ⟨_, rfl⟩
  rw [hsdef] at hQ hpos
  have hlow : ∃ Q'' : MvPolynomial (Fin N × Fin N) k,
      f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q''
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ (s - 1) := by
    refine ⟨Q', ?_⟩
    rw [hQ, map_mul,
      show IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ s
          = IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ (s - 1)
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N)
        from by conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ]]
    calc
      algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N)
            * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q'
          * (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ (s - 1)
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N))
        = (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) (auxiliary_matrix_polynomial k N)
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N))
          * (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q'
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ (s - 1)) := by ring
      _ = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q'
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ (s - 1) := by
          rw [IsLocalization.Away.mul_invSelf, one_mul]
  have hle := denominator_order_le_of_exists_presentation hlow
  rw [hsdef] at hle
  omega

/-- A presentation whose exponent is zero or whose numerator is not divisible by the localized polynomial realizes the denominator order. -/
theorem denominator_order_eq_of_reduced_presentation {f : Localization.Away (auxiliary_matrix_polynomial k N)} {r : ℕ}
    {Q : MvPolynomial (Fin N × Fin N) k}
    (hQ : f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r)
    (hred : r = 0 ∨ ¬ auxiliary_matrix_polynomial k N ∣ Q) : r = localization_denominator_order f := by
  refine le_antisymm ?_ (denominator_order_le_of_exists_presentation ⟨Q, hQ⟩)
  by_contra hlt
  push Not at hlt
  rcases hred with h0 | hnd
  · omega
  · exact hnd (auxiliary_polynomial_dvd_numerator_of_order_lt hQ hlt)

/-- Every localized element has a presentation with minimal inverse exponent and, for positive exponent, a numerator not divisible by the auxiliary polynomial. -/
theorem exists_minimal_localization_presentation (f : Localization.Away (auxiliary_matrix_polynomial k N)) :
    ∃ (r : ℕ) (Q : MvPolynomial (Fin N × Fin N) k),
      f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r
        ∧ (1 ≤ r → ¬ auxiliary_matrix_polynomial k N ∣ Q)
        ∧ ∀ (r' : ℕ) (Q' : MvPolynomial (Fin N × Fin N) k),
            f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q'
                  * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r' → r ≤ r' := by
  obtain ⟨Q, hQ⟩ := exists_numerator_at_denominator_order f
  exact ⟨localization_denominator_order f, Q, hQ, fun hpos => auxiliary_polynomial_not_dvd_numerator_at_order hQ hpos,
    fun _ Q' h' => denominator_order_le_of_exists_presentation ⟨Q', h'⟩⟩

/-- Two reduced presentations of the same localized element have equal inverse exponents and equal numerators. -/
theorem reduced_localization_presentation_unique {f : Localization.Away (auxiliary_matrix_polynomial k N)} {r₁ r₂ : ℕ}
    {Q₁ Q₂ : MvPolynomial (Fin N × Fin N) k}
    (h₁ : f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q₁
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r₁)
    (hred₁ : r₁ = 0 ∨ ¬ auxiliary_matrix_polynomial k N ∣ Q₁)
    (h₂ : f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q₂
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r₂)
    (hred₂ : r₂ = 0 ∨ ¬ auxiliary_matrix_polynomial k N ∣ Q₂) :
    r₁ = r₂ ∧ Q₁ = Q₂ := by
  have e₁ := denominator_order_eq_of_reduced_presentation h₁ hred₁
  have e₂ := denominator_order_eq_of_reduced_presentation h₂ hred₂
  refine ⟨e₁.trans e₂.symm, ?_⟩
  rw [e₁] at h₁
  rw [e₂] at h₂
  exact numerator_unique_of_fixed_denominator h₁ h₂

/-- A localized element has denominator order zero exactly when it belongs to the range of the canonical algebra map. -/
theorem denominator_order_eq_zero_iff_mem_range_algebraMap (f : Localization.Away (auxiliary_matrix_polynomial k N)) :
    localization_denominator_order f = 0 ↔ f ∈ Set.range
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (auxiliary_matrix_polynomial k N))) := by
  constructor
  · intro h0
    obtain ⟨Q, hQ⟩ := exists_numerator_at_denominator_order f
    rw [h0, pow_zero, mul_one] at hQ
    exact ⟨Q, hQ.symm⟩
  · rintro ⟨Q, rfl⟩
    exact Nat.le_zero.mp (denominator_order_le_of_exists_presentation (r := 0) ⟨Q, by rw [pow_zero, mul_one]⟩)

end RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
