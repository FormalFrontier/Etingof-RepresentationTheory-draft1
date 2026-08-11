import Mathlib
import EtingofRepresentationTheory.Chapter2.Definition2_3_8

/-!
# Problem 2.5.1: A quotient of a polynomial ring is indecomposable

Let `A = k[x₁, …, xₙ]` and let `I ≠ A` be any ideal in `A` containing all homogeneous polynomials
of degree `≥ N`. The problem asks to show that `A/I` is an indecomposable representation of `A`.

## Formalization

`A = MvPolynomial (Fin n) k`, `I : Ideal A`, and `A/I` carries its natural `A`-module structure.
"Indecomposable representation" is `Etingof.IsIndecomposable` (Definition 2.3.8). The hypothesis
that `I` contains every homogeneous polynomial of degree `≥ N` is `MvPolynomial.IsHomogeneous`.

## Proof outline

`A/I` is a *local* ring: writing an element as `constant term + higher-degree part`, the
higher-degree part is nilpotent (each homogeneous component of positive degree `i` has its
`N`-th power homogeneous of degree `i·N ≥ N`, hence in `I`), so an element is a unit when its
constant term is nonzero and nilpotent otherwise. A local ring has no idempotents other than
`0` and `1`. Finally, an `A`-submodule of the cyclic module `A/I` is closed under multiplication
by `A/I` (it is an ideal of `A/I`), so a complementary pair `A/I = W₁ ⊕ W₂` yields an idempotent
`e₁ ∈ W₁` with `1 = e₁ + e₂`; triviality of `e₁` forces `W₁ = ⊥` or `W₂ = ⊥`.
-/

namespace Etingof.Problem2_5_1

open MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}

/-- **Problem 2.5.1.** If `I ≠ A = k[x₁, …, xₙ]` is an ideal containing every homogeneous
polynomial of degree `≥ N`, then `A/I` is an indecomposable representation of `A`. -/
theorem quotient_isIndecomposable (N : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (hIne : I ≠ ⊤)
    (hI : ∀ (d : ℕ) (p : MvPolynomial (Fin n) k), N ≤ d → p.IsHomogeneous d → p ∈ I) :
    Etingof.IsIndecomposable (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I) := by
  classical
  set A := MvPolynomial (Fin n) k with hA
  have hnt : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  -- Any polynomial with vanishing constant term becomes nilpotent in `A/I`.
  have nil : ∀ q : A, constantCoeff q = 0 → IsNilpotent (Ideal.Quotient.mk I q) := by
    intro q hq
    have hmk : Ideal.Quotient.mk I q
        = ∑ i ∈ Finset.range (q.totalDegree + 1),
            Ideal.Quotient.mk I (homogeneousComponent i q) := by
      conv_lhs => rw [← sum_homogeneousComponent q]
      rw [map_sum]
    rw [hmk]
    apply isNilpotent_sum
    intro i _
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [homogeneousComponent_zero, ← constantCoeff_eq, hq]
      simp
    · refine ⟨N, ?_⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hI (i * N) _ (le_mul_of_one_le_left (Nat.zero_le N) hipos)
        ((homogeneousComponent_isHomogeneous i q).pow N)
  -- `A/I` is a local ring: every element or its complement is a unit.
  have hlocal : ∀ a : A ⧸ I, IsUnit a ∨ IsUnit (1 - a) := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    set c := constantCoeff p with hc
    have hqnil : IsNilpotent (Ideal.Quotient.mk I (p - C c)) := by
      apply nil
      simp [hc]
    have hsplit : Ideal.Quotient.mk I p
        = Ideal.Quotient.mk I (C c) + Ideal.Quotient.mk I (p - C c) := by
      rw [← map_add]; congr 1; ring
    by_cases hcz : c = 0
    · right
      have hpq : Ideal.Quotient.mk I p = Ideal.Quotient.mk I (p - C c) := by
        rw [hsplit, hcz]; simp
      rw [hpq]
      exact hqnil.isUnit_one_sub
    · left
      have hcu : IsUnit (Ideal.Quotient.mk I (C c)) :=
        ((isUnit_iff_ne_zero.mpr hcz).map (C : k →+* A)).map (Ideal.Quotient.mk I)
      rw [hsplit]
      exact hqnil.isUnit_add_left_of_commute hcu (Commute.all _ _)
  -- An `A`-submodule of the cyclic module `A/I` is closed under `A/I`-multiplication.
  have hideal : ∀ (W : Submodule A (A ⧸ I)) (r w : A ⧸ I), w ∈ W → r * w ∈ W := by
    intro W r w hw
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hsmul : Ideal.Quotient.mk I a * w = a • w := by
      rw [← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def]
    rw [hsmul]
    exact W.smul_mem a hw
  refine ⟨hnt, ?_⟩
  intro W₁ W₂ hcompl
  have hbot : W₁ ⊓ W₂ = ⊥ := hcompl.inf_eq_bot
  have htop : W₁ ⊔ W₂ = ⊤ := hcompl.sup_eq_top
  have h1 : (1 : A ⧸ I) ∈ W₁ ⊔ W₂ := htop.ge Submodule.mem_top
  rw [Submodule.mem_sup] at h1
  obtain ⟨e₁, he₁, e₂, he₂, hsum1⟩ := h1
  -- `e₁ * e₂ = 0` since it lies in `W₁ ⊓ W₂ = ⊥`.
  have hprod12 : e₁ * e₂ = 0 := by
    have hm : e₁ * e₂ ∈ W₁ ⊓ W₂ := by
      refine ⟨?_, hideal W₂ e₁ e₂ he₂⟩
      rw [mul_comm]; exact hideal W₁ e₂ e₁ he₁
    rw [hbot] at hm
    simpa using hm
  -- `e₁` is idempotent.
  have hidem : e₁ * e₁ = e₁ := by
    have h := congrArg (e₁ * ·) hsum1
    simp only [mul_add, hprod12, add_zero, mul_one] at h
    exact h
  -- In a local ring the only idempotents are `0` and `1`.
  have he₁triv : e₁ = 0 ∨ e₁ = 1 := by
    rcases hlocal e₁ with hu | hu
    · right
      have hz : e₁ * (e₁ - 1) = 0 := by rw [mul_sub, hidem, mul_one, sub_self]
      have := hu.mul_right_eq_zero.mp hz
      rwa [sub_eq_zero] at this
    · left
      have hz : (1 - e₁) * e₁ = 0 := by rw [sub_mul, one_mul, hidem, sub_self]
      exact hu.mul_right_eq_zero.mp hz
  rcases he₁triv with h0 | h1e
  · left
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwe2 : w * e₂ = 0 := by
      have hm : w * e₂ ∈ W₁ ⊓ W₂ := by
        refine ⟨?_, hideal W₂ w e₂ he₂⟩
        rw [mul_comm]; exact hideal W₁ e₂ w hw
      rw [hbot] at hm
      simpa using hm
    have hw' : w = w * e₁ + w * e₂ := by rw [← mul_add, hsum1, mul_one]
    rw [h0, mul_zero, zero_add, hwe2] at hw'
    exact hw'
  · right
    have he2z : e₂ = 0 := by
      have h := hsum1
      rw [h1e] at h
      simpa using h
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwe1 : w * e₁ = 0 := by
      have hm : w * e₁ ∈ W₁ ⊓ W₂ := by
        refine ⟨hideal W₁ w e₁ he₁, ?_⟩
        rw [mul_comm]; exact hideal W₂ e₁ w hw
      rw [hbot] at hm
      simpa using hm
    have hw' : w = w * e₁ + w * e₂ := by rw [← mul_add, hsum1, mul_one]
    rw [he2z, mul_zero, add_zero, hwe1] at hw'
    exact hw'

end Etingof.Problem2_5_1
