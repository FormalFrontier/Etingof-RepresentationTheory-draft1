import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Proposition 9.1.1: Lifting of idempotents from quotient by nilpotent ideal

Let A be a unital ring, and I ⊂ A a nilpotent ideal. Then:

(i) Any idempotent ē ∈ A/I can be lifted to an idempotent e ∈ A (i.e., there exists an
idempotent e ∈ A such that the image of e in A/I is ē).

(ii) Any two liftings of an idempotent ē to A are conjugate by an element of 1 + I.

## Proof sketch

For I² = 0: Given a ∈ A with a² ≡ a (mod I), set e = 3a² − 2a³. Then e² − e ∈ I²  = 0.
For general nilpotent I: use induction on the nilpotency degree, applying the I² = 0 case
to successive quotients.
-/

/-- Idempotent lifting, Part (i): any idempotent in A/I lifts to an idempotent in A,
when I is a nilpotent two-sided ideal. (Etingof Proposition 9.1.1(i))

This follows directly from Mathlib's `exists_isIdempotentElem_eq_of_ker_isNilpotent`. -/
theorem Etingof.idempotent_lifting_exists {A : Type*} [Ring A]
    (I : Ideal A) [I.IsTwoSided] (hI : IsNilpotent I)
    (ebar : A ⧸ I) (h_idem : IsIdempotentElem ebar) :
    ∃ e : A, IsIdempotentElem e ∧ Ideal.Quotient.mk I e = ebar := by
  obtain ⟨n, hn⟩ := hI
  apply exists_isIdempotentElem_eq_of_ker_isNilpotent (Ideal.Quotient.mk I)
  · intro x hx
    rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact ⟨n, by
      have h_mem := Ideal.pow_mem_pow hx n
      rw [hn] at h_mem
      exact Ideal.mem_bot.mp h_mem⟩
  · exact Ideal.Quotient.mk_surjective ebar
  · exact h_idem

/-- Idempotent lifting, Part (ii): any two liftings of an idempotent are conjugate
by an element of 1 + I. (Etingof Proposition 9.1.1(ii))

This is a stronger result than uniqueness — in the non-commutative case, two lifted
idempotents need not be equal but are always conjugate.

The conjugating unit is `u = 1 + (2e₂ - 1)(e₁ - e₂)`, which lies in `1 + I` since
`e₁ - e₂ ∈ I`. It is a unit because `(2e₂ - 1)(e₁ - e₂) ∈ I` and `I` is nilpotent.
The key identity `u·e₁ = e₂·u` follows from pure idempotent algebra. -/
theorem Etingof.idempotent_lifting_conjugate {A : Type*} [Ring A]
    (I : Ideal A) [I.IsTwoSided] (hI : IsNilpotent I)
    (e₁ e₂ : A) (h₁ : IsIdempotentElem e₁) (h₂ : IsIdempotentElem e₂)
    (h_eq : Ideal.Quotient.mk I e₁ = Ideal.Quotient.mk I e₂) :
    ∃ u : Aˣ, (↑u - 1 : A) ∈ I ∧ ↑u * e₁ * ↑u⁻¹ = e₂ := by
  -- e₁ - e₂ ∈ I from equal quotient images
  have hdiff : e₁ - e₂ ∈ I := by
    have : Ideal.Quotient.mk I (e₁ - e₂) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact h_eq
    rwa [Ideal.Quotient.eq_zero_iff_mem] at this
  -- s = (2e₂ - 1)(e₁ - e₂) ∈ I
  set s := (2 * e₂ - 1) * (e₁ - e₂) with hs_def
  have hs_mem : s ∈ I := I.mul_mem_left _ hdiff
  -- s is nilpotent: s ∈ I, so s^n ∈ I^n = ⊥
  obtain ⟨n, hn⟩ := hI
  have hs_nil : IsNilpotent s := by
    refine ⟨n, ?_⟩
    have h_mem := Ideal.pow_mem_pow hs_mem n
    simp only [hn] at h_mem
    simpa using h_mem
  -- 1 + s is a unit
  obtain ⟨u, hu⟩ := IsNilpotent.isUnit_one_add hs_nil
  refine ⟨u, ?_, ?_⟩
  · -- u - 1 = s ∈ I
    rw [show (↑u : A) = 1 + s from hu, add_sub_cancel_left]
    exact hs_mem
  · -- u * e₁ * u⁻¹ = e₂, via (1+s)*e₁ = e₂*(1+s)
    -- Key identity 1: (1+s)*e₁ = e₂*e₁
    have hleft : (1 + s) * e₁ = e₂ * e₁ := by
      suffices h : s * e₁ = e₂ * e₁ - e₁ by rw [add_mul, one_mul, h]; abel
      -- s * e₁ = (2e₂-1)*(e₁-e₂)*e₁ = (2e₂-1)*(e₁ - e₂*e₁) = e₂*e₁ - e₁
      have h_de : (e₁ - e₂) * e₁ = e₁ - e₂ * e₁ := by rw [sub_mul, h₁.eq]
      calc s * e₁
          = (2 * e₂ - 1) * ((e₁ - e₂) * e₁) := by rw [hs_def, mul_assoc]
        _ = (2 * e₂ - 1) * (e₁ - e₂ * e₁) := by rw [h_de]
        _ = (2 * e₂) * (e₁ - e₂ * e₁) - (e₁ - e₂ * e₁) := by rw [sub_mul, one_mul]
        _ = ((2 * e₂) * e₁ - (2 * e₂) * (e₂ * e₁)) - (e₁ - e₂ * e₁) := by rw [mul_sub]
        _ = ((2 * e₂) * e₁ - 2 * (e₂ * (e₂ * e₁))) - (e₁ - e₂ * e₁) := by
            rw [mul_assoc (2 : A) e₂ (e₂ * e₁)]
        _ = ((2 * e₂) * e₁ - 2 * (e₂ * e₁)) - (e₁ - e₂ * e₁) := by
            rw [← mul_assoc e₂ e₂ e₁, h₂.eq]
        _ = e₂ * e₁ - e₁ := by rw [mul_assoc (2 : A) e₂ e₁]; abel
    -- Key identity 2: e₂*(1+s) = e₂*e₁
    have hright : e₂ * (1 + s) = e₂ * e₁ := by
      rw [mul_add, mul_one, hs_def, ← mul_assoc e₂]
      -- Goal: e₂ + e₂ * (2 * e₂ - 1) * (e₁ - e₂) = e₂ * e₁
      -- e₂ * (2e₂ - 1) = e₂
      have h5 : e₂ * (2 * e₂ - 1) = e₂ := by
        rw [mul_sub, mul_one, show (2 : A) * e₂ = e₂ + e₂ from two_mul e₂,
            mul_add, h₂.eq]
        abel
      rw [h5, mul_sub, h₂.eq]
      -- Goal: e₂ + (e₂ * e₁ - e₂) = e₂ * e₁
      abel
    -- (1+s)*e₁ = e₂*(1+s), so u*e₁*u⁻¹ = e₂
    have hcomm : ↑u * e₁ = e₂ * ↑u := by rw [hu, hleft, ← hright]
    calc (↑u : A) * e₁ * ↑u⁻¹
        = e₂ * ↑u * ↑u⁻¹ := by rw [hcomm]
      _ = e₂ := by rw [mul_assoc]; simp
