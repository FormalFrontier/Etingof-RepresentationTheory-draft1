import Mathlib.RingTheory.Idempotents

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

**Proof strategy** (not yet formalized):
- Base case (I² = 0): Set d = e₁ - e₂ ∈ I with d² = 0. The conjugating unit is
  u = 1 - e₁ - e₂ + 2·e₂·e₁ with inverse v = 1 - e₁ - e₂ + 2·e₁·e₂.
  Key identities (from d² = 0): e₁·e₂·e₁ = e₁, e₂·e₁·e₂ = e₂, u·v = v·u = 1,
  u·e₁ = e₂·u = e₂·e₁, and u - 1 ∈ I.
- General case: induction on nilpotency degree n. Factor through A → A/I^⌈n/2⌉ → A/I
  and compose conjugating units from successive liftings. -/
theorem Etingof.idempotent_lifting_conjugate {A : Type*} [Ring A]
    (I : Ideal A) [I.IsTwoSided] (hI : IsNilpotent I)
    (e₁ e₂ : A) (h₁ : IsIdempotentElem e₁) (h₂ : IsIdempotentElem e₂)
    (h_eq : Ideal.Quotient.mk I e₁ = Ideal.Quotient.mk I e₂) :
    ∃ u : Aˣ, (↑u - 1 : A) ∈ I ∧ ↑u * e₁ * ↑u⁻¹ = e₂ := by
  sorry
