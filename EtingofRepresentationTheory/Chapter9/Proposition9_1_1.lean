import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Nilpotent.Defs

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

/-- Idempotents can be lifted through nilpotent ideals: any idempotent in A/I lifts to A.
(Etingof Proposition 9.1.1) -/
theorem Etingof.idempotent_lifting : (sorry : Prop) := sorry
