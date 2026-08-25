import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Proposition 3.5.3: Rad(A) is the Largest Nilpotent Two-Sided Ideal

Let A be a finite dimensional algebra.

(i) Let I be a nilpotent two-sided ideal in A; i.e., I^n = 0 for some n.
    Then I ⊆ Rad(A).

(ii) Rad(A) is a nilpotent ideal. Thus, Rad(A) is the largest nilpotent
     two-sided ideal in A.
-/

/-- Any nilpotent two-sided ideal is contained in the radical.
Etingof Proposition 3.5.3(i). -/
theorem Etingof.nilpotent_ideal_le_radical (A : Type*) [Ring A]
    (I : Ideal A) (hI : IsNilpotent I) :
    I ≤ Ideal.jacobson ⊥ := by
  intro x hx
  rw [Ideal.mem_jacobson_iff]
  intro y
  -- y * x ∈ I since I is a left ideal
  have hyx : y * x ∈ I := I.mul_mem_left y hx
  -- (y * x)^n ∈ I^n = ⊥, so y * x is nilpotent
  obtain ⟨n, hn⟩ := hI
  have hnil : IsNilpotent (y * x) := ⟨n, by
    have h := Ideal.pow_mem_pow hyx n
    rw [hn] at h
    exact (Submodule.mem_bot A).mp h⟩
  -- 1 + y * x is a unit
  obtain ⟨u, hu_eq⟩ := hnil.isUnit_one_add
  refine ⟨↑u⁻¹, ?_⟩
  simp only [Submodule.mem_bot]
  have : ↑u⁻¹ * y * x + ↑u⁻¹ - 1 = ↑u⁻¹ * (y * x + 1) - 1 := by
    rw [mul_add, mul_one, mul_assoc]
  rw [this, add_comm (y * x) 1, ← hu_eq, u.inv_mul, sub_self]

/-- The radical of a finite dimensional algebra is nilpotent.
Etingof Proposition 3.5.3(ii). -/
theorem Etingof.radical_is_nilpotent (k : Type*) (A : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    IsNilpotent (Ideal.jacobson (⊥ : Ideal A)) := by
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  exact IsArtinianRing.isNilpotent_jacobson_bot
