import EtingofRepresentationTheory.Chapter5.Definition5_12_1

/-!
# Lemma 5.13.1: Young Projector Linear Functional

For x ∈ ℂ[S_n], we have a_λ · x · b_λ = ℓ_λ(x) · c_λ, where ℓ_λ is a linear
functional on ℂ[S_n]. Here a_λ = Σ_{g ∈ P_λ} g and b_λ = Σ_{g ∈ Q_λ} sign(g) · g.

## Mathlib correspondence

Requires Young symmetrizer infrastructure (Definition 5.12.1).
-/

namespace Etingof

private abbrev G (n : ℕ) := Equiv.Perm (Fin n)

/-- The row symmetrizer absorbs row group elements on the right:
a_λ * of(p) = a_λ for p ∈ P_λ. -/
theorem RowSymmetrizer_mul_of_row {n : ℕ} {la : Nat.Partition n}
    (p : G n) (hp : p ∈ RowSubgroup n la) :
    RowSymmetrizer n la * MonoidAlgebra.of ℂ (G n) p =
      RowSymmetrizer n la := by
  classical
  simp only [RowSymmetrizer]
  rw [Finset.sum_mul]
  simp_rw [← (MonoidAlgebra.of ℂ (G n)).map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight ⟨p, hp⟩) _ _
    (fun g => by simp [Subgroup.coe_mul])

/-- Row group elements are absorbed on the left:
of(p) * a_λ = a_λ for p ∈ P_λ. -/
theorem of_row_mul_RowSymmetrizer {n : ℕ} {la : Nat.Partition n}
    (p : G n) (hp : p ∈ RowSubgroup n la) :
    MonoidAlgebra.of ℂ (G n) p * RowSymmetrizer n la =
      RowSymmetrizer n la := by
  classical
  simp only [RowSymmetrizer]
  rw [Finset.mul_sum]
  simp_rw [← (MonoidAlgebra.of ℂ (G n)).map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft ⟨p, hp⟩) _ _
    (fun g => by simp [Subgroup.coe_mul])

/-- Column group elements are absorbed on the left of b_λ with sign:
of(q) * b_λ = sign(q) • b_λ for q ∈ Q_λ. -/
theorem of_col_mul_ColumnAntisymmetrizer {n : ℕ} {la : Nat.Partition n}
    (q : G n) (hq : q ∈ ColumnSubgroup n la) :
    MonoidAlgebra.of ℂ (G n) q * ColumnAntisymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • ColumnAntisymmetrizer n la := by
  classical
  simp only [ColumnAntisymmetrizer]
  rw [Finset.mul_sum, Finset.smul_sum]
  simp_rw [Algebra.mul_smul_comm, ← (MonoidAlgebra.of ℂ (G n)).map_mul, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft ⟨q, hq⟩) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  congr 1
  -- Need: sign(g) = sign(q) * sign(q * g), using sign_mul and sign(q)^2 = 1
  have hsqq : ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) * ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) = 1 := by
    have hmul : (Equiv.Perm.sign q : ℤˣ) * (Equiv.Perm.sign q : ℤˣ) = 1 := Int.units_mul_self _
    have h : ((Equiv.Perm.sign q : ℤˣ) : ℤ) * ((Equiv.Perm.sign q : ℤˣ) : ℤ) = 1 := by
      have := congr_arg Units.val hmul
      simp only [Units.val_mul, Units.val_one] at this
      exact this
    exact_mod_cast h
  simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, hsqq, one_mul]

/-- Column group elements are absorbed on the right of b_λ with sign:
b_λ * of(q) = sign(q) • b_λ for q ∈ Q_λ. -/
theorem ColumnAntisymmetrizer_mul_of_col {n : ℕ} {la : Nat.Partition n}
    (q : G n) (hq : q ∈ ColumnSubgroup n la) :
    ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ (G n) q =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • ColumnAntisymmetrizer n la := by
  classical
  simp only [ColumnAntisymmetrizer]
  rw [Finset.sum_mul, Finset.smul_sum]
  simp_rw [Algebra.smul_mul_assoc, ← (MonoidAlgebra.of ℂ (G n)).map_mul, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulRight ⟨q, hq⟩) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul]
  congr 1
  -- Need: sign(g) = sign(q) * sign(g * q), using sign_mul and sign(q)^2 = 1
  have hsqq : ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) * ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) = 1 := by
    have hmul : (Equiv.Perm.sign q : ℤˣ) * (Equiv.Perm.sign q : ℤˣ) = 1 := Int.units_mul_self _
    have h : ((Equiv.Perm.sign q : ℤˣ) : ℤ) * ((Equiv.Perm.sign q : ℤˣ) : ℤ) = 1 := by
      have := congr_arg Units.val hmul
      simp only [Units.val_mul, Units.val_one] at this
      exact this
    exact_mod_cast h
  simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  -- Goal: sg = sq * (sg * sq). Proof: sq*(sg*sq) = sq*sq*sg = 1*sg = sg
  linear_combination -((↑(↑(Equiv.Perm.sign g.val) : ℤ) : ℂ)) * hsqq

end Etingof

open Etingof in
/-- For x ∈ ℂ[S_n], a_λ · x · b_λ is a scalar multiple of c_λ = a_λ · b_λ.
More precisely, there exists a linear functional ℓ_λ on ℂ[S_n] such that
a_λ * x * b_λ = ℓ_λ(x) • c_λ for all x.
(Etingof Lemma 5.13.1) -/
theorem Etingof.Lemma5_13_1
    (n : ℕ) (la : Nat.Partition n) :
    ∃ ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ,
      ∀ x, RowSymmetrizer n la * x * ColumnAntisymmetrizer n la =
        ℓ x • YoungSymmetrizer n la := by
  sorry
