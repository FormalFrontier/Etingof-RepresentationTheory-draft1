import Mathlib

/-!
# Example 4.3: Irreducible Representations of Q₈

The quaternion group Q₈ = {±1, ±i, ±j, ±k} has 5 conjugacy classes:
{1}, {-1}, {±i}, {±j}, {±k}.

By the sum-of-squares formula d₁² + d₂² + d₃² + d₄² + d₅² = 8,
the dimensions are 1, 1, 1, 1, 2.

The four 1-dimensional representations are pulled back from Q₈/Z(Q₈) ≅ ℤ₂ × ℤ₂.
The 2-dimensional representation `V = ℂ²` of (4.3.1) sends `-1 ↦ -Id` and uses the
Pauli matrices:
- ρ(i) = [[0, 1], [-1, 0]]
- ρ(j) = [[√(-1), 0], [0, -√(-1)]]
- ρ(k) = [[0, -√(-1)], [-√(-1), 0]]

## Mathlib correspondence

Mathlib has `QuaternionGroup`. We model Q₈ as `QuaternionGroup 2`, whose generators
are `a 1` (an order-4 element, the quaternion `i`) and `xa 0` (the quaternion `j`),
with `a 2` the central element `-1`. We build the genuine 2-dimensional representation
of (4.3.1) as a monoid homomorphism into `Matrix (Fin 2) (Fin 2) ℂ` and verify that the
generators map to the Pauli matrices.
-/

open Complex Matrix QuaternionGroup

/-- Q₈ has exactly 5 conjugacy classes, hence 5 irreducible representations.
(Etingof Example 4.3) -/
theorem Etingof.Example4_3_Q8_conj_classes :
    Fintype.card (ConjClasses (QuaternionGroup 2)) = 5 := by
  decide

/-- The sum-of-squares formula for Q₈: 1² + 1² + 1² + 1² + 2² = 8 = |Q₈|. -/
theorem Etingof.Example4_3_Q8_sum_of_squares :
    1 ^ 2 + 1 ^ 2 + 1 ^ 2 + 1 ^ 2 + 2 ^ 2 = Fintype.card (QuaternionGroup 2) := by
  decide

namespace Etingof.Example4_3_Q8

/-! ## The Pauli matrices of (4.3.1) -/

/-- ρ(i) of (4.3.1): the matrix `[[0, 1], [-1, 0]]`. -/
noncomputable def rhoI : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- ρ(j) of (4.3.1): the matrix `diag(√(-1), -√(-1))`. -/
noncomputable def rhoJ : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

/-- ρ(k) of (4.3.1): the matrix `[[0, -√(-1)], [-√(-1), 0]]`. -/
noncomputable def rhoK : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; -Complex.I, 0]

/-! ### The quaternion relations as matrix identities -/

theorem rhoI_sq : rhoI ^ 2 = -1 := by
  simp only [pow_two, rhoI, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two]

theorem rhoJ_sq : rhoJ ^ 2 = -1 := by
  simp only [pow_two, rhoJ, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two, Complex.I_mul_I]

theorem rhoK_sq : rhoK ^ 2 = -1 := by
  simp only [pow_two, rhoK, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two, Complex.I_mul_I]

/-- ρ(i)·ρ(j) = ρ(k): the quaternion relation `ij = k`. -/
theorem rhoI_mul_rhoJ : rhoI * rhoJ = rhoK := by
  simp only [rhoI, rhoJ, rhoK, Matrix.mul_fin_two]
  norm_num [Complex.ext_iff]

/-- ρ(i) and ρ(j) anticommute: `ij = -ji`. -/
theorem rhoI_mul_rhoJ_anticomm : rhoI * rhoJ = -(rhoJ * rhoI) := by
  simp only [rhoI, rhoJ, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.neg_apply]

/-! ### Powers of ρ(i) -/

theorem rhoI_pow_four : rhoI ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, rhoI_sq]; simp

theorem rhoI_pow_three : rhoI ^ 3 = -rhoI := by
  rw [pow_succ, rhoI_sq]; simp

/-- The defining commutation relation `i·j = j·i⁻¹` in matrix form: `ρ(i)·ρ(j) = ρ(j)·ρ(i)³`. -/
theorem rhoI_mul_rhoJ_eq : rhoI * rhoJ = rhoJ * rhoI ^ 3 := by
  rw [rhoI_pow_three, mul_neg, ← rhoI_mul_rhoJ_anticomm]

/-- Reduce a power of ρ(i) modulo 4. -/
theorem rhoI_pow_mod (m : ℕ) : rhoI ^ m = rhoI ^ (m % 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul, rhoI_pow_four, one_pow, one_mul]

/-- If two exponents agree on the cast to `ZMod 4`, the corresponding powers of ρ(i) agree. -/
theorem rhoI_pow_congr {p q : ℕ} (h : (p : ZMod 4) = (q : ZMod 4)) :
    rhoI ^ p = rhoI ^ q := by
  have hmod : p % 4 = q % 4 := (ZMod.natCast_eq_natCast_iff p q 4).mp h
  rw [rhoI_pow_mod p, rhoI_pow_mod q, hmod]

/-- The conjugation rule, iterated: `ρ(i)ᵐ·ρ(j) = ρ(j)·ρ(i)³ᵐ`. -/
theorem rhoI_pow_mul_rhoJ (m : ℕ) : rhoI ^ m * rhoJ = rhoJ * rhoI ^ (3 * m) := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, pow_succ rhoI k, mul_assoc, rhoI_mul_rhoJ_eq, ← mul_assoc, ih,
        mul_assoc, ← pow_add]

/-! ## The 2-dimensional representation -/

/-- The underlying function of the 2-dimensional representation: `a i ↦ ρ(i)ⁱ`,
`xa i ↦ ρ(j)·ρ(i)ⁱ`. -/
noncomputable def repFun : QuaternionGroup 2 → Matrix (Fin 2) (Fin 2) ℂ
  | .a i => rhoI ^ i.val
  | .xa i => rhoJ * rhoI ^ i.val

@[simp] theorem repFun_a (i : ZMod 4) : repFun (a i) = rhoI ^ i.val := rfl
@[simp] theorem repFun_xa (i : ZMod 4) : repFun (xa i) = rhoJ * rhoI ^ i.val := rfl

theorem natCast_val (i : ZMod 4) : ((i.val : ℕ) : ZMod 4) = i := ZMod.natCast_rightInverse i

end Etingof.Example4_3_Q8
