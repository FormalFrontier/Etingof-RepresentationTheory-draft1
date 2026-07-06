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

/-- ρ(i)² = ρ(j)², both equal to `-Id`. -/
theorem rhoJ_sq_eq_rhoI_sq : rhoJ ^ 2 = rhoI ^ 2 := by rw [rhoJ_sq, rhoI_sq]

/-- The conjugation identity that drives the `xa · xa` case:
`ρ(j)·ρ(i)ᵖ·ρ(j) = ρ(i)²·ρ(i)³ᵖ`. -/
theorem rhoJ_mul_pow_mul_rhoJ (p : ℕ) :
    rhoJ * rhoI ^ p * rhoJ = rhoI ^ 2 * rhoI ^ (3 * p) := by
  rw [mul_assoc, rhoI_pow_mul_rhoJ, ← mul_assoc, ← sq, rhoJ_sq_eq_rhoI_sq]

/-- The 2-dimensional representation `V = ℂ²` of (4.3.1), as a monoid homomorphism
`Q₈ = QuaternionGroup 2 →* Matrix (Fin 2) (Fin 2) ℂ`. The generator `a 1` (the quaternion
`i`) maps to ρ(i) and `xa 0` (the quaternion `j`) maps to ρ(j). -/
noncomputable def rep : QuaternionGroup 2 →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := repFun
  map_one' := by
    change repFun (a 0) = 1
    simp only [repFun_a, ZMod.val_zero, pow_zero]
  map_mul' := by
    rintro (i | i) (j | j)
    · -- a i * a j = a (i + j)
      simp only [a_mul_a, repFun_a, ← pow_add]
      exact rhoI_pow_congr (by revert i j; decide)
    · -- a i * xa j = xa (j - i)
      simp only [a_mul_xa, repFun_a, repFun_xa]
      rw [← mul_assoc, rhoI_pow_mul_rhoJ, mul_assoc, ← pow_add]
      congr 1
      exact rhoI_pow_congr (by revert i j; decide)
    · -- xa i * a j = xa (i + j)
      simp only [xa_mul_a, repFun_a, repFun_xa, mul_assoc, ← pow_add]
      congr 1
      exact rhoI_pow_congr (by revert i j; decide)
    · -- xa i * xa j = a (2 + j - i)
      simp only [xa_mul_xa, repFun_a, repFun_xa]
      rw [← mul_assoc, rhoJ_mul_pow_mul_rhoJ, mul_assoc, ← pow_add, ← pow_add]
      exact rhoI_pow_congr (by revert i j; decide)

/-! ### Generator values -/

@[simp] theorem rep_a (i : ZMod 4) : rep (a i) = rhoI ^ i.val := rfl
@[simp] theorem rep_xa (i : ZMod 4) : rep (xa i) = rhoJ * rhoI ^ i.val := rfl

/-- ρ(i) = the first Pauli matrix, the image of the generator `a 1`. -/
theorem rep_i : rep (a 1) = rhoI := by
  rw [rep_a, show ((1 : ZMod (2 * 2)).val) = 1 from rfl, pow_one]

/-- ρ(j) = the second Pauli matrix, the image of the generator `xa 0`. -/
theorem rep_j : rep (xa 0) = rhoJ := by
  rw [rep_xa, show ((0 : ZMod (2 * 2)).val) = 0 from rfl, pow_zero, mul_one]

/-- ρ(k) = the third Pauli matrix; `k = ij` corresponds to `a 1 * xa 0 = xa 3`. -/
theorem rep_k : rep (xa 3) = rhoK := by
  rw [rep_xa, show ((3 : ZMod (2 * 2)).val) = 3 from rfl, rhoI_pow_three, mul_neg,
    ← rhoI_mul_rhoJ_anticomm, rhoI_mul_rhoJ]

/-- ρ(-1) = -Id: the central element `-1 = a 2` of Q₈ acts as `-Id`, as in (4.3.1). -/
theorem rep_neg_one : rep (a 2) = -1 := by
  rw [rep_a, show ((2 : ZMod (2 * 2)).val) = 2 from rfl]; exact rhoI_sq

/-- The same 2-dimensional representation packaged as a Mathlib `Representation`
of Q₈ on `ℂ²`, by viewing each Pauli matrix as a linear endomorphism. -/
noncomputable def repLin : Representation ℂ (QuaternionGroup 2) (Fin 2 → ℂ) :=
  (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin 2)).toAlgHom.toMonoidHom.comp rep

/-- The representation `repLin` acts on the 2-dimensional space `ℂ²`. -/
theorem repLin_dim : Module.finrank ℂ (Fin 2 → ℂ) = 2 := by
  simp

open CategoryTheory Module

/-! ## The four 1-dimensional representations (pulled back from `Q₈/Z(Q₈) ≅ ℤ₂ × ℤ₂`)

The center of `Q₈` is `Z(Q₈) = {±1}` and the quotient `Q₈/Z(Q₈) ≅ ℤ₂ × ℤ₂` is abelian
with four 1-dimensional representations.  Pulled back along the quotient map
`q : Q₈ → Q₈/Z(Q₈)` these give four 1-dimensional representations of `Q₈`.  Concretely a
1-dimensional character `χ` of `Q₈` is determined by the two signs `α = χ(i)` and
`β = χ(j)` with `α² = β² = 1` — it necessarily kills the commutators and the center, so it
factors through `Q₈/Z(Q₈)`.  The four sign choices `(±1, ±1)` give the four characters. -/

/-- If `α² = 1` then `α^m` depends only on the parity of `m`. -/
theorem pow_eq_of_parity {α : ℂ} (hα : α ^ 2 = 1) {m n : ℕ} (h : m % 2 = n % 2) :
    α ^ m = α ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  conv_rhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_add, pow_mul, pow_mul, hα, one_pow, one_pow, h]

/-- The underlying function of a 1-dimensional character: `a i ↦ α^i`, `xa i ↦ β·α^i`. -/
def chiFun (α β : ℂ) : QuaternionGroup 2 → ℂ
  | .a i => α ^ i.val
  | .xa i => β * α ^ i.val

/-- The 1-dimensional character of `Q₈` determined by `α = χ(i)` and `β = χ(j)` with
`α² = β² = 1`.  These are the four characters of the abelianization `Q₈/Z(Q₈) ≅ ℤ₂ × ℤ₂`. -/
def chiHom (α β : ℂ) (hα : α ^ 2 = 1) (hβ : β ^ 2 = 1) : QuaternionGroup 2 →* ℂ where
  toFun := chiFun α β
  map_one' := by change chiFun α β (a 0) = 1; change α ^ (0 : ZMod 4).val = 1; simp
  map_mul' x y := by
    rcases x with i | i <;> rcases y with j | j
    · -- a i * a j = a (i + j)
      change chiFun α β (a i * a j) = chiFun α β (a i) * chiFun α β (a j)
      rw [a_mul_a]
      change α ^ (i + j).val = α ^ i.val * α ^ j.val
      have hp : (i + j).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      rw [← pow_add]
      exact pow_eq_of_parity hα hp
    · -- a i * xa j = xa (j - i)
      change chiFun α β (a i * xa j) = chiFun α β (a i) * chiFun α β (xa j)
      rw [a_mul_xa]
      change β * α ^ (j - i).val = α ^ i.val * (β * α ^ j.val)
      have hp : (j - i).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      have e : α ^ i.val * (β * α ^ j.val) = β * α ^ (i.val + j.val) := by rw [pow_add]; ring
      rw [e]
      exact congrArg (β * ·) (pow_eq_of_parity hα hp)
    · -- xa i * a j = xa (i + j)
      change chiFun α β (xa i * a j) = chiFun α β (xa i) * chiFun α β (a j)
      rw [xa_mul_a]
      change β * α ^ (i + j).val = β * α ^ i.val * α ^ j.val
      have hp : (i + j).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      rw [mul_assoc, ← pow_add]
      exact congrArg (β * ·) (pow_eq_of_parity hα hp)
    · -- xa i * xa j = a (2 + j - i)
      change chiFun α β (xa i * xa j) = chiFun α β (xa i) * chiFun α β (xa j)
      rw [xa_mul_xa]
      change α ^ ((2 : ZMod 4) + j - i).val = β * α ^ i.val * (β * α ^ j.val)
      have hp : ((2 : ZMod 4) + j - i).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      have e : β * α ^ i.val * (β * α ^ j.val) = β ^ 2 * α ^ (i.val + j.val) := by
        rw [pow_add]; ring
      rw [e, hβ, one_mul]
      exact pow_eq_of_parity hα hp

/-- The 1-dimensional representation on `ℂ` attached to a multiplicative character. -/
def oneDimRep (χ : QuaternionGroup 2 →* ℂ) : Representation ℂ (QuaternionGroup 2) ℂ where
  toFun g := χ g • LinearMap.id
  map_one' := by rw [map_one, one_smul]; rfl
  map_mul' g h := by
    ext
    simp only [map_mul, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      smul_smul]

/-- The character of a 1-dimensional representation is the defining homomorphism. -/
lemma oneDim_char (χ : QuaternionGroup 2 →* ℂ) (g : QuaternionGroup 2) :
    (FDRep.of (oneDimRep χ)).character g = χ g := by
  rw [show (FDRep.of (oneDimRep χ)).character g = LinearMap.trace ℂ ℂ (oneDimRep χ g) from rfl]
  change LinearMap.trace ℂ ℂ (χ g • LinearMap.id) = χ g
  rw [map_smul, LinearMap.trace_id]
  simp

/-- The trivial character `ℂ₊₊`, `χ(i) = χ(j) = 1`. -/
def chiPP : QuaternionGroup 2 →* ℂ := chiHom 1 1 (by norm_num) (by norm_num)
/-- The character `ℂ₊₋`, `χ(i) = 1`, `χ(j) = -1`. -/
def chiPM : QuaternionGroup 2 →* ℂ := chiHom 1 (-1) (by norm_num) (by norm_num)
/-- The character `ℂ₋₊`, `χ(i) = -1`, `χ(j) = 1`. -/
def chiMP : QuaternionGroup 2 →* ℂ := chiHom (-1) 1 (by norm_num) (by norm_num)
/-- The character `ℂ₋₋`, `χ(i) = χ(j) = -1`. -/
def chiMM : QuaternionGroup 2 →* ℂ := chiHom (-1) (-1) (by norm_num) (by norm_num)

/-- The four 1-dimensional irreducible representations, as objects of `FDRep ℂ Q₈`. -/
noncomputable def repPP : FDRep ℂ (QuaternionGroup 2) := FDRep.of (oneDimRep chiPP)
noncomputable def repPM : FDRep ℂ (QuaternionGroup 2) := FDRep.of (oneDimRep chiPM)
noncomputable def repMP : FDRep ℂ (QuaternionGroup 2) := FDRep.of (oneDimRep chiMP)
noncomputable def repMM : FDRep ℂ (QuaternionGroup 2) := FDRep.of (oneDimRep chiMM)

/-! ## Enumeration of `Q₈` and the norm-one sums -/

/-- An explicit enumeration of the eight elements of `Q₈`. -/
def enum : Fin 8 → QuaternionGroup 2 :=
  ![a 0, a 1, a 2, a 3, xa 0, xa 1, xa 2, xa 3]

lemma enum_bijective : Function.Bijective enum := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨by decide, by decide⟩

/-- A sum over `Q₈` is the sum of its eight values. -/
lemma sum_univ_Q8 (f : QuaternionGroup 2 → ℂ) :
    ∑ g, f g = f (a 0) + f (a 1) + f (a 2) + f (a 3)
             + f (xa 0) + f (xa 1) + f (xa 2) + f (xa 3) := by
  rw [← Equiv.sum_comp (Equiv.ofBijective enum enum_bijective) f, Fin.sum_univ_eight]
  simp only [Equiv.ofBijective_apply, enum]
  rfl

/-- Norm-one identity for a 1-dimensional character: `∑_g χ(g)·χ(g⁻¹) = |Q₈|`. -/
lemma oneDim_norm (χ : QuaternionGroup 2 →* ℂ) :
    ∑ g : QuaternionGroup 2, (FDRep.of (oneDimRep χ)).character g
      * (FDRep.of (oneDimRep χ)).character g⁻¹ = Nat.card (QuaternionGroup 2) := by
  have hone : ∀ g : QuaternionGroup 2, χ g * χ g⁻¹ = 1 := fun g => by
    rw [← map_mul, mul_inv_cancel, map_one]
  simp only [oneDim_char]
  rw [Finset.sum_congr rfl (fun g _ => hone g), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]

/-! ## The 2-dimensional representation `repLin` as an `FDRep`, and its character -/

/-- The 2-dimensional representation of (4.3.1) packaged as an object of `FDRep ℂ Q₈`. -/
noncomputable def repFD : FDRep ℂ (QuaternionGroup 2) := FDRep.of repLin

lemma repLin_apply (g : QuaternionGroup 2) (v : Fin 2 → ℂ) :
    repLin g v = (rep g).mulVec v := by
  change (Matrix.toLinAlgEquiv' (rep g)) v = _
  rw [Matrix.toLinAlgEquiv'_apply]

/-- The 2-dimensional character is the matrix trace of `rep`. -/
lemma char2_eq (g : QuaternionGroup 2) :
    repFD.character g = (rep g).trace := by
  rw [show repFD.character g = LinearMap.trace ℂ (Fin 2 → ℂ) (repLin g) from rfl]
  have h : repLin g = Matrix.toLin' (rep g) := by
    apply LinearMap.ext; intro v
    rw [repLin_apply, Matrix.toLin'_apply]
  rw [h, Matrix.trace_toLin'_eq]

/-! 2-dimensional character values at the eight elements: `χ(1) = 2`, `χ(-1) = -2`, and `0`
on all six elements of order 4. -/

lemma char2_a0 : repFD.character (a 0) = 2 := by
  rw [char2_eq, rep_a, show (0 : ZMod (2 * 2)).val = 0 from rfl, pow_zero]
  simp

lemma char2_a1 : repFD.character (a 1) = 0 := by
  rw [char2_eq, rep_a, show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one]
  simp [rhoI, Matrix.trace_fin_two]

lemma char2_a2 : repFD.character (a 2) = -2 := by
  rw [char2_eq, rep_a, show (2 : ZMod (2 * 2)).val = 2 from rfl, rhoI_sq]
  simp

lemma char2_a3 : repFD.character (a 3) = 0 := by
  rw [char2_eq, rep_a, show (3 : ZMod (2 * 2)).val = 3 from rfl, rhoI_pow_three]
  simp [rhoI, Matrix.trace_fin_two]

lemma char2_xa0 : repFD.character (xa 0) = 0 := by
  rw [char2_eq, rep_xa, show (0 : ZMod (2 * 2)).val = 0 from rfl, pow_zero, mul_one]
  simp [rhoJ, Matrix.trace_fin_two]

lemma char2_xa1 : repFD.character (xa 1) = 0 := by
  rw [char2_eq, rep_xa, show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one]
  simp [rhoJ, rhoI, Matrix.trace_fin_two]

lemma char2_xa2 : repFD.character (xa 2) = 0 := by
  rw [char2_eq, rep_xa, show (2 : ZMod (2 * 2)).val = 2 from rfl, rhoI_sq]
  simp [rhoJ, Matrix.trace_fin_two]

lemma char2_xa3 : repFD.character (xa 3) = 0 := by
  rw [char2_eq, rep_xa, show (3 : ZMod (2 * 2)).val = 3 from rfl, rhoI_pow_three]
  simp [rhoJ, rhoI, Matrix.trace_fin_two]

/-- Norm-one identity for the 2-dimensional representation: `∑_g χ(g)·χ(g⁻¹) = |Q₈| = 8`. -/
lemma twoDim_norm :
    ∑ g : QuaternionGroup 2, repFD.character g * repFD.character g⁻¹
      = Nat.card (QuaternionGroup 2) := by
  rw [sum_univ_Q8 (fun g => repFD.character g * repFD.character g⁻¹)]
  simp only [show (a 0 : QuaternionGroup 2)⁻¹ = a 0 from by decide,
    show (a 1 : QuaternionGroup 2)⁻¹ = a 3 from by decide,
    show (a 2 : QuaternionGroup 2)⁻¹ = a 2 from by decide,
    show (a 3 : QuaternionGroup 2)⁻¹ = a 1 from by decide,
    show (xa 0 : QuaternionGroup 2)⁻¹ = xa 2 from by decide,
    show (xa 1 : QuaternionGroup 2)⁻¹ = xa 3 from by decide,
    show (xa 2 : QuaternionGroup 2)⁻¹ = xa 0 from by decide,
    show (xa 3 : QuaternionGroup 2)⁻¹ = xa 1 from by decide,
    char2_a0, char2_a1, char2_a2, char2_a3, char2_xa0, char2_xa1, char2_xa2, char2_xa3]
  rw [show Nat.card (QuaternionGroup 2) = 8 from by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]]
  norm_num

/-! ## Irreducibility of all five representations

Each of the five representations is simple, via the character norm-one criterion
`∑_g χ(g)·χ(g⁻¹) = |G|` (`FDRep.simple_iff_char_is_norm_one`). -/

/-- `ℂ₊₊` is irreducible. -/
lemma repPP_simple : Simple repPP :=
  (FDRep.simple_iff_char_is_norm_one _).mpr (oneDim_norm chiPP)
/-- `ℂ₊₋` is irreducible. -/
lemma repPM_simple : Simple repPM :=
  (FDRep.simple_iff_char_is_norm_one _).mpr (oneDim_norm chiPM)
/-- `ℂ₋₊` is irreducible. -/
lemma repMP_simple : Simple repMP :=
  (FDRep.simple_iff_char_is_norm_one _).mpr (oneDim_norm chiMP)
/-- `ℂ₋₋` is irreducible. -/
lemma repMM_simple : Simple repMM :=
  (FDRep.simple_iff_char_is_norm_one _).mpr (oneDim_norm chiMM)

/-- **The 2-dimensional representation of (4.3.1) is irreducible** (Etingof Example 4.3).
Proved from its character: `∑_g χ(g)·χ(g⁻¹) = 2² + (−2)² = 8 = |Q₈|`. -/
lemma repFD_simple : Simple repFD :=
  (FDRep.simple_iff_char_is_norm_one _).mpr twoDim_norm

/-! ## Dimensions: the sum-of-squares decomposition `1² + 1² + 1² + 1² + 2² = 8` -/

lemma repPP_finrank : finrank ℂ (repPP : Type) = 1 := by
  have h := FDRep.char_one repPP
  rw [show repPP = FDRep.of (oneDimRep chiPP) from rfl, oneDim_char, map_one] at h
  exact_mod_cast h.symm

lemma repPM_finrank : finrank ℂ (repPM : Type) = 1 := by
  have h := FDRep.char_one repPM
  rw [show repPM = FDRep.of (oneDimRep chiPM) from rfl, oneDim_char, map_one] at h
  exact_mod_cast h.symm

lemma repMP_finrank : finrank ℂ (repMP : Type) = 1 := by
  have h := FDRep.char_one repMP
  rw [show repMP = FDRep.of (oneDimRep chiMP) from rfl, oneDim_char, map_one] at h
  exact_mod_cast h.symm

lemma repMM_finrank : finrank ℂ (repMM : Type) = 1 := by
  have h := FDRep.char_one repMM
  rw [show repMM = FDRep.of (oneDimRep chiMM) from rfl, oneDim_char, map_one] at h
  exact_mod_cast h.symm

lemma repFD_finrank : finrank ℂ (repFD : Type) = 2 := by
  have h := FDRep.char_one repFD
  rw [show (1 : QuaternionGroup 2) = a 0 from QuaternionGroup.one_def, char2_a0] at h
  exact_mod_cast h.symm

/-- The dimensions `1, 1, 1, 1, 2` of the five irreducible representations realise the
sum-of-squares decomposition `1² + 1² + 1² + 1² + 2² = 8 = |Q₈|`, now tied to the actual
`finrank` of the constructed irreducibles. (Etingof Example 4.3) -/
theorem irreps_dim_sum_of_squares :
    finrank ℂ (repPP : Type) ^ 2 + finrank ℂ (repPM : Type) ^ 2
      + finrank ℂ (repMP : Type) ^ 2 + finrank ℂ (repMM : Type) ^ 2
      + finrank ℂ (repFD : Type) ^ 2 = Fintype.card (QuaternionGroup 2) := by
  rw [repPP_finrank, repPM_finrank, repMP_finrank, repMM_finrank, repFD_finrank]
  decide

/-! ## The center `Z(Q₈) = {±1}` -/

/-- **The center of `Q₈` is `{1, -1} = {a 0, a 2}`** (Etingof Example 4.3).  Here `a 2 = -1`
is the central element acting as `-Id` (see `rep_neg_one`). -/
theorem mem_center_iff (g : QuaternionGroup 2) :
    g ∈ Subgroup.center (QuaternionGroup 2) ↔ g = a 0 ∨ g = a 2 := by
  rw [Subgroup.mem_center_iff]
  revert g
  decide

end Etingof.Example4_3_Q8
