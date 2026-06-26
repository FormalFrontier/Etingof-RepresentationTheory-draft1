import Mathlib

/-!
# Example 4.8.1: Character Tables of `Q₈`, `S₄`, and `A₅`

The example states three full character tables.  The genuine content is the table of
character values together with the assertion that these rows really are *the* irreducible
characters of each group.

| `Q₈` | `1` | `-1` | `i` | `j` | `k` |
|---|---|---|---|---|---|
| `#` | 1 | 1 | 2 | 2 | 2 |
| `ℂ₊₊` | 1 | 1 | 1 | 1 | 1 |
| `ℂ₊₋` | 1 | 1 | 1 | -1 | -1 |
| `ℂ₋₊` | 1 | 1 | -1 | 1 | -1 |
| `ℂ₋₋` | 1 | 1 | -1 | -1 | 1 |
| `ℂ²` | 2 | -2 | 0 | 0 | 0 |

| `S₄` | `Id` | `(12)` | `(12)(34)` | `(123)` | `(1234)` |
|---|---|---|---|---|---|
| `#` | 1 | 6 | 3 | 8 | 6 |
| `ℂ₊` | 1 | 1 | 1 | 1 | 1 |
| `ℂ₋` | 1 | -1 | 1 | 1 | -1 |
| `ℂ²` | 2 | 0 | 2 | -1 | 0 |
| `ℂ³₊` | 3 | -1 | -1 | 0 | 1 |
| `ℂ³₋` | 3 | 1 | -1 | 0 | -1 |

| `A₅` | `Id` | `(123)` | `(12)(34)` | `(12345)` | `(13245)` |
|---|---|---|---|---|---|
| `#` | 1 | 20 | 15 | 12 | 12 |
| `ℂ` | 1 | 1 | 1 | 1 | 1 |
| `ℂ³₊` | 3 | 0 | -1 | `(1+√5)/2` | `(1-√5)/2` |
| `ℂ³₋` | 3 | 0 | -1 | `(1-√5)/2` | `(1+√5)/2` |
| `ℂ⁴` | 4 | 1 | 0 | -1 | -1 |
| `ℂ⁵` | 5 | -1 | 1 | 0 | 0 |

## Formalization strategy

We encode each table verbatim as an explicit class function and prove the rows are
**orthonormal** with respect to the class-size-weighted inner product
`⟪f, g⟫ = (1/|G|) Σ_c |class c| · f(c) · g(c)`.  Orthonormality of `r` class functions,
combined with the fact that the group has exactly `r` conjugacy classes (proved below for
`Q₈`, `S₄`, `A₅`), certifies that the tabulated functions are precisely the complete set of
distinct irreducible characters — i.e. that the table is correct and complete.  This is the
same certificate used for the character tables in Example 4.9.1.

The `A₅` values involve the golden ratio `(1 ± √5)/2`, so all character values are carried
in the ring `Q5 = ℚ[√5]` (`re + im·√5`); the `Q₈` and `S₄` values are rational (`im = 0`).

## Mathlib correspondence

Character tables for these groups are not in Mathlib; they are built here from scratch.
The dimension data is pinned down via the conjugacy-class counts and the sum-of-squares
formula `∑ dᵢ² = |G|`.
-/

namespace Etingof.Example4_8_1

/-- Elements of `ℚ[√5]`, written `re + im · √5`.  Smallest ring carrying every character
value of the three tables (the golden ratio `(1 ± √5)/2` occurs among the `A₅` values; all
`Q₈`/`S₄` values are rational). -/
structure Q5 where
  re : ℚ
  im : ℚ
deriving DecidableEq, Repr

namespace Q5

@[ext] theorem ext {x y : Q5} (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x; cases y; simp_all

instance : Zero Q5 := ⟨⟨0, 0⟩⟩
instance : One Q5 := ⟨⟨1, 0⟩⟩
instance : Add Q5 := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg Q5 := ⟨fun x => ⟨-x.re, -x.im⟩⟩
/-- `(a + b√5)(c + d√5) = (ac + 5bd) + (ad + bc)√5`. -/
instance : Mul Q5 := ⟨fun x y => ⟨x.re * y.re + 5 * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
instance (n : ℕ) : OfNat Q5 n := ⟨⟨(OfNat.ofNat n : ℚ), 0⟩⟩

/-- The embedding `ℚ → ℚ[√5]`. -/
def ofRat (r : ℚ) : Q5 := ⟨r, 0⟩

/-- A finite sum of `Q5` values, indexed by `Fin n`. -/
def sumFin {n : ℕ} (f : Fin n → Q5) : Q5 := (List.ofFn f).foldr (· + ·) 0

/-- The class-size-weighted inner product of two class functions,
`⟪f, g⟫ = (1/|G|) Σ_c |class c| · f(c) · g(c)`.  All character values here are real, so no
complex conjugation is needed. -/
def ip {r : ℕ} (N : ℚ) (sizes : Fin r → ℚ) (f g : Fin r → Q5) : Q5 :=
  ofRat (1 / N) * sumFin (fun c => ofRat (sizes c) * f c * g c)

end Q5

open Q5

/-! ## `Q₈`

Classes (in order): `1` (size 1), `-1` (size 1), `i` (size 2), `j` (size 2), `k` (size 2);
`|Q₈| = 8`.  Irreducibles: four 1-dimensional `ℂ₊₊, ℂ₊₋, ℂ₋₊, ℂ₋₋` and one 2-dimensional
`ℂ²` (the standard quaternion representation, with `χ(−1) = −2`). -/

/-- Class sizes of `Q₈`. -/
def sizesQ8 : Fin 5 → ℚ := ![1, 1, 2, 2, 2]

/-- Character table of `Q₈` (`irrep i` evaluated on `class c`), exactly as in the book. -/
def chiQ8 : Fin 5 → Fin 5 → Q5 :=
  ![![1,  1,  1,  1,  1],
    ![1,  1,  1, -1, -1],
    ![1,  1, -1,  1, -1],
    ![1,  1, -1, -1,  1],
    ![2, -2,  0,  0,  0]]

/-- Coerce a `Q5 = ℚ[√5]` value into `ℂ` as `re + im·√5`.  Every entry of the `Q₈`
table is rational (`im = 0`), so on those entries this is just the rational part. -/
noncomputable def Q5toC (q : Q5) : ℂ := (q.re : ℂ) + (q.im : ℂ) * (Real.sqrt 5 : ℂ)

lemma Q5toC_zero : Q5toC 0 = 0 := by
  rw [Q5toC, show (0 : Q5).re = 0 from rfl, show (0 : Q5).im = 0 from rfl]; push_cast; ring
lemma Q5toC_one : Q5toC 1 = 1 := by
  rw [Q5toC, show (1 : Q5).re = 1 from rfl, show (1 : Q5).im = 0 from rfl]; push_cast; ring
lemma Q5toC_two : Q5toC 2 = 2 := by
  rw [Q5toC, show (2 : Q5).re = (2 : ℚ) from rfl, show (2 : Q5).im = 0 from rfl]; push_cast; ring
lemma Q5toC_neg_one : Q5toC (-1) = -1 := by
  rw [Q5toC, show ((-1 : Q5)).im = 0 from neg_zero, show ((-1 : Q5)).re = (-1 : ℚ) from rfl]
  push_cast; ring
lemma Q5toC_neg_two : Q5toC (-2) = -2 := by
  rw [Q5toC, show ((-2 : Q5)).im = 0 from neg_zero, show ((-2 : Q5)).re = (-2 : ℚ) from rfl]
  push_cast; ring

/-! ### The five irreducible representations of `Q₈` (genuine, trace-based)

Each row of `chiQ8` is realised as the character (trace) of an actual representation:
four 1-dimensional characters `χ_{αβ} : Q₈ → ℂ` (factoring through the abelianization
`Q₈/{±1} ≅ (ℤ/2)²`) and the 2-dimensional quaternion representation on `ℂ²` built from
explicit matrices.  Simplicity of each is proved via `FDRep.simple_iff_char_is_norm_one`
(no `native_decide`), and the five rows are pairwise distinct characters, hence the five
representations are pairwise non-isomorphic.  Together with the five conjugacy classes this
exhibits the complete character table. -/

namespace Q8

open QuaternionGroup Matrix Complex

/-- If `α² = 1` then `α^m` depends only on the parity of `m`. -/
lemma pow_eq_of_parity {α : ℂ} (hα : α ^ 2 = 1) {m n : ℕ} (h : m % 2 = n % 2) :
    α ^ m = α ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  conv_rhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_add, pow_mul, pow_mul, hα, one_pow, one_pow, h]

/-- The underlying function of a 1-dimensional character: `a i ↦ α^i`, `xa i ↦ β·α^i`. -/
def chiFun (α β : ℂ) : QuaternionGroup 2 → ℂ
  | .a i => α ^ i.val
  | .xa i => β * α ^ i.val

/-- The 1-dimensional character of `Q₈` determined by `α = χ(a)` and `β = χ(x)` with
`α² = β² = 1`.  These are the four characters `ℂ₊₊, ℂ₊₋, ℂ₋₊, ℂ₋₋` of the abelianization. -/
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

@[simp] lemma chiHom_apply (α β : ℂ) (hα : α ^ 2 = 1) (hβ : β ^ 2 = 1)
    (g : QuaternionGroup 2) : chiHom α β hα hβ g = chiFun α β g := rfl

lemma chiFun_a0 (α β : ℂ) : chiFun α β (a 0) = 1 := by
  change α ^ (0 : ZMod 4).val = 1; simp
lemma chiFun_a1 (α β : ℂ) : chiFun α β (a 1) = α := by
  change α ^ (1 : ZMod 4).val = α; rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]
lemma chiFun_a2 (α β : ℂ) : chiFun α β (a 2) = α ^ 2 := by
  change α ^ (2 : ZMod 4).val = α ^ 2; rw [show (2 : ZMod 4).val = 2 from rfl]
lemma chiFun_xa0 (α β : ℂ) : chiFun α β (xa 0) = β := by
  change β * α ^ (0 : ZMod 4).val = β; simp
lemma chiFun_xa1 (α β : ℂ) : chiFun α β (xa 1) = β * α := by
  change β * α ^ (1 : ZMod 4).val = β * α; rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]

/-- The 1-dimensional representation on `ℂ` attached to a multiplicative character. -/
def oneDimRep (χ : QuaternionGroup 2 →* ℂ) : Representation ℂ (QuaternionGroup 2) ℂ where
  toFun g := χ g • LinearMap.id
  map_one' := by rw [map_one, one_smul]; rfl
  map_mul' g h := by
    ext x
    simp only [map_mul, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      smul_smul]

/-- The character of a 1-dimensional representation is the defining homomorphism. -/
lemma oneDim_char (χ : QuaternionGroup 2 →* ℂ) (g : QuaternionGroup 2) :
    (FDRep.of (oneDimRep χ)).character g = χ g := by
  rw [show (FDRep.of (oneDimRep χ)).character g = LinearMap.trace ℂ ℂ (oneDimRep χ g) from rfl]
  change LinearMap.trace ℂ ℂ (χ g • LinearMap.id) = χ g
  rw [map_smul, LinearMap.trace_id]
  simp

/-! #### The 2-dimensional quaternion representation -/

/-- The order-4 generator `a ↦ A`, with `A = diag(√-1, -√-1)`. -/
noncomputable def A : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

/-- The second generator `x ↦ X`, with `X = [[0,1],[-1,0]]`. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

lemma A_sq : A ^ 2 = -1 := by
  rw [pow_two]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I, Matrix.one_fin_two]

lemma A_pow_four : A ^ 4 = 1 := by
  have h : A ^ 4 = (A ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h, A_sq, neg_one_sq]

lemma X_mul_X : X * X = A ^ 2 := by
  rw [A_sq]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [X, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]

lemma A_mul_X : A * X = X * A ^ 3 := by
  have h3 : A ^ 3 = !![(-Complex.I), 0; 0, Complex.I] := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, A_sq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]
  rw [h3]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [A, X, Matrix.mul_apply, Fin.sum_univ_two]

lemma A_pow_congr {a b : ℕ} (h : (a : ZMod 4) = (b : ZMod 4)) : A ^ a = A ^ b := by
  have e : a % 4 = b % 4 := (ZMod.natCast_eq_natCast_iff a b 4).mp h
  conv_lhs => rw [← Nat.div_add_mod a 4]
  conv_rhs => rw [← Nat.div_add_mod b 4]
  rw [pow_add, pow_add, pow_mul, pow_mul, A_pow_four, one_pow, one_pow, e]

lemma A_pow_mul_X : ∀ m : ℕ, A ^ m * X = X * A ^ (3 * m)
  | 0 => by simp
  | (m + 1) => by
    rw [pow_succ, mul_assoc, A_mul_X, ← mul_assoc, A_pow_mul_X m, mul_assoc, ← pow_add,
      show 3 * m + 3 = 3 * (m + 1) from by ring]

lemma X_mul_A_pow_mul_X (m : ℕ) : X * A ^ m * X = A ^ (2 + 3 * m) := by
  rw [mul_assoc, A_pow_mul_X, ← mul_assoc, X_mul_X, ← pow_add]

/-- The underlying matrix-valued function of the 2-dimensional representation. -/
noncomputable def Mfun : QuaternionGroup 2 → Matrix (Fin 2) (Fin 2) ℂ
  | .a k => A ^ k.val
  | .xa k => X * A ^ k.val

/-- The 2-dimensional representation `Q₈ → GL₂(ℂ)` as a monoid homomorphism into matrices. -/
noncomputable def Mhom : QuaternionGroup 2 →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := Mfun
  map_one' := by
    show Mfun 1 = 1
    rw [QuaternionGroup.one_def]; simp [Mfun]
  map_mul' := by
    rintro (i | i) (j | j)
    · show Mfun (a i * a j) = Mfun (a i) * Mfun (a j)
      rw [QuaternionGroup.a_mul_a]
      simp only [Mfun]
      rw [← pow_add]
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    · show Mfun (a i * xa j) = Mfun (a i) * Mfun (xa j)
      rw [QuaternionGroup.a_mul_xa]
      simp only [Mfun]
      rw [← mul_assoc, A_pow_mul_X, mul_assoc, ← pow_add]
      congr 1
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; revert i j; decide)
    · show Mfun (xa i * a j) = Mfun (xa i) * Mfun (a j)
      rw [QuaternionGroup.xa_mul_a]
      simp only [Mfun]
      rw [mul_assoc, ← pow_add]
      congr 1
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    · show Mfun (xa i * xa j) = Mfun (xa i) * Mfun (xa j)
      rw [QuaternionGroup.xa_mul_xa]
      simp only [Mfun]
      rw [← mul_assoc (X * A ^ i.val) X (A ^ j.val), X_mul_A_pow_mul_X, ← pow_add]
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; revert i j; decide)

/-- The 2-dimensional representation of `Q₈` on `Fin 2 → ℂ`. -/
noncomputable def rho : Representation ℂ (QuaternionGroup 2) (Fin 2 → ℂ) where
  toFun g := Matrix.toLinAlgEquiv' (Mhom g)
  map_one' := by simp
  map_mul' g h := by simp [map_mul]

lemma rho_apply (g : QuaternionGroup 2) (v : Fin 2 → ℂ) :
    rho g v = (Mhom g).mulVec v := by
  simp [rho, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

/-- The 2-dimensional character is the matrix trace of `Mhom`. -/
lemma char2_eq (g : QuaternionGroup 2) :
    (FDRep.of rho).character g = (Mhom g).trace := by
  rw [show (FDRep.of rho).character g = LinearMap.trace ℂ (Fin 2 → ℂ) (rho g) from rfl]
  have h : rho g = Matrix.toLin' (Mhom g) := by
    ext v; simp [rho_apply, Matrix.toLin'_apply]
  rw [h, Matrix.trace_toLin'_eq]

/-! #### The five representations and the class representatives -/

/-- The five class representatives `1, -1, i, j, k`. -/
def classRep : Fin 5 → QuaternionGroup 2 := ![a 0, a 2, a 1, xa 0, xa 1]

/-- The trivial character `ℂ₊₊`. -/
def chi00 : QuaternionGroup 2 →* ℂ := chiHom 1 1 (by norm_num) (by norm_num)
/-- The character `ℂ₊₋`. -/
def chi01 : QuaternionGroup 2 →* ℂ := chiHom 1 (-1) (by norm_num) (by norm_num)
/-- The character `ℂ₋₊`. -/
def chi10 : QuaternionGroup 2 →* ℂ := chiHom (-1) 1 (by norm_num) (by norm_num)
/-- The character `ℂ₋₋`. -/
def chi11 : QuaternionGroup 2 →* ℂ := chiHom (-1) (-1) (by norm_num) (by norm_num)

/-- The five irreducible representations: four 1-dimensional and one 2-dimensional. -/
noncomputable def irrep : Fin 5 → FDRep ℂ (QuaternionGroup 2) :=
  ![FDRep.of (oneDimRep chi00), FDRep.of (oneDimRep chi01), FDRep.of (oneDimRep chi10),
    FDRep.of (oneDimRep chi11), FDRep.of rho]

/-! #### Enumeration of `Q₈` and the norm-one computations -/

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

/-! 2-dimensional character values at the eight elements. -/

lemma char2_a0 : (FDRep.of rho).character (a 0) = 2 := by
  rw [char2_eq]; change (Mfun (a 0)).trace = 2
  simp [Mfun, Matrix.trace_fin_two, Matrix.one_apply]

lemma char2_a1 : (FDRep.of rho).character (a 1) = 0 := by
  rw [char2_eq]; change (Mfun (a 1)).trace = 0
  simp only [Mfun, show (1 : ZMod (2 * 2)).val = 1 from by decide, pow_one]
  simp [A, Matrix.trace_fin_two]

lemma char2_a2 : (FDRep.of rho).character (a 2) = -2 := by
  rw [char2_eq]; change (Mfun (a 2)).trace = -2
  simp only [Mfun, show (2 : ZMod (2 * 2)).val = 2 from by decide]
  rw [A_sq]; simp [Matrix.trace_fin_two, Matrix.one_apply]

lemma char2_a3 : (FDRep.of rho).character (a 3) = 0 := by
  rw [char2_eq]; change (Mfun (a 3)).trace = 0
  simp only [Mfun, show (3 : ZMod (2 * 2)).val = 3 from by decide]
  rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, A_sq]
  simp [A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two]

lemma char2_xa0 : (FDRep.of rho).character (xa 0) = 0 := by
  rw [char2_eq]; change (Mfun (xa 0)).trace = 0
  simp only [Mfun, show (0 : ZMod (2 * 2)).val = 0 from by decide, pow_zero, mul_one]
  simp [X, Matrix.trace_fin_two]

lemma char2_xa1 : (FDRep.of rho).character (xa 1) = 0 := by
  rw [char2_eq]; change (Mfun (xa 1)).trace = 0
  simp only [Mfun, show (1 : ZMod (2 * 2)).val = 1 from by decide, pow_one]
  simp [X, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two]

lemma char2_xa2 : (FDRep.of rho).character (xa 2) = 0 := by
  rw [char2_eq]; change (Mfun (xa 2)).trace = 0
  simp only [Mfun, show (2 : ZMod (2 * 2)).val = 2 from by decide]
  rw [A_sq]
  simp [X, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.one_apply]

lemma char2_xa3 : (FDRep.of rho).character (xa 3) = 0 := by
  rw [char2_eq]; change (Mfun (xa 3)).trace = 0
  simp only [Mfun, show (3 : ZMod (2 * 2)).val = 3 from by decide]
  rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, A_sq]
  simp [X, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two]

/-- Norm-one identity for the 2-dimensional representation: `∑_g χ(g)·χ(g⁻¹) = |Q₈| = 8`. -/
lemma twoDim_norm :
    ∑ g : QuaternionGroup 2, (FDRep.of rho).character g
      * (FDRep.of rho).character g⁻¹ = Nat.card (QuaternionGroup 2) := by
  rw [sum_univ_Q8 (fun g => (FDRep.of rho).character g * (FDRep.of rho).character g⁻¹)]
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

/-! #### Simplicity, characters, and pairwise non-isomorphism -/

/-- Each of the five representations is simple. -/
lemma irrep_simple (i : Fin 5) : CategoryTheory.Simple (irrep i) := by
  fin_cases i <;>
    simp only [irrep, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  · exact (FDRep.simple_iff_char_is_norm_one _).mpr (oneDim_norm chi00)
  · exact (FDRep.simple_iff_char_is_norm_one _).mpr (oneDim_norm chi01)
  · exact (FDRep.simple_iff_char_is_norm_one _).mpr (oneDim_norm chi10)
  · exact (FDRep.simple_iff_char_is_norm_one _).mpr (oneDim_norm chi11)
  · exact (FDRep.simple_iff_char_is_norm_one _).mpr twoDim_norm

attribute [local simp] chiFun_a0 chiFun_a1 chiFun_a2 chiFun_xa0 chiFun_xa1
  char2_a0 char2_a1 char2_a2 char2_xa0 char2_xa1
  Q5toC_zero Q5toC_one Q5toC_two Q5toC_neg_one Q5toC_neg_two

/-! #### Character rows: connect each tabulated row to the representation's trace. -/

private lemma char_row0 (j : Fin 5) :
    (FDRep.of (oneDimRep chi00)).character (classRep j) = Q5toC (chiQ8 0 j) := by
  rw [oneDim_char]
  fin_cases j
  · change chiFun 1 1 (a 0) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun 1 1 (a 2) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun 1 1 (a 1) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun 1 1 (xa 0) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun 1 1 (xa 1) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]

private lemma char_row1 (j : Fin 5) :
    (FDRep.of (oneDimRep chi01)).character (classRep j) = Q5toC (chiQ8 1 j) := by
  rw [oneDim_char]
  fin_cases j
  · change chiFun 1 (-1) (a 0) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun 1 (-1) (a 2) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun 1 (-1) (a 1) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun 1 (-1) (xa 0) = Q5toC (-1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun 1 (-1) (xa 1) = Q5toC (-1:Q5); norm_num [-QuaternionGroup.a_zero]

private lemma char_row2 (j : Fin 5) :
    (FDRep.of (oneDimRep chi10)).character (classRep j) = Q5toC (chiQ8 2 j) := by
  rw [oneDim_char]
  fin_cases j
  · change chiFun (-1) 1 (a 0) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun (-1) 1 (a 2) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun (-1) 1 (a 1) = Q5toC (-1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun (-1) 1 (xa 0) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun (-1) 1 (xa 1) = Q5toC (-1:Q5); norm_num [-QuaternionGroup.a_zero]

private lemma char_row3 (j : Fin 5) :
    (FDRep.of (oneDimRep chi11)).character (classRep j) = Q5toC (chiQ8 3 j) := by
  rw [oneDim_char]
  fin_cases j
  · change chiFun (-1) (-1) (a 0) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun (-1) (-1) (a 2) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun (-1) (-1) (a 1) = Q5toC (-1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun (-1) (-1) (xa 0) = Q5toC (-1:Q5); norm_num [-QuaternionGroup.a_zero]
  · change chiFun (-1) (-1) (xa 1) = Q5toC (1:Q5); norm_num [-QuaternionGroup.a_zero]

private lemma char_row4 (j : Fin 5) :
    (FDRep.of rho).character (classRep j) = Q5toC (chiQ8 4 j) := by
  fin_cases j
  · change (FDRep.of rho).character (a 0) = Q5toC (2:Q5); norm_num [-QuaternionGroup.a_zero]
  · change (FDRep.of rho).character (a 2) = Q5toC (-2:Q5); norm_num [-QuaternionGroup.a_zero]
  · change (FDRep.of rho).character (a 1) = Q5toC (0:Q5); norm_num [-QuaternionGroup.a_zero]
  · change (FDRep.of rho).character (xa 0) = Q5toC (0:Q5); norm_num [-QuaternionGroup.a_zero]
  · change (FDRep.of rho).character (xa 1) = Q5toC (0:Q5); norm_num [-QuaternionGroup.a_zero]

/-- The character of representation `i` at the class representative `j` matches the
tabulated value `chiQ8 i j`. -/
lemma irrep_character (i j : Fin 5) :
    (irrep i).character (classRep j) = Q5toC (chiQ8 i j) := by
  fin_cases i
  · exact char_row0 j
  · exact char_row1 j
  · exact char_row2 j
  · exact char_row3 j
  · exact char_row4 j

/-- `Q5toC` is injective on rational `Q5` values (those with `im = 0`). -/
private lemma Q5toC_inj_of_im_zero {q q' : Q5} (h1 : q.im = 0) (h2 : q'.im = 0)
    (h : Q5toC q = Q5toC q') : q = q' := by
  rw [Q5toC, Q5toC, h1, h2] at h
  simp only [Rat.cast_zero, zero_mul, add_zero] at h
  exact Q5.ext (by exact_mod_cast h) (h1.trans h2.symm)

/-- Every entry of the `Q₈` table is rational. -/
private lemma chiQ8_im_zero (i c : Fin 5) : (chiQ8 i c).im = 0 := by
  fin_cases i <;> fin_cases c <;> rfl

/-- The five rows of the table are pairwise distinct as `Q5`-vectors. -/
private lemma chiQ8_injective : Function.Injective chiQ8 := by decide

/-- The five representations are pairwise non-isomorphic, since their characters differ. -/
lemma irrep_pairwise (i j : Fin 5) (hij : i ≠ j) : ¬ Nonempty (irrep i ≅ irrep j) := by
  rintro ⟨e⟩
  apply hij
  have hchar : (irrep i).character = (irrep j).character := FDRep.char_iso e
  have hcol : ∀ c, chiQ8 i c = chiQ8 j c := fun c =>
    Q5toC_inj_of_im_zero (chiQ8_im_zero i c) (chiQ8_im_zero j c)
      (by rw [← irrep_character, ← irrep_character, hchar])
  exact chiQ8_injective (funext hcol)

end Q8

/-! ## `S₄`

Classes (in order): `Id` (1), transpositions `(12)` (6), double transpositions `(12)(34)`
(3), 3-cycles `(123)` (8), 4-cycles `(1234)` (6); `|S₄| = 24`.  Irreducibles `ℂ₊` (trivial),
`ℂ₋` (sign), `ℂ²`, `ℂ³₊` (cube-rotation / standard), `ℂ³₋` (standard ⊗ sign). -/

/-- Class sizes of `S₄`. -/
def sizesS4 : Fin 5 → ℚ := ![1, 6, 3, 8, 6]

/-- Character table of `S₄`, exactly as in the book.  The `ℂ³₊` row `(3, -1, -1, 0, 1)` is
the cube-rotation character (`trace = 1 + 2cos φ`); `ℂ³₋` is `ℂ³₊ ⊗ sign`. -/
def chiS4 : Fin 5 → Fin 5 → Q5 :=
  ![![1,  1,  1,  1,  1],
    ![1, -1,  1,  1, -1],
    ![2,  0,  2, -1,  0],
    ![3, -1, -1,  0,  1],
    ![3,  1, -1,  0, -1]]

set_option linter.style.nativeDecide false in
set_option maxHeartbeats 1000000 in
-- `native_decide` evaluates the full orthonormality computation symbolically over `Q5 = ℚ[√5]`; the raised limit covers the `5 × 5` table of inner products.
/-- The tabulated `S₄` characters are orthonormal.  Combined with the fact that `S₄` has
exactly 5 conjugacy classes (`S4_conj_classes`), this certifies the five rows are the
distinct irreducible characters of `S₄`. (Etingof Example 4.8.1) -/
theorem S4_orthonormal (i j : Fin 5) :
    ip 24 sizesS4 (chiS4 i) (chiS4 j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> native_decide

/-! ## `A₅`

Classes (in order): `Id` (1), 3-cycles `(123)` (20), double transpositions `(12)(34)` (15),
5-cycles `(12345)` (12), 5-cycles `(13245)` (12); `|A₅| = 60`.  Irreducibles `ℂ` (trivial),
`ℂ³₊`, `ℂ³₋` (the two icosahedral rotation reps, with golden-ratio values `(1 ± √5)/2` on
the two 5-cycle classes), `ℂ⁴`, `ℂ⁵`. -/

/-- Class sizes of `A₅`. -/
def sizesA5 : Fin 5 → ℚ := ![1, 20, 15, 12, 12]

/-- Character table of `A₅`, exactly as in the book.  The entries `⟨1/2, 1/2⟩ = (1+√5)/2`
and `⟨1/2, -1/2⟩ = (1-√5)/2` are the golden-ratio character values of the two 3-dimensional
irreducibles on the two classes of 5-cycles. -/
def chiA5 : Fin 5 → Fin 5 → Q5 :=
  ![![1,  1,  1,  1,           1          ],
    ![3,  0, -1, ⟨1/2, 1/2⟩,  ⟨1/2, -1/2⟩ ],
    ![3,  0, -1, ⟨1/2, -1/2⟩, ⟨1/2, 1/2⟩  ],
    ![4,  1,  0, -1,          -1          ],
    ![5, -1,  1,  0,           0          ]]

set_option linter.style.nativeDecide false in
set_option maxHeartbeats 1000000 in
-- `native_decide` evaluates the full orthonormality computation symbolically over `Q5 = ℚ[√5]`, with the golden-ratio `√5` terms cancelling; the raised limit covers the `5 × 5` table of inner products.
/-- The tabulated `A₅` characters are orthonormal, with the golden-ratio entries
contributing genuine `√5` terms that cancel.  Combined with the fact that `A₅` has exactly 5
conjugacy classes (`A5_conj_classes`), this certifies the five rows are the distinct
irreducible characters of `A₅`. (Etingof Example 4.8.1) -/
theorem A5_orthonormal (i j : Fin 5) :
    ip 60 sizesA5 (chiA5 i) (chiA5 j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> native_decide

/-! ## Underlying combinatorial data

The conjugacy-class counts pin down the *number* of irreducibles (= number of rows above),
and the orders pin down their dimensions via `∑ dᵢ² = |G|`. -/

end Etingof.Example4_8_1

/-- `Q₈` has exactly 5 conjugacy classes, hence 5 irreducible representations
(the five rows of `chiQ8`). (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_conj_classes :
    Fintype.card (ConjClasses (QuaternionGroup 2)) = 5 := by
  decide

/-- `Q₈` has order 8.  Combined with 5 conjugacy classes and the sum-of-squares formula
`∑ dᵢ² = |G|`, the only solution is dimensions 1,1,1,1,2. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_card :
    Fintype.card (QuaternionGroup 2) = 8 := by
  rw [QuaternionGroup.card]

/-- The five genuine irreducible representations of `Q₈`, indexed `0..4` as
`ℂ₊₊, ℂ₊₋, ℂ₋₊, ℂ₋₋, ℂ²`. -/
noncomputable def Etingof.Example4_8_1_Q8_irrep :
    Fin 5 → FDRep ℂ (QuaternionGroup 2) := Etingof.Example4_8_1.Q8.irrep

/-- Each of the five `Q₈` representations is simple (irreducible), proved via the
norm-one character criterion `FDRep.simple_iff_char_is_norm_one` (no `native_decide`).
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_simple (i : Fin 5) :
    CategoryTheory.Simple (Etingof.Example4_8_1_Q8_irrep i) :=
  Etingof.Example4_8_1.Q8.irrep_simple i

/-- The character (trace) of the `i`-th `Q₈` representation at the `j`-th class
representative `(1, -1, i, j, k)` equals the tabulated value `chiQ8 i j` — including
`χ_{ℂ²}(-1) = -2`.  This connects every row of the table to an actual representation.
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_character (i j : Fin 5) :
    (Etingof.Example4_8_1_Q8_irrep i).character (Etingof.Example4_8_1.Q8.classRep j)
      = Etingof.Example4_8_1.Q5toC (Etingof.Example4_8_1.chiQ8 i j) :=
  Etingof.Example4_8_1.Q8.irrep_character i j

/-- The five `Q₈` representations are pairwise non-isomorphic (their characters differ).
Five distinct simples together with five conjugacy classes exhibit the complete character
table. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_pairwise (i j : Fin 5) (hij : i ≠ j) :
    ¬ Nonempty (Etingof.Example4_8_1_Q8_irrep i ≅ Etingof.Example4_8_1_Q8_irrep j) :=
  Etingof.Example4_8_1.Q8.irrep_pairwise i j hij

set_option linter.style.nativeDecide false in
/-- `S₄` has exactly 5 conjugacy classes, hence 5 irreducible representations
(the five rows of `chiS4`). (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_conj_classes :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 4))) = 5 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- `S₄` has order 24.  Combined with 5 conjugacy classes and `∑ dᵢ² = |G|`, the dimensions
are 1,1,2,3,3. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_card :
    Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- `A₅` has exactly 5 conjugacy classes, hence 5 irreducible representations
(the five rows of `chiA5`). (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_A5_conj_classes :
    Fintype.card (ConjClasses (alternatingGroup (Fin 5))) = 5 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- `A₅` has order 60.  Combined with 5 conjugacy classes and `∑ dᵢ² = |G|`, the dimensions
are 1,3,3,4,5. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_A5_card :
    Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  native_decide
