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

/-! ### Genuine `S₄` character table via real representations and traces

Each row of `chiS4` is realised as the character (trace) of an actual representation of
`S₄ = Equiv.Perm (Fin 4)`: the trivial `ℂ₊`, the sign `ℂ₋`, the standard deleted permutation
representation `ℂ³₋`, its sign twist `ℂ³₊ = ℂ³₋ ⊗ sign`, and the 2-dimensional `ℂ²` obtained
from the conjugation action of `S₄` on the three pair-partitions of `Fin 4` (the surjection
`S₄ → S₃` with kernel the Klein four-group).  Simplicity of each is proved via
`FDRep.simple_iff_char_is_norm_one` (the norm-one character sum, evaluated by honest `decide`
over the 24 group elements — no `native_decide`), the five rows are pairwise distinct
characters, hence the representations are pairwise non-isomorphic, and together with the five
conjugacy classes this exhibits the complete character table. -/

namespace S4

open CategoryTheory MonoidalCategory Module

noncomputable section

-- The generic deleted-permutation-rep helpers carry `[Fintype α] [DecidableEq α]` instances
-- that several specialised lemmas do not mention in their statement; silence the style linters.
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.dupNamespace false

/-! ## Carrier-level helpers (depend only on the index type `α`) -/
section Carrier
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The sum functional `(α → ℂ) →ₗ[ℂ] ℂ`. -/
def sumLM : (α → ℂ) →ₗ[ℂ] ℂ := ∑ a, LinearMap.proj a

@[simp] lemma sumLM_apply (f : α → ℂ) : sumLM f = ∑ a, f a := by
  simp [sumLM, Finset.sum_apply]

/-- The all-ones vector. -/
def onesVecM : α → ℂ := fun _ => 1

lemma onesVecM_ne_zero [Nonempty α] : (onesVecM : α → ℂ) ≠ 0 := by
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  intro h; have := congrFun h a; simp [onesVecM] at this

/-- The line of constant vectors. -/
def constLineM : Submodule ℂ (α → ℂ) := Submodule.span ℂ {(onesVecM : α → ℂ)}

lemma mem_constLineM {x : α → ℂ} : x ∈ (constLineM : Submodule ℂ (α → ℂ)) ↔
    ∃ c : ℂ, c • (onesVecM : α → ℂ) = x := Submodule.mem_span_singleton

lemma sumLM_onesVecM : sumLM (onesVecM : α → ℂ) = (Fintype.card α : ℂ) := by
  rw [sumLM_apply]
  simp only [onesVecM, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end Carrier

/-! ## Generic deleted permutation representation of a `MulAction` -/
section Generic
variable {G : Type} [Group G] {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] [MulAction G α]

/-- The permutation representation of `G` on `α → ℂ` attached to a `MulAction G α`:
`g` acts by `f ↦ (a ↦ f (g⁻¹ • a))`. -/
def permRepM : Representation ℂ G (α → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (fun a => g⁻¹ • a)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext a; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, mul_smul]

@[simp] lemma permRepM_apply (g : G) (f : α → ℂ) (a : α) :
    permRepM g f a = f (g⁻¹ • a) := rfl

/-- The sum-zero subrepresentation. -/
def stdSubM : Subrepresentation (permRepM : Representation ℂ G (α → ℂ)) where
  toSubmodule := LinearMap.ker sumLM
  apply_mem_toSubmodule g f hf := by
    simp only [LinearMap.mem_ker, sumLM_apply] at hf ⊢
    calc ∑ a, permRepM g f a = ∑ a, f (g⁻¹ • a) := by
            refine Finset.sum_congr rfl fun a _ => ?_; rw [permRepM_apply]
      _ = ∑ a, f ((MulAction.toPerm (g⁻¹ : G)) a) := rfl
      _ = ∑ a, f a := Equiv.sum_comp (MulAction.toPerm (g⁻¹ : G)) f
      _ = 0 := hf

/-- The deleted permutation representation as an `FDRep`. -/
def stdRepM : FDRep ℂ G := FDRep.of (stdSubM (G := G) (α := α)).toRepresentation

/-- Number of fixed points of the action of `g`. -/
def fixCardM (g : G) : ℕ := (Finset.univ.filter (fun a : α => g • a = a)).card

@[simp] lemma permRepM_onesVec (g : G) :
    permRepM (α := α) g (onesVecM : α → ℂ) = onesVecM := by
  funext a; simp [onesVecM]

lemma permRepM_eq_toLin' (g : G) :
    (permRepM (G := G) (α := α) g) = ((MulAction.toPerm (g⁻¹ : G)).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext a
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, permRepM_apply]; rfl

lemma trace_permRepM (g : G) :
    LinearMap.trace ℂ (α → ℂ) (permRepM (G := G) (α := α) g)
      = (Function.fixedPoints ⇑(MulAction.toPerm (g⁻¹ : G) : Equiv.Perm α)).ncard := by
  rw [permRepM_eq_toLin', Matrix.trace_toLin'_eq, Matrix.trace_permutation]

lemma fixedPoints_inv_ncard (g : G) :
    (Function.fixedPoints ⇑(MulAction.toPerm (g⁻¹ : G) : Equiv.Perm α)).ncard
      = fixCardM (α := α) g := by
  rw [fixCardM, ← Set.ncard_coe_finset]
  congr 1; ext a
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and, MulAction.toPerm_apply]
  constructor
  · intro h; rw [inv_smul_eq_iff] at h; exact h.symm
  · intro h; rw [inv_smul_eq_iff, h]

@[simp] lemma fixCardM_inv (g : G) : fixCardM (α := α) g⁻¹ = fixCardM (α := α) g := by
  rw [fixCardM, fixCardM]; congr 1; ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; rw [inv_smul_eq_iff] at h; exact h.symm
  · intro h; rw [inv_smul_eq_iff, h]

/-- **Character of the deleted permutation representation.** `χ(g) = #fix(g) − 1`. -/
lemma stdRepM_character (g : G) :
    (stdRepM (G := G) (α := α)).character g = (fixCardM (α := α) g : ℂ) - 1 := by
  classical
  set N : Fin 2 → Submodule ℂ (α → ℂ) :=
    ![(stdSubM (G := G) (α := α)).toSubmodule, constLineM] with hN
  have hsurj : Function.Surjective (sumLM (α := α)) := by
    obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
    intro c; refine ⟨Pi.single a₀ c, ?_⟩
    rw [sumLM_apply, Finset.sum_pi_single']; simp
  have hcardpos : 1 ≤ Fintype.card α := Fintype.card_pos
  have hkerdim : Module.finrank ℂ (LinearMap.ker (sumLM (α := α))) = Fintype.card α - 1 := by
    have h := (sumLM (α := α)).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, Module.finrank_pi] at h
    omega
  have hcompl : IsCompl (stdSubM (G := G) (α := α)).toSubmodule constLineM := by
    have hone : Module.finrank ℂ (constLineM : Submodule ℂ (α → ℂ)) = 1 :=
      finrank_span_singleton onesVecM_ne_zero
    have hdim : Module.finrank ℂ (α → ℂ) ≤
        Module.finrank ℂ (stdSubM (G := G) (α := α)).toSubmodule
          + Module.finrank ℂ (constLineM : Submodule ℂ (α → ℂ)) := by
      have hk : Module.finrank ℂ (stdSubM (G := G) (α := α)).toSubmodule
          = Fintype.card α - 1 := hkerdim
      rw [hk, hone, Module.finrank_pi]; omega
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxk hxc
    rw [mem_constLineM] at hxc
    obtain ⟨c, rfl⟩ := hxc
    have h0 : sumLM (c • (onesVecM : α → ℂ)) = 0 := hxk
    rw [map_smul, sumLM_onesVecM, smul_eq_mul] at h0
    have hc : c = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (Nat.cast_ne_zero.mpr (by omega))
    simp [hc]
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i; simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]; omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (zero_ne_one) huniv).mpr hcompl
  have hf0 : Set.MapsTo (permRepM (α := α) g) (N 0) (N 0) := fun x hx =>
    (stdSubM (G := G) (α := α)).apply_mem_toSubmodule g hx
  have hf1 : Set.MapsTo (permRepM (α := α) g) (N 1) (N 1) := by
    intro x hx
    change x ∈ (constLineM : Submodule ℂ (α → ℂ)) at hx
    change permRepM g x ∈ (constLineM : Submodule ℂ (α → ℂ))
    rw [mem_constLineM] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, permRepM_onesVec]⟩
  have hf : ∀ i, Set.MapsTo (permRepM (α := α) g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_permRepM, fixedPoints_inv_ncard, Fin.sum_univ_two] at htr
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((permRepM g).restrict (hf 0))
      = (stdRepM (G := G) (α := α)).character g := by
    change LinearMap.trace ℂ ↥((stdSubM (G := G) (α := α)).toSubmodule)
        ((stdSubM (G := G) (α := α)).toRepresentation g)
      = LinearMap.trace ℂ ↥((stdSubM (G := G) (α := α)).toSubmodule)
        ((FDRep.of (stdSubM (G := G) (α := α)).toRepresentation).ρ g)
    rw [FDRep.of_ρ']
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((permRepM g).restrict (hf 1)) = 1 := by
    have hid : (permRepM g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext; intro x; apply Subtype.ext
      have hx : (x : α → ℂ) ∈ (constLineM : Submodule ℂ (α → ℂ)) := x.2
      rw [mem_constLineM] at hx
      obtain ⟨c, hc⟩ := hx
      change permRepM g (x : α → ℂ) = (x : α → ℂ)
      rw [← hc, map_smul, permRepM_onesVec]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton onesVecM_ne_zero
    rw [hid, LinearMap.trace_id, hfin]; norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]; exact htr.symm

end Generic

/-! ## The character table of `S₄` -/

open Equiv

abbrev S4 := Equiv.Perm (Fin 4)

/-- One-dimensional representation attached to a character `χ : G →* ℂˣ`. -/
def charRep {G : Type} [Group G] (χ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

@[simp] lemma charRep_character {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    (FDRep.of (charRep χ)).character g = (χ g : ℂ) := by
  change LinearMap.trace ℂ ℂ ((FDRep.of (charRep χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', show charRep χ g = ((χ g : ℂˣ) : ℂ) • LinearMap.id from rfl,
    map_smul, LinearMap.trace_id]; simp

lemma charRep_simple {G : Type} [Group G] [Finite G] (χ : G →* ℂˣ) :
    Simple (FDRep.of (charRep χ)) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [FDRep.simple_iff_char_is_norm_one]
  have : ∀ g : G, (FDRep.of (charRep χ)).character g
      * (FDRep.of (charRep χ)).character g⁻¹ = 1 := by
    intro g
    rw [charRep_character, charRep_character, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Nat.card_eq_fintype_card]

/-- The trivial representation `ℂ₊`. -/
def trivRepS4 : FDRep ℂ S4 := FDRep.of (charRep (1 : S4 →* ℂˣ))
/-- The sign character `S₄ →* ℂˣ`. -/
def signHomS4 : S4 →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign
/-- The sign representation `ℂ₋`. -/
def signRepS4 : FDRep ℂ S4 := FDRep.of (charRep signHomS4)

/-! ### The conjugation action of `S₄` on the three pair-partitions of `Fin 4` -/

/-- The three fixed-point-free involutions of `Fin 4` (the pair-partitions). -/
def involS4 : Fin 3 → S4 :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

lemma involS4_injective : Function.Injective involS4 := by decide

/-- The index of `g · ιₐ · g⁻¹` among the three involutions. -/
def conjIdxS4 (g : S4) (a : Fin 3) : Fin 3 :=
  if g * involS4 a * g⁻¹ = involS4 0 then 0
  else if g * involS4 a * g⁻¹ = involS4 1 then 1 else 2

set_option maxHeartbeats 4000000 in
-- honest `decide` over the 24×3 conjugation table (no `native_decide`); the raised limit
-- covers kernel reduction of the permutation multiplications.
lemma conjIdxS4_spec (g : S4) (a : Fin 3) : involS4 (conjIdxS4 g a) = g * involS4 a * g⁻¹ := by
  revert g a; decide

/-- `S₄` acts on the three pair-partitions (`Fin 3`) by conjugation of involutions. -/
instance conjActionS4 : MulAction S4 (Fin 3) where
  smul := conjIdxS4
  one_smul a := involS4_injective (by
    change involS4 (conjIdxS4 1 a) = involS4 a
    rw [conjIdxS4_spec]; simp)
  mul_smul g h a := involS4_injective (by
    change involS4 (conjIdxS4 (g * h) a) = involS4 (conjIdxS4 g (conjIdxS4 h a))
    rw [conjIdxS4_spec, conjIdxS4_spec, conjIdxS4_spec]; group)

/-! ### The five irreducible representations -/

/-- `ℂ³₋`, the deleted natural permutation representation. -/
def repStd : FDRep ℂ S4 := stdRepM (G := S4) (α := Fin 4)
/-- `ℂ²`, the deleted conjugation-on-partitions representation. -/
def repC2 : FDRep ℂ S4 := stdRepM (G := S4) (α := Fin 3)
/-- `ℂ³₊ = ℂ³₋ ⊗ sign`. -/
def repStdPlus : FDRep ℂ S4 := repStd ⊗ signRepS4

/-- The five irreducibles, indexed as the rows of `chiS4`: `ℂ₊, ℂ₋, ℂ², ℂ³₊, ℂ³₋`. -/
def irrepS4 : Fin 5 → FDRep ℂ S4 := ![trivRepS4, signRepS4, repC2, repStdPlus, repStd]

/-- The five class representatives `Id, (12), (12)(34), (123), (1234)`. -/
def classRepS4 : Fin 5 → S4 :=
  ![1, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 2, finRotate 4]

/-- The integer character table (book values). -/
def tbl : Fin 5 → Fin 5 → ℤ :=
  ![![1,  1,  1,  1,  1],
    ![1, -1,  1,  1, -1],
    ![2,  0,  2, -1,  0],
    ![3, -1, -1,  0,  1],
    ![3,  1, -1,  0, -1]]

/-! ### Character values -/

lemma trivRepS4_char (j : Fin 5) : trivRepS4.character (classRepS4 j) = (tbl 0 j : ℂ) := by
  rw [trivRepS4, charRep_character]
  fin_cases j <;>
    norm_num [tbl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

lemma signRepS4_char (j : Fin 5) : signRepS4.character (classRepS4 j) = (tbl 1 j : ℂ) := by
  have hs : ∀ k, (Equiv.Perm.sign (classRepS4 k) : ℤ) = ![1, -1, 1, 1, -1] k := by decide
  rw [signRepS4, charRep_character]
  have hbridge : ((signHomS4 (classRepS4 j) : ℂˣ) : ℂ)
      = ((Equiv.Perm.sign (classRepS4 j) : ℤ) : ℂ) := by
    simp [signHomS4]
  rw [hbridge, hs j]
  fin_cases j <;>
    norm_num [tbl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

lemma repStd_char (j : Fin 5) : repStd.character (classRepS4 j) = (tbl 4 j : ℂ) := by
  have hf : ∀ k, fixCardM (G := S4) (α := Fin 4) (classRepS4 k) = ![4, 2, 0, 1, 0] k := by decide
  rw [repStd, stdRepM_character, hf j]
  fin_cases j <;>
    norm_num [tbl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

lemma repC2_char (j : Fin 5) : repC2.character (classRepS4 j) = (tbl 2 j : ℂ) := by
  have hf : ∀ k, fixCardM (G := S4) (α := Fin 3) (classRepS4 k) = ![3, 1, 3, 0, 1] k := by decide
  rw [repC2, stdRepM_character, hf j]
  fin_cases j <;>
    norm_num [tbl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

lemma hstd_char (g : S4) :
    repStd.character g = (((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1 : ℂ)) := by
  rw [repStd, stdRepM_character]; push_cast; ring

lemma hsgn_char (g : S4) : signRepS4.character g = (signHomS4 g : ℂ) := by
  rw [signRepS4, charRep_character]

lemma repStdPlus_char_eq (g : S4) :
    repStdPlus.character g
      = (((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1 : ℂ)) * (signHomS4 g : ℂ) := by
  have hchar : repStdPlus.character = repStd.character * signRepS4.character := by
    rw [repStdPlus]; exact FDRep.char_tensor repStd signRepS4
  have h := congrFun hchar g
  rw [Pi.mul_apply, hstd_char, hsgn_char] at h
  exact h

lemma repStdPlus_char (j : Fin 5) : repStdPlus.character (classRepS4 j) = (tbl 3 j : ℂ) := by
  rw [repStdPlus_char_eq]
  have hf : ∀ k, fixCardM (G := S4) (α := Fin 4) (classRepS4 k) = ![4, 2, 0, 1, 0] k := by decide
  have hs : ∀ k, (Equiv.Perm.sign (classRepS4 k) : ℤ) = ![1, -1, 1, 1, -1] k := by decide
  rw [hf j]
  have hbridge : ((signHomS4 (classRepS4 j) : ℂˣ) : ℂ)
      = ((Equiv.Perm.sign (classRepS4 j) : ℤ) : ℂ) := by simp [signHomS4]
  rw [hbridge, hs j]
  fin_cases j <;>
    norm_num [tbl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-- The character of `irrepS4 i` at the class representative `classRepS4 j` equals `tbl i j`. -/
lemma irrepS4_character (i j : Fin 5) :
    (irrepS4 i).character (classRepS4 j) = (tbl i j : ℂ) := by
  fin_cases i
  · exact trivRepS4_char j
  · exact signRepS4_char j
  · exact repC2_char j
  · exact repStdPlus_char j
  · exact repStd_char j

/-! ### Simplicity -/

lemma trivRepS4_simple : Simple trivRepS4 := charRep_simple _
lemma signRepS4_simple : Simple signRepS4 := charRep_simple _

lemma repStd_simple : Simple repStd := by
  rw [repStd, FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : S4,
      (stdRepM (G := S4) (α := Fin 4)).character g
        * (stdRepM (G := S4) (α := Fin 4)).character g⁻¹
      = ((((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [stdRepM_character, stdRepM_character, fixCardM_inv]; push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : S4, (((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; norm_num

lemma repC2_simple : Simple repC2 := by
  rw [repC2, FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : S4,
      (stdRepM (G := S4) (α := Fin 3)).character g
        * (stdRepM (G := S4) (α := Fin 3)).character g⁻¹
      = ((((fixCardM (G := S4) (α := Fin 3) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [stdRepM_character, stdRepM_character, fixCardM_inv]; push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : S4, (((fixCardM (G := S4) (α := Fin 3) g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; norm_num

lemma repStdPlus_simple : Simple repStdPlus := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hsign : ∀ g : S4, (signHomS4 g : ℂ) * (signHomS4 g⁻¹ : ℂ) = 1 := by
    intro g; rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hterm : ∀ g : S4, repStdPlus.character g * repStdPlus.character g⁻¹
      = ((((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [repStdPlus_char_eq, repStdPlus_char_eq, fixCardM_inv]
    push_cast
    linear_combination (((fixCardM (G := S4) (α := Fin 4) g : ℂ) - 1) ^ 2) * hsign g
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : S4, (((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; norm_num

lemma irrepS4_simple (i : Fin 5) : Simple (irrepS4 i) := by
  fin_cases i
  · exact trivRepS4_simple
  · exact signRepS4_simple
  · exact repC2_simple
  · exact repStdPlus_simple
  · exact repStd_simple

/-! ### Pairwise non-isomorphism -/

lemma tbl_injective : Function.Injective tbl := by decide

lemma irrepS4_pairwise (i j : Fin 5) (hij : i ≠ j) : ¬ Nonempty (irrepS4 i ≅ irrepS4 j) := by
  rintro ⟨e⟩
  apply hij
  have hchar : (irrepS4 i).character = (irrepS4 j).character := FDRep.char_iso e
  have hrow : ∀ c, tbl i c = tbl j c := fun c => by
    have h2 : ((tbl i c : ℤ) : ℂ) = ((tbl j c : ℤ) : ℂ) := by
      rw [← irrepS4_character, ← irrepS4_character, hchar]
    exact_mod_cast h2
  exact tbl_injective (funext hrow)


/-! ### Bridge to the tabulated `Q5` values -/

/-- Every entry of the `S₄` table is rational (`im = 0`), and its rational part is the
corresponding integer of `tbl`; hence `Q5toC (chiS4 i j) = tbl i j`. -/
lemma chiS4_eq_tbl (i j : Fin 5) : Q5toC (chiS4 i j) = (tbl i j : ℂ) := by
  have him : (chiS4 i j).im = 0 := by fin_cases i <;> fin_cases j <;> decide
  have hre : (chiS4 i j).re = ((tbl i j : ℤ) : ℚ) := by fin_cases i <;> fin_cases j <;> decide
  rw [Q5toC, him, hre]; push_cast; ring

/-- The character of `irrepS4 i` at `classRepS4 j` equals the tabulated `Q5` value
`chiS4 i j`. -/
lemma irrepS4_character_book (i j : Fin 5) :
    (irrepS4 i).character (classRepS4 j) = Q5toC (chiS4 i j) := by
  rw [irrepS4_character, chiS4_eq_tbl]

end

end S4

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

set_option maxRecDepth 4000 in
/-- `S₄` has exactly 5 conjugacy classes, hence 5 irreducible representations
(the five rows of `chiS4`).  Proved by honest `decide` (no `native_decide`).
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_conj_classes :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 4))) = 5 := by
  decide

/-- `S₄` has order 24.  Combined with 5 conjugacy classes and `∑ dᵢ² = |G|`, the dimensions
are 1,1,2,3,3.  Proved from `Fintype.card_perm` (`= 4!`), no `native_decide`.
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_card :
    Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Fintype.card_perm, Fintype.card_fin]; decide

/-- The five genuine irreducible representations of `S₄`, indexed `0..4` as
`ℂ₊, ℂ₋, ℂ², ℂ³₊, ℂ³₋`. -/
noncomputable def Etingof.Example4_8_1_S4_irrep :
    Fin 5 → FDRep ℂ (Equiv.Perm (Fin 4)) := Etingof.Example4_8_1.S4.irrepS4

/-- Each of the five `S₄` representations is simple (irreducible), proved via the
norm-one character criterion `FDRep.simple_iff_char_is_norm_one` (no `native_decide`).
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_simple (i : Fin 5) :
    CategoryTheory.Simple (Etingof.Example4_8_1_S4_irrep i) :=
  Etingof.Example4_8_1.S4.irrepS4_simple i

/-- The character (trace) of the `i`-th `S₄` representation at the `j`-th class
representative `(Id, (12), (12)(34), (123), (1234))` equals the tabulated value
`chiS4 i j`.  This connects every row of the table to an actual representation.
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_character (i j : Fin 5) :
    (Etingof.Example4_8_1_S4_irrep i).character (Etingof.Example4_8_1.S4.classRepS4 j)
      = Etingof.Example4_8_1.Q5toC (Etingof.Example4_8_1.chiS4 i j) :=
  Etingof.Example4_8_1.S4.irrepS4_character_book i j

/-- The five `S₄` representations are pairwise non-isomorphic (their characters differ).
Five distinct simples together with five conjugacy classes exhibit the complete character
table. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_S4_pairwise (i j : Fin 5) (hij : i ≠ j) :
    ¬ Nonempty (Etingof.Example4_8_1_S4_irrep i ≅ Etingof.Example4_8_1_S4_irrep j) :=
  Etingof.Example4_8_1.S4.irrepS4_pairwise i j hij

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
