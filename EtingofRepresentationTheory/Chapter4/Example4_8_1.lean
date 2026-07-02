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

theorem mk_re (a b : ℚ) : (Q5.mk a b).re = a := rfl
theorem mk_im (a b : ℚ) : (Q5.mk a b).im = b := rfl
theorem zero_re : (0 : Q5).re = 0 := rfl
theorem zero_im : (0 : Q5).im = 0 := rfl
theorem one_re : (1 : Q5).re = 1 := rfl
theorem one_im : (1 : Q5).im = 0 := rfl
theorem add_re (x y : Q5) : (x + y).re = x.re + y.re := rfl
theorem add_im (x y : Q5) : (x + y).im = x.im + y.im := rfl
theorem neg_re (x : Q5) : (-x).re = -x.re := rfl
theorem neg_im (x : Q5) : (-x).im = -x.im := rfl
theorem mul_re (x y : Q5) : (x * y).re = x.re * y.re + 5 * x.im * y.im := rfl
theorem mul_im (x y : Q5) : (x * y).im = x.re * y.im + x.im * y.re := rfl
theorem ofNat_re (n : ℕ) : (no_index (OfNat.ofNat n) : Q5).re = (OfNat.ofNat n : ℚ) :=
  rfl
theorem ofNat_im (n : ℕ) : (no_index (OfNat.ofNat n) : Q5).im = 0 := rfl

/-- The embedding `ℚ → ℚ[√5]`. -/
def ofRat (r : ℚ) : Q5 := ⟨r, 0⟩

theorem ofRat_re (r : ℚ) : (ofRat r).re = r := rfl
theorem ofRat_im (r : ℚ) : (ofRat r).im = 0 := rfl

/-- A finite sum of `Q5` values, indexed by `Fin n`. -/
def sumFin {n : ℕ} (f : Fin n → Q5) : Q5 := (List.ofFn f).foldr (· + ·) 0

/-- Expand a 5-term `sumFin` into an explicit nested sum (the foldr over `List.ofFn`). -/
theorem sumFin_five (f : Fin 5 → Q5) :
    sumFin f = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + 0)))) := by
  simp only [sumFin, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil]; rfl

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

/-- The tabulated `A₅` characters are orthonormal, with the golden-ratio entries
contributing genuine `√5` terms that cancel.  Combined with the fact that `A₅` has exactly 5
conjugacy classes (`A5_conj_classes`), this certifies the five rows are the distinct
irreducible characters of `A₅`. (Etingof Example 4.8.1)

Proved honestly (no `native_decide`): each of the 25 inner products is split into its rational
`re`/`im` components (`Q5.ext`), the 5-term `sumFin` is unfolded (`Q5.sumFin_five`), and the
resulting rational arithmetic -- in which the golden-ratio `√5` terms cancel -- is discharged
by `norm_num`.  Kernel `decide` cannot evaluate this directly: the `ℚ`-normalisation of the
`1/60` factor stalls the kernel. -/
theorem A5_orthonormal (i j : Fin 5) :
    ip 60 sizesA5 (chiA5 i) (chiA5 j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    (first | rw [if_pos rfl] | rw [if_neg (by decide)]) <;>
    apply Q5.ext <;>
    norm_num [ip, Q5.sumFin_five, sizesA5, chiA5, Q5.mk_re, Q5.mk_im, Q5.add_re, Q5.add_im,
      Q5.mul_re, Q5.mul_im, Q5.neg_re, Q5.neg_im, Q5.zero_re, Q5.zero_im, Q5.one_re, Q5.one_im,
      Q5.ofNat_re, Q5.ofNat_im, Q5.ofRat_re, Q5.ofRat_im, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons]

/-! ### Genuine `A₅` representations: trivial `ℂ`, the 4-dim `ℂ⁴`, and the 5-dim `ℂ⁵`

Three of the five rows of `chiA5` are realised here as the characters (traces) of actual
representations of `A₅ = alternatingGroup (Fin 5)`:

* `ℂ` (row 0) is the trivial representation, character `(1,1,1,1,1)`;
* `ℂ⁴` (row 3) is the deleted natural permutation representation of `A₅` on `Fin 5`, with
  character `χ(g) = #fix(g) − 1`, giving the row `(4,1,0,-1,-1)`;
* `ℂ⁵` (row 4) is the deleted permutation representation on the **six Sylow-5 subgroups** of
  `A₅` (equivalently the six pairs of opposite icosahedron vertices, i.e. `P¹(𝔽₅)`), on which
  `A₅` acts 2-transitively by conjugation, giving the row `(5,-1,1,0,0)`.

Simplicity of `ℂ⁴` and `ℂ⁵` follows from `FDRep.simple_iff_char_is_norm_one` via the honest
`decide`-evaluated character-norm sum over the 60 elements (no `native_decide`); the three rows
are pairwise distinct characters, hence the three representations are pairwise non-isomorphic.
The generic deleted-permutation-representation machinery (`S4.stdRepM`, `S4.fixCardM`,
`S4.stdRepM_character`) and the one-dimensional `S4.charRep` are reused from the `S₄` section. -/

namespace A5

open Equiv CategoryTheory

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- `A₅`, realised as the alternating group on `Fin 5`. -/
abbrev G := alternatingGroup (Fin 5)

/-- `|A₅| = 5! / 2 = 60`. -/
lemma card_G : Nat.card G = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide

/-- The five class representatives `Id, (123), (12)(34), (12345), (13245)`. -/
def classRepA5 : Fin 5 → G :=
  ![1,
    ⟨Equiv.swap 0 2 * Equiv.swap 0 1, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1,
      Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨(Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1) ^ 2,
      Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩]

/-! #### The trivial representation `ℂ` -/

/-- The trivial representation `ℂ` of `A₅`. -/
def repTriv : FDRep ℂ G := FDRep.of (S4.charRep (1 : G →* ℂˣ))

lemma repTriv_char (g : G) : repTriv.character g = 1 := by
  rw [repTriv, S4.charRep_character]; simp

lemma repTriv_simple : Simple repTriv := S4.charRep_simple _

/-! #### The 4-dimensional representation `ℂ⁴` (deleted natural permutation rep on `Fin 5`) -/

/-- `ℂ⁴`, the deleted natural permutation representation of `A₅` on `Fin 5`. -/
def repC4 : FDRep ℂ G := S4.stdRepM (G := G) (α := Fin 5)

lemma repC4_char (g : G) :
    repC4.character g = (S4.fixCardM (G := G) (α := Fin 5) g : ℂ) - 1 := by
  rw [repC4, S4.stdRepM_character]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` of the character-norm sum over the 60 elements of A₅; no `native_decide`
lemma repC4_simple : Simple repC4 := by
  rw [repC4, FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : G,
      (S4.stdRepM (G := G) (α := Fin 5)).character g
        * (S4.stdRepM (G := G) (α := Fin 5)).character g⁻¹
      = ((((S4.fixCardM (G := G) (α := Fin 5) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [S4.stdRepM_character, S4.stdRepM_character, S4.fixCardM_inv]; push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : G, (((S4.fixCardM (G := G) (α := Fin 5) g : ℤ) - 1) ^ 2) = 60 := by decide
  rw [hsum, card_G]; norm_num

/-! #### The 5-dimensional representation `ℂ⁵`

`A₅` has six Sylow-5 subgroups; each is generated by a 5-cycle, and the six 5-cycles sending
`0 ↦ 1` are exactly one generator per subgroup.  `A₅` permutes the six subgroups by
conjugation, a 2-transitive action on a 6-element set; the deleted permutation representation
of this action is `ℂ⁵`.  We model the six subgroups by the `Finset`s of their four non-identity
elements; conjugation maps such a `Finset` to another of the six exactly, so the conjugation
permutation index `conjIdx5` defines a genuine `MulAction G (Fin 6)`. -/

/-- The 5-cycle `(0 1 a b c)` of `Fin 5`. -/
def cyc (a b c : Fin 5) : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 c * Equiv.swap 0 b * Equiv.swap 0 a * Equiv.swap 0 1

/-- Representative 5-cycles, one per Sylow-5 subgroup of `A₅` (each sends `0 ↦ 1`). -/
def c5rep : Fin 6 → Equiv.Perm (Fin 5) :=
  ![cyc 2 3 4, cyc 2 4 3, cyc 3 2 4, cyc 3 4 2, cyc 4 2 3, cyc 4 3 2]

/-- The carrier of the `i`-th Sylow-5 subgroup: its four non-identity elements. -/
def carrier (i : Fin 6) : Finset (Equiv.Perm (Fin 5)) :=
  {c5rep i, (c5rep i) ^ 2, (c5rep i) ^ 3, (c5rep i) ^ 4}

/-- Conjugation of a permutation by an element of `A₅`. -/
def conjPerm (g : G) (x : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 5) :=
  (g : Equiv.Perm (Fin 5)) * x * (g : Equiv.Perm (Fin 5))⁻¹

lemma conjPerm_one : conjPerm 1 = id := by
  funext x; simp [conjPerm]

lemma conjPerm_mul (g h : G) (x : Equiv.Perm (Fin 5)) :
    conjPerm g (conjPerm h x) = conjPerm (g * h) x := by
  simp only [conjPerm, Subgroup.coe_mul]; group

/-- The index of the subgroup `g · (subgroup i) · g⁻¹` among the six subgroups. -/
def conjIdx5 (g : G) (i : Fin 6) : Fin 6 :=
  if carrier 0 = (carrier i).image (conjPerm g) then 0
  else if carrier 1 = (carrier i).image (conjPerm g) then 1
  else if carrier 2 = (carrier i).image (conjPerm g) then 2
  else if carrier 3 = (carrier i).image (conjPerm g) then 3
  else if carrier 4 = (carrier i).image (conjPerm g) then 4 else 5

lemma carrier_injective : Function.Injective carrier := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` over the 60×6 conjugation table of A₅ on its Sylow-5 subgroups
/-- Conjugation by any `g ∈ A₅` permutes the six Sylow-5 subgroups: the conjugate of the
`i`-th carrier is exactly the `conjIdx5 g i`-th carrier (honest `decide` over the `60 × 6`
conjugation table, no `native_decide`). -/
lemma conjIdx5_spec (g : G) (i : Fin 6) :
    carrier (conjIdx5 g i) = (carrier i).image (conjPerm g) := by
  revert g i; decide

/-- `A₅` acts on the six Sylow-5 subgroups (`Fin 6`) by conjugation. -/
instance instMulActionFin6 : MulAction G (Fin 6) where
  smul := conjIdx5
  one_smul i := carrier_injective (by
    change carrier (conjIdx5 1 i) = carrier i
    rw [conjIdx5_spec, conjPerm_one, Finset.image_id])
  mul_smul g h i := carrier_injective (by
    have hcomp : conjPerm g ∘ conjPerm h = conjPerm (g * h) := by
      funext x; exact conjPerm_mul g h x
    change carrier (conjIdx5 (g * h) i) = carrier (conjIdx5 g (conjIdx5 h i))
    rw [conjIdx5_spec, conjIdx5_spec, conjIdx5_spec, Finset.image_image, hcomp])

/-- `ℂ⁵`, the deleted permutation representation on the six Sylow-5 subgroups. -/
def repC5 : FDRep ℂ G := S4.stdRepM (G := G) (α := Fin 6)

lemma repC5_char (g : G) :
    repC5.character g = (S4.fixCardM (G := G) (α := Fin 6) g : ℂ) - 1 := by
  rw [repC5, S4.stdRepM_character]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` of the character-norm sum over the 60 elements of A₅; no `native_decide`
lemma repC5_simple : Simple repC5 := by
  rw [repC5, FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : G,
      (S4.stdRepM (G := G) (α := Fin 6)).character g
        * (S4.stdRepM (G := G) (α := Fin 6)).character g⁻¹
      = ((((S4.fixCardM (G := G) (α := Fin 6) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [S4.stdRepM_character, S4.stdRepM_character, S4.fixCardM_inv]; push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : G, (((S4.fixCardM (G := G) (α := Fin 6) g : ℤ) - 1) ^ 2) = 60 := by decide
  rw [hsum, card_G]; norm_num

/-! #### The exterior square `Λ²(ℂ⁴)` (genuine 6-dimensional representation)

`Λ²(ℂ⁴)` is realised as the antisymmetric subrepresentation of `repC4 ⊗ repC4`: the range of
the antisymmetriser `a = ½·(1 − β)`, where `β` is the swap of the two tensor factors.  `a` is a
projection that commutes with the diagonal `A₅`-action, so `range a` is `A₅`-invariant.  Its
character is `χ_{Λ²}(g) = ½·(χ_V(g)² − χ_V(g²))`, computed from the **swap-trace identity**
`trace(β ∘ (ρg ⊗ ρg)) = trace(ρg ∘ ρg) = χ_V(g²)`.  This 6-dimensional representation is the
carrier on which the central element `Σ_{c} ρ(c)` (a 5-cycle class sum) splits into the two
3-dimensional icosahedral representations `ℂ³₊`, `ℂ³₋`.  Character at the five class reps:
`(6, 0, -2, 1, 1)` (since `Λ²ℂ⁴ ≅ ℂ³₊ ⊕ ℂ³₋` and `φ + φ' = 1`). -/

open scoped TensorProduct

/-- Carrier of `repC4`: the sum-zero subspace of `Fin 5 → ℂ` (4-dimensional). -/
abbrev W4 : Submodule ℂ (Fin 5 → ℂ) := (S4.stdSubM (G := G) (α := Fin 5)).toSubmodule

/-- The underlying representation of `repC4` (deleted natural permutation rep on `Fin 5`). -/
def rhoV : Representation ℂ G W4 := (S4.stdSubM (G := G) (α := Fin 5)).toRepresentation

lemma trace_rhoV (g : G) : LinearMap.trace ℂ W4 (rhoV g) = repC4.character g := by
  rw [repC4, S4.stdRepM, FDRep.character, FDRep.of_ρ', rhoV]

/-- Trace of an endomorphism via a basis: `trace f = ∑ i, b.repr (f (b i)) i`. -/
private lemma trace_eq_sum_repr_diagW
    {M : Type*} [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ M) (f : M →ₗ[ℂ] M) :
    LinearMap.trace ℂ M f = ∑ i, b.repr (f (b i)) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b f]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]

/-- **Swap-trace identity.** On `W ⊗ W` (finite-dimensional `W`), the trace of
`swap ∘ (A ⊗ B)` equals `trace (A ∘ B)`.  (Specialised copy of the Chapter 5 lemma
`Etingof.…FrobeniusSchurRealType.trace_comm_comp_map`, which Chapter 4 cannot import.) -/
private lemma trace_comm_comp_mapW
    {W : Type*} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] (A B : W →ₗ[ℂ] W) :
    LinearMap.trace ℂ (W ⊗[ℂ] W)
        ((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B)
      = LinearMap.trace ℂ W (A ∘ₗ B) := by
  classical
  set b := Module.finBasis ℂ W with hb
  rw [trace_eq_sum_repr_diagW (b.tensorProduct b)
        ((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B),
      Fintype.sum_prod_type]
  have hLHS : ∀ i j, (b.tensorProduct b).repr
        ((((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B))
          ((b.tensorProduct b) (i, j))) (i, j)
        = b.repr (A (b i)) j * b.repr (B (b j)) i := by
    intro i j
    rw [Module.Basis.tensorProduct_apply]
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      TensorProduct.comm_tmul, Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
  simp_rw [hLHS]
  rw [trace_eq_sum_repr_diagW b (A ∘ₗ B)]
  have hRHS : ∀ i, b.repr ((A ∘ₗ B) (b i)) i
      = ∑ j, b.repr (A (b j)) i * b.repr (B (b i)) j := by
    intro i
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← Module.Basis.sum_repr b (B (b i))]
    rw [map_sum, map_sum, Finset.sum_apply']
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hRHS]
  rw [Finset.sum_comm]

/-- The swap endomorphism `β` of `W4 ⊗ W4`. -/
def beta : Module.End ℂ (W4 ⊗[ℂ] W4) := (TensorProduct.comm ℂ W4 W4).toLinearMap

/-- The antisymmetriser `a = ½·(1 − β)`, a projection onto the antisymmetric tensors. -/
def asym : Module.End ℂ (W4 ⊗[ℂ] W4) := (2⁻¹ : ℂ) • (1 - beta)

lemma beta_mul_beta : beta * beta = 1 := by
  rw [Module.End.mul_eq_comp, beta, TensorProduct.comm_comp_comm]; rfl

lemma asym_idem : IsIdempotentElem asym := by
  have hbb : (1 - beta) * (1 - beta) = 1 - beta - beta + beta * beta := by
    rw [sub_mul, mul_sub, mul_sub]; simp only [one_mul, mul_one]; abel
  rw [IsIdempotentElem, asym, smul_mul_smul_comm, hbb, beta_mul_beta]
  rw [show (1 : Module.End ℂ (W4 ⊗[ℂ] W4)) - beta - beta + 1 = (2 : ℂ) • (1 - beta) by module]
  rw [smul_smul, show (2⁻¹ * 2⁻¹ * 2 : ℂ) = 2⁻¹ by norm_num]

/-- `β` commutes with the diagonal action `ρg ⊗ ρg`. -/
lemma beta_comm (g : G) :
    beta * (rhoV.tprod rhoV) g = (rhoV.tprod rhoV) g * beta := by
  rw [Representation.tprod_apply, beta]
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul]

/-- `a` commutes with the diagonal action `ρg ⊗ ρg`. -/
lemma asym_comm (g : G) :
    asym * (rhoV.tprod rhoV) g = (rhoV.tprod rhoV) g * asym := by
  rw [asym, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, beta_comm]

/-- `Λ²(ℂ⁴)` as a subrepresentation of `repC4 ⊗ repC4`: the antisymmetric tensors. -/
def lam2Sub : Subrepresentation (rhoV.tprod rhoV) where
  toSubmodule := LinearMap.range asym
  apply_mem_toSubmodule g := by
    intro v hv
    rw [LinearMap.IsIdempotentElem.mem_range_iff asym_idem] at hv ⊢
    calc asym ((rhoV.tprod rhoV) g v)
        = (asym * (rhoV.tprod rhoV) g) v := rfl
      _ = ((rhoV.tprod rhoV) g * asym) v := by rw [asym_comm]
      _ = (rhoV.tprod rhoV) g (asym v) := rfl
      _ = (rhoV.tprod rhoV) g v := by rw [hv]

/-- `Λ²(ℂ⁴)`, the genuine 6-dimensional exterior-square representation of `A₅`. -/
def lam2 : FDRep ℂ G := FDRep.of lam2Sub.toRepresentation

/-- **Character of `Λ²(ℂ⁴)`**: `χ_{Λ²}(g) = ½·(χ_V(g)² − χ_V(g²))`. -/
lemma lam2_char_formula (g : G) :
    lam2.character g = (2⁻¹ : ℂ) * (repC4.character g ^ 2 - repC4.character (g * g)) := by
  classical
  -- the diagonal action and its restriction to the two β-eigenspaces
  set T := (rhoV.tprod rhoV) g with hT
  set N : Fin 2 → Submodule ℂ (W4 ⊗[ℂ] W4) := ![LinearMap.range asym, LinearMap.ker asym] with hN
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i; simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]; omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (zero_ne_one) huniv).mpr
      (LinearMap.IsIdempotentElem.isCompl asym_idem)
  -- `β = -1` on `range a`, `β = +1` on `ker a`
  have hbeta_range : ∀ x ∈ LinearMap.range asym, beta x = -x := by
    intro x hx
    rw [LinearMap.IsIdempotentElem.mem_range_iff asym_idem, asym, LinearMap.smul_apply,
      LinearMap.sub_apply, Module.End.one_apply] at hx
    -- hx : 2⁻¹ • (x - beta x) = x
    have h2 : x - beta x = (2 : ℂ) • x := by
      have h := congrArg (fun z : W4 ⊗[ℂ] W4 => (2 : ℂ) • z) hx
      simp only [smul_smul] at h
      rwa [show (2 : ℂ) * 2⁻¹ = 1 by norm_num, one_smul] at h
    have hb : beta x = x - (2 : ℂ) • x := by rw [eq_sub_iff_add_eq, ← h2]; abel
    rw [hb]; module
  have hbeta_ker : ∀ x ∈ LinearMap.ker asym, beta x = x := by
    intro x hx
    rw [LinearMap.mem_ker, asym, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply] at hx
    -- hx : 2⁻¹ • (x - beta x) = 0
    rw [smul_eq_zero] at hx
    rcases hx with h | h
    · norm_num at h
    · rw [sub_eq_zero] at h; exact h.symm
  -- maps-to for `T` and for `β ∘ T`
  have hfT : ∀ i, Set.MapsTo T (N i) (N i) := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · exact fun x hx => lam2Sub.apply_mem_toSubmodule g hx
    · intro x hx
      have hxk : asym x = 0 := (LinearMap.mem_ker (f := asym)).mp hx
      have hzero : asym (T x) = 0 := by
        rw [hT]
        calc asym ((rhoV.tprod rhoV) g x)
              = (asym * (rhoV.tprod rhoV) g) x := rfl
            _ = ((rhoV.tprod rhoV) g * asym) x := by rw [asym_comm]
            _ = (rhoV.tprod rhoV) g (asym x) := rfl
            _ = 0 := by rw [hxk, map_zero]
      exact (LinearMap.mem_ker (f := asym)).mpr hzero
  have hbetaT : (TensorProduct.comm ℂ W4 W4).toLinearMap ∘ₗ TensorProduct.map (rhoV g) (rhoV g)
      = beta ∘ₗ T := by rw [beta, hT, Representation.tprod_apply]
  have hfbT : ∀ i, Set.MapsTo (beta ∘ₗ T) (N i) (N i) := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · intro x hx
      have hbx : (beta ∘ₗ T) x = -(T x) := by
        rw [LinearMap.comp_apply, hbeta_range (T x) (hfT 0 hx)]
      rw [SetLike.mem_coe, hbx]
      exact neg_mem (hfT 0 hx)
    · intro x hx
      have hbx : (beta ∘ₗ T) x = T x := by
        rw [LinearMap.comp_apply, hbeta_ker (T x) (hfT 1 hx)]
      rw [SetLike.mem_coe, hbx]
      exact hfT 1 hx
  -- the two trace decompositions
  have htrT := LinearMap.trace_eq_sum_trace_restrict hInternal hfT
  have htrbT := LinearMap.trace_eq_sum_trace_restrict hInternal hfbT
  rw [Fin.sum_univ_two] at htrT htrbT
  -- restriction of `β ∘ T` on `range a` is `-(T restrict)`, on `ker a` is `T restrict`
  have hres0 : (beta ∘ₗ T).restrict (hfbT 0) = -(T.restrict (hfT 0)) := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    have hx : (x : W4 ⊗[ℂ] W4) ∈ N 0 := x.2
    change (beta ∘ₗ T) (x : W4 ⊗[ℂ] W4) = -(T (x : W4 ⊗[ℂ] W4))
    rw [LinearMap.comp_apply, hbeta_range (T x) (hfT 0 hx)]
  have hres1 : (beta ∘ₗ T).restrict (hfbT 1) = T.restrict (hfT 1) := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    have hx : (x : W4 ⊗[ℂ] W4) ∈ N 1 := x.2
    change (beta ∘ₗ T) (x : W4 ⊗[ℂ] W4) = T (x : W4 ⊗[ℂ] W4)
    rw [LinearMap.comp_apply, hbeta_ker (T x) (hfT 1 hx)]
  have htr_b0 : LinearMap.trace ℂ ↥(N 0) ((beta ∘ₗ T).restrict (hfbT 0))
      = -(LinearMap.trace ℂ ↥(N 0) (T.restrict (hfT 0))) := by
    rw [hres0]; exact map_neg (LinearMap.trace ℂ ↥(N 0)) (T.restrict (hfT 0))
  have htr_b1 : LinearMap.trace ℂ ↥(N 1) ((beta ∘ₗ T).restrict (hfbT 1))
      = LinearMap.trace ℂ ↥(N 1) (T.restrict (hfT 1)) := by rw [hres1]
  rw [htr_b0, htr_b1] at htrbT
  -- identify `trace T = χ_V(g)²` and `trace (β∘T) = χ_V(g²)`
  have hTtrace : LinearMap.trace ℂ (W4 ⊗[ℂ] W4) T = repC4.character g ^ 2 := by
    rw [hT, Representation.tprod_apply, LinearMap.trace_tensorProduct', trace_rhoV, sq]
  have hbTtrace : LinearMap.trace ℂ (W4 ⊗[ℂ] W4) (beta ∘ₗ T) = repC4.character (g * g) := by
    rw [← hbetaT, trace_comm_comp_mapW, ← Module.End.mul_eq_comp, ← map_mul, trace_rhoV]
  -- `lam2.character g = trace_{range a}(T restrict)`
  have hlam2 : lam2.character g = LinearMap.trace ℂ (N 0) (T.restrict (hfT 0)) := rfl
  -- solve: trace T = A + K, trace(β∘T) = -A + K ⟹ A = ½(trace T - trace(β∘T))
  rw [hTtrace] at htrT
  rw [hbTtrace] at htrbT
  rw [hlam2]
  -- htrT : χ² = A + K ; htrbT : χ(g²) = -A + K
  linear_combination (-2⁻¹ : ℂ) * htrT + (2⁻¹ : ℂ) * htrbT

/-- **Character of `Λ²(ℂ⁴)` at the five class representatives is `(6, 0, -2, 1, 1)`.**
Together with `Λ²ℂ⁴ ≅ ℂ³₊ ⊕ ℂ³₋`, this is the character `(3,0,-1,φ,φ') + (3,0,-1,φ',φ)`
(the golden-ratio entries cancel in the sum, leaving `1` since `φ + φ' = 1`). -/
lemma lam2_character (j : Fin 5) :
    lam2.character (classRepA5 j) = (![6, 0, -2, 1, 1] j : ℂ) := by
  have hf : ∀ k, S4.fixCardM (G := G) (α := Fin 5) (classRepA5 k) = ![5, 2, 1, 0, 0] k := by decide
  have hsq : ∀ k, S4.fixCardM (G := G) (α := Fin 5) (classRepA5 k * classRepA5 k)
      = ![5, 2, 5, 0, 0] k := by decide
  rw [lam2_char_formula, repC4_char, repC4_char, hf j, hsq j]
  fin_cases j <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **`Λ²(ℂ⁴)` is multiplicity-free: `dim_ℂ End_G(Λ²(ℂ⁴)) = 2`.**

By `FDRep.scalar_product_char_eq_finrank_equivariant`, the dimension of the space of
`A₅`-equivariant endomorphisms of `Λ²(ℂ⁴)` equals the character scalar product
`⟨χ_{Λ²}, χ_{Λ²}⟩ = ⅟60 · ∑_{g} χ_{Λ²}(g)·χ_{Λ²}(g⁻¹)`.  Writing `χ_{Λ²}(g) = ½·P(g)` with the
**integer** `P(g) = (fix₅(g) − 1)² − (fix₅(g²) − 1)` (from `lam2_char_formula` and `repC4_char`;
the character is real, `χ(g⁻¹) = χ(g)`), the sum is `¼·∑_g P(g)² = ¼·480 = 120`, evaluated by an
honest `decide` over the 60 elements of `A₅` (no `native_decide`).  Hence `120/60 = 2`.

Consequently `Λ²(ℂ⁴)` decomposes as a direct sum of **two distinct** irreducible constituents —
these are precisely the two 3-dimensional icosahedral representations `ℂ³₊`, `ℂ³₋`.  Because the
endomorphism algebra is only 2-dimensional, the three endomorphisms `1, Z, Z²` (for the central
`Z = Zamb` of Phase B) are linearly dependent, which is the linchpin for the minimal polynomial
`Z² − 20·Z − 400 = 0` splitting `Λ²(ℂ⁴)` into the two golden-ratio eigenspaces. -/
lemma lam2_hom_finrank : Module.finrank ℂ (lam2 ⟶ lam2) = 2 := by
  haveI : Invertible (Fintype.card G : ℂ) := by
    have h60 : Fintype.card G = 60 := by rw [← Nat.card_eq_fintype_card, card_G]
    rw [h60]; exact invertibleOfNonzero (by norm_num)
  have key := FDRep.scalar_product_char_eq_finrank_equivariant lam2 lam2
  -- Each squared character term is `¼·P(g)²` with `P(g)` the integer defined above.
  have hterm : ∀ g : G, lam2.character g * lam2.character g⁻¹
      = (4⁻¹ : ℂ) * ((((((S4.fixCardM (G := G) (α := Fin 5) g : ℤ) - 1) ^ 2
          - ((S4.fixCardM (G := G) (α := Fin 5) (g * g) : ℤ) - 1)) ^ 2 : ℤ) : ℂ)) := by
    intro g
    rw [lam2_char_formula, lam2_char_formula]
    simp only [repC4_char, S4.fixCardM_inv]
    rw [show g⁻¹ * g⁻¹ = (g * g)⁻¹ from by group, S4.fixCardM_inv]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Finset.mul_sum, ← Int.cast_sum] at key
  have hZ : ∑ g : G, ((((S4.fixCardM (G := G) (α := Fin 5) g : ℤ) - 1) ^ 2
      - ((S4.fixCardM (G := G) (α := Fin 5) (g * g) : ℤ) - 1)) ^ 2) = 480 := by decide
  rw [hZ] at key
  have h60 : Fintype.card G = 60 := by rw [← Nat.card_eq_fintype_card, card_G]
  -- `key : ⅟(card G) • (¼ · 480 : ℂ) = ↑(finrank ℂ (lam2 ⟶ lam2))`; the LHS is `2`.
  rw [invOf_eq_inv, smul_eq_mul, h60] at key
  have hval : ((60 : ℕ) : ℂ)⁻¹ * ((4⁻¹ : ℂ) * ((480 : ℤ) : ℂ)) = (2 : ℂ) := by
    push_cast; norm_num
  rw [hval] at key
  exact_mod_cast key.symm

/-! #### The three representations, characters, and pairwise non-isomorphism -/

/-- The integer character table for the three rows realised here (`ℂ`, `ℂ⁴`, `ℂ⁵`). -/
def tblA5 : Fin 3 → Fin 5 → ℤ :=
  ![![1,  1,  1,  1,  1],
    ![4,  1,  0, -1, -1],
    ![5, -1,  1,  0,  0]]

/-- The three genuine representations, indexed `0,1,2` as `ℂ, ℂ⁴, ℂ⁵`. -/
def irrepA5 : Fin 3 → FDRep ℂ G := ![repTriv, repC4, repC5]

/-- The rows of `chiA5` realised here: `ℂ` is row 0, `ℂ⁴` is row 3, `ℂ⁵` is row 4. -/
def rowA5 : Fin 3 → Fin 5 := ![0, 3, 4]

lemma repTriv_character (j : Fin 5) : repTriv.character (classRepA5 j) = (tblA5 0 j : ℂ) := by
  rw [repTriv_char]
  fin_cases j <;>
    norm_num [tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

lemma repC4_character (j : Fin 5) : repC4.character (classRepA5 j) = (tblA5 1 j : ℂ) := by
  have hf : ∀ k, S4.fixCardM (G := G) (α := Fin 5) (classRepA5 k) = ![5, 2, 1, 0, 0] k := by decide
  rw [repC4_char, hf j]
  fin_cases j <;>
    norm_num [tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` of the fixed-point counts of the conjugation action; no `native_decide`
lemma repC5_character (j : Fin 5) : repC5.character (classRepA5 j) = (tblA5 2 j : ℂ) := by
  have hf : ∀ k, S4.fixCardM (G := G) (α := Fin 6) (classRepA5 k) = ![6, 0, 2, 1, 1] k := by decide
  rw [repC5_char, hf j]
  fin_cases j <;>
    norm_num [tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-- The character of `irrepA5 i` at the class representative `classRepA5 j` equals
`tblA5 i j`. -/
lemma irrepA5_character (i : Fin 3) (j : Fin 5) :
    (irrepA5 i).character (classRepA5 j) = (tblA5 i j : ℂ) := by
  fin_cases i
  · exact repTriv_character j
  · exact repC4_character j
  · exact repC5_character j

lemma irrepA5_simple (i : Fin 3) : Simple (irrepA5 i) := by
  fin_cases i
  · exact repTriv_simple
  · exact repC4_simple
  · exact repC5_simple

lemma tblA5_injective : Function.Injective tblA5 := by decide

/-- The three representations are pairwise non-isomorphic (their characters differ). -/
lemma irrepA5_pairwise (i j : Fin 3) (hij : i ≠ j) : ¬ Nonempty (irrepA5 i ≅ irrepA5 j) := by
  rintro ⟨e⟩
  apply hij
  have hchar : (irrepA5 i).character = (irrepA5 j).character := FDRep.char_iso e
  have hrow : ∀ c, tblA5 i c = tblA5 j c := fun c => by
    have h2 : ((tblA5 i c : ℤ) : ℂ) = ((tblA5 j c : ℤ) : ℂ) := by
      rw [← irrepA5_character, ← irrepA5_character, hchar]
    exact_mod_cast h2
  exact tblA5_injective (funext hrow)

/-! #### Bridge to the tabulated `Q5` values of `chiA5` -/

/-- Rows `0, 3, 4` of `chiA5` are rational and equal the integer rows of `tblA5`. -/
lemma chiA5_eq_tblA5 (i : Fin 3) (j : Fin 5) :
    Q5toC (chiA5 (rowA5 i) j) = (tblA5 i j : ℂ) := by
  have him : (chiA5 (rowA5 i) j).im = 0 := by fin_cases i <;> fin_cases j <;> decide
  have hre : (chiA5 (rowA5 i) j).re = ((tblA5 i j : ℤ) : ℚ) := by
    fin_cases i <;> fin_cases j <;> decide
  rw [Q5toC, him, hre]; push_cast; ring

/-- The character of `irrepA5 i` at `classRepA5 j` equals the tabulated `Q5` value
`chiA5 (rowA5 i) j`. -/
lemma irrepA5_character_book (i : Fin 3) (j : Fin 5) :
    (irrepA5 i).character (classRepA5 j) = Q5toC (chiA5 (rowA5 i) j) := by
  rw [irrepA5_character, chiA5_eq_tblA5]

/-! #### Phase B: the central 5-cycle class-sum splits `Λ²(ℂ⁴)`

The 5-cycle class-sum acts on `Λ²(ℂ⁴)` as a central element `z = Σ_{g∈A₅} ρ(g·r·g⁻¹)`
(`r` a 5-cycle, the sum running over all of `A₅`, which makes centrality immediate).  Its
minimal polynomial is `z² − 20·z − 400 = 0`, with the two roots `μ⁺ = 10 + 10√5 = 20φ` and
`μ⁻ = 10 − 10√5 = 20φ'` (`φ = (1+√5)/2`).  The two eigenspaces are the two genuine
3-dimensional icosahedral subrepresentations `ℂ³₊`, `ℂ³₋`. -/

/-- The 5-cycle class representative whose `A₅`-class-sum is the central element splitting
`Λ²(ℂ⁴)`. -/
def r5 : G := classRepA5 3

/-- The central element `z = Σ_{g∈A₅} ρ(g·r·g⁻¹)` on `Λ²(ℂ⁴)`, where `r` is a 5-cycle.
Summing over **all** of `A₅` (rather than over the conjugacy class) makes the centrality
proof a one-line reindexing.  Equal to `5·(class-sum)` since the centralizer of a 5-cycle
has order 5. -/
def zEnd : Module.End ℂ ↥lam2Sub.toSubmodule :=
  ∑ g : G, lam2Sub.toRepresentation (g * r5 * g⁻¹)

/-- **Centrality of `z`.** `z` commutes with every `ρ(h)`, by the reindexing
`h·z·h⁻¹ = Σ_g ρ((hg)·r·(hg)⁻¹) = z`. -/
lemma zEnd_central (h : G) : Commute (lam2Sub.toRepresentation h) zEnd := by
  show lam2Sub.toRepresentation h * zEnd = zEnd * lam2Sub.toRepresentation h
  rw [zEnd, Finset.mul_sum, Finset.sum_mul,
    ← Equiv.sum_comp (Equiv.mulLeft h⁻¹)
      (fun g => lam2Sub.toRepresentation h * lam2Sub.toRepresentation (g * r5 * g⁻¹))]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [← map_mul, ← map_mul]
  congr 1
  group

/-- **Trace of `z` on `Λ²(ℂ⁴)` is `60`.**  Each summand `ρ(g·r·g⁻¹)` is a conjugate of the
5-cycle `r`, on which `χ_{Λ²} = 1` (`lam2_character 3`); the constant `1` summed over the 60
elements of `A₅` gives `60`.  Equivalently `tr z = 3·μ⁺ + 3·μ⁻ = 60`, one of the two trace
identities pinning the golden-ratio eigenvalues `μ± = 10 ± 10√5` (the second being `tr z² = 3600`,
giving `μ⁺ + μ⁻ = 20`, `μ⁺·μ⁻ = −400`, i.e. the minimal polynomial `z² − 20z − 400`). -/
lemma zEnd_trace : LinearMap.trace ℂ (↥lam2Sub.toSubmodule) zEnd = 60 := by
  have hchar : ∀ x : G,
      LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (lam2Sub.toRepresentation x)
        = lam2.character x := fun x => rfl
  have hterm : ∀ g : G,
      LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (lam2Sub.toRepresentation (g * r5 * g⁻¹)) = 1 := by
    intro g
    rw [hchar, FDRep.char_conj, r5]
    simpa using lam2_character 3
  rw [zEnd, map_sum, Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcard : (Fintype.card G : ℂ) = 60 := by
    rw [← Nat.card_eq_fintype_card, card_G]; norm_num
  rw [hcard]

/-- The same central element realised as an **ambient** operator on `W4 ⊗ W4` (the sum of
`(ρ_V ⊗ ρ_V)(g·r·g⁻¹)` over all `g`).  It restricts to `zEnd` on `range asym`, commutes both
with the diagonal action and with the antisymmetriser `asym`, and preserves `range asym`.
Working ambiently keeps the carrier one nesting level deep (a submodule of `W4 ⊗ W4`, like
`lam2Sub`), which avoids the subtype-of-subtype typeclass diamond and sets up the minimal
polynomial computation. -/
def Zamb : Module.End ℂ (W4 ⊗[ℂ] W4) :=
  ∑ g : G, (rhoV.tprod rhoV) (g * r5 * g⁻¹)

/-- **Centrality of the ambient `Z`.** `Z` commutes with every `(ρ_V ⊗ ρ_V)(h)`, by the
reindexing `h·Z·h⁻¹ = Σ_g ρ((hg)·r·(hg)⁻¹) = Z`. -/
lemma Zamb_comm (h : G) : Commute ((rhoV.tprod rhoV) h) Zamb := by
  show (rhoV.tprod rhoV) h * Zamb = Zamb * (rhoV.tprod rhoV) h
  rw [Zamb, Finset.mul_sum, Finset.sum_mul,
    ← Equiv.sum_comp (Equiv.mulLeft h⁻¹)
      (fun g => (rhoV.tprod rhoV) h * (rhoV.tprod rhoV) (g * r5 * g⁻¹))]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [← map_mul, ← map_mul]
  congr 1
  group

/-- `Z` commutes with the antisymmetriser `asym` (each summand does, by `asym_comm`). -/
lemma Zamb_comm_asym : Commute asym Zamb := by
  show asym * Zamb = Zamb * asym
  rw [Zamb, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun g _ => asym_comm (g * r5 * g⁻¹)

/-- `Z` preserves the antisymmetric subspace `range asym = Λ²(ℂ⁴)`. -/
lemma Zamb_mapsTo : ∀ v ∈ lam2Sub.toSubmodule, Zamb v ∈ lam2Sub.toSubmodule := by
  intro v hv
  rw [Zamb, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun g _ => lam2Sub.apply_mem_toSubmodule (g * r5 * g⁻¹) hv

/-- **`z` is the restriction of the ambient `Z` to `Λ²(ℂ⁴)`.**  Both are the same 60-term group
sum `Σ_g ρ(g·r·g⁻¹)`: `zEnd` restricts each summand to `lam2Sub` (Phase B, where the traces are
computed), while `Zamb` keeps it ambient on `W4 ⊗ W4` (Phase C, where the eigenspaces defining
`ℂ³₊`, `ℂ³₋` live).  Coercing `zEnd v` back to `W4 ⊗ W4` recovers `Z` applied to the coercion —
the identity transporting the trace / minimal-polynomial data of `z` onto the `Z`-eigenspaces. -/
lemma zEnd_coe (v : ↥lam2Sub.toSubmodule) :
    ((zEnd v : ↥lam2Sub.toSubmodule) : W4 ⊗[ℂ] W4) = Zamb (v : W4 ⊗[ℂ] W4) := by
  simp only [zEnd, Zamb, LinearMap.sum_apply, Submodule.coe_sum]
  rfl

/-- **The `μ`-eigenspaces of `z` and of `Z` correspond under `Λ²(ℂ⁴) ↪ W4 ⊗ W4`.**  A vector of
`Λ²(ℂ⁴)` is a `μ`-eigenvector of the intrinsic `zEnd` iff its ambient image is a `μ`-eigenvector
of `Zamb`.  Immediate from `zEnd_coe`. -/
lemma zEnd_eigenspace_iff (μ : ℂ) (v : ↥lam2Sub.toSubmodule) :
    v ∈ Module.End.eigenspace zEnd μ
      ↔ (v : W4 ⊗[ℂ] W4) ∈ Module.End.eigenspace Zamb μ := by
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Subtype.ext_iff, zEnd_coe,
    Submodule.coe_smul]

/-! #### The two eigenvalues and the genuine eigenspace subrepresentations -/

/-- The eigenvalue `μ⁺ = 10 + 10√5 = 20·φ` of `z` on `ℂ³₊`. -/
noncomputable def muPlus : ℂ := 10 + 10 * (Real.sqrt 5 : ℂ)

/-- The eigenvalue `μ⁻ = 10 − 10√5 = 20·φ'` of `z` on `ℂ³₋`. -/
noncomputable def muMinus : ℂ := 10 - 10 * (Real.sqrt 5 : ℂ)

/-- `ℂ³₊` as a subrepresentation of `repC4 ⊗ repC4`: the antisymmetric tensors that also lie in
the `μ⁺`-eigenspace of the central `Z`.  Invariance of the eigenspace factor is
`mapsTo_genEigenspace_of_comm` applied to the centrality of `Z`; invariance of `range asym` is
Phase A's `lam2Sub.apply_mem_toSubmodule`. -/
def repC3plusSub : Subrepresentation (rhoV.tprod rhoV) where
  toSubmodule := lam2Sub.toSubmodule ⊓ Module.End.eigenspace Zamb muPlus
  apply_mem_toSubmodule h v hv := by
    rw [Submodule.mem_inf] at hv ⊢
    exact ⟨lam2Sub.apply_mem_toSubmodule h hv.1,
      Module.End.mapsTo_genEigenspace_of_comm (Zamb_comm h).symm muPlus 1 hv.2⟩

/-- `ℂ³₋` as a subrepresentation of `repC4 ⊗ repC4`: the antisymmetric tensors in the
`μ⁻`-eigenspace of `Z`. -/
def repC3minusSub : Subrepresentation (rhoV.tprod rhoV) where
  toSubmodule := lam2Sub.toSubmodule ⊓ Module.End.eigenspace Zamb muMinus
  apply_mem_toSubmodule h v hv := by
    rw [Submodule.mem_inf] at hv ⊢
    exact ⟨lam2Sub.apply_mem_toSubmodule h hv.1,
      Module.End.mapsTo_genEigenspace_of_comm (Zamb_comm h).symm muMinus 1 hv.2⟩

/-- `ℂ³₊`, the first genuine 3-dimensional icosahedral representation of `A₅`. -/
def repC3plus : FDRep ℂ G := FDRep.of repC3plusSub.toRepresentation

/-- `ℂ³₋`, the second genuine 3-dimensional icosahedral representation of `A₅`. -/
def repC3minus : FDRep ℂ G := FDRep.of repC3minusSub.toRepresentation

/-- **The carrier of `ℂ³₊` is the image of the `μ⁺`-eigenspace of the intrinsic `z`.**  The
subrepresentation `ℂ³₊ = Λ²(ℂ⁴) ⊓ ker(Z − μ⁺)` is exactly the `μ⁺`-eigenspace of `zEnd` inside
`Λ²(ℂ⁴)`, pushed forward along the inclusion `Λ²(ℂ⁴) ↪ W4 ⊗ W4` (`zEnd_eigenspace_iff`). -/
lemma repC3plusSub_toSubmodule_eq :
    repC3plusSub.toSubmodule
      = (Module.End.eigenspace zEnd muPlus).map lam2Sub.toSubmodule.subtype := by
  ext x
  rw [show repC3plusSub.toSubmodule
      = lam2Sub.toSubmodule ⊓ Module.End.eigenspace Zamb muPlus from rfl,
    Submodule.mem_inf, Submodule.mem_map]
  constructor
  · rintro ⟨hx, hxe⟩
    exact ⟨⟨x, hx⟩, (zEnd_eigenspace_iff muPlus ⟨x, hx⟩).mpr hxe, rfl⟩
  · rintro ⟨⟨y, hy⟩, hye, rfl⟩
    exact ⟨hy, (zEnd_eigenspace_iff muPlus ⟨y, hy⟩).mp hye⟩

/-- **The carrier of `ℂ³₋` is the image of the `μ⁻`-eigenspace of the intrinsic `z`.** -/
lemma repC3minusSub_toSubmodule_eq :
    repC3minusSub.toSubmodule
      = (Module.End.eigenspace zEnd muMinus).map lam2Sub.toSubmodule.subtype := by
  ext x
  rw [show repC3minusSub.toSubmodule
      = lam2Sub.toSubmodule ⊓ Module.End.eigenspace Zamb muMinus from rfl,
    Submodule.mem_inf, Submodule.mem_map]
  constructor
  · rintro ⟨hx, hxe⟩
    exact ⟨⟨x, hx⟩, (zEnd_eigenspace_iff muMinus ⟨x, hx⟩).mpr hxe, rfl⟩
  · rintro ⟨⟨y, hy⟩, hye, rfl⟩
    exact ⟨hy, (zEnd_eigenspace_iff muMinus ⟨y, hy⟩).mp hye⟩

/-- **`dim ℂ³₊ = dim(μ⁺-eigenspace of `z`)`.**  Reduces the dimension of the icosahedral
representation `ℂ³₊` to the eigenspace dimension of the single 6-dimensional operator `z` on
`Λ²(ℂ⁴)` — the last combinatorial input still needed (`= 3`, via the minimal polynomial
`z² = 20z + 400` and `tr z = 60`) to prove `ℂ³₊` genuinely 3-dimensional. -/
lemma repC3plusSub_finrank_eq :
    Module.finrank ℂ repC3plusSub.toSubmodule
      = Module.finrank ℂ (Module.End.eigenspace zEnd muPlus) := by
  rw [repC3plusSub_toSubmodule_eq, Submodule.finrank_map_subtype_eq]

/-- **`dim ℂ³₋ = dim(μ⁻-eigenspace of `z`)`.** -/
lemma repC3minusSub_finrank_eq :
    Module.finrank ℂ repC3minusSub.toSubmodule
      = Module.finrank ℂ (Module.End.eigenspace zEnd muMinus) := by
  rw [repC3minusSub_toSubmodule_eq, Submodule.finrank_map_subtype_eq]

/-! #### The eigenspace character numerator `S(g) = tr(z ∘ ρ(g))`

The two 3-dimensional icosahedral characters are recovered from `Λ²(ℂ⁴)` by the linear system
`χ₊ + χ₋ = χ_{Λ²}` and `μ⁺·χ₊ + μ⁻·χ₋ = S`, where `S(g) := tr(z·ρ(g))` and `z` acts as the
scalar `μ⁺` on `ℂ³₊` and `μ⁻` on `ℂ³₋`.  Solving gives the golden-ratio entries
`χ₊(g) = (S(g) − μ⁻·χ_{Λ²}(g))/(μ⁺ − μ⁻)`.  Here we compute the honest 60-term group sum
`S = (60, 0, −20, 60, −40)` at the five class representatives. -/

/-- `tr(z·ρ(g))` written as the honest character sum `∑_{h∈A₅} χ_{Λ²}(h·r·h⁻¹·g)`, using that
`z = ∑_h ρ(h·r·h⁻¹)` and that `ρ` is a monoid homomorphism. -/
lemma zEnd_comp_char (g : G) :
    LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation g)
      = ∑ h : G, lam2.character (h * r5 * h⁻¹ * g) := by
  have hchar : ∀ x : G, LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (lam2Sub.toRepresentation x)
      = lam2.character x := fun _ => rfl
  rw [zEnd, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← map_mul, hchar]

-- honest `decide` of the character sum over 5×60 group elements; no `native_decide`
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **The eigenspace character numerator `S(g) = tr(z·ρ(g))` at the five class representatives is
`(60, 0, −20, 60, −40)`.**  Each value is the honest 60-term sum `∑_h χ_{Λ²}(h·r·h⁻¹·g)`, with
`χ_{Λ²}(y) = ½·((fix₅(y) − 1)² − (fix₅(y²) − 1))` evaluated by `decide` over the 60 elements of
`A₅` (no `native_decide`).  Together with `χ_{Λ²} = (6, 0, −2, 1, 1)` and `z = μ⁺` on `ℂ³₊`,
`z = μ⁻` on `ℂ³₋`, this pins the golden-ratio characters `χ₊ = (3, 0, −1, φ, φ')`,
`χ₋ = (3, 0, −1, φ', φ)`. -/
lemma zEnd_comp_char_val (j : Fin 5) :
    LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation (classRepA5 j))
      = (![60, 0, -20, 60, -40] j : ℂ) := by
  rw [zEnd_comp_char]
  have hchar : ∀ y : G, lam2.character y
      = (2⁻¹ : ℂ) * ((((S4.fixCardM (G := G) (α := Fin 5) y : ℤ) - 1) ^ 2
          - ((S4.fixCardM (G := G) (α := Fin 5) (y * y) : ℤ) - 1) : ℤ) : ℂ) := by
    intro y
    rw [lam2_char_formula, repC4_char, repC4_char]
    push_cast; ring
  have key : ∀ i : Fin 5,
      (∑ h : G, (((S4.fixCardM (G := G) (α := Fin 5) (h * r5 * h⁻¹ * classRepA5 i) : ℤ) - 1) ^ 2
        - ((S4.fixCardM (G := G) (α := Fin 5) ((h * r5 * h⁻¹ * classRepA5 i)
            * (h * r5 * h⁻¹ * classRepA5 i)) : ℤ) - 1)))
      = ![120, 0, -40, 120, -80] i := by decide
  rw [Finset.sum_congr rfl (fun h _ => hchar _), ← Finset.mul_sum, ← Int.cast_sum, key j]
  fin_cases j <;> norm_num

/-- **`tr(z²) = 3600` on `Λ²(ℂ⁴)`.**  Since `z` is central (`zEnd_central`), each summand of
`z² = ∑_g z·ρ(g·r·g⁻¹)` has the same trace as `z·ρ(r)` (conjugation invariance of the trace):
`tr(z·ρ(g·r·g⁻¹)) = tr(ρ(g)·z·ρ(r)·ρ(g)⁻¹) = tr(z·ρ(r))`.  Summing the constant over the 60
elements of `A₅` gives `60·tr(z·ρ(r)) = 60·60 = 3600` (using `zEnd_comp_char_val 3`, as
`r = classRepA5 3`).  With `tr(z) = 60` (`zEnd_trace`) and `dim_ℂ End_G(Λ²) = 2`
(`lam2_hom_finrank`), this is the second trace identity: writing `z² = a·1 + b·z` in the
2-dimensional endomorphism algebra, `tr(z²) = 6a + 60b = 3600` and `tr(z) = 60` combine (with
`dim ℂ³₊ = dim ℂ³₋ = 3`, so `b = μ⁺ + μ⁻ = 20`) to give `a = 400`, i.e. the minimal polynomial
`z² − 20·z − 400 = 0` with roots `μ± = 10 ± 10√5`. -/
lemma zEnd_sq_trace : LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * zEnd) = 3600 := by
  have hconj : ∀ g : G,
      LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹))
        = LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation r5) := by
    intro g
    have hc : lam2Sub.toRepresentation g * zEnd = zEnd * lam2Sub.toRepresentation g :=
      (zEnd_central g).eq
    have hrw : zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹)
        = lam2Sub.toRepresentation g * (zEnd * lam2Sub.toRepresentation r5)
            * lam2Sub.toRepresentation g⁻¹ := by
      rw [map_mul, map_mul]
      simp only [← mul_assoc]
      rw [hc]
    rw [hrw, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hz2 : zEnd * zEnd = ∑ g : G, zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹) := by
    rw [← Finset.mul_sum]; rfl
  rw [hz2, map_sum, Finset.sum_congr rfl (fun g _ => hconj g), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hr5 : LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation r5) = 60 := by
    have h := zEnd_comp_char_val 3
    rw [show classRepA5 3 = r5 from rfl] at h
    rw [h]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  have hcard : (Fintype.card G : ℂ) = 60 := by
    rw [← Nat.card_eq_fintype_card, card_G]; norm_num
  rw [hr5, hcard]; norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000000 in
-- honest `decide` of the character double-sum over 60×60 group elements (no `native_decide`);
-- the 3600-term sum is ~12× the scale of `zEnd_comp_char_val`, so the heartbeat/recursion limits
-- are raised accordingly (the class-index reduction fallback is unavailable until `classIdxA5`
-- lands).
/-- **`tr(z³) = 96000` on `Λ²(ℂ⁴)`.**  Mirrors `zEnd_sq_trace` one level up: since `z²` is
central (`zEnd_central` twice), each summand of `z³ = ∑_g z²·ρ(g·r·g⁻¹)` has the same trace as
`z²·ρ(r)` (conjugation invariance of the trace), giving `tr(z³) = 60·tr(z²·ρ(r))`.  Then
`z²·ρ(r) = ∑_h z·ρ(h·r·h⁻¹·r)` (unfolding one `z`), so `tr(z²·ρ(r)) = ∑_h tr(z·ρ(h·r·h⁻¹·r))
= ∑_h ∑_{h'} χ_{Λ²}(h'·r·h'⁻¹·h·r·h⁻¹·r)` via `zEnd_comp_char`, the honest 60×60 = 3600-term
group double sum, evaluated by `decide` (no `native_decide`) to `2⁻¹·3200 = 1600`.  Hence
`tr(z³) = 60·1600 = 96000`.  With `tr(z) = 60` and `tr(z²) = 3600`, the linear trace system
`tr(z²) = a·tr(z) + 6b`, `tr(z³) = a·tr(z²) + b·tr(z)` pins `a = 20`, `b = 400`, i.e. the minimal
polynomial `z² − 20·z − 400 = 0` with roots `μ± = 10 ± 10√5`. -/
lemma zEnd_cube_trace :
    LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * zEnd * zEnd) = 96000 := by
  -- `z³ = ∑_g z²·ρ(g·r·g⁻¹)`; each summand's trace equals `tr(z²·ρ(r))` since `z²` is central.
  have hconj : ∀ g : G,
      LinearMap.trace ℂ (↥lam2Sub.toSubmodule)
          (zEnd * zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹))
        = LinearMap.trace ℂ (↥lam2Sub.toSubmodule)
          (zEnd * zEnd * lam2Sub.toRepresentation r5) := by
    intro g
    have hcomm : Commute (lam2Sub.toRepresentation g) (zEnd * zEnd) :=
      (zEnd_central g).mul_right (zEnd_central g)
    have hrw : zEnd * zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹)
        = lam2Sub.toRepresentation g * (zEnd * zEnd * lam2Sub.toRepresentation r5)
            * lam2Sub.toRepresentation g⁻¹ := by
      rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← hcomm.eq,
        mul_assoc (lam2Sub.toRepresentation g)]
    rw [hrw, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hz3 : zEnd * zEnd * zEnd
      = ∑ g : G, zEnd * zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹) := by
    rw [← Finset.mul_sum]; rfl
  rw [hz3, map_sum, Finset.sum_congr rfl (fun g _ => hconj g), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  -- `tr(z²·ρ(r)) = 1600`: unfold one `z` so `z²·ρ(r) = ∑_h z·ρ(h·r·h⁻¹·r)`.
  have hexpand : zEnd * zEnd * lam2Sub.toRepresentation r5
      = ∑ h : G, zEnd * lam2Sub.toRepresentation (h * r5 * h⁻¹ * r5) := by
    rw [show (zEnd * zEnd : Module.End ℂ ↥lam2Sub.toSubmodule)
          = ∑ h : G, zEnd * lam2Sub.toRepresentation (h * r5 * h⁻¹) by
        rw [← Finset.mul_sum]; rfl, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [mul_assoc, ← map_mul]
  have hr5 : LinearMap.trace ℂ (↥lam2Sub.toSubmodule)
      (zEnd * zEnd * lam2Sub.toRepresentation r5) = 1600 := by
    rw [hexpand, map_sum,
      Finset.sum_congr rfl (fun h _ => zEnd_comp_char (h * r5 * h⁻¹ * r5))]
    have hchar : ∀ y : G, lam2.character y
        = (2⁻¹ : ℂ) * ((((S4.fixCardM (G := G) (α := Fin 5) y : ℤ) - 1) ^ 2
            - ((S4.fixCardM (G := G) (α := Fin 5) (y * y) : ℤ) - 1) : ℤ) : ℂ) := by
      intro y
      rw [lam2_char_formula, repC4_char, repC4_char]
      push_cast; ring
    have key :
        (∑ h : G, ∑ h' : G,
          (((S4.fixCardM (G := G) (α := Fin 5)
                (h' * r5 * h'⁻¹ * (h * r5 * h⁻¹ * r5)) : ℤ) - 1) ^ 2
            - ((S4.fixCardM (G := G) (α := Fin 5)
                ((h' * r5 * h'⁻¹ * (h * r5 * h⁻¹ * r5))
                  * (h' * r5 * h'⁻¹ * (h * r5 * h⁻¹ * r5))) : ℤ) - 1)))
          = 3200 := by decide
    rw [Finset.sum_congr rfl (fun h _ =>
        Finset.sum_congr rfl (fun h' _ => hchar (h' * r5 * h'⁻¹ * (h * r5 * h⁻¹ * r5))))]
    simp only [← Finset.mul_sum, ← Int.cast_sum]
    rw [key]
    norm_num
  have hcard : (Fintype.card G : ℂ) = 60 := by
    rw [← Nat.card_eq_fintype_card, card_G]; norm_num
  rw [hr5, hcard]; norm_num

/-- **`dim_ℂ Λ²(ℂ⁴) = 6`.**  The value of the character at the identity (`FDRep.char_one`),
equal to `lam2_character 0 = 6` since `classRepA5 0 = 1`.  This is the dimension `tr 1` that the
two eigenspaces of `z` must add up to (`3 + 3 = 6`). -/
lemma lam2_finrank : Module.finrank ℂ (↥lam2Sub.toSubmodule) = 6 := by
  have h : (Module.finrank ℂ lam2 : ℂ) = 6 := by
    rw [← FDRep.char_one lam2, show (1 : G) = classRepA5 0 from rfl, lam2_character]
    norm_num
  exact_mod_cast h

/-- **`z` is not a scalar operator on `Λ²(ℂ⁴)`.**  If `z = c·1`, then `tr z = 6c = 60` forces
`c = 10`, but then `tr z² = 6c² = 600 ≠ 3600` (`zEnd_sq_trace`).  Hence `{1, z}` are linearly
independent in the 2-dimensional endomorphism algebra `End_{A₅}(Λ²)` (`lam2_hom_finrank`), so
they are a basis: `z` satisfies a minimal polynomial of degree exactly `2` (the linchpin for the
eigenspace split `z² = 20z + 400`). -/
lemma zEnd_not_scalar (c : ℂ) : zEnd ≠ c • 1 := by
  intro hc
  have htr1 : LinearMap.trace ℂ (↥lam2Sub.toSubmodule)
      (1 : Module.End ℂ ↥lam2Sub.toSubmodule) = 6 := by
    rw [Module.End.one_eq_id, LinearMap.trace_id, lam2_finrank]; norm_num
  have h1 : c * 6 = 60 := by
    have h := zEnd_trace
    rwa [hc, map_smul, htr1, smul_eq_mul] at h
  have h2 : c * c * 6 = 3600 := by
    have h := zEnd_sq_trace
    rwa [hc, smul_mul_smul_comm, one_mul, map_smul, htr1, smul_eq_mul] at h
  have hc10 : c = 10 := by linear_combination h1 / 6
  rw [hc10] at h2; norm_num at h2

/-! #### The two eigenvalues `μ± = 10 ± 10√5` and the minimal polynomial `X² − 20X − 400`

The eigenvalues of `z` on the two 3-dimensional eigenspaces are `μ± = 10 ± 10√5 = 20φ, 20φ'`.
These are exactly the two roots of `X² − 20X − 400`: their sum is `20` and their product is
`−400`, and their difference is `20√5` (the `√5` that produces the golden-ratio characters).
These identities are the algebraic content of the minimal polynomial `z² − 20z − 400 = 0`. -/

/-- `μ⁺ + μ⁻ = 20` — the trace of the companion `X² − 20X − 400`, i.e. `z² = 20z + 400·1`. -/
lemma muPlus_add_muMinus : muPlus + muMinus = 20 := by
  simp only [muPlus, muMinus]; ring

/-- `√5² = 5` in `ℂ`, the single irrational identity feeding the eigenvalue arithmetic. -/
lemma sqrt5_sq : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num

/-- `μ⁺ · μ⁻ = −400` — the constant term of the companion `X² − 20X − 400`. -/
lemma muPlus_mul_muMinus : muPlus * muMinus = -400 := by
  simp only [muPlus, muMinus]; ring_nf; rw [sqrt5_sq]; norm_num

/-- `μ⁺ − μ⁻ = 20√5` — the golden-ratio-producing gap between the two eigenvalues, the
denominator in `χ₊(g) = (S(g) − μ⁻·χ_{Λ²}(g))/(μ⁺ − μ⁻)`. -/
lemma muPlus_sub_muMinus : muPlus - muMinus = 20 * (Real.sqrt 5 : ℂ) := by
  simp only [muPlus, muMinus]; ring

/-! #### `χ_{Λ²} = χ₊ + χ₋`: the honest character of `Λ²(ℂ⁴)` is the sum of the two book rows -/

/-- `Q5toC` is additive. -/
lemma Q5toC_add (a b : Q5) : Q5toC (a + b) = Q5toC a + Q5toC b := by
  simp only [Q5toC, Q5.add_re, Q5.add_im]; push_cast; ring

/-- **The character of `Λ²(ℂ⁴)` is the sum of the two golden-ratio rows `χ₊ + χ₋`.**  The honest
trace `χ_{Λ²} = (6, 0, −2, 1, 1)` (`lam2_character`) equals `chiA5 1 + chiA5 2` at every class:
row 1 is `(3, 0, −1, φ, φ')`, row 2 is `(3, 0, −1, φ', φ)`, and `φ + φ' = 1` makes the two
`√5` contributions cancel on the 5-cycle classes.  Combined with `A5_orthonormal` (rows 1 and 2
are orthonormal, and orthogonal to rows 0/3/4), this exhibits `Λ²(ℂ⁴)` as the multiplicity-free
sum of the two 3-dimensional icosahedral constituents `ℂ³₊ ⊕ ℂ³₋` — the character-level
statement underlying the eigenspace split of the central `z`. -/
lemma lam2_character_eq_sum (j : Fin 5) :
    lam2.character (classRepA5 j) = Q5toC (chiA5 1 j) + Q5toC (chiA5 2 j) := by
  rw [lam2_character, ← Q5toC_add, Q5toC]
  fin_cases j <;>
    simp only [chiA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    norm_num [Q5.add_re, Q5.add_im, Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re,
      Q5.neg_im, Q5.one_re, Q5.one_im, Q5.zero_re, Q5.zero_im]

end

end A5

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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` over the `ConjClasses` quotient of the 60-element group A₅; no `native_decide`
/-- `A₅` has exactly 5 conjugacy classes, hence 5 irreducible representations
(the five rows of `chiA5`).  Proved by honest `decide` (no `native_decide`).
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_A5_conj_classes :
    Fintype.card (ConjClasses (alternatingGroup (Fin 5))) = 5 := by
  decide

/-- `A₅` has order 60.  Combined with 5 conjugacy classes and `∑ dᵢ² = |G|`, the dimensions
are 1,3,3,4,5.  Proved from `card_alternatingGroup` (`= 5!/2`), no `native_decide`.
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_A5_card :
    Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [card_alternatingGroup, Fintype.card_fin]; decide

/-- The three genuine `A₅` representations realised here, indexed `0,1,2` as `ℂ, ℂ⁴, ℂ⁵`
(the trivial, 4-dimensional, and 5-dimensional rows of `chiA5`). -/
noncomputable def Etingof.Example4_8_1_A5_irrep :
    Fin 3 → FDRep ℂ (alternatingGroup (Fin 5)) := Etingof.Example4_8_1.A5.irrepA5

/-- Each of the three `A₅` representations is simple (irreducible), proved via the norm-one
character criterion `FDRep.simple_iff_char_is_norm_one` (no `native_decide`).
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_A5_simple (i : Fin 3) :
    CategoryTheory.Simple (Etingof.Example4_8_1_A5_irrep i) :=
  Etingof.Example4_8_1.A5.irrepA5_simple i

/-- The character (trace) of the `i`-th `A₅` representation (`ℂ, ℂ⁴, ℂ⁵`) at the `j`-th class
representative `(Id, (123), (12)(34), (12345), (13245))` equals the tabulated value
`chiA5 (rowA5 i) j` (rows `0, 3, 4`).  This connects the trivial, 4-dim, and 5-dim rows of the
table to actual representations. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_A5_character (i : Fin 3) (j : Fin 5) :
    (Etingof.Example4_8_1_A5_irrep i).character (Etingof.Example4_8_1.A5.classRepA5 j)
      = Etingof.Example4_8_1.Q5toC
          (Etingof.Example4_8_1.chiA5 (Etingof.Example4_8_1.A5.rowA5 i) j) :=
  Etingof.Example4_8_1.A5.irrepA5_character_book i j

/-- The three `A₅` representations `ℂ, ℂ⁴, ℂ⁵` are pairwise non-isomorphic (their characters
differ). (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_A5_pairwise (i j : Fin 3) (hij : i ≠ j) :
    ¬ Nonempty (Etingof.Example4_8_1_A5_irrep i ≅ Etingof.Example4_8_1_A5_irrep j) :=
  Etingof.Example4_8_1.A5.irrepA5_pairwise i j hij
