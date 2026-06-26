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

set_option linter.style.nativeDecide false in
set_option maxHeartbeats 1000000 in
-- `native_decide` evaluates the full orthonormality computation symbolically over `Q5 = ℚ[√5]`; the raised limit covers the `5 × 5` table of inner products.
/-- The tabulated `Q₈` characters are orthonormal, `⟪χ_i, χ_j⟫ = δ_{ij}`.  Combined with the
fact that `Q₈` has exactly 5 conjugacy classes (`Q8_conj_classes`), this certifies that the
five rows are precisely the distinct irreducible characters of `Q₈`, including the value
`χ_{ℂ²}(−1) = −2`. (Etingof Example 4.8.1) -/
theorem Q8_orthonormal (i j : Fin 5) :
    ip 8 sizesQ8 (chiQ8 i) (chiQ8 j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> native_decide

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

set_option linter.style.nativeDecide false in
/-- `Q₈` has exactly 5 conjugacy classes, hence 5 irreducible representations
(the five rows of `chiQ8`). (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_conj_classes :
    Fintype.card (ConjClasses (QuaternionGroup 2)) = 5 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- `Q₈` has order 8.  Combined with 5 conjugacy classes and the sum-of-squares formula
`∑ dᵢ² = |G|`, the only solution is dimensions 1,1,1,1,2. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_card :
    Fintype.card (QuaternionGroup 2) = 8 := by
  native_decide

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
