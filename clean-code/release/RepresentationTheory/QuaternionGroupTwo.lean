import Mathlib



namespace RepresentationTheory.QuaternionGroupTwo


/-- An auxiliary type. -/
structure AuxiliaryType where
  /-- Returns the first rational coordinate. -/
  re : ℚ
  /-- Returns the second rational coordinate. -/
  im : ℚ
deriving DecidableEq, Repr

namespace AuxiliaryType

/-- Two values are equal when both rational coordinates agree. -/
@[ext] theorem ext {x y : AuxiliaryType} (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x; cases y; simp_all

/-- The additive zero of the auxiliary coordinate type. -/
instance : Zero AuxiliaryType := ⟨⟨0, 0⟩⟩
/-- The multiplicative unit of the auxiliary coordinate type. -/
instance : One AuxiliaryType := ⟨⟨1, 0⟩⟩
/-- Addition on the auxiliary coordinate type. -/
instance : Add AuxiliaryType := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
/-- Negation on the auxiliary coordinate type. -/
instance : Neg AuxiliaryType := ⟨fun x => ⟨-x.re, -x.im⟩⟩

/-- Multiplication on the auxiliary coordinate type. -/
instance : Mul AuxiliaryType := ⟨fun x y => ⟨x.re * y.re + 5 * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
/-- Interprets natural numerals in the auxiliary coordinate type. -/
instance (n : ℕ) : OfNat AuxiliaryType n := ⟨⟨(OfNat.ofNat n : ℚ), 0⟩⟩

/-- The first coordinate of a value built from two rationals is the first input. -/
theorem mk_re (a b : ℚ) : (AuxiliaryType.mk a b).re = a := rfl
/-- The second coordinate of a value built from two rationals is the second input. -/
theorem mk_im (a b : ℚ) : (AuxiliaryType.mk a b).im = b := rfl
/-- Zero has zero first coordinate. -/
theorem zero_re : (0 : AuxiliaryType).re = 0 := rfl
/-- Zero has zero second coordinate. -/
theorem zero_im : (0 : AuxiliaryType).im = 0 := rfl
/-- The multiplicative unit has first coordinate one. -/
theorem one_re : (1 : AuxiliaryType).re = 1 := rfl
/-- The multiplicative unit has zero second coordinate. -/
theorem one_im : (1 : AuxiliaryType).im = 0 := rfl
/-- The first coordinate of a sum is the sum of the first coordinates. -/
theorem add_re (x y : AuxiliaryType) : (x + y).re = x.re + y.re := rfl
/-- The second coordinate of a sum is the sum of the second coordinates. -/
theorem add_im (x y : AuxiliaryType) : (x + y).im = x.im + y.im := rfl
/-- The first coordinate commutes with negation. -/
theorem neg_re (x : AuxiliaryType) : (-x).re = -x.re := rfl
/-- The second coordinate commutes with negation. -/
theorem neg_im (x : AuxiliaryType) : (-x).im = -x.im := rfl
/-- The first coordinate of a product is the first-coordinate product plus five times the second-coordinate product. -/
theorem mul_re (x y : AuxiliaryType) : (x * y).re = x.re * y.re + 5 * x.im * y.im := rfl
/-- The second coordinate of a product is the cross-term sum. -/
theorem mul_im (x y : AuxiliaryType) : (x * y).im = x.re * y.im + x.im * y.re := rfl
/-- The first coordinate of a natural numeral is that numeral. -/
theorem ofNat_re (n : ℕ) : (no_index (OfNat.ofNat n) : AuxiliaryType).re = (OfNat.ofNat n : ℚ) :=
  rfl
/-- A natural numeral has zero second coordinate. -/
theorem ofNat_im (n : ℕ) : (no_index (OfNat.ofNat n) : AuxiliaryType).im = 0 := rfl


/-- Embeds a rational as a value of the auxiliary coordinate type. -/
def ofRat (r : ℚ) : AuxiliaryType := ⟨r, 0⟩

/-- The first coordinate of the rational embedding is its input. -/
theorem ofRat_re (r : ℚ) : (ofRat r).re = r := rfl
/-- The rational embedding has zero second coordinate. -/
theorem ofRat_im (r : ℚ) : (ofRat r).im = 0 := rfl


/-- Sums a finite family of auxiliary coordinate values. -/
def sum {n : ℕ} (f : Fin n → AuxiliaryType) : AuxiliaryType := (List.ofFn f).foldr (· + ·) 0


/-- Expands the sum of a five-term family into its individual entries. -/
theorem sum_fin_five (f : Fin 5 → AuxiliaryType) :
    sum f = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + 0)))) := by
  simp only [sum, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil]; rfl


/-- Maps a rational, an indexed rational family, and two indexed auxiliary families to an auxiliary value. -/
def auxiliaryCombination {r : ℕ} (N : ℚ) (sizes : Fin r → ℚ) (f g : Fin r → AuxiliaryType) : AuxiliaryType :=
  ofRat (1 / N) * sum (fun c => ofRat (sizes c) * f c * g c)

end AuxiliaryType

open AuxiliaryType




/-- A five-entry vector of rational values. -/
def auxiliaryRatVector : Fin 5 → ℚ := ![1, 1, 2, 2, 2]


/-- A five-by-five table with values in the auxiliary coordinate type. -/
def auxiliaryCharacterTable : Fin 5 → Fin 5 → AuxiliaryType :=
  ![![1,  1,  1,  1,  1],
    ![1,  1,  1, -1, -1],
    ![1,  1, -1,  1, -1],
    ![1,  1, -1, -1,  1],
    ![2, -2,  0,  0,  0]]


/-- Maps the auxiliary coordinate type into the complex numbers. -/
noncomputable def auxiliaryTypeToComplex (q : AuxiliaryType) : ℂ := (q.re : ℂ) + (q.im : ℂ) * (Real.sqrt 5 : ℂ)

/-- The auxiliary map sends zero to zero. -/
lemma auxiliaryTypeToComplex_zero : auxiliaryTypeToComplex 0 = 0 := by
  rw [auxiliaryTypeToComplex, show (0 : AuxiliaryType).re = 0 from rfl, show (0 : AuxiliaryType).im = 0 from rfl]; push_cast; ring
/-- The auxiliary map sends one to one. -/
lemma auxiliaryTypeToComplex_one : auxiliaryTypeToComplex 1 = 1 := by
  rw [auxiliaryTypeToComplex, show (1 : AuxiliaryType).re = 1 from rfl, show (1 : AuxiliaryType).im = 0 from rfl]; push_cast; ring
/-- The auxiliary map sends two to two. -/
lemma auxiliaryTypeToComplex_two : auxiliaryTypeToComplex 2 = 2 := by
  rw [auxiliaryTypeToComplex, show (2 : AuxiliaryType).re = (2 : ℚ) from rfl, show (2 : AuxiliaryType).im = 0 from rfl]; push_cast; ring
/-- An auxiliary result with an unavailable displayed type. -/
lemma auxiliaryResultOne : auxiliaryTypeToComplex (-1) = -1 := by
  rw [auxiliaryTypeToComplex, show ((-1 : AuxiliaryType)).im = 0 from neg_zero, show ((-1 : AuxiliaryType)).re = (-1 : ℚ) from rfl]
  push_cast; ring
/-- An auxiliary result with an unavailable displayed type. -/
lemma auxiliaryResultTwo : auxiliaryTypeToComplex (-2) = -2 := by
  rw [auxiliaryTypeToComplex, show ((-2 : AuxiliaryType)).im = 0 from neg_zero, show ((-2 : AuxiliaryType)).re = (-2 : ℚ) from rfl]
  push_cast; ring




open QuaternionGroup Matrix Complex


/-- For a complex square root of one, powers depend only on the exponent modulo two. -/
lemma pow_eq_of_mod_two_eq {α : ℂ} (hα : α ^ 2 = 1) {m n : ℕ} (h : m % 2 = n % 2) :
    α ^ m = α ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  conv_rhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_add, pow_mul, pow_mul, hα, one_pow, one_pow, h]


/-- Forms a complex-valued function on the quaternion group from two parameters. -/
def characterValueFunction (α β : ℂ) : QuaternionGroup 2 → ℂ
  | .a i => α ^ i.val
  | .xa i => β * α ^ i.val


/-- Builds a complex-valued monoid homomorphism from two square roots of one. -/
def characterHomOfSquareEqOne (α β : ℂ) (hα : α ^ 2 = 1) (hβ : β ^ 2 = 1) : QuaternionGroup 2 →* ℂ where
  toFun := characterValueFunction α β
  map_one' := by change characterValueFunction α β (a 0) = 1; change α ^ (0 : ZMod 4).val = 1; simp
  map_mul' x y := by
    rcases x with i | i <;> rcases y with j | j
    · -- a i * a j = a (i + j)
      change characterValueFunction α β (a i * a j) = characterValueFunction α β (a i) * characterValueFunction α β (a j)
      rw [a_mul_a]
      change α ^ (i + j).val = α ^ i.val * α ^ j.val
      have hp : (i + j).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      rw [← pow_add]
      exact pow_eq_of_mod_two_eq hα hp
    · -- a i * xa j = xa (j - i)
      change characterValueFunction α β (a i * xa j) = characterValueFunction α β (a i) * characterValueFunction α β (xa j)
      rw [a_mul_xa]
      change β * α ^ (j - i).val = α ^ i.val * (β * α ^ j.val)
      have hp : (j - i).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      have e : α ^ i.val * (β * α ^ j.val) = β * α ^ (i.val + j.val) := by rw [pow_add]; ring
      rw [e]
      exact congrArg (β * ·) (pow_eq_of_mod_two_eq hα hp)
    · -- xa i * a j = xa (i + j)
      change characterValueFunction α β (xa i * a j) = characterValueFunction α β (xa i) * characterValueFunction α β (a j)
      rw [xa_mul_a]
      change β * α ^ (i + j).val = β * α ^ i.val * α ^ j.val
      have hp : (i + j).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      rw [mul_assoc, ← pow_add]
      exact congrArg (β * ·) (pow_eq_of_mod_two_eq hα hp)
    · -- xa i * xa j = a (2 + j - i)
      change characterValueFunction α β (xa i * xa j) = characterValueFunction α β (xa i) * characterValueFunction α β (xa j)
      rw [xa_mul_xa]
      change α ^ ((2 : ZMod 4) + j - i).val = β * α ^ i.val * (β * α ^ j.val)
      have hp : ((2 : ZMod 4) + j - i).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      have e : β * α ^ i.val * (β * α ^ j.val) = β ^ 2 * α ^ (i.val + j.val) := by
        rw [pow_add]; ring
      rw [e, hβ, one_mul]
      exact pow_eq_of_mod_two_eq hα hp

/-- The constructed homomorphism agrees pointwise with the parameterized function. -/
@[simp] lemma characterHomOfSquareEqOne_apply (α β : ℂ) (hα : α ^ 2 = 1) (hβ : β ^ 2 = 1)
    (g : QuaternionGroup 2) : characterHomOfSquareEqOne α β hα hβ g = characterValueFunction α β g := rfl

/-- The parameterized function is one at the zeroth power element. -/
lemma characterValueFunction_a_zero (α β : ℂ) : characterValueFunction α β (a 0) = 1 := by
  change α ^ (0 : ZMod 4).val = 1; simp
/-- The parameterized function equals its first parameter at the first power element. -/
lemma characterValueFunction_a_one (α β : ℂ) : characterValueFunction α β (a 1) = α := by
  change α ^ (1 : ZMod 4).val = α; rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]
/-- The parameterized function equals the square of its first parameter at the second power element. -/
lemma characterValueFunction_a_two (α β : ℂ) : characterValueFunction α β (a 2) = α ^ 2 := by
  change α ^ (2 : ZMod 4).val = α ^ 2; rw [show (2 : ZMod 4).val = 2 from rfl]
/-- The parameterized function equals its second parameter at QuaternionGroup.xa 0. -/
lemma characterValueFunction_xa_zero (α β : ℂ) : characterValueFunction α β (xa 0) = β := by
  change β * α ^ (0 : ZMod 4).val = β; simp
/-- At QuaternionGroup.xa 1, the parameterized function is the second parameter times the first. -/
lemma characterValueFunction_xa_one (α β : ℂ) : characterValueFunction α β (xa 1) = β * α := by
  change β * α ^ (1 : ZMod 4).val = β * α; rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]


/-- Turns a complex-valued monoid homomorphism into a one-dimensional representation. -/
def representationOfComplexCharacter (χ : QuaternionGroup 2 →* ℂ) : Representation ℂ (QuaternionGroup 2) ℂ where
  toFun g := χ g • LinearMap.id
  map_one' := by rw [map_one, one_smul]; rfl
  map_mul' g h := by
    ext x
    simp only [map_mul, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      smul_smul]


/-- The character of the one-dimensional representation is the original homomorphism. -/
lemma representationOfComplexCharacter_character (χ : QuaternionGroup 2 →* ℂ) (g : QuaternionGroup 2) :
    (FDRep.of (representationOfComplexCharacter χ)).character g = χ g := by
  rw [show (FDRep.of (representationOfComplexCharacter χ)).character g = LinearMap.trace ℂ ℂ (representationOfComplexCharacter χ g) from rfl]
  change LinearMap.trace ℂ ℂ (χ g • LinearMap.id) = χ g
  rw [map_smul, LinearMap.trace_id]
  simp




/-- A fixed two-by-two complex matrix. -/
noncomputable def firstMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]


/-- A second fixed two-by-two complex matrix. -/
def secondMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- An auxiliary result with an unavailable displayed type. -/
lemma auxiliaryResultThree : firstMatrix ^ 2 = -1 := by
  rw [pow_two]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [firstMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I, Matrix.one_fin_two]

/-- The fourth power of the first fixed matrix is the identity. -/
lemma firstMatrix_pow_four : firstMatrix ^ 4 = 1 := by
  have h : firstMatrix ^ 4 = (firstMatrix ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h, auxiliaryResultThree, neg_one_sq]

/-- The square of the second matrix equals the square of the first. -/
lemma secondMatrix_sq : secondMatrix * secondMatrix = firstMatrix ^ 2 := by
  rw [auxiliaryResultThree]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [secondMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]

/-- Multiplying the two fixed matrices in one order equals the reversed product with a third power. -/
lemma firstMatrix_mul_secondMatrix : firstMatrix * secondMatrix = secondMatrix * firstMatrix ^ 3 := by
  have h3 : firstMatrix ^ 3 = !![(-Complex.I), 0; 0, Complex.I] := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, auxiliaryResultThree]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [firstMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]
  rw [h3]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [firstMatrix, secondMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Equal complex casts of natural exponents give equal powers of the first matrix. -/
lemma firstMatrix_pow_eq_of_cast_eq {a b : ℕ} (h : (a : ZMod 4) = (b : ZMod 4)) : firstMatrix ^ a = firstMatrix ^ b := by
  have e : a % 4 = b % 4 := (ZMod.natCast_eq_natCast_iff a b 4).mp h
  conv_lhs => rw [← Nat.div_add_mod a 4]
  conv_rhs => rw [← Nat.div_add_mod b 4]
  rw [pow_add, pow_add, pow_mul, pow_mul, firstMatrix_pow_four, one_pow, one_pow, e]

/-- Moving the second matrix past a power of the first multiplies the exponent by three. -/
lemma firstMatrix_pow_mul_secondMatrix : ∀ m : ℕ, firstMatrix ^ m * secondMatrix = secondMatrix * firstMatrix ^ (3 * m)
  | 0 => by simp
  | (m + 1) => by
    rw [pow_succ, mul_assoc, firstMatrix_mul_secondMatrix, ← mul_assoc, firstMatrix_pow_mul_secondMatrix m, mul_assoc, ← pow_add,
      show 3 * m + 3 = 3 * (m + 1) from by ring]

/-- Multiplying the second matrix, a power of the first, and the second matrix yields the displayed shifted power. -/
lemma secondMatrix_mul_firstMatrix_pow_mul_secondMatrix (m : ℕ) : secondMatrix * firstMatrix ^ m * secondMatrix = firstMatrix ^ (2 + 3 * m) := by
  rw [mul_assoc, firstMatrix_pow_mul_secondMatrix, ← mul_assoc, secondMatrix_sq, ← pow_add]


/-- Assigns a two-by-two complex matrix to each element of the quaternion group. -/
noncomputable def quaternionGroupMatrix : QuaternionGroup 2 → Matrix (Fin 2) (Fin 2) ℂ
  | .a k => firstMatrix ^ k.val
  | .xa k => secondMatrix * firstMatrix ^ k.val


/-- The matrix-valued monoid homomorphism on the quaternion group. -/
noncomputable def quaternionGroupMatrixHom : QuaternionGroup 2 →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := quaternionGroupMatrix
  map_one' := by
    change quaternionGroupMatrix 1 = 1
    rw [QuaternionGroup.one_def]; simp [quaternionGroupMatrix]
  map_mul' := by
    rintro (i | i) (j | j)
    · change quaternionGroupMatrix (a i * a j) = quaternionGroupMatrix (a i) * quaternionGroupMatrix (a j)
      rw [QuaternionGroup.a_mul_a]
      simp only [quaternionGroupMatrix]
      rw [← pow_add]
      exact firstMatrix_pow_eq_of_cast_eq (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    · change quaternionGroupMatrix (a i * xa j) = quaternionGroupMatrix (a i) * quaternionGroupMatrix (xa j)
      rw [QuaternionGroup.a_mul_xa]
      simp only [quaternionGroupMatrix]
      rw [← mul_assoc, firstMatrix_pow_mul_secondMatrix, mul_assoc, ← pow_add]
      congr 1
      exact firstMatrix_pow_eq_of_cast_eq (by push_cast [ZMod.natCast_val, ZMod.cast_id]; revert i j; decide)
    · change quaternionGroupMatrix (xa i * a j) = quaternionGroupMatrix (xa i) * quaternionGroupMatrix (a j)
      rw [QuaternionGroup.xa_mul_a]
      simp only [quaternionGroupMatrix]
      rw [mul_assoc, ← pow_add]
      congr 1
      exact firstMatrix_pow_eq_of_cast_eq (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    · change quaternionGroupMatrix (xa i * xa j) = quaternionGroupMatrix (xa i) * quaternionGroupMatrix (xa j)
      rw [QuaternionGroup.xa_mul_xa]
      simp only [quaternionGroupMatrix]
      rw [← mul_assoc (secondMatrix * firstMatrix ^ i.val) secondMatrix (firstMatrix ^ j.val), secondMatrix_mul_firstMatrix_pow_mul_secondMatrix, ← pow_add]
      exact firstMatrix_pow_eq_of_cast_eq (by push_cast [ZMod.natCast_val, ZMod.cast_id]; revert i j; decide)


/-- The two-dimensional complex representation defined by the fixed matrices. -/
noncomputable def matrixRepresentation : Representation ℂ (QuaternionGroup 2) (Fin 2 → ℂ) where
  toFun g := Matrix.toLinAlgEquiv' (quaternionGroupMatrixHom g)
  map_one' := by simp
  map_mul' g h := by simp [map_mul]

/-- The representation action is multiplication by the corresponding matrix. -/
lemma matrixRepresentation_apply (g : QuaternionGroup 2) (v : Fin 2 → ℂ) :
    matrixRepresentation g v = (quaternionGroupMatrixHom g).mulVec v := by
  simp [matrixRepresentation, Matrix.toLinAlgEquiv'_apply]


/-- The character of the matrix representation is the trace of its assigned matrix. -/
lemma matrixRepresentation_character_eq_trace (g : QuaternionGroup 2) :
    (FDRep.of matrixRepresentation).character g = (quaternionGroupMatrixHom g).trace := by
  rw [show (FDRep.of matrixRepresentation).character g = LinearMap.trace ℂ (Fin 2 → ℂ) (matrixRepresentation g) from rfl]
  have h : matrixRepresentation g = Matrix.toLin' (quaternionGroupMatrixHom g) := by
    ext v; simp [matrixRepresentation_apply, Matrix.toLin'_apply]
  rw [h, Matrix.trace_toLin'_eq]




/-- An indexed family of five quaternion-group elements. -/
def selectedQuaternionGroupElements : Fin 5 → QuaternionGroup 2 := ![a 0, a 2, a 1, xa 0, xa 1]


/-- A fixed complex-valued monoid homomorphism on the quaternion group. -/
def complexCharacterZero : QuaternionGroup 2 →* ℂ := characterHomOfSquareEqOne 1 1 (by norm_num) (by norm_num)

/-- A second fixed complex-valued monoid homomorphism on the quaternion group. -/
def complexCharacterOne : QuaternionGroup 2 →* ℂ := characterHomOfSquareEqOne 1 (-1) (by norm_num) (by norm_num)

/-- A third fixed complex-valued monoid homomorphism on the quaternion group. -/
def complexCharacterTwo : QuaternionGroup 2 →* ℂ := characterHomOfSquareEqOne (-1) 1 (by norm_num) (by norm_num)

/-- A fourth fixed complex-valued monoid homomorphism on the quaternion group. -/
def complexCharacterThree : QuaternionGroup 2 →* ℂ := characterHomOfSquareEqOne (-1) (-1) (by norm_num) (by norm_num)


/-- An indexed family of five finite-dimensional complex representations. -/
noncomputable def irreducibleRepresentations : Fin 5 → FDRep ℂ (QuaternionGroup 2) :=
  ![FDRep.of (representationOfComplexCharacter complexCharacterZero), FDRep.of (representationOfComplexCharacter complexCharacterOne), FDRep.of (representationOfComplexCharacter complexCharacterTwo),
    FDRep.of (representationOfComplexCharacter complexCharacterThree), FDRep.of matrixRepresentation]




/-- An enumeration of the quaternion group by eight indices. -/
def finEightToQuaternionGroup : Fin 8 → QuaternionGroup 2 :=
  ![a 0, a 1, a 2, a 3, xa 0, xa 1, xa 2, xa 3]

/-- The eight-term enumeration of the quaternion group is bijective. -/
lemma finEightToQuaternionGroup_bijective : Function.Bijective finEightToQuaternionGroup := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨by decide, by decide⟩


/-- Expands a finite sum over the quaternion group into its eight element values. -/
lemma sum_quaternionGroup_eq_explicit (f : QuaternionGroup 2 → ℂ) :
    ∑ g, f g = f (a 0) + f (a 1) + f (a 2) + f (a 3)
             + f (xa 0) + f (xa 1) + f (xa 2) + f (xa 3) := by
  rw [← Equiv.sum_comp (Equiv.ofBijective finEightToQuaternionGroup finEightToQuaternionGroup_bijective) f, Fin.sum_univ_eight]
  simp only [Equiv.ofBijective_apply, finEightToQuaternionGroup]
  rfl


/-- The sum of a one-dimensional character times its inverse-argument value equals the group cardinality. -/
lemma representationOfComplexCharacter_norm_sum (χ : QuaternionGroup 2 →* ℂ) :
    ∑ g : QuaternionGroup 2, (FDRep.of (representationOfComplexCharacter χ)).character g
      * (FDRep.of (representationOfComplexCharacter χ)).character g⁻¹ = Nat.card (QuaternionGroup 2) := by
  have hone : ∀ g : QuaternionGroup 2, χ g * χ g⁻¹ = 1 := fun g => by
    rw [← map_mul, mul_inv_cancel, map_one]
  simp only [representationOfComplexCharacter_character]
  rw [Finset.sum_congr rfl (fun g _ => hone g), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]



/-- The matrix representation has character value two at the zeroth power element. -/
lemma matrixRepresentation_character_a_zero : (FDRep.of matrixRepresentation).character (a 0) = 2 := by
  rw [matrixRepresentation_character_eq_trace]; change (quaternionGroupMatrix (a 0)).trace = 2
  simp [quaternionGroupMatrix]

/-- The matrix representation has character value zero at the first power element. -/
lemma matrixRepresentation_character_a_one : (FDRep.of matrixRepresentation).character (a 1) = 0 := by
  rw [matrixRepresentation_character_eq_trace]; change (quaternionGroupMatrix (a 1)).trace = 0
  simp only [quaternionGroupMatrix, show (1 : ZMod (2 * 2)).val = 1 from by decide, pow_one]
  simp [firstMatrix, Matrix.trace_fin_two]

/-- An auxiliary result with an unavailable displayed type. -/
lemma auxiliaryResultFour : (FDRep.of matrixRepresentation).character (a 2) = -2 := by
  rw [matrixRepresentation_character_eq_trace]; change (quaternionGroupMatrix (a 2)).trace = -2
  simp only [quaternionGroupMatrix, show (2 : ZMod (2 * 2)).val = 2 from by decide]
  rw [auxiliaryResultThree]; simp

/-- The matrix representation has character value zero at the third power element. -/
lemma matrixRepresentation_character_a_three : (FDRep.of matrixRepresentation).character (a 3) = 0 := by
  rw [matrixRepresentation_character_eq_trace]; change (quaternionGroupMatrix (a 3)).trace = 0
  simp only [quaternionGroupMatrix, show (3 : ZMod (2 * 2)).val = 3 from by decide]
  rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, auxiliaryResultThree]
  simp [firstMatrix, Matrix.trace_fin_two]

/-- The matrix representation has character value zero at QuaternionGroup.xa 0. -/
lemma matrixRepresentation_character_xa_zero : (FDRep.of matrixRepresentation).character (xa 0) = 0 := by
  rw [matrixRepresentation_character_eq_trace]; change (quaternionGroupMatrix (xa 0)).trace = 0
  simp only [quaternionGroupMatrix, show (0 : ZMod (2 * 2)).val = 0 from by decide, pow_zero, mul_one]
  simp [secondMatrix, Matrix.trace_fin_two]

/-- The matrix representation has character value zero at QuaternionGroup.xa 1. -/
lemma matrixRepresentation_character_xa_one : (FDRep.of matrixRepresentation).character (xa 1) = 0 := by
  rw [matrixRepresentation_character_eq_trace]; change (quaternionGroupMatrix (xa 1)).trace = 0
  simp only [quaternionGroupMatrix, show (1 : ZMod (2 * 2)).val = 1 from by decide, pow_one]
  simp [secondMatrix, firstMatrix, Matrix.trace_fin_two]

/-- The matrix representation has character value zero at QuaternionGroup.xa 2. -/
lemma matrixRepresentation_character_xa_two : (FDRep.of matrixRepresentation).character (xa 2) = 0 := by
  rw [matrixRepresentation_character_eq_trace]; change (quaternionGroupMatrix (xa 2)).trace = 0
  simp only [quaternionGroupMatrix, show (2 : ZMod (2 * 2)).val = 2 from by decide]
  rw [auxiliaryResultThree]
  simp [secondMatrix, Matrix.trace_fin_two]

/-- The matrix representation has character value zero at QuaternionGroup.xa 3. -/
lemma matrixRepresentation_character_xa_three : (FDRep.of matrixRepresentation).character (xa 3) = 0 := by
  rw [matrixRepresentation_character_eq_trace]; change (quaternionGroupMatrix (xa 3)).trace = 0
  simp only [quaternionGroupMatrix, show (3 : ZMod (2 * 2)).val = 3 from by decide]
  rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, auxiliaryResultThree]
  simp [secondMatrix, firstMatrix, Matrix.trace_fin_two]


/-- The character norm sum of the matrix representation equals the group cardinality. -/
lemma matrixRepresentation_character_norm_sum :
    ∑ g : QuaternionGroup 2, (FDRep.of matrixRepresentation).character g
      * (FDRep.of matrixRepresentation).character g⁻¹ = Nat.card (QuaternionGroup 2) := by
  rw [sum_quaternionGroup_eq_explicit (fun g => (FDRep.of matrixRepresentation).character g * (FDRep.of matrixRepresentation).character g⁻¹)]
  simp only [show (a 0 : QuaternionGroup 2)⁻¹ = a 0 from by decide,
    show (a 1 : QuaternionGroup 2)⁻¹ = a 3 from by decide,
    show (a 2 : QuaternionGroup 2)⁻¹ = a 2 from by decide,
    show (a 3 : QuaternionGroup 2)⁻¹ = a 1 from by decide,
    show (xa 0 : QuaternionGroup 2)⁻¹ = xa 2 from by decide,
    show (xa 1 : QuaternionGroup 2)⁻¹ = xa 3 from by decide,
    show (xa 2 : QuaternionGroup 2)⁻¹ = xa 0 from by decide,
    show (xa 3 : QuaternionGroup 2)⁻¹ = xa 1 from by decide,
    matrixRepresentation_character_a_zero, matrixRepresentation_character_a_one, auxiliaryResultFour, matrixRepresentation_character_a_three, matrixRepresentation_character_xa_zero, matrixRepresentation_character_xa_one, matrixRepresentation_character_xa_two, matrixRepresentation_character_xa_three]
  rw [show Nat.card (QuaternionGroup 2) = 8 from by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]]
  norm_num




/-- Every representation in the indexed family is simple. -/
lemma irreducibleRepresentations_simple (i : Fin 5) : CategoryTheory.Simple (irreducibleRepresentations i) := by
  fin_cases i <;>
    simp only [irreducibleRepresentations,
      Matrix.cons_val_two]
  · exact (FDRep.simple_iff_char_is_norm_one _).mpr (representationOfComplexCharacter_norm_sum complexCharacterZero)
  · exact (FDRep.simple_iff_char_is_norm_one _).mpr (representationOfComplexCharacter_norm_sum complexCharacterOne)
  · exact (FDRep.simple_iff_char_is_norm_one _).mpr (representationOfComplexCharacter_norm_sum complexCharacterTwo)
  · exact (FDRep.simple_iff_char_is_norm_one _).mpr (representationOfComplexCharacter_norm_sum complexCharacterThree)
  · exact (FDRep.simple_iff_char_is_norm_one _).mpr matrixRepresentation_character_norm_sum

attribute [local simp] characterValueFunction_a_zero characterValueFunction_a_one characterValueFunction_a_two characterValueFunction_xa_zero characterValueFunction_xa_one
  matrixRepresentation_character_a_zero matrixRepresentation_character_a_one auxiliaryResultFour matrixRepresentation_character_xa_zero matrixRepresentation_character_xa_one
  auxiliaryTypeToComplex_zero auxiliaryTypeToComplex_one auxiliaryTypeToComplex_two auxiliaryResultOne auxiliaryResultTwo



private lemma char_row0 (j : Fin 5) :
    (FDRep.of (representationOfComplexCharacter complexCharacterZero)).character (selectedQuaternionGroupElements j) = auxiliaryTypeToComplex (auxiliaryCharacterTable 0 j) := by
  rw [representationOfComplexCharacter_character]
  fin_cases j
  · change characterValueFunction 1 1 (a 0) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction 1 1 (a 2) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction 1 1 (a 1) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction 1 1 (xa 0) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction 1 1 (xa 1) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]

private lemma char_row1 (j : Fin 5) :
    (FDRep.of (representationOfComplexCharacter complexCharacterOne)).character (selectedQuaternionGroupElements j) = auxiliaryTypeToComplex (auxiliaryCharacterTable 1 j) := by
  rw [representationOfComplexCharacter_character]
  fin_cases j
  · change characterValueFunction 1 (-1) (a 0) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction 1 (-1) (a 2) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction 1 (-1) (a 1) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction 1 (-1) (xa 0) = auxiliaryTypeToComplex (-1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction 1 (-1) (xa 1) = auxiliaryTypeToComplex (-1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]

private lemma char_row2 (j : Fin 5) :
    (FDRep.of (representationOfComplexCharacter complexCharacterTwo)).character (selectedQuaternionGroupElements j) = auxiliaryTypeToComplex (auxiliaryCharacterTable 2 j) := by
  rw [representationOfComplexCharacter_character]
  fin_cases j
  · change characterValueFunction (-1) 1 (a 0) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction (-1) 1 (a 2) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction (-1) 1 (a 1) = auxiliaryTypeToComplex (-1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction (-1) 1 (xa 0) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction (-1) 1 (xa 1) = auxiliaryTypeToComplex (-1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]

private lemma char_row3 (j : Fin 5) :
    (FDRep.of (representationOfComplexCharacter complexCharacterThree)).character (selectedQuaternionGroupElements j) = auxiliaryTypeToComplex (auxiliaryCharacterTable 3 j) := by
  rw [representationOfComplexCharacter_character]
  fin_cases j
  · change characterValueFunction (-1) (-1) (a 0) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction (-1) (-1) (a 2) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction (-1) (-1) (a 1) = auxiliaryTypeToComplex (-1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction (-1) (-1) (xa 0) = auxiliaryTypeToComplex (-1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change characterValueFunction (-1) (-1) (xa 1) = auxiliaryTypeToComplex (1:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]

private lemma char_row4 (j : Fin 5) :
    (FDRep.of matrixRepresentation).character (selectedQuaternionGroupElements j) = auxiliaryTypeToComplex (auxiliaryCharacterTable 4 j) := by
  fin_cases j
  · change (FDRep.of matrixRepresentation).character (a 0) = auxiliaryTypeToComplex (2:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change (FDRep.of matrixRepresentation).character (a 2) = auxiliaryTypeToComplex (-2:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change (FDRep.of matrixRepresentation).character (a 1) = auxiliaryTypeToComplex (0:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change (FDRep.of matrixRepresentation).character (xa 0) = auxiliaryTypeToComplex (0:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]
  · change (FDRep.of matrixRepresentation).character (xa 1) = auxiliaryTypeToComplex (0:AuxiliaryType); norm_num [-QuaternionGroup.a_zero]


/-- The character values of the indexed representations are given by the displayed auxiliary table. -/
lemma irreducibleRepresentations_character (i j : Fin 5) :
    (irreducibleRepresentations i).character (selectedQuaternionGroupElements j) = auxiliaryTypeToComplex (auxiliaryCharacterTable i j) := by
  fin_cases i
  · exact char_row0 j
  · exact char_row1 j
  · exact char_row2 j
  · exact char_row3 j
  · exact char_row4 j


private lemma Q5toC_inj_of_im_zero {q q' : AuxiliaryType} (h1 : q.im = 0) (h2 : q'.im = 0)
    (h : auxiliaryTypeToComplex q = auxiliaryTypeToComplex q') : q = q' := by
  rw [auxiliaryTypeToComplex, auxiliaryTypeToComplex, h1, h2] at h
  simp only [Rat.cast_zero, zero_mul, add_zero] at h
  exact AuxiliaryType.ext (by exact_mod_cast h) (h1.trans h2.symm)


private lemma chiQ8_im_zero (i c : Fin 5) : (auxiliaryCharacterTable i c).im = 0 := by
  fin_cases i <;> fin_cases c <;> rfl


private lemma chiQ8_injective : Function.Injective auxiliaryCharacterTable := by decide


/-- Representations at distinct indices are not isomorphic. -/
lemma irreducibleRepresentations_pairwise_nonisomorphic (i j : Fin 5) (hij : i ≠ j) : ¬ Nonempty (irreducibleRepresentations i ≅ irreducibleRepresentations j) := by
  rintro ⟨e⟩
  apply hij
  have hchar : (irreducibleRepresentations i).character = (irreducibleRepresentations j).character := FDRep.char_iso e
  have hcol : ∀ c, auxiliaryCharacterTable i c = auxiliaryCharacterTable j c := fun c =>
    Q5toC_inj_of_im_zero (chiQ8_im_zero i c) (chiQ8_im_zero j c)
      (by rw [← irreducibleRepresentations_character, ← irreducibleRepresentations_character, hchar])
  exact chiQ8_injective (funext hcol)


end RepresentationTheory.QuaternionGroupTwo
