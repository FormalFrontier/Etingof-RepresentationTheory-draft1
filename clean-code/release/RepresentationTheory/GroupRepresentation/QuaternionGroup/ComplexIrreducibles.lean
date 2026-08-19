/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Group.SimpleRepresentations
import RepresentationTheory.Alignment.Attribute

/-!
# Complex irreducible representations of the quaternion group
-/

open Complex Matrix QuaternionGroup

/-- The quaternion group of order eight has five conjugacy classes. -/
@[source_ref "Chapter4/Example4.3_Q8" (role := supporting)]
theorem RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.card_conjClasses_quaternionGroup :
    Fintype.card (ConjClasses (QuaternionGroup 2)) = 5 := by
  decide

/-- The sum of four copies of one squared and one copy of two squared equals the cardinality of the quaternion group of order eight. -/
theorem RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.four_one_sq_add_two_sq_eq_card :
    1 ^ 2 + 1 ^ 2 + 1 ^ 2 + 1 ^ 2 + 2 ^ 2 = Fintype.card (QuaternionGroup 2) := by
  decide

namespace RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles



/-- The first distinguished two-by-two complex matrix used in the quaternion-group representation. -/
noncomputable def firstGeneratorMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The second distinguished two-by-two complex matrix used in the quaternion-group representation. -/
noncomputable def secondGeneratorMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

/-- A third distinguished two-by-two complex matrix associated with the two generator matrices. -/
noncomputable def thirdDistinguishedMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; -Complex.I, 0]



/-- An auxiliary proposition depending on the displayed two-by-two complex matrix. -/
theorem auxiliary_fact3 : firstGeneratorMatrix ^ 2 = -1 := by
  simp only [pow_two, firstGeneratorMatrix, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two]

/-- An auxiliary proposition depending on the displayed two-by-two complex matrix. -/
theorem auxiliary_fact4 : secondGeneratorMatrix ^ 2 = -1 := by
  simp only [pow_two, secondGeneratorMatrix, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two, Complex.I_mul_I]

/-- An auxiliary proposition depending on the displayed two-by-two complex matrix. -/
theorem auxiliary_fact5 : thirdDistinguishedMatrix ^ 2 = -1 := by
  simp only [pow_two, thirdDistinguishedMatrix, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two, Complex.I_mul_I]

/-- The product of the first and second generator matrices is the third distinguished matrix. -/
theorem firstGeneratorMatrix_mul_secondGeneratorMatrix : firstGeneratorMatrix * secondGeneratorMatrix = thirdDistinguishedMatrix := by
  simp only [firstGeneratorMatrix, secondGeneratorMatrix, thirdDistinguishedMatrix, Matrix.mul_fin_two]
  norm_num [Complex.ext_iff]

/-- The first and second generator matrices anticommute. -/
theorem firstGeneratorMatrix_mul_secondGeneratorMatrix_eq_neg : firstGeneratorMatrix * secondGeneratorMatrix = -(secondGeneratorMatrix * firstGeneratorMatrix) := by
  simp only [firstGeneratorMatrix, secondGeneratorMatrix, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.neg_apply]



/-- The fourth power of the first generator matrix is the identity. -/
theorem firstGeneratorMatrix_pow_four : firstGeneratorMatrix ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, auxiliary_fact3]; simp

/-- The third power of the first generator matrix is its negative. -/
theorem firstGeneratorMatrix_pow_three : firstGeneratorMatrix ^ 3 = -firstGeneratorMatrix := by
  rw [pow_succ, auxiliary_fact3]; simp

/-- The product of the first and second generator matrices equals the second generator matrix times the third power of the first. -/
theorem firstGeneratorMatrix_mul_secondGeneratorMatrix_eq : firstGeneratorMatrix * secondGeneratorMatrix = secondGeneratorMatrix * firstGeneratorMatrix ^ 3 := by
  rw [firstGeneratorMatrix_pow_three, mul_neg, ← firstGeneratorMatrix_mul_secondGeneratorMatrix_eq_neg]

/-- A power of the first generator matrix depends only on its exponent modulo four. -/
theorem firstGeneratorMatrix_pow_eq_mod_four (m : ℕ) : firstGeneratorMatrix ^ m = firstGeneratorMatrix ^ (m % 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul, firstGeneratorMatrix_pow_four, one_pow, one_mul]

/-- Powers of the first generator matrix agree when the corresponding natural-number casts agree. -/
theorem firstGeneratorMatrix_pow_eq_of_natCast_eq {p q : ℕ} (h : (p : ZMod 4) = (q : ZMod 4)) :
    firstGeneratorMatrix ^ p = firstGeneratorMatrix ^ q := by
  have hmod : p % 4 = q % 4 := (ZMod.natCast_eq_natCast_iff p q 4).mp h
  rw [firstGeneratorMatrix_pow_eq_mod_four p, firstGeneratorMatrix_pow_eq_mod_four q, hmod]

/-- Moving a power of the first generator matrix past the second replaces the exponent by three times that exponent. -/
theorem firstGeneratorMatrix_pow_mul_secondGeneratorMatrix (m : ℕ) : firstGeneratorMatrix ^ m * secondGeneratorMatrix = secondGeneratorMatrix * firstGeneratorMatrix ^ (3 * m) := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, pow_succ firstGeneratorMatrix k, mul_assoc, firstGeneratorMatrix_mul_secondGeneratorMatrix_eq, ← mul_assoc, ih,
        mul_assoc, ← pow_add]



/-- The matrix-valued function underlying the distinguished two-dimensional quaternion-group representation. -/
noncomputable def standardMatrixValue : QuaternionGroup 2 → Matrix (Fin 2) (Fin 2) ℂ
  | .a i => firstGeneratorMatrix ^ i.val
  | .xa i => secondGeneratorMatrix * firstGeneratorMatrix ^ i.val

/-- On a cyclic element, the matrix-valued function is the corresponding power of the first generator matrix. -/
@[simp] theorem standardMatrixValue_a (i : ZMod 4) : standardMatrixValue (a i) = firstGeneratorMatrix ^ i.val := rfl
/-- On an element of the second coset, the matrix-valued function is the second generator matrix times a power of the first. -/
@[simp] theorem standardMatrixValue_xa (i : ZMod 4) : standardMatrixValue (xa i) = secondGeneratorMatrix * firstGeneratorMatrix ^ i.val := rfl

/-- Casting the natural representative of an element of integers modulo four recovers that element. -/
theorem natCast_zmod_val (i : ZMod 4) : ((i.val : ℕ) : ZMod 4) = i := ZMod.natCast_rightInverse i

/-- The square of the second generator matrix equals the square of the first generator matrix. -/
theorem secondGeneratorMatrix_sq : secondGeneratorMatrix ^ 2 = firstGeneratorMatrix ^ 2 := by rw [auxiliary_fact4, auxiliary_fact3]

/-- Sandwiching a power of the first generator matrix between two copies of the second gives the square of the first times its power with exponent multiplied by three. -/
theorem secondGeneratorMatrix_mul_pow_mul_secondGeneratorMatrix (p : ℕ) :
    secondGeneratorMatrix * firstGeneratorMatrix ^ p * secondGeneratorMatrix = firstGeneratorMatrix ^ 2 * firstGeneratorMatrix ^ (3 * p) := by
  rw [mul_assoc, firstGeneratorMatrix_pow_mul_secondGeneratorMatrix, ← mul_assoc, ← sq, secondGeneratorMatrix_sq]

/-- A two-dimensional complex matrix representation of the quaternion group of order eight. -/
noncomputable def standardMatrixRepresentation : QuaternionGroup 2 →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := standardMatrixValue
  map_one' := by
    change standardMatrixValue (a 0) = 1
    simp only [standardMatrixValue_a, ZMod.val_zero, pow_zero]
  map_mul' := by
    rintro (i | i) (j | j)
    · -- a i * a j = a (i + j)
      simp only [a_mul_a, standardMatrixValue_a, ← pow_add]
      exact firstGeneratorMatrix_pow_eq_of_natCast_eq (by revert i j; decide)
    · -- a i * xa j = xa (j - i)
      simp only [a_mul_xa, standardMatrixValue_a, standardMatrixValue_xa]
      rw [← mul_assoc, firstGeneratorMatrix_pow_mul_secondGeneratorMatrix, mul_assoc, ← pow_add]
      congr 1
      exact firstGeneratorMatrix_pow_eq_of_natCast_eq (by revert i j; decide)
    · -- xa i * a j = xa (i + j)
      simp only [xa_mul_a, standardMatrixValue_a, standardMatrixValue_xa, mul_assoc, ← pow_add]
      congr 1
      exact firstGeneratorMatrix_pow_eq_of_natCast_eq (by revert i j; decide)
    · -- xa i * xa j = a (2 + j - i)
      simp only [xa_mul_xa, standardMatrixValue_a, standardMatrixValue_xa]
      rw [← mul_assoc, secondGeneratorMatrix_mul_pow_mul_secondGeneratorMatrix, mul_assoc, ← pow_add, ← pow_add]
      exact firstGeneratorMatrix_pow_eq_of_natCast_eq (by revert i j; decide)



/-- The standard matrix representation sends a cyclic element to the corresponding power of the first generator matrix. -/
@[simp] theorem standardMatrixRepresentation_a (i : ZMod 4) : standardMatrixRepresentation (a i) = firstGeneratorMatrix ^ i.val := rfl
/-- The standard matrix representation sends a second-coset element to the second generator matrix times a power of the first. -/
@[simp] theorem standardMatrixRepresentation_xa (i : ZMod 4) : standardMatrixRepresentation (xa i) = secondGeneratorMatrix * firstGeneratorMatrix ^ i.val := rfl

/-- The standard matrix representation sends the first cyclic generator to the first generator matrix. -/
@[source_ref "Chapter4/Example4.3_Q8" (role := supporting)]
theorem standardMatrixRepresentation_a_one : standardMatrixRepresentation (a 1) = firstGeneratorMatrix := by
  rw [standardMatrixRepresentation_a, show ((1 : ZMod (2 * 2)).val) = 1 from rfl, pow_one]

/-- The standard matrix representation sends the zeroth element of the second coset to the second generator matrix. -/
@[source_ref "Chapter4/Example4.3_Q8" (role := supporting)]
theorem standardMatrixRepresentation_xa_zero : standardMatrixRepresentation (xa 0) = secondGeneratorMatrix := by
  rw [standardMatrixRepresentation_xa, show ((0 : ZMod (2 * 2)).val) = 0 from rfl, pow_zero, mul_one]

/-- The standard matrix representation sends the third element of the second coset to the third distinguished matrix. -/
@[source_ref "Chapter4/Example4.3_Q8" (role := supporting)]
theorem standardMatrixRepresentation_xa_three : standardMatrixRepresentation (xa 3) = thirdDistinguishedMatrix := by
  rw [standardMatrixRepresentation_xa, show ((3 : ZMod (2 * 2)).val) = 3 from rfl, firstGeneratorMatrix_pow_three, mul_neg,
    ← firstGeneratorMatrix_mul_secondGeneratorMatrix_eq_neg, firstGeneratorMatrix_mul_secondGeneratorMatrix]

/-- An auxiliary proposition depending on the displayed matrix-valued monoid homomorphism. -/
theorem auxiliary_fact2 : standardMatrixRepresentation (a 2) = -1 := by
  rw [standardMatrixRepresentation_a, show ((2 : ZMod (2 * 2)).val) = 2 from rfl]; exact auxiliary_fact3

/-- The two-dimensional complex linear representation induced by the standard matrix representation. -/
noncomputable def standardLinearRepresentation : Representation ℂ (QuaternionGroup 2) (Fin 2 → ℂ) :=
  (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin 2)).toAlgHom.toMonoidHom.comp standardMatrixRepresentation

/-- The complex vector space of functions on a two-element finite type has dimension two. -/
theorem finTwoComplex_finrank : Module.finrank ℂ (Fin 2 → ℂ) = 2 := by
  simp

open CategoryTheory Module



/-- Powers of a complex scalar that squares to one agree when their exponents have the same remainder modulo two. -/
theorem pow_eq_pow_of_mod_two_eq {α : ℂ} (hα : α ^ 2 = 1) {m n : ℕ} (h : m % 2 = n % 2) :
    α ^ m = α ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  conv_rhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_add, pow_mul, pow_mul, hα, one_pow, one_pow, h]

/-- A two-parameter complex-valued function on the quaternion group of order eight. -/
def linearCharacterValue (α β : ℂ) : QuaternionGroup 2 → ℂ
  | .a i => α ^ i.val
  | .xa i => β * α ^ i.val

/-- A complex-valued monoid homomorphism of the quaternion group determined by two scalars that square to one. -/
@[source_ref "Chapter4/Example4.3_Q8" (role := supporting)]
def linearCharacter (α β : ℂ) (hα : α ^ 2 = 1) (hβ : β ^ 2 = 1) : QuaternionGroup 2 →* ℂ where
  toFun := linearCharacterValue α β
  map_one' := by change linearCharacterValue α β (a 0) = 1; change α ^ (0 : ZMod 4).val = 1; simp
  map_mul' x y := by
    rcases x with i | i <;> rcases y with j | j
    · -- a i * a j = a (i + j)
      change linearCharacterValue α β (a i * a j) = linearCharacterValue α β (a i) * linearCharacterValue α β (a j)
      rw [a_mul_a]
      change α ^ (i + j).val = α ^ i.val * α ^ j.val
      have hp : (i + j).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      rw [← pow_add]
      exact pow_eq_pow_of_mod_two_eq hα hp
    · -- a i * xa j = xa (j - i)
      change linearCharacterValue α β (a i * xa j) = linearCharacterValue α β (a i) * linearCharacterValue α β (xa j)
      rw [a_mul_xa]
      change β * α ^ (j - i).val = α ^ i.val * (β * α ^ j.val)
      have hp : (j - i).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      have e : α ^ i.val * (β * α ^ j.val) = β * α ^ (i.val + j.val) := by rw [pow_add]; ring
      rw [e]
      exact congrArg (β * ·) (pow_eq_pow_of_mod_two_eq hα hp)
    · -- xa i * a j = xa (i + j)
      change linearCharacterValue α β (xa i * a j) = linearCharacterValue α β (xa i) * linearCharacterValue α β (a j)
      rw [xa_mul_a]
      change β * α ^ (i + j).val = β * α ^ i.val * α ^ j.val
      have hp : (i + j).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      rw [mul_assoc, ← pow_add]
      exact congrArg (β * ·) (pow_eq_pow_of_mod_two_eq hα hp)
    · -- xa i * xa j = a (2 + j - i)
      change linearCharacterValue α β (xa i * xa j) = linearCharacterValue α β (xa i) * linearCharacterValue α β (xa j)
      rw [xa_mul_xa]
      change α ^ ((2 : ZMod 4) + j - i).val = β * α ^ i.val * (β * α ^ j.val)
      have hp : ((2 : ZMod 4) + j - i).val % 2 = (i.val + j.val) % 2 := by revert i j; decide
      have e : β * α ^ i.val * (β * α ^ j.val) = β ^ 2 * α ^ (i.val + j.val) := by
        rw [pow_add]; ring
      rw [e, hβ, one_mul]
      exact pow_eq_pow_of_mod_two_eq hα hp

/-- The one-dimensional complex representation associated with a complex-valued monoid homomorphism of the quaternion group. -/
@[source_ref "Chapter4/Example4.3_Q8" (role := supporting)]
def representationOfLinearCharacter (χ : QuaternionGroup 2 →* ℂ) : Representation ℂ (QuaternionGroup 2) ℂ where
  toFun g := χ g • LinearMap.id
  map_one' := by rw [map_one, one_smul]; rfl
  map_mul' g h := by
    ext
    simp only [map_mul, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      smul_smul]

/-- The character of the representation associated with a linear character is the original monoid homomorphism. -/
lemma representationOfLinearCharacter_character (χ : QuaternionGroup 2 →* ℂ) (g : QuaternionGroup 2) :
    (FDRep.of (representationOfLinearCharacter χ)).character g = χ g := by
  rw [show (FDRep.of (representationOfLinearCharacter χ)).character g = LinearMap.trace ℂ ℂ (representationOfLinearCharacter χ g) from rfl]
  change LinearMap.trace ℂ ℂ (χ g • LinearMap.id) = χ g
  rw [map_smul, LinearMap.trace_id]
  simp

/-- An auxiliary distinguished complex-valued linear character of the quaternion group. -/
def linearCharacter_aux4 : QuaternionGroup 2 →* ℂ := linearCharacter 1 1 (by norm_num) (by norm_num)
/-- An auxiliary distinguished complex-valued linear character of the quaternion group. -/
def linearCharacter_aux3 : QuaternionGroup 2 →* ℂ := linearCharacter 1 (-1) (by norm_num) (by norm_num)
/-- An auxiliary distinguished complex-valued linear character of the quaternion group. -/
def linearCharacter_aux2 : QuaternionGroup 2 →* ℂ := linearCharacter (-1) 1 (by norm_num) (by norm_num)
/-- An auxiliary distinguished complex-valued linear character of the quaternion group. -/
def linearCharacter_aux1 : QuaternionGroup 2 →* ℂ := linearCharacter (-1) (-1) (by norm_num) (by norm_num)

/-- An auxiliary distinguished one-dimensional complex representation of the quaternion group. -/
noncomputable def linearRepresentation_aux4 : FDRep ℂ (QuaternionGroup 2) := FDRep.of (representationOfLinearCharacter linearCharacter_aux4)
/-- An auxiliary distinguished one-dimensional complex representation of the quaternion group. -/
noncomputable def linearRepresentation_aux3 : FDRep ℂ (QuaternionGroup 2) := FDRep.of (representationOfLinearCharacter linearCharacter_aux3)
/-- An auxiliary distinguished one-dimensional complex representation of the quaternion group. -/
noncomputable def linearRepresentation_aux2 : FDRep ℂ (QuaternionGroup 2) := FDRep.of (representationOfLinearCharacter linearCharacter_aux2)
/-- An auxiliary distinguished one-dimensional complex representation of the quaternion group. -/
noncomputable def linearRepresentation_aux1 : FDRep ℂ (QuaternionGroup 2) := FDRep.of (representationOfLinearCharacter linearCharacter_aux1)



/-- A map enumerating the quaternion group of order eight by a finite type with eight elements. -/
def finEightToQuaternionGroup : Fin 8 → QuaternionGroup 2 :=
  ![a 0, a 1, a 2, a 3, xa 0, xa 1, xa 2, xa 3]

/-- The finite enumeration of the quaternion group of order eight is bijective. -/
lemma finEightToQuaternionGroup_bijective : Function.Bijective finEightToQuaternionGroup := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨by decide, by decide⟩

/-- A sum over the quaternion group of order eight expands as the sum of its values on the four cyclic elements and four second-coset elements. -/
lemma sum_quaternionGroup_eq (f : QuaternionGroup 2 → ℂ) :
    ∑ g, f g = f (a 0) + f (a 1) + f (a 2) + f (a 3)
             + f (xa 0) + f (xa 1) + f (xa 2) + f (xa 3) := by
  rw [← Equiv.sum_comp (Equiv.ofBijective finEightToQuaternionGroup finEightToQuaternionGroup_bijective) f, Fin.sum_univ_eight]
  simp only [Equiv.ofBijective_apply, finEightToQuaternionGroup]
  rfl

/-- The sum of a linear character times its value on inverses equals the order of the quaternion group. -/
lemma representationOfLinearCharacter_character_norm (χ : QuaternionGroup 2 →* ℂ) :
    ∑ g : QuaternionGroup 2, (FDRep.of (representationOfLinearCharacter χ)).character g
      * (FDRep.of (representationOfLinearCharacter χ)).character g⁻¹ = Nat.card (QuaternionGroup 2) := by
  have hone : ∀ g : QuaternionGroup 2, χ g * χ g⁻¹ = 1 := fun g => by
    rw [← map_mul, mul_inv_cancel, map_one]
  simp only [representationOfLinearCharacter_character]
  rw [Finset.sum_congr rfl (fun g _ => hone g), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]



/-- The distinguished two-dimensional finite-dimensional complex representation of the quaternion group. -/
noncomputable def standardRepresentation : FDRep ℂ (QuaternionGroup 2) := FDRep.of standardLinearRepresentation

/-- The standard linear action is matrix-vector multiplication by the corresponding representation matrix. -/
lemma standardLinearRepresentation_apply (g : QuaternionGroup 2) (v : Fin 2 → ℂ) :
    standardLinearRepresentation g v = (standardMatrixRepresentation g).mulVec v := by
  change (Matrix.toLinAlgEquiv' (standardMatrixRepresentation g)) v = _
  rw [Matrix.toLinAlgEquiv'_apply]

/-- The character of the distinguished two-dimensional representation equals the trace of its matrix representation. -/
lemma standardRepresentation_character_eq_trace (g : QuaternionGroup 2) :
    standardRepresentation.character g = (standardMatrixRepresentation g).trace := by
  rw [show standardRepresentation.character g = LinearMap.trace ℂ (Fin 2 → ℂ) (standardLinearRepresentation g) from rfl]
  have h : standardLinearRepresentation g = Matrix.toLin' (standardMatrixRepresentation g) := by
    apply LinearMap.ext; intro v
    rw [standardLinearRepresentation_apply, Matrix.toLin'_apply]
  rw [h, Matrix.trace_toLin'_eq]



/-- The character of the distinguished two-dimensional representation at the zeroth cyclic element is two. -/
lemma standardRepresentation_character_a_zero : standardRepresentation.character (a 0) = 2 := by
  rw [standardRepresentation_character_eq_trace, standardMatrixRepresentation_a, show (0 : ZMod (2 * 2)).val = 0 from rfl, pow_zero]
  simp

/-- The character of the distinguished two-dimensional representation at the first cyclic element is zero. -/
lemma standardRepresentation_character_a_one : standardRepresentation.character (a 1) = 0 := by
  rw [standardRepresentation_character_eq_trace, standardMatrixRepresentation_a, show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one]
  simp [firstGeneratorMatrix, Matrix.trace_fin_two]

/-- An auxiliary proposition depending on the displayed finite-dimensional complex representation. -/
lemma auxiliary_fact1 : standardRepresentation.character (a 2) = -2 := by
  rw [standardRepresentation_character_eq_trace, standardMatrixRepresentation_a, show (2 : ZMod (2 * 2)).val = 2 from rfl, auxiliary_fact3]
  simp

/-- The character of the distinguished two-dimensional representation at the third cyclic element is zero. -/
lemma standardRepresentation_character_a_three : standardRepresentation.character (a 3) = 0 := by
  rw [standardRepresentation_character_eq_trace, standardMatrixRepresentation_a, show (3 : ZMod (2 * 2)).val = 3 from rfl, firstGeneratorMatrix_pow_three]
  simp [firstGeneratorMatrix, Matrix.trace_fin_two]

/-- The character of the distinguished two-dimensional representation at the zeroth element of the second coset is zero. -/
lemma standardRepresentation_character_xa_zero : standardRepresentation.character (xa 0) = 0 := by
  rw [standardRepresentation_character_eq_trace, standardMatrixRepresentation_xa, show (0 : ZMod (2 * 2)).val = 0 from rfl, pow_zero, mul_one]
  simp [secondGeneratorMatrix, Matrix.trace_fin_two]

/-- The character of the distinguished two-dimensional representation at the first element of the second coset is zero. -/
lemma standardRepresentation_character_xa_one : standardRepresentation.character (xa 1) = 0 := by
  rw [standardRepresentation_character_eq_trace, standardMatrixRepresentation_xa, show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one]
  simp [secondGeneratorMatrix, firstGeneratorMatrix, Matrix.trace_fin_two]

/-- The character of the distinguished two-dimensional representation at the second element of the second coset is zero. -/
lemma standardRepresentation_character_xa_two : standardRepresentation.character (xa 2) = 0 := by
  rw [standardRepresentation_character_eq_trace, standardMatrixRepresentation_xa, show (2 : ZMod (2 * 2)).val = 2 from rfl, auxiliary_fact3]
  simp [secondGeneratorMatrix, Matrix.trace_fin_two]

/-- The character of the distinguished two-dimensional representation at the third element of the second coset is zero. -/
lemma standardRepresentation_character_xa_three : standardRepresentation.character (xa 3) = 0 := by
  rw [standardRepresentation_character_eq_trace, standardMatrixRepresentation_xa, show (3 : ZMod (2 * 2)).val = 3 from rfl, firstGeneratorMatrix_pow_three]
  simp [secondGeneratorMatrix, firstGeneratorMatrix, Matrix.trace_fin_two]

/-- The sum of the standard character times its value on inverses equals the order of the quaternion group. -/
lemma standardRepresentation_character_norm :
    ∑ g : QuaternionGroup 2, standardRepresentation.character g * standardRepresentation.character g⁻¹
      = Nat.card (QuaternionGroup 2) := by
  rw [sum_quaternionGroup_eq (fun g => standardRepresentation.character g * standardRepresentation.character g⁻¹)]
  simp only [show (a 0 : QuaternionGroup 2)⁻¹ = a 0 from by decide,
    show (a 1 : QuaternionGroup 2)⁻¹ = a 3 from by decide,
    show (a 2 : QuaternionGroup 2)⁻¹ = a 2 from by decide,
    show (a 3 : QuaternionGroup 2)⁻¹ = a 1 from by decide,
    show (xa 0 : QuaternionGroup 2)⁻¹ = xa 2 from by decide,
    show (xa 1 : QuaternionGroup 2)⁻¹ = xa 3 from by decide,
    show (xa 2 : QuaternionGroup 2)⁻¹ = xa 0 from by decide,
    show (xa 3 : QuaternionGroup 2)⁻¹ = xa 1 from by decide,
    standardRepresentation_character_a_zero, standardRepresentation_character_a_one, auxiliary_fact1, standardRepresentation_character_a_three, standardRepresentation_character_xa_zero, standardRepresentation_character_xa_one, standardRepresentation_character_xa_two, standardRepresentation_character_xa_three]
  rw [show Nat.card (QuaternionGroup 2) = 8 from by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]]
  norm_num



/-- The indicated auxiliary one-dimensional quaternion-group representation is simple. -/
lemma linearRepresentation_aux4_simple : Simple linearRepresentation_aux4 :=
  (FDRep.simple_iff_char_is_norm_one _).mpr (representationOfLinearCharacter_character_norm linearCharacter_aux4)
/-- The indicated auxiliary one-dimensional quaternion-group representation is simple. -/
lemma linearRepresentation_aux3_simple : Simple linearRepresentation_aux3 :=
  (FDRep.simple_iff_char_is_norm_one _).mpr (representationOfLinearCharacter_character_norm linearCharacter_aux3)
/-- The indicated auxiliary one-dimensional quaternion-group representation is simple. -/
lemma linearRepresentation_aux2_simple : Simple linearRepresentation_aux2 :=
  (FDRep.simple_iff_char_is_norm_one _).mpr (representationOfLinearCharacter_character_norm linearCharacter_aux2)
/-- The indicated auxiliary one-dimensional quaternion-group representation is simple. -/
lemma linearRepresentation_aux1_simple : Simple linearRepresentation_aux1 :=
  (FDRep.simple_iff_char_is_norm_one _).mpr (representationOfLinearCharacter_character_norm linearCharacter_aux1)

/-- The distinguished two-dimensional quaternion-group representation is simple. -/
@[source_ref "Chapter4/Example4.3_Q8" (role := supporting)]
lemma standardRepresentation_simple : Simple standardRepresentation :=
  (FDRep.simple_iff_char_is_norm_one _).mpr standardRepresentation_character_norm



/-- The indicated auxiliary one-dimensional representation has complex dimension one. -/
lemma linearRepresentation_aux4_finrank : finrank ℂ (linearRepresentation_aux4 : Type) = 1 := by
  have h := FDRep.char_one linearRepresentation_aux4
  rw [show linearRepresentation_aux4 = FDRep.of (representationOfLinearCharacter linearCharacter_aux4) from rfl, representationOfLinearCharacter_character, map_one] at h
  exact_mod_cast h.symm

/-- The indicated auxiliary one-dimensional representation has complex dimension one. -/
lemma linearRepresentation_aux3_finrank : finrank ℂ (linearRepresentation_aux3 : Type) = 1 := by
  have h := FDRep.char_one linearRepresentation_aux3
  rw [show linearRepresentation_aux3 = FDRep.of (representationOfLinearCharacter linearCharacter_aux3) from rfl, representationOfLinearCharacter_character, map_one] at h
  exact_mod_cast h.symm

/-- The indicated auxiliary one-dimensional representation has complex dimension one. -/
lemma linearRepresentation_aux2_finrank : finrank ℂ (linearRepresentation_aux2 : Type) = 1 := by
  have h := FDRep.char_one linearRepresentation_aux2
  rw [show linearRepresentation_aux2 = FDRep.of (representationOfLinearCharacter linearCharacter_aux2) from rfl, representationOfLinearCharacter_character, map_one] at h
  exact_mod_cast h.symm

/-- The indicated auxiliary one-dimensional representation has complex dimension one. -/
lemma linearRepresentation_aux1_finrank : finrank ℂ (linearRepresentation_aux1 : Type) = 1 := by
  have h := FDRep.char_one linearRepresentation_aux1
  rw [show linearRepresentation_aux1 = FDRep.of (representationOfLinearCharacter linearCharacter_aux1) from rfl, representationOfLinearCharacter_character, map_one] at h
  exact_mod_cast h.symm

/-- The distinguished quaternion-group representation has complex dimension two. -/
lemma standardRepresentation_finrank : finrank ℂ (standardRepresentation : Type) = 2 := by
  have h := FDRep.char_one standardRepresentation
  rw [show (1 : QuaternionGroup 2) = a 0 from QuaternionGroup.one_def, standardRepresentation_character_a_zero] at h
  exact_mod_cast h.symm



/-- Two one-dimensional representations are not isomorphic if their defining characters differ at some group element. -/
lemma representationOfLinearCharacter_not_iso_of_ne (chi psi : QuaternionGroup 2 →* ℂ)
    (g : QuaternionGroup 2) (h : chi g ≠ psi g) :
    ¬ Nonempty (FDRep.of (representationOfLinearCharacter chi) ≅ FDRep.of (representationOfLinearCharacter psi)) := by
  rintro ⟨e⟩
  apply h
  simpa only [representationOfLinearCharacter_character] using congrFun (FDRep.char_iso e) g

/-- The indicated auxiliary one-dimensional representations are not isomorphic. -/
lemma linearRepresentation_aux4_not_iso_linearRepresentation_aux3 : ¬ Nonempty (linearRepresentation_aux4 ≅ linearRepresentation_aux3) := by
  simpa only [linearRepresentation_aux4, linearRepresentation_aux3] using representationOfLinearCharacter_not_iso_of_ne linearCharacter_aux4 linearCharacter_aux3 (xa 0) (by
    norm_num [linearCharacter_aux4, linearCharacter_aux3, linearCharacter, linearCharacterValue])

/-- The indicated auxiliary one-dimensional representations are not isomorphic. -/
lemma linearRepresentation_aux4_not_iso_linearRepresentation_aux2 : ¬ Nonempty (linearRepresentation_aux4 ≅ linearRepresentation_aux2) := by
  simpa only [linearRepresentation_aux4, linearRepresentation_aux2] using representationOfLinearCharacter_not_iso_of_ne linearCharacter_aux4 linearCharacter_aux2 (a 1) (by
    norm_num [linearCharacter_aux4, linearCharacter_aux2, linearCharacter, linearCharacterValue, show (1 : ZMod 4).val = 1 from rfl])

/-- The indicated auxiliary one-dimensional representations are not isomorphic. -/
lemma linearRepresentation_aux4_not_iso_linearRepresentation_aux1 : ¬ Nonempty (linearRepresentation_aux4 ≅ linearRepresentation_aux1) := by
  simpa only [linearRepresentation_aux4, linearRepresentation_aux1] using representationOfLinearCharacter_not_iso_of_ne linearCharacter_aux4 linearCharacter_aux1 (a 1) (by
    norm_num [linearCharacter_aux4, linearCharacter_aux1, linearCharacter, linearCharacterValue, show (1 : ZMod 4).val = 1 from rfl])

/-- The indicated auxiliary one-dimensional representations are not isomorphic. -/
lemma linearRepresentation_aux3_not_iso_linearRepresentation_aux2 : ¬ Nonempty (linearRepresentation_aux3 ≅ linearRepresentation_aux2) := by
  simpa only [linearRepresentation_aux3, linearRepresentation_aux2] using representationOfLinearCharacter_not_iso_of_ne linearCharacter_aux3 linearCharacter_aux2 (a 1) (by
    norm_num [linearCharacter_aux3, linearCharacter_aux2, linearCharacter, linearCharacterValue, show (1 : ZMod 4).val = 1 from rfl])

/-- The indicated auxiliary one-dimensional representations are not isomorphic. -/
lemma linearRepresentation_aux3_not_iso_linearRepresentation_aux1 : ¬ Nonempty (linearRepresentation_aux3 ≅ linearRepresentation_aux1) := by
  simpa only [linearRepresentation_aux3, linearRepresentation_aux1] using representationOfLinearCharacter_not_iso_of_ne linearCharacter_aux3 linearCharacter_aux1 (a 1) (by
    norm_num [linearCharacter_aux3, linearCharacter_aux1, linearCharacter, linearCharacterValue, show (1 : ZMod 4).val = 1 from rfl])

/-- The indicated auxiliary one-dimensional representations are not isomorphic. -/
lemma linearRepresentation_aux2_not_iso_linearRepresentation_aux1 : ¬ Nonempty (linearRepresentation_aux2 ≅ linearRepresentation_aux1) := by
  simpa only [linearRepresentation_aux2, linearRepresentation_aux1] using representationOfLinearCharacter_not_iso_of_ne linearCharacter_aux2 linearCharacter_aux1 (xa 0) (by
    norm_num [linearCharacter_aux2, linearCharacter_aux1, linearCharacter, linearCharacterValue])

/-- The four distinguished one-dimensional representations of the quaternion group are pairwise nonisomorphic. -/
theorem linearRepresentations_pairwise_nonisomorphic :
    ¬ Nonempty (linearRepresentation_aux4 ≅ linearRepresentation_aux3) ∧ ¬ Nonempty (linearRepresentation_aux4 ≅ linearRepresentation_aux2) ∧
      ¬ Nonempty (linearRepresentation_aux4 ≅ linearRepresentation_aux1) ∧ ¬ Nonempty (linearRepresentation_aux3 ≅ linearRepresentation_aux2) ∧
      ¬ Nonempty (linearRepresentation_aux3 ≅ linearRepresentation_aux1) ∧ ¬ Nonempty (linearRepresentation_aux2 ≅ linearRepresentation_aux1) :=
  ⟨linearRepresentation_aux4_not_iso_linearRepresentation_aux3, linearRepresentation_aux4_not_iso_linearRepresentation_aux2, linearRepresentation_aux4_not_iso_linearRepresentation_aux1,
    linearRepresentation_aux3_not_iso_linearRepresentation_aux2, linearRepresentation_aux3_not_iso_linearRepresentation_aux1, linearRepresentation_aux2_not_iso_linearRepresentation_aux1⟩

private lemma not_iso_standardRepresentation_of_finrank_one {V : FDRep ℂ (QuaternionGroup 2)}
    (hV : finrank ℂ (V : Type) = 1) : ¬ Nonempty (V ≅ standardRepresentation) := by
  rintro ⟨e⟩
  have h := (FDRep.isoToLinearEquiv e).finrank_eq
  rw [hV, standardRepresentation_finrank] at h
  omega

/-- The indicated auxiliary one-dimensional representation is not isomorphic to the distinguished two-dimensional representation. -/
lemma linearRepresentation_aux4_not_iso_standardRepresentation : ¬ Nonempty (linearRepresentation_aux4 ≅ standardRepresentation) :=
  not_iso_standardRepresentation_of_finrank_one linearRepresentation_aux4_finrank

/-- The indicated auxiliary one-dimensional representation is not isomorphic to the distinguished two-dimensional representation. -/
lemma linearRepresentation_aux3_not_iso_standardRepresentation : ¬ Nonempty (linearRepresentation_aux3 ≅ standardRepresentation) :=
  not_iso_standardRepresentation_of_finrank_one linearRepresentation_aux3_finrank

/-- The indicated auxiliary one-dimensional representation is not isomorphic to the distinguished two-dimensional representation. -/
lemma linearRepresentation_aux2_not_iso_standardRepresentation : ¬ Nonempty (linearRepresentation_aux2 ≅ standardRepresentation) :=
  not_iso_standardRepresentation_of_finrank_one linearRepresentation_aux2_finrank

/-- The indicated auxiliary one-dimensional representation is not isomorphic to the distinguished two-dimensional representation. -/
lemma linearRepresentation_aux1_not_iso_standardRepresentation : ¬ Nonempty (linearRepresentation_aux1 ≅ standardRepresentation) :=
  not_iso_standardRepresentation_of_finrank_one linearRepresentation_aux1_finrank

/-- The five distinguished complex representations of the quaternion group are pairwise nonisomorphic. -/
@[source_ref "Chapter4/Example4.3_Q8" (role := supporting)]
theorem distinguishedRepresentations_pairwise_nonisomorphic :
    ¬ Nonempty (linearRepresentation_aux4 ≅ linearRepresentation_aux3) ∧ ¬ Nonempty (linearRepresentation_aux4 ≅ linearRepresentation_aux2) ∧
      ¬ Nonempty (linearRepresentation_aux4 ≅ linearRepresentation_aux1) ∧ ¬ Nonempty (linearRepresentation_aux4 ≅ standardRepresentation) ∧
      ¬ Nonempty (linearRepresentation_aux3 ≅ linearRepresentation_aux2) ∧ ¬ Nonempty (linearRepresentation_aux3 ≅ linearRepresentation_aux1) ∧
      ¬ Nonempty (linearRepresentation_aux3 ≅ standardRepresentation) ∧ ¬ Nonempty (linearRepresentation_aux2 ≅ linearRepresentation_aux1) ∧
      ¬ Nonempty (linearRepresentation_aux2 ≅ standardRepresentation) ∧ ¬ Nonempty (linearRepresentation_aux1 ≅ standardRepresentation) :=
  ⟨linearRepresentation_aux4_not_iso_linearRepresentation_aux3, linearRepresentation_aux4_not_iso_linearRepresentation_aux2, linearRepresentation_aux4_not_iso_linearRepresentation_aux1,
    linearRepresentation_aux4_not_iso_standardRepresentation, linearRepresentation_aux3_not_iso_linearRepresentation_aux2, linearRepresentation_aux3_not_iso_linearRepresentation_aux1,
    linearRepresentation_aux3_not_iso_standardRepresentation, linearRepresentation_aux2_not_iso_linearRepresentation_aux1, linearRepresentation_aux2_not_iso_standardRepresentation,
    linearRepresentation_aux1_not_iso_standardRepresentation⟩

/-- The sum of the squared dimensions of the four distinguished one-dimensional representations and the distinguished two-dimensional representation equals the group order. -/
@[source_ref "Chapter4/Example4.3_Q8" (role := supporting)]
theorem sum_sq_finrank_distinguishedRepresentations :
    finrank ℂ (linearRepresentation_aux4 : Type) ^ 2 + finrank ℂ (linearRepresentation_aux3 : Type) ^ 2
      + finrank ℂ (linearRepresentation_aux2 : Type) ^ 2 + finrank ℂ (linearRepresentation_aux1 : Type) ^ 2
      + finrank ℂ (standardRepresentation : Type) ^ 2 = Fintype.card (QuaternionGroup 2) := by
  rw [linearRepresentation_aux4_finrank, linearRepresentation_aux3_finrank, linearRepresentation_aux2_finrank, linearRepresentation_aux1_finrank, standardRepresentation_finrank]
  decide



/-- Every simple finite-dimensional complex representation of the quaternion group of order eight is isomorphic to the distinguished two-dimensional representation or one of four distinguished one-dimensional representations. -/
@[source_ref "Chapter4/Example4.3_Q8" (role := supporting)]
theorem simpleRepresentation_iso_standard_or_linear (S : FDRep ℂ (QuaternionGroup 2)) [Simple S] :
    Nonempty (S ≅ linearRepresentation_aux4) ∨ Nonempty (S ≅ linearRepresentation_aux3) ∨ Nonempty (S ≅ linearRepresentation_aux2) ∨
      Nonempty (S ≅ linearRepresentation_aux1) ∨ Nonempty (S ≅ standardRepresentation) := by
  classical
  letI : Invertible (Fintype.card (QuaternionGroup 2) : ℂ) :=
    invertibleOfNonzero (by norm_num [QuaternionGroup.card])
  obtain ⟨n, V, _, _, hsurj, hn⟩ :=
    RepresentationTheory.Group.SimpleRepresentations.exists_simpleReps_card_eq_conjClasses (G := QuaternionGroup 2) (k := ℂ)
  obtain ⟨a, ⟨ea⟩⟩ := hsurj linearRepresentation_aux4 linearRepresentation_aux4_simple
  obtain ⟨b, ⟨eb⟩⟩ := hsurj linearRepresentation_aux3 linearRepresentation_aux3_simple
  obtain ⟨c, ⟨ec⟩⟩ := hsurj linearRepresentation_aux2 linearRepresentation_aux2_simple
  obtain ⟨d, ⟨ed⟩⟩ := hsurj linearRepresentation_aux1 linearRepresentation_aux1_simple
  obtain ⟨e, ⟨ee⟩⟩ := hsurj standardRepresentation standardRepresentation_simple
  obtain ⟨s, ⟨es⟩⟩ := hsurj S inferInstance
  have hab : a ≠ b := by rintro rfl; exact linearRepresentation_aux4_not_iso_linearRepresentation_aux3 ⟨ea ≪≫ eb.symm⟩
  have hac : a ≠ c := by rintro rfl; exact linearRepresentation_aux4_not_iso_linearRepresentation_aux2 ⟨ea ≪≫ ec.symm⟩
  have had : a ≠ d := by rintro rfl; exact linearRepresentation_aux4_not_iso_linearRepresentation_aux1 ⟨ea ≪≫ ed.symm⟩
  have hae : a ≠ e := by rintro rfl; exact linearRepresentation_aux4_not_iso_standardRepresentation ⟨ea ≪≫ ee.symm⟩
  have hbc : b ≠ c := by rintro rfl; exact linearRepresentation_aux3_not_iso_linearRepresentation_aux2 ⟨eb ≪≫ ec.symm⟩
  have hbd : b ≠ d := by rintro rfl; exact linearRepresentation_aux3_not_iso_linearRepresentation_aux1 ⟨eb ≪≫ ed.symm⟩
  have hbe : b ≠ e := by rintro rfl; exact linearRepresentation_aux3_not_iso_standardRepresentation ⟨eb ≪≫ ee.symm⟩
  have hcd : c ≠ d := by rintro rfl; exact linearRepresentation_aux2_not_iso_linearRepresentation_aux1 ⟨ec ≪≫ ed.symm⟩
  have hce : c ≠ e := by rintro rfl; exact linearRepresentation_aux2_not_iso_standardRepresentation ⟨ec ≪≫ ee.symm⟩
  have hde : d ≠ e := by rintro rfl; exact linearRepresentation_aux1_not_iso_standardRepresentation ⟨ed ≪≫ ee.symm⟩
  have hn5 : n = 5 := hn.trans RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.card_conjClasses_quaternionGroup
  have hcard : ({a, b, c, d, e} : Finset (Fin n)).card = 5 := by
    simp [hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde]
  have hall : ({a, b, c, d, e} : Finset (Fin n)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [hn5] using hcard
  have hs : s = a ∨ s = b ∨ s = c ∨ s = d ∨ s = e := by
    have : s ∈ ({a, b, c, d, e} : Finset (Fin n)) := by rw [hall]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨es ≪≫ ea.symm⟩
  · exact Or.inr (Or.inl ⟨es ≪≫ eb.symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨es ≪≫ ec.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨es ≪≫ ed.symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨es ≪≫ ee.symm⟩)))



/-- An element of the quaternion group of order eight lies in the center exactly when it is the zeroth or second cyclic element. -/
@[source_ref "Chapter4/Example4.3_Q8" (role := supporting)]
theorem mem_center_iff (g : QuaternionGroup 2) :
    g ∈ Subgroup.center (QuaternionGroup 2) ↔ g = a 0 ∨ g = a 2 := by
  rw [Subgroup.mem_center_iff]
  revert g
  decide

end RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles
