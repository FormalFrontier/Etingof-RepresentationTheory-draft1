/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.PermutationActionRepresentations
import RepresentationTheory.Group.SimpleRepresentations
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.AlternatingGroupFourRepresentations

open CategoryTheory Equiv

noncomputable section

set_option linter.unusedSectionVars false

/-- A subgroup of the permutation group on four points. -/
abbrev alternatingSubgroupFour := alternatingGroup (Fin 4)

/-- The specified subgroup of permutations on four points has twelve elements. -/
lemma card_alternatingSubgroupFour : Fintype.card alternatingSubgroupFour = 12 := by
  rw [card_alternatingGroup, Fintype.card_fin]; decide

/-- An auxiliary map from the specified subgroup to a three-element finite type. -/
def auxiliaryFinClassIndex (g : alternatingSubgroupFour) : Fin 3 :=
  RepresentationTheory.PermutationActionRepresentations.actOnFinThree (g : Equiv.Perm (Fin 4)) 0

/-- A map from the specified subgroup to the additive integers modulo three. -/
def additiveClassIndex (g : alternatingSubgroupFour) : ZMod 3 := -((auxiliaryFinClassIndex g).val : ZMod 3)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in

/-- The additive class index sends multiplication in the subgroup to addition modulo three. -/
lemma additiveClassIndex_mul (g h : alternatingSubgroupFour) : additiveClassIndex (g * h) = additiveClassIndex g + additiveClassIndex h := by
  revert g h; decide

/-- The additive class index of the identity is zero. -/
lemma additiveClassIndex_one : additiveClassIndex 1 = 0 := by decide

/-- A homomorphism from the specified subgroup to the multiplicative group of integers modulo three. -/
def conjugacyQuotientHom : alternatingSubgroupFour →* Multiplicative (ZMod 3) where
  toFun g := Multiplicative.ofAdd (additiveClassIndex g)
  map_one' := congrArg Multiplicative.ofAdd additiveClassIndex_one
  map_mul' g h := congrArg Multiplicative.ofAdd (additiveClassIndex_mul g h)

/-- The quotient homomorphism sends an element to the multiplicative form of its additive class index. -/
@[simp] lemma conjugacyQuotientHom_apply (g : alternatingSubgroupFour) : conjugacyQuotientHom g = Multiplicative.ofAdd (additiveClassIndex g) := rfl

set_option maxRecDepth 10000 in

/-- The quotient homomorphism onto the multiplicative integers modulo three is surjective. -/
lemma conjugacyQuotientHom_surjective : Function.Surjective conjugacyQuotientHom := by
  intro x
  have : ∀ y : ZMod 3, ∃ g : alternatingSubgroupFour, additiveClassIndex g = y := by decide
  obtain ⟨g, hg⟩ := this (Multiplicative.toAdd x)
  exact ⟨g, by rw [conjugacyQuotientHom_apply, hg]; rfl⟩

set_option maxRecDepth 10000 in

/-- The kernel of the auxiliary quotient homomorphism is the Klein four subgroup. -/
lemma ker_conjugacyQuotientHom : conjugacyQuotientHom.ker = alternatingGroup.kleinFour (Fin 4) := by
  have hfwd : ∀ g : alternatingSubgroupFour, additiveClassIndex g = 0 → (g = 1 ∨ (g : Equiv.Perm (Fin 4)).cycleType = {2, 2}) := by
    decide
  have hbwd : ∀ g : alternatingSubgroupFour, (g : Equiv.Perm (Fin 4)).cycleType = {2, 2} → additiveClassIndex g = 0 := by decide
  refine le_antisymm (fun g hg => ?_) ?_
  · rcases hfwd g (Multiplicative.ofAdd.injective (MonoidHom.mem_ker.mp hg)) with rfl | h
    · exact one_mem _
    · exact Subgroup.subset_closure h
  · rw [alternatingGroup.kleinFour, Subgroup.closure_le]
    exact fun g hg => MonoidHom.mem_ker.mpr (congrArg Multiplicative.ofAdd (hbwd g hg))

/-- The Klein four subgroup of permutations on four points is normal. -/
lemma kleinFour_normal : (alternatingGroup.kleinFour (Fin 4)).Normal :=
  alternatingGroup.normal_kleinFour (by simp)

/-- An auxiliary unit of the complex numbers. -/
def auxiliaryComplexUnit : ℂˣ := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / 3)) (Complex.exp_ne_zero _)

/-- An auxiliary complex scalar. -/
def auxiliaryComplexScalar : ℂ := (auxiliaryComplexUnit : ℂ)

/-- The auxiliary complex scalar is the exponential of two pi times the imaginary unit divided by three. -/
lemma auxiliaryComplexScalar_eq_exp : auxiliaryComplexScalar = Complex.exp (2 * Real.pi * Complex.I / 3) := rfl

/-- The cube of the auxiliary complex unit is one. -/
lemma auxiliaryComplexUnit_pow_three : auxiliaryComplexUnit ^ 3 = 1 := by
  apply Units.ext
  have hval : ((auxiliaryComplexUnit ^ 3 : ℂˣ) : ℂ) = (Complex.exp (2 * Real.pi * Complex.I / 3)) ^ 3 := by
    simp [auxiliaryComplexUnit]
  rw [hval, ← Complex.exp_nat_mul,
    show ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3) = 2 * Real.pi * Complex.I by
      push_cast; ring, Complex.exp_two_pi_mul_I, Units.val_one]

/-- Powers of the auxiliary complex unit depend only on the exponent modulo three. -/
lemma auxiliaryComplexUnit_pow_mod_three (m : ℕ) : auxiliaryComplexUnit ^ (m % 3) = auxiliaryComplexUnit ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 3]
  rw [pow_add, pow_mul, auxiliaryComplexUnit_pow_three, one_pow, one_mul]

/-- The complex value of the auxiliary unit is a primitive third root of unity. -/
lemma auxiliaryComplexUnit_val_isPrimitiveRoot : IsPrimitiveRoot (auxiliaryComplexUnit : ℂ) 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  rw [show (auxiliaryComplexUnit : ℂ) = Complex.exp (2 * ↑Real.pi * Complex.I / 3) from rfl,
    show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num]
  exact h

/-- The auxiliary complex scalar is a primitive third root of unity. -/
lemma auxiliaryComplexScalar_isPrimitiveRoot : IsPrimitiveRoot auxiliaryComplexScalar 3 := auxiliaryComplexUnit_val_isPrimitiveRoot

/-- Powers of the auxiliary complex scalar with natural exponents below three are equal only when the exponents are equal. -/
lemma pow_auxiliaryComplexScalar_injective_below_three {i j : ℕ} (hi : i < 3) (hj : j < 3) (h : auxiliaryComplexScalar ^ i = auxiliaryComplexScalar ^ j) : i = j :=
  auxiliaryComplexUnit_val_isPrimitiveRoot.pow_inj hi hj h

/-- An auxiliary family of homomorphisms from the multiplicative form of integers modulo three to the complex units. -/
def auxiliaryCyclicMultiplicativeCharacter (k : ZMod 3) : Multiplicative (ZMod 3) →* ℂˣ where
  toFun x := auxiliaryComplexUnit ^ (k * Multiplicative.toAdd x).val
  map_one' := by
    change auxiliaryComplexUnit ^ (k * (0 : ZMod 3)).val = 1
    rw [mul_zero, ZMod.val_zero, pow_zero]
  map_mul' x y := by
    change auxiliaryComplexUnit ^ (k * (Multiplicative.toAdd x + Multiplicative.toAdd y)).val
      = auxiliaryComplexUnit ^ (k * Multiplicative.toAdd x).val * auxiliaryComplexUnit ^ (k * Multiplicative.toAdd y).val
    rw [mul_add, ZMod.val_add, ← pow_add, auxiliaryComplexUnit_pow_mod_three]

/-- An auxiliary family of complex-unit-valued homomorphisms on the specified subgroup, indexed modulo three. -/
def auxiliaryLinearCharacterHom (k : ZMod 3) : alternatingSubgroupFour →* ℂˣ := (auxiliaryCyclicMultiplicativeCharacter k).comp conjugacyQuotientHom

/-- The auxiliary character homomorphism evaluates as a power of the distinguished complex unit with exponent determined by the modular class index. -/
lemma auxiliaryLinearCharacterHom_apply (k : ZMod 3) (g : alternatingSubgroupFour) : auxiliaryLinearCharacterHom k g = auxiliaryComplexUnit ^ (k * additiveClassIndex g).val := rfl

/-- A family of finite-dimensional complex representations indexed by integers modulo three. -/
def oneDimensionalRepresentations (k : ZMod 3) : FDRep ℂ alternatingSubgroupFour := FDRep.of (RepresentationTheory.PermutationActionRepresentations.representationOfUnitsCharacter (auxiliaryLinearCharacterHom k))

/-- The character of an indexed representation is a power of the distinguished complex scalar determined by the index and additive class index. -/
lemma oneDimensionalRepresentations_character (k : ZMod 3) (g : alternatingSubgroupFour) :
    (oneDimensionalRepresentations k).character g = auxiliaryComplexScalar ^ (k * additiveClassIndex g).val := by
  rw [oneDimensionalRepresentations, RepresentationTheory.PermutationActionRepresentations.representationOfUnitsCharacter_character, auxiliaryLinearCharacterHom_apply, auxiliaryComplexScalar,
    Units.val_pow_eq_pow_val]

/-- A finite-dimensional complex representation of the specified subgroup. -/
def auxiliaryRepresentation : FDRep ℂ alternatingSubgroupFour := RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation (G := alternatingSubgroupFour) (α := Fin 4)

/-- The character of the specified representation at an element is the cast of the displayed auxiliary value minus one. -/
lemma auxiliaryRepresentation_character (g : alternatingSubgroupFour) :
    auxiliaryRepresentation.character g
      = ((RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := alternatingSubgroupFour) (α := Fin 4) g : ℤ) - 1 : ℂ) := by
  rw [auxiliaryRepresentation, RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation_character_general]; push_cast; ring

/-- A four-element family of selected elements in the specified subgroup. -/
def conjugacyClassRepresentative : Fin 4 → alternatingSubgroupFour :=
  ![1,
    ⟨Equiv.swap 0 2 * Equiv.swap 0 1, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩]

/-- An auxiliary index in a four-element type assigned to each element of the specified subgroup. -/
def conjugacyClassIndex (g : alternatingSubgroupFour) : Fin 4 :=
  if RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := alternatingSubgroupFour) (α := Fin 4) g = 4 then 0
  else if RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := alternatingSubgroupFour) (α := Fin 4) g = 0 then 3
  else if additiveClassIndex g = 1 then 1
  else 2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in

/-- Every subgroup element is conjugate to the selected representative indexed by that element. -/
lemma exists_conjugate_representative (g : alternatingSubgroupFour) : ∃ c : alternatingSubgroupFour, c * conjugacyClassRepresentative (conjugacyClassIndex g) * c⁻¹ = g := by
  revert g; decide

set_option maxRecDepth 10000 in

/-- The four fibers of the class-index map have cardinalities one, four, four, and three. -/
lemma card_fiber_conjugacyClassIndex (j : Fin 4) :
    (Finset.univ.filter fun g => conjugacyClassIndex g = j).card = ![1, 4, 4, 3] j := by
  revert j; decide

set_option maxRecDepth 10000 in

/-- Each selected representative is sent to its own class index. -/
lemma conjugacyClassIndex_representative (j : Fin 4) : conjugacyClassIndex (conjugacyClassRepresentative j) = j := by
  revert j; decide

set_option maxRecDepth 10000 in

/-- The representatives indexed by one and two are not conjugate. -/
lemma representative_one_not_conjugate_representative_two : ¬ ∃ c : alternatingSubgroupFour, c * conjugacyClassRepresentative 1 * c⁻¹ = conjugacyClassRepresentative 2 := by
  decide

/-- An auxiliary four-by-four table of complex values. -/
def auxiliaryCharacterTable : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1],
    ![1, auxiliaryComplexScalar, auxiliaryComplexScalar ^ 2, 1],
    ![1, auxiliaryComplexScalar ^ 2, auxiliaryComplexScalar, 1],
    ![3, 0, 0, -1]]

/-- A four-element family of finite-dimensional complex representations of the specified subgroup. -/
def indexedIrreducibleRepresentations : Fin 4 → FDRep ℂ alternatingSubgroupFour := ![oneDimensionalRepresentations 0, oneDimensionalRepresentations 1, oneDimensionalRepresentations 2, auxiliaryRepresentation]

set_option maxRecDepth 10000 in
/-- The additive class indices of the four selected representatives are zero, one, two, and zero. -/
lemma additiveClassIndex_representative : ∀ j : Fin 4, additiveClassIndex (conjugacyClassRepresentative j) = ![0, 1, 2, 0] j := by decide

set_option maxRecDepth 10000 in
/-- The auxiliary values at the selected representatives are four, one, one, and zero in the displayed order. -/
lemma auxiliaryValue_conjugacyClassRepresentative : ∀ j : Fin 4,
    RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := alternatingSubgroupFour) (α := Fin 4) (conjugacyClassRepresentative j) = ![4, 1, 1, 0] j := by
  decide

/-- The character of the representation indexed by zero on each selected representative is the corresponding entry of row zero of the auxiliary table. -/
lemma oneDimensionalRepresentation_zero_character_representative (j : Fin 4) : (oneDimensionalRepresentations 0).character (conjugacyClassRepresentative j) = auxiliaryCharacterTable 0 j := by
  have hexp : ∀ j : Fin 4, ((0 : ZMod 3) * additiveClassIndex (conjugacyClassRepresentative j)).val = 0 := by
    intro j; rw [zero_mul, ZMod.val_zero]
  rw [oneDimensionalRepresentations_character, hexp j, pow_zero]
  fin_cases j <;>
    norm_num [auxiliaryCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

set_option maxRecDepth 10000 in
/-- The character of the representation indexed by one on each selected representative is the corresponding entry of row one of the auxiliary table. -/
lemma oneDimensionalRepresentation_one_character_representative (j : Fin 4) : (oneDimensionalRepresentations 1).character (conjugacyClassRepresentative j) = auxiliaryCharacterTable 1 j := by
  have hexp : ∀ j : Fin 4, ((1 : ZMod 3) * additiveClassIndex (conjugacyClassRepresentative j)).val = ![0, 1, 2, 0] j := by decide
  rw [oneDimensionalRepresentations_character, hexp j]
  fin_cases j <;>
    norm_num [auxiliaryCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

set_option maxRecDepth 10000 in
/-- The character of the representation indexed by two on each selected representative is the corresponding entry of row two of the auxiliary table. -/
lemma oneDimensionalRepresentation_two_character_representative (j : Fin 4) : (oneDimensionalRepresentations 2).character (conjugacyClassRepresentative j) = auxiliaryCharacterTable 2 j := by
  have hexp : ∀ j : Fin 4, ((2 : ZMod 3) * additiveClassIndex (conjugacyClassRepresentative j)).val = ![0, 2, 1, 0] j := by decide
  rw [oneDimensionalRepresentations_character, hexp j]
  fin_cases j <;>
    norm_num [auxiliaryCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- The character of the specified representation on each selected representative is the corresponding entry of row three of the auxiliary table. -/
lemma auxiliaryRepresentation_character_representative (j : Fin 4) : auxiliaryRepresentation.character (conjugacyClassRepresentative j) = auxiliaryCharacterTable 3 j := by
  rw [auxiliaryRepresentation_character, auxiliaryValue_conjugacyClassRepresentative j]
  fin_cases j <;>
    norm_num [auxiliaryCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- The character values of the indexed representations on the selected representatives agree with the corresponding entries of the auxiliary table. -/
theorem indexedIrreducibleRepresentations_character (i j : Fin 4) :
    (indexedIrreducibleRepresentations i).character (conjugacyClassRepresentative j) = auxiliaryCharacterTable i j := by
  fin_cases i
  · exact oneDimensionalRepresentation_zero_character_representative j
  · exact oneDimensionalRepresentation_one_character_representative j
  · exact oneDimensionalRepresentation_two_character_representative j
  · exact auxiliaryRepresentation_character_representative j

/-- Every representation in the family indexed modulo three is simple. -/
lemma oneDimensionalRepresentations_simple (k : ZMod 3) : Simple (oneDimensionalRepresentations k) :=
  RepresentationTheory.PermutationActionRepresentations.representationOfUnitsCharacter_simple _

set_option maxRecDepth 10000 in
/-- The specified finite-dimensional complex representation is simple. -/
lemma auxiliaryRepresentation_simple : Simple auxiliaryRepresentation := by
  rw [auxiliaryRepresentation, FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : alternatingSubgroupFour,
      (RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation (G := alternatingSubgroupFour) (α := Fin 4)).character g
        * (RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation (G := alternatingSubgroupFour) (α := Fin 4)).character g⁻¹
      = ((((RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := alternatingSubgroupFour) (α := Fin 4) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation_character_general, RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation_character_general,
      RepresentationTheory.PermutationActionRepresentations.fixedPointCount_inv]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : alternatingSubgroupFour,
      (((RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := alternatingSubgroupFour) (α := Fin 4) g : ℤ) - 1) ^ 2) = 12 := by
    decide
  rw [hsum, Nat.card_eq_fintype_card, card_alternatingSubgroupFour]; norm_num

/-- Every representation in the four-element family is simple. -/
theorem indexedIrreducibleRepresentations_simple (i : Fin 4) : Simple (indexedIrreducibleRepresentations i) := by
  fin_cases i
  · exact oneDimensionalRepresentations_simple 0
  · exact oneDimensionalRepresentations_simple 1
  · exact oneDimensionalRepresentations_simple 2
  · exact auxiliaryRepresentation_simple

/-- The entry in column zero is three in row three and one in every other row. -/
lemma auxiliaryCharacterTable_column_zero (i : Fin 4) : auxiliaryCharacterTable i 0 = if i = 3 then 3 else 1 := by
  fin_cases i <;>
    norm_num [auxiliaryCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> decide

/-- Away from row three, the entry in column one is the corresponding power of the auxiliary complex scalar. -/
lemma auxiliaryCharacterTable_column_one (i : Fin 4) (hi : i ≠ 3) : auxiliaryCharacterTable i 1 = auxiliaryComplexScalar ^ (i : ℕ) := by
  fin_cases i
  · norm_num [auxiliaryCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
  · norm_num [auxiliaryCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
  · norm_num [auxiliaryCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  · exact absurd rfl hi

/-- Distinct row indices determine distinct rows of the auxiliary character table. -/
lemma auxiliaryCharacterTable_injective : Function.Injective auxiliaryCharacterTable := by
  intro i j hij
  have h1 : auxiliaryCharacterTable i 1 = auxiliaryCharacterTable j 1 := congrFun hij 1
  have h0 : auxiliaryCharacterTable i 0 = auxiliaryCharacterTable j 0 := congrFun hij 0
  have hpow := auxiliaryCharacterTable_column_one
  have hzero := auxiliaryCharacterTable_column_zero
  by_cases hi3 : i = 3
  · by_cases hj3 : j = 3
    · rw [hi3, hj3]
    · rw [hzero i, hzero j, if_pos hi3, if_neg hj3] at h0
      exact absurd h0 (by norm_num)
  · by_cases hj3 : j = 3
    · rw [hzero i, hzero j, if_neg hi3, if_pos hj3] at h0
      exact absurd h0 (by norm_num)
    · rw [hpow i hi3, hpow j hj3] at h1
      exact Fin.ext (pow_auxiliaryComplexScalar_injective_below_three (by omega) (by omega) h1)

/-- Representations at distinct indices in the four-element family are not isomorphic. -/
theorem indexedIrreducibleRepresentations_pairwise_nonisomorphic (i j : Fin 4) (hij : i ≠ j) :
    ¬ Nonempty (indexedIrreducibleRepresentations i ≅ indexedIrreducibleRepresentations j) := by
  rintro ⟨e⟩
  apply hij
  have hchar : (indexedIrreducibleRepresentations i).character = (indexedIrreducibleRepresentations j).character := FDRep.char_iso e
  refine auxiliaryCharacterTable_injective (funext fun c => ?_)
  rw [← indexedIrreducibleRepresentations_character, ← indexedIrreducibleRepresentations_character, hchar]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in

/-- The specified subgroup has four conjugacy classes. -/
theorem card_conjClasses_alternatingSubgroupFour : Fintype.card (ConjClasses alternatingSubgroupFour) = 4 := by decide

private instance : Invertible (Fintype.card alternatingSubgroupFour : ℂ) :=
  invertibleOfNonzero (by rw [card_alternatingSubgroupFour]; norm_num)

/-- Every simple finite-dimensional complex representation of the specified subgroup is isomorphic to one member of the indexed four-element family. -/
theorem simpleRepresentation_iso_indexedIrreducibleRepresentation (V : FDRep ℂ alternatingSubgroupFour) [Simple V] :
    ∃ i : Fin 4, Nonempty (V ≅ indexedIrreducibleRepresentations i) := by
  obtain ⟨n, W, _hWsimp, _hWinj, hWsurj, hn⟩ := RepresentationTheory.Group.SimpleRepresentations.exists_simpleReps_card_eq_conjClasses (k := ℂ) (G := alternatingSubgroupFour)
  rw [card_conjClasses_alternatingSubgroupFour] at hn
  subst hn
  choose c hc using fun i => hWsurj (indexedIrreducibleRepresentations i) (indexedIrreducibleRepresentations_simple i)
  have hcinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    refine indexedIrreducibleRepresentations_pairwise_nonisomorphic i j hne ?_
    obtain ⟨αi⟩ := hc i
    obtain ⟨αj⟩ := hc j
    exact ⟨αi ≪≫ eqToIso (congrArg W hij) ≪≫ αj.symm⟩
  have hcsurj : Function.Surjective c := Finite.surjective_of_injective hcinj
  obtain ⟨k, hk⟩ := hWsurj V ‹Simple V›
  obtain ⟨i, hi⟩ := hcsurj k
  refine ⟨i, ?_⟩
  obtain ⟨αV⟩ := hk
  obtain ⟨αi⟩ := hc i
  exact ⟨αV ≪≫ eqToIso (congrArg W hi.symm) ≪≫ αi.symm⟩

/-- The sum of the squares of the degree entries in the auxiliary character table equals the cardinality of the specified subgroup. -/
theorem sum_sq_characterTable_degree_eq_card : ∑ i : Fin 4, (auxiliaryCharacterTable i 0) ^ 2 = (Fintype.card alternatingSubgroupFour : ℂ) := by
  rw [card_alternatingSubgroupFour]
  simp only [Fin.sum_univ_four]
  norm_num [auxiliaryCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

end

/-- The alternating group on four points has twelve elements. -/
theorem card_alternatingGroup_four :
    Fintype.card (alternatingGroup (Fin 4)) = 12 := card_alternatingSubgroupFour

/-- The alternating group on four points has four conjugacy classes. -/
theorem card_conjClasses_alternatingGroup_four :
    Fintype.card (ConjClasses (alternatingGroup (Fin 4))) = 4 := card_conjClasses_alternatingSubgroupFour

/-- The fibers of the class-index map have cardinalities one, four, four, and three. -/
@[source_ref "Chapter4/Introduction_4.8" (role := supporting)]
theorem card_conjugacyClassIndex_fiber (j : Fin 4) :
    (Finset.univ.filter fun g => conjugacyClassIndex g = j).card = ![1, 4, 4, 3] j :=
  card_fiber_conjugacyClassIndex j

/-- The quotient homomorphism is surjective and has the Klein four subgroup as its kernel. -/
@[source_ref "Chapter4/Introduction_4.8" (role := supporting)]
theorem conjugacyQuotientHom_surjective_and_ker :
    Function.Surjective conjugacyQuotientHom ∧
      conjugacyQuotientHom.ker = alternatingGroup.kleinFour (Fin 4) :=
  ⟨conjugacyQuotientHom_surjective, ker_conjugacyQuotientHom⟩

/-- Every element of the alternating group on four points is conjugate to its indexed representative, each representative has its stated index, and the representatives at indices one and two are not conjugate. -/
theorem conjugacyClassRepresentatives_spec :
    (∀ g : alternatingGroup (Fin 4),
        ∃ c : alternatingGroup (Fin 4),
          c * conjugacyClassRepresentative (conjugacyClassIndex g) * c⁻¹ = g) ∧
      (∀ j, conjugacyClassIndex (conjugacyClassRepresentative j) = j) ∧
      ¬ ∃ c : alternatingGroup (Fin 4), c * conjugacyClassRepresentative 1 * c⁻¹ = conjugacyClassRepresentative 2 :=
  ⟨exists_conjugate_representative, conjugacyClassIndex_representative, representative_one_not_conjugate_representative_two⟩

/-- The auxiliary scalar equals the exponential of two pi times the imaginary unit divided by three and is a primitive third root of unity. -/
theorem auxiliaryComplexScalar_spec :
    auxiliaryComplexScalar = Complex.exp (2 * Real.pi * Complex.I / 3) ∧ IsPrimitiveRoot auxiliaryComplexScalar 3 :=
  ⟨auxiliaryComplexScalar_eq_exp, auxiliaryComplexScalar_isPrimitiveRoot⟩

/-- The sum of squared degree entries in the auxiliary table equals the cardinality of the alternating group on four points. -/
theorem sum_sq_alternatingGroupFour_characterDegrees_eq_card :
    ∑ i : Fin 4, (auxiliaryCharacterTable i 0) ^ 2 = (Fintype.card (alternatingGroup (Fin 4)) : ℂ) :=
  sum_sq_characterTable_degree_eq_card

/-- A four-element family of finite-dimensional complex representations of the alternating group on four points. -/
noncomputable def alternatingGroupFourRepresentations :
    Fin 4 → FDRep ℂ (alternatingGroup (Fin 4)) := indexedIrreducibleRepresentations

/-- Every representation in the specified four-element family for the alternating group on four points is simple. -/
@[source_ref "Chapter4/Introduction_4.8" (role := supporting)]
theorem alternatingGroupFourRepresentations_simple (i : Fin 4) :
    CategoryTheory.Simple (alternatingGroupFourRepresentations i) := indexedIrreducibleRepresentations_simple i

/-- The indexed representations of the alternating group on four points have character values given by the auxiliary table on the selected representatives. -/
@[source_ref "Chapter4/Introduction_4.8" (role := supporting)]
theorem alternatingGroupFourRepresentations_character (i j : Fin 4) :
    (alternatingGroupFourRepresentations i).character (conjugacyClassRepresentative j) = auxiliaryCharacterTable i j :=
  indexedIrreducibleRepresentations_character i j

/-- Distinct indices give nonisomorphic representations in the specified family for the alternating group on four points. -/
@[source_ref "Chapter4/Introduction_4.8" (role := supporting)]
theorem alternatingGroupFourRepresentations_pairwise_nonisomorphic (i j : Fin 4) (hij : i ≠ j) :
    ¬ Nonempty (alternatingGroupFourRepresentations i ≅ alternatingGroupFourRepresentations j) :=
  indexedIrreducibleRepresentations_pairwise_nonisomorphic i j hij

/-- Every simple finite-dimensional complex representation of the alternating group on four points is isomorphic to an indexed member of the specified family. -/
@[source_ref "Chapter4/Introduction_4.8" (role := supporting)]
theorem simpleRepresentation_iso_alternatingGroupFourRepresentation (V : FDRep ℂ (alternatingGroup (Fin 4)))
    [CategoryTheory.Simple V] :
    ∃ i : Fin 4, Nonempty (V ≅ alternatingGroupFourRepresentations i) :=
  simpleRepresentation_iso_indexedIrreducibleRepresentation V

end RepresentationTheory.AlternatingGroupFourRepresentations
