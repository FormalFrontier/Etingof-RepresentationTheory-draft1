/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.QuaternionGroupTwo



namespace RepresentationTheory.PermutationActionRepresentations

open RepresentationTheory.QuaternionGroupTwo.AuxiliaryType



/-- A five-entry vector of rational values. -/
def auxiliaryRatVector : Fin 5 → ℚ := ![1, 6, 3, 8, 6]


/-- A five-by-five character table valued in the auxiliary coordinate type. -/
def auxiliaryCharacterTable : Fin 5 → Fin 5 → RepresentationTheory.QuaternionGroupTwo.AuxiliaryType :=
  ![![1,  1,  1,  1,  1],
    ![1, -1,  1,  1, -1],
    ![2,  0,  2, -1,  0],
    ![3, -1, -1,  0,  1],
    ![3,  1, -1,  0, -1]]




open CategoryTheory MonoidalCategory Module

noncomputable section

-- The generic deleted-permutation-rep helpers carry `[Fintype α] [DecidableEq α]` instances
-- that several specialised lemmas do not mention in their statement; silence the style linters.
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.dupNamespace false


section Carrier
variable {α : Type} [Fintype α] [DecidableEq α]


/-- The complex-linear map that sums a finite family of coordinates. -/
def sumLinearMap : (α → ℂ) →ₗ[ℂ] ℂ := ∑ a, LinearMap.proj a

/-- The summation linear map evaluates as the sum over all indices. -/
@[simp] lemma sumLinearMap_apply (f : α → ℂ) : sumLinearMap f = ∑ a, f a := by
  simp [sumLinearMap, Finset.sum_apply]


/-- A distinguished complex-valued function on an arbitrary type. -/
def distinguishedFunction : α → ℂ := fun _ => 1

/-- The distinguished function on a nonempty finite type is nonzero. -/
lemma distinguishedFunction_ne_zero [Nonempty α] : (distinguishedFunction : α → ℂ) ≠ 0 := by
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  intro h; have := congrFun h a; simp [distinguishedFunction] at this


/-- A complex submodule of functions associated with a distinguished function. -/
def distinguishedFunctionSubmodule : Submodule ℂ (α → ℂ) := Submodule.span ℂ {(distinguishedFunction : α → ℂ)}

/-- A function lies in the selected submodule exactly when it is a scalar multiple of the distinguished function. -/
lemma mem_distinguishedFunctionSubmodule_iff {x : α → ℂ} : x ∈ (distinguishedFunctionSubmodule : Submodule ℂ (α → ℂ)) ↔
    ∃ c : ℂ, c • (distinguishedFunction : α → ℂ) = x := Submodule.mem_span_singleton

/-- Applying the summation linear map to the distinguished function gives the index-type cardinality. -/
lemma sumLinearMap_distinguishedFunction : sumLinearMap (distinguishedFunction : α → ℂ) = (Fintype.card α : ℂ) := by
  rw [sumLinearMap_apply]
  simp only [distinguishedFunction, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end Carrier


section Generic
variable {G : Type} [Group G] {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] [MulAction G α]


/-- The complex representation on functions induced by a group action. -/
def permutationRepresentation : Representation ℂ G (α → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (fun a => g⁻¹ • a)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext a; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, mul_smul]

/-- The induced action evaluates a function at the inverse translate of the point. -/
@[simp] lemma permutationRepresentation_apply (g : G) (f : α → ℂ) (a : α) :
    permutationRepresentation g f a = f (g⁻¹ • a) := rfl


/-- An auxiliary subrepresentation of the permutation representation. -/
def auxiliarySubrepresentation : Subrepresentation (permutationRepresentation : Representation ℂ G (α → ℂ)) where
  toSubmodule := LinearMap.ker sumLinearMap
  apply_mem_toSubmodule g f hf := by
    simp only [LinearMap.mem_ker, sumLinearMap_apply] at hf ⊢
    calc ∑ a, permutationRepresentation g f a = ∑ a, f (g⁻¹ • a) := by
            refine Finset.sum_congr rfl fun a _ => ?_; rw [permutationRepresentation_apply]
      _ = ∑ a, f ((MulAction.toPerm (g⁻¹ : G)) a) := rfl
      _ = ∑ a, f a := Equiv.sum_comp (MulAction.toPerm (g⁻¹ : G)) f
      _ = 0 := hf


/-- The finite-dimensional representation obtained from a finite permutation action after removing the constant part. -/
def reducedPermutationRepresentation : FDRep ℂ G := FDRep.of (auxiliarySubrepresentation (G := G) (α := α)).toRepresentation


/-- Counts fixed points of an element acting on a finite set. -/
def fixedPointCount (g : G) : ℕ := (Finset.univ.filter (fun a : α => g • a = a)).card

/-- Every group element fixes the distinguished function. -/
@[simp] lemma permutationRepresentation_distinguishedFunction (g : G) :
    permutationRepresentation (α := α) g (distinguishedFunction : α → ℂ) = distinguishedFunction := by
  funext a; simp [distinguishedFunction]

/-- The induced linear action is the permutation matrix of the inverse permutation. -/
lemma permutationRepresentation_eq_permMatrix (g : G) :
    (permutationRepresentation (G := G) (α := α) g) = ((MulAction.toPerm (g⁻¹ : G)).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext a
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, permutationRepresentation_apply]; rfl

/-- The trace of the induced permutation action is the number of fixed points of the inverse permutation. -/
lemma trace_permutationRepresentation (g : G) :
    LinearMap.trace ℂ (α → ℂ) (permutationRepresentation (G := G) (α := α) g)
      = (Function.fixedPoints ⇑(MulAction.toPerm (g⁻¹ : G) : Equiv.Perm α)).ncard := by
  rw [permutationRepresentation_eq_permMatrix, Matrix.trace_toLin'_eq, Matrix.trace_permutation]

/-- The cardinality of the inverse action's fixed-point set equals the fixed-point count. -/
lemma ncard_fixedPoints_inv (g : G) :
    (Function.fixedPoints ⇑(MulAction.toPerm (g⁻¹ : G) : Equiv.Perm α)).ncard
      = fixedPointCount (α := α) g := by
  rw [fixedPointCount, ← Set.ncard_coe_finset]
  congr 1; ext a
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and, MulAction.toPerm_apply]
  constructor
  · intro h; rw [inv_smul_eq_iff] at h; exact h.symm
  · intro h; rw [inv_smul_eq_iff, h]

/-- An element and its inverse have the same number of fixed points. -/
@[simp] lemma fixedPointCount_inv (g : G) : fixedPointCount (α := α) g⁻¹ = fixedPointCount (α := α) g := by
  rw [fixedPointCount, fixedPointCount]; congr 1; ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; rw [inv_smul_eq_iff] at h; exact h.symm
  · intro h; rw [inv_smul_eq_iff, h]


/-- The reduced permutation character equals the number of fixed points minus one. -/
lemma reducedPermutationRepresentation_character_general (g : G) :
    (reducedPermutationRepresentation (G := G) (α := α)).character g = (fixedPointCount (α := α) g : ℂ) - 1 := by
  classical
  set N : Fin 2 → Submodule ℂ (α → ℂ) :=
    ![(auxiliarySubrepresentation (G := G) (α := α)).toSubmodule, distinguishedFunctionSubmodule] with hN
  have hsurj : Function.Surjective (sumLinearMap (α := α)) := by
    obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
    intro c; refine ⟨Pi.single a₀ c, ?_⟩
    rw [sumLinearMap_apply, Finset.sum_pi_single']; simp
  have hcardpos : 1 ≤ Fintype.card α := Fintype.card_pos
  have hkerdim : Module.finrank ℂ (LinearMap.ker (sumLinearMap (α := α))) = Fintype.card α - 1 := by
    have h := (sumLinearMap (α := α)).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, Module.finrank_pi] at h
    omega
  have hcompl : IsCompl (auxiliarySubrepresentation (G := G) (α := α)).toSubmodule distinguishedFunctionSubmodule := by
    have hone : Module.finrank ℂ (distinguishedFunctionSubmodule : Submodule ℂ (α → ℂ)) = 1 :=
      finrank_span_singleton distinguishedFunction_ne_zero
    have hdim : Module.finrank ℂ (α → ℂ) ≤
        Module.finrank ℂ (auxiliarySubrepresentation (G := G) (α := α)).toSubmodule
          + Module.finrank ℂ (distinguishedFunctionSubmodule : Submodule ℂ (α → ℂ)) := by
      have hk : Module.finrank ℂ (auxiliarySubrepresentation (G := G) (α := α)).toSubmodule
          = Fintype.card α - 1 := hkerdim
      rw [hk, hone, Module.finrank_pi]; omega
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxk hxc
    rw [mem_distinguishedFunctionSubmodule_iff] at hxc
    obtain ⟨c, rfl⟩ := hxc
    have h0 : sumLinearMap (c • (distinguishedFunction : α → ℂ)) = 0 := hxk
    rw [map_smul, sumLinearMap_distinguishedFunction, smul_eq_mul] at h0
    have hc : c = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (Nat.cast_ne_zero.mpr (by omega))
    simp [hc]
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i; simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]; omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (zero_ne_one) huniv).mpr hcompl
  have hf0 : Set.MapsTo (permutationRepresentation (α := α) g) (N 0) (N 0) := fun x hx =>
    (auxiliarySubrepresentation (G := G) (α := α)).apply_mem_toSubmodule g hx
  have hf1 : Set.MapsTo (permutationRepresentation (α := α) g) (N 1) (N 1) := by
    intro x hx
    change x ∈ (distinguishedFunctionSubmodule : Submodule ℂ (α → ℂ)) at hx
    change permutationRepresentation g x ∈ (distinguishedFunctionSubmodule : Submodule ℂ (α → ℂ))
    rw [mem_distinguishedFunctionSubmodule_iff] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, permutationRepresentation_distinguishedFunction]⟩
  have hf : ∀ i, Set.MapsTo (permutationRepresentation (α := α) g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_permutationRepresentation, ncard_fixedPoints_inv, Fin.sum_univ_two] at htr
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((permutationRepresentation g).restrict (hf 0))
      = (reducedPermutationRepresentation (G := G) (α := α)).character g := by
    change LinearMap.trace ℂ ↥((auxiliarySubrepresentation (G := G) (α := α)).toSubmodule)
        ((auxiliarySubrepresentation (G := G) (α := α)).toRepresentation g)
      = LinearMap.trace ℂ ↥((auxiliarySubrepresentation (G := G) (α := α)).toSubmodule)
        ((FDRep.of (auxiliarySubrepresentation (G := G) (α := α)).toRepresentation).ρ g)
    rw [FDRep.of_ρ']
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((permutationRepresentation g).restrict (hf 1)) = 1 := by
    have hid : (permutationRepresentation g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext; intro x; apply Subtype.ext
      have hx : (x : α → ℂ) ∈ (distinguishedFunctionSubmodule : Submodule ℂ (α → ℂ)) := x.2
      rw [mem_distinguishedFunctionSubmodule_iff] at hx
      obtain ⟨c, hc⟩ := hx
      change permutationRepresentation g (x : α → ℂ) = (x : α → ℂ)
      rw [← hc, map_smul, permutationRepresentation_distinguishedFunction]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton distinguishedFunction_ne_zero
    rw [hid, LinearMap.trace_id, hfin]; norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]; exact htr.symm


/-- The number of fixed points is invariant under conjugation. -/
lemma fixedPointCount_conj (c g : G) :
    fixedPointCount (α := α) (c * g * c⁻¹) = fixedPointCount (α := α) g := by
  rw [fixedPointCount, fixedPointCount,
    show (Finset.univ.filter fun a : α => (c * g * c⁻¹) • a = a)
        = (Finset.univ.filter fun a : α => g • a = a).image (c • ·) by
      ext b
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hb
        refine ⟨c⁻¹ • b, ?_, smul_inv_smul c b⟩
        rw [mul_smul, mul_smul] at hb
        refine MulAction.injective c ?_
        change c • (g • (c⁻¹ • b)) = c • (c⁻¹ • b)
        rw [smul_inv_smul]
        exact hb
      · rintro ⟨a, ha, rfl⟩
        rw [mul_smul, mul_smul, inv_smul_smul, ha],
    Finset.card_image_of_injective _ (MulAction.injective c)]

end Generic



open Equiv

/-- An auxiliary type. -/
abbrev AuxiliaryType := Equiv.Perm (Fin 4)


/-- Builds a one-dimensional complex representation from a character valued in complex units. -/
def representationOfUnitsCharacter {G : Type} [Group G] (χ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The character of the constructed representation is the underlying complex value of the units character. -/
@[simp] lemma representationOfUnitsCharacter_character {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    (FDRep.of (representationOfUnitsCharacter χ)).character g = (χ g : ℂ) := by
  change LinearMap.trace ℂ ℂ ((FDRep.of (representationOfUnitsCharacter χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', show representationOfUnitsCharacter χ g = ((χ g : ℂˣ) : ℂ) • LinearMap.id from rfl,
    map_smul, LinearMap.trace_id]; simp

/-- A one-dimensional representation arising from a units character is simple for a finite group. -/
lemma representationOfUnitsCharacter_simple {G : Type} [Group G] [Finite G] (χ : G →* ℂˣ) :
    Simple (FDRep.of (representationOfUnitsCharacter χ)) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [FDRep.simple_iff_char_is_norm_one]
  have : ∀ g : G, (FDRep.of (representationOfUnitsCharacter χ)).character g
      * (FDRep.of (representationOfUnitsCharacter χ)).character g⁻¹ = 1 := by
    intro g
    rw [representationOfUnitsCharacter_character, representationOfUnitsCharacter_character, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Nat.card_eq_fintype_card]


/-- A selected finite-dimensional complex representation corresponding to row zero. -/
def selectedRepresentationZero : FDRep ℂ AuxiliaryType := FDRep.of (representationOfUnitsCharacter (1 : AuxiliaryType →* ℂˣ))

/-- A complex-units-valued character of the auxiliary type. -/
def selectedUnitsCharacter : AuxiliaryType →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign

/-- The one-dimensional representation attached to the selected units character. -/
def selectedRepresentationOne : FDRep ℂ AuxiliaryType := FDRep.of (representationOfUnitsCharacter selectedUnitsCharacter)




/-- Embeds the three point indices into the auxiliary type. -/
def pointEmbedding : Fin 3 → AuxiliaryType :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

/-- The embedding of the three point indices is injective. -/
lemma pointEmbedding_injective : Function.Injective pointEmbedding := by decide


/-- Applies an auxiliary element to one of three points. -/
def actOnFinThree (g : AuxiliaryType) (a : Fin 3) : Fin 3 :=
  if g * pointEmbedding a * g⁻¹ = pointEmbedding 0 then 0
  else if g * pointEmbedding a * g⁻¹ = pointEmbedding 1 then 1 else 2

set_option maxHeartbeats 4000000 in
-- honest `decide` over the 24×3 conjugation table (no `native_decide`); the raised limit
-- covers kernel reduction of the permutation multiplications.
/-- The embedded action point is obtained by conjugating its embedded representative. -/
lemma pointEmbedding_actOnFinThree (g : AuxiliaryType) (a : Fin 3) : pointEmbedding (actOnFinThree g a) = g * pointEmbedding a * g⁻¹ := by
  revert g a; decide


/-- An action of the auxiliary type on three points. -/
instance finThreeAction : MulAction AuxiliaryType (Fin 3) where
  smul := actOnFinThree
  one_smul a := pointEmbedding_injective (by
    change pointEmbedding (actOnFinThree 1 a) = pointEmbedding a
    rw [pointEmbedding_actOnFinThree]; simp)
  mul_smul g h a := pointEmbedding_injective (by
    change pointEmbedding (actOnFinThree (g * h) a) = pointEmbedding (actOnFinThree g (actOnFinThree h a))
    rw [pointEmbedding_actOnFinThree, pointEmbedding_actOnFinThree, pointEmbedding_actOnFinThree]; group)




/-- A selected finite-dimensional complex representation corresponding to row four. -/
def selectedRepresentationFour : FDRep ℂ AuxiliaryType := reducedPermutationRepresentation (G := AuxiliaryType) (α := Fin 4)

/-- A selected finite-dimensional complex representation of the auxiliary type. -/
def selectedRepresentationTwo : FDRep ℂ AuxiliaryType := reducedPermutationRepresentation (G := AuxiliaryType) (α := Fin 3)

/-- A selected finite-dimensional complex representation corresponding to row three. -/
def selectedRepresentationThree : FDRep ℂ AuxiliaryType := selectedRepresentationFour ⊗ selectedRepresentationOne


/-- A five-entry family of finite-dimensional complex representations of the auxiliary type. -/
def irreducibleRepresentations : Fin 5 → FDRep ℂ AuxiliaryType := ![selectedRepresentationZero, selectedRepresentationOne, selectedRepresentationTwo, selectedRepresentationThree, selectedRepresentationFour]


/-- A five-entry family of elements of the auxiliary type. -/
def auxiliaryElementFamily : Fin 5 → AuxiliaryType :=
  ![1, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 2, finRotate 4]


/-- A five-by-five table of integer character values. -/
def integerCharacterTable : Fin 5 → Fin 5 → ℤ :=
  ![![1,  1,  1,  1,  1],
    ![1, -1,  1,  1, -1],
    ![2,  0,  2, -1,  0],
    ![3, -1, -1,  0,  1],
    ![3,  1, -1,  0, -1]]



/-- Its character on each selected element is row zero of the integer table. -/
lemma selectedRepresentationZero_character (j : Fin 5) : selectedRepresentationZero.character (auxiliaryElementFamily j) = (integerCharacterTable 0 j : ℂ) := by
  rw [selectedRepresentationZero, representationOfUnitsCharacter_character]
  fin_cases j <;>
    norm_num [integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-- Its character on each selected element is row one of the integer table. -/
lemma selectedRepresentationOne_character (j : Fin 5) : selectedRepresentationOne.character (auxiliaryElementFamily j) = (integerCharacterTable 1 j : ℂ) := by
  have hs : ∀ k, (Equiv.Perm.sign (auxiliaryElementFamily k) : ℤ) = ![1, -1, 1, 1, -1] k := by decide
  rw [selectedRepresentationOne, representationOfUnitsCharacter_character]
  have hbridge : ((selectedUnitsCharacter (auxiliaryElementFamily j) : ℂˣ) : ℂ)
      = ((Equiv.Perm.sign (auxiliaryElementFamily j) : ℤ) : ℂ) := by
    simp [selectedUnitsCharacter]
  rw [hbridge, hs j]
  fin_cases j <;>
    norm_num [integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-- Its character on each selected element is row four of the integer table. -/
lemma selectedRepresentationFour_character (j : Fin 5) : selectedRepresentationFour.character (auxiliaryElementFamily j) = (integerCharacterTable 4 j : ℂ) := by
  have hf : ∀ k, fixedPointCount (G := AuxiliaryType) (α := Fin 4) (auxiliaryElementFamily k) = ![4, 2, 0, 1, 0] k := by decide
  rw [selectedRepresentationFour, reducedPermutationRepresentation_character_general, hf j]
  fin_cases j <;>
    norm_num [integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-- Its character on each selected element is row two of the integer table. -/
lemma selectedRepresentationTwo_character (j : Fin 5) : selectedRepresentationTwo.character (auxiliaryElementFamily j) = (integerCharacterTable 2 j : ℂ) := by
  have hf : ∀ k, fixedPointCount (G := AuxiliaryType) (α := Fin 3) (auxiliaryElementFamily k) = ![3, 1, 3, 0, 1] k := by decide
  rw [selectedRepresentationTwo, reducedPermutationRepresentation_character_general, hf j]
  fin_cases j <;>
    norm_num [integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-- The selected character equals the fixed-point count minus one. -/
lemma reducedPermutationRepresentation_character (g : AuxiliaryType) :
    selectedRepresentationFour.character g = (((fixedPointCount (G := AuxiliaryType) (α := Fin 4) g : ℤ) - 1 : ℂ)) := by
  rw [selectedRepresentationFour, reducedPermutationRepresentation_character_general]; push_cast; ring

/-- The character of the selected representation is the complex value of its units character. -/
lemma unitsCharacterRepresentation_character (g : AuxiliaryType) : selectedRepresentationOne.character g = (selectedUnitsCharacter g : ℂ) := by
  rw [selectedRepresentationOne, representationOfUnitsCharacter_character]

/-- Its character is the product of the reduced fixed-point character and the units character. -/
lemma selectedRepresentationThree_character_formula (g : AuxiliaryType) :
    selectedRepresentationThree.character g
      = (((fixedPointCount (G := AuxiliaryType) (α := Fin 4) g : ℤ) - 1 : ℂ)) * (selectedUnitsCharacter g : ℂ) := by
  have hchar : selectedRepresentationThree.character = selectedRepresentationFour.character * selectedRepresentationOne.character := by
    rw [selectedRepresentationThree]; exact FDRep.char_tensor selectedRepresentationFour selectedRepresentationOne
  have h := congrFun hchar g
  rw [Pi.mul_apply, reducedPermutationRepresentation_character, unitsCharacterRepresentation_character] at h
  exact h

/-- Its character on each selected element is row three of the integer table. -/
lemma selectedRepresentationThree_character (j : Fin 5) : selectedRepresentationThree.character (auxiliaryElementFamily j) = (integerCharacterTable 3 j : ℂ) := by
  rw [selectedRepresentationThree_character_formula]
  have hf : ∀ k, fixedPointCount (G := AuxiliaryType) (α := Fin 4) (auxiliaryElementFamily k) = ![4, 2, 0, 1, 0] k := by decide
  have hs : ∀ k, (Equiv.Perm.sign (auxiliaryElementFamily k) : ℤ) = ![1, -1, 1, 1, -1] k := by decide
  rw [hf j]
  have hbridge : ((selectedUnitsCharacter (auxiliaryElementFamily j) : ℂˣ) : ℂ)
      = ((Equiv.Perm.sign (auxiliaryElementFamily j) : ℤ) : ℂ) := by simp [selectedUnitsCharacter]
  rw [hbridge, hs j]
  fin_cases j <;>
    norm_num [integerCharacterTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]


/-- Character values on the selected elements are the casts of entries in the integer table. -/
lemma irreducibleRepresentations_character_int (i j : Fin 5) :
    (irreducibleRepresentations i).character (auxiliaryElementFamily j) = (integerCharacterTable i j : ℂ) := by
  fin_cases i
  · exact selectedRepresentationZero_character j
  · exact selectedRepresentationOne_character j
  · exact selectedRepresentationTwo_character j
  · exact selectedRepresentationThree_character j
  · exact selectedRepresentationFour_character j



/-- The selected representation indexed by row zero is simple. -/
lemma selectedRepresentationZero_simple : Simple selectedRepresentationZero := representationOfUnitsCharacter_simple _
/-- The selected one-dimensional representation is simple. -/
lemma selectedRepresentationOne_simple : Simple selectedRepresentationOne := representationOfUnitsCharacter_simple _

/-- The selected representation indexed by row four is simple. -/
lemma selectedRepresentationFour_simple : Simple selectedRepresentationFour := by
  rw [selectedRepresentationFour, FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : AuxiliaryType,
      (reducedPermutationRepresentation (G := AuxiliaryType) (α := Fin 4)).character g
        * (reducedPermutationRepresentation (G := AuxiliaryType) (α := Fin 4)).character g⁻¹
      = ((((fixedPointCount (G := AuxiliaryType) (α := Fin 4) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [reducedPermutationRepresentation_character_general, reducedPermutationRepresentation_character_general, fixedPointCount_inv]; push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : AuxiliaryType, (((fixedPointCount (G := AuxiliaryType) (α := Fin 4) g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; norm_num

/-- The selected representation indexed by row two is simple. -/
lemma selectedRepresentationTwo_simple : Simple selectedRepresentationTwo := by
  rw [selectedRepresentationTwo, FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : AuxiliaryType,
      (reducedPermutationRepresentation (G := AuxiliaryType) (α := Fin 3)).character g
        * (reducedPermutationRepresentation (G := AuxiliaryType) (α := Fin 3)).character g⁻¹
      = ((((fixedPointCount (G := AuxiliaryType) (α := Fin 3) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [reducedPermutationRepresentation_character_general, reducedPermutationRepresentation_character_general, fixedPointCount_inv]; push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : AuxiliaryType, (((fixedPointCount (G := AuxiliaryType) (α := Fin 3) g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; norm_num

/-- The selected representation indexed by row three is simple. -/
lemma selectedRepresentationThree_simple : Simple selectedRepresentationThree := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hsign : ∀ g : AuxiliaryType, (selectedUnitsCharacter g : ℂ) * (selectedUnitsCharacter g⁻¹ : ℂ) = 1 := by
    intro g; rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hterm : ∀ g : AuxiliaryType, selectedRepresentationThree.character g * selectedRepresentationThree.character g⁻¹
      = ((((fixedPointCount (G := AuxiliaryType) (α := Fin 4) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [selectedRepresentationThree_character_formula, selectedRepresentationThree_character_formula, fixedPointCount_inv]
    push_cast
    linear_combination (((fixedPointCount (G := AuxiliaryType) (α := Fin 4) g : ℂ) - 1) ^ 2) * hsign g
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : AuxiliaryType, (((fixedPointCount (G := AuxiliaryType) (α := Fin 4) g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; norm_num

/-- Each member of the five-entry representation family is simple. -/
lemma irreducibleRepresentations_simple (i : Fin 5) : Simple (irreducibleRepresentations i) := by
  fin_cases i
  · exact selectedRepresentationZero_simple
  · exact selectedRepresentationOne_simple
  · exact selectedRepresentationTwo_simple
  · exact selectedRepresentationThree_simple
  · exact selectedRepresentationFour_simple



/-- Distinct row indices determine distinct rows of the integer character table. -/
lemma integerCharacterTable_injective : Function.Injective integerCharacterTable := by decide

/-- Representations at different indices are not isomorphic. -/
lemma irreducibleRepresentations_pairwise_nonisomorphic (i j : Fin 5) (hij : i ≠ j) : ¬ Nonempty (irreducibleRepresentations i ≅ irreducibleRepresentations j) := by
  rintro ⟨e⟩
  apply hij
  have hchar : (irreducibleRepresentations i).character = (irreducibleRepresentations j).character := FDRep.char_iso e
  have hrow : ∀ c, integerCharacterTable i c = integerCharacterTable j c := fun c => by
    have h2 : ((integerCharacterTable i c : ℤ) : ℂ) = ((integerCharacterTable j c : ℤ) : ℂ) := by
      rw [← irreducibleRepresentations_character_int, ← irreducibleRepresentations_character_int, hchar]
    exact_mod_cast h2
  exact integerCharacterTable_injective (funext hrow)





/-- The complex image of the auxiliary table agrees with the corresponding integer table entry. -/
lemma auxiliaryCharacterTable_cast (i j : Fin 5) : RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (auxiliaryCharacterTable i j) = (integerCharacterTable i j : ℂ) := by
  have him : (auxiliaryCharacterTable i j).im = 0 := by fin_cases i <;> fin_cases j <;> decide
  have hre : (auxiliaryCharacterTable i j).re = ((integerCharacterTable i j : ℤ) : ℚ) := by fin_cases i <;> fin_cases j <;> decide
  rw [RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, him, hre]; push_cast; ring


/-- Character values on the selected elements are the complex images of entries in the auxiliary table. -/
lemma irreducibleRepresentations_character_aux (i j : Fin 5) :
    (irreducibleRepresentations i).character (auxiliaryElementFamily j) = RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (auxiliaryCharacterTable i j) := by
  rw [irreducibleRepresentations_character_int, auxiliaryCharacterTable_cast]

end


end RepresentationTheory.PermutationActionRepresentations

