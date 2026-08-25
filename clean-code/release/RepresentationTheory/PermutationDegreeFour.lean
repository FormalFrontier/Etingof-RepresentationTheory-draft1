/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! # Permutations of degree four -/


set_option maxRecDepth 10000 in

/-- The permutation group on four elements has five conjugacy classes. -/
@[source_ref "Chapter4/Example4.3_S4" (role := supporting)]
theorem RepresentationTheory.PermutationDegreeFour.card_conjClasses_perm_fin_four :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 4))) = 5 := by
  decide


/-- The displayed squares of one, one, two, three, and three sum to the cardinality of the permutation group on four elements. -/
@[source_ref "Chapter4/Example4.3_S4" (role := supporting)]
theorem RepresentationTheory.PermutationDegreeFour.sum_dimension_squares_eq_card_perm_fin_four :
    1 ^ 2 + 1 ^ 2 + 2 ^ 2 + 3 ^ 2 + 3 ^ 2 = Fintype.card (Equiv.Perm (Fin 4)) := by
  decide

open CategoryTheory MonoidalCategory Module

noncomputable section

namespace RepresentationTheory.PermutationDegreeFour


/-- An auxiliary type. -/
abbrev AuxiliaryType : Type := Equiv.Perm (Fin 4)


/-- The one-dimensional complex representation associated to a unit-valued group character. -/
def representationOfUnitCharacter {G : Type*} [Group G] (χ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]


/-- The character of a representation built from a unit-valued character is its underlying complex value. -/
@[simp] lemma character_representationOfUnitCharacter {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    (FDRep.of (representationOfUnitCharacter χ)).character g = (χ g : ℂ) := by
  have hg : representationOfUnitCharacter χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ ((FDRep.of (representationOfUnitCharacter χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', hg, map_smul, LinearMap.trace_id]
  simp


/-- The representation associated to a unit-valued character of a finite group is simple. -/
lemma simple_representationOfUnitCharacter {G : Type} [Group G] [Finite G] (χ : G →* ℂˣ) :
    Simple (FDRep.of (representationOfUnitCharacter χ)) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [FDRep.simple_iff_char_is_norm_one]
  have : ∀ g : G, (FDRep.of (representationOfUnitCharacter χ)).character g * (FDRep.of (representationOfUnitCharacter χ)).character g⁻¹
      = 1 := by
    intro g
    rw [character_representationOfUnitCharacter, character_representationOfUnitCharacter, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Nat.card_eq_fintype_card]


/-- An auxiliary finite-dimensional complex representation. -/
def auxiliaryRepresentationTwo : FDRep ℂ AuxiliaryType := FDRep.of (representationOfUnitCharacter (1 : AuxiliaryType →* ℂˣ))


/-- The complex unit-valued character obtained from the sign of a permutation. -/
def signCharacter : AuxiliaryType →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign


/-- An auxiliary finite-dimensional complex representation. -/
def auxiliaryRepresentationOne : FDRep ℂ AuxiliaryType := FDRep.of (representationOfUnitCharacter signCharacter)


/-- The underlying complex value of the sign character is the integer cast of the permutation sign. -/
lemma coe_signCharacter (g : AuxiliaryType) : ((signCharacter g : ℂˣ) : ℂ) = ((Equiv.Perm.sign g : ℤ) : ℂ) := by
  simp [signCharacter]


/-- The second auxiliary representation is simple. -/
lemma simple_auxiliaryRepresentationTwo : Simple auxiliaryRepresentationTwo := simple_representationOfUnitCharacter _


/-- The first auxiliary representation is simple. -/
lemma simple_auxiliaryRepresentationOne : Simple auxiliaryRepresentationOne := simple_representationOfUnitCharacter _


/-- The complex representation obtained by permuting four coordinates. -/
def coordinatePermutationRepresentationFinFour : Representation ℂ AuxiliaryType (Fin 4 → ℂ) where
  toFun σ := LinearMap.funLeft ℂ ℂ (⇑σ⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext i; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, Equiv.Perm.coe_mul,
      Function.comp_apply]

/-- The four-coordinate representation acts by precomposition with the inverse permutation. -/
@[simp] lemma coordinatePermutationRepresentationFinFour_apply (σ : AuxiliaryType) (f : Fin 4 → ℂ) (i : Fin 4) :
    coordinatePermutationRepresentationFinFour σ f i = f (σ⁻¹ i) := rfl


/-- The complex-linear functional summing four coordinates. -/
def coordinateSumFinFour : (Fin 4 → ℂ) →ₗ[ℂ] ℂ := ∑ i, LinearMap.proj i

/-- The four-coordinate sum functional evaluates as the sum over all coordinates. -/
@[simp] lemma coordinateSumFinFour_apply (f : Fin 4 → ℂ) : coordinateSumFinFour f = ∑ i, f i := by
  simp [coordinateSumFinFour, Finset.sum_apply]


/-- An auxiliary subrepresentation of the four-coordinate permutation representation. -/
def auxiliaryCoordinateSubrepresentationFinFour : Subrepresentation coordinatePermutationRepresentationFinFour where
  toSubmodule := LinearMap.ker coordinateSumFinFour
  apply_mem_toSubmodule σ f hf := by
    simp only [LinearMap.mem_ker, coordinateSumFinFour_apply] at hf ⊢
    calc ∑ i, coordinatePermutationRepresentationFinFour σ f i = ∑ i, f (σ⁻¹ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [coordinatePermutationRepresentationFinFour_apply]
      _ = ∑ i, f i := Equiv.sum_comp (σ⁻¹ : Equiv.Perm (Fin 4)) f
      _ = 0 := hf


/-- A finite-dimensional representation whose character is the four-coordinate fixed-point count minus one. -/
@[source_ref "Chapter4/Example4.3_S4" (role := supporting)]
def reducedCoordinateRepresentation : FDRep ℂ AuxiliaryType := FDRep.of auxiliaryCoordinateSubrepresentationFinFour.toRepresentation


/-- The constant complex-valued vector on four coordinates. -/
def constantVectorFinFour : Fin 4 → ℂ := fun _ => 1

/-- Every entry of the four-coordinate constant vector equals one. -/
@[simp] lemma constantVectorFinFour_apply (i : Fin 4) : constantVectorFinFour i = 1 := rfl

/-- The four-coordinate constant vector is nonzero. -/
lemma constantVectorFinFour_ne_zero : (constantVectorFinFour : Fin 4 → ℂ) ≠ 0 := by
  intro h; have := congrFun h 0; simp [constantVectorFinFour] at this

/-- The four-coordinate permutation representation fixes the constant vector. -/
@[simp] lemma coordinatePermutationRepresentationFinFour_fixed_constantVector (g : AuxiliaryType) : coordinatePermutationRepresentationFinFour g constantVectorFinFour = constantVectorFinFour := by
  funext i; simp


/-- The complex line of four-coordinate vectors spanned by the distinguished constant vector. -/
def constantLineFinFour : Submodule ℂ (Fin 4 → ℂ) := Submodule.span ℂ {constantVectorFinFour}

/-- A four-coordinate vector lies in the constant line exactly when it is a scalar multiple of the constant vector. -/
lemma mem_constantLineFinFour_iff {x : Fin 4 → ℂ} : x ∈ constantLineFinFour ↔ ∃ c : ℂ, c • constantVectorFinFour = x :=
  Submodule.mem_span_singleton


/-- A four-coordinate representation operator is the linear map of the inverse permutation matrix. -/
lemma coordinatePermutationRepresentationFinFour_eq_permMatrix (g : AuxiliaryType) :
    (coordinatePermutationRepresentationFinFour g) = ((g⁻¹ : AuxiliaryType).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext i
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, coordinatePermutationRepresentationFinFour_apply]
  rfl


/-- The trace of a four-coordinate permutation operator is the number of fixed points of its inverse. -/
lemma trace_coordinatePermutationRepresentationFinFour (g : AuxiliaryType) :
    LinearMap.trace ℂ (Fin 4 → ℂ) (coordinatePermutationRepresentationFinFour g) = (Function.fixedPoints ⇑g⁻¹).ncard := by
  rw [coordinatePermutationRepresentationFinFour_eq_permMatrix, Matrix.trace_toLin'_eq, Matrix.trace_permutation]


/-- A natural-number statistic given by fixed points in the four-coordinate action. -/
def fixedPointCount (g : AuxiliaryType) : ℕ := (Finset.univ.filter (fun i : Fin 4 => g i = i)).card

/-- A coordinate is fixed by an inverse permutation exactly when it is fixed by the permutation. -/
lemma inv_fixed_iff_fixed (g : AuxiliaryType) (i : Fin 4) : g⁻¹ i = i ↔ g i = i := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, eq_comm]

/-- The inverse permutation has as many fixed points as the four-coordinate fixed-point count. -/
lemma ncard_fixedPoints_inv_eq (g : AuxiliaryType) :
    (Function.fixedPoints ⇑g⁻¹).ncard = fixedPointCount g := by
  rw [fixedPointCount, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and]
  exact inv_fixed_iff_fixed g i

/-- The four-coordinate fixed-point count is invariant under inversion. -/
@[simp] lemma fixedPointCount_inv (g : AuxiliaryType) : fixedPointCount g⁻¹ = fixedPointCount g := by
  rw [fixedPointCount, fixedPointCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact inv_fixed_iff_fixed g i


/-- The reduced coordinate character equals the fixed-point count minus one. -/
lemma character_reducedCoordinateRepresentation (g : AuxiliaryType) :
    reducedCoordinateRepresentation.character g = (fixedPointCount g : ℂ) - 1 := by
  classical
  set N : Fin 2 → Submodule ℂ (Fin 4 → ℂ) := ![auxiliaryCoordinateSubrepresentationFinFour.toSubmodule, constantLineFinFour] with hN
  have hsurj : Function.Surjective coordinateSumFinFour := by
    intro c
    refine ⟨Pi.single 0 c, ?_⟩
    rw [coordinateSumFinFour_apply, Fin.sum_univ_four]
    simp
  have hkerdim : Module.finrank ℂ (LinearMap.ker coordinateSumFinFour) = 3 := by
    have h := coordinateSumFinFour.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_pi] at h
    simp only [Fintype.card_fin] at h
    omega
  have hsum1 : coordinateSumFinFour constantVectorFinFour = 4 := by rw [coordinateSumFinFour_apply]; simp
  have hcompl : IsCompl auxiliaryCoordinateSubrepresentationFinFour.toSubmodule constantLineFinFour := by
    have hone : Module.finrank ℂ constantLineFinFour = 1 := finrank_span_singleton constantVectorFinFour_ne_zero
    have hdim : Module.finrank ℂ (Fin 4 → ℂ) ≤
        Module.finrank ℂ auxiliaryCoordinateSubrepresentationFinFour.toSubmodule + Module.finrank ℂ constantLineFinFour := by
      have hk : Module.finrank ℂ auxiliaryCoordinateSubrepresentationFinFour.toSubmodule = 3 := hkerdim
      rw [hk, hone, Module.finrank_pi]
      simp
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxk hxc
    rw [mem_constantLineFinFour_iff] at hxc
    obtain ⟨c, rfl⟩ := hxc
    have h0 : coordinateSumFinFour (c • constantVectorFinFour) = 0 := hxk
    rw [map_smul, hsum1, smul_eq_mul] at h0
    have hc : c = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · norm_num at h
    simp [hc]
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
    omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (zero_ne_one) huniv).mpr hcompl
  have hf0 : Set.MapsTo (coordinatePermutationRepresentationFinFour g) (N 0) (N 0) := auxiliaryCoordinateSubrepresentationFinFour.apply_mem_toSubmodule g
  have hf1 : Set.MapsTo (coordinatePermutationRepresentationFinFour g) (N 1) (N 1) := by
    intro x hx
    change x ∈ constantLineFinFour at hx
    change coordinatePermutationRepresentationFinFour g x ∈ constantLineFinFour
    rw [mem_constantLineFinFour_iff] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, coordinatePermutationRepresentationFinFour_fixed_constantVector]⟩
  have hf : ∀ i, Set.MapsTo (coordinatePermutationRepresentationFinFour g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_coordinatePermutationRepresentationFinFour, ncard_fixedPoints_inv_eq, Fin.sum_univ_two] at htr
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((coordinatePermutationRepresentationFinFour g).restrict (hf 0)) = reducedCoordinateRepresentation.character g := by
    change LinearMap.trace ℂ ↥(auxiliaryCoordinateSubrepresentationFinFour.toSubmodule) (auxiliaryCoordinateSubrepresentationFinFour.toRepresentation g)
      = LinearMap.trace ℂ ↥(auxiliaryCoordinateSubrepresentationFinFour.toSubmodule) ((FDRep.of auxiliaryCoordinateSubrepresentationFinFour.toRepresentation).ρ g)
    rw [FDRep.of_ρ']
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((coordinatePermutationRepresentationFinFour g).restrict (hf 1)) = 1 := by
    have hid : (coordinatePermutationRepresentationFinFour g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hx : (x : Fin 4 → ℂ) ∈ constantLineFinFour := x.2
      rw [mem_constantLineFinFour_iff] at hx
      obtain ⟨c, hc⟩ := hx
      change coordinatePermutationRepresentationFinFour g (x : Fin 4 → ℂ) = (x : Fin 4 → ℂ)
      rw [← hc, map_smul, coordinatePermutationRepresentationFinFour_fixed_constantVector]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton constantVectorFinFour_ne_zero
    rw [hid, LinearMap.trace_id, hfin]
    norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]
  exact htr.symm


/-- The reduced coordinate representation is simple. -/
lemma simple_reducedCoordinateRepresentation : Simple reducedCoordinateRepresentation := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : AuxiliaryType, reducedCoordinateRepresentation.character g * reducedCoordinateRepresentation.character g⁻¹
      = (((fixedPointCount g : ℤ) - 1) ^ 2 : ℤ) := by
    intro g
    rw [character_reducedCoordinateRepresentation, character_reducedCoordinateRepresentation, fixedPointCount_inv]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← Int.cast_sum]
  have hsum : ∑ g : AuxiliaryType, (((fixedPointCount g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num


/-- The representation obtained by scaling each action operator by a unit-valued character. -/
@[source_ref "Chapter4/Example4.3_S4" (role := supporting)]
def twistRepresentationByCharacter {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (χ : G →* ℂˣ) (ρ : Representation ℂ G V) : Representation ℂ G V where
  toFun g := ((χ g : ℂˣ) : ℂ) • ρ g
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, Units.val_mul, Module.End.mul_eq_comp]
    ext x
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul]
    ring_nf

/-- A character twist acts by the character value times the original representation operator. -/
@[simp] lemma twistRepresentationByCharacter_apply {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (χ : G →* ℂˣ) (ρ : Representation ℂ G V) (g : G) :
    twistRepresentationByCharacter χ ρ g = ((χ g : ℂˣ) : ℂ) • ρ g := rfl


/-- The character of a character twist is the product of the twisting character and the original character. -/
lemma character_twistRepresentationByCharacter {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (χ : G →* ℂˣ) (ρ : Representation ℂ G V) (g : G) :
    (FDRep.of (twistRepresentationByCharacter χ ρ)).character g = (χ g : ℂ) * (FDRep.of ρ).character g := by
  change LinearMap.trace ℂ V ((FDRep.of (twistRepresentationByCharacter χ ρ)).ρ g)
    = (χ g : ℂ) * LinearMap.trace ℂ V ((FDRep.of ρ).ρ g)
  rw [FDRep.of_ρ', FDRep.of_ρ', twistRepresentationByCharacter_apply, map_smul, smul_eq_mul]


/-- A finite-dimensional representation whose character is the permutation sign times the fixed-point count minus one. -/
def signTwistedReducedCoordinateRepresentation : FDRep ℂ AuxiliaryType := FDRep.of (twistRepresentationByCharacter signCharacter auxiliaryCoordinateSubrepresentationFinFour.toRepresentation)


/-- Its character is the permutation sign multiplied by the fixed-point count minus one. -/
lemma character_signTwistedReducedCoordinateRepresentation (g : AuxiliaryType) :
    signTwistedReducedCoordinateRepresentation.character g = ((Equiv.Perm.sign g : ℤ) : ℂ) * ((fixedPointCount g : ℂ) - 1) := by
  rw [signTwistedReducedCoordinateRepresentation, character_twistRepresentationByCharacter, coe_signCharacter]
  congr 1
  exact character_reducedCoordinateRepresentation g


/-- The sign-twisted reduced coordinate representation is simple. -/
lemma simple_signTwistedReducedCoordinateRepresentation : Simple signTwistedReducedCoordinateRepresentation := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : AuxiliaryType, signTwistedReducedCoordinateRepresentation.character g * signTwistedReducedCoordinateRepresentation.character g⁻¹
      = (((fixedPointCount g : ℤ) - 1) ^ 2 : ℤ) := by
    intro g
    rw [character_signTwistedReducedCoordinateRepresentation, character_signTwistedReducedCoordinateRepresentation, fixedPointCount_inv, Equiv.Perm.sign_inv]
    have hsign : ((Equiv.Perm.sign g : ℤ) : ℂ) ^ 2 = 1 := by
      rw [sq, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have key : ((Equiv.Perm.sign g : ℤ) : ℂ) * ((fixedPointCount g : ℂ) - 1)
        * (((Equiv.Perm.sign g : ℤ) : ℂ) * ((fixedPointCount g : ℂ) - 1))
        = ((Equiv.Perm.sign g : ℤ) : ℂ) ^ 2 * ((fixedPointCount g : ℂ) - 1) ^ 2 := by ring
    rw [key, hsign, one_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← Int.cast_sum]
  have hsum : ∑ g : AuxiliaryType, (((fixedPointCount g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num


/-- An auxiliary map assigning a three-valued index to a pair of four-valued indices. -/
def auxiliaryPairIndexMap (a b : Fin 4) : Fin 3 :=
  if (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) ∨
     (a.val = 2 ∧ b.val = 3) ∨ (a.val = 3 ∧ b.val = 2) then 0
  else if (a.val = 0 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 0) ∨
          (a.val = 1 ∧ b.val = 3) ∨ (a.val = 3 ∧ b.val = 1) then 1
  else 2


/-- The action of a group element on the three induced indices. -/
def inducedIndexMap (σ : AuxiliaryType) (i : Fin 3) : Fin 3 := auxiliaryPairIndexMap (σ 0) (σ i.succ)

/-- The identity element acts identically on the induced indices. -/
lemma inducedIndexMap_one (i : Fin 3) : inducedIndexMap 1 i = i := by revert i; decide

set_option maxRecDepth 10000 in
/-- The induced index map sends a product to composition of the corresponding maps. -/
lemma inducedIndexMap_mul (σ τ : AuxiliaryType) (i : Fin 3) :
    inducedIndexMap (σ * τ) i = inducedIndexMap σ (inducedIndexMap τ i) := by revert σ τ i; decide


/-- The permutation of three indices induced by a group element. -/
def inducedPermThree (σ : AuxiliaryType) : Equiv.Perm (Fin 3) where
  toFun := inducedIndexMap σ
  invFun := inducedIndexMap σ⁻¹
  left_inv i := by rw [inducedIndexMap_mul (σ⁻¹) σ i |>.symm, inv_mul_cancel, inducedIndexMap_one]
  right_inv i := by rw [inducedIndexMap_mul σ (σ⁻¹) i |>.symm, mul_inv_cancel, inducedIndexMap_one]

/-- The induced permutation agrees pointwise with the induced index map. -/
@[simp] lemma inducedPermThree_apply (σ : AuxiliaryType) (i : Fin 3) : inducedPermThree σ i = inducedIndexMap σ i := rfl


/-- The monoid homomorphism describing the induced permutation action on three indices. -/
@[source_ref "Chapter4/Example4.3_S4" (role := supporting)]
def inducedPermutationHom : AuxiliaryType →* Equiv.Perm (Fin 3) where
  toFun := inducedPermThree
  map_one' := by ext i; simp [inducedIndexMap_one]
  map_mul' a b := by ext i; simp [Equiv.Perm.mul_apply, inducedIndexMap_mul]

/-- The induced permutation homomorphism acts through the induced index map. -/
@[simp] lemma inducedPermutationHom_apply (σ : AuxiliaryType) (i : Fin 3) : inducedPermutationHom σ i = inducedIndexMap σ i := rfl


/-- The complex coordinate representation associated to the induced action on three indices. -/
def inducedCoordinateRepresentationFinThree : Representation ℂ AuxiliaryType (Fin 3 → ℂ) where
  toFun σ := LinearMap.funLeft ℂ ℂ (⇑(inducedPermutationHom σ)⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext i
    simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [map_mul, Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev,
      Equiv.Perm.coe_mul, Function.comp_apply]

/-- The induced coordinate representation acts by precomposition with the inverse induced permutation. -/
@[simp] lemma inducedCoordinateRepresentation_apply (σ : AuxiliaryType) (f : Fin 3 → ℂ) (i : Fin 3) :
    inducedCoordinateRepresentationFinThree σ f i = f ((inducedPermutationHom σ)⁻¹ i) := rfl


/-- The complex-linear functional summing three coordinates. -/
def coordinateSumFinThree : (Fin 3 → ℂ) →ₗ[ℂ] ℂ := ∑ i, LinearMap.proj i

/-- The three-coordinate sum functional evaluates as the sum over all coordinates. -/
@[simp] lemma coordinateSumFinThree_apply (f : Fin 3 → ℂ) : coordinateSumFinThree f = ∑ i, f i := by
  simp [coordinateSumFinThree, Finset.sum_apply]


/-- An auxiliary subrepresentation of the induced three-coordinate representation. -/
def auxiliaryInducedCoordinateSubrepresentationFinThree : Subrepresentation inducedCoordinateRepresentationFinThree where
  toSubmodule := LinearMap.ker coordinateSumFinThree
  apply_mem_toSubmodule σ f hf := by
    simp only [LinearMap.mem_ker, coordinateSumFinThree_apply] at hf ⊢
    calc ∑ i, inducedCoordinateRepresentationFinThree σ f i = ∑ i, f ((inducedPermutationHom σ)⁻¹ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [inducedCoordinateRepresentation_apply]
      _ = ∑ i, f i := Equiv.sum_comp ((inducedPermutationHom σ)⁻¹) f
      _ = 0 := hf


/-- A finite-dimensional representation whose character is the induced fixed-point count minus one. -/
@[source_ref "Chapter4/Example4.3_S4" (role := supporting)]
def inducedReducedCoordinateRepresentation : FDRep ℂ AuxiliaryType := FDRep.of auxiliaryInducedCoordinateSubrepresentationFinThree.toRepresentation


/-- The constant complex-valued vector on three coordinates. -/
def constantVectorFinThree : Fin 3 → ℂ := fun _ => 1

/-- Every entry of the three-coordinate constant vector equals one. -/
@[simp] lemma constantVectorFinThree_apply (i : Fin 3) : constantVectorFinThree i = 1 := rfl

/-- The three-coordinate constant vector is nonzero. -/
lemma constantVectorFinThree_ne_zero : (constantVectorFinThree : Fin 3 → ℂ) ≠ 0 := by
  intro h; have := congrFun h 0; simp [constantVectorFinThree] at this

/-- The induced coordinate representation fixes the three-coordinate constant vector. -/
@[simp] lemma inducedCoordinateRepresentation_fixed_constantVector (g : AuxiliaryType) : inducedCoordinateRepresentationFinThree g constantVectorFinThree = constantVectorFinThree := by
  funext i; simp


/-- The complex line of three-coordinate vectors spanned by the distinguished constant vector. -/
def constantLineFinThree : Submodule ℂ (Fin 3 → ℂ) := Submodule.span ℂ {constantVectorFinThree}

/-- A three-coordinate vector lies in the constant line exactly when it is a scalar multiple of the constant vector. -/
lemma mem_constantLineFinThree_iff {x : Fin 3 → ℂ} : x ∈ constantLineFinThree ↔ ∃ c : ℂ, c • constantVectorFinThree = x :=
  Submodule.mem_span_singleton

/-- An induced coordinate operator is the linear map of the inverse induced permutation matrix. -/
lemma inducedCoordinateRepresentation_eq_permMatrix (g : AuxiliaryType) :
    (inducedCoordinateRepresentationFinThree g) = (((inducedPermutationHom g)⁻¹).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext i
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, inducedCoordinateRepresentation_apply]
  rfl

/-- The trace of an induced three-coordinate operator is the inverse induced permutation's fixed-point count. -/
lemma trace_inducedCoordinateRepresentationFinThree (g : AuxiliaryType) :
    LinearMap.trace ℂ (Fin 3 → ℂ) (inducedCoordinateRepresentationFinThree g)
      = (Function.fixedPoints ⇑(inducedPermutationHom g)⁻¹).ncard := by
  rw [inducedCoordinateRepresentation_eq_permMatrix, Matrix.trace_toLin'_eq, Matrix.trace_permutation]


/-- A natural-number statistic given by fixed points in the induced three-index action. -/
def inducedFixedPointCount (g : AuxiliaryType) : ℕ := (Finset.univ.filter (fun i : Fin 3 => inducedIndexMap g i = i)).card

/-- An index is fixed by the inverse induced permutation exactly when the induced index map fixes it. -/
lemma inducedPermutationHom_inv_fixed_iff (g : AuxiliaryType) (i : Fin 3) : (inducedPermutationHom g)⁻¹ i = i ↔ inducedIndexMap g i = i := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, eq_comm, inducedPermutationHom_apply]

/-- The inverse induced permutation has as many fixed points as the induced fixed-point count. -/
lemma ncard_inducedFixedPoints_inv_eq (g : AuxiliaryType) :
    (Function.fixedPoints ⇑(inducedPermutationHom g)⁻¹).ncard = inducedFixedPointCount g := by
  rw [inducedFixedPointCount, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and]
  exact inducedPermutationHom_inv_fixed_iff g i


/-- The induced reduced character equals the induced fixed-point count minus one. -/
lemma character_inducedReducedCoordinateRepresentation (g : AuxiliaryType) :
    inducedReducedCoordinateRepresentation.character g = (inducedFixedPointCount g : ℂ) - 1 := by
  classical
  set N : Fin 2 → Submodule ℂ (Fin 3 → ℂ) := ![auxiliaryInducedCoordinateSubrepresentationFinThree.toSubmodule, constantLineFinThree] with hN
  have hsurj : Function.Surjective coordinateSumFinThree := by
    intro c
    refine ⟨Pi.single 0 c, ?_⟩
    rw [coordinateSumFinThree_apply, Fin.sum_univ_three]
    simp
  have hkerdim : Module.finrank ℂ (LinearMap.ker coordinateSumFinThree) = 2 := by
    have h := coordinateSumFinThree.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_pi] at h
    simp only [Fintype.card_fin] at h
    omega
  have hsum1 : coordinateSumFinThree constantVectorFinThree = 3 := by rw [coordinateSumFinThree_apply]; simp
  have hcompl : IsCompl auxiliaryInducedCoordinateSubrepresentationFinThree.toSubmodule constantLineFinThree := by
    have hone : Module.finrank ℂ constantLineFinThree = 1 := finrank_span_singleton constantVectorFinThree_ne_zero
    have hdim : Module.finrank ℂ (Fin 3 → ℂ) ≤
        Module.finrank ℂ auxiliaryInducedCoordinateSubrepresentationFinThree.toSubmodule + Module.finrank ℂ constantLineFinThree := by
      have hk : Module.finrank ℂ auxiliaryInducedCoordinateSubrepresentationFinThree.toSubmodule = 2 := hkerdim
      rw [hk, hone, Module.finrank_pi]
      simp
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxk hxc
    rw [mem_constantLineFinThree_iff] at hxc
    obtain ⟨c, rfl⟩ := hxc
    have h0 : coordinateSumFinThree (c • constantVectorFinThree) = 0 := hxk
    rw [map_smul, hsum1, smul_eq_mul] at h0
    have hc : c = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · norm_num at h
    simp [hc]
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
    omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (zero_ne_one) huniv).mpr hcompl
  have hf0 : Set.MapsTo (inducedCoordinateRepresentationFinThree g) (N 0) (N 0) := auxiliaryInducedCoordinateSubrepresentationFinThree.apply_mem_toSubmodule g
  have hf1 : Set.MapsTo (inducedCoordinateRepresentationFinThree g) (N 1) (N 1) := by
    intro x hx
    change x ∈ constantLineFinThree at hx
    change inducedCoordinateRepresentationFinThree g x ∈ constantLineFinThree
    rw [mem_constantLineFinThree_iff] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, inducedCoordinateRepresentation_fixed_constantVector]⟩
  have hf : ∀ i, Set.MapsTo (inducedCoordinateRepresentationFinThree g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_inducedCoordinateRepresentationFinThree, ncard_inducedFixedPoints_inv_eq, Fin.sum_univ_two] at htr
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((inducedCoordinateRepresentationFinThree g).restrict (hf 0)) = inducedReducedCoordinateRepresentation.character g := by
    change LinearMap.trace ℂ ↥(auxiliaryInducedCoordinateSubrepresentationFinThree.toSubmodule) (auxiliaryInducedCoordinateSubrepresentationFinThree.toRepresentation g)
      = LinearMap.trace ℂ ↥(auxiliaryInducedCoordinateSubrepresentationFinThree.toSubmodule) ((FDRep.of auxiliaryInducedCoordinateSubrepresentationFinThree.toRepresentation).ρ g)
    rw [FDRep.of_ρ']
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((inducedCoordinateRepresentationFinThree g).restrict (hf 1)) = 1 := by
    have hid : (inducedCoordinateRepresentationFinThree g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hx : (x : Fin 3 → ℂ) ∈ constantLineFinThree := x.2
      rw [mem_constantLineFinThree_iff] at hx
      obtain ⟨c, hc⟩ := hx
      change inducedCoordinateRepresentationFinThree g (x : Fin 3 → ℂ) = (x : Fin 3 → ℂ)
      rw [← hc, map_smul, inducedCoordinateRepresentation_fixed_constantVector]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton constantVectorFinThree_ne_zero
    rw [hid, LinearMap.trace_id, hfin]
    norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]
  exact htr.symm


/-- The induced reduced coordinate representation is simple. -/
lemma simple_inducedReducedCoordinateRepresentation : Simple inducedReducedCoordinateRepresentation := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : AuxiliaryType, inducedReducedCoordinateRepresentation.character g * inducedReducedCoordinateRepresentation.character g⁻¹
      = (((inducedFixedPointCount g : ℤ) - 1) * ((inducedFixedPointCount g⁻¹ : ℤ) - 1) : ℤ) := by
    intro g
    rw [character_inducedReducedCoordinateRepresentation, character_inducedReducedCoordinateRepresentation]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← Int.cast_sum]
  have hsum : ∑ g : AuxiliaryType, (((inducedFixedPointCount g : ℤ) - 1) * ((inducedFixedPointCount g⁻¹ : ℤ) - 1)) = 24 := by decide
  rw [hsum]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num


/-- At a transposition, the reduced coordinate character differs from its sign-twisted counterpart. -/
lemma character_reduced_ne_signTwisted_at_swap :
    reducedCoordinateRepresentation.character (Equiv.swap 0 1) ≠ signTwistedReducedCoordinateRepresentation.character (Equiv.swap 0 1) := by
  rw [character_reducedCoordinateRepresentation, character_signTwistedReducedCoordinateRepresentation, show fixedPointCount (Equiv.swap (0 : Fin 4) 1) = 2 from by decide,
    show Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1) = -1 from by decide]
  norm_num


/-- The second auxiliary representation has complex dimension one. -/
lemma finrank_auxiliaryRepresentationTwo : finrank ℂ (auxiliaryRepresentationTwo : Type) = 1 := by
  have h := FDRep.char_one auxiliaryRepresentationTwo
  rw [show auxiliaryRepresentationTwo = FDRep.of (representationOfUnitCharacter (1 : AuxiliaryType →* ℂˣ)) from rfl, character_representationOfUnitCharacter] at h
  simp only [map_one, Units.val_one] at h
  exact_mod_cast h.symm


/-- The first auxiliary representation has complex dimension one. -/
lemma finrank_auxiliaryRepresentationOne : finrank ℂ (auxiliaryRepresentationOne : Type) = 1 := by
  have h := FDRep.char_one auxiliaryRepresentationOne
  rw [show auxiliaryRepresentationOne = FDRep.of (representationOfUnitCharacter signCharacter) from rfl, character_representationOfUnitCharacter] at h
  simp only [map_one, Units.val_one] at h
  exact_mod_cast h.symm


/-- The induced reduced coordinate representation has character value two at the identity. -/
lemma character_inducedReducedCoordinateRepresentation_one : inducedReducedCoordinateRepresentation.character 1 = 2 := by
  rw [character_inducedReducedCoordinateRepresentation, show inducedFixedPointCount (1 : AuxiliaryType) = 3 from by decide]; norm_num


/-- The reduced four-coordinate representation has character value three at the identity. -/
lemma character_reducedCoordinateRepresentation_one : reducedCoordinateRepresentation.character 1 = 3 := by
  rw [character_reducedCoordinateRepresentation, show fixedPointCount (1 : AuxiliaryType) = 4 from by decide]; norm_num


/-- The sign-twisted reduced coordinate representation has character value three at the identity. -/
lemma character_signTwistedReducedCoordinateRepresentation_one : signTwistedReducedCoordinateRepresentation.character 1 = 3 := by
  rw [character_signTwistedReducedCoordinateRepresentation, show fixedPointCount (1 : AuxiliaryType) = 4 from by decide, map_one, Units.val_one]
  norm_num


/-- The induced reduced coordinate representation has complex dimension two. -/
lemma finrank_inducedReducedCoordinateRepresentation : finrank ℂ (inducedReducedCoordinateRepresentation : Type) = 2 := by
  have h := FDRep.char_one inducedReducedCoordinateRepresentation
  rw [character_inducedReducedCoordinateRepresentation_one] at h
  exact_mod_cast h.symm


/-- The reduced coordinate representation has complex dimension three. -/
lemma finrank_reducedCoordinateRepresentation : finrank ℂ (reducedCoordinateRepresentation : Type) = 3 := by
  have h := FDRep.char_one reducedCoordinateRepresentation
  rw [character_reducedCoordinateRepresentation_one] at h
  exact_mod_cast h.symm


/-- The sign-twisted reduced coordinate representation has dimension three. -/
lemma finrank_signTwistedReducedCoordinateRepresentation : finrank ℂ (signTwistedReducedCoordinateRepresentation : Type) = 3 := by
  have h := FDRep.char_one signTwistedReducedCoordinateRepresentation
  rw [character_signTwistedReducedCoordinateRepresentation_one] at h
  exact_mod_cast h.symm


/-- The sum of the squares of the five displayed representation dimensions equals the group cardinality. -/
theorem sum_sq_finrank_eq_card :
    finrank ℂ (auxiliaryRepresentationTwo : Type) ^ 2 + finrank ℂ (auxiliaryRepresentationOne : Type) ^ 2
      + finrank ℂ (inducedReducedCoordinateRepresentation : Type) ^ 2 + finrank ℂ (reducedCoordinateRepresentation : Type) ^ 2
      + finrank ℂ (signTwistedReducedCoordinateRepresentation : Type) ^ 2 = Fintype.card AuxiliaryType := by
  rw [finrank_auxiliaryRepresentationTwo, finrank_auxiliaryRepresentationOne, finrank_inducedReducedCoordinateRepresentation, finrank_reducedCoordinateRepresentation, finrank_signTwistedReducedCoordinateRepresentation]
  decide

end RepresentationTheory.PermutationDegreeFour

end

