/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Permutations of degree three
-/
/-- The permutation group on three elements has three conjugacy classes. -/
@[source_ref "Chapter4/Example4.3_S3" (role := supporting)]
theorem RepresentationTheory.PermutationDegreeThree.card_conjClasses_perm_fin_three :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 3))) = 3 := by
  decide


/-- The squares of one, one, and two sum to the cardinality of the permutation group on three elements. -/
@[source_ref "Chapter4/Example4.3_S3" (role := supporting)]
theorem RepresentationTheory.PermutationDegreeThree.one_sq_add_one_sq_add_two_sq_eq_card_perm_fin_three :
    1 ^ 2 + 1 ^ 2 + 2 ^ 2 = Fintype.card (Equiv.Perm (Fin 3)) := by
  decide

open CategoryTheory MonoidalCategory Module

noncomputable section

namespace RepresentationTheory.PermutationDegreeThree


/-- An auxiliary type. -/
abbrev AuxiliaryType : Type := Equiv.Perm (Fin 3)





/-- The one-dimensional complex representation associated to a unit-valued group character. -/
def representationOfUnitCharacter {G : Type*} [Group G] (χ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]


/-- The character of the representation associated to a unit-valued character is its underlying complex value. -/
@[simp] lemma character_representationOfUnitCharacter {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    (FDRep.of (representationOfUnitCharacter χ)).character g = (χ g : ℂ) := by
  have hg : representationOfUnitCharacter χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ ((FDRep.of (representationOfUnitCharacter χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', hg, map_smul, LinearMap.trace_id]
  simp



/-- A one-dimensional representation arising from a unit-valued character of a finite group is simple. -/
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
@[source_ref "Chapter4/Introduction_4.8/Derived2" (role := supporting)]
def auxiliaryRepresentationTwo : FDRep ℂ AuxiliaryType := FDRep.of (representationOfUnitCharacter (1 : AuxiliaryType →* ℂˣ))


/-- The complex unit-valued character obtained from the sign of a permutation. -/
def signCharacter : AuxiliaryType →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign


/-- An auxiliary finite-dimensional complex representation. -/
@[source_ref "Chapter4/Introduction_4.8/Derived2" (role := supporting)]
def auxiliaryRepresentationOne : FDRep ℂ AuxiliaryType := FDRep.of (representationOfUnitCharacter signCharacter)


/-- The underlying complex value of the sign character is the integer cast of the permutation sign. -/
lemma coe_signCharacter (g : AuxiliaryType) : ((signCharacter g : ℂˣ) : ℂ) = ((Equiv.Perm.sign g : ℤ) : ℂ) := by
  simp [signCharacter]


/-- The second auxiliary representation is simple. -/
lemma simple_auxiliaryRepresentationTwo : Simple auxiliaryRepresentationTwo := simple_representationOfUnitCharacter _


/-- The first auxiliary representation is simple. -/
lemma simple_auxiliaryRepresentationOne : Simple auxiliaryRepresentationOne := simple_representationOfUnitCharacter _




/-- The complex representation obtained by permuting three coordinates. -/
def coordinatePermutationRepresentation : Representation ℂ AuxiliaryType (Fin 3 → ℂ) where
  toFun σ := LinearMap.funLeft ℂ ℂ (⇑σ⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext i; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, Equiv.Perm.coe_mul,
      Function.comp_apply]

/-- The coordinate permutation representation acts by precomposition with the inverse permutation. -/
@[simp] lemma coordinatePermutationRepresentation_apply (σ : AuxiliaryType) (f : Fin 3 → ℂ) (i : Fin 3) :
    coordinatePermutationRepresentation σ f i = f (σ⁻¹ i) := rfl


/-- The complex-linear functional that sums the three coordinates of a vector. -/
def coordinateSumLinearMap : (Fin 3 → ℂ) →ₗ[ℂ] ℂ := ∑ i, LinearMap.proj i

/-- The coordinate-sum functional evaluates as the sum over all coordinates. -/
@[simp] lemma coordinateSumLinearMap_apply (f : Fin 3 → ℂ) : coordinateSumLinearMap f = ∑ i, f i := by
  simp [coordinateSumLinearMap, Finset.sum_apply]


/-- An auxiliary subrepresentation of the three-coordinate permutation representation. -/
def auxiliaryCoordinateSubrepresentation : Subrepresentation coordinatePermutationRepresentation where
  toSubmodule := LinearMap.ker coordinateSumLinearMap
  apply_mem_toSubmodule σ f hf := by
    simp only [LinearMap.mem_ker, coordinateSumLinearMap_apply] at hf ⊢
    calc ∑ i, coordinatePermutationRepresentation σ f i = ∑ i, f (σ⁻¹ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [coordinatePermutationRepresentation_apply]
      _ = ∑ i, f i := Equiv.sum_comp (σ⁻¹ : Equiv.Perm (Fin 3)) f
      _ = 0 := hf


/-- A finite-dimensional representation whose character is the coordinate fixed-point count minus one. -/
@[source_ref "Chapter4/Introduction_4.8/Derived2" (role := supporting)]
def reducedCoordinateRepresentation : FDRep ℂ AuxiliaryType :=
  FDRep.of auxiliaryCoordinateSubrepresentation.toRepresentation







/-- The constant complex-valued vector on three coordinates. -/
def constantVector : Fin 3 → ℂ := fun _ => 1

/-- Every coordinate of the constant vector is one. -/
@[simp] lemma constantVector_apply (i : Fin 3) : constantVector i = 1 := rfl

/-- The constant vector is nonzero. -/
lemma constantVector_ne_zero : (constantVector : Fin 3 → ℂ) ≠ 0 := by
  intro h; have := congrFun h 0; simp [constantVector] at this

/-- Every group element fixes the constant vector in the coordinate representation. -/
@[simp] lemma coordinatePermutationRepresentation_fixed_constantVector (g : AuxiliaryType) : coordinatePermutationRepresentation g constantVector = constantVector := by
  funext i; simp


/-- The complex submodule of three-coordinate functions spanned by a constant vector. -/
def constantLineSubmodule : Submodule ℂ (Fin 3 → ℂ) := Submodule.span ℂ {constantVector}

/-- A vector lies in the constant line exactly when it is a scalar multiple of the distinguished constant vector. -/
lemma mem_constantLineSubmodule_iff {x : Fin 3 → ℂ} : x ∈ constantLineSubmodule ↔ ∃ c : ℂ, c • constantVector = x :=
  Submodule.mem_span_singleton


/-- Each operator of the coordinate permutation representation is the linear map of the inverse permutation matrix. -/
lemma coordinatePermutationRepresentation_eq_permMatrix (g : AuxiliaryType) :
    (coordinatePermutationRepresentation g) = ((g⁻¹ : AuxiliaryType).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext i
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, coordinatePermutationRepresentation_apply]
  rfl


/-- The trace of a coordinate permutation operator is the number of fixed coordinates of its inverse. -/
lemma trace_coordinatePermutationRepresentation (g : AuxiliaryType) :
    LinearMap.trace ℂ (Fin 3 → ℂ) (coordinatePermutationRepresentation g) = (Function.fixedPoints ⇑g⁻¹).ncard := by
  rw [coordinatePermutationRepresentation_eq_permMatrix, Matrix.trace_toLin'_eq, Matrix.trace_permutation]


/-- The number attached to a group element by counting its fixed coordinates. -/
def fixedPointCount (g : AuxiliaryType) : ℕ := (Finset.univ.filter (fun i : Fin 3 => g i = i)).card

/-- A coordinate is fixed by a permutation inverse exactly when it is fixed by the permutation. -/
lemma inv_fixed_iff_fixed (g : AuxiliaryType) (i : Fin 3) : g⁻¹ i = i ↔ g i = i := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, eq_comm]

/-- The number of fixed points of the inverse permutation equals the fixed-point count. -/
lemma ncard_fixedPoints_inv_eq_fixedPointCount (g : AuxiliaryType) :
    (Function.fixedPoints ⇑g⁻¹).ncard = fixedPointCount g := by
  rw [fixedPointCount, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and]
  exact inv_fixed_iff_fixed g i

/-- The fixed-point count is unchanged on taking inverses. -/
@[simp] lemma fixedPointCount_inv (g : AuxiliaryType) : fixedPointCount g⁻¹ = fixedPointCount g := by
  rw [fixedPointCount, fixedPointCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact inv_fixed_iff_fixed g i


/-- The reduced coordinate character equals the fixed-point count minus one. -/
@[source_ref "Chapter4/Introduction_4.8/Derived2" (role := supporting)]
lemma character_reducedCoordinateRepresentation (g : AuxiliaryType) :
    reducedCoordinateRepresentation.character g = (fixedPointCount g : ℂ) - 1 := by
  classical
  set N : Fin 2 → Submodule ℂ (Fin 3 → ℂ) :=
    ![auxiliaryCoordinateSubrepresentation.toSubmodule, constantLineSubmodule] with hN
  have hsurj : Function.Surjective coordinateSumLinearMap := by
    intro c
    refine ⟨Pi.single 0 c, ?_⟩
    rw [coordinateSumLinearMap_apply, Fin.sum_univ_three]
    simp
  have hkerdim : Module.finrank ℂ (LinearMap.ker coordinateSumLinearMap) = 2 := by
    have h := coordinateSumLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_pi] at h
    simp only [Fintype.card_fin] at h
    omega
  have hsum1 : coordinateSumLinearMap constantVector = 3 := by rw [coordinateSumLinearMap_apply]; simp
  have hcompl : IsCompl auxiliaryCoordinateSubrepresentation.toSubmodule constantLineSubmodule := by
    have hone : Module.finrank ℂ constantLineSubmodule = 1 := finrank_span_singleton constantVector_ne_zero
    have hdim : Module.finrank ℂ (Fin 3 → ℂ) ≤
        Module.finrank ℂ auxiliaryCoordinateSubrepresentation.toSubmodule +
          Module.finrank ℂ constantLineSubmodule := by
      have hk : Module.finrank ℂ auxiliaryCoordinateSubrepresentation.toSubmodule = 2 := hkerdim
      rw [hk, hone, Module.finrank_pi]
      simp
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxk hxc
    rw [mem_constantLineSubmodule_iff] at hxc
    obtain ⟨c, rfl⟩ := hxc
    have h0 : coordinateSumLinearMap (c • constantVector) = 0 := hxk
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
  have hf0 : Set.MapsTo (coordinatePermutationRepresentation g) (N 0) (N 0) :=
    auxiliaryCoordinateSubrepresentation.apply_mem_toSubmodule g
  have hf1 : Set.MapsTo (coordinatePermutationRepresentation g) (N 1) (N 1) := by
    intro x hx
    change x ∈ constantLineSubmodule at hx
    change coordinatePermutationRepresentation g x ∈ constantLineSubmodule
    rw [mem_constantLineSubmodule_iff] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, coordinatePermutationRepresentation_fixed_constantVector]⟩
  have hf : ∀ i, Set.MapsTo (coordinatePermutationRepresentation g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_coordinatePermutationRepresentation, ncard_fixedPoints_inv_eq_fixedPointCount, Fin.sum_univ_two] at htr
  have hN0 : LinearMap.trace ℂ ↥(N 0)
      ((coordinatePermutationRepresentation g).restrict (hf 0)) =
        reducedCoordinateRepresentation.character g := by
    change LinearMap.trace ℂ ↥(auxiliaryCoordinateSubrepresentation.toSubmodule)
      (auxiliaryCoordinateSubrepresentation.toRepresentation g) =
        LinearMap.trace ℂ ↥(auxiliaryCoordinateSubrepresentation.toSubmodule)
          ((FDRep.of auxiliaryCoordinateSubrepresentation.toRepresentation).ρ g)
    rw [FDRep.of_ρ']
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((coordinatePermutationRepresentation g).restrict (hf 1)) = 1 := by
    have hid : (coordinatePermutationRepresentation g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hx : (x : Fin 3 → ℂ) ∈ constantLineSubmodule := x.2
      rw [mem_constantLineSubmodule_iff] at hx
      obtain ⟨c, hc⟩ := hx
      change coordinatePermutationRepresentation g (x : Fin 3 → ℂ) = (x : Fin 3 → ℂ)
      rw [← hc, map_smul, coordinatePermutationRepresentation_fixed_constantVector]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton constantVector_ne_zero
    rw [hid, LinearMap.trace_id, hfin]
    norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]
  exact htr.symm



/-- The reduced coordinate representation is simple. -/
lemma simple_reducedCoordinateRepresentation : Simple reducedCoordinateRepresentation := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : AuxiliaryType,
      reducedCoordinateRepresentation.character g * reducedCoordinateRepresentation.character g⁻¹
      = (((fixedPointCount g : ℤ) - 1) ^ 2 : ℤ) := by
    intro g
    rw [character_reducedCoordinateRepresentation, character_reducedCoordinateRepresentation, fixedPointCount_inv]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← Int.cast_sum]
  have hsum : ∑ g : AuxiliaryType, (((fixedPointCount g : ℤ) - 1) ^ 2) = 6 := by decide
  rw [hsum]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num




/-- The reduced coordinate representation has character value two at the identity. -/
lemma character_reducedCoordinateRepresentation_one :
    reducedCoordinateRepresentation.character 1 = 2 := by
  rw [character_reducedCoordinateRepresentation]
  have : fixedPointCount (1 : AuxiliaryType) = 3 := by decide
  rw [this]; norm_num


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


/-- The reduced coordinate representation has complex dimension two. -/
lemma finrank_reducedCoordinateRepresentation : finrank ℂ (reducedCoordinateRepresentation : Type) = 2 := by
  have h := FDRep.char_one reducedCoordinateRepresentation
  rw [character_reducedCoordinateRepresentation_one] at h
  exact_mod_cast h.symm



/-- The sum of the squares of the three displayed representation dimensions equals the group cardinality. -/
theorem sum_sq_finrank_eq_card :
    finrank ℂ (auxiliaryRepresentationTwo : Type) ^ 2 + finrank ℂ (auxiliaryRepresentationOne : Type) ^ 2
      + finrank ℂ (reducedCoordinateRepresentation : Type) ^ 2 = Fintype.card AuxiliaryType := by
  rw [finrank_auxiliaryRepresentationTwo, finrank_auxiliaryRepresentationOne, finrank_reducedCoordinateRepresentation]
  decide

end RepresentationTheory.PermutationDegreeThree

end
