/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Group.SmallRepresentationData
import RepresentationTheory.FiniteGroups.CharacterRigidity
import RepresentationTheory.Representation.FiniteProducts
import RepresentationTheory.Alignment.Attribute

/-!
# Tensor-product decompositions for finite-group representations

This module gives character identities and representation-level tensor-product decompositions for
three finite permutation groups, together with the finite multiplicity sums occurring in them.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace RepresentationTheory.RepresentationTensorDecompositions

section MultSum

variable {G : Type} [Group G] [Finite G] {ι : Type} [Fintype ι]

/-- Forms the finite-dimensional representation sum specified by natural multiplicities. -/
def multiplicitySum (V : ι → FDRep ℂ G) (n : ι → ℕ) : FDRep ℂ G :=
  _root_.RepresentationTheory.Representation.FiniteProducts.finiteProduct fun p : (k : ι) × Fin (n k) => V p.1

/-- The character of a representation sum is the corresponding multiplicity-weighted character sum. -/
theorem multiplicitySum_character (V : ι → FDRep ℂ G) (n : ι → ℕ) (g : G) :
    (multiplicitySum V n).character g = ∑ k, (n k : ℂ) * (V k).character g := by
  classical
  rw [multiplicitySum, _root_.RepresentationTheory.Representation.FiniteProducts.character_finiteProduct, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- the summand `(V ⟨k, s⟩.1).character g` is `(V k).character g` by iota reduction, but not
  -- syntactically constant in `s`, so `Finset.sum_const` needs the reduced form first
  change ∑ _s : Fin (n k), (V k).character g = (n k : ℂ) * (V k).character g
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A representation whose character is a natural weighted sum is isomorphic to the associated representation sum. -/
theorem iso_multiplicitySum_of_character_eq (V : ι → FDRep ℂ G) (n : ι → ℕ) (W : FDRep ℂ G)
    (h : ∀ g, W.character g = ∑ k, (n k : ℂ) * (V k).character g) :
    Nonempty (W ≅ multiplicitySum V n) :=
  _root_.RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq _ _ (funext fun g => by rw [multiplicitySum_character]; exact h g)

/-- The multiplicity sum is isomorphic to the biproduct indexed by repeated representation labels. -/
def multiplicitySumIsoBiproduct (V : ι → FDRep ℂ G) (n : ι → ℕ) :
    multiplicitySum V n ≅ ⨁ fun p : (k : ι) × Fin (n k) => V p.1 := by
  classical
  exact _root_.RepresentationTheory.Representation.FiniteProducts.finiteProductIsoBiproduct _

end MultSum

/-- An auxiliary type. -/
abbrev AuxiliaryType : Type := Equiv.Perm (Fin 3)

/-- Constructs a one-dimensional complex representation from a character valued in complex units. -/
def representationOfUnitsCharacter {G : Type*} [Group G] (χ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The constructed representation's character is the underlying complex value of the units character. -/
@[simp] lemma representationOfUnitsCharacter_character {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    (FDRep.of (representationOfUnitsCharacter χ)).character g = (χ g : ℂ) := by
  have hg : representationOfUnitsCharacter χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ ((FDRep.of (representationOfUnitsCharacter χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', hg, map_smul, LinearMap.trace_id]
  simp

/-- A selected finite-dimensional complex representation of the auxiliary type. -/
def selectedRepresentation : FDRep ℂ AuxiliaryType := FDRep.of (representationOfUnitsCharacter (1 : AuxiliaryType →* ℂˣ))

/-- A complex-units-valued character derived from permutation sign. -/
def signUnitsCharacter : AuxiliaryType →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign

/-- A finite-dimensional complex representation of the auxiliary type. -/
def auxiliaryRepresentation : FDRep ℂ AuxiliaryType := FDRep.of (representationOfUnitsCharacter signUnitsCharacter)

/-- The complex value of the units character is the integer cast of permutation sign. -/
lemma signUnitsCharacter_val (g : AuxiliaryType) : ((signUnitsCharacter g : ℂˣ) : ℂ) = ((Equiv.Perm.sign g : ℤ) : ℂ) := by
  simp [signUnitsCharacter]

/-- The complex representation on functions induced by permutations of three points. -/
def permutationRepresentation : Representation ℂ AuxiliaryType (Fin 3 → ℂ) where
  toFun σ := LinearMap.funLeft ℂ ℂ (⇑σ⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext i; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, Equiv.Perm.coe_mul,
      Function.comp_apply]

/-- The representation acts by precomposition with the inverse permutation. -/
@[simp] lemma permutationRepresentation_apply (σ : AuxiliaryType) (f : Fin 3 → ℂ) (i : Fin 3) :
    permutationRepresentation σ f i = f (σ⁻¹ i) := rfl

/-- The complex-linear map summing the three function coordinates. -/
def sumLinearMap : (Fin 3 → ℂ) →ₗ[ℂ] ℂ := ∑ i, LinearMap.proj i

/-- The summation linear map evaluates as the sum over the three indices. -/
@[simp] lemma sumLinearMap_apply (f : Fin 3 → ℂ) : sumLinearMap f = ∑ i, f i := by
  simp [sumLinearMap, Finset.sum_apply]

/-- An auxiliary subrepresentation of the permutation representation. -/
def auxiliarySubrepresentation : Subrepresentation permutationRepresentation where
  toSubmodule := LinearMap.ker sumLinearMap
  apply_mem_toSubmodule σ f hf := by
    simp only [LinearMap.mem_ker, sumLinearMap_apply] at hf ⊢
    calc ∑ i, permutationRepresentation σ f i = ∑ i, f (σ⁻¹ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [permutationRepresentation_apply]
      _ = ∑ i, f i := Equiv.sum_comp (σ⁻¹ : Equiv.Perm (Fin 3)) f
      _ = 0 := hf

/-- The finite-dimensional representation obtained by removing the constant part of the permutation representation. -/
def reducedPermutationRepresentation : FDRep ℂ AuxiliaryType := FDRep.of auxiliarySubrepresentation.toRepresentation

open Module

/-- The constant complex-valued function one on three points. -/
def oneFunction : Fin 3 → ℂ := fun _ => 1

/-- The all-ones function evaluates to one at every point. -/
@[simp] lemma oneFunction_apply (i : Fin 3) : oneFunction i = 1 := rfl

/-- The all-ones function on three points is nonzero. -/
lemma oneFunction_ne_zero : (oneFunction : Fin 3 → ℂ) ≠ 0 := by
  intro h; have := congrFun h 0; simp [oneFunction] at this

/-- Every permutation fixes the all-ones function. -/
@[simp] lemma permutationRepresentation_oneFunction (g : AuxiliaryType) : permutationRepresentation g oneFunction = oneFunction := by
  funext i; simp

/-- The complex submodule spanned by the constant function on three points. -/
def constantFunctionSubmodule : Submodule ℂ (Fin 3 → ℂ) := Submodule.span ℂ {oneFunction}

/-- A function lies in the constant submodule exactly when it is a scalar multiple of the all-ones function. -/
lemma mem_constantFunctionSubmodule_iff {x : Fin 3 → ℂ} : x ∈ constantFunctionSubmodule ↔ ∃ c : ℂ, c • oneFunction = x :=
  Submodule.mem_span_singleton

/-- The action's linear map is the permutation matrix of the inverse. -/
lemma permutationRepresentation_eq_permMatrix (g : AuxiliaryType) :
    (permutationRepresentation g) = ((g⁻¹ : AuxiliaryType).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext i
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, permutationRepresentation_apply]
  rfl

/-- The trace of a permutation action is the number of fixed points of its inverse. -/
lemma trace_permutationRepresentation (g : AuxiliaryType) :
    LinearMap.trace ℂ (Fin 3 → ℂ) (permutationRepresentation g) = (Function.fixedPoints ⇑g⁻¹).ncard := by
  rw [permutationRepresentation_eq_permMatrix, Matrix.trace_toLin'_eq, Matrix.trace_permutation]

/-- Counts fixed points of an auxiliary permutation. -/
def fixedPointCount (g : AuxiliaryType) : ℕ := (Finset.univ.filter (fun i : Fin 3 => g i = i)).card

/-- A point is fixed by a permutation exactly when it is fixed by its inverse. -/
lemma inv_fixed_iff_fixed (g : AuxiliaryType) (i : Fin 3) : g⁻¹ i = i ↔ g i = i := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, eq_comm]

/-- The inverse permutation's fixed-point set has cardinality equal to the fixed-point count. -/
lemma ncard_fixedPoints_inv (g : AuxiliaryType) :
    (Function.fixedPoints ⇑g⁻¹).ncard = fixedPointCount g := by
  rw [fixedPointCount, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and]
  exact inv_fixed_iff_fixed g i

/-- The reduced permutation character is the fixed-point count minus one. -/
lemma reducedPermutationRepresentation_character (g : AuxiliaryType) :
    reducedPermutationRepresentation.character g = (fixedPointCount g : ℂ) - 1 := by
  classical
  set N : Fin 2 → Submodule ℂ (Fin 3 → ℂ) := ![auxiliarySubrepresentation.toSubmodule, constantFunctionSubmodule] with hN
  have hsurj : Function.Surjective sumLinearMap := by
    intro c
    refine ⟨Pi.single 0 c, ?_⟩
    rw [sumLinearMap_apply, Fin.sum_univ_three]
    simp
  have hkerdim : Module.finrank ℂ (LinearMap.ker sumLinearMap) = 2 := by
    have h := sumLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_pi] at h
    simp only [Fintype.card_fin] at h
    omega
  have hsum1 : sumLinearMap oneFunction = 3 := by rw [sumLinearMap_apply]; simp
  have hcompl : IsCompl auxiliarySubrepresentation.toSubmodule constantFunctionSubmodule := by
    have hone : Module.finrank ℂ constantFunctionSubmodule = 1 := finrank_span_singleton oneFunction_ne_zero
    have hdim : Module.finrank ℂ (Fin 3 → ℂ) ≤
        Module.finrank ℂ auxiliarySubrepresentation.toSubmodule + Module.finrank ℂ constantFunctionSubmodule := by
      have hk : Module.finrank ℂ auxiliarySubrepresentation.toSubmodule = 2 := hkerdim
      rw [hk, hone, Module.finrank_pi]
      simp
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxk hxc
    rw [mem_constantFunctionSubmodule_iff] at hxc
    obtain ⟨c, rfl⟩ := hxc
    have h0 : sumLinearMap (c • oneFunction) = 0 := hxk
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
  have hf0 : Set.MapsTo (permutationRepresentation g) (N 0) (N 0) := auxiliarySubrepresentation.apply_mem_toSubmodule g
  have hf1 : Set.MapsTo (permutationRepresentation g) (N 1) (N 1) := by
    intro x hx
    change x ∈ constantFunctionSubmodule at hx
    change permutationRepresentation g x ∈ constantFunctionSubmodule
    rw [mem_constantFunctionSubmodule_iff] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, permutationRepresentation_oneFunction]⟩
  have hf : ∀ i, Set.MapsTo (permutationRepresentation g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_permutationRepresentation, ncard_fixedPoints_inv, Fin.sum_univ_two] at htr
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((permutationRepresentation g).restrict (hf 0)) = reducedPermutationRepresentation.character g := by
    change LinearMap.trace ℂ ↥(auxiliarySubrepresentation.toSubmodule) (auxiliarySubrepresentation.toRepresentation g)
      = LinearMap.trace ℂ ↥(auxiliarySubrepresentation.toSubmodule) ((FDRep.of auxiliarySubrepresentation.toRepresentation).ρ g)
    rw [FDRep.of_ρ']
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((permutationRepresentation g).restrict (hf 1)) = 1 := by
    have hid : (permutationRepresentation g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hx : (x : Fin 3 → ℂ) ∈ constantFunctionSubmodule := x.2
      rw [mem_constantFunctionSubmodule_iff] at hx
      obtain ⟨c, hc⟩ := hx
      change permutationRepresentation g (x : Fin 3 → ℂ) = (x : Fin 3 → ℂ)
      rw [← hc, map_smul, permutationRepresentation_oneFunction]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton oneFunction_ne_zero
    rw [hid, LinearMap.trace_id, hfin]
    norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]
  exact htr.symm

/-- A three-entry family of finite-dimensional complex representations. -/
def representationFamily : Fin 3 → FDRep ℂ AuxiliaryType := ![selectedRepresentation, auxiliaryRepresentation, reducedPermutationRepresentation]

/-- A function recording three complex character values for each auxiliary element. -/
def characterTable (g : AuxiliaryType) : Fin 3 → ℂ := ![1, ((signUnitsCharacter g : ℂˣ) : ℂ), (fixedPointCount g : ℂ) - 1]

/-- The character at index zero is constantly one. -/
lemma character_zero (g : AuxiliaryType) : (representationFamily 0).character g = 1 := by
  change (FDRep.of (representationOfUnitsCharacter (1 : AuxiliaryType →* ℂˣ))).character g = 1
  rw [representationOfUnitsCharacter_character]; simp

/-- The character at index one is the complex value of the selected units character. -/
lemma character_one (g : AuxiliaryType) : (representationFamily 1).character g = ((signUnitsCharacter g : ℂˣ) : ℂ) := by
  change (FDRep.of (representationOfUnitsCharacter signUnitsCharacter)).character g = _
  rw [representationOfUnitsCharacter_character]

/-- The character at index two is the fixed-point count minus one. -/
lemma character_two (g : AuxiliaryType) : (representationFamily 2).character g = (fixedPointCount g : ℂ) - 1 := by
  change reducedPermutationRepresentation.character g = _
  exact reducedPermutationRepresentation_character g

/-- The indexed representation characters agree with the three-column complex table. -/
lemma representationFamily_character_eq_table (i : Fin 3) (g : AuxiliaryType) : (representationFamily i).character g = characterTable g i := by
  fin_cases i
  · exact character_zero g
  · exact character_one g
  · exact character_two g

/-- Natural multiplicities for tensor products in the three-entry representation family. -/
def representationFamilyTensorMultiplicities : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![1,0,0], ![0,1,0], ![0,0,1]],
    ![![0,1,0], ![1,0,0], ![0,0,1]],
    ![![0,0,1], ![0,0,1], ![1,1,1]]]

/-- An auxiliary result with an unavailable displayed type. -/
lemma auxiliaryResult (g : AuxiliaryType) :
    (Equiv.Perm.sign g = 1 ∧ fixedPointCount g = 3) ∨
    (Equiv.Perm.sign g = -1 ∧ fixedPointCount g = 1) ∨
    (Equiv.Perm.sign g = 1 ∧ fixedPointCount g = 0) := by
  revert g; decide

/-- Products of characters in the three-entry family decompose with the displayed natural multiplicities. -/
theorem representationFamily_character_mul (i j : Fin 3) (g : AuxiliaryType) :
    (representationFamily i).character g * (representationFamily j).character g
      = ∑ k, (representationFamilyTensorMultiplicities i j k : ℂ) * (representationFamily k).character g := by
  have hsign := signUnitsCharacter_val g
  simp only [representationFamily_character_eq_table, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp only [characterTable, representationFamilyTensorMultiplicities, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue] <;>
    rcases auxiliaryResult g with ⟨hs, hf⟩ | ⟨hs, hf⟩ | ⟨hs, hf⟩ <;>
    · rw [hsign, hs, hf]; push_cast; ring

/-- The tensor character is the weighted sum determined by the three-index multiplicity table. -/
theorem representationFamily_tensor_character (i j : Fin 3) (g : AuxiliaryType) :
    (representationFamily i ⊗ representationFamily j).character g = ∑ k, (representationFamilyTensorMultiplicities i j k : ℂ) * (representationFamily k).character g := by
  rw [FDRep.char_tensor, Pi.mul_apply]
  exact representationFamily_character_mul i j g

/-- Each tensor product in the three-entry family is isomorphic to its multiplicity sum. -/
@[source_ref "Chapter4/Example4.9.1" (role := primary)]
theorem representationFamily_tensor_iso_multiplicitySum (i j : Fin 3) :
    Nonempty ((representationFamily i ⊗ representationFamily j : FDRep ℂ AuxiliaryType) ≅ multiplicitySum representationFamily (representationFamilyTensorMultiplicities i j)) :=
  iso_multiplicitySum_of_character_eq representationFamily (representationFamilyTensorMultiplicities i j) _ (representationFamily_tensor_character i j)

/-- Each tensor product in the three-entry family is isomorphic to the corresponding biproduct. -/
@[source_ref "Chapter4/Example4.9.1" (role := primary)]
theorem representationFamily_tensor_iso_biproduct (i j : Fin 3) :
    Nonempty ((representationFamily i ⊗ representationFamily j : FDRep ℂ AuxiliaryType) ≅
      ⨁ fun p : (k : Fin 3) × Fin (representationFamilyTensorMultiplicities i j k) => representationFamily p.1) :=
  (representationFamily_tensor_iso_multiplicitySum i j).map fun e => e ≪≫ multiplicitySumIsoBiproduct representationFamily (representationFamilyTensorMultiplicities i j)

/-- The tensor square of the reduced permutation representation is isomorphic to the displayed comparison representation. -/
@[source_ref "Chapter4/Example4.9.1" (role := supporting)]
theorem reducedPermutationRepresentation_tensor_sq_iso :
    Nonempty ((reducedPermutationRepresentation ⊗ reducedPermutationRepresentation : FDRep ℂ AuxiliaryType) ≅ _root_.RepresentationTheory.Representation.FiniteProducts.finiteProduct representationFamily) := by
  have hone : ∀ k, representationFamilyTensorMultiplicities 2 2 k = 1 := by decide
  refine _root_.RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq _ _ (funext fun g => ?_)
  rw [_root_.RepresentationTheory.Representation.FiniteProducts.character_finiteProduct]
  refine (representationFamily_tensor_character 2 2 g).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [hone k, Nat.cast_one, one_mul]

/-- The permutation group on three points has three conjugacy classes. -/
theorem permFinThree_conjClasses_card :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 3))) = 3 := by
  decide

/-- The permutation group on three points has six elements. -/
theorem permFinThree_card :
    Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  decide

section A5
open _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType

/-- Natural multiplicities for tensor products in the first five-entry representation family. -/
def firstFiveTensorMultiplicities : Fin 5 → Fin 5 → Fin 5 → ℕ :=
  ![![![1,0,0,0,0], /- next entry -/ ![0,1,0,0,0], /- next entry -/ ![0,0,1,0,0],
      /- next entry -/ ![0,0,0,1,0], /- next entry -/ ![0,0,0,0,1]],
    /- next entry -/ ![![0,1,0,0,0], /- next entry -/ ![1,1,0,0,1],
      /- next entry -/ ![0,0,0,1,1], /- next entry -/ ![0,0,1,1,1],
      /- next entry -/ ![0,1,1,1,1]],
    /- next entry -/ ![![0,0,1,0,0], /- next entry -/ ![0,0,0,1,1],
      /- next entry -/ ![1,0,1,0,1], /- next entry -/ ![0,1,0,1,1],
      /- next entry -/ ![0,1,1,1,1]],
    /- next entry -/ ![![0,0,0,1,0], /- next entry -/ ![0,0,1,1,1],
      /- next entry -/ ![0,1,0,1,1], /- next entry -/ ![1,1,1,1,1],
      /- next entry -/ ![0,1,1,1,2]],
    /- next entry -/ ![![0,0,0,0,1], /- next entry -/ ![0,1,1,1,1],
      /- next entry -/ ![0,1,1,1,1], /- next entry -/ ![0,1,1,1,2],
      /- next entry -/ ![1,1,1,2,2]]]

/-- Characters in the first five-entry family are given by the displayed composite expression. -/
lemma firstFiveRepresentationFamily_character_formula (i : Fin 5) (g : _root_.RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) :
    (_root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g = _root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (_root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable i (_root_.RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)) := by
  obtain ⟨c, hc⟩ := _root_.RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
  have key : (_root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g
      = (_root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character (_root_.RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative (_root_.RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)) := by
    rw [← FDRep.char_conj (_root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i) (_root_.RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative (_root_.RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)) c, hc]
  rw [key]
  simpa only [_root_.RepresentationTheory.TensorSquareSpectralDecomposition.representationCharacterRowIndex, id_eq] using _root_.RepresentationTheory.TensorSquareSpectralDecomposition.character_indexedSimpleRepresentations i (_root_.RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

/-- Maps natural numbers into an auxiliary type. -/
def auxiliaryNatMap (n : ℕ) : _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType := ⟨(n : ℚ), 0⟩

/-- Composing the displayed auxiliary map with the natural-number map gives the natural cast. -/
lemma auxiliaryMap_natMap (n : ℕ) : _root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (auxiliaryNatMap n) = (n : ℂ) := by
  simp [_root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, auxiliaryNatMap]

/-- The displayed auxiliary map preserves multiplication. -/
lemma auxiliaryMap_mul (a b : _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType) : _root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (a * b) = _root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex a * _root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex b := by
  have hs := _root_.RepresentationTheory.TensorSquareSpectralDecomposition.sq_complex_sqrt_five
  simp only [_root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mul_re, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mul_im]
  push_cast
  linear_combination (-((a.im : ℂ) * (b.im : ℂ))) * hs

-- the `5·5·5 = 125`-way `fin_cases` split needs a raised heartbeat budget; each case is
-- closed by rational `norm_num` on the `re`/`im` components
set_option maxHeartbeats 2000000 in
/-- Products of table entries expand explicitly using the displayed natural-number map and multiplicities. -/
lemma firstFiveTable_mul_raw (i i' j : Fin 5) :
    _root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable i j * _root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable i' j
      = auxiliaryNatMap (firstFiveTensorMultiplicities i i' 0) * _root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable 0 j + auxiliaryNatMap (firstFiveTensorMultiplicities i i' 1) * _root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable 1 j
        + auxiliaryNatMap (firstFiveTensorMultiplicities i i' 2) * _root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable 2 j + auxiliaryNatMap (firstFiveTensorMultiplicities i i' 3) * _root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable 3 j
        + auxiliaryNatMap (firstFiveTensorMultiplicities i i' 4) * _root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable 4 j := by
  fin_cases i <;> fin_cases i' <;> fin_cases j <;>
    apply _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ext <;>
    norm_num [firstFiveTensorMultiplicities, _root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable, auxiliaryNatMap, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mul_re, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mul_im, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.add_re, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.add_im,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im,
      _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re, _root_.RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im]

/-- Products of mapped table entries expand using the first five-entry multiplicities. -/
lemma firstFiveTable_mul_mapped (i i' j : Fin 5) :
    _root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (_root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable i j) * _root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (_root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable i' j)
      = ∑ k, (firstFiveTensorMultiplicities i i' k : ℂ) * _root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex (_root_.RepresentationTheory.Group.PermutationSubgroupData.indexedTable k j) := by
  rw [← auxiliaryMap_mul, firstFiveTable_mul_raw, Fin.sum_univ_five]
  simp only [_root_.RepresentationTheory.TensorSquareSpectralDecomposition.complexValueMap_add, auxiliaryMap_mul, auxiliaryMap_natMap]

/-- Products of characters in the first five-entry family decompose with the displayed natural multiplicities. -/
theorem firstFiveRepresentationFamily_character_mul (i j : Fin 5) (g : _root_.RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) :
    (_root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i).character g * (_root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations j).character g
      = ∑ k, (firstFiveTensorMultiplicities i j k : ℂ) * (_root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations k).character g := by
  simp only [firstFiveRepresentationFamily_character_formula]
  exact firstFiveTable_mul_mapped i j (_root_.RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)

/-- The tensor-product character is the multiplicity-weighted sum of the first five-entry family's characters. -/
theorem firstFiveRepresentationFamily_tensor_character (i j : Fin 5) (g : _root_.RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) :
    (_root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i ⊗ _root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations j).character g
      = ∑ k, (firstFiveTensorMultiplicities i j k : ℂ) * (_root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations k).character g := by
  rw [FDRep.char_tensor, Pi.mul_apply]
  exact firstFiveRepresentationFamily_character_mul i j g

/-- Each tensor product in the first five-entry family is isomorphic to the representation formed from its multiplicity vector. -/
@[source_ref "Chapter4/Example4.9.1" (role := primary)]
theorem firstFiveRepresentationFamily_tensor_iso_multiplicitySum (i j : Fin 5) :
    Nonempty ((_root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i ⊗ _root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations j : FDRep ℂ _root_.RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) ≅
      multiplicitySum _root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations (firstFiveTensorMultiplicities i j)) :=
  iso_multiplicitySum_of_character_eq _root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations (firstFiveTensorMultiplicities i j) _ (firstFiveRepresentationFamily_tensor_character i j)

/-- Each tensor product in the first five-entry family is isomorphic to the corresponding indexed biproduct. -/
@[source_ref "Chapter4/Example4.9.1" (role := primary)]
theorem firstFiveRepresentationFamily_tensor_iso_biproduct (i j : Fin 5) :
    Nonempty ((_root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations i ⊗ _root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations j : FDRep ℂ _root_.RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) ≅
      ⨁ fun p : (k : Fin 5) × Fin (firstFiveTensorMultiplicities i j k) => _root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations p.1) :=
  (firstFiveRepresentationFamily_tensor_iso_multiplicitySum i j).map fun e => e ≪≫ multiplicitySumIsoBiproduct _root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations (firstFiveTensorMultiplicities i j)

/-- The alternating permutations on five points have five conjugacy classes. -/
theorem alternatingFinFive_conjClasses_card :
    Fintype.card (ConjClasses (alternatingGroup (Fin 5))) = 5 :=
  _root_.RepresentationTheory.Group.SmallRepresentationData.card_conjClasses_alternatingGroup_fin5

end A5

section S4
open _root_.RepresentationTheory.PermutationActionRepresentations

/-- Natural multiplicities for tensor products in the second five-entry representation family. -/
def secondFiveTensorMultiplicities : Fin 5 → Fin 5 → Fin 5 → ℕ :=
  ![![![1,0,0,0,0], /- next entry -/ ![0,1,0,0,0], /- next entry -/ ![0,0,1,0,0],
      /- next entry -/ ![0,0,0,1,0], /- next entry -/ ![0,0,0,0,1]],
    /- next entry -/ ![![0,1,0,0,0], /- next entry -/ ![1,0,0,0,0],
      /- next entry -/ ![0,0,1,0,0], /- next entry -/ ![0,0,0,0,1],
      /- next entry -/ ![0,0,0,1,0]],
    /- next entry -/ ![![0,0,1,0,0], /- next entry -/ ![0,0,1,0,0],
      /- next entry -/ ![1,1,1,0,0], /- next entry -/ ![0,0,0,1,1],
      /- next entry -/ ![0,0,0,1,1]],
    /- next entry -/ ![![0,0,0,1,0], /- next entry -/ ![0,0,0,0,1],
      /- next entry -/ ![0,0,0,1,1], /- next entry -/ ![1,0,1,1,1],
      /- next entry -/ ![0,1,1,1,1]],
    /- next entry -/ ![![0,0,0,0,1], /- next entry -/ ![0,0,0,1,0],
      /- next entry -/ ![0,0,0,1,1], /- next entry -/ ![0,1,1,1,1],
      /- next entry -/ ![1,0,1,1,1]]]

/-- Assigns one of five indices to each element of the domain type. -/
def selectedElementIndex (g : _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) : Fin 5 :=
  if _root_.RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) (α := Fin 4) g = 4 then 0
  else if _root_.RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) (α := Fin 4) g = 2 then 1
  else if _root_.RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) (α := Fin 4) g = 1 then 3
  else if Equiv.Perm.sign g = 1 then 2
  else 4

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- `decide` over the 24 elements of `S₄`, with a conjugacy search per element
/-- Every element is conjugate to the selected indexed element. -/
lemma exists_conj_selectedElement (g : _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) : ∃ c : _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType, c * _root_.RepresentationTheory.PermutationActionRepresentations.auxiliaryElementFamily (selectedElementIndex g) * c⁻¹ = g := by
  revert g; decide

/-- Characters in the second five-entry family are given by displayed table entries selected by the index. -/
lemma secondFiveRepresentationFamily_character_formula (i : Fin 5) (g : _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) :
    (_root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations i).character g = (_root_.RepresentationTheory.PermutationActionRepresentations.integerCharacterTable i (selectedElementIndex g) : ℂ) := by
  obtain ⟨c, hc⟩ := exists_conj_selectedElement g
  have key : (_root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations i).character g
      = (_root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations i).character (_root_.RepresentationTheory.PermutationActionRepresentations.auxiliaryElementFamily (selectedElementIndex g)) := by
    rw [← FDRep.char_conj (_root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations i) (_root_.RepresentationTheory.PermutationActionRepresentations.auxiliaryElementFamily (selectedElementIndex g)) c, hc]
  rw [key, _root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations_character_int]

/-- Products of entries in the displayed table expand using the second five-entry multiplicities. -/
lemma secondFiveTable_mul (i i' c : Fin 5) :
    _root_.RepresentationTheory.PermutationActionRepresentations.integerCharacterTable i c * _root_.RepresentationTheory.PermutationActionRepresentations.integerCharacterTable i' c
      = (secondFiveTensorMultiplicities i i' 0 : ℤ) * _root_.RepresentationTheory.PermutationActionRepresentations.integerCharacterTable 0 c + (secondFiveTensorMultiplicities i i' 1 : ℤ) * _root_.RepresentationTheory.PermutationActionRepresentations.integerCharacterTable 1 c + (secondFiveTensorMultiplicities i i' 2 : ℤ) * _root_.RepresentationTheory.PermutationActionRepresentations.integerCharacterTable 2 c
        + (secondFiveTensorMultiplicities i i' 3 : ℤ) * _root_.RepresentationTheory.PermutationActionRepresentations.integerCharacterTable 3 c + (secondFiveTensorMultiplicities i i' 4 : ℤ) * _root_.RepresentationTheory.PermutationActionRepresentations.integerCharacterTable 4 c := by
  fin_cases i <;> fin_cases i' <;> fin_cases c <;> decide

/-- Products of characters in the second five-entry family decompose with the displayed natural multiplicities. -/
theorem secondFiveRepresentationFamily_character_mul (i j : Fin 5) (g : _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) :
    (_root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations i).character g * (_root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations j).character g
      = ∑ k, (secondFiveTensorMultiplicities i j k : ℂ) * (_root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations k).character g := by
  simp only [secondFiveRepresentationFamily_character_formula, Fin.sum_univ_five]
  have hc := congrArg (fun z : ℤ => (z : ℂ)) (secondFiveTable_mul i j (selectedElementIndex g))
  push_cast at hc ⊢
  linear_combination hc

/-- The tensor character is the weighted sum prescribed by the displayed five-index multiplicities. -/
theorem secondFiveRepresentationFamily_tensor_character (i j : Fin 5) (g : _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) :
    (_root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations i ⊗ _root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations j).character g
      = ∑ k, (secondFiveTensorMultiplicities i j k : ℂ) * (_root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations k).character g := by
  rw [FDRep.char_tensor, Pi.mul_apply]
  exact secondFiveRepresentationFamily_character_mul i j g

/-- Each tensor product in the second five-entry family is isomorphic to its multiplicity sum. -/
@[source_ref "Chapter4/Example4.9.1" (role := primary)]
theorem secondFiveRepresentationFamily_tensor_iso_multiplicitySum (i j : Fin 5) :
    Nonempty ((_root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations i ⊗ _root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations j : FDRep ℂ _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) ≅ multiplicitySum _root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations (secondFiveTensorMultiplicities i j)) :=
  iso_multiplicitySum_of_character_eq _root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations (secondFiveTensorMultiplicities i j) _ (secondFiveRepresentationFamily_tensor_character i j)

/-- Each tensor product in the second five-entry family is isomorphic to the corresponding biproduct. -/
@[source_ref "Chapter4/Example4.9.1" (role := supporting)]
theorem secondFiveRepresentationFamily_tensor_iso_biproduct (i j : Fin 5) :
    Nonempty ((_root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations i ⊗ _root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations j : FDRep ℂ _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) ≅
      ⨁ fun p : (k : Fin 5) × Fin (secondFiveTensorMultiplicities i j k) => _root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations p.1) :=
  (secondFiveRepresentationFamily_tensor_iso_multiplicitySum i j).map fun e => e ≪≫ multiplicitySumIsoBiproduct _root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations (secondFiveTensorMultiplicities i j)

/-- The permutation group on four points has five conjugacy classes. -/
theorem permFinFour_conjClasses_card :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 4))) = 5 :=
  _root_.RepresentationTheory.Group.SmallRepresentationData.card_conjClasses_perm_fin4

end S4

end RepresentationTheory.RepresentationTensorDecompositions

end
