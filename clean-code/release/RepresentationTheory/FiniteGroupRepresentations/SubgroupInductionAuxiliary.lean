/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.FDRep.Character
import RepresentationTheory.PermutationDegreeFour
import RepresentationTheory.FiniteGroups.CharacterRigidity
import RepresentationTheory.InductionAndCoinduction
import RepresentationTheory.Subgroup.HomAdjunction
import RepresentationTheory.AuxiliaryRepresentationComputations
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.Alignment.Attribute

/-!
# Subgroup induction auxiliary results

This module records auxiliary finite-group representation and subgroup-induction computations.
-/

open CategoryTheory Module

noncomputable section

namespace RepresentationTheory.FiniteGroupRepresentations.SubgroupInductionAuxiliary

/-! ### Pairwise non-isomorphism -/

/-- Two `S₄`-representations of different dimension cannot be isomorphic. -/
private lemma not_iso_of_finrank_ne {V W : FDRep ℂ _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType}
    (h : finrank ℂ (V : Type) ≠ finrank ℂ (W : Type)) : ¬ Nonempty (V ≅ W) := by
  rintro ⟨e⟩
  exact h (FDRep.isoToLinearEquiv e).finrank_eq

/-- The auxiliary constant-target representation is not isomorphic to the sign-target representation. -/
lemma auxiliary_constant_target_not_iso_sign_target : ¬ Nonempty (_root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo ≅ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne) := by
  rintro ⟨e⟩
  have h := congrFun (FDRep.char_iso e) (Equiv.swap (0 : Fin 4) 1)
  rw [show _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo = FDRep.of (_root_.RepresentationTheory.PermutationDegreeFour.representationOfUnitCharacter (1 : _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType →* ℂˣ)) from rfl,
      show _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne = FDRep.of (_root_.RepresentationTheory.PermutationDegreeFour.representationOfUnitCharacter _root_.RepresentationTheory.PermutationDegreeFour.signCharacter) from rfl,
      _root_.RepresentationTheory.PermutationDegreeFour.character_representationOfUnitCharacter, _root_.RepresentationTheory.PermutationDegreeFour.character_representationOfUnitCharacter] at h
  simp only [MonoidHom.one_apply, Units.val_one, _root_.RepresentationTheory.PermutationDegreeFour.coe_signCharacter] at h
  rw [show Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1) = -1 from by decide] at h
  norm_num at h

/-- The auxiliary constant-target representation is not isomorphic to the second shifted-statistic representation. -/
lemma auxiliary_constant_target_not_iso_second_statistic : ¬ Nonempty (_root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo ≅ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation) :=
  not_iso_of_finrank_ne (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationTwo, _root_.RepresentationTheory.PermutationDegreeFour.finrank_inducedReducedCoordinateRepresentation]; norm_num)

/-- The auxiliary constant-target representation is not isomorphic to the first shifted-statistic representation. -/
lemma auxiliary_constant_target_not_iso_statistic : ¬ Nonempty (_root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo ≅ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation) :=
  not_iso_of_finrank_ne (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationTwo, _root_.RepresentationTheory.PermutationDegreeFour.finrank_reducedCoordinateRepresentation]; norm_num)

/-- The auxiliary constant-target representation is not isomorphic to the signed-statistic representation. -/
lemma auxiliary_constant_target_not_iso_signed_statistic : ¬ Nonempty (_root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo ≅ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) :=
  not_iso_of_finrank_ne (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationTwo, _root_.RepresentationTheory.PermutationDegreeFour.finrank_signTwistedReducedCoordinateRepresentation]; norm_num)

/-- The auxiliary sign-target representation is not isomorphic to the second shifted-statistic representation. -/
lemma auxiliary_sign_target_not_iso_second_statistic : ¬ Nonempty (_root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne ≅ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation) :=
  not_iso_of_finrank_ne (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationOne, _root_.RepresentationTheory.PermutationDegreeFour.finrank_inducedReducedCoordinateRepresentation]; norm_num)

/-- The auxiliary sign-target representation is not isomorphic to the first shifted-statistic representation. -/
lemma auxiliary_sign_target_not_iso_statistic : ¬ Nonempty (_root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne ≅ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation) :=
  not_iso_of_finrank_ne (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationOne, _root_.RepresentationTheory.PermutationDegreeFour.finrank_reducedCoordinateRepresentation]; norm_num)

/-- The auxiliary sign-target representation is not isomorphic to the signed-statistic representation. -/
lemma auxiliary_sign_target_not_iso_signed_statistic : ¬ Nonempty (_root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne ≅ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) :=
  not_iso_of_finrank_ne (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationOne, _root_.RepresentationTheory.PermutationDegreeFour.finrank_signTwistedReducedCoordinateRepresentation]; norm_num)

/-- The auxiliary second-statistic representation is not isomorphic to the first shifted-statistic representation. -/
lemma auxiliary_second_statistic_not_iso_statistic : ¬ Nonempty (_root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation ≅ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation) :=
  not_iso_of_finrank_ne (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_inducedReducedCoordinateRepresentation, _root_.RepresentationTheory.PermutationDegreeFour.finrank_reducedCoordinateRepresentation]; norm_num)

/-- The auxiliary second-statistic representation is not isomorphic to the signed-statistic representation. -/
lemma auxiliary_second_statistic_not_iso_signed_statistic : ¬ Nonempty (_root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation ≅ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) :=
  not_iso_of_finrank_ne (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_inducedReducedCoordinateRepresentation, _root_.RepresentationTheory.PermutationDegreeFour.finrank_signTwistedReducedCoordinateRepresentation]; norm_num)

/-- The auxiliary shifted-statistic representation is not isomorphic to the signed-statistic representation. -/
lemma auxiliary_statistic_not_iso_signed_statistic : ¬ Nonempty (_root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation ≅ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) := by
  rintro ⟨e⟩
  exact _root_.RepresentationTheory.PermutationDegreeFour.character_reduced_ne_signTwisted_at_swap (congrFun (FDRep.char_iso e) (Equiv.swap 0 1))

/-! ### Completeness of the auxiliary catalogue -/

/-- The scalar cast of the cardinality of the specified group is nonzero. -/
instance group_card_cast_neZero : NeZero (Nat.card _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

/-- The auxiliary representation whose character is one on the auxiliary subgroup image is simple. -/
instance auxiliary_constant_target_representation_isSimple : Simple _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo := _root_.RepresentationTheory.PermutationDegreeFour.simple_auxiliaryRepresentationTwo
/-- The auxiliary representation whose character restricts to permutation sign is simple. -/
instance auxiliary_sign_target_representation_isSimple : Simple _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne := _root_.RepresentationTheory.PermutationDegreeFour.simple_auxiliaryRepresentationOne
/-- The auxiliary representation with the second shifted-statistic character formula is simple. -/
instance auxiliary_second_statistic_representation_isSimple : Simple _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation := _root_.RepresentationTheory.PermutationDegreeFour.simple_inducedReducedCoordinateRepresentation
/-- The auxiliary representation with the first shifted-statistic character formula is simple. -/
instance auxiliary_statistic_representation_isSimple : Simple _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation := _root_.RepresentationTheory.PermutationDegreeFour.simple_reducedCoordinateRepresentation
/-- The auxiliary representation with the signed-statistic character formula is simple. -/
instance auxiliary_signed_statistic_representation_isSimple : Simple _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation := _root_.RepresentationTheory.PermutationDegreeFour.simple_signTwistedReducedCoordinateRepresentation

/-- Every simple finite-dimensional complex representation of the specified group is isomorphic to one of the five listed auxiliary representations. -/
@[source_ref "Chapter4/Example4.3_S4" (role := primary)]
theorem simple_iso_auxiliary_cases (S : FDRep ℂ _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType) [Simple S] :
    Nonempty (S ≅ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo) ∨ Nonempty (S ≅ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne) ∨ Nonempty (S ≅ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation) ∨
      Nonempty (S ≅ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation) ∨ Nonempty (S ≅ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) := by
  classical
  obtain ⟨n, V, hsimple, hinj, hsurj, hsum⟩ := RepresentationTheory.FDRep.GroupAlgebraDecomposition.exists_completeSimpleFamily_sum_finrank_sq_eq_card ℂ _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType
  obtain ⟨a, ⟨ea⟩⟩ := hsurj _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo _root_.RepresentationTheory.PermutationDegreeFour.simple_auxiliaryRepresentationTwo
  obtain ⟨b, ⟨eb⟩⟩ := hsurj _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne _root_.RepresentationTheory.PermutationDegreeFour.simple_auxiliaryRepresentationOne
  obtain ⟨c, ⟨ec⟩⟩ := hsurj _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation _root_.RepresentationTheory.PermutationDegreeFour.simple_inducedReducedCoordinateRepresentation
  obtain ⟨d, ⟨ed⟩⟩ := hsurj _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation _root_.RepresentationTheory.PermutationDegreeFour.simple_reducedCoordinateRepresentation
  obtain ⟨f, ⟨ef⟩⟩ := hsurj _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation _root_.RepresentationTheory.PermutationDegreeFour.simple_signTwistedReducedCoordinateRepresentation
  obtain ⟨s, ⟨es⟩⟩ := hsurj S inferInstance
  -- dimensions of the five distinguished indices
  have hda : finrank ℂ (V a : Type) = 1 := by
    rw [← (FDRep.isoToLinearEquiv ea).finrank_eq, _root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationTwo]
  have hdb : finrank ℂ (V b : Type) = 1 := by
    rw [← (FDRep.isoToLinearEquiv eb).finrank_eq, _root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationOne]
  have hdc : finrank ℂ (V c : Type) = 2 := by
    rw [← (FDRep.isoToLinearEquiv ec).finrank_eq, _root_.RepresentationTheory.PermutationDegreeFour.finrank_inducedReducedCoordinateRepresentation]
  have hdd : finrank ℂ (V d : Type) = 3 := by
    rw [← (FDRep.isoToLinearEquiv ed).finrank_eq, _root_.RepresentationTheory.PermutationDegreeFour.finrank_reducedCoordinateRepresentation]
  have hdf : finrank ℂ (V f : Type) = 3 := by
    rw [← (FDRep.isoToLinearEquiv ef).finrank_eq, _root_.RepresentationTheory.PermutationDegreeFour.finrank_signTwistedReducedCoordinateRepresentation]
  -- a, b, c, d, f are pairwise distinct
  have hab : a ≠ b := by rintro rfl; exact auxiliary_constant_target_not_iso_sign_target ⟨ea ≪≫ eb.symm⟩
  have hac : a ≠ c := by rintro rfl; exact auxiliary_constant_target_not_iso_second_statistic ⟨ea ≪≫ ec.symm⟩
  have had : a ≠ d := by rintro rfl; exact auxiliary_constant_target_not_iso_statistic ⟨ea ≪≫ ed.symm⟩
  have haf : a ≠ f := by rintro rfl; exact auxiliary_constant_target_not_iso_signed_statistic ⟨ea ≪≫ ef.symm⟩
  have hbc : b ≠ c := by rintro rfl; exact auxiliary_sign_target_not_iso_second_statistic ⟨eb ≪≫ ec.symm⟩
  have hbd : b ≠ d := by rintro rfl; exact auxiliary_sign_target_not_iso_statistic ⟨eb ≪≫ ed.symm⟩
  have hbf : b ≠ f := by rintro rfl; exact auxiliary_sign_target_not_iso_signed_statistic ⟨eb ≪≫ ef.symm⟩
  have hcd : c ≠ d := by rintro rfl; exact auxiliary_second_statistic_not_iso_statistic ⟨ec ≪≫ ed.symm⟩
  have hcf : c ≠ f := by rintro rfl; exact auxiliary_second_statistic_not_iso_signed_statistic ⟨ec ≪≫ ef.symm⟩
  have hdf' : d ≠ f := by rintro rfl; exact auxiliary_statistic_not_iso_signed_statistic ⟨ed ≪≫ ef.symm⟩
  -- s is one of a, b, c, d, f
  have hs : s = a ∨ s = b ∨ s = c ∨ s = d ∨ s = f := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hsa, hsb, hsc, hsd, hsf⟩ := hcon
    -- {a,b,c,d,f,s} are six distinct indices; their squared dims sum to ≥ 25 > 24
    have hsub : ({a, b, c, d, f, s} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have hpos : 0 < finrank ℂ (V s : Type) := by
      haveI := hsimple s
      exact RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_pos_of_not_isZero (Simple.not_isZero (V s))
    have hle : ∑ i ∈ ({a, b, c, d, f, s} : Finset (Fin n)), finrank ℂ (V i : Type) ^ 2 ≤
        ∑ i, finrank ℂ (V i : Type) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
    have hcard : ∑ i ∈ ({a, b, c, d, f, s} : Finset (Fin n)), finrank ℂ (V i : Type) ^ 2 =
        finrank ℂ (V a : Type) ^ 2 + finrank ℂ (V b : Type) ^ 2 + finrank ℂ (V c : Type) ^ 2 +
          finrank ℂ (V d : Type) ^ 2 + finrank ℂ (V f : Type) ^ 2 + finrank ℂ (V s : Type) ^ 2 := by
      rw [Finset.sum_insert (by simp [hab, hac, had, haf, hsa.symm]),
        Finset.sum_insert (by simp [hbc, hbd, hbf, hsb.symm]),
        Finset.sum_insert (by simp [hcd, hcf, hsc.symm]),
        Finset.sum_insert (by simp [hdf', hsd.symm]),
        Finset.sum_insert (by simp [hsf.symm]), Finset.sum_singleton]
      ring
    have hcard24 : Fintype.card _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType = 24 := by decide
    rw [hsum, hcard24] at hle
    rw [hcard, hda, hdb, hdc, hdd, hdf] at hle
    -- 1 + 1 + 4 + 9 + 9 + (≥1) ≤ 24 is impossible
    have hsq : 1 ≤ finrank ℂ (V s : Type) ^ 2 := Nat.one_le_pow 2 _ hpos
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨es ≪≫ ea.symm⟩
  · exact Or.inr (Or.inl ⟨es ≪≫ eb.symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨es ≪≫ ec.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨es ≪≫ ed.symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨es ≪≫ ef.symm⟩)))

/-! ### Group-generic Frobenius reciprocity at the dimension level -/

section GenericFrobenius

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
/-- The character of a restricted representation at a subgroup element equals the original character at its underlying group element. -/
lemma character_restriction_apply (H : Subgroup G) (S : FDRep ℂ G) (h : ↥H) :
    FDRep.character ((Action.res (FGModuleCat ℂ) H.subtype).obj S) h = S.character (h : G) := rfl

/-- The dimension of morphisms from an induced representation equals the dimension of morphisms into the restriction. -/
theorem finrank_hom_induced_eq_finrank_hom_restricted (H : Subgroup G) {V : Type}
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ ↥H V) (S : FDRep ℂ G) :
    finrank ℂ (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ) ⟶ S)
      = finrank ℂ (FDRep.of ρ ⟶ (Action.res (FGModuleCat ℂ) H.subtype).obj S) := by
  rw [← (FDRep.forget₂HomLinearEquiv (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ)) S).finrank_eq]
  have hG : (forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ))
      = Rep.ind H.subtype (Rep.of ρ) := rfl
  rw [hG, (Rep.indResHomEquiv H.subtype (Rep.of ρ)
      ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj S)).finrank_eq]
  have hWρ : Rep.of ρ = (forget₂ (FDRep ℂ ↥H) (Rep ℂ ↥H)).obj (FDRep.of ρ) := rfl
  have hRes : (Rep.resFunctor H.subtype).obj ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj S)
      = (forget₂ (FDRep ℂ ↥H) (Rep ℂ ↥H)).obj
          ((Action.res (FGModuleCat ℂ) H.subtype).obj S) := rfl
  have key : finrank ℂ (FDRep.of ρ ⟶ (Action.res (FGModuleCat ℂ) H.subtype).obj S)
      = finrank ℂ (Rep.of ρ ⟶ (Rep.resFunctor H.subtype).obj
          ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj S)) := by
    rw [← (FDRep.forget₂HomLinearEquiv (FDRep.of ρ)
      ((Action.res (FGModuleCat ℂ) H.subtype).obj S)).finrank_eq, ← hWρ, ← hRes]
  rw [key]

/-- The dimension of morphisms into an induced representation is the normalized sum of the target character times the inducing character on inverses. -/
lemma finrank_hom_induced_eq_character_average (H : Subgroup G) [Fintype ↥H] [Invertible (Fintype.card ↥H : ℂ)]
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ ↥H V) (S : FDRep ℂ G) :
    (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ)) : ℂ)
      = ⅟(Fintype.card ↥H : ℂ) • ∑ h : ↥H, S.character (h : G) * (FDRep.of ρ).character h⁻¹ := by
  rw [RepresentationTheory.AuxiliaryRepresentationComputations.finrank_hom_comm, finrank_hom_induced_eq_finrank_hom_restricted,
    ← RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_finrank_hom
      ((Action.res (FGModuleCat ℂ) H.subtype).obj S) (FDRep.of ρ)]
  simp only [character_restriction_apply]

omit [Finite G] in
/-- The character of a representation precomposed with a monoid homomorphism is obtained by evaluating the original character after that homomorphism. -/
lemma character_comp_monoidHom {K : Type} [Group K] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (τ : Representation ℂ K V) (π : G →* K) (g : G) :
    (FDRep.of (τ.comp π)).character g = (FDRep.of τ).character (π g) := by
  change LinearMap.trace ℂ V ((FDRep.of (τ.comp π)).ρ g)
    = LinearMap.trace ℂ V ((FDRep.of τ).ρ (π g))
  rw [FDRep.of_ρ', FDRep.of_ρ']
  rfl

end GenericFrobenius

/-! ### An auxiliary point-stabilizer subgroup -/

/-- The three-element finite type is equivalent to the subtype of elements unequal to three. -/
def finThreeEquivSubtypeNeThree : Fin 3 ≃ {x : Fin 4 // x ≠ 3} where
  toFun i := ⟨i.castSucc, by fin_cases i <;> decide⟩
  invFun x := if h : (x : Fin 4).val < 3 then ⟨(x : Fin 4).val, h⟩ else 0
  left_inv := by decide
  right_inv := by decide

/-- An auxiliary monoid homomorphism from permutations of three elements to the specified group. -/
def auxiliary_monoidHom : Equiv.Perm (Fin 3) →* _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType := Equiv.Perm.extendDomainHom finThreeEquivSubtypeNeThree

/-- The auxiliary monoid homomorphism is injective. -/
lemma auxiliary_monoidHom_injective : Function.Injective auxiliary_monoidHom := Equiv.Perm.extendDomainHom_injective finThreeEquivSubtypeNeThree

/-- The auxiliary monoid homomorphism preserves permutation sign. -/
@[simp] lemma sign_auxiliary_monoidHom_apply (σ : Equiv.Perm (Fin 3)) :
    Equiv.Perm.sign (auxiliary_monoidHom σ) = Equiv.Perm.sign σ :=
  Equiv.Perm.sign_extendDomain σ finThreeEquivSubtypeNeThree

/-- An auxiliary subgroup of the specified group. -/
def auxiliary_subgroup : Subgroup _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType := auxiliary_monoidHom.range

/-- The auxiliary subgroup carries a finite type structure. -/
noncomputable instance auxiliary_subgroup_fintype : Fintype ↥auxiliary_subgroup := Fintype.ofFinite _

/-- Permutations of three elements are multiplicatively equivalent to the auxiliary subgroup. -/
noncomputable def auxiliary_subgroup_mulEquiv : Equiv.Perm (Fin 3) ≃* ↥auxiliary_subgroup := MonoidHom.ofInjective auxiliary_monoidHom_injective

/-- The underlying group element of the auxiliary multiplicative equivalence agrees with the auxiliary monoid homomorphism. -/
@[simp] lemma coe_auxiliary_mulEquiv_eq_auxiliary_monoidHom (σ : Equiv.Perm (Fin 3)) : ((auxiliary_subgroup_mulEquiv σ : ↥auxiliary_subgroup) : _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType) = auxiliary_monoidHom σ :=
  MonoidHom.ofInjective_apply auxiliary_monoidHom_injective

/-- The auxiliary subgroup has six elements. -/
lemma card_auxiliary_subgroup : Fintype.card ↥auxiliary_subgroup = 6 := by
  rw [← Fintype.card_congr auxiliary_subgroup_mulEquiv.toEquiv]; decide

/-- The scalar cast of the cardinality of the auxiliary subgroup is invertible. -/
noncomputable instance invertible_card_auxiliary_subgroup : Invertible (Fintype.card ↥auxiliary_subgroup : ℂ) :=
  invertibleOfNonzero (by rw [card_auxiliary_subgroup]; norm_num)

/-- A sum over the auxiliary subgroup equals the corresponding sum over permutations of three elements through the auxiliary equivalence. -/
lemma sum_auxiliary_subgroup_eq_sum_perm_three (f : ↥auxiliary_subgroup → ℂ) :
    ∑ h : ↥auxiliary_subgroup, f h = ∑ σ : Equiv.Perm (Fin 3), f (auxiliary_subgroup_mulEquiv σ) :=
  (Equiv.sum_comp auxiliary_subgroup_mulEquiv.toEquiv f).symm

/-! ### The three inducing representations of `auxiliary_subgroup` -/

/-- An auxiliary one-dimensional complex representation of the auxiliary subgroup. -/
noncomputable def auxiliary_trivial_representation : Representation ℂ ↥auxiliary_subgroup ℂ := _root_.RepresentationTheory.PermutationDegreeFour.representationOfUnitCharacter (1 : ↥auxiliary_subgroup →* ℂˣ)

/-- An auxiliary one-dimensional complex representation of the auxiliary subgroup. -/
noncomputable def auxiliary_sign_representation : Representation ℂ ↥auxiliary_subgroup ℂ := _root_.RepresentationTheory.PermutationDegreeFour.representationOfUnitCharacter (_root_.RepresentationTheory.PermutationDegreeFour.signCharacter.comp auxiliary_subgroup.subtype)

/-- An auxiliary complex representation on the specified invariant subspace. -/
noncomputable def auxiliary_subrepresentation : Representation ℂ ↥auxiliary_subgroup ↥(RepresentationTheory.AuxiliaryRepresentationComputations.auxiliarySubrepresentation.toSubmodule) :=
  (RepresentationTheory.AuxiliaryRepresentationComputations.auxiliarySubrepresentation.toRepresentation).comp (auxiliary_subgroup_mulEquiv.symm : ↥auxiliary_subgroup →* Equiv.Perm (Fin 3))

/-- The character of the auxiliary one-dimensional representation is constantly one. -/
lemma character_auxiliary_trivial_representation (h : ↥auxiliary_subgroup) : (FDRep.of auxiliary_trivial_representation).character h = 1 := by
  rw [auxiliary_trivial_representation, _root_.RepresentationTheory.PermutationDegreeFour.character_representationOfUnitCharacter]; simp

/-- The character of the auxiliary one-dimensional representation is the integer cast of the permutation sign. -/
lemma character_auxiliary_sign_representation (h : ↥auxiliary_subgroup) :
    (FDRep.of auxiliary_sign_representation).character h = ((Equiv.Perm.sign (h : _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType) : ℤ) : ℂ) := by
  rw [auxiliary_sign_representation, _root_.RepresentationTheory.PermutationDegreeFour.character_representationOfUnitCharacter]
  simp [MonoidHom.comp_apply, _root_.RepresentationTheory.PermutationDegreeFour.coe_signCharacter]

/-- The character of the auxiliary subrepresentation agrees with the specified character after transport along the auxiliary equivalence. -/
lemma character_auxiliary_subrepresentation (h : ↥auxiliary_subgroup) :
    (FDRep.of auxiliary_subrepresentation).character h = RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryRepresentationTwo.character (auxiliary_subgroup_mulEquiv.symm h) := by
  rw [auxiliary_subrepresentation, character_comp_monoidHom]
  rfl

/-! ### The three induced multiplicity formulas -/

/-- The dimension of morphisms into the induced auxiliary trivial representation is the normalized character sum over permutations of three elements. -/
lemma finrank_hom_induced_auxiliary_trivial_eq_character_sum (S : FDRep ℂ _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType) :
    (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_trivial_representation)) : ℂ)
      = ⅟(Fintype.card ↥auxiliary_subgroup : ℂ) • ∑ σ : Equiv.Perm (Fin 3), S.character (auxiliary_monoidHom σ) := by
  rw [finrank_hom_induced_eq_character_average, sum_auxiliary_subgroup_eq_sum_perm_three]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coe_auxiliary_mulEquiv_eq_auxiliary_monoidHom, character_auxiliary_trivial_representation, mul_one]

/-- The dimension of morphisms into the induced auxiliary sign representation is the normalized sign-weighted character sum over permutations of three elements. -/
lemma finrank_hom_induced_auxiliary_sign_eq_character_sum (S : FDRep ℂ _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType) :
    (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_sign_representation)) : ℂ)
      = ⅟(Fintype.card ↥auxiliary_subgroup : ℂ) • ∑ σ : Equiv.Perm (Fin 3),
          S.character (auxiliary_monoidHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
  rw [finrank_hom_induced_eq_character_average, sum_auxiliary_subgroup_eq_sum_perm_three]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [character_auxiliary_sign_representation]
  simp only [coe_auxiliary_mulEquiv_eq_auxiliary_monoidHom, Subgroup.coe_inv, Equiv.Perm.sign_inv, sign_auxiliary_monoidHom_apply]

/-- The dimension of morphisms into the induced auxiliary subrepresentation is the normalized character sum weighted by one less than the displayed auxiliary statistic. -/
lemma finrank_hom_induced_auxiliary_subrepresentation_eq_character_sum (S : FDRep ℂ _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType) :
    (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_subrepresentation)) : ℂ)
      = ⅟(Fintype.card ↥auxiliary_subgroup : ℂ) • ∑ σ : Equiv.Perm (Fin 3),
          S.character (auxiliary_monoidHom σ) * ((RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue σ : ℂ) - 1) := by
  rw [finrank_hom_induced_eq_character_average, sum_auxiliary_subgroup_eq_sum_perm_three]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coe_auxiliary_mulEquiv_eq_auxiliary_monoidHom, character_auxiliary_subrepresentation, map_inv, auxiliary_subgroup_mulEquiv.symm_apply_apply,
    RepresentationTheory.AuxiliaryRepresentationComputations.character_auxiliaryRepresentationTwo, RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue_inv]

/-! ### Character closed forms along the embedding, and the sum transport -/

/-- The character of the auxiliary constant-target representation is one on the image of the auxiliary homomorphism. -/
lemma character_auxiliary_constant_target_representation (σ : Equiv.Perm (Fin 3)) : _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo.character (auxiliary_monoidHom σ) = 1 := by
  rw [_root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo, _root_.RepresentationTheory.PermutationDegreeFour.character_representationOfUnitCharacter]; simp

/-- The character of the auxiliary sign-target representation is the integer cast of the permutation sign. -/
lemma character_auxiliary_sign_target_representation (σ : Equiv.Perm (Fin 3)) :
    _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne.character (auxiliary_monoidHom σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
  rw [_root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne, _root_.RepresentationTheory.PermutationDegreeFour.character_representationOfUnitCharacter, _root_.RepresentationTheory.PermutationDegreeFour.coe_signCharacter, sign_auxiliary_monoidHom_apply]

/-- The character of the auxiliary statistic representation is the displayed auxiliary statistic minus one. -/
lemma character_auxiliary_statistic_representation (σ : Equiv.Perm (Fin 3)) :
    _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation.character (auxiliary_monoidHom σ) = (_root_.RepresentationTheory.PermutationDegreeFour.fixedPointCount (auxiliary_monoidHom σ) : ℂ) - 1 :=
  _root_.RepresentationTheory.PermutationDegreeFour.character_reducedCoordinateRepresentation (auxiliary_monoidHom σ)

/-- The character of the auxiliary signed-statistic representation is the permutation sign multiplied by one less than the displayed auxiliary statistic. -/
lemma character_auxiliary_signed_statistic_representation (σ : Equiv.Perm (Fin 3)) :
    _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation.character (auxiliary_monoidHom σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((_root_.RepresentationTheory.PermutationDegreeFour.fixedPointCount (auxiliary_monoidHom σ) : ℂ) - 1) := by
  rw [_root_.RepresentationTheory.PermutationDegreeFour.character_signTwistedReducedCoordinateRepresentation, sign_auxiliary_monoidHom_apply]

/-- The character of the auxiliary second-statistic representation is the displayed auxiliary statistic minus one. -/
lemma character_auxiliary_second_statistic_representation (σ : Equiv.Perm (Fin 3)) :
    _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation.character (auxiliary_monoidHom σ) = (_root_.RepresentationTheory.PermutationDegreeFour.inducedFixedPointCount (auxiliary_monoidHom σ) : ℂ) - 1 :=
  _root_.RepresentationTheory.PermutationDegreeFour.character_inducedReducedCoordinateRepresentation (auxiliary_monoidHom σ)

/-- A finite sum of complex values that are pointwise integer casts is the cast of the corresponding integer sum. -/
lemma sum_eq_intCast_of_pointwise_eq_intCast (F : Equiv.Perm (Fin 3) → ℂ) (g : Equiv.Perm (Fin 3) → ℤ) (N : ℤ)
    (hF : ∀ σ, F σ = (g σ : ℂ)) (hN : (∑ σ, g σ) = N) :
    (∑ σ : Equiv.Perm (Fin 3), F σ) = (N : ℂ) := by
  rw [Finset.sum_congr rfl fun σ _ => hF σ, ← Int.cast_sum, hN]

/-! ## Three induced-representation decompositions -/

/-- The representation induced from the auxiliary trivial representation is isomorphic to the displayed biproduct. -/
@[source_ref "Chapter5/Introduction_5.11" (role := supporting),
  source_ref "Chapter5/Discussion_5.11_examples" (role := supporting),
  source_ref "Chapter5/Discussion_5.11_examples/Derived01" (role := supporting)]
theorem induced_auxiliary_trivial_iso_biprod :
    Nonempty (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_trivial_representation) ≅ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation) := by
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_finrank_eq_of_finrank_hom_simple_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  rcases simple_iso_auxiliary_cases S with h | h | h | h | h
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo : 1 = 1 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_trivial_representation)) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliary_trivial_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo.character (auxiliary_monoidHom σ)) (fun _ => 1) 6
          (fun σ => by rw [character_auxiliary_constant_target_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation, if_pos ⟨e⟩,
        if_neg (fun hh => auxiliary_constant_target_not_iso_statistic ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_trivial_representation)) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliary_trivial_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne.character (auxiliary_monoidHom σ)) (fun σ => (Equiv.Perm.sign σ : ℤ)) 0
          (fun σ => by rw [character_auxiliary_sign_target_representation σ]) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation) = 0 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_constant_target_not_iso_sign_target ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => auxiliary_sign_target_not_iso_statistic ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_trivial_representation)) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliary_trivial_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation.character (auxiliary_monoidHom σ)) (fun σ => (_root_.RepresentationTheory.PermutationDegreeFour.inducedFixedPointCount (auxiliary_monoidHom σ) : ℤ) - 1) 0
          (fun σ => by rw [character_auxiliary_second_statistic_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation) = 0 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_constant_target_not_iso_second_statistic ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => auxiliary_second_statistic_not_iso_statistic ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation : 1 = 0 + 1
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_trivial_representation)) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliary_trivial_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation.character (auxiliary_monoidHom σ)) (fun σ => (_root_.RepresentationTheory.PermutationDegreeFour.fixedPointCount (auxiliary_monoidHom σ) : ℤ) - 1) 6
          (fun σ => by rw [character_auxiliary_statistic_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_constant_target_not_iso_statistic ⟨hh.some.symm ≪≫ e⟩), if_pos ⟨e⟩]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_trivial_representation)) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliary_trivial_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation.character (auxiliary_monoidHom σ))
          (fun σ => (Equiv.Perm.sign σ : ℤ) * ((_root_.RepresentationTheory.PermutationDegreeFour.fixedPointCount (auxiliary_monoidHom σ) : ℤ) - 1)) 0
          (fun σ => by rw [character_auxiliary_signed_statistic_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation) = 0 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_constant_target_not_iso_signed_statistic ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => auxiliary_statistic_not_iso_signed_statistic ⟨hh.some.symm ≪≫ e⟩)]
    rw [hR]; exact_mod_cast hL

/-- The representation induced from the auxiliary sign representation is isomorphic to the displayed biproduct. -/
@[source_ref "Chapter5/Discussion_5.11_examples" (role := supporting),
  source_ref "Chapter5/Discussion_5.11_examples/Derived01" (role := supporting)]
theorem induced_auxiliary_sign_iso_biprod :
    Nonempty (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_sign_representation) ≅ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) := by
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_finrank_eq_of_finrank_hom_simple_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  rcases simple_iso_auxiliary_cases S with h | h | h | h | h
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_sign_representation)) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliary_sign_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo.character (auxiliary_monoidHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ))
          (fun σ => (Equiv.Perm.sign σ : ℤ)) 0
          (fun σ => by rw [character_auxiliary_constant_target_representation σ]; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) = 0 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_constant_target_not_iso_sign_target ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => auxiliary_constant_target_not_iso_signed_statistic ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne : 1 = 1 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_sign_representation)) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliary_sign_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne.character (auxiliary_monoidHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ))
          (fun σ => (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ)) 6
          (fun σ => by rw [character_auxiliary_sign_target_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation, if_pos ⟨e⟩,
        if_neg (fun hh => auxiliary_sign_target_not_iso_signed_statistic ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_sign_representation)) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliary_sign_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation.character (auxiliary_monoidHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ))
          (fun σ => ((_root_.RepresentationTheory.PermutationDegreeFour.inducedFixedPointCount (auxiliary_monoidHom σ) : ℤ) - 1) * (Equiv.Perm.sign σ : ℤ)) 0
          (fun σ => by rw [character_auxiliary_second_statistic_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) = 0 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_sign_target_not_iso_second_statistic ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => auxiliary_second_statistic_not_iso_signed_statistic ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_sign_representation)) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliary_sign_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation.character (auxiliary_monoidHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ))
          (fun σ => ((_root_.RepresentationTheory.PermutationDegreeFour.fixedPointCount (auxiliary_monoidHom σ) : ℤ) - 1) * (Equiv.Perm.sign σ : ℤ)) 0
          (fun σ => by rw [character_auxiliary_statistic_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) = 0 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_sign_target_not_iso_statistic ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => auxiliary_statistic_not_iso_signed_statistic ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation : 1 = 0 + 1
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_sign_representation)) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliary_sign_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation.character (auxiliary_monoidHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ))
          (fun σ => ((Equiv.Perm.sign σ : ℤ) * ((_root_.RepresentationTheory.PermutationDegreeFour.fixedPointCount (auxiliary_monoidHom σ) : ℤ) - 1)) *
            (Equiv.Perm.sign σ : ℤ)) 6
          (fun σ => by rw [character_auxiliary_signed_statistic_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_sign_target_not_iso_signed_statistic ⟨hh.some.symm ≪≫ e⟩), if_pos ⟨e⟩]
    rw [hR]; exact_mod_cast hL

/-- The representation induced from the auxiliary subrepresentation is isomorphic to the displayed iterated biproduct. -/
@[source_ref "Chapter5/Discussion_5.11_examples" (role := supporting),
  source_ref "Chapter5/Discussion_5.11_examples/Derived01" (role := supporting)]
theorem induced_auxiliary_subrepresentation_iso_biprod :
    Nonempty
      (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_subrepresentation) ≅ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) := by
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_finrank_eq_of_finrank_hom_simple_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  rcases simple_iso_auxiliary_cases S with h | h | h | h | h
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo : 0 = 0 + 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_subrepresentation)) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliary_subrepresentation_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationTwo.character (auxiliary_monoidHom σ) *
            ((RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue σ : ℂ) - 1))
          (fun σ => (RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue σ : ℤ) - 1) 0
          (fun σ => by rw [character_auxiliary_constant_target_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) = 0 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_constant_target_not_iso_second_statistic ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => auxiliary_constant_target_not_iso_statistic ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => auxiliary_constant_target_not_iso_signed_statistic ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne : 0 = 0 + 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_subrepresentation)) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliary_subrepresentation_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryRepresentationOne.character (auxiliary_monoidHom σ) *
            ((RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue σ : ℂ) - 1))
          (fun σ => (Equiv.Perm.sign σ : ℤ) * ((RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue σ : ℤ) - 1)) 0
          (fun σ => by rw [character_auxiliary_sign_target_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) = 0 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_sign_target_not_iso_second_statistic ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => auxiliary_sign_target_not_iso_statistic ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => auxiliary_sign_target_not_iso_signed_statistic ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation : 1 = 1 + 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_subrepresentation)) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliary_subrepresentation_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation.character (auxiliary_monoidHom σ) *
            ((RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue σ : ℂ) - 1))
          (fun σ => ((_root_.RepresentationTheory.PermutationDegreeFour.inducedFixedPointCount (auxiliary_monoidHom σ) : ℤ) - 1) *
            ((RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue σ : ℤ) - 1)) 6
          (fun σ => by rw [character_auxiliary_second_statistic_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation,
        if_pos ⟨e⟩,
        if_neg (fun hh => auxiliary_second_statistic_not_iso_statistic ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => auxiliary_second_statistic_not_iso_signed_statistic ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation : 1 = 0 + 1 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_subrepresentation)) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliary_subrepresentation_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation.character (auxiliary_monoidHom σ) *
            ((RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue σ : ℂ) - 1))
          (fun σ => ((_root_.RepresentationTheory.PermutationDegreeFour.fixedPointCount (auxiliary_monoidHom σ) : ℤ) - 1) *
            ((RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue σ : ℤ) - 1)) 6
          (fun σ => by rw [character_auxiliary_statistic_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_second_statistic_not_iso_statistic ⟨hh.some.symm ≪≫ e⟩), if_pos ⟨e⟩,
        if_neg (fun hh => auxiliary_statistic_not_iso_signed_statistic ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation : 1 = 0 + 0 + 1
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliary_subgroup auxiliary_subrepresentation)) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliary_subrepresentation_eq_character_sum S, hc,
        sum_eq_intCast_of_pointwise_eq_intCast (fun σ => _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation.character (auxiliary_monoidHom σ) *
            ((RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue σ : ℂ) - 1))
          (fun σ => ((Equiv.Perm.sign σ : ℤ) * ((_root_.RepresentationTheory.PermutationDegreeFour.fixedPointCount (auxiliary_monoidHom σ) : ℤ) - 1)) *
            ((RepresentationTheory.AuxiliaryRepresentationComputations.auxiliaryNatValue σ : ℤ) - 1)) 6
          (fun σ => by rw [character_auxiliary_signed_statistic_representation σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, card_auxiliary_subgroup, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation ⊞ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation,
        FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation, FDRep.finrank_hom_simple_simple S _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation,
        if_neg (fun hh => auxiliary_second_statistic_not_iso_signed_statistic ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => auxiliary_statistic_not_iso_signed_statistic ⟨hh.some.symm ≪≫ e⟩), if_pos ⟨e⟩]
    rw [hR]; exact_mod_cast hL

end RepresentationTheory.FiniteGroupRepresentations.SubgroupInductionAuxiliary
