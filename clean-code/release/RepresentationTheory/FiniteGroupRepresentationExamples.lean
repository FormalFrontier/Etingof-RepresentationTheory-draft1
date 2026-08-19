/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteGroupRepresentations.Auxiliary
import RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar
import RepresentationTheory.Representation.Character.InversionAndInvariantForms
import RepresentationTheory.Representation.Character.AuxiliaryVanishing
import RepresentationTheory.SimpleModule.SubtypeRepresentation
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.FDRep.Auxiliary
import RepresentationTheory.ComplexUnitCharacters
import RepresentationTheory.OddOrder.CharacterSums
import RepresentationTheory.Group.SimpleRepresentations
import RepresentationTheory.Alignment.Attribute





namespace RepresentationTheory.FiniteGroupRepresentationExamples

/-- A function coercion that evaluates a monoid-algebra element at a coefficient index. -/
local instance monoidAlgebraCoeFunToCoeff {R M : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R M) (fun _ => M → R) :=
  ⟨fun a => a.coeff⟩

/-- An auxiliary theorem. -/
theorem auxiliaryTheoremH
    {G : Type*} [Group G] [Fintype G]
    (ρ : Representation ℂ G ℂ)
    (h : ∃ g : G, ρ g 1 ≠ 1 ∧ ρ g 1 ≠ -1) :
    ¬ RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by



  rintro ⟨B, _hsym, hnondeg, hinv⟩
  obtain ⟨g, hg1, hg2⟩ := h
  set χ : ℂ := ρ g 1 with hχ

  have key : ∀ a b : ℂ, B a b = a * b * B 1 1 := by
    intro a b
    have step : (B a) b = a • (b • B 1 1) := by
      have h1 : (B a) b = (B (a • (1:ℂ))) (b • (1:ℂ)) := by simp
      rw [h1, show B (a • (1:ℂ)) = a • B 1 from map_smul B a 1,
        LinearMap.smul_apply, show (B 1) (b • (1:ℂ)) = b • (B 1) 1 from map_smul (B 1) b 1]
    rw [step, smul_eq_mul, smul_eq_mul, mul_assoc]

  have hc : B 1 1 ≠ 0 := by
    intro hc0
    have : (1 : ℂ) = 0 := hnondeg 1 (fun w => by rw [key, hc0, mul_zero])
    exact one_ne_zero this

  have hinvg : χ * χ * B 1 1 = B 1 1 := by
    have := hinv g 1 1
    rw [← hχ, key] at this
    exact this

  have hχχ : χ * χ = 1 := by
    have : χ * χ * B 1 1 = 1 * B 1 1 := by rw [one_mul]; exact hinvg
    exact mul_right_cancel₀ hc this
  rcases mul_self_eq_one_iff.mp hχχ with h1 | h1
  · exact hg1 h1
  · exact hg2 h1

/-- An auxiliary theorem. -/
theorem auxiliaryTheoremB
    {n : ℕ} [NeZero n]
    (ρ : Representation ℂ (Multiplicative (ZMod n)) ℂ)
    (h : ∃ g : Multiplicative (ZMod n), ρ g 1 ≠ 1 ∧ ρ g 1 ≠ -1) :
    ¬ RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ :=
  auxiliaryTheoremH ρ h

section ZModTypeClassification

/-- Every complex representation on the complex numbers is simple as a module over the group algebra. -/
theorem isSimpleModule_representationOnComplex
    {G : Type*} [Group G]
    (ρ : Representation ℂ G ℂ) :
    IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule := by
  suffices hSO : IsSimpleOrder ρ.invtSubmodule by
    haveI := (Representation.mapSubmodule ρ).isSimpleOrder_iff.mp hSO
    exact ⟨⟩
  refine { eq_bot_or_eq_top := fun a => ?_ }
  rcases IsSimpleOrder.eq_bot_or_eq_top (a : Submodule ℂ ℂ) with h | h
  · exact Or.inl (Subtype.ext (by rw [Representation.invtSubmodule.coe_bot]; exact h))
  · exact Or.inr (Subtype.ext (by rw [Representation.invtSubmodule.coe_top]; exact h))

/-- An auxiliary theorem. -/
theorem auxiliaryTheoremG
    {G : Type*} [Group G] [Fintype G]
    (ρ : Representation ℂ G ℂ)
    (h : ∀ g : G, ρ g 1 = 1 ∨ ρ g 1 = -1) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by

  have hlin : ∀ (g : G) (a : ℂ), ρ g a = a * ρ g 1 := by
    intro g a
    have := (ρ g).map_smul a (1 : ℂ)
    simpa using this
  refine ⟨LinearMap.mul ℂ ℂ, ?_, ?_, ?_⟩
  ·
    intro v w; rw [LinearMap.mul_apply', LinearMap.mul_apply', mul_comm]
  ·
    intro v hv
    have := hv 1
    rwa [LinearMap.mul_apply', mul_one] at this
  ·
    intro g v w
    rw [LinearMap.mul_apply', LinearMap.mul_apply', hlin g v, hlin g w]
    rcases h g with hg | hg <;> rw [hg] <;> ring

/-- An auxiliary theorem. -/
theorem auxiliaryTheoremF
    {G : Type} [Group G] [Fintype G]
    (ρ : Representation ℂ G ℂ)
    (h : ∃ g : G, ρ g 1 ≠ 1 ∧ ρ g 1 ≠ -1) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationProperty ρ := by
  classical
  intro hsd
  have hsimple := isSimpleModule_representationOnComplex ρ
  rcases RepresentationTheory.OddOrder.CharacterSums.auxiliary_of_simple_of_dual_intertwiner ρ hsimple hsd with hr | hq
  · exact auxiliaryTheoremH ρ h hr
  · have heven := RepresentationTheory.Representation.Character.InversionAndInvariantForms.even_finrank_of_auxiliary ρ hq
    rw [Module.finrank_self] at heven
    exact (Nat.not_even_one) heven

/-- A simple complex representation of a finite cyclic group of positive order is isomorphic to one of the auxiliary representations. -/
@[source_ref "Chapter5/Example5.1.3" (role := supporting)]
theorem simpleFiniteCyclicRepresentationIsoAuxiliary
    {n : ℕ} [NeZero n] (S : FDRep ℂ (Multiplicative (ZMod n)))
    [CategoryTheory.Simple S] :
    ∃ ξ : Multiplicative (ZMod n) →* ℂˣ,
      Nonempty (S ≅ RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ) :=
  RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter S

/-- The value constructed from the trivial character of a positive-order finite cyclic group satisfies the auxiliary condition. -/
theorem auxiliaryPropertyForTrivialCyclicCharacter {n : ℕ} [NeZero n] :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo (RepresentationTheory.ComplexUnitCharacters.representationOfComplexUnitCharacter (1 : Multiplicative (ZMod n) →* ℂˣ)) := by
  apply auxiliaryTheoremG
  intro g
  left
  change ((((1 : Multiplicative (ZMod n) →* ℂˣ) g : ℂˣ) : ℂ) • LinearMap.id) (1 : ℂ) = 1
  simp


private lemma pow_eq_pow_mod_two_of_sq_eq_one {M : Type*} [Monoid M] {u : M}
    (hu : u ^ 2 = 1) (a : ℕ) : u ^ a = u ^ (a % 2) := by
  conv_lhs => rw [← Nat.div_add_mod a 2]
  rw [pow_add, pow_mul, hu, one_pow, one_mul]

/-- A complex-valued multiplicative character attached to a finite cyclic group of even order. -/
def cyclicCharacterOfEvenOrder {n : ℕ} [NeZero n] (hn : 2 ∣ n) :
    Multiplicative (ZMod n) →* ℂˣ where
  toFun g := (-1 : ℂˣ) ^ (Multiplicative.toAdd g).val
  map_one' := by simp
  map_mul' a b := by
    change (-1 : ℂˣ) ^ (Multiplicative.toAdd (a * b)).val
        = (-1 : ℂˣ) ^ (Multiplicative.toAdd a).val * (-1 : ℂˣ) ^ (Multiplicative.toAdd b).val
    rw [← pow_add]
    have hsq : (-1 : ℂˣ) ^ 2 = 1 := by
      rw [pow_two]; ext; simp
    rw [pow_eq_pow_mod_two_of_sq_eq_one hsq,
      pow_eq_pow_mod_two_of_sq_eq_one hsq
        ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val)]
    congr 1
    change (Multiplicative.toAdd a + Multiplicative.toAdd b).val % 2
        = ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) % 2
    rw [ZMod.val_add]
    exact (Nat.mod_modEq _ n).of_dvd hn

/-- For an even order at least two, the associated cyclic character is nontrivial. -/
theorem cyclicCharacterOfEvenOrder_ne_one {n : ℕ} [NeZero n] (hn : 2 ∣ n) (hn2 : 2 ≤ n) :
    cyclicCharacterOfEvenOrder hn ≠ 1 := by
  intro hcontra
  haveI : Fact (1 < n) := ⟨by omega⟩
  have h1 : cyclicCharacterOfEvenOrder hn (Multiplicative.ofAdd (1 : ZMod n)) = 1 := by
    rw [hcontra]; rfl
  rw [show cyclicCharacterOfEvenOrder hn (Multiplicative.ofAdd (1 : ZMod n))
      = (-1 : ℂˣ) ^ (1 : ZMod n).val from rfl] at h1
  rw [ZMod.val_one, pow_one] at h1
  have hv := congrArg Units.val h1
  norm_num at hv

/-- The value constructed from the specified character for an even order satisfies the auxiliary condition. -/
theorem auxiliaryPropertyForEvenCyclicCharacter {n : ℕ} [NeZero n] (hn : 2 ∣ n) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo (RepresentationTheory.ComplexUnitCharacters.representationOfComplexUnitCharacter (cyclicCharacterOfEvenOrder hn)) := by
  apply auxiliaryTheoremG
  intro g
  have hval : (RepresentationTheory.ComplexUnitCharacters.representationOfComplexUnitCharacter (cyclicCharacterOfEvenOrder hn) g) (1 : ℂ)
      = ((-1 : ℂ)) ^ (Multiplicative.toAdd g).val := by
    change (((cyclicCharacterOfEvenOrder hn g : ℂˣ) : ℂ) • LinearMap.id) (1 : ℂ) = _
    change ((cyclicCharacterOfEvenOrder hn g : ℂˣ) : ℂ) * 1 = _
    rw [mul_one]
    change (((-1 : ℂˣ) ^ (Multiplicative.toAdd g).val : ℂˣ) : ℂ) = _
    push_cast
    ring
  rw [hval]
  rcases Nat.even_or_odd (Multiplicative.toAdd g).val with he | ho
  · left; rw [he.neg_one_pow]
  · right; rw [ho.neg_one_pow]



private theorem zmod_eq_generator_pow_val {n : ℕ} [NeZero n]
    (g : Multiplicative (ZMod n)) :
    g = Multiplicative.ofAdd (1 : ZMod n) ^ ZMod.val (Multiplicative.toAdd g) := by
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd g = ZMod.val (Multiplicative.toAdd g) • (1 : ZMod n)
  rw [nsmul_eq_mul, mul_one]
  exact (ZMod.natCast_rightInverse _).symm



private theorem zmodCharacter_ext {n : ℕ} [NeZero n]
    {ξ ψ : Multiplicative (ZMod n) →* ℂˣ}
    (h : ξ (Multiplicative.ofAdd (1 : ZMod n)) =
      ψ (Multiplicative.ofAdd (1 : ZMod n))) :
    ξ = ψ := by
  apply MonoidHom.ext
  intro g
  rw [zmod_eq_generator_pow_val g, map_pow, map_pow, h]

/-- An auxiliary theorem. -/
theorem auxiliaryTheoremD
    {n : ℕ} [NeZero n]
    (ξ : Multiplicative (ZMod n) →* ℂˣ)
    (h : ∀ g, ξ g = 1 ∨ ξ g = -1) :
    ξ = 1 ∨ ∃ hn : 2 ∣ n, ξ = cyclicCharacterOfEvenOrder hn := by
  let gen := Multiplicative.ofAdd (1 : ZMod n)
  rcases h gen with hgen | hgen
  · exact Or.inl (zmodCharacter_ext hgen)
  · right
    have hn : 2 ∣ n := by
      have hpow : gen ^ n = 1 := by
        apply Multiplicative.toAdd.injective
        change n • (1 : ZMod n) = 0
        rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
      have hneg : (-1 : ℂˣ) ^ n = 1 := by
        rw [← hgen, ← map_pow, hpow, map_one]
      apply even_iff_two_dvd.mp
      rcases Nat.even_or_odd n with hn | hn
      · exact hn
      · rw [hn.neg_one_pow] at hneg
        have := congrArg Units.val hneg
        norm_num at this
    refine ⟨hn, zmodCharacter_ext ?_⟩
    rw [hgen]
    symm
    have hn2 : 2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hn
    letI : Fact (1 < n) := ⟨by omega⟩
    change (-1 : ℂˣ) ^ (1 : ZMod n).val = -1
    rw [ZMod.val_one, pow_one]

/-- An auxiliary condition on the value constructed from a cyclic character holds exactly when the character is trivial or agrees with the specified character for some proof that two divides the order. -/
@[source_ref "Chapter5/Example5.1.3" (role := supporting)]
theorem auxiliaryCharacterCriterion_eq_one_or_eq_specifiedEvenOrder
    {n : ℕ} [NeZero n] (ξ : Multiplicative (ZMod n) →* ℂˣ) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo (RepresentationTheory.ComplexUnitCharacters.representationOfComplexUnitCharacter ξ) ↔
      ξ = 1 ∨ ∃ hn : 2 ∣ n, ξ = cyclicCharacterOfEvenOrder hn := by
  constructor
  · intro hreal
    apply auxiliaryTheoremD ξ
    intro g
    by_cases h1 : ξ g = 1
    · exact Or.inl h1
    by_cases hm1 : ξ g = -1
    · exact Or.inr hm1
    exfalso
    apply auxiliaryTheoremH
      (RepresentationTheory.ComplexUnitCharacters.representationOfComplexUnitCharacter ξ) ?_ hreal
    refine ⟨g, ?_, ?_⟩
    · rw [RepresentationTheory.ComplexUnitCharacters.representationOfComplexUnitCharacter_apply, mul_one]
      exact fun h => h1 (Units.ext h)
    · rw [RepresentationTheory.ComplexUnitCharacters.representationOfComplexUnitCharacter_apply, mul_one]
      exact fun h => hm1 (Units.ext h)
  · rintro (rfl | ⟨hn, rfl⟩)
    · exact auxiliaryPropertyForTrivialCyclicCharacter
    · exact auxiliaryPropertyForEvenCyclicCharacter hn

/-- An auxiliary condition on the value constructed from a cyclic character holds exactly when the character is nontrivial and differs from the specified character for every proof that two divides the order. -/
@[source_ref "Chapter5/Example5.1.3" (role := supporting)]
theorem auxiliaryCharacterCriterionForFiniteCyclicGroup
    {n : ℕ} [NeZero n] (ξ : Multiplicative (ZMod n) →* ℂˣ) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationProperty (RepresentationTheory.ComplexUnitCharacters.representationOfComplexUnitCharacter ξ) ↔
      ξ ≠ 1 ∧ ∀ hn : 2 ∣ n, ξ ≠ cyclicCharacterOfEvenOrder hn := by
  constructor
  · intro hcomplex
    constructor
    · intro hξ
      subst ξ
      exact RepresentationTheory.FiniteGroupRepresentations.Auxiliary.not_auxiliaryRepresentationProperty_of_conditionTwo
        auxiliaryPropertyForTrivialCyclicCharacter hcomplex
    · intro hn hξ
      subst ξ
      exact RepresentationTheory.FiniteGroupRepresentations.Auxiliary.not_auxiliaryRepresentationProperty_of_conditionTwo
        (auxiliaryPropertyForEvenCyclicCharacter hn) hcomplex
  · rintro ⟨hneOne, hneSign⟩
    apply auxiliaryTheoremF
    by_contra hnone
    push Not at hnone
    simp only [RepresentationTheory.ComplexUnitCharacters.representationOfComplexUnitCharacter_apply, mul_one] at hnone
    have hpm : ∀ g, ξ g = 1 ∨ ξ g = -1 := by
      intro g
      by_cases h1 : ξ g = 1
      · exact Or.inl h1
      · exact Or.inr (Units.ext (hnone g (fun h => h1 (Units.ext h))))
    rcases auxiliaryTheoremD ξ hpm with h | ⟨hn, h⟩
    · exact hneOne h
    · exact hneSign hn h

end ZModTypeClassification



open Module (finrank)

/-- An auxiliary permutation of three elements. -/
def auxiliaryPermutationA : Equiv.Perm (Fin 3) := finRotate 3
/-- A second auxiliary permutation of three elements. -/
def auxiliaryPermutationB : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The cube of the first auxiliary permutation is the identity. -/
theorem auxiliaryPermutationA_pow_three : auxiliaryPermutationA ^ 3 = 1 := by decide
/-- The square of the second auxiliary permutation is the identity. -/
theorem auxiliaryPermutationB_sq : auxiliaryPermutationB * auxiliaryPermutationB = 1 := by decide
/-- The product of the first auxiliary permutation with the second equals the second followed by two copies of the first. -/
theorem auxiliaryPermutationA_mul_auxiliaryPermutationB : auxiliaryPermutationA * auxiliaryPermutationB = auxiliaryPermutationB * auxiliaryPermutationA * auxiliaryPermutationA := by decide
/-- The square of the square of the first auxiliary permutation equals that permutation. -/
theorem auxiliaryPermutationA_sq_sq : auxiliaryPermutationA * auxiliaryPermutationA * (auxiliaryPermutationA * auxiliaryPermutationA) = auxiliaryPermutationA := by decide
/-- The first auxiliary permutation differs from its square. -/
theorem auxiliaryPermutationA_ne_sq : auxiliaryPermutationA ≠ auxiliaryPermutationA * auxiliaryPermutationA := by decide
/-- The square of the first auxiliary permutation equals the stated product involving the second permutation and its inverse. -/
theorem auxiliaryPermutationA_sq_relation : auxiliaryPermutationA * auxiliaryPermutationA = auxiliaryPermutationB * (auxiliaryPermutationA * auxiliaryPermutationB⁻¹) := by decide
/-- Multiplying the first auxiliary permutation by the inverse of the second and then by the second returns the first. -/
theorem auxiliaryPermutationA_mul_inv_mul : auxiliaryPermutationA * auxiliaryPermutationB⁻¹ * auxiliaryPermutationB = auxiliaryPermutationA := by decide

/-- The two auxiliary permutations generate the full symmetric group on three letters. -/
theorem auxiliaryPermutations_closure : Subgroup.closure ({auxiliaryPermutationA, auxiliaryPermutationB} : Set (Equiv.Perm (Fin 3))) = ⊤ := by
  apply Equiv.Perm.closure_prime_cycle_swap
  · rw [Fintype.card_fin]; exact Nat.prime_three
  · exact isCycle_finRotate
  · exact support_finRotate
  · exact ⟨0, 1, by decide, rfl⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- A submodule stable under both auxiliary permutations is invariant under the representation. -/
theorem mem_invariantSubmodule_of_stable_under_auxiliaryPermutations (ρ : Representation ℂ (Equiv.Perm (Fin 3)) V) (W : Submodule ℂ V)
    (hσ : ∀ x ∈ W, ρ auxiliaryPermutationA x ∈ W) (hτ : ∀ x ∈ W, ρ auxiliaryPermutationB x ∈ W) :
    W ∈ ρ.invtSubmodule := by
  rw [ρ.mem_invtSubmodule]
  intro g
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  have hmem : g ∈ Subgroup.closure ({auxiliaryPermutationA, auxiliaryPermutationB} : Set (Equiv.Perm (Fin 3))) := by
    rw [auxiliaryPermutations_closure]; trivial
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hmem
  · intro x hx
    rcases hx with hx | hx
    · subst hx; exact hσ
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact hτ
  · intro x hx; rw [map_one, Module.End.one_apply]; exact hx
  · intro x y _ _ Px Py z hz
    rw [map_mul, Module.End.mul_apply]; exact Px _ (Py _ hz)
  · intro x _ Px z hz
    have hxinj : Function.Injective (ρ x) := by
      have hli : Function.LeftInverse (ρ x⁻¹) (ρ x) := fun w => by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      exact hli.injective
    let fW : W →ₗ[ℂ] W := (ρ x).restrict Px
    have hfWinj : Function.Injective fW := by
      intro a b hab
      apply Subtype.ext
      apply hxinj
      have ha : (fW a : V) = ρ x (a : V) := rfl
      have hb : (fW b : V) = ρ x (b : V) := rfl
      rw [← ha, ← hb, hab]
    have hfWsurj : Function.Surjective fW := LinearMap.injective_iff_surjective.mp hfWinj
    obtain ⟨a, ha⟩ := hfWsurj ⟨z, hz⟩
    have haz : ρ x (a : V) = z := congrArg Subtype.val ha
    have hxz : ρ x⁻¹ z = (a : V) := by
      rw [← haz, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hxz]; exact a.2



/-- A simple finite-dimensional complex representation of the symmetric group on three letters has the auxiliary property. -/
@[source_ref "Chapter5/Example5.1.3" (role := supporting)]
theorem auxiliaryPropertyOfSimpleSymmetricThreeRepresentation
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin 3)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin 3))) ρ.asModule) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by
  classical
  apply RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_property_of_auxiliary_eq_one ρ hρ

  have hSO : IsSimpleOrder ρ.invtSubmodule :=
    (Representation.mapSubmodule ρ).isSimpleOrder_iff.mpr hρ.toIsSimpleOrder
  haveI := hSO
  haveI : Nontrivial V := (Representation.invtSubmodule.nontrivial_iff ρ).mp inferInstance

  have hkey : 4 * (Module.finrank ℂ V : ℂ)
      + LinearMap.trace ℂ V (ρ auxiliaryPermutationA)
      + LinearMap.trace ℂ V (ρ (auxiliaryPermutationA * auxiliaryPermutationA)) = 6 := by

    have hop : ρ auxiliaryPermutationA * ρ auxiliaryPermutationB
        = ρ auxiliaryPermutationB * ρ auxiliaryPermutationA * ρ auxiliaryPermutationA := by
      rw [← map_mul ρ, ← map_mul ρ, ← map_mul ρ, auxiliaryPermutationA_mul_auxiliaryPermutationB]

    have hconj : LinearMap.trace ℂ V (ρ (auxiliaryPermutationA * auxiliaryPermutationA))
        = LinearMap.trace ℂ V (ρ auxiliaryPermutationA) := by
      rw [auxiliaryPermutationA_sq_relation, map_mul, LinearMap.trace_mul_comm, ← map_mul, auxiliaryPermutationA_mul_inv_mul]

    have hE1inv : LinearMap.ker (ρ auxiliaryPermutationA - 1) ∈ ρ.invtSubmodule := by
      apply mem_invariantSubmodule_of_stable_under_auxiliaryPermutations
      · intro x hx
        have hx' : ρ auxiliaryPermutationA x = x := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
          exact hx
        rw [hx', LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        exact hx'
      · intro x hx
        have hx' : ρ auxiliaryPermutationA x = x := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
          exact hx
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        calc ρ auxiliaryPermutationA (ρ auxiliaryPermutationB x)
            = (ρ auxiliaryPermutationA * ρ auxiliaryPermutationB) x := by rw [Module.End.mul_apply]
          _ = (ρ auxiliaryPermutationB * ρ auxiliaryPermutationA * ρ auxiliaryPermutationA) x := by rw [hop]
          _ = ρ auxiliaryPermutationB (ρ auxiliaryPermutationA (ρ auxiliaryPermutationA x)) := by
                rw [Module.End.mul_apply, Module.End.mul_apply]
          _ = ρ auxiliaryPermutationB x := by rw [hx', hx']
    rcases hSO.eq_bot_or_eq_top (⟨_, hE1inv⟩ : ρ.invtSubmodule) with hb | ht
    ·
      have hE : LinearMap.ker (ρ auxiliaryPermutationA - 1) = ⊥ := by
        have := congrArg Subtype.val hb
        rwa [Representation.invtSubmodule.coe_bot] at this
      have hsinj : Function.Injective ((ρ auxiliaryPermutationA - 1 : Module.End ℂ V)) := by
        rw [← LinearMap.ker_eq_bot]; exact hE
      have hcube : (ρ auxiliaryPermutationA) ^ 3 = 1 := by
        rw [← map_pow, auxiliaryPermutationA_pow_three, map_one]
      have hquad : ((ρ auxiliaryPermutationA) ^ 2 + ρ auxiliaryPermutationA + 1 : Module.End ℂ V) = 0 := by
        have hfactor : (ρ auxiliaryPermutationA - 1) * ((ρ auxiliaryPermutationA) ^ 2 + ρ auxiliaryPermutationA + 1) = 0 := by
          have h : (ρ auxiliaryPermutationA - 1) * ((ρ auxiliaryPermutationA) ^ 2 + ρ auxiliaryPermutationA + 1)
              = (ρ auxiliaryPermutationA) ^ 3 - 1 := by noncomm_ring
          rw [h, hcube, sub_self]
        ext x
        simp only [LinearMap.zero_apply]
        apply hsinj
        rw [map_zero, ← Module.End.mul_apply, hfactor, LinearMap.zero_apply]
      have hsq : (ρ auxiliaryPermutationA) ^ 2 = ρ (auxiliaryPermutationA * auxiliaryPermutationA) := by rw [map_mul, sq]
      have htr : LinearMap.trace ℂ V (ρ auxiliaryPermutationA)
          + LinearMap.trace ℂ V (ρ auxiliaryPermutationA) + (Module.finrank ℂ V : ℂ) = 0 := by
        have h := congrArg (LinearMap.trace ℂ V) hquad
        rw [map_add, map_add, LinearMap.trace_one, map_zero, hsq, hconj] at h
        exact h

      obtain ⟨μ, hμev⟩ := Module.End.exists_eigenvalue (ρ auxiliaryPermutationA)
      obtain ⟨v, hv⟩ := hμev.exists_hasEigenvector
      have hv0 : v ≠ 0 := hv.2
      have hσv : ρ auxiliaryPermutationA v = μ • v := hv.apply_eq_smul
      have hμ1 : μ ≠ 1 := by
        intro h
        apply hv0
        have hker : v ∈ LinearMap.ker (ρ auxiliaryPermutationA - 1) := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hσv, h, one_smul,
            sub_self]
        rw [hE, Submodule.mem_bot] at hker; exact hker
      have hμ3 : μ ^ 3 = 1 := by
        have h1 : ((ρ auxiliaryPermutationA) ^ 3) v = v := by rw [hcube, Module.End.one_apply]
        rw [hv.pow_apply 3] at h1
        have hh : (μ ^ 3 - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
        rcases smul_eq_zero.mp hh with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hv0
      have hμ2 : μ ^ 2 ≠ μ := by
        intro h
        have hμ0 : μ ≠ 0 := fun h0 => by rw [h0] at hμ3; norm_num at hμ3
        apply hμ1
        apply mul_left_cancel₀ hμ0
        rw [mul_one, ← sq, h]
      have hτinj : Function.Injective (ρ auxiliaryPermutationB) := by
        have hli : Function.LeftInverse (ρ auxiliaryPermutationB⁻¹) (ρ auxiliaryPermutationB) := fun w => by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        exact hli.injective
      have hτv0 : ρ auxiliaryPermutationB v ≠ 0 := fun h => hv0 (hτinj (by rw [h, map_zero]))
      have hσu : ρ auxiliaryPermutationA (ρ auxiliaryPermutationB v) = μ ^ 2 • ρ auxiliaryPermutationB v := by
        calc ρ auxiliaryPermutationA (ρ auxiliaryPermutationB v)
            = (ρ auxiliaryPermutationA * ρ auxiliaryPermutationB) v := by rw [Module.End.mul_apply]
          _ = (ρ auxiliaryPermutationB * ρ auxiliaryPermutationA * ρ auxiliaryPermutationA) v := by rw [hop]
          _ = ρ auxiliaryPermutationB (ρ auxiliaryPermutationA (ρ auxiliaryPermutationA v)) := by
                rw [Module.End.mul_apply, Module.End.mul_apply]
          _ = ρ auxiliaryPermutationB (μ ^ 2 • v) := by rw [hσv, map_smul, hσv, smul_smul, ← sq]
          _ = μ ^ 2 • ρ auxiliaryPermutationB v := by rw [map_smul]
      have hindep : LinearIndependent ℂ (![v, ρ auxiliaryPermutationB v] : Fin 2 → V) := by
        apply Module.End.eigenvectors_linearIndependent' (ρ auxiliaryPermutationA)
          (![μ, μ ^ 2] : Fin 2 → ℂ) ?_ (![v, ρ auxiliaryPermutationB v])
        · intro i
          fin_cases i
          · exact ⟨Module.End.mem_eigenspace_iff.mpr hσv, hv0⟩
          · exact ⟨Module.End.mem_eigenspace_iff.mpr hσu, hτv0⟩
        · intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm]
      have hWinv : (Submodule.span ℂ ({v, ρ auxiliaryPermutationB v} : Set V)) ∈ ρ.invtSubmodule := by
        apply mem_invariantSubmodule_of_stable_under_auxiliaryPermutations
        · intro x hx
          have hle : Submodule.span ℂ ({v, ρ auxiliaryPermutationB v} : Set V)
              ≤ (Submodule.span ℂ ({v, ρ auxiliaryPermutationB v} : Set V)).comap (ρ auxiliaryPermutationA) := by
            rw [Submodule.span_le]
            rintro y (rfl | hy)
            · rw [SetLike.mem_coe, Submodule.mem_comap, hσv]
              exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
            · rw [Set.mem_singleton_iff] at hy; subst hy
              rw [SetLike.mem_coe, Submodule.mem_comap, hσu]
              exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
          exact hle hx
        · intro x hx
          have hle : Submodule.span ℂ ({v, ρ auxiliaryPermutationB v} : Set V)
              ≤ (Submodule.span ℂ ({v, ρ auxiliaryPermutationB v} : Set V)).comap (ρ auxiliaryPermutationB) := by
            rw [Submodule.span_le]
            rintro y (rfl | hy)
            · rw [SetLike.mem_coe, Submodule.mem_comap]
              exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
            · rw [Set.mem_singleton_iff] at hy; subst hy
              rw [SetLike.mem_coe, Submodule.mem_comap,
                show ρ auxiliaryPermutationB (ρ auxiliaryPermutationB v) = v by
                  rw [← Module.End.mul_apply, ← map_mul, auxiliaryPermutationB_sq, map_one,
                    Module.End.one_apply]]
              exact Submodule.subset_span (Set.mem_insert _ _)
          exact hle hx
      have hWtop : Submodule.span ℂ ({v, ρ auxiliaryPermutationB v} : Set V) = ⊤ := by
        rcases hSO.eq_bot_or_eq_top (⟨_, hWinv⟩ : ρ.invtSubmodule) with h | h
        · exfalso
          have hb' : Submodule.span ℂ ({v, ρ auxiliaryPermutationB v} : Set V) = ⊥ := by
            have := congrArg Subtype.val h
            rwa [Representation.invtSubmodule.coe_bot] at this
          apply hv0
          have : v ∈ (⊥ : Submodule ℂ V) := by
            rw [← hb']; exact Submodule.subset_span (Set.mem_insert _ _)
          rwa [Submodule.mem_bot] at this
        · have := congrArg Subtype.val h
          rwa [Representation.invtSubmodule.coe_top] at this
      have hrange : Set.range (![v, ρ auxiliaryPermutationB v] : Fin 2 → V) = {v, ρ auxiliaryPermutationB v} := by
        ext x
        simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]
      let B : Module.Basis (Fin 2) ℂ V := Module.Basis.mk hindep (le_of_eq (by rw [hrange, hWtop]))
      have hd2 : Module.finrank ℂ V = 2 := by rw [Module.finrank_eq_card_basis B]; simp
      have hcast : (Module.finrank ℂ V : ℂ) = 2 := by rw [hd2]; norm_num
      rw [hconj, hcast]
      rw [hcast] at htr
      linear_combination htr
    ·
      have hE : LinearMap.ker (ρ auxiliaryPermutationA - 1) = ⊤ := by
        have := congrArg Subtype.val ht
        rwa [Representation.invtSubmodule.coe_top] at this
      have hs1 : ρ auxiliaryPermutationA = 1 := sub_eq_zero.mp (LinearMap.ker_eq_top.mp hE)
      obtain ⟨ν, hνev⟩ := Module.End.exists_eigenvalue (ρ auxiliaryPermutationB)
      obtain ⟨w, hw⟩ := hνev.exists_hasEigenvector
      have hw0 : w ≠ 0 := hw.2
      have hτw : ρ auxiliaryPermutationB w = ν • w := hw.apply_eq_smul
      have hW'inv : (Submodule.span ℂ ({w} : Set V)) ∈ ρ.invtSubmodule := by
        apply mem_invariantSubmodule_of_stable_under_auxiliaryPermutations
        · intro x hx; rw [hs1, Module.End.one_apply]; exact hx
        · intro x hx
          have hle : Submodule.span ℂ ({w} : Set V)
              ≤ (Submodule.span ℂ ({w} : Set V)).comap (ρ auxiliaryPermutationB) := by
            rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
              Submodule.mem_comap, hτw]
            exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
          exact hle hx
      have hW'top : Submodule.span ℂ ({w} : Set V) = ⊤ := by
        rcases hSO.eq_bot_or_eq_top (⟨_, hW'inv⟩ : ρ.invtSubmodule) with h | h
        · exfalso
          have hb' : Submodule.span ℂ ({w} : Set V) = ⊥ := by
            have := congrArg Subtype.val h
            rwa [Representation.invtSubmodule.coe_bot] at this
          apply hw0
          have : w ∈ (⊥ : Submodule ℂ V) := by
            rw [← hb']; exact Submodule.subset_span rfl
          rwa [Submodule.mem_bot] at this
        · have := congrArg Subtype.val h
          rwa [Representation.invtSubmodule.coe_top] at this
      have hd1 : Module.finrank ℂ V = 1 := by
        have h1 : Module.finrank ℂ V
            = Module.finrank ℂ (Submodule.span ℂ ({w} : Set V)) := by rw [hW'top, finrank_top]
        rw [h1, finrank_span_singleton hw0]
      have hcast : (Module.finrank ℂ V : ℂ) = 1 := by rw [hd1]; norm_num
      have hT : LinearMap.trace ℂ V (ρ auxiliaryPermutationA) = 1 := by
        rw [hs1, LinearMap.trace_one, hcast]
      have hT2 : LinearMap.trace ℂ V (ρ (auxiliaryPermutationA * auxiliaryPermutationA)) = 1 := by
        rw [map_mul, hs1, mul_one, LinearMap.trace_one, hcast]
      rw [hT, hT2, hcast]; norm_num

  unfold RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar
  have hsum : ∑ g : Equiv.Perm (Fin 3), LinearMap.trace ℂ V (ρ (g * g))
      = 4 * LinearMap.trace ℂ V (ρ 1) + LinearMap.trace ℂ V (ρ auxiliaryPermutationA)
        + LinearMap.trace ℂ V (ρ (auxiliaryPermutationA * auxiliaryPermutationA)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g => g * g = 1)]
    have e1 : ∑ g ∈ Finset.univ.filter (fun g : Equiv.Perm (Fin 3) => g * g = 1),
        LinearMap.trace ℂ V (ρ (g * g))
        = ∑ _g ∈ Finset.univ.filter (fun g : Equiv.Perm (Fin 3) => g * g = 1),
          LinearMap.trace ℂ V (ρ 1) :=
      Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.mp hg).2])
    have hc : (Finset.univ.filter (fun g : Equiv.Perm (Fin 3) => g * g = 1)).card = 4 := by decide
    have e2 : (Finset.univ.filter (fun g : Equiv.Perm (Fin 3) => ¬ g * g = 1))
        = {auxiliaryPermutationA, auxiliaryPermutationA * auxiliaryPermutationA} := by decide
    rw [e1, Finset.sum_const, hc, e2, Finset.sum_pair auxiliaryPermutationA_ne_sq, auxiliaryPermutationA_sq_sq]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have htr1 : LinearMap.trace ℂ V (ρ 1) = (Module.finrank ℂ V : ℂ) := by
    rw [map_one, LinearMap.trace_one]
  have hcard : (Fintype.card (Equiv.Perm (Fin 3)) : ℂ) = 6 := by
    rw [Fintype.card_perm, Fintype.card_fin]; norm_num
  rw [hsum, htr1, hkey, hcard]
  norm_num















section GroupAlgebraRealForm

open scoped MonoidAlgebra
open MonoidAlgebra

variable {G : Type*} [Group G] [Fintype G]

/-- A linear pairing from a finite monoid algebra to its linear dual. -/
noncomputable def coefficientPairing :
    MonoidAlgebra ℂ G →ₗ[ℂ] MonoidAlgebra ℂ G →ₗ[ℂ] ℂ :=
  ∑ g : G, (LinearMap.mul ℂ ℂ).compl₁₂
    ((Finsupp.lapply g).comp (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)
    ((Finsupp.lapply g).comp (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)

/-- The coefficient pairing is the sum of pointwise products of coefficients. -/
lemma coefficientPairing_apply (x y : MonoidAlgebra ℂ G) :
    coefficientPairing x y = ∑ g : G, x g * y g := by
  simp only [coefficientPairing, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
  rfl

/-- The coefficient pairing is symmetric. -/
lemma coefficientPairing_comm (x y : MonoidAlgebra ℂ G) : coefficientPairing x y = coefficientPairing y x := by
  rw [coefficientPairing_apply, coefficientPairing_apply]
  exact Finset.sum_congr rfl fun g _ => mul_comm _ _

/-- Left multiplication of both arguments by the same group element preserves the coefficient pairing. -/
lemma coefficientPairing_mul_single_left (h : G) (x y : MonoidAlgebra ℂ G) :
    coefficientPairing (of ℂ G h * x) (of ℂ G h * y) = coefficientPairing x y := by
  rw [coefficientPairing_apply, coefficientPairing_apply]
  have hx : ∀ g : G, (of ℂ G h * x) g = x (h⁻¹ * g) := by
    intro g; rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply, one_mul]
  have hy : ∀ g : G, (of ℂ G h * y) g = y (h⁻¹ * g) := by
    intro g; rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply, one_mul]
  simp only [hx, hy]
  exact Equiv.sum_comp (Equiv.mulLeft h⁻¹) (fun g => x g * y g)

/-- A nonzero group-algebra element with real coefficients has nonzero self-pairing. -/
lemma coefficientPairing_self_ne_zero_of_coeff_im_eq_zero (c : MonoidAlgebra ℂ G)
    (hreal : ∀ x, (c x).im = 0) (hc : c ≠ 0) : coefficientPairing c c ≠ 0 := by
  have hre : ∀ g : G, c g * c g = (((c g).re ^ 2 : ℝ) : ℂ) := by
    intro g
    have h := hreal g
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, h, pow_two]
  have key : coefficientPairing c c = (((∑ g : G, (c g).re ^ 2) : ℝ) : ℂ) := by
    rw [coefficientPairing_apply, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun g _ => hre g
  rw [key, Ne, Complex.ofReal_eq_zero]
  intro hsum
  apply hc
  have hzero : ∀ g : G, (c g).re = 0 := by
    intro g
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun g _ => sq_nonneg ((c g).re)).mp hsum g
      (Finset.mem_univ g)
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h
  ext g
  change c g = 0
  exact Complex.ext (by simpa using hzero g) (by simpa using hreal g)

/-- A simple representation has the auxiliary property when an equivariant map sends some vector to a nonzero group-algebra element with real coefficients. -/
theorem auxiliaryPropertyOfEquivariantMapWithNonzeroRealImage
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (ψ : V →ₗ[ℂ] MonoidAlgebra ℂ G)
    (hψ : ∀ g v, ψ (ρ g v) = of ℂ G g * ψ v)
    (c : MonoidAlgebra ℂ G) (hreal : ∀ x, (c x).im = 0)
    (v₀ : V) (hv₀ : ψ v₀ = c) (hcne : c ≠ 0) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by
  set B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ := coefficientPairing.compl₁₂ ψ ψ with hB
  have hBapply : ∀ v w, B v w = coefficientPairing (ψ v) (ψ w) := fun v w => by
    simp [hB, LinearMap.compl₁₂_apply]
  have hsym : ∀ v w, B v w = B w v := fun v w => by
    rw [hBapply, hBapply]; exact coefficientPairing_comm _ _
  have hinv : ∀ g v w, B (ρ g v) (ρ g w) = B v w := fun g v w => by
    rw [hBapply, hBapply, hψ, hψ, coefficientPairing_mul_single_left]
  have hBne : B ≠ 0 := by
    intro h0
    have hzero : B v₀ v₀ = 0 := by rw [h0]; simp
    rw [hBapply, hv₀] at hzero
    exact coefficientPairing_self_ne_zero_of_coeff_im_eq_zero c hreal hcne hzero
  exact ⟨B, hsym, RepresentationTheory.Representation.Character.InversionAndInvariantForms.invariant_bilinear_form_left_nondegenerate ρ hρ B hBne hinv, hinv⟩

end GroupAlgebraRealForm

/-- Every coefficient of the specified symmetric-group algebra element has zero imaginary part. -/
lemma auxiliarySymmetricGroupCoefficient_im_eq_zero (n : ℕ) (la : Nat.Partition n)
    (x : Equiv.Perm (Fin n)) : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la x).im = 0 := by
  rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.complexPartitionSymmetrizer_eq_map_int, MonoidAlgebra.mapRingHom_apply]
  simp

/-- A simple finite-dimensional complex representation of the symmetric group on four letters has the auxiliary property. -/
@[source_ref "Chapter5/Example5.1.3" (role := supporting)]
theorem auxiliaryPropertyOfSimpleSymmetricFourRepresentation
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin 4)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin 4))) ρ.asModule) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by
  classical
  haveI := hρ


  obtain ⟨I, ⟨φ_M⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
      (MonoidAlgebra ℂ (Equiv.Perm (Fin 4))) ρ.asModule
  haveI : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin 4))) I :=
    IsSimpleModule.congr φ_M.symm
  obtain ⟨la, ⟨φ_I⟩⟩ := RepresentationTheory.SimpleModule.SubtypeRepresentation.exists_linearEquiv_to_subtype 4 I

  set Ψ := φ_M.trans φ_I with hΨ
  set c := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC 4 la with hc
  have hc_mem : c ∈ RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 la := Submodule.subset_span rfl

  set ψ : V →ₗ[ℂ] MonoidAlgebra ℂ (Equiv.Perm (Fin 4)) :=
    ((RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 la).subtype.restrictScalars ℂ).comp
      ((Ψ.restrictScalars ℂ).toLinearMap.comp ρ.asModuleEquiv.symm.toLinearMap) with hψdef
  have hψ_apply : ∀ v : V,
      ψ v = (Ψ (ρ.asModuleEquiv.symm v) : MonoidAlgebra ℂ (Equiv.Perm (Fin 4))) := by
    intro v; rfl

  have hψ : ∀ (g : Equiv.Perm (Fin 4)) (v : V),
      ψ (ρ g v) = MonoidAlgebra.of ℂ (Equiv.Perm (Fin 4)) g * ψ v := by
    intro g v
    rw [hψ_apply, hψ_apply, ρ.asModuleEquiv_symm_map_rho, map_smul]
    simp only [Submodule.coe_smul, smul_eq_mul]

  have hcne : c ≠ 0 := by
    intro h0
    rw [hc] at h0
    exact RepresentationTheory.PartitionAuxiliary.self_mul_ne_zero 4 la (by rw [h0, mul_zero])
  set v₀ : V := ρ.asModuleEquiv (Ψ.symm ⟨c, hc_mem⟩) with hv₀def
  have hv₀ : ψ v₀ = c := by
    rw [hψ_apply, hv₀def, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  exact auxiliaryPropertyOfEquivariantMapWithNonzeroRealImage ρ hρ ψ hψ c
    (auxiliarySymmetricGroupCoefficient_im_eq_zero 4 la) v₀ hv₀ hcne

set_option maxRecDepth 10000 in
/-- Every element of the alternating group on five letters is conjugate to its inverse. -/
theorem isConj_inv_in_alternatingGroupFive (g : alternatingGroup (Fin 5)) :
    IsConj g g⁻¹ := by
  have h : ∀ h : alternatingGroup (Fin 5), ∃ c : alternatingGroup (Fin 5),
      c * h * c⁻¹ = h⁻¹ := by decide
  obtain ⟨c, hc⟩ := h g
  exact isConj_iff.mpr ⟨c, hc⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The alternating group on five letters has five conjugacy classes. -/
theorem card_conjClasses_alternatingGroupFive :
    Fintype.card (ConjClasses (alternatingGroup (Fin 5))) = 5 := by decide

/-- An auxiliary theorem. -/
lemma auxiliaryTheoremA
    (d ε : Fin 5 → ℤ)
    (hd : ∀ i, 1 ≤ d i)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hsq : ∑ i, d i ^ 2 = 60)
    (hcount : ∑ i, ε i * d i = 16) :
    ∀ i, ε i = 1 := by

  have hcheb : (∑ i, d i) ^ 2 ≤ 5 * ∑ i, d i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 5))) (f := d)
    simpa using h
  rw [hsq] at hcheb
  set T := ∑ j, d j with hT
  intro i
  by_contra hi
  have hneg : ε i = -1 := (hε i).resolve_left hi


  have hf_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin 5)), (0 : ℤ) ≤ d j - ε j * d j := by
    intro j _
    rcases hε j with hj | hj
    · rw [hj]; simp
    · rw [hj]; nlinarith [hd j]
  have hsum_def : ∑ j, (d j - ε j * d j) = T - 16 := by
    rw [Finset.sum_sub_distrib, hcount, hT]
  have hfi : (2 : ℤ) ≤ d i - ε i * d i := by rw [hneg]; nlinarith [hd i]
  have hsingle : d i - ε i * d i ≤ ∑ j, (d j - ε j * d j) :=
    Finset.single_le_sum hf_nonneg (Finset.mem_univ i)
  have hTge : (18 : ℤ) ≤ T := by rw [hsum_def] at hsingle; linarith
  nlinarith [hcheb, hTge]

section A5EvenAssembly

open _root_.CategoryTheory

/-- An auxiliary theorem. -/
lemma auxiliaryTheoremE {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 5) (d ε : ι → ℤ)
    (hd : ∀ i, 1 ≤ d i) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hsq : ∑ i, d i ^ 2 = 60) (hcount : ∑ i, ε i * d i = 16) :
    ∀ i, ε i = 1 := by
  have hcheb : (∑ i, d i) ^ 2 ≤ 5 * ∑ i, d i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := d)
    rw [Finset.card_univ, hcard] at h
    simpa using h
  rw [hsq] at hcheb
  set T := ∑ j, d j with hT
  intro i
  by_contra hi
  have hneg : ε i = -1 := (hε i).resolve_left hi
  have hf_nonneg : ∀ j ∈ (Finset.univ : Finset ι), (0 : ℤ) ≤ d j - ε j * d j := by
    intro j _
    rcases hε j with hj | hj
    · rw [hj]; simp
    · rw [hj]; nlinarith [hd j]
  have hsum_def : ∑ j, (d j - ε j * d j) = T - 16 := by
    rw [Finset.sum_sub_distrib, hcount, hT]
  have hfi : (2 : ℤ) ≤ d i - ε i * d i := by rw [hneg]; nlinarith [hd i]
  have hsingle : d i - ε i * d i ≤ ∑ j, (d j - ε j * d j) :=
    Finset.single_le_sum hf_nonneg (Finset.mem_univ i)
  have hTge : (18 : ℤ) ≤ T := by rw [hsum_def] at hsingle; linarith
  nlinarith [hcheb, hTge]

/-- Finite-dimensional complex representations with equal characters have equal auxiliary invariants. -/
lemma auxiliaryInvariant_eq_of_character_eq
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : ∀ g, Representation.character ρ g = Representation.character σ g) :
    RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar σ := by
  simp only [RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar]
  congr 1
  exact Finset.sum_congr rfl (fun g _ => h (g * g))

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]


private lemma simple_of_full_faithful_preservesMono' {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f



private lemma simple_FDRep_of_isSimpleModule [NeZero (Nat.card G : ℂ)]
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V)
    [IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule] :
    Simple (FDRep.of ρ) := by
  let E := Rep.equivalenceModuleMonoidAlgebra (k := ℂ) (G := G)
  haveI : Simple (E.functor.obj ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of ρ))) := by
    change Simple (ModuleCat.of (MonoidAlgebra ℂ G) ρ.asModule)
    exact simple_of_isSimpleModule
  haveI : Simple ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of ρ)) :=
    simple_of_full_faithful_preservesMono' E.functor _
  exact simple_of_full_faithful_preservesMono' (forget₂ (FDRep ℂ G) (Rep ℂ G)) _









private lemma frobeniusSchurIndicator_pm_one_of_simple_selfDual
    [NeZero (Nat.card G : ℂ)] [Invertible (Fintype.card G : ℂ)]
    (W : FDRep ℂ G) (hW : IsSimpleModule (MonoidAlgebra ℂ G) (Representation.asModule W.ρ))
    (hsd : ∀ g, Representation.character W.ρ g⁻¹ = Representation.character W.ρ g) :
    RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar W.ρ = 1 ∨ RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar W.ρ = -1 :=
  RepresentationTheory.Representation.Character.AuxiliaryVanishing.auxiliaryStatement W.ρ hW hsd

set_option maxRecDepth 10000 in
/-- A simple even-dimensional representation of the alternating group on five letters whose character is invariant under inversion has the auxiliary property. -/
theorem auxiliaryPropertyOfEvenDimensionalSimpleAlternatingFiveRepresentation
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (alternatingGroup (Fin 5)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (alternatingGroup (Fin 5))) ρ.asModule)
    (hsd : ∀ g, Representation.character ρ g⁻¹ = Representation.character ρ g)
    (heven : Even (Module.finrank ℂ V)) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by
  classical

  apply RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_property_of_auxiliary_eq_one ρ hρ

  have hcard60 : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
    rw [card_alternatingGroup, Fintype.card_fin]; rfl
  haveI hNZ : NeZero (Nat.card (alternatingGroup (Fin 5)) : ℂ) := by
    refine ⟨?_⟩; rw [Nat.card_eq_fintype_card, hcard60]; norm_num
  haveI hInv : Invertible (Fintype.card (alternatingGroup (Fin 5)) : ℂ) :=
    invertibleOfNonzero (by rw [hcard60]; norm_num)

  let D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData ℂ (alternatingGroup (Fin 5)) := RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default
  let W : Fin D.count → FDRep ℂ (alternatingGroup (Fin 5)) := D.representation
  have hWs : ∀ i, Simple (W i) := D.simple_representation
  have hWi : ∀ i j, Nonempty ((W i) ≅ (W j)) → i = j := D.representation_index_eq_of_iso

  have h5 : Fintype.card (Fin D.count) = 5 := by
    rw [Fintype.card_fin, D.invariant_eq_card_conjClasses]
    exact card_conjClasses_alternatingGroupFive

  have hsqN : ∑ i, (Module.finrank ℂ (W i)) ^ 2 = 60 := by
    rw [D.sum_finrank_sq_eq_card_of_simple_pairwise W hWs hWi, hcard60]

  have hcountC : ((Finset.univ.filter
        (fun g : alternatingGroup (Fin 5) => g * g = 1)).card : ℂ)
      = ∑ i, RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar (W i).ρ * (Module.finrank ℂ (W i) : ℂ) :=
    RepresentationTheory.FDRep.Auxiliary.card_sq_eq_one_eq_sum_representationInvariant_mul_finrank D W hWs hWi
  have hinv16 : (Finset.univ.filter
      (fun g : alternatingGroup (Fin 5) => g * g = 1)).card = 16 := by decide

  have hsdW : ∀ i, ∀ g, Representation.character (W i).ρ g⁻¹
      = Representation.character (W i).ρ g := by
    intro i g
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_inv_in_alternatingGroupFive g)
    rw [← hc]; exact Representation.char_conj (W i).ρ g c

  have hFSmem : ∀ i, RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar (W i).ρ = 1
      ∨ RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar (W i).ρ = -1 :=
    fun i => frobeniusSchurIndicator_pm_one_of_simple_selfDual (W i)
      (D.isSimpleModule_coordinateRepresentation i) (hsdW i)

  set dd : Fin D.count → ℤ := fun i => (Module.finrank ℂ (W i) : ℤ) with hdd
  set ee : Fin D.count → ℤ :=
    fun i => if RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar (W i).ρ = 1 then (1 : ℤ) else -1 with hee
  have hεval : ∀ i, RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar (W i).ρ = (ee i : ℂ) := by
    intro i
    rcases hFSmem i with h1 | h1
    · rw [hee]; simp only [if_pos h1]; rw [h1]; norm_num
    · have hne : RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar (W i).ρ ≠ 1 := by rw [h1]; norm_num
      rw [hee]; simp only [if_neg hne]; rw [h1]; norm_num
  have hd : ∀ i, 1 ≤ dd i := by
    intro i
    have hfpos : 0 < Module.finrank ℂ (W i) := by
      rw [D.finrank_representation i]; exact Nat.pos_of_ne_zero (D.dimension_neZero i).out
    simp only [hdd]; exact_mod_cast hfpos
  have hε : ∀ i, ee i = 1 ∨ ee i = -1 := by
    intro i
    by_cases h : RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar (W i).ρ = 1
    · left; rw [hee]; simp only [if_pos h]
    · right; rw [hee]; simp only [if_neg h]
  have hsq : ∑ i, dd i ^ 2 = 60 := by
    rw [hdd]
    calc ∑ i, ((Module.finrank ℂ (W i) : ℤ)) ^ 2
        = ((∑ i, (Module.finrank ℂ (W i)) ^ 2 : ℕ) : ℤ) := by push_cast; ring
      _ = ((60 : ℕ) : ℤ) := by rw [hsqN]
      _ = 60 := by norm_num
  have hcount : ∑ i, ee i * dd i = 16 := by
    have hC : ((16 : ℕ) : ℂ)
        = ∑ i, RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar (W i).ρ * (Module.finrank ℂ (W i) : ℂ) := by
      rw [← hinv16]; exact_mod_cast hcountC
    have hC3 : ((∑ i, ee i * dd i : ℤ) : ℂ) = ((16 : ℤ) : ℂ) := by
      rw [show ((16 : ℤ) : ℂ) = ((16 : ℕ) : ℂ) from by norm_num, hC]
      push_cast [hdd]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hεval i]
    exact_mod_cast hC3

  have hall : ∀ i, ee i = 1 :=
    auxiliaryTheoremE h5 dd ee hd hε hsq hcount

  haveI := hρ
  haveI hsimp : Simple (FDRep.of ρ) := simple_FDRep_of_isSimpleModule ρ
  obtain ⟨i₀, ⟨iso⟩⟩ := D.exists_iso_representation_of_simple (FDRep.of ρ) hsimp
  have hchar : ∀ g, Representation.character ρ g = Representation.character (W i₀).ρ g :=
    fun g => congrFun (FDRep.char_iso iso) g
  rw [auxiliaryInvariant_eq_of_character_eq ρ (W i₀).ρ hchar, hεval i₀, hall i₀]
  norm_num

end A5EvenAssembly

/-- A simple finite-dimensional complex representation of the alternating group on five letters has the auxiliary property. -/
@[source_ref "Chapter5/Example5.1.3" (role := supporting)]
theorem auxiliaryPropertyOfSimpleAlternatingFiveRepresentation
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (alternatingGroup (Fin 5)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (alternatingGroup (Fin 5))) ρ.asModule) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by

  have hsd : ∀ g, Representation.character ρ g⁻¹ = Representation.character ρ g := by
    intro g
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_inv_in_alternatingGroupFive g)
    rw [← hc]; exact Representation.char_conj ρ g c
  rcases Nat.even_or_odd (Module.finrank ℂ V) with heven | hodd
  · exact auxiliaryPropertyOfEvenDimensionalSimpleAlternatingFiveRepresentation ρ hρ hsd heven
  · exact RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_property_of_odd_finrank_and_character_inv_eq ρ hρ hsd hodd



open Matrix Complex QuaternionGroup

/-- An auxiliary two-by-two complex matrix. -/
noncomputable def auxiliaryMatrixA : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

/-- A second auxiliary two-by-two complex matrix. -/
def auxiliaryMatrixB : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The determinant of the first auxiliary matrix is one. -/
@[simp] lemma auxiliaryMatrixA_det : auxiliaryMatrixA.det = 1 := by
  simp [auxiliaryMatrixA, Matrix.det_fin_two_of, Complex.I_mul_I]

/-- The determinant of the second auxiliary matrix is one. -/
@[simp] lemma auxiliaryMatrixB_det : auxiliaryMatrixB.det = 1 := by
  simp [auxiliaryMatrixB, Matrix.det_fin_two_of]

/-- An auxiliary theorem. -/
lemma auxiliaryTheoremC : auxiliaryMatrixA ^ 2 = -1 := by
  rw [pow_two]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [auxiliaryMatrixA, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I, Matrix.one_fin_two]

/-- The fourth power of the first auxiliary matrix is the identity. -/
lemma auxiliaryMatrixA_pow_four : auxiliaryMatrixA ^ 4 = 1 := by
  have h : auxiliaryMatrixA ^ 4 = (auxiliaryMatrixA ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h, auxiliaryTheoremC, neg_one_sq]

/-- The square of the second auxiliary matrix equals the square of the first. -/
lemma auxiliaryMatrixB_sq : auxiliaryMatrixB * auxiliaryMatrixB = auxiliaryMatrixA ^ 2 := by
  rw [auxiliaryTheoremC]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [auxiliaryMatrixB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]

/-- The product of the first auxiliary matrix with the second equals the second multiplied by the cube of the first. -/
lemma auxiliaryMatrixA_mul_auxiliaryMatrixB : auxiliaryMatrixA * auxiliaryMatrixB = auxiliaryMatrixB * auxiliaryMatrixA ^ 3 := by
  have h3 : auxiliaryMatrixA ^ 3 = !![(-Complex.I), 0; 0, Complex.I] := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, auxiliaryTheoremC]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [auxiliaryMatrixA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]
  rw [h3]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [auxiliaryMatrixA, auxiliaryMatrixB, Matrix.mul_apply, Fin.sum_univ_two]

/-- Equal casts of natural exponents give equal powers of the first auxiliary matrix. -/
lemma auxiliaryMatrixA_pow_eq_pow_of_natCast_eq {a b : ℕ} (h : (a : ZMod 4) = (b : ZMod 4)) : auxiliaryMatrixA ^ a = auxiliaryMatrixA ^ b := by
  have e : a % 4 = b % 4 := (ZMod.natCast_eq_natCast_iff a b 4).mp h
  conv_lhs => rw [← Nat.div_add_mod a 4]
  conv_rhs => rw [← Nat.div_add_mod b 4]
  rw [pow_add, pow_add, pow_mul, pow_mul, auxiliaryMatrixA_pow_four, one_pow, one_pow, e]

/-- Multiplying a power of the first auxiliary matrix by the second moves the second to the left and triples the exponent. -/
lemma auxiliaryMatrixA_pow_mul_auxiliaryMatrixB : ∀ m : ℕ, auxiliaryMatrixA ^ m * auxiliaryMatrixB = auxiliaryMatrixB * auxiliaryMatrixA ^ (3 * m)
  | 0 => by simp
  | (m + 1) => by
    rw [pow_succ, mul_assoc, auxiliaryMatrixA_mul_auxiliaryMatrixB, ← mul_assoc, auxiliaryMatrixA_pow_mul_auxiliaryMatrixB m, mul_assoc, ← pow_add,
      show 3 * m + 3 = 3 * (m + 1) from by ring]

/-- Sandwiching a power of the first auxiliary matrix between two copies of the second yields the indicated power of the first. -/
lemma auxiliaryMatrixB_mul_pow_mul_auxiliaryMatrixB (m : ℕ) : auxiliaryMatrixB * auxiliaryMatrixA ^ m * auxiliaryMatrixB = auxiliaryMatrixA ^ (2 + 3 * m) := by
  rw [mul_assoc, auxiliaryMatrixA_pow_mul_auxiliaryMatrixB, ← mul_assoc, auxiliaryMatrixB_sq, ← pow_add]

/-- A function from the quaternion group to two-by-two complex matrices. -/
noncomputable def quaternionGroupMatrixMap : QuaternionGroup 2 → Matrix (Fin 2) (Fin 2) ℂ
  | .a k => auxiliaryMatrixA ^ k.val
  | .xa k => auxiliaryMatrixB * auxiliaryMatrixA ^ k.val

/-- A multiplicative homomorphism from the quaternion group to two-by-two complex matrices. -/
noncomputable def quaternionGroupMatrixHom : QuaternionGroup 2 →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := quaternionGroupMatrixMap
  map_one' := by
    change quaternionGroupMatrixMap 1 = 1
    rw [QuaternionGroup.one_def]; simp [quaternionGroupMatrixMap]
  map_mul' := by
    rintro (i | i) (j | j)
    · change quaternionGroupMatrixMap (a i * a j) = quaternionGroupMatrixMap (a i) * quaternionGroupMatrixMap (a j)
      rw [QuaternionGroup.a_mul_a]
      simp only [quaternionGroupMatrixMap]
      rw [← pow_add]
      exact auxiliaryMatrixA_pow_eq_pow_of_natCast_eq (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    · change quaternionGroupMatrixMap (a i * xa j) = quaternionGroupMatrixMap (a i) * quaternionGroupMatrixMap (xa j)
      rw [QuaternionGroup.a_mul_xa]
      simp only [quaternionGroupMatrixMap]
      rw [← mul_assoc, auxiliaryMatrixA_pow_mul_auxiliaryMatrixB, mul_assoc, ← pow_add]
      congr 1
      exact auxiliaryMatrixA_pow_eq_pow_of_natCast_eq (by push_cast [ZMod.natCast_val, ZMod.cast_id]; revert i j; decide)
    · change quaternionGroupMatrixMap (xa i * a j) = quaternionGroupMatrixMap (xa i) * quaternionGroupMatrixMap (a j)
      rw [QuaternionGroup.xa_mul_a]
      simp only [quaternionGroupMatrixMap]
      rw [mul_assoc, ← pow_add]
      congr 1
      exact auxiliaryMatrixA_pow_eq_pow_of_natCast_eq (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    · change quaternionGroupMatrixMap (xa i * xa j) = quaternionGroupMatrixMap (xa i) * quaternionGroupMatrixMap (xa j)
      rw [QuaternionGroup.xa_mul_xa]
      simp only [quaternionGroupMatrixMap]
      rw [← mul_assoc (auxiliaryMatrixB * auxiliaryMatrixA ^ i.val) auxiliaryMatrixB (auxiliaryMatrixA ^ j.val), auxiliaryMatrixB_mul_pow_mul_auxiliaryMatrixB, ← pow_add]
      exact auxiliaryMatrixA_pow_eq_pow_of_natCast_eq (by push_cast [ZMod.natCast_val, ZMod.cast_id]; revert i j; decide)

/-- A two-dimensional complex representation of the quaternion group. -/
noncomputable def quaternionGroupTwoDimensionalRepresentation : Representation ℂ (QuaternionGroup 2) (Fin 2 → ℂ) where
  toFun g := Matrix.toLinAlgEquiv' (quaternionGroupMatrixHom g)
  map_one' := by simp
  map_mul' g h := by simp [map_mul]

/-- The action of the two-dimensional quaternion representation is matrix-vector multiplication by its matrix homomorphism. -/
lemma quaternionGroupTwoDimensionalRepresentation_apply (g : QuaternionGroup 2) (v : Fin 2 → ℂ) :
    quaternionGroupTwoDimensionalRepresentation g v = (quaternionGroupMatrixHom g).mulVec v := by
  simp [quaternionGroupTwoDimensionalRepresentation, Matrix.toLinAlgEquiv'_apply]



/-- The specified two-dimensional complex representation of the quaternion group is simple. -/
theorem quaternionGroupTwoDimensionalRepresentation_isSimple :
    IsSimpleModule (MonoidAlgebra ℂ (QuaternionGroup 2)) quaternionGroupTwoDimensionalRepresentation.asModule := by

    have hAv : ∀ v : Fin 2 → ℂ, quaternionGroupTwoDimensionalRepresentation (QuaternionGroup.a 1) v
        = ![Complex.I * v 0, -Complex.I * v 1] := by
      intro v
      rw [quaternionGroupTwoDimensionalRepresentation_apply]
      change (quaternionGroupMatrixMap (QuaternionGroup.a 1)).mulVec v = _
      simp only [quaternionGroupMatrixMap, show (1 : ZMod (2 * 2)).val = 1 from by decide, pow_one]
      funext i; fin_cases i <;>
        simp [auxiliaryMatrixA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hXv : ∀ v : Fin 2 → ℂ, quaternionGroupTwoDimensionalRepresentation (QuaternionGroup.xa 0) v
        = ![v 1, -v 0] := by
      intro v
      rw [quaternionGroupTwoDimensionalRepresentation_apply]
      change (quaternionGroupMatrixMap (QuaternionGroup.xa 0)).mulVec v = _
      simp only [quaternionGroupMatrixMap, show (0 : ZMod (2 * 2)).val = 0 from by decide, pow_zero,
        mul_one]
      funext i; fin_cases i <;>
        simp [auxiliaryMatrixB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

    suffices hSO : IsSimpleOrder (quaternionGroupTwoDimensionalRepresentation.invtSubmodule) by
      haveI := (Representation.mapSubmodule quaternionGroupTwoDimensionalRepresentation).isSimpleOrder_iff.mp hSO
      exact ⟨⟩
    refine { eq_bot_or_eq_top := fun a => ?_ }
    have hinv : ∀ g, ∀ x ∈ (a : Submodule ℂ (Fin 2 → ℂ)),
        quaternionGroupTwoDimensionalRepresentation g x ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
      intro g x hx
      have hmem : (a : Submodule ℂ (Fin 2 → ℂ)) ∈ Module.End.invtSubmodule (quaternionGroupTwoDimensionalRepresentation g) :=
        (Representation.mem_invtSubmodule (ρ := quaternionGroupTwoDimensionalRepresentation)).mp a.2 g
      exact ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
        (f := quaternionGroupTwoDimensionalRepresentation g)).mp hmem) x hx
    rcases eq_or_ne (a : Submodule ℂ (Fin 2 → ℂ)) ⊥ with hbot | hbot
    · exact Or.inl (Subtype.ext (by rw [Representation.invtSubmodule.coe_bot]; exact hbot))
    · refine Or.inr (Subtype.ext ?_)
      rw [Representation.invtSubmodule.coe_top]

      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hbot
      have he0 : (![1, 0] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) ∧
          (![0, 1] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
        by_cases hv1 : v 1 = 0
        ·
          have hv0' : v 0 ≠ 0 := by
            intro h; apply hv0; funext i; fin_cases i
            · simpa using h
            · simpa using hv1
          have he0 : (![1, 0] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have : (v 0)⁻¹ • v = (![1, 0] : Fin 2 → ℂ) := by
              funext i; fin_cases i
              · simpa using inv_mul_cancel₀ hv0'
              · simp [hv1]
            rw [← this]; exact (a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ hv
          have he1 : (![0, 1] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have hx := hinv (QuaternionGroup.xa 0) _ he0
            rw [hXv] at hx
            have : (![(![1, 0] : Fin 2 → ℂ) 1, -(![1, 0] : Fin 2 → ℂ) 0] : Fin 2 → ℂ)
                = -(![0, 1] : Fin 2 → ℂ) := by funext i; fin_cases i <;> simp
            rw [this] at hx
            simpa using (a : Submodule ℂ (Fin 2 → ℂ)).neg_mem hx
          exact ⟨he0, he1⟩
        ·
          have hmem : (Complex.I • v - quaternionGroupTwoDimensionalRepresentation (QuaternionGroup.a 1) v)
              ∈ (a : Submodule ℂ (Fin 2 → ℂ)) :=
            (a : Submodule ℂ (Fin 2 → ℂ)).sub_mem
              ((a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ hv) (hinv _ _ hv)
          have heq : Complex.I • v - quaternionGroupTwoDimensionalRepresentation (QuaternionGroup.a 1) v
              = ![0, 2 * Complex.I * v 1] := by
            rw [hAv]; funext i; fin_cases i <;> simp [Pi.smul_apply] ; ring
          rw [heq] at hmem
          have hc : (2 : ℂ) * Complex.I * v 1 ≠ 0 := by
            simp [hv1, Complex.I_ne_zero]
          have he1 : (![0, 1] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have : (2 * Complex.I * v 1)⁻¹ • (![0, 2 * Complex.I * v 1] : Fin 2 → ℂ)
                = (![0, 1] : Fin 2 → ℂ) := by
              funext i; fin_cases i
              · simp
              · simpa using inv_mul_cancel₀ hc
            rw [← this]; exact (a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ hmem
          have he0 : (![1, 0] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have hx := hinv (QuaternionGroup.xa 0) _ he1
            rw [hXv] at hx
            have : (![(![0, 1] : Fin 2 → ℂ) 1, -(![0, 1] : Fin 2 → ℂ) 0] : Fin 2 → ℂ)
                = (![1, 0] : Fin 2 → ℂ) := by funext i; fin_cases i <;> simp
            rwa [this] at hx
          exact ⟨he0, he1⟩

      rw [eq_top_iff]
      intro w _
      have hw : w = w 0 • (![1, 0] : Fin 2 → ℂ) + w 1 • ![0, 1] := by
        funext i; fin_cases i <;> simp
      rw [hw]
      exact (a : Submodule ℂ (Fin 2 → ℂ)).add_mem
        ((a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ he0.1)
        ((a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ he0.2)

/-- There exists a simple complex representation of the quaternion group satisfying the auxiliary property. -/
@[source_ref "Chapter5/Example5.1.3" (role := supporting)]
theorem existsSimpleQuaternionRepresentationWithAuxiliaryProperty :
    ∃ ρ : Representation ℂ (QuaternionGroup 2) (Fin 2 → ℂ),
      IsSimpleModule (MonoidAlgebra ℂ (QuaternionGroup 2)) ρ.asModule ∧
      RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ := by



  refine ⟨quaternionGroupTwoDimensionalRepresentation, quaternionGroupTwoDimensionalRepresentation_isSimple, ?_⟩
  ·

    set B : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
      LinearMap.mk₂ ℂ (fun v w => v 0 * w 1 - v 1 * w 0)
        (fun v v' w => by simp only [Pi.add_apply]; ring)
        (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
        (fun v w w' => by simp only [Pi.add_apply]; ring)
        (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul]; ring) with hBdef
    have hB : ∀ v w : Fin 2 → ℂ, B v w = v 0 * w 1 - v 1 * w 0 := fun v w => rfl
    refine ⟨B, ?_, ?_, ?_⟩
    ·
      intro v w; rw [hB, hB]; ring
    ·
      intro v hv
      have h0 : v 0 = 0 := by have := hv ![0, 1]; rw [hB] at this; simpa using this
      have h1 : v 1 = 0 := by have := hv ![1, 0]; rw [hB] at this; simpa using this
      funext i; fin_cases i
      · simpa using h0
      · simpa using h1
    ·
      intro g v w
      have key : ∀ (N : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin 2 → ℂ),
          B (N.mulVec x) (N.mulVec y) = N.det * B x y := by
        intro N x y
        rw [hB, hB]
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
        ring
      rw [quaternionGroupTwoDimensionalRepresentation_apply, quaternionGroupTwoDimensionalRepresentation_apply, key]
      have hdet : (quaternionGroupMatrixHom g).det = 1 := by
        rcases g with k | k
        · change (quaternionGroupMatrixMap (QuaternionGroup.a k)).det = 1
          simp [quaternionGroupMatrixMap, Matrix.det_pow]
        · change (quaternionGroupMatrixMap (QuaternionGroup.xa k)).det = 1
          simp [quaternionGroupMatrixMap, Matrix.det_mul, Matrix.det_pow]
      rw [hdet, one_mul]

/-- Every complex representation of the quaternion group on the complex numbers has the auxiliary property. -/
@[source_ref "Chapter5/Example5.1.3" (role := supporting)]
theorem auxiliaryPropertyForQuaternionRepresentationOnComplex
    (ρ : Representation ℂ (QuaternionGroup 2) ℂ) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by
  apply auxiliaryTheoremG

  have hmul : ∀ a b : QuaternionGroup 2, ρ (a * b) 1 = ρ a 1 * ρ b 1 := by
    intro a b
    have hstep : ρ a (ρ b 1) = ρ b 1 * ρ a 1 := by
      have h := (ρ a).map_smul (ρ b 1) (1 : ℂ)
      simpa [smul_eq_mul] using h
    rw [map_mul, Module.End.mul_apply, hstep, mul_comm]
  have hone : ρ 1 1 = 1 := by simp

  have hamb : ∀ g : QuaternionGroup 2, ∃ c : QuaternionGroup 2, c * g * c⁻¹ = g⁻¹ := by
    decide
  intro g
  obtain ⟨c, hc⟩ := hamb g

  have hcc : ρ c 1 * ρ c⁻¹ 1 = 1 := by rw [← hmul, mul_inv_cancel, hone]
  have hconj : ρ g⁻¹ 1 = ρ g 1 := by
    rw [← hc, hmul, hmul]
    calc ρ c 1 * ρ g 1 * ρ c⁻¹ 1
        = (ρ c 1 * ρ c⁻¹ 1) * ρ g 1 := by ring
      _ = 1 * ρ g 1 := by rw [hcc]
      _ = ρ g 1 := one_mul _

  have hsq : ρ g 1 * ρ g 1 = 1 := by
    have h1 : ρ (g⁻¹ * g) 1 = 1 := by rw [inv_mul_cancel, hone]
    rw [hmul, hconj] at h1
    exact h1
  exact mul_self_eq_one_iff.mp hsq

/-- A simple two-dimensional complex representation of the quaternion group is isomorphic to the specified representation. -/
@[source_ref "Chapter5/Example5.1.3" (role := supporting)]
theorem simpleQuaternionRepresentationOfFinrankTwoIso
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (σ : Representation ℂ (QuaternionGroup 2) V)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (QuaternionGroup 2)) σ.asModule)
    (hdim : Module.finrank ℂ V = 2) :
    Nonempty (FDRep.of σ ≅ FDRep.of quaternionGroupTwoDimensionalRepresentation) := by
  classical

  haveI hNe : NeZero (Nat.card (QuaternionGroup 2) : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := QuaternionGroup 2)).ne'⟩

  haveI := hσ
  haveI hσsimple : CategoryTheory.Simple (FDRep.of σ) :=
    RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule σ
  haveI hrhosimple : CategoryTheory.Simple (FDRep.of quaternionGroupTwoDimensionalRepresentation) := by
    haveI := quaternionGroupTwoDimensionalRepresentation_isSimple
    exact RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule quaternionGroupTwoDimensionalRepresentation
  haveI := isSimpleModule_representationOnComplex (Representation.trivial ℂ (QuaternionGroup 2) ℂ)
  haveI htrivsimple :
      CategoryTheory.Simple (FDRep.of (Representation.trivial ℂ (QuaternionGroup 2) ℂ)) :=
    RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule _

  obtain ⟨n, W, _hWsimple, _hWinj, hWsurj, hWsum⟩ :=
    RepresentationTheory.FDRep.GroupAlgebraDecomposition.exists_completeSimpleFamily_sum_finrank_sq_eq_card ℂ (QuaternionGroup 2)
  obtain ⟨i, ⟨eσ⟩⟩ := hWsurj (FDRep.of σ) hσsimple
  obtain ⟨j, ⟨eρ⟩⟩ := hWsurj (FDRep.of quaternionGroupTwoDimensionalRepresentation) hrhosimple
  obtain ⟨l, ⟨etriv⟩⟩ :=
    hWsurj (FDRep.of (Representation.trivial ℂ (QuaternionGroup 2) ℂ)) htrivsimple

  have hfi : Module.finrank ℂ (W i) = 2 := by
    rw [← (FDRep.isoToLinearEquiv eσ).finrank_eq]; exact hdim
  have hfj : Module.finrank ℂ (W j) = 2 := by
    rw [← (FDRep.isoToLinearEquiv eρ).finrank_eq]
    change Module.finrank ℂ (Fin 2 → ℂ) = 2
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hfl : Module.finrank ℂ (W l) = 1 := by
    rw [← (FDRep.isoToLinearEquiv etriv).finrank_eq]; exact Module.finrank_self ℂ

  have hij : i = j := by
    by_contra hij
    have hli : l ≠ i := fun h => by rw [h, hfi] at hfl; exact absurd hfl (by norm_num)
    have hlj : l ≠ j := fun h => by rw [h, hfj] at hfl; exact absurd hfl (by norm_num)
    have hmemj : i ∉ ({j, l} : Finset (Fin n)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hij, fun h => hli h.symm⟩
    have hmeml : j ∉ ({l} : Finset (Fin n)) := by
      simp only [Finset.mem_singleton]; exact fun h => hlj h.symm
    have hle : (9 : ℕ) ≤ Fintype.card (QuaternionGroup 2) :=
      calc (9 : ℕ)
          = ∑ k ∈ ({i, j, l} : Finset (Fin n)), Module.finrank ℂ (W k) ^ 2 := by
            rw [Finset.sum_insert hmemj, Finset.sum_insert hmeml, Finset.sum_singleton,
              hfi, hfj, hfl]; norm_num
        _ ≤ ∑ k, Module.finrank ℂ (W k) ^ 2 :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = Fintype.card (QuaternionGroup 2) := hWsum
    rw [QuaternionGroup.card] at hle
    omega

  exact ⟨(hij ▸ eσ) ≪≫ eρ.symm⟩

end RepresentationTheory.FiniteGroupRepresentationExamples
