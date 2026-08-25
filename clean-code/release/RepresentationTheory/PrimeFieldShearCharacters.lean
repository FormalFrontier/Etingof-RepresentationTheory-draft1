/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.AuxiliaryRepresentationIsomorphisms
import RepresentationTheory.ComplexUnitCharacters
import RepresentationTheory.FiniteDimensional.Equivalences
import RepresentationTheory.ThreeCoordinateGroupRepresentations
import RepresentationTheory.Alignment.Attribute


noncomputable section

open CategoryTheory Module

namespace RepresentationTheory.PrimeFieldShearCharacters

variable (p : ℕ) [Fact p.Prime]

/-- A multiplicative automorphism of multiplicative residue pairs associated with a residue parameter. -/
def residuePairMulAut (a : ZMod p) : MulAut (Multiplicative (ZMod p × ZMod p)) where
  toFun x := Multiplicative.ofAdd
    ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2 + a * (Multiplicative.toAdd x).1)
  invFun x := Multiplicative.ofAdd
    ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2 - a * (Multiplicative.toAdd x).1)
  left_inv x := by
    apply Multiplicative.toAdd.injective; apply Prod.ext
    · rfl
    · change (Multiplicative.toAdd x).2 + a * (Multiplicative.toAdd x).1
        - a * (Multiplicative.toAdd x).1 = (Multiplicative.toAdd x).2
      ring
  right_inv x := by
    apply Multiplicative.toAdd.injective; apply Prod.ext
    · rfl
    · change (Multiplicative.toAdd x).2 - a * (Multiplicative.toAdd x).1
        + a * (Multiplicative.toAdd x).1 = (Multiplicative.toAdd x).2
      ring
  map_mul' x y := by
    apply Multiplicative.toAdd.injective; apply Prod.ext
    · rfl
    · change ((Multiplicative.toAdd x).2 + (Multiplicative.toAdd y).2)
          + a * ((Multiplicative.toAdd x).1 + (Multiplicative.toAdd y).1)
        = ((Multiplicative.toAdd x).2 + a * (Multiplicative.toAdd x).1)
          + ((Multiplicative.toAdd y).2 + a * (Multiplicative.toAdd y).1)
      ring

/-- The automorphism associated with the zero parameter is the identity. -/
@[simp] lemma residuePairMulAut_zero : residuePairMulAut p 0 = 1 := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.one_apply]
  apply Multiplicative.toAdd.injective
  change ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2 + 0 * (Multiplicative.toAdd x).1)
      = Multiplicative.toAdd x
  apply Prod.ext
  · rfl
  · change (Multiplicative.toAdd x).2 + 0 * (Multiplicative.toAdd x).1 = (Multiplicative.toAdd x).2
    ring

/-- The automorphism associated with a sum of parameters is the product of the corresponding automorphisms. -/
lemma residuePairMulAut_add (a a' : ZMod p) :
    residuePairMulAut p (a + a') = residuePairMulAut p a * residuePairMulAut p a' := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply]
  apply Multiplicative.toAdd.injective
  change ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2 + (a + a') * (Multiplicative.toAdd x).1)
      = ((Multiplicative.toAdd x).1,
          (Multiplicative.toAdd x).2 + a' * (Multiplicative.toAdd x).1 + a * (Multiplicative.toAdd x).1)
  apply Prod.ext
  · rfl
  · change (Multiplicative.toAdd x).2 + (a + a') * (Multiplicative.toAdd x).1
        = (Multiplicative.toAdd x).2 + a' * (Multiplicative.toAdd x).1
          + a * ((Multiplicative.toAdd x).1)
    ring

/-- The monoid homomorphism from multiplicative residues to automorphisms of multiplicative residue pairs given by shears. -/
def shearAction : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod p × ZMod p)) where
  toFun a := residuePairMulAut p (Multiplicative.toAdd a)
  map_one' := by
    change residuePairMulAut p (0 : ZMod p) = 1
    exact residuePairMulAut_zero p
  map_mul' a a' := by
    change residuePairMulAut p (Multiplicative.toAdd a + Multiplicative.toAdd a')
      = residuePairMulAut p (Multiplicative.toAdd a) * residuePairMulAut p (Multiplicative.toAdd a')
    exact residuePairMulAut_add p _ _

/-- An auxiliary type indexed by a prime natural number. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
abbrev AuxiliaryType : Type := Multiplicative (ZMod p × ZMod p) ⋊[shearAction p] Multiplicative (ZMod p)


/-- A natural number equipped with a primality fact is nonzero. -/
instance primeFact_neZero : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- A complex unit forming a primitive root of prime order. -/
noncomputable def primitiveRootUnit : ℂˣ :=
  ((Complex.isPrimitiveRoot_exp p (NeZero.ne p)).isUnit (NeZero.ne p)).unit

/-- The distinguished complex unit is a primitive root of the prime order. -/
lemma primitiveRootUnit_isPrimitiveRoot : IsPrimitiveRoot (primitiveRootUnit p) p :=
  IsPrimitiveRoot.isUnit_unit (NeZero.ne p) (Complex.isPrimitiveRoot_exp p (NeZero.ne p))

/-- The additive homomorphism taking a pair of residues to a weighted sum of its coordinates. -/
def weightedCoordinateHom (β γ : ZMod p) : ZMod p × ZMod p →+ ZMod p :=
  (AddMonoidHom.mulLeft β).comp (AddMonoidHom.fst (ZMod p) (ZMod p)) +
    (AddMonoidHom.mulLeft γ).comp (AddMonoidHom.snd (ZMod p) (ZMod p))

/-- The weighted coordinate homomorphism evaluates to the sum of the two coefficient-coordinate products. -/
@[simp] lemma weightedCoordinateHom_apply (β γ : ZMod p) (bc : ZMod p × ZMod p) :
    weightedCoordinateHom p β γ bc = β * bc.1 + γ * bc.2 := rfl

/-- A unit-valued additive character on pairs of residues, parametrized by two residues. -/
noncomputable def pairAddChar (β γ : ZMod p) : AddChar (ZMod p × ZMod p) ℂˣ :=
  (AddChar.zmodChar p (primitiveRootUnit_isPrimitiveRoot p).pow_eq_one).compAddMonoidHom
    (weightedCoordinateHom p β γ)

/-- A unit-valued monoid homomorphism on multiplicative pairs of residues determined by two parameters. -/
noncomputable def pairUnitChar (β γ : ZMod p) : Multiplicative (ZMod p × ZMod p) →* ℂˣ :=
  AddChar.toMonoidHomEquiv (pairAddChar p β γ)

/-- The pair character at a residue pair is the distinguished unit raised to the corresponding weighted exponent. -/
lemma pairUnitChar_apply (β γ : ZMod p) (b c : ZMod p) :
    pairUnitChar p β γ (Multiplicative.ofAdd (b, c)) =
      primitiveRootUnit p ^ (β * b + γ * c).val := by
  rfl

/-- A shear fixes the first coordinate and adds the parameter times the first coordinate to the second. -/
lemma shearAction_apply (a : Multiplicative (ZMod p)) (b c : ZMod p) :
    (shearAction p a : MulAut _) (Multiplicative.ofAdd (b, c))
      = Multiplicative.ofAdd (b, c + Multiplicative.toAdd a * b) := rfl

/-- Precomposition by an inverse shear replaces the first character parameter by its difference with the shear parameter times the second. -/
lemma pairUnitChar_comp_shearAction (g : Multiplicative (ZMod p)) (β γ : ZMod p) :
    (pairUnitChar p β γ).comp (shearAction p g⁻¹ : MulAut _).toMonoidHom
      = pairUnitChar p (β - Multiplicative.toAdd g * γ) γ := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨b, c, rfl⟩ : ∃ b c, x = Multiplicative.ofAdd (b, c) :=
    ⟨(Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2, rfl⟩
  have hexp : β * b + γ * (c + Multiplicative.toAdd g⁻¹ * b)
      = (β - Multiplicative.toAdd g * γ) * b + γ * c := by
    rw [toAdd_inv]; ring
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, shearAction_apply,
    pairUnitChar_apply, hexp]

/-- Equal pair characters have equal first and second parameters. -/
lemma pairUnitChar_parameters_eq {β γ β' γ' : ZMod p}
    (h : pairUnitChar p β γ = pairUnitChar p β' γ') : β = β' ∧ γ = γ' := by
  have h1 := DFunLike.congr_fun h (Multiplicative.ofAdd (1, 0))
  have h2 := DFunLike.congr_fun h (Multiplicative.ofAdd (0, 1))
  rw [pairUnitChar_apply, pairUnitChar_apply] at h1 h2
  simp only [mul_one, mul_zero, add_zero, zero_add] at h1 h2
  exact ⟨ZMod.val_injective p
      ((primitiveRootUnit_isPrimitiveRoot p).pow_inj (ZMod.val_lt β) (ZMod.val_lt β') h1),
    ZMod.val_injective p
      ((primitiveRootUnit_isPrimitiveRoot p).pow_inj (ZMod.val_lt γ) (ZMod.val_lt γ') h2)⟩

/-- The parametrization of pair characters by pairs of residues is injective. -/
lemma pairUnitChar_injective :
    Function.Injective (fun bg : ZMod p × ZMod p => pairUnitChar p bg.1 bg.2) := by
  rintro ⟨β, γ⟩ ⟨β', γ'⟩ h
  obtain ⟨hβ, hγ⟩ := pairUnitChar_parameters_eq p h
  exact Prod.ext hβ hγ

/-- A pair character is invariant under every inverse shear exactly when its second parameter is zero. -/
lemma pairUnitChar_shearInvariant_iff (β γ : ZMod p) :
    (∀ g : Multiplicative (ZMod p),
      (pairUnitChar p β γ).comp (shearAction p g⁻¹ : MulAut _).toMonoidHom
        = pairUnitChar p β γ) ↔ γ = 0 := by
  constructor
  · intro hfix
    have hg1 := hfix (Multiplicative.ofAdd 1)
    rw [pairUnitChar_comp_shearAction] at hg1
    obtain ⟨h, -⟩ := pairUnitChar_parameters_eq p hg1
    simp only [toAdd_ofAdd, one_mul, sub_eq_self] at h
    exact h
  · rintro rfl g
    rw [pairUnitChar_comp_shearAction]
    simp

/-- A pair character with nonzero second parameter has trivial stabilizer under inverse shears. -/
lemma pairUnitChar_shearStabilizer_eq_one (β γ : ZMod p) (hγ : γ ≠ 0)
    (g : Multiplicative (ZMod p))
    (hg : (pairUnitChar p β γ).comp (shearAction p g⁻¹ : MulAut _).toMonoidHom
      = pairUnitChar p β γ) :
    g = 1 := by
  rw [pairUnitChar_comp_shearAction] at hg
  obtain ⟨h, -⟩ := pairUnitChar_parameters_eq p hg
  have hz : Multiplicative.toAdd g * γ = 0 := sub_eq_self.mp h
  have htg : Multiplicative.toAdd g = 0 := (mul_eq_zero.mp hz).resolve_right hγ
  apply Multiplicative.toAdd.injective
  rw [htg]; rfl

/-- Every unit-valued monoid homomorphism on multiplicative residue pairs is represented by two residue parameters. -/
lemma exists_pairUnitChar_eq (χ : Multiplicative (ZMod p × ZMod p) →* ℂˣ) :
    ∃ β γ, pairUnitChar p β γ = χ := by
  classical
  haveI : Fintype (Multiplicative (ZMod p × ZMod p) →* ℂˣ) := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod p × ZMod p)
      = Fintype.card (Multiplicative (ZMod p × ZMod p) →* ℂˣ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      RepresentationTheory.ComplexUnitCharacters.natCard_complexUnitCharacters_eq]
    exact (Nat.card_congr Multiplicative.ofAdd)
  have hbij := (Fintype.bijective_iff_injective_and_card
    (fun bg : ZMod p × ZMod p => pairUnitChar p bg.1 bg.2)).mpr
    ⟨pairUnitChar_injective p, hcard⟩
  obtain ⟨bg, hbg⟩ := hbij.surjective χ
  exact ⟨bg.1, bg.2, hbg⟩


/-- The distinguished complex unit raised to the prime exponent is one. -/
lemma primitiveRootUnit_pow_prime : ((primitiveRootUnit p : ℂ)) ^ p = 1 := by
  have h := (primitiveRootUnit_isPrimitiveRoot p).pow_eq_one
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

/-- The complex value of the distinguished unit is a primitive root of the prime order. -/
lemma primitiveRootUnit_val_isPrimitiveRoot : IsPrimitiveRoot ((primitiveRootUnit p : ℂ)) p :=
  IsPrimitiveRoot.coe_units_iff.mpr (primitiveRootUnit_isPrimitiveRoot p)

/-- A complex-valued additive character on residues modulo a prime. -/
noncomputable def primitiveAddChar : AddChar (ZMod p) ℂ :=
  AddChar.zmodChar p (primitiveRootUnit_pow_prime p)

/-- The additive character at a residue is the distinguished complex unit raised to its natural representative. -/
lemma primitiveAddChar_apply (x : ZMod p) : primitiveAddChar p x = (primitiveRootUnit p : ℂ) ^ x.val :=
  AddChar.zmodChar_apply _ x

/-- The complex-valued additive character on prime residues is primitive. -/
lemma primitiveAddChar_isPrimitive : (primitiveAddChar p).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root p (primitiveRootUnit_val_isPrimitiveRoot p)

/-- The complex value of the pair character is the primitive additive character of the weighted coordinate sum. -/
lemma pairUnitChar_val (β γ b c : ZMod p) :
    ((pairUnitChar p β γ (Multiplicative.ofAdd (b, c)) : ℂˣ) : ℂ)
      = primitiveAddChar p (β * b + γ * c) := by
  rw [pairUnitChar_apply, Units.val_pow_eq_pow_val, primitiveAddChar_apply]

/-- Summing a pair character along all shears yields the original value multiplied by the prime when the indicated product vanishes, and zero otherwise. -/
lemma sum_pairUnitChar_shear (β γ b c : ZMod p) :
    ∑ h : Multiplicative (ZMod p),
      ((pairUnitChar p β γ
        (Multiplicative.ofAdd (b, c + Multiplicative.toAdd h * b)) : ℂˣ) : ℂ)
    = (if γ * b = 0 then (p : ℂ) else 0) *
        ((pairUnitChar p β γ (Multiplicative.ofAdd (b, c)) : ℂˣ) : ℂ) := by
  have hterm : ∀ h : Multiplicative (ZMod p),
      ((pairUnitChar p β γ
        (Multiplicative.ofAdd (b, c + Multiplicative.toAdd h * b)) : ℂˣ) : ℂ)
        = primitiveAddChar p (β * b + γ * c) *
            primitiveAddChar p (γ * b * Multiplicative.toAdd h) := by
    intro h
    rw [pairUnitChar_val,
      show β * b + γ * (c + Multiplicative.toAdd h * b)
        = (β * b + γ * c) + (γ * b * Multiplicative.toAdd h) from by ring,
      AddChar.map_add_eq_mul]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hreindex : ∑ h : Multiplicative (ZMod p),
        primitiveAddChar p (γ * b * Multiplicative.toAdd h)
      = ∑ t : ZMod p, primitiveAddChar p (t * (γ * b)) :=
    Fintype.sum_equiv (Multiplicative.toAdd (α := ZMod p)) _ _ (fun h => by rw [mul_comm])
  rw [hreindex, AddChar.sum_mulShift (γ * b) (primitiveAddChar_isPrimitive p), ZMod.card,
    pairUnitChar_val]
  push_cast
  ring

open Classical in
/-- There is a complete nonisomorphic family of simple representations of the auxiliary type, with dimensions one or the prime and with the specified counts. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
theorem auxiliaryType_exists_simpleRepresentatives :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (AuxiliaryType p)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (AuxiliaryType p), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      (∀ i, finrank ℂ (W i : Type) = 1 ∨ finrank ℂ (W i : Type) = p) ∧
      n = p ^ 2 + (p - 1) ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = p ^ 2 ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = p)).card = p - 1 := by
  classical
  obtain ⟨dualSmul, hdual, stab, hstab, V, transport, hi, hii, hiii, hiv, hv, hvi, _, _, _⟩ :=
    RepresentationTheory.AuxiliaryRepresentationIsomorphisms.auxiliary_theorem (Multiplicative (ZMod p)) (Multiplicative (ZMod p × ZMod p))
      (shearAction p)
  have hdualhb : ∀ (g : Multiplicative (ZMod p)) (β γ : ZMod p),
      dualSmul g (pairUnitChar p β γ)
        = pairUnitChar p (β - Multiplicative.toAdd g * γ) γ := by
    intro g β γ
    refine MonoidHom.ext fun a => ?_
    exact (hdual g (pairUnitChar p β γ) a).trans
      (DFunLike.congr_fun (pairUnitChar_comp_shearAction p g β γ) a)
  have hstab_f : ∀ β : ZMod p, stab (pairUnitChar p β 0) = ⊤ := by
    intro β
    rw [eq_top_iff]
    intro g _
    rw [hstab (pairUnitChar p β 0) g, hdualhb]
    simp
  have hstab_r : ∀ (β γ : ZMod p), γ ≠ 0 → stab (pairUnitChar p β γ) = ⊥ := by
    intro β γ hγ
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    rw [hstab (pairUnitChar p β γ) g, hdualhb] at hg
    obtain ⟨h1, -⟩ := pairUnitChar_parameters_eq p hg
    have hz : Multiplicative.toAdd g * γ = 0 := sub_eq_self.mp h1
    have htg : Multiplicative.toAdd g = 0 := (mul_eq_zero.mp hz).resolve_right hγ
    exact Multiplicative.toAdd.injective (by rw [htg]; rfl)
  have hconj : ∀ (h g : Multiplicative (ZMod p)), h * g * h⁻¹ = g := by
    intro h g; rw [mul_right_comm, mul_inv_cancel, one_mul]
  have hcardG : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_eq_fintype_card, ZMod.card]
  haveI : Fintype (Multiplicative (ZMod p) →* ℂˣ) := Fintype.ofFinite _
  haveI : Finite (AuxiliaryType p) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have fixed_charρ : ∀ (β : ZMod p) (ρ : Multiplicative (ZMod p) →* ℂˣ)
      (b c : ZMod p) (g : Multiplicative (ZMod p)),
      (V (pairUnitChar p β 0)
        (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
          (ρ.comp (stab (pairUnitChar p β 0)).subtype))).character
          ⟨Multiplicative.ofAdd (b, c), g⟩
      = ((ρ g : ℂˣ) : ℂ) * (primitiveRootUnit p : ℂ) ^ (β * b).val := by
    intro β ρ b c g
    have hSimpleU := RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter
      (ρ.comp (stab (pairUnitChar p β 0)).subtype)
    have hmemg : g ∈ stab (pairUnitChar p β 0) := by rw [hstab_f β]; exact Subgroup.mem_top g
    have hmemall : ∀ h : Multiplicative (ZMod p), h * g * h⁻¹ ∈ stab (pairUnitChar p β 0) := by
      intro h; rw [hstab_f β]; exact Subgroup.mem_top _
    have hcard : Fintype.card ↥(stab (pairUnitChar p β 0)) = p := by
      rw [← Nat.card_eq_fintype_card, hstab_f β, Nat.card_congr Subgroup.topEquiv.toEquiv, hcardG]
    have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).pos.ne'
    have hterm : ∀ h : Multiplicative (ZMod p),
        (if hh : h * g * h⁻¹ ∈ stab (pairUnitChar p β 0)
          then ((pairUnitChar p β 0
                ((shearAction p h : MulAut _) (Multiplicative.ofAdd (b, c))) : ℂˣ) : ℂ)
              * (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
                  (ρ.comp (stab (pairUnitChar p β 0)).subtype)).character ⟨h * g * h⁻¹, hh⟩
          else 0)
        = ((ρ g : ℂˣ) : ℂ)
            * ((pairUnitChar p β 0
                (Multiplicative.ofAdd (b, c + Multiplicative.toAdd h * b)) : ℂˣ) : ℂ) := by
      intro h
      rw [dif_pos (hmemall h),
        show (⟨h * g * h⁻¹, hmemall h⟩ : ↥(stab (pairUnitChar p β 0))) = ⟨g, hmemg⟩ from
          Subtype.ext (hconj h g),
        RepresentationTheory.ComplexUnitCharacters.character_fdRepOfComplexUnitCharacter, shearAction_apply,
        show ((ρ.comp (stab (pairUnitChar p β 0)).subtype) ⟨g, hmemg⟩ : ℂˣ) = ρ g from rfl,
        mul_comm]
    rw [hiv (pairUnitChar p β 0) _ hSimpleU (Multiplicative.ofAdd (b, c)) g,
      Finset.sum_congr rfl (fun h _ => hterm h), ← Finset.mul_sum, sum_pairUnitChar_shear, hcard,
      zero_mul, if_pos rfl, pairUnitChar_apply, Units.val_pow_eq_pow_val,
      show β * b + 0 * c = β * b from by ring]
    field_simp
  have free_char : ∀ (β γ : ZMod p), γ ≠ 0 → ∀ (b c : ZMod p) (g : Multiplicative (ZMod p)),
      (V (pairUnitChar p β γ)
        (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
          (1 : ↥(stab (pairUnitChar p β γ)) →* ℂˣ))).character
          ⟨Multiplicative.ofAdd (b, c), g⟩
      = if g = 1 ∧ b = 0 then (p : ℂ) * (primitiveRootUnit p : ℂ) ^ (γ * c).val else 0 := by
    intro β γ hγ b c g
    have hSimpleU := RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter
      (1 : ↥(stab (pairUnitChar p β γ)) →* ℂˣ)
    have hcard1 : Fintype.card ↥(stab (pairUnitChar p β γ)) = 1 := by
      rw [← Nat.card_eq_fintype_card, hstab_r β γ hγ]; exact Subgroup.card_bot
    rw [hiv (pairUnitChar p β γ) _ hSimpleU (Multiplicative.ofAdd (b, c)) g, hcard1]
    simp only [Nat.cast_one, inv_one, one_mul]
    by_cases hg : g = 1
    · subst hg
      have hterm : ∀ h : Multiplicative (ZMod p),
          (if hh : h * 1 * h⁻¹ ∈ stab (pairUnitChar p β γ)
            then ((pairUnitChar p β γ
                  ((shearAction p h : MulAut _) (Multiplicative.ofAdd (b, c))) : ℂˣ) : ℂ)
                * (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
                    (1 : ↥(stab (pairUnitChar p β γ)) →* ℂˣ)).character ⟨h * 1 * h⁻¹, hh⟩
            else 0)
          = ((pairUnitChar p β γ
              (Multiplicative.ofAdd (b, c + Multiplicative.toAdd h * b)) : ℂˣ) : ℂ) := by
        intro h
        have hmem : h * 1 * h⁻¹ ∈ stab (pairUnitChar p β γ) := by
          rw [hconj, hstab_r β γ hγ]; exact Subgroup.one_mem _
        rw [dif_pos hmem, RepresentationTheory.ComplexUnitCharacters.character_fdRepOfComplexUnitCharacter, MonoidHom.one_apply,
          Units.val_one, mul_one, shearAction_apply]
      rw [Finset.sum_congr rfl (fun h _ => hterm h), sum_pairUnitChar_shear]
      by_cases hb : b = 0
      · subst hb
        rw [mul_zero, if_pos rfl, if_pos ⟨rfl, rfl⟩, pairUnitChar_apply,
          Units.val_pow_eq_pow_val, show β * 0 + γ * c = γ * c from by ring]
      · rw [if_neg (fun h => hb ((mul_eq_zero.mp h).resolve_left hγ)),
          if_neg (fun h => hb h.2), zero_mul]
    · have hterm0 : ∀ h : Multiplicative (ZMod p),
          (if hh : h * g * h⁻¹ ∈ stab (pairUnitChar p β γ)
            then ((pairUnitChar p β γ
                  ((shearAction p h : MulAut _) (Multiplicative.ofAdd (b, c))) : ℂˣ) : ℂ)
                * (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
                    (1 : ↥(stab (pairUnitChar p β γ)) →* ℂˣ)).character ⟨h * g * h⁻¹, hh⟩
            else 0) = 0 := by
        intro h
        rw [dif_neg]
        intro hmem
        rw [hconj, hstab_r β γ hγ, Subgroup.mem_bot] at hmem
        exact hg hmem
      rw [Finset.sum_congr rfl (fun h _ => hterm0 h), Finset.sum_const_zero,
        if_neg (fun h => hg h.1)]
  let ι := (ZMod p × (Multiplicative (ZMod p) →* ℂˣ)) ⊕ {γ : ZMod p // γ ≠ 0}
  let F : ι → FDRep ℂ (AuxiliaryType p) :=
    Sum.elim
      (fun x => V (pairUnitChar p x.1 0)
        (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (x.2.comp (stab (pairUnitChar p x.1 0)).subtype)))
      (fun y => V (pairUnitChar p 0 y.1)
        (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter (1 : ↥(stab (pairUnitChar p 0 y.1)) →* ℂˣ)))
  have hFsimple : ∀ a : ι, Simple (F a) := by
    rintro (⟨β, ρ⟩ | ⟨γ, hγ⟩)
    · exact hi _ _ (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _)
    · exact hi _ _ (RepresentationTheory.ComplexUnitCharacters.simple_fdRepOfComplexUnitCharacter _)
  have hFdim1 : ∀ (β : ZMod p) (ρ : Multiplicative (ZMod p) →* ℂˣ),
      finrank ℂ (F (Sum.inl (β, ρ)) : Type) = 1 := by
    intro β ρ
    change finrank ℂ (V (pairUnitChar p β 0) _ : Type) = 1
    rw [hv, hstab_f β, Subgroup.index_top, RepresentationTheory.ComplexUnitCharacters.finrank_fdRepOfComplexUnitCharacter, mul_one]
  have hFdimp : ∀ (γ : ZMod p) (hγ : γ ≠ 0),
      finrank ℂ (F (Sum.inr ⟨γ, hγ⟩) : Type) = p := by
    intro γ hγ
    change finrank ℂ (V (pairUnitChar p 0 γ) _ : Type) = p
    rw [hv, hstab_r 0 γ hγ, Subgroup.index_bot, RepresentationTheory.ComplexUnitCharacters.finrank_fdRepOfComplexUnitCharacter, mul_one,
      hcardG]
  have hFdim : ∀ a : ι, finrank ℂ (F a : Type) = 1 ∨ finrank ℂ (F a : Type) = p := by
    rintro (⟨β, ρ⟩ | ⟨γ, hγ⟩)
    · exact Or.inl (hFdim1 β ρ)
    · exact Or.inr (hFdimp γ hγ)
  have hFinj : ∀ a b : ι, Nonempty (F a ≅ F b) → a = b := by
    rintro (⟨β, ρ⟩ | ⟨γ, hγ⟩) (⟨β', ρ'⟩ | ⟨γ', hγ'⟩) ⟨α⟩
    · -- fixed vs fixed: distinguish `β` (via `(1,0,1)`) and `ρ` (via `(0,0,g)`)
      have hchar := FDRep.char_iso α
      have hρ : ρ = ρ' := by
        refine MonoidHom.ext fun g => ?_
        have e1 : (F (Sum.inl (β, ρ))).character
              (⟨Multiplicative.ofAdd ((0 : ZMod p), (0 : ZMod p)), g⟩ : AuxiliaryType p)
            = ((ρ g : ℂˣ) : ℂ) * (primitiveRootUnit p : ℂ) ^ (β * (0 : ZMod p)).val :=
          fixed_charρ β ρ 0 0 g
        have e2 : (F (Sum.inl (β', ρ'))).character
              (⟨Multiplicative.ofAdd ((0 : ZMod p), (0 : ZMod p)), g⟩ : AuxiliaryType p)
            = ((ρ' g : ℂˣ) : ℂ) * (primitiveRootUnit p : ℂ) ^ (β' * (0 : ZMod p)).val :=
          fixed_charρ β' ρ' 0 0 g
        have h0 := congrFun hchar
          (⟨Multiplicative.ofAdd ((0 : ZMod p), (0 : ZMod p)), g⟩ : AuxiliaryType p)
        rw [e1, e2] at h0
        simp only [mul_zero, ZMod.val_zero, pow_zero, mul_one] at h0
        exact Units.ext h0
      have hβ : β = β' := by
        have e1 : (F (Sum.inl (β, ρ))).character
              (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
                (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
            = ((ρ 1 : ℂˣ) : ℂ) * (primitiveRootUnit p : ℂ) ^ (β * (1 : ZMod p)).val :=
          fixed_charρ β ρ 1 0 1
        have e2 : (F (Sum.inl (β', ρ'))).character
              (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
                (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
            = ((ρ' 1 : ℂˣ) : ℂ) * (primitiveRootUnit p : ℂ) ^ (β' * (1 : ZMod p)).val :=
          fixed_charρ β' ρ' 1 0 1
        have h1 := congrFun hchar
          (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
            (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
        rw [e1, e2] at h1
        simp only [map_one, Units.val_one, one_mul, mul_one] at h1
        exact ZMod.val_injective p
          ((primitiveRootUnit_val_isPrimitiveRoot p).pow_inj (ZMod.val_lt β) (ZMod.val_lt β') h1)
      exact congrArg Sum.inl (Prod.ext hβ hρ)
    · -- fixed vs free: impossible (`ζ^(β.val) ≠ 0` but free char there is `0`)
      exfalso
      have hchar := FDRep.char_iso α
      have e1 : (F (Sum.inl (β, ρ))).character
            (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
          = ((ρ 1 : ℂˣ) : ℂ) * (primitiveRootUnit p : ℂ) ^ (β * (1 : ZMod p)).val :=
        fixed_charρ β ρ 1 0 1
      have e2 : (F (Sum.inr ⟨γ', hγ'⟩)).character
            (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
          = if (1 : Multiplicative (ZMod p)) = 1 ∧ (1 : ZMod p) = 0
              then (p : ℂ) * (primitiveRootUnit p : ℂ) ^ (γ' * (0 : ZMod p)).val else 0 :=
        free_char 0 γ' hγ' 1 0 1
      have h1 := congrFun hchar
        (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
          (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
      rw [e1, e2, if_neg (fun h => one_ne_zero h.2)] at h1
      simp only [map_one, Units.val_one, one_mul, mul_one] at h1
      exact pow_ne_zero _ (Units.ne_zero (primitiveRootUnit p)) h1
    · -- free vs fixed: symmetric impossibility
      exfalso
      have hchar := FDRep.char_iso α
      have e1 : (F (Sum.inr ⟨γ, hγ⟩)).character
            (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
          = if (1 : Multiplicative (ZMod p)) = 1 ∧ (1 : ZMod p) = 0
              then (p : ℂ) * (primitiveRootUnit p : ℂ) ^ (γ * (0 : ZMod p)).val else 0 :=
        free_char 0 γ hγ 1 0 1
      have e2 : (F (Sum.inl (β', ρ'))).character
            (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
          = ((ρ' 1 : ℂˣ) : ℂ) * (primitiveRootUnit p : ℂ) ^ (β' * (1 : ZMod p)).val :=
        fixed_charρ β' ρ' 1 0 1
      have h1 := congrFun hchar
        (⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)),
          (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
      rw [e1, e2, if_neg (fun h => one_ne_zero h.2)] at h1
      simp only [map_one, Units.val_one, one_mul, mul_one] at h1
      exact pow_ne_zero _ (Units.ne_zero (primitiveRootUnit p)) h1.symm
    · -- free vs free: distinguish `γ` (via `(0,1,1)`)
      have hchar := FDRep.char_iso α
      have e1 : (F (Sum.inr ⟨γ, hγ⟩)).character
            (⟨Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
          = if (1 : Multiplicative (ZMod p)) = 1 ∧ (0 : ZMod p) = 0
              then (p : ℂ) * (primitiveRootUnit p : ℂ) ^ (γ * (1 : ZMod p)).val else 0 :=
        free_char 0 γ hγ 0 1 1
      have e2 : (F (Sum.inr ⟨γ', hγ'⟩)).character
            (⟨Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)),
              (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
          = if (1 : Multiplicative (ZMod p)) = 1 ∧ (0 : ZMod p) = 0
              then (p : ℂ) * (primitiveRootUnit p : ℂ) ^ (γ' * (1 : ZMod p)).val else 0 :=
        free_char 0 γ' hγ' 0 1 1
      have h1 := congrFun hchar
        (⟨Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)),
          (1 : Multiplicative (ZMod p))⟩ : AuxiliaryType p)
      rw [e1, e2, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, mul_one, mul_one] at h1
      have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).pos.ne'
      have h2 := mul_left_cancel₀ hp h1
      exact congrArg Sum.inr (Subtype.ext (ZMod.val_injective p
        ((primitiveRootUnit_val_isPrimitiveRoot p).pow_inj (ZMod.val_lt γ) (ZMod.val_lt γ') h2)))
  have hFcomplete : ∀ S : FDRep ℂ (AuxiliaryType p), Simple S → ∃ a : ι, Nonempty (S ≅ F a) := by
    intro S hS
    obtain ⟨χ, U, hU, hSU⟩ := hiii S hS
    obtain ⟨β, γ, rfl⟩ := exists_pairUnitChar_eq p χ
    haveI : Simple U := hU
    by_cases hγ : γ = 0
    · -- fixed orbit: `U ≅ charFDRep ξ`, recover `ρ : G →* ℂˣ` from `ξ` (stabilizer is `⊤`)
      subst hγ
      obtain ⟨ξ, hξ⟩ := RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter U
      let eStab : ↥(stab (pairUnitChar p β 0)) ≃* Multiplicative (ZMod p) :=
        (MulEquiv.subgroupCongr (hstab_f β)).trans Subgroup.topEquiv
      have heStab : ∀ s, eStab s = ((stab (pairUnitChar p β 0)).subtype s) := fun s => rfl
      refine ⟨Sum.inl (β, ξ.comp eStab.symm.toMonoidHom), ?_⟩
      have hρξ : (ξ.comp eStab.symm.toMonoidHom).comp
          (stab (pairUnitChar p β 0)).subtype = ξ := by
        refine MonoidHom.ext fun s => ?_
        change ξ (eStab.symm ((stab (pairUnitChar p β 0)).subtype s)) = ξ s
        rw [← heStab s, MulEquiv.symm_apply_apply]
      have hFeq : F (Sum.inl (β, ξ.comp eStab.symm.toMonoidHom))
          = V (pairUnitChar p β 0) (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ) := by
        change V (pairUnitChar p β 0)
            (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
              ((ξ.comp eStab.symm.toMonoidHom).comp (stab (pairUnitChar p β 0)).subtype))
          = V (pairUnitChar p β 0) (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ)
        rw [hρξ]
      rw [hFeq]
      exact ⟨hSU.some ≪≫
        (hvi (pairUnitChar p β 0) U (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter ξ) hξ).some⟩
    · -- free orbit: `U ≅ charFDRep 1`, move base point `χ_{β,γ} ⇝ χ_{0,γ}` via equal characters
      refine ⟨Sum.inr ⟨γ, hγ⟩, ?_⟩
      haveI : Subsingleton ↥(stab (pairUnitChar p β γ)) := by
        rw [hstab_r β γ hγ]
        exact ⟨fun a b => Subtype.ext
          (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
      obtain ⟨ξ, hξ⟩ := RepresentationTheory.ComplexUnitCharacters.simple_fdRep_iso_fdRepOfComplexUnitCharacter U
      have hξ1 : ξ = 1 := by
        refine MonoidHom.ext fun x => ?_
        rw [Subsingleton.elim x 1]; simp
      rw [hξ1] at hξ
      have hchareq : (V (pairUnitChar p β γ)
            (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
              (1 : ↥(stab (pairUnitChar p β γ)) →* ℂˣ))).character
          = (V (pairUnitChar p 0 γ)
            (RepresentationTheory.ComplexUnitCharacters.fdRepOfComplexUnitCharacter
              (1 : ↥(stab (pairUnitChar p 0 γ)) →* ℂˣ))).character := by
        funext x
        obtain ⟨a, gg⟩ := x
        obtain ⟨b, c, rfl⟩ : ∃ b c, a = Multiplicative.ofAdd (b, c) :=
          ⟨(Multiplicative.toAdd a).1, (Multiplicative.toAdd a).2, rfl⟩
        rw [free_char β γ hγ b c gg, free_char 0 γ hγ b c gg]
      exact ⟨hSU.some ≪≫ (hvi (pairUnitChar p β γ) U _ hξ).some
        ≪≫ (RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq _ _ hchareq).some⟩
  have hcardHom : Fintype.card (Multiplicative (ZMod p) →* ℂˣ) = p := by
    rw [← Nat.card_eq_fintype_card, RepresentationTheory.ComplexUnitCharacters.natCard_complexUnitCharacters_eq, hcardG]
  have hcardSub : Fintype.card {γ : ZMod p // γ ≠ 0} = p - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ZMod.card]
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have hleft1 : ∀ x : ZMod p × (Multiplicative (ZMod p) →* ℂˣ),
      (if finrank ℂ (F (Sum.inl x) : Type) = 1 then (1 : ℕ) else 0) = 1 := by
    rintro ⟨β, ρ⟩; rw [if_pos (hFdim1 β ρ)]
  have hright1 : ∀ y : {γ : ZMod p // γ ≠ 0},
      (if finrank ℂ (F (Sum.inr y) : Type) = 1 then (1 : ℕ) else 0) = 0 := by
    rintro ⟨γ, hγ⟩; rw [if_neg fun h => hp1 (by rw [hFdimp γ hγ] at h; exact h)]
  have hleftp : ∀ x : ZMod p × (Multiplicative (ZMod p) →* ℂˣ),
      (if finrank ℂ (F (Sum.inl x) : Type) = p then (1 : ℕ) else 0) = 0 := by
    rintro ⟨β, ρ⟩; rw [if_neg fun h => hp1 (by rw [hFdim1 β ρ] at h; exact h.symm)]
  have hrightp : ∀ y : {γ : ZMod p // γ ≠ 0},
      (if finrank ℂ (F (Sum.inr y) : Type) = p then (1 : ℕ) else 0) = 1 := by
    rintro ⟨γ, hγ⟩; rw [if_pos (hFdimp γ hγ)]
  set e := Fintype.equivFin ι with he
  refine ⟨Fintype.card ι, fun i => F (e.symm i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hFsimple _
  · intro i j hij
    exact e.symm.injective (hFinj _ _ hij)
  · intro S hS
    obtain ⟨a, ha⟩ := hFcomplete S hS
    exact ⟨e a, by simpa only [Equiv.symm_apply_apply] using ha⟩
  · exact fun i => hFdim (e.symm i)
  · have hcard : Fintype.card ι
        = Fintype.card (ZMod p × (Multiplicative (ZMod p) →* ℂˣ))
          + Fintype.card {γ : ZMod p // γ ≠ 0} := Fintype.card_sum
    rw [hcard, Fintype.card_prod, ZMod.card, hcardHom, hcardSub, pow_two]
  · rw [Finset.card_filter,
      Equiv.sum_comp e.symm (fun a => if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0)]
    have hsum : (∑ a : ι, if finrank ℂ (F a : Type) = 1 then (1 : ℕ) else 0)
        = (∑ x : ZMod p × (Multiplicative (ZMod p) →* ℂˣ),
            if finrank ℂ (F (Sum.inl x) : Type) = 1 then (1 : ℕ) else 0)
          + ∑ y : {γ : ZMod p // γ ≠ 0},
            if finrank ℂ (F (Sum.inr y) : Type) = 1 then (1 : ℕ) else 0 :=
      Fintype.sum_sum_type _
    rw [hsum]
    simp only [hleft1, hright1, Finset.sum_const, smul_eq_mul, mul_one,
      mul_zero, add_zero, Finset.card_univ, Fintype.card_prod, ZMod.card, hcardHom, pow_two]
  · rw [Finset.card_filter,
      Equiv.sum_comp e.symm (fun a => if finrank ℂ (F a : Type) = p then (1 : ℕ) else 0)]
    have hsum : (∑ a : ι, if finrank ℂ (F a : Type) = p then (1 : ℕ) else 0)
        = (∑ x : ZMod p × (Multiplicative (ZMod p) →* ℂˣ),
            if finrank ℂ (F (Sum.inl x) : Type) = p then (1 : ℕ) else 0)
          + ∑ y : {γ : ZMod p // γ ≠ 0},
            if finrank ℂ (F (Sum.inr y) : Type) = p then (1 : ℕ) else 0 :=
      Fintype.sum_sum_type _
    rw [hsum]
    simp only [hleftp, hrightp, Finset.sum_const, smul_eq_mul, mul_one,
      mul_zero, zero_add, Finset.card_univ, hcardSub]


/-- An auxiliary multiplicative equivalence between the indicated prime-indexed types. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := supporting)]
def auxiliaryMulEquiv : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p ≃* AuxiliaryType p where
  toFun x := ⟨Multiplicative.ofAdd (x.secondCoordinate, x.thirdCoordinate),
    Multiplicative.ofAdd x.firstCoordinate⟩
  invFun y := ⟨Multiplicative.toAdd y.right, (Multiplicative.toAdd y.left).1,
    (Multiplicative.toAdd y.left).2⟩
  left_inv x := rfl
  right_inv y := rfl
  map_mul' x y := by
    refine SemidirectProduct.ext ?_ rfl
    change Multiplicative.ofAdd
        (x.secondCoordinate + y.secondCoordinate,
          x.thirdCoordinate + y.thirdCoordinate + x.firstCoordinate * y.secondCoordinate)
      = Multiplicative.ofAdd (x.secondCoordinate, x.thirdCoordinate) *
        residuePairMulAut p x.firstCoordinate
          (Multiplicative.ofAdd (y.secondCoordinate, y.thirdCoordinate))
    apply Multiplicative.toAdd.injective
    exact Prod.ext rfl (by
      change x.thirdCoordinate + y.thirdCoordinate + x.firstCoordinate * y.secondCoordinate =
        x.thirdCoordinate + (y.thirdCoordinate + x.firstCoordinate * y.secondCoordinate)
      ring)

/-- The auxiliary equivalence sends an element to the semidirect-product element built from its three displayed components. -/
@[simp] lemma auxiliaryMulEquiv_apply (x : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p) :
    auxiliaryMulEquiv p x =
      ⟨Multiplicative.ofAdd (x.secondCoordinate, x.thirdCoordinate),
        Multiplicative.ofAdd x.firstCoordinate⟩ := rfl

open Classical in
/-- There is a complete nonisomorphic family of simple representations of the auxiliary group, with prime-square one-dimensional members and one fewer than the prime of prime dimension. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := primary)]
theorem auxiliaryGroup_exists_simpleRepresentatives :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      (∀ i, finrank ℂ (W i : Type) = 1 ∨ finrank ℂ (W i : Type) = p) ∧
      n = p ^ 2 + (p - 1) ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = p ^ 2 ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = p)).card = p - 1 := by
  classical
  obtain ⟨n, V, hSimple, hInj, hComplete, hDim, hn, hcard1, hcardp⟩ := auxiliaryType_exists_simpleRepresentatives p
  obtain ⟨W, hW1, hW2, hW3, hWdim⟩ :=
    RepresentationTheory.FiniteDimensional.Equivalences.exists_simple_representatives_preserving_finrank
      (auxiliaryMulEquiv p) V hSimple hInj hComplete
  have hfilt : ∀ d : ℕ, (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = d)) =
      (Finset.univ.filter (fun i => finrank ℂ (V i : Type) = d)) :=
    fun d =>
      RepresentationTheory.FiniteDimensional.Equivalences.filter_univ_finrank_eq_of_forall_eq
        hWdim d
  refine ⟨n, W, hW1, hW2, hW3, fun i => by rw [hWdim i]; exact hDim i, hn, ?_, ?_⟩
  · rw [hfilt]; exact hcard1
  · rw [hfilt]; exact hcardp

open Classical in
/-- A complete family of simple representations of the auxiliary group has the stated dimension counts and is represented by the displayed one-dimensional and prime-dimensional models. -/
@[source_ref "Chapter5/Exercise5.27.2" (role := primary)]
theorem auxiliaryGroup_exists_simpleRepresentatives_with_models :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)),
      (∀ i, Simple (W i)) ∧
      (∀ i j, Nonempty (W i ≅ W j) → i = j) ∧
      (∀ S : FDRep ℂ (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p), Simple S → ∃ i, Nonempty (S ≅ W i)) ∧
      n = p ^ 2 + (p - 1) ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = 1)).card = p ^ 2 ∧
      (Finset.univ.filter (fun i => finrank ℂ (W i : Type) = p)).card = p - 1 ∧
      (∀ i, finrank ℂ (W i : Type) = 1 → ∃ χ : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ,
        Nonempty (W i ≅ FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ))) ∧
      (∀ i, finrank ℂ (W i : Type) = p → ∃ (z : ℂ) (hz : z ^ p = 1), z ≠ 1 ∧
        Nonempty (W i ≅ FDRep.of (RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation z hz))) ∧
      (∀ χ : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ,
        ∃ i, Nonempty (FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ) ≅ W i)) ∧
      (∀ (z : ℂ) (hz : z ^ p = 1), z ≠ 1 →
        ∃ i, Nonempty (FDRep.of (RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation z hz) ≅ W i)) := by
  classical
  obtain ⟨n, W, hSimple, hInj, hComplete, _, hn, hcard1, hcardp⟩ := auxiliaryGroup_exists_simpleRepresentatives p
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  refine ⟨n, W, hSimple, hInj, hComplete, hn, hcard1, hcardp, ?_, ?_, ?_, ?_⟩
  · -- a `1`-dimensional member cannot be an `R_z` (those have dimension `p > 1`)
    intro i hi
    haveI := hSimple i
    rcases RepresentationTheory.ThreeCoordinateGroupRepresentations.simple_representation_iso_character_or_shiftScale (W i) with ⟨χ, hχ⟩ | ⟨z, hz, _, hiso⟩
    · exact ⟨χ, hχ⟩
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hiso.some)
      rw [hi, RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation_finrank z hz] at hfr
      omega
  · -- a `p`-dimensional member cannot be a character (those have dimension `1 < p`)
    intro i hi
    haveI := hSimple i
    rcases RepresentationTheory.ThreeCoordinateGroupRepresentations.simple_representation_iso_character_or_shiftScale (W i) with ⟨χ, hχ⟩ | ⟨z, hz, hz1, hiso⟩
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hχ.some)
      rw [hi, show finrank ℂ (FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ)) = 1 from
        Module.finrank_self ℂ] at hfr
      omega
    · exact ⟨z, hz, hz1, hiso⟩
  · -- every character occurs: it is simple, so completeness catches it
    intro χ
    haveI : Simple (FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ)) :=
      RepresentationTheory.PermutationDegreeThree.simple_representationOfUnitCharacter χ
    exact hComplete _ inferInstance
  · -- every `R_z` with `z ≠ 1` occurs: it is simple by Problem 4.12.2(b)
    intro z hz hz1
    haveI : IsSimpleModule (MonoidAlgebra ℂ (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p))
        (RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation z hz).asModule :=
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation_simple_iff z hz (RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation z hz)
        (RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation_firstGenerator_apply z hz) (RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation_secondGenerator_apply z hz)).mpr hz1
    haveI : Simple (FDRep.of (RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation z hz)) :=
      RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule _
    exact hComplete _ inferInstance

end RepresentationTheory.PrimeFieldShearCharacters
