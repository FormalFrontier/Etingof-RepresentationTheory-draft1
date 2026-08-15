/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FDRep.RegularRepresentationCharacter
import RepresentationTheory.Alignment.Attribute

open scoped Classical
open MonoidAlgebra CategoryTheory

namespace RepresentationTheory.CharacterCoefficientAlgebra

universe u

/-- An auxiliary type attached to a group. -/
abbrev AuxiliaryGroupFunctionType (G : Type u) [Group G] : Type u := MonoidAlgebra ℂ G

/-- Supplies evaluation of an auxiliary group-function element as a complex-valued function on the group. -/
local instance instCoeFunAuxiliaryGroupFunctionType (G : Type u) [Group G] : CoeFun (AuxiliaryGroupFunctionType G) (fun _ => G → ℂ) :=
  ⟨fun f => f.coeff⟩

variable {G : Type u} [Group G]

/-- Identifies the multiplicative unit with the monoid-algebra singleton supported at the identity with value one. -/
theorem one_eq_single_one_one : (1 : AuxiliaryGroupFunctionType G) = single (1 : G) (1 : ℂ) := rfl

section Fintype

variable [Fintype G]

/-- Computes a coefficient of a product as a finite sum of coefficients evaluated at an element and at its inverse translate. -/
@[source_ref "Chapter4/Remark4.5.3" (role := supporting)]
theorem coeff_mul_eq_sum_coeff_mul_coeff_inv_mul (f g : AuxiliaryGroupFunctionType G) (z : G) :
    (f * g) z = ∑ x : G, f x * g (x⁻¹ * z) := by
  have hinj : Function.Injective (fun x : G => (x, x⁻¹ * z)) := by
    intro a b h
    simpa using congrArg Prod.fst h
  rw [MonoidAlgebra.mul_apply_antidiagonal f g z
        (Finset.univ.map ⟨fun x : G => (x, x⁻¹ * z), hinj⟩)]
  · rw [Finset.sum_map]
    rfl
  · rintro ⟨p1, p2⟩
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Prod.mk.injEq]
    constructor
    · rintro ⟨x, rfl, rfl⟩
      group
    · intro hp
      exact ⟨p1, rfl, by rw [← hp]; group⟩

end Fintype

/-- An auxiliary predicate on elements of the group-indexed auxiliary type. -/
def auxiliaryGroupFunctionPredicate (f : AuxiliaryGroupFunctionType G) : Prop :=
  ∀ x y : G, f (y * x * y⁻¹) = f x

/-- An auxiliary complex subalgebra of the monoid algebra of a group. -/
@[source_ref "Chapter4/Remark4.5.3" (role := primary)]
noncomputable def auxiliaryComplexGroupSubalgebra (G : Type u) [Group G] : Subalgebra ℂ (MonoidAlgebra ℂ G) :=
  Subalgebra.center ℂ (MonoidAlgebra ℂ G)

/-- Endows the auxiliary complex group subalgebra with a commutative ring structure. -/
noncomputable instance instCommRingAuxiliaryComplexGroupSubalgebra : CommRing (auxiliaryComplexGroupSubalgebra G) :=
  inferInstanceAs (CommRing (Subalgebra.center ℂ (MonoidAlgebra ℂ G)))

/-- Membership in the auxiliary complex group subalgebra is equivalent to the auxiliary group-function predicate. -/
theorem mem_auxiliaryComplexGroupSubalgebra_iff (f : AuxiliaryGroupFunctionType G) :
    f ∈ auxiliaryComplexGroupSubalgebra G ↔ auxiliaryGroupFunctionPredicate f := by
  simp only [auxiliaryComplexGroupSubalgebra, Subalgebra.mem_center_iff]
  constructor
  ·
    intro h x y
    have happ := congrArg (fun F : AuxiliaryGroupFunctionType G => F (y * x)) (h (single y 1))
    simp only [single_mul_apply, mul_single_apply, one_mul, mul_one] at happ

    rw [show y⁻¹ * (y * x) = x by group] at happ
    exact happ.symm
  ·
    intro h b
    ext z
    rw [mul_apply_left, mul_apply_right]
    refine Finsupp.sum_congr (fun g _ => ?_)

    have hc := h (z * g⁻¹) g⁻¹
    rw [show g⁻¹ * (z * g⁻¹) * g⁻¹⁻¹ = g⁻¹ * z by group] at hc
    rw [mul_comm, hc]

/-- An auxiliary predicate on elements of a ring. -/
def auxiliaryRingElementPredicate {A : Type*} [Ring A] (e : A) : Prop :=
  IsIdempotentElem e ∧ e ≠ 0 ∧
    ∀ a b : A, IsIdempotentElem a → IsIdempotentElem b → a ≠ 0 → b ≠ 0 → e ≠ a + b

variable [Fintype G]

/-- Associates an auxiliary group-function element to a finite-dimensional complex representation. -/
noncomputable def representationAuxiliaryElement (V : FDRep ℂ G) : AuxiliaryGroupFunctionType G :=
  (V.character 1 / (Fintype.card G : ℂ)) • ∑ g : G, V.character g • single g (1 : ℂ)

/-- Computes a coefficient of the auxiliary element associated to a representation as the character value at the identity divided by the group cardinality, multiplied by the character value at the given group element. -/
theorem coeff_representationAuxiliaryElement (V : FDRep ℂ G) (z : G) :
    representationAuxiliaryElement V z = (V.character 1 / (Fintype.card G : ℂ)) * V.character z := by
  unfold representationAuxiliaryElement
  have hsum : (∑ g : G, V.character g • single g (1 : ℂ)) z = V.character z := by
    change (∑ g : G, V.character g • single g (1 : ℂ)).coeff z = V.character z
    rw [MonoidAlgebra.coeff_sum]
    change Finsupp.applyAddHom z
      (∑ g : G, (V.character g • single g (1 : ℂ)).coeff) = V.character z
    rw [map_sum]
    simp [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply]

  have : ((V.character 1 / (Fintype.card G : ℂ)) • ∑ g : G, V.character g • single g (1 : ℂ)) z
      = (V.character 1 / (Fintype.card G : ℂ)) * (∑ g : G, V.character g • single g (1 : ℂ)) z := by
    simp
  rw [this, hsum]

/-- The auxiliary element associated to a representation belongs to the auxiliary complex group subalgebra. -/
theorem representationAuxiliaryElement_mem_auxiliarySubalgebra (V : FDRep ℂ G) :
    representationAuxiliaryElement V ∈ auxiliaryComplexGroupSubalgebra G := by
  rw [mem_auxiliaryComplexGroupSubalgebra_iff]
  intro x y
  rw [coeff_representationAuxiliaryElement, coeff_representationAuxiliaryElement]
  congr 1
  exact V.char_conj x y

/-- Associates to a finite-dimensional complex representation an element of the auxiliary complex group subalgebra. -/
noncomputable def representationSubalgebraElement (V : FDRep ℂ G) : auxiliaryComplexGroupSubalgebra G :=
  ⟨representationAuxiliaryElement V, representationAuxiliaryElement_mem_auxiliarySubalgebra V⟩

private lemma finrank_pos_of_simple (V : FDRep ℂ G) [Simple V] : 0 < Module.finrank ℂ V := by
  by_contra h
  push Not at h
  have h0 : Module.finrank ℂ V = 0 := Nat.le_zero.mp h
  have hsub : Subsingleton V := Module.finrank_zero_iff.mp h0
  have hsub2 : Subsingleton (V ⟶ V) := by
    refine ⟨fun f g => ?_⟩
    exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))
  have e1 : Module.finrank ℂ (V ⟶ V) = 1 := by rw [FDRep.finrank_hom_simple_simple]; simp
  have e0 : Module.finrank ℂ (V ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
  omega

/-- For a simple finite-dimensional complex representation, there is a scalar whose square and products with the associated coefficients recover the stated cardinality ratio and character values. -/
theorem exists_characterCoefficient_scale_of_simple (V : FDRep ℂ G) [Simple V] :
    ∃ c : ℂ, c ^ 2 = (Fintype.card G : ℂ) / representationAuxiliaryElement V 1 ∧
      ∀ g : G, V.character g = c * representationAuxiliaryElement V g := by

  have hd : V.character 1 ≠ 0 := by
    rw [FDRep.char_one]
    exact_mod_cast (finrank_pos_of_simple V).ne'
  have hG : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := G)).ne'

  refine ⟨(Fintype.card G : ℂ) / V.character 1, ?_, ?_⟩
  · rw [coeff_representationAuxiliaryElement]
    field_simp
  · intro g
    rw [coeff_representationAuxiliaryElement]
    field_simp

/-- Expresses the character of a simple representation as the corresponding coefficient multiplied by the group cardinality divided by the representation rank. -/
@[source_ref "Chapter4/Remark4.5.3" (role := primary)]
theorem character_eq_card_div_finrank_mul_coefficient (V : FDRep ℂ G) [Simple V] (g : G) :
    V.character g =
      ((Fintype.card G : ℂ) / (Module.finrank ℂ V : ℂ)) * representationAuxiliaryElement V g := by
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_simple V).ne'
  have hG : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := G)).ne'
  rw [coeff_representationAuxiliaryElement, FDRep.char_one]
  field_simp

private lemma exists_scalar_of_invariant (V : FDRep ℂ G) [Simple V]
    (T : V →ₗ[ℂ] V)
    (hT : T ∈ (Representation.linHom V.ρ V.ρ).invariants) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have h1dim : Module.finrank ℂ (Representation.linHom V.ρ V.ρ).invariants = 1 := by
    rw [LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom V V)]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ V
  have hid_mem : LinearMap.id ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g; ext v
    simp only [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.id_apply]
    change (V.ρ g * V.ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  have hdim_ne : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_simple V).ne'
  have hid_ne : (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff, Submodule.coe_zero]
    intro h
    have : (Module.finrank ℂ V : ℂ) = 0 := by
      rw [← LinearMap.trace_id (R := ℂ) (M := V), h, map_zero]
    exact hdim_ne this
  obtain ⟨c, hc⟩ := ((finrank_eq_one_iff_of_nonzero'
    (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) hid_ne).mp h1dim)
    ⟨T, hT⟩
  refine ⟨c, ?_⟩
  have := congr_arg Subtype.val hc
  simpa using this.symm

private lemma representationAuxiliaryElement_mul_of_auxiliaryGroupFunctionPredicate
    (V : FDRep ℂ G) [Simple V]
    (z : AuxiliaryGroupFunctionType G) (hz : auxiliaryGroupFunctionPredicate z) :
    ∃ σ : ℂ, representationAuxiliaryElement V * z = σ • representationAuxiliaryElement V := by
  set S : V →ₗ[ℂ] V := ∑ y : G, z y • V.ρ y⁻¹ with hSdef

  have hmem : S ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g
    rw [Representation.linHom_apply]
    simp only [← Module.End.mul_eq_comp]
    rw [hSdef, Finset.sum_mul, Finset.mul_sum]
    have hterm : ∀ y : G, V.ρ g * ((z y • V.ρ y⁻¹) * V.ρ g⁻¹) = z y • V.ρ (g * y⁻¹ * g⁻¹) := by
      intro y
      rw [smul_mul_assoc, mul_smul_comm]
      congr 1
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [Finset.sum_congr rfl (fun y _ => hterm y)]
    apply Fintype.sum_equiv ((Equiv.mulLeft g).trans (Equiv.mulRight g⁻¹))
    intro y
    change z y • V.ρ (g * y⁻¹ * g⁻¹) = z (g * y * g⁻¹) • V.ρ ((g * y * g⁻¹)⁻¹)
    rw [hz y g, show (g * y * g⁻¹)⁻¹ = g * y⁻¹ * g⁻¹ by group]
  obtain ⟨σ, hσ⟩ := exists_scalar_of_invariant V S hmem
  refine ⟨σ, ?_⟩
  ext w
  rw [coeff_mul_eq_sum_coeff_mul_coeff_inv_mul]

  have hcore : (∑ x : G, V.character x * z (x⁻¹ * w)) = σ * V.character w := by
    have hreindex : (∑ x : G, V.character x * z (x⁻¹ * w))
        = ∑ y : G, z y * V.character (w * y⁻¹) := by
      apply Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight w))
      intro x
      change V.character x * z (x⁻¹ * w) = z (x⁻¹ * w) * V.character (w * (x⁻¹ * w)⁻¹)
      rw [show w * (x⁻¹ * w)⁻¹ = x by group]
      ring
    have htrace : (∑ y : G, z y * V.character (w * y⁻¹)) = σ * V.character w := by
      have hstep : ∀ y : G, z y * V.character (w * y⁻¹)
          = LinearMap.trace ℂ V (V.ρ w * (z y • V.ρ y⁻¹)) := by
        intro y
        change z y * LinearMap.trace ℂ V (V.ρ (w * y⁻¹)) = _
        rw [map_mul, mul_smul_comm, map_smul, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun y _ => hstep y), ← map_sum, ← Finset.mul_sum,
          ← hSdef, hσ, mul_smul_comm, ← Module.End.one_eq_id, mul_one, map_smul, smul_eq_mul]
      rfl
    rw [hreindex, htrace]
  rw [MonoidAlgebra.smul_apply, smul_eq_mul, coeff_representationAuxiliaryElement]
  simp only [coeff_representationAuxiliaryElement]
  rw [show (∑ x : G, V.character 1 / (Fintype.card G : ℂ) * V.character x * z (x⁻¹ * w))
        = V.character 1 / (Fintype.card G : ℂ) * ∑ x : G, V.character x * z (x⁻¹ * w) from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)]
  rw [hcore]
  ring

/-- The subalgebra element associated to a simple representation satisfies the auxiliary ring-element predicate. -/
theorem auxiliaryRingElementPredicate_representationSubalgebraElement_of_simple (V : FDRep ℂ G) [Simple V] :
    auxiliaryRingElementPredicate (representationSubalgebraElement V) := by
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd : V.character 1 ≠ 0 := by
    rw [FDRep.char_one]; exact_mod_cast (finrank_pos_of_simple V).ne'

  have he1 : representationAuxiliaryElement V 1 ≠ 0 := by
    rw [coeff_representationAuxiliaryElement]; exact mul_ne_zero (div_ne_zero hd hG) hd
  have hne : representationAuxiliaryElement V ≠ 0 := fun h => he1 (by rw [h]; rfl)

  have hclass : auxiliaryGroupFunctionPredicate (representationAuxiliaryElement V) :=
    (mem_auxiliaryComplexGroupSubalgebra_iff (representationAuxiliaryElement V)).mp (representationAuxiliaryElement_mem_auxiliarySubalgebra V)
  obtain ⟨σ0, hσ0⟩ :=
    representationAuxiliaryElement_mul_of_auxiliaryGroupFunctionPredicate V
      (representationAuxiliaryElement V) hclass
  have hval1 : (representationAuxiliaryElement V * representationAuxiliaryElement V) 1 = representationAuxiliaryElement V 1 := by
    rw [coeff_mul_eq_sum_coeff_mul_coeff_inv_mul]
    have hterm : ∀ x : G, representationAuxiliaryElement V x * representationAuxiliaryElement V (x⁻¹ * 1)
        = (V.character 1 / (Fintype.card G : ℂ)) ^ 2 * (V.character x * V.character x⁻¹) := by
      intro x; rw [mul_one, coeff_representationAuxiliaryElement, coeff_representationAuxiliaryElement]; ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
    have horth := FDRep.char_orthonormal V V
    rw [if_pos ⟨Iso.refl V⟩] at horth
    have hsum : (∑ g : G, V.character g * V.character g⁻¹) = (Fintype.card G : ℂ) := by
      have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have horth' : (Fintype.card G : ℂ)⁻¹ *
          ∑ g : G, V.character g * V.character g⁻¹ = 1 := by
        simpa only [Nat.card_eq_fintype_card] using horth
      calc
        _ = (Fintype.card G : ℂ) *
            ((Fintype.card G : ℂ)⁻¹ * ∑ g : G, V.character g * V.character g⁻¹) := by
              field_simp
        _ = (Fintype.card G : ℂ) := by rw [horth', mul_one]
    rw [hsum, coeff_representationAuxiliaryElement]
    field_simp
  have hidem : representationAuxiliaryElement V * representationAuxiliaryElement V = representationAuxiliaryElement V := by
    have hcoef : representationAuxiliaryElement V 1 = σ0 * representationAuxiliaryElement V 1 := by
      have h : (representationAuxiliaryElement V * representationAuxiliaryElement V) 1 = (σ0 • representationAuxiliaryElement V) 1 := by rw [hσ0]
      rw [hval1, MonoidAlgebra.smul_apply, smul_eq_mul] at h
      exact h
    have hσ1 : σ0 = 1 :=
      mul_right_cancel₀ he1 (by rw [one_mul]; exact hcoef.symm)
    rw [hσ0, hσ1, one_smul]

  have he_idem : representationSubalgebraElement V * representationSubalgebraElement V = representationSubalgebraElement V := Subtype.ext hidem
  have he_ne : representationSubalgebraElement V ≠ 0 := by
    intro h
    apply hne
    have h2 := congrArg Subtype.val h
    rwa [ZeroMemClass.coe_zero] at h2

  have hsmul_cancel : ∀ s t : ℂ, s • representationSubalgebraElement V = t • representationSubalgebraElement V → s = t := by
    intro s t h
    have hv := congrArg (fun x : ↥(auxiliaryComplexGroupSubalgebra G) => (x : AuxiliaryGroupFunctionType G) 1) h
    simp only [SetLike.val_smul, MonoidAlgebra.smul_apply, smul_eq_mul] at hv
    exact mul_right_cancel₀ he1 hv
  refine ⟨he_idem, he_ne, ?_⟩
  intro a b ha hb ha0 hb0 hEq

  have h2u : IsUnit (2 : ↥(auxiliaryComplexGroupSubalgebra G)) := by
    rw [show (2 : ↥(auxiliaryComplexGroupSubalgebra G)) = algebraMap ℂ _ 2 by rw [map_ofNat]]
    exact ((two_ne_zero (α := ℂ)).isUnit).map (algebraMap ℂ (↥(auxiliaryComplexGroupSubalgebra G)))
  have hab : a * b = 0 := by
    have hexp : (a + b) * (a + b) = a + b := by rw [← hEq]; exact he_idem
    rw [add_mul, mul_add, mul_add, ha, hb] at hexp
    have h2 : a * b + a * b = 0 := by
      rw [mul_comm b a] at hexp; linear_combination hexp
    have : (2 : ↥(auxiliaryComplexGroupSubalgebra G)) * (a * b) = 0 := by rw [two_mul]; exact h2
    exact (h2u.mul_right_eq_zero).mp this
  have hba0 : b * a = 0 := by rw [mul_comm]; exact hab

  have hea : representationSubalgebraElement V * a = a := by rw [hEq, add_mul, ha, hba0, add_zero]
  have ha_class : auxiliaryGroupFunctionPredicate (a : AuxiliaryGroupFunctionType G) :=
    (mem_auxiliaryComplexGroupSubalgebra_iff (a : AuxiliaryGroupFunctionType G)).mp a.2
  obtain ⟨σa, hσa⟩ :=
    representationAuxiliaryElement_mul_of_auxiliaryGroupFunctionPredicate V
      (a : AuxiliaryGroupFunctionType G) ha_class
  have hσa' : representationSubalgebraElement V * a = σa • representationSubalgebraElement V := by
    apply Subtype.ext; simp only [MulMemClass.coe_mul, SetLike.val_smul]; exact hσa
  have haσ : a = σa • representationSubalgebraElement V := hea ▸ hσa'
  have hσa_sq : σa * σa = σa := by
    have h' : a * a = a := ha
    rw [haσ, smul_mul_smul_comm, he_idem] at h'
    exact hsmul_cancel _ _ h'
  have hσa_ne : σa ≠ 0 := fun h0 => ha0 (by rw [haσ, h0, zero_smul])
  have hσa_one : σa = 1 := by
    have hz : σa * (σa - 1) = 0 := by linear_combination hσa_sq
    exact (mul_eq_zero.mp hz).resolve_left hσa_ne |> sub_eq_zero.mp
  have ha_eq : a = representationSubalgebraElement V := by rw [haσ, hσa_one, one_smul]

  have heb : representationSubalgebraElement V * b = b := by rw [hEq, add_mul, hb, hab, zero_add]
  have hb_class : auxiliaryGroupFunctionPredicate (b : AuxiliaryGroupFunctionType G) :=
    (mem_auxiliaryComplexGroupSubalgebra_iff (b : AuxiliaryGroupFunctionType G)).mp b.2
  obtain ⟨σb, hσb⟩ :=
    representationAuxiliaryElement_mul_of_auxiliaryGroupFunctionPredicate V
      (b : AuxiliaryGroupFunctionType G) hb_class
  have hσb' : representationSubalgebraElement V * b = σb • representationSubalgebraElement V := by
    apply Subtype.ext; simp only [MulMemClass.coe_mul, SetLike.val_smul]; exact hσb
  have hbσ : b = σb • representationSubalgebraElement V := heb ▸ hσb'
  have hσb_sq : σb * σb = σb := by
    have h' : b * b = b := hb
    rw [hbσ, smul_mul_smul_comm, he_idem] at h'
    exact hsmul_cancel _ _ h'
  have hσb_ne : σb ≠ 0 := fun h0 => hb0 (by rw [hbσ, h0, zero_smul])
  have hσb_one : σb = 1 := by
    have hz : σb * (σb - 1) = 0 := by linear_combination hσb_sq
    exact (mul_eq_zero.mp hz).resolve_left hσb_ne |> sub_eq_zero.mp
  have hb_eq : b = representationSubalgebraElement V := by rw [hbσ, hσb_one, one_smul]

  rw [ha_eq, hb_eq] at hEq
  apply he_ne
  have h0 : representationSubalgebraElement V + (0 : ↥(auxiliaryComplexGroupSubalgebra G)) = representationSubalgebraElement V + representationSubalgebraElement V := by
    rw [add_zero]; exact hEq
  exact ((add_right_inj _).mp h0).symm

private lemma primitive_eq_of_mul_ne_zero {A : Type*} [CommRing A] {e c : A}
    (he : auxiliaryRingElementPredicate e) (hc : auxiliaryRingElementPredicate c)
    (hp0 : e * c ≠ 0) : e = c := by
  rcases he with ⟨he_idem, he0, he_primitive⟩
  rcases hc with ⟨hc_idem, hc0, hc_primitive⟩
  have hp : IsIdempotentElem (e * c) := by
    calc
      (e * c) * (e * c) = (e * e) * (c * c) := by ring
      _ = e * c := by rw [he_idem, hc_idem]
  have hce : IsIdempotentElem (1 - c) := by
    dsimp [IsIdempotentElem] at hc_idem ⊢
    linear_combination hc_idem
  have hq : IsIdempotentElem (e * (1 - c)) := by
    calc
      (e * (1 - c)) * (e * (1 - c)) = (e * e) * ((1 - c) * (1 - c)) := by ring
      _ = e * (1 - c) := by rw [he_idem, hce]
  have he_split : e = e * c + e * (1 - c) := by ring
  have hq0 : e * (1 - c) = 0 := by
    by_contra hq0
    exact (he_primitive (e * c) (e * (1 - c)) hp hq hp0 hq0) he_split
  have hep : e = e * c := by
    calc
      e = e * c + e * (1 - c) := he_split
      _ = e * c := by rw [hq0, add_zero]
  have hec : IsIdempotentElem (1 - e) := by
    dsimp [IsIdempotentElem] at he_idem ⊢
    linear_combination he_idem
  have hr : IsIdempotentElem ((1 - e) * c) := by
    calc
      ((1 - e) * c) * ((1 - e) * c) = ((1 - e) * (1 - e)) * (c * c) := by ring
      _ = (1 - e) * c := by rw [hec, hc_idem]
  have hc_split : c = e * c + (1 - e) * c := by ring
  have hr0 : (1 - e) * c = 0 := by
    by_contra hr0
    exact (hc_primitive (e * c) ((1 - e) * c) hp hr hp0 hr0) hc_split
  have hcp : c = e * c := by
    calc
      c = e * c + (1 - e) * c := hc_split
      _ = e * c := by rw [hr0, add_zero]
  exact hep.trans hcp.symm

section Classification

variable {G₀ : Type} [Group G₀] [Fintype G₀]

/-- The finite sum of the subalgebra elements associated to the indexed representations is one. -/
theorem sum_representationSubalgebraElements_eq_one [NeZero (Nat.card G₀ : ℂ)] (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData ℂ G₀) :
    ∑ i : Fin D.count, representationSubalgebraElement (D.representation i) = 1 := by
  have h : (∑ i : Fin D.count, representationAuxiliaryElement (D.representation i)) =
      (1 : MonoidAlgebra ℂ G₀) := by
    ext g
    have happly_finset : ∀ s : Finset (Fin D.count),
        (∑ i ∈ s, representationAuxiliaryElement (D.representation i)) g =
          ∑ i ∈ s, representationAuxiliaryElement (D.representation i) g := by
      intro s
      induction s using Finset.induction_on with
      | empty => rfl
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          exact congrArg (representationAuxiliaryElement (D.representation a) g + ·) ih
    have happly := happly_finset Finset.univ
    rw [happly, one_eq_single_one_one]
    change _ = (Finsupp.single (1 : G₀) (1 : ℂ)) g
    rw [Finsupp.single_apply]
    simp_rw [coeff_representationAuxiliaryElement]
    by_cases hg : g = 1
    · subst g
      simp only [FDRep.char_one]
      have hdim : ∀ i, Module.finrank ℂ (D.representation i) = D.dimension i :=
        D.finrank_representation
      simp_rw [hdim]
      simp only [if_pos]
      calc
        ∑ i : Fin D.count, (D.dimension i : ℂ) / (Fintype.card G₀ : ℂ) * (D.dimension i : ℂ) =
            ∑ i : Fin D.count, ((D.dimension i : ℂ) ^ 2) / (Fintype.card G₀ : ℂ) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (∑ i : Fin D.count, ((D.dimension i : ℂ) ^ 2)) / (Fintype.card G₀ : ℂ) := by
          rw [Finset.sum_div]
        _ = ((∑ i : Fin D.count, (D.dimension i) ^ 2 : ℕ) : ℂ) /
            (Fintype.card G₀ : ℂ) := by push_cast; rfl
        _ = 1 := by rw [D.sum_dimension_sq_eq_card]; simp
    · rw [if_neg (fun h => hg h.symm)]
      have hsum := RepresentationTheory.FDRep.RegularRepresentationCharacter.sum_finrank_mul_character_eq_zero_of_ne_one D D.representation
        D.simple_representation D.representation_index_eq_of_iso g hg
      rw [show (∑ i : Fin D.count,
          (D.representation i).character 1 / (Fintype.card G₀ : ℂ) *
            (D.representation i).character g) =
          (∑ i : Fin D.count,
            (Module.finrank ℂ (D.representation i) : ℂ) *
              (D.representation i).character g) / (Fintype.card G₀ : ℂ) from by
        simp_rw [FDRep.char_one]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring,
        hsum, zero_div]
  apply Subtype.ext
  have hcoe_finset : ∀ s : Finset (Fin D.count),
      ↑(∑ i ∈ s, representationSubalgebraElement (D.representation i)) =
        (∑ i ∈ s, representationAuxiliaryElement (D.representation i) : MonoidAlgebra ℂ G₀) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact congrArg (representationAuxiliaryElement (D.representation a) + ·) ih
  have hcoe := hcoe_finset Finset.univ
  rw [hcoe]
  exact h

/-- Characterizes the auxiliary ring-element predicate by equality with the associated element of some simple representation. -/
@[source_ref "Chapter4/Remark4.5.3" (role := primary)]
theorem auxiliaryRingElementPredicate_iff_exists_simple_representationElement (e : auxiliaryComplexGroupSubalgebra G₀) :
    auxiliaryRingElementPredicate e ↔
      ∃ V : FDRep ℂ G₀, Simple V ∧ e = representationSubalgebraElement V := by
  constructor
  · intro he
    letI : NeZero (Nat.card G₀ : ℂ) :=
      ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := G₀)).ne'⟩
    let D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData ℂ G₀ := RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default
    have hsum := sum_representationSubalgebraElements_eq_one D
    have he_sum : e = ∑ i : Fin D.count, e * representationSubalgebraElement (D.representation i) := by
      rw [← Finset.mul_sum, hsum, mul_one]
    obtain ⟨i, hi⟩ : ∃ i : Fin D.count, e * representationSubalgebraElement (D.representation i) ≠ 0 := by
      by_contra hnone
      apply he.2.1
      rw [he_sum]
      apply Finset.sum_eq_zero
      intro i _
      by_contra hi
      exact hnone ⟨i, hi⟩
    let V := D.representation i
    letI : Simple V := D.simple_representation i
    refine ⟨V, inferInstance, primitive_eq_of_mul_ne_zero he
      (auxiliaryRingElementPredicate_representationSubalgebraElement_of_simple V) ?_⟩
    exact hi
  · rintro ⟨V, hV, rfl⟩
    letI : Simple V := hV
    exact auxiliaryRingElementPredicate_representationSubalgebraElement_of_simple V

end Classification

end RepresentationTheory.CharacterCoefficientAlgebra
