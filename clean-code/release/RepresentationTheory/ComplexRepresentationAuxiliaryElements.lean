/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.FDRep.Character

/-!
# Auxiliary elements for complex representations

This module associates an element of the complex group algebra to each finite-dimensional complex
representation of a finite group. On simple representations, the corresponding algebra action is
the identity on the associated representation and vanishes on nonisomorphic ones. These action
formulas yield idempotence and pairwise orthogonality of the elements.
-/

open CategoryTheory MonoidAlgebra Module

namespace RepresentationTheory.ComplexRepresentationAuxiliaryElements

variable {G : Type*} [Group G] [Fintype G]

/-- An auxiliary element of the complex group algebra associated to a finite-dimensional complex representation. -/
@[source_ref "Chapter4/Problem4.5.2" (role := supporting)]
noncomputable def auxiliaryElement (V : FDRep ℂ G) : MonoidAlgebra ℂ G :=
  ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) •
    ∑ g : G, V.character g • MonoidAlgebra.single g⁻¹ (1 : ℂ)

/-! ### Basic nonvanishing facts -/

private lemma card_ne_zero_cx : (Fintype.card G : ℂ) ≠ 0 := by
  haveI : Nonempty G := ⟨1⟩
  exact_mod_cast Fintype.card_ne_zero

/-- Simple finite-dimensional representations have positive dimension. -/
private lemma finrank_pos_of_simple (V : FDRep ℂ G) [Simple V] : 0 < Module.finrank ℂ V := by
  by_contra hcon
  push Not at hcon
  have h0 : Module.finrank ℂ V = 0 := Nat.eq_zero_of_le_zero hcon
  have hsub : Subsingleton (V : Type _) := Module.finrank_zero_iff.mp h0
  have hsub2 : Subsingleton (V ⟶ V) := by
    constructor; intro f g
    exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))
  have hone : Module.finrank ℂ (V ⟶ V) = 1 := by
    rw [FDRep.finrank_hom_simple_simple]; simp
  have hzero : Module.finrank ℂ (V ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
  omega

private lemma finrank_ne_zero_cx (V : FDRep ℂ G) [Simple V] :
    (Module.finrank ℂ V : ℂ) ≠ 0 := by
  have := finrank_pos_of_simple V
  exact_mod_cast this.ne'

/-! ### Scalar endomorphisms -/

/-- A linear endomorphism commuting with the action on a simple representation is scalar, with
the scalar determined by its trace. -/
private lemma endo_scalar (V : FDRep ℂ G) [Simple V]
    (T : V →ₗ[ℂ] V) (hT : ∀ g : G, T ∘ₗ V.ρ g = V.ρ g ∘ₗ T) :
    ∃ c : ℂ, T = c • LinearMap.id ∧
      LinearMap.trace ℂ V T = c * (Module.finrank ℂ V : ℂ) := by
  -- The endomorphism lies in the invariants of the representation on linear maps.
  have hmemT : T ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g
    rw [Representation.linHom_apply, hT g⁻¹, ← LinearMap.comp_assoc,
      show V.ρ g ∘ₗ V.ρ g⁻¹ = LinearMap.id by
        rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_eq_id],
      LinearMap.id_comp]
  -- The invariant space is one dimensional.
  have h1dim : Module.finrank ℂ (Representation.linHom V.ρ V.ρ).invariants = 1 := by
    rw [LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom V V)]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ V
  -- The identity is a nonzero invariant.
  have hid_mem : (LinearMap.id : V →ₗ[ℂ] V) ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g; ext v
    simp only [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.id_apply]
    change (V.ρ g * V.ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  have hid_ne : (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff, Submodule.coe_zero]
    intro hz
    have : (Module.finrank ℂ V : ℂ) = 0 := by
      rw [← LinearMap.trace_id (R := ℂ) (M := V), hz, map_zero]
    exact finrank_ne_zero_cx V this
  -- Every invariant is a scalar multiple of the identity.
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) hid_ne).mp h1dim
    ⟨T, hmemT⟩
  have hTeq : T = c • LinearMap.id := by
    have hval := congrArg Subtype.val hc
    simpa using hval.symm
  refine ⟨c, hTeq, ?_⟩
  rw [hTeq, map_smul, LinearMap.trace_id, smul_eq_mul]

/-! ### Actions of the auxiliary element -/

/-- The action of the auxiliary element on a representation as a scalar multiple of a sum of
representation operators. -/
private lemma asAlgebraHom_psi (V W : FDRep ℂ G) :
    Representation.asAlgebraHom W.ρ (auxiliaryElement V)
      = ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) •
          ∑ g : G, V.character g • W.ρ g⁻¹ := by
  simp only [auxiliaryElement, map_smul, map_sum, Representation.asAlgebraHom_single_one]

/-- The auxiliary element commutes with every group-basis element of the group algebra. -/
private lemma psi_comm_single (V : FDRep ℂ G) (h : G) :
    auxiliaryElement V * MonoidAlgebra.single h (1 : ℂ) =
      MonoidAlgebra.single h (1 : ℂ) * auxiliaryElement V := by
  rw [auxiliaryElement, smul_mul_assoc, mul_smul_comm]
  congr 1
  rw [Finset.sum_mul, Finset.mul_sum]
  -- Reindex by conjugation.
  let e : G ≃ G :=
    { toFun := fun g => h⁻¹ * g * h
      invFun := fun g => h * g * h⁻¹
      left_inv := by intro g; group
      right_inv := by intro g; group }
  refine Fintype.sum_equiv e _ _ ?_
  intro g
  have hchar : V.character (h⁻¹ * g * h) = V.character g := by
    have := V.char_conj g h⁻¹; simpa using this
  simp only [e, Equiv.coe_fn_mk, smul_mul_assoc, mul_smul_comm,
    MonoidAlgebra.single_mul_single, one_mul]
  rw [hchar, show h * (h⁻¹ * g * h)⁻¹ = g⁻¹ * h by group]

/-- The action of the auxiliary element commutes with the group action. -/
private lemma asAlgebraHom_psi_comm (V W : FDRep ℂ G) (g : G) :
    (Representation.asAlgebraHom W.ρ (auxiliaryElement V)) ∘ₗ W.ρ g
      = W.ρ g ∘ₗ (Representation.asAlgebraHom W.ρ (auxiliaryElement V)) := by
  have hc := psi_comm_single V g
  have h2 := congrArg (Representation.asAlgebraHom W.ρ) hc
  rw [map_mul, map_mul, Representation.asAlgebraHom_single_one] at h2
  simpa only [Module.End.mul_eq_comp] using h2

/-- The trace of the action of the auxiliary element on a representation. -/
private lemma trace_asAlgebraHom_psi (V W : FDRep ℂ G) :
    LinearMap.trace ℂ W (Representation.asAlgebraHom W.ρ (auxiliaryElement V))
      = ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) *
          ∑ g : G, V.character g * W.character g⁻¹ := by
  rw [asAlgebraHom_psi V W, map_smul, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

/-- A simple representation sends its associated auxiliary group-algebra element to the identity linear map. -/
@[source_ref "Chapter4/Problem4.5.2" (role := primary)]
theorem map_auxiliaryElement_eq_id (V : FDRep ℂ G) [Simple V] :
    Representation.asAlgebraHom V.ρ (auxiliaryElement V) = LinearMap.id := by
  haveI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero card_ne_zero_cx
  obtain ⟨c, hTc, htr⟩ := endo_scalar V _ (asAlgebraHom_psi_comm V V)
  have hsum : ∑ g : G, V.character g * V.character g⁻¹ = (Fintype.card G : ℂ) := by
    have ho :=
      RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple V V
    rw [if_pos ⟨Iso.refl V⟩] at ho
    have h2 : ∑ g : G, V.character g * V.character g⁻¹
        = (Fintype.card G : ℂ) •
            (⅟(Fintype.card G : ℂ) • ∑ g : G, V.character g * V.character g⁻¹) := by
      rw [smul_smul, mul_invOf_self, one_smul]
    rw [h2, ho]; simp
  have htrace : LinearMap.trace ℂ V (Representation.asAlgebraHom V.ρ (auxiliaryElement V))
      = (Module.finrank ℂ V : ℂ) := by
    rw [trace_asAlgebraHom_psi V V, hsum, div_mul_cancel₀ _ card_ne_zero_cx]
  have hc1 : c = 1 := by
    have h : c * (Module.finrank ℂ V : ℂ) = (Module.finrank ℂ V : ℂ) := htr.symm.trans htrace
    have : c * (Module.finrank ℂ V : ℂ) = 1 * (Module.finrank ℂ V : ℂ) := by rw [one_mul]; exact h
    exact mul_right_cancel₀ (finrank_ne_zero_cx V) this
  rw [hTc, hc1, one_smul]

/-- The algebra action of one simple representation sends the auxiliary element of a nonisomorphic simple representation to zero. -/
@[source_ref "Chapter4/Problem4.5.2" (role := primary)]
theorem map_auxiliaryElement_eq_zero_of_not_iso (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : IsEmpty (W ≅ V)) :
    Representation.asAlgebraHom W.ρ (auxiliaryElement V) = 0 := by
  haveI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero card_ne_zero_cx
  obtain ⟨c, hTc, htr⟩ := endo_scalar W _ (asAlgebraHom_psi_comm V W)
  have hsum : ∑ g : G, V.character g * W.character g⁻¹ = 0 := by
    have ho :=
      RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple V W
    rw [if_neg (by rintro ⟨e⟩; exact h.false e.symm)] at ho
    have h2 : ∑ g : G, V.character g * W.character g⁻¹
        = (Fintype.card G : ℂ) •
            (⅟(Fintype.card G : ℂ) • ∑ g : G, V.character g * W.character g⁻¹) := by
      rw [smul_smul, mul_invOf_self, one_smul]
    rw [h2, ho]; simp
  have htrace : LinearMap.trace ℂ W (Representation.asAlgebraHom W.ρ (auxiliaryElement V)) = 0 := by
    rw [trace_asAlgebraHom_psi V W, hsum, mul_zero]
  have hc0 : c = 0 := by
    have h2 : c * (Module.finrank ℂ W : ℂ) = 0 := htr.symm.trans htrace
    exact (mul_eq_zero.mp h2).resolve_right (finrank_ne_zero_cx W)
  rw [hTc, hc0, zero_smul]

/-! ### Character-convolution identities

Tracing a representation operator composed with the auxiliary action gives the coefficient
identities used in the product formulas below.
-/

/-- The trace of a representation operator composed with an auxiliary action, expressed as a
character convolution. -/
private lemma trace_rho_comp_psi (V W : FDRep ℂ G) (x : G) :
    LinearMap.trace ℂ V (V.ρ x ∘ₗ Representation.asAlgebraHom V.ρ (auxiliaryElement W))
      = ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ)) *
          ∑ g : G, W.character g * V.character (x * g⁻¹) := by
  have hcomp : V.ρ x ∘ₗ Representation.asAlgebraHom V.ρ (auxiliaryElement W)
      = ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ)) •
          ∑ g : G, W.character g • V.ρ (x * g⁻¹) := by
    rw [asAlgebraHom_psi W V, ← Module.End.mul_eq_comp, mul_smul_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    rw [mul_smul_comm, ← map_mul]
  rw [hcomp, map_smul, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

/-- The diagonal character-convolution identity. -/
private lemma conv_self (V : FDRep ℂ G) [Simple V] (x : G) :
    ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) *
        ∑ g : G, V.character g * V.character (x * g⁻¹) = V.character x := by
  have h := trace_rho_comp_psi V V x
  rw [map_auxiliaryElement_eq_id V, LinearMap.comp_id] at h
  exact h.symm

/-- The off-diagonal character-convolution identity for nonisomorphic simple representations. -/
private lemma conv_other (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : IsEmpty (W ≅ V)) (x : G) :
    ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ)) *
        ∑ g : G, W.character g * V.character (x * g⁻¹) = 0 := by
  have hVW : IsEmpty (V ≅ W) := ⟨fun e => h.false e.symm⟩
  have ht := trace_rho_comp_psi V W x
  rw [map_auxiliaryElement_eq_zero_of_not_iso W V hVW, LinearMap.comp_zero, map_zero] at ht
  exact ht.symm

/-! ### Products of auxiliary elements -/

/-- A reindexing that displays the coefficient of each group-basis element. -/
private lemma psi_eq (V : FDRep ℂ G) :
    auxiliaryElement V = ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) •
      ∑ k : G, V.character k⁻¹ • MonoidAlgebra.single k (1 : ℂ) := by
  rw [auxiliaryElement]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by rw [Equiv.inv_apply, inv_inv])

/-- The product of two auxiliary elements expanded as a single sum with character-convolution
coefficients. -/
private lemma psi_mul_psi_eq (A B : FDRep ℂ G) :
    auxiliaryElement A * auxiliaryElement B
      = ∑ k : G,
          (((Module.finrank ℂ A : ℂ) / (Fintype.card G : ℂ)) *
              (((Module.finrank ℂ B : ℂ) / (Fintype.card G : ℂ)) *
                ∑ a : G, A.character a * B.character (k⁻¹ * a⁻¹))) •
            MonoidAlgebra.single k (1 : ℂ) := by
  have hSS : (∑ a : G, A.character a • MonoidAlgebra.single a⁻¹ (1 : ℂ)) *
      (∑ b : G, B.character b • MonoidAlgebra.single b⁻¹ (1 : ℂ))
      = ∑ k : G, (∑ a : G, A.character a * B.character (k⁻¹ * a⁻¹)) •
          MonoidAlgebra.single k (1 : ℂ) := by
    rw [Finset.sum_mul]
    have step1 : ∀ a : G,
        (A.character a • MonoidAlgebra.single a⁻¹ (1 : ℂ)) *
            (∑ b : G, B.character b • MonoidAlgebra.single b⁻¹ (1 : ℂ))
          = ∑ k : G, (A.character a * B.character (k⁻¹ * a⁻¹)) •
              MonoidAlgebra.single k (1 : ℂ) := by
      intro a
      rw [smul_mul_assoc, Finset.mul_sum]
      have inner : ∀ b : G,
          MonoidAlgebra.single a⁻¹ (1 : ℂ) * (B.character b • MonoidAlgebra.single b⁻¹ (1 : ℂ))
            = B.character b • MonoidAlgebra.single (a⁻¹ * b⁻¹) (1 : ℂ) := by
        intro b; rw [mul_smul_comm, MonoidAlgebra.single_mul_single, one_mul]
      rw [Finset.sum_congr rfl (fun b _ => inner b)]
      let e : G ≃ G :=
        { toFun := fun b => a⁻¹ * b⁻¹
          invFun := fun k => k⁻¹ * a⁻¹
          left_inv := by intro b; group
          right_inv := by intro k; group }
      have reindex :
          (∑ b : G, B.character b • MonoidAlgebra.single (a⁻¹ * b⁻¹) (1 : ℂ))
            = ∑ k : G, B.character (k⁻¹ * a⁻¹) • MonoidAlgebra.single k (1 : ℂ) := by
        refine Fintype.sum_equiv e _ _ (fun b => ?_)
        simp only [e, Equiv.coe_fn_mk]
        rw [show (a⁻¹ * b⁻¹)⁻¹ * a⁻¹ = b from by group]
      rw [reindex, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [smul_smul]
    rw [Finset.sum_congr rfl (fun a _ => step1 a), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_smul]
  rw [auxiliaryElement, auxiliaryElement, smul_mul_assoc, mul_smul_comm, hSS]
  simp only [Finset.smul_sum, smul_smul]

/-- The auxiliary group-algebra element associated to a simple representation is idempotent. -/
@[source_ref "Chapter4/Problem4.5.2" (role := primary)]
theorem auxiliaryElement_mul_self (V : FDRep ℂ G) [Simple V] :
    auxiliaryElement V * auxiliaryElement V = auxiliaryElement V := by
  rw [psi_mul_psi_eq V V, psi_eq V, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [conv_self V, smul_smul]

/-- The product of the auxiliary group-algebra elements of two nonisomorphic simple representations is zero. -/
@[source_ref "Chapter4/Problem4.5.2" (role := primary)]
theorem auxiliaryElement_mul_eq_zero_of_not_iso (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : IsEmpty (W ≅ V)) :
    auxiliaryElement W * auxiliaryElement V = 0 := by
  rw [psi_mul_psi_eq W V]
  apply Finset.sum_eq_zero
  intro k _
  rw [mul_left_comm, conv_other V W h, mul_zero, zero_smul]

end RepresentationTheory.ComplexRepresentationAuxiliaryElements
