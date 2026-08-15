/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.FiniteGroups.CharacterRigidity
import RepresentationTheory.AuxiliaryUnavailableStatement
import RepresentationTheory.Subgroup.HomAdjunction
import Mathlib.RepresentationTheory.FiniteIndex
import RepresentationTheory.Alignment.Attribute

/-!
# Induction and coinduction comparisons

This module develops identity and finite-group equivalences for induction and coinduction,
along with a restriction adjunction and a compatibility result for dual representations.
-/

open CategoryTheory

universe u

namespace RepresentationTheory.InductionCoinduction

variable (k G : Type u) [Field k] [Group G]

/-- Induction of a representation along the identity homomorphism is isomorphic to that representation. -/
noncomputable def indIdIso (V : Rep k G) :
    Rep.ind (MonoidHom.id G) V ≅ V := by
  let forward :=
    ((Rep.indResHomEquiv (MonoidHom.id G) V V).symm (𝟙 V)).hom.toLinearMap
  let backward := Representation.IndV.mk (MonoidHom.id G) V.ρ 1
  let e : (Rep.ind (MonoidHom.id G) V).V ≃ₗ[k] V.V :=
    LinearEquiv.ofLinear forward backward (by ext v; simp [forward, backward])
      (by ext g v; simp [forward, backward])
  exact Rep.mkIso (Representation.Equiv.mk e fun g => by
    ext v
    simp [e, forward])

/-- The inverse of the identity-induction isomorphism sends a vector to the induced vector constructed at the group identity. -/
@[simp]
lemma indIdIso_inv_apply (V : Rep k G) (v : V) :
    (indIdIso k G V).inv.hom v =
      Representation.IndV.mk (MonoidHom.id G) V.ρ 1 v :=
  rfl

variable (H : Subgroup G)

/-- After restriction to a subgroup, induction along the identity homomorphism is isomorphic to the original representation. -/
@[source_ref "Chapter5/Discussion_Problem5.10.2_parts" (role := primary)]
noncomputable def restrictIndIdIso (V : Rep k G) :
    (Rep.resFunctor H.subtype).obj (Rep.ind (MonoidHom.id G) V) ≅
      (Rep.resFunctor H.subtype).obj V :=
  (Rep.resFunctor H.subtype).mapIso (indIdIso k G V)

/-- The inverse of the restricted identity-induction isomorphism sends a vector to the induced vector constructed at the group identity. -/
@[source_ref "Chapter5/Discussion_Problem5.10.2_parts" (role := primary), simp]
lemma restrictIndIdIso_inv_apply (V : Rep k G) (v : V) :
    (restrictIndIdIso k G H V).inv.hom v =
      Representation.IndV.mk (MonoidHom.id G) V.ρ 1 v :=
  rfl

/-- Coinduction of a representation along the identity homomorphism is isomorphic to that representation. -/
noncomputable def coindIdIso (V : Rep k G) :
    Rep.coind (MonoidHom.id G) V ≅ V := by
  let forward : (Rep.coind (MonoidHom.id G) V).V →ₗ[k] V.V :=
    LinearMap.proj 1 ∘ₗ Submodule.subtype _
  let backward :=
    ((Rep.resCoindHomEquiv (MonoidHom.id G) V V) (𝟙 V)).hom.toLinearMap
  let e : (Rep.coind (MonoidHom.id G) V).V ≃ₗ[k] V.V :=
    LinearEquiv.ofLinear forward backward (by
      apply LinearMap.ext
      intro v
      simp [forward, backward, Rep.resCoindHomEquiv, Rep.resCoindToHom]
      rfl) (by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext g
      change (backward (forward f)).1 g = f.1 g
      rw [show ((backward (forward f)).1 g) = V.ρ g (f.1 1) by
        simp [backward, forward, Rep.resCoindHomEquiv, Rep.resCoindToHom]
        rfl]
      simpa using (f.2 g 1).symm)
  exact Rep.mkIso (Representation.Equiv.mk e fun g => by
    apply LinearMap.ext
    intro f
    change f.1 (1 * g) = V.ρ g (f.1 1)
    simpa using f.2 g 1)

/-- The forward map from identity coinduction evaluates a coinduced vector at the group identity. -/
@[simp]
lemma coindIdIso_hom_apply (V : Rep k G)
    (f : (Rep.coind (MonoidHom.id G) V).V) :
    (coindIdIso k G V).hom.hom f = f.1 1 :=
  rfl

/-- After restriction to a subgroup, coinduction along the identity homomorphism is isomorphic to the original representation. -/
@[source_ref "Chapter5/Discussion_Problem5.10.2_parts" (role := primary)]
noncomputable def restrictCoindIdIso (V : Rep k G) :
    (Rep.resFunctor H.subtype).obj (Rep.coind (MonoidHom.id G) V) ≅
      (Rep.resFunctor H.subtype).obj V :=
  (Rep.resFunctor H.subtype).mapIso (coindIdIso k G V)

/-- The forward map of the restricted identity-coinduction isomorphism evaluates a coinduced vector at the group identity. -/
@[source_ref "Chapter5/Discussion_Problem5.10.2_parts" (role := primary), simp]
lemma restrictCoindIdIso_hom_apply (V : Rep k G)
    (f : (Rep.coind (MonoidHom.id G) V).V) :
    (restrictCoindIdIso k G H V).hom.hom f = f.1 1 :=
  rfl

variable [Finite G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- For a finite ambient group, coinduction from a subgroup is isomorphic to induction from that subgroup. -/
@[source_ref "Chapter5/Discussion_Problem5.10.2_parts" (role := primary)]
noncomputable def coindIsoIndOfFinite (W : Rep k H) :
    Rep.coind H.subtype W ≅ Rep.ind H.subtype W :=
  open scoped Classical in (Rep.indCoindIso W).symm

/-- An auxiliary construction assigning an induced vector to a coinduced vector and a right coset. -/
noncomputable def coindToIndCosetAuxiliary (W : Rep k H)
    (f : (Rep.coind H.subtype W).V)
    (q : Quotient (QuotientGroup.rightRel H)) : (Rep.ind H.subtype W).V :=
  Quotient.liftOn q
    (fun g => Representation.IndV.mk H.subtype W.ρ g (f.1 g))
    (fun g₁ g₂ ⟨s, (hs : _ * _ = _)⟩ =>
      (Submodule.Quotient.eq _).2 <|
        Representation.Coinvariants.mem_ker_of_eq s
          (MonoidAlgebra.single g₂ (1 : k) ⊗ₜ[k] f.1 g₂) _ (by
            have := f.2 s g₂
            simp_all))

/-- The forward finite-group comparison map is the sum of its auxiliary induced vectors over all right cosets. -/
@[source_ref "Chapter5/Discussion_Problem5.10.2_parts" (role := primary)]
theorem coindIsoIndOfFinite_hom_apply (W : Rep k H)
    (f : (Rep.coind H.subtype W).V) :
    (coindIsoIndOfFinite k G H W).hom.hom f =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        coindToIndCosetAuxiliary k G H W f q := by
  classical
  rw [coindIsoIndOfFinite]
  change W.coindToInd f = _
  simpa [coindToIndCosetAuxiliary] using Rep.coindToInd_apply W f

/-- Induction from a subgroup is left adjoint to restriction to that subgroup. -/
@[source_ref "Chapter5/Discussion_Problem5.10.2_parts" (role := primary)]
noncomputable def indResAdjunction :
    Rep.indFunctor k H.subtype ⊣ Rep.resFunctor H.subtype :=
  Rep.indResAdjunction k H.subtype

/-- Morphisms from an induced representation to an ambient representation are linearly equivalent to morphisms into its restriction. -/
@[source_ref "Chapter5/Discussion_Problem5.10.2_parts" (role := supporting)]
noncomputable def indResHomLinearEquiv (W : Rep k H) (V : Rep k G) :
    (Rep.ind H.subtype W ⟶ V) ≃ₗ[k]
      (W ⟶ Rep.res H.subtype V) :=
  Rep.indResHomEquiv H.subtype W V

variable {G₀ : Type} [Group G₀] [Fintype G₀] (H₀ : Subgroup G₀)

/-- An auxiliary operation sending a finite-dimensional complex representation of a subgroup to one of the finite ambient group. -/
noncomputable def finiteGroupFDRepAuxiliary (W : FDRep ℂ H₀) : FDRep ℂ G₀ :=
  FDRep.of (Representation.ind H₀.subtype W.ρ)

/-- The character obtained by applying the finite-group auxiliary construction to a dual equals the character of the dual of its value. -/
theorem character_finiteGroupFDRepAuxiliary_dual (V : FDRep ℂ H₀) :
    (finiteGroupFDRepAuxiliary H₀
      (FDRep.of (Representation.dual V.ρ))).character =
      (FDRep.of (Representation.dual
        (finiteGroupFDRepAuxiliary H₀ V).ρ)).character := by
  classical
  funext g
  rw [FDRep.char_dual]
  change LinearMap.trace ℂ _
      (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H₀
        (Representation.dual V.ρ) g) =
    LinearMap.trace ℂ _
      (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H₀ V.ρ g⁻¹)
  rw [RepresentationTheory.AuxiliaryUnavailableStatement.auxiliary_theorem H₀
      (Representation.dual V.ρ) g,
    RepresentationTheory.AuxiliaryUnavailableStatement.auxiliary_theorem H₀ V.ρ g⁻¹]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have hinv : (x * g * x⁻¹)⁻¹ = x * g⁻¹ * x⁻¹ := by
    simp [mul_assoc]
  by_cases hx : x * g * x⁻¹ ∈ H₀
  · have hx' : x * g⁻¹ * x⁻¹ ∈ H₀ := by
      rw [← hinv]
      exact H₀.inv_mem hx
    simp only [dif_pos hx, dif_pos hx']
    rw [show LinearMap.trace ℂ _
        (Representation.dual V.ρ ⟨x * g * x⁻¹, hx⟩) =
        (FDRep.of (Representation.dual V.ρ)).character
          ⟨x * g * x⁻¹, hx⟩ from rfl,
      FDRep.char_dual]
    congr 2
    apply Subtype.ext
    exact hinv
  · have hx' : x * g⁻¹ * x⁻¹ ∉ H₀ := by
      intro h
      apply hx
      rw [← show (x * g⁻¹ * x⁻¹)⁻¹ = x * g * x⁻¹ by simp [mul_assoc]]
      exact H₀.inv_mem h
    simp [hx, hx']

/-- The finite-group auxiliary construction applied to a dual representation is isomorphic to the dual of its value. -/
@[source_ref "Chapter5/Discussion_Problem5.10.2_parts" (role := primary)]
noncomputable def finiteGroupFDRepAuxiliaryDualIso (V : FDRep ℂ H₀) :
    finiteGroupFDRepAuxiliary H₀ (FDRep.of (Representation.dual V.ρ)) ≅
      FDRep.of (Representation.dual (finiteGroupFDRepAuxiliary H₀ V).ρ) :=
  (RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq _ _
    (character_finiteGroupFDRepAuxiliary_dual H₀ V)).some

end RepresentationTheory.InductionCoinduction
