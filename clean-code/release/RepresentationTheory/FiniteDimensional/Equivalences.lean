/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.PermutationDegreeThree
import RepresentationTheory.FiniteGroups.CharacterRigidity

/-!
# Equivalences of finite-dimensional representations

This module records how simple finite-dimensional complex representations and their dimensions
behave under equivalences induced by group isomorphisms.
-/

noncomputable section

open CategoryTheory Module

namespace RepresentationTheory.FiniteDimensional.Equivalences

section Simple

open CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- A full faithful functor preserving monomorphisms reflects simplicity of an object. -/
lemma simple_of_map (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms]
    (X : C) [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f _ := by
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) :=
        (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
          (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

/-- An equivalence functor sends a simple object to a simple object. -/
lemma simple_map_of_equivalence (E : C ≌ D) (X : C) [Simple X] :
    Simple (E.functor.obj X) := by
  haveI : Simple ((𝟭 C).obj X) := inferInstanceAs (Simple X)
  haveI : Simple (E.inverse.obj (E.functor.obj X)) := Simple.of_iso (E.unitIso.app X).symm
  exact simple_of_map E.inverse (E.functor.obj X)

end Simple

variable {G H : Type} [Group G] [Group H]

/-- Builds an equivalence of finite-dimensional complex representation categories from a group
equivalence. -/
def fdRepEquivalenceOfMulEquiv (e : G ≃* H) : FDRep ℂ H ≌ FDRep ℂ G :=
  Action.resEquiv (FGModuleCat ℂ) e

/-- The functor induced by a group equivalence preserves the finite dimension of a
representation. -/
lemma finrank_map_group_equiv (e : G ≃* H) (V : FDRep ℂ H) :
    finrank ℂ ((fdRepEquivalenceOfMulEquiv e).functor.obj V : Type) =
      finrank ℂ (V : Type) := rfl

/-- A complete pairwise distinct family of simple representations transfers across a group
equivalence while preserving dimensions. -/
theorem exists_simple_representatives_preserving_finrank (e : G ≃* H) {n : ℕ}
    (W : Fin n → FDRep ℂ H) (hsimple : ∀ i, Simple (W i))
    (hinj : ∀ i j, Nonempty (W i ≅ W j) → i = j)
    (hcomplete : ∀ S : FDRep ℂ H, Simple S → ∃ i, Nonempty (S ≅ W i)) :
    ∃ W' : Fin n → FDRep ℂ G,
      (∀ i, Simple (W' i)) ∧
      (∀ i j, Nonempty (W' i ≅ W' j) → i = j) ∧
      (∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ W' i)) ∧
      (∀ i, finrank ℂ (W' i : Type) = finrank ℂ (W i : Type)) := by
  set E := fdRepEquivalenceOfMulEquiv e with hE
  refine ⟨fun i => E.functor.obj (W i), ?_, ?_, ?_, ?_⟩
  · -- simplicity is preserved by the equivalence
    intro i
    haveI := hsimple i
    exact simple_map_of_equivalence E (W i)
  · -- fully faithful reflects isomorphisms
    intro i j ⟨h⟩
    exact hinj i j ⟨E.fullyFaithfulFunctor.preimageIso h⟩
  · -- essential surjectivity: pull `S` back, classify, push forward
    intro S hS
    haveI := hS
    haveI : Simple (E.inverse.obj S) := simple_map_of_equivalence E.symm S
    obtain ⟨i, ⟨h⟩⟩ := hcomplete (E.inverse.obj S) inferInstance
    exact ⟨i, ⟨(E.counitIso.app S).symm ≪≫ E.functor.mapIso h⟩⟩
  · -- dimensions are unchanged: the underlying vector space is the same
    intro i
    exact finrank_map_group_equiv e (W i)

/-- Pointwise equality of finite dimensions gives equal index filters at every dimension. -/
lemma filter_univ_finrank_eq_of_forall_eq {n : ℕ} {W' : Fin n → FDRep ℂ G}
    {W : Fin n → FDRep ℂ H}
    (hdim : ∀ i, finrank ℂ (W' i : Type) = finrank ℂ (W i : Type)) (d : ℕ)
    [DecidablePred fun i => finrank ℂ (W' i : Type) = d]
    [DecidablePred fun i => finrank ℂ (W i : Type) = d] :
    (Finset.univ.filter fun i => finrank ℂ (W' i : Type) = d)
      = (Finset.univ.filter fun i => finrank ℂ (W i : Type) = d) := by
  apply Finset.filter_congr
  intro i _
  rw [hdim i]

section OneDim

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
/-- Expresses the action on a one-dimensional representation as scalar multiplication by its
character value. -/
private lemma rho_eq_character_smul (S : FDRep ℂ G) (hdim : finrank ℂ (S : Type) = 1)
    (g : G) : S.ρ g = (S.character g : ℂ) • LinearMap.id := by
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (S.ρ g)
  have hchar : S.character g = c := by
    change LinearMap.trace ℂ _ (S.ρ g) = c
    rw [hc, map_smul, LinearMap.trace_id, hdim]
    simp
  rw [hchar]; exact hc

omit [Finite G] in
/-- Equality between scalar multiples of the identity on a one-dimensional representation
implies equality of the scalars. -/
private lemma smul_id_inj (S : FDRep ℂ G) (hdim : finrank ℂ (S : Type) = 1) {a b : ℂ}
    (h : (a : ℂ) • (LinearMap.id : (S : Type) →ₗ[ℂ] (S : Type)) = b • LinearMap.id) : a = b := by
  have := congrArg (LinearMap.trace ℂ (S : Type)) h
  rwa [map_smul, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at this

/-- A finite-dimensional representation of rank one is isomorphic to a representation of the
displayed form. -/
theorem exists_iso_to_representation_of_finrank_eq_one (S : FDRep ℂ G)
    (hdim : finrank ℂ (S : Type) = 1) :
    ∃ ξ : G →* ℂˣ,
      Nonempty
        (S ≅ FDRep.of
          (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter ξ)) := by
  have hone : S.character (1 : G) = 1 := by rw [FDRep.char_one, hdim, Nat.cast_one]
  have hmul : ∀ g h : G, S.character (g * h) = S.character g * S.character h := by
    intro g h
    apply smul_id_inj S hdim
    have h1 : S.ρ (g * h) = (S.character (g * h) : ℂ) • LinearMap.id :=
      rho_eq_character_smul S hdim (g * h)
    have h2 : S.ρ (g * h) = (S.character g * S.character h : ℂ) • LinearMap.id := by
      rw [map_mul, rho_eq_character_smul S hdim g, rho_eq_character_smul S hdim h]
      ext x
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
    rw [← h1, ← h2]
  have hne : ∀ g : G, S.character g ≠ 0 := by
    intro g h0
    have hgi := hmul g g⁻¹
    rw [mul_inv_cancel, hone, h0, zero_mul] at hgi
    exact one_ne_zero hgi
  refine ⟨{ toFun := fun g => Units.mk0 (S.character g) (hne g)
            map_one' := Units.ext (by simp [hone])
            map_mul' := fun g h => Units.ext (by simp [hmul g h, Units.val_mul]) }, ?_⟩
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
    S _ (funext fun g => ?_)
  rw [RepresentationTheory.PermutationDegreeThree.character_representationOfUnitCharacter]
  rfl

end OneDim

end RepresentationTheory.FiniteDimensional.Equivalences
