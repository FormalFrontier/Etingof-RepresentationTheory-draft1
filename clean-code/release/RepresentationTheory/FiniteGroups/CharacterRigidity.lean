/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Character rigidity for finite-group representations

This module establishes that a finite-dimensional complex representation of a finite group is
determined up to isomorphism by its character.
-/

open CategoryTheory CategoryTheory.Limits Module

namespace RepresentationTheory.FiniteGroups.CharacterRigidity

variable {G : Type} [Group G] [Finite G]

/-- An auxiliary functor from finite-dimensional complex representations to complex modules. -/
noncomputable abbrev auxiliaryModuleFunctor : FDRep ℂ G ⥤ ModuleCat ℂ :=
  Action.forget (FGModuleCat ℂ) G ⋙ forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)

omit [Finite G] in
/-- The linear map underlying the image of a monomorphism under the auxiliary module functor is injective. -/
theorem injective_auxiliaryModuleFunctor_map_of_mono {A B : FDRep ℂ G} (g : A ⟶ B) [Mono g] :
    Function.Injective (auxiliaryModuleFunctor.map g).hom := by
  haveI : Mono (auxiliaryModuleFunctor.map g) := inferInstance
  rw [← ModuleCat.mono_iff_injective]; infer_instance

/-- Every finite-dimensional complex representation is an Artinian object. -/
instance isArtinianObject (V : FDRep ℂ G) : IsArtinianObject V := by
  set len : Subobject V → ℕ := fun s => finrank ℂ ((s : FDRep ℂ G) : Type) with hlen
  have hlt : ∀ a b : Subobject V, a < b → len a < len b := by
    intro a b hab
    have hle : a ≤ b := le_of_lt hab
    let g : (a : FDRep ℂ G) ⟶ (b : FDRep ℂ G) := Subobject.ofLE a b hle
    haveI : FiniteDimensional ℂ ↥(auxiliaryModuleFunctor.obj (a : FDRep ℂ G)) :=
      (inferInstance : FiniteDimensional ℂ ((a : FDRep ℂ G) : Type))
    haveI : FiniteDimensional ℂ ↥(auxiliaryModuleFunctor.obj (b : FDRep ℂ G)) :=
      (inferInstance : FiniteDimensional ℂ ((b : FDRep ℂ G) : Type))
    have hginj : Function.Injective (auxiliaryModuleFunctor.map g).hom :=
      injective_auxiliaryModuleFunctor_map_of_mono g
    have hfle : len a ≤ len b :=
      (auxiliaryModuleFunctor.map g).hom.finrank_le_finrank_of_injective hginj
    rcases lt_or_eq_of_le hfle with h | h
    · exact h
    · exfalso
      have hsurj : Function.Surjective (auxiliaryModuleFunctor.map g).hom := by
        have hrk := (auxiliaryModuleFunctor.map g).hom.finrank_range_add_finrank_ker
        rw [LinearMap.ker_eq_bot.mpr hginj, finrank_bot, add_zero] at hrk
        rw [← LinearMap.range_eq_top]
        exact Submodule.eq_top_of_finrank_eq (by rw [hrk]; exact h)
      haveI : Epi (auxiliaryModuleFunctor.map g) := by
        rw [ModuleCat.epi_iff_surjective]; exact hsurj
      haveI : IsIso (auxiliaryModuleFunctor.map g) :=
        isIso_of_mono_of_epi (auxiliaryModuleFunctor.map g)
      haveI : IsIso g := isIso_of_reflects_iso g auxiliaryModuleFunctor
      have hba : b ≤ a := Subobject.le_of_comm (inv g) (by
        rw [← Subobject.ofLE_arrow hle]
        change inv g ≫ g ≫ b.arrow = b.arrow
        rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp])
      exact absurd (le_antisymm hle hba) (ne_of_lt hab)
  have wf : WellFounded ((· < ·) : Subobject V → Subobject V → Prop) :=
    Subrelation.wf (fun {a b} hab => hlt a b hab) (InvImage.wf len wellFounded_lt)
  exact (isArtinianObject_iff_not_strictAnti V).mpr (fun f hf => by
    haveI : WellFoundedLT (Subobject V) := ⟨wf⟩
    exact not_strictAnti_of_wellFoundedLT f hf)

omit [Finite G] in
/-- A finite-dimensional complex representation of dimension zero is a zero object. -/
theorem isZero_of_finrank_eq_zero {V : FDRep ℂ G} (h : finrank ℂ (V : Type) = 0) :
    IsZero V := by
  haveI : Subsingleton (V : Type) := finrank_zero_iff.mp h
  haveI : Subsingleton ↥(auxiliaryModuleFunctor.obj V) :=
    (inferInstance : Subsingleton (V : Type))
  haveI : Subsingleton (V ⟶ V) := ⟨fun f g => by
    apply auxiliaryModuleFunctor.map_injective
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => Subsingleton.elim _ _⟩
  exact (IsZero.iff_id_eq_zero V).2 (Subsingleton.elim _ _)

omit [Finite G] in
/-- A nonzero finite-dimensional complex representation has positive dimension. -/
theorem finrank_pos_of_not_isZero {V : FDRep ℂ G} (h : ¬ IsZero V) :
    0 < finrank ℂ (V : Type) :=
  Nat.pos_of_ne_zero fun h0 => h (isZero_of_finrank_eq_zero h0)

omit [Finite G] in
/-- The morphism space into a zero representation has dimension zero. -/
theorem finrank_hom_eq_zero_of_isZero {S V : FDRep ℂ G} (h : IsZero V) :
    finrank ℂ (S ⟶ V) = 0 := by
  haveI : Subsingleton (S ⟶ V) := ⟨fun f g => h.eq_of_tgt f g⟩
  exact finrank_zero_of_subsingleton

/-- An isomorphism of target representations induces a linear equivalence between the corresponding morphism spaces. -/
noncomputable def homLinearEquivOfIso (S : FDRep ℂ G) {A B : FDRep ℂ G} (e : A ≅ B) :
    (S ⟶ A) ≃ₗ[ℂ] (S ⟶ B) where
  toFun f := f ≫ e.hom
  map_add' f g := by simp [Preadditive.add_comp]
  map_smul' c f := by simp [Linear.smul_comp]
  invFun f := f ≫ e.inv
  left_inv f := by simp
  right_inv f := by simp

omit [Finite G] in
/-- Isomorphic target representations have morphism spaces of equal dimension from any fixed source. -/
theorem finrank_hom_eq_of_iso (S : FDRep ℂ G) {A B : FDRep ℂ G} (e : A ≅ B) :
    finrank ℂ (S ⟶ A) = finrank ℂ (S ⟶ B) :=
  (homLinearEquivOfIso S e).finrank_eq

/-- Morphisms from a fixed representation into a biproduct are linearly equivalent to pairs of morphisms into its summands. -/
noncomputable def homBiprodLinearEquiv (S A B : FDRep ℂ G) :
    (S ⟶ A ⊞ B) ≃ₗ[ℂ] (S ⟶ A) × (S ⟶ B) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  map_add' f g := by simp [Preadditive.add_comp]
  map_smul' c f := by simp [Linear.smul_comp]
  invFun p := biprod.lift p.1 p.2
  left_inv f := by apply biprod.hom_ext <;> simp
  right_inv p := by ext <;> simp

omit [Finite G] in
/-- The dimension of morphisms into a binary biproduct is the sum of the two component morphism-space dimensions. -/
theorem finrank_hom_biprod (S A B : FDRep ℂ G) :
    finrank ℂ (S ⟶ A ⊞ B) = finrank ℂ (S ⟶ A) + finrank ℂ (S ⟶ B) := by
  rw [(homBiprodLinearEquiv S A B).finrank_eq, Module.finrank_prod]

omit [Finite G] in
/-- The dimension of a binary biproduct representation is the sum of the dimensions of its two summands. -/
theorem finrank_biprod (A B : FDRep ℂ G) :
    finrank ℂ (A ⊞ B : FDRep ℂ G) = finrank ℂ (A : Type) + finrank ℂ (B : Type) := by
  haveI : PreservesBinaryBiproduct A B (auxiliaryModuleFunctor (G := G)) :=
    preservesBinaryBiproduct_of_preservesBinaryProduct _
  haveI : Module.Finite ℂ ↥(auxiliaryModuleFunctor.obj A) :=
    (inferInstance : Module.Finite ℂ (A : Type))
  haveI : Module.Finite ℂ ↥(auxiliaryModuleFunctor.obj B) :=
    (inferInstance : Module.Finite ℂ (B : Type))
  have e := (((auxiliaryModuleFunctor.mapBiprod A B) ≪≫
    ModuleCat.biprodIsoProd (auxiliaryModuleFunctor.obj A)
      (auxiliaryModuleFunctor.obj B)).toLinearEquiv)
  have key : finrank ℂ ↥(auxiliaryModuleFunctor.obj (A ⊞ B))
      = finrank ℂ ↥(auxiliaryModuleFunctor.obj A) +
        finrank ℂ ↥(auxiliaryModuleFunctor.obj B) := by
    rw [e.finrank_eq, Module.finrank_prod]
  exact key

/-- An auxiliary definition whose displayed type is unavailable. -/
noncomputable def auxiliaryDefinition {X Y : FDRep ℂ G} (f : X ⟶ Y) [IsSplitMono f] :
    Σ' Z : FDRep ℂ G, (Y ≅ X ⊞ Z) :=
  ⟨cokernel f, (isBilimitBinaryBiconeOfIsSplitMonoOfCokernel
    (cokernelIsCokernel f)).isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit X (cokernel f))⟩

omit [Finite G] in
/-- A monomorphism with simple source cannot be the zero morphism. -/
theorem ne_zero_of_mono_of_simple {S V : FDRep ℂ G} (f : S ⟶ V) [Mono f] [Simple S] :
    f ≠ 0 :=
  fun h0 => (Simple.not_isZero S) ((IsZero.iff_id_eq_zero S).2
    ((cancel_mono f).mp (by rw [h0]; simp)))

section CharField

variable [Fintype G] [Invertible (Fintype.card G : ℂ)]

omit [Fintype G] [Invertible (Fintype.card G : ℂ)] in
/-- Equal characters of finite-group representations imply equality of their morphism-space dimensions from any fixed source. -/
theorem finrank_hom_eq_of_character_eq (S V W : FDRep ℂ G) (h : V.character = W.character) :
    finrank ℂ (S ⟶ V) = finrank ℂ (S ⟶ W) := by
  letI := Fintype.ofFinite G
  have hV := FDRep.scalar_product_char_eq_finrank_equivariant S V
  have hW := FDRep.scalar_product_char_eq_finrank_equivariant S W
  rw [h] at hV
  have : (finrank ℂ (S ⟶ V) : ℂ) = (finrank ℂ (S ⟶ W) : ℂ) := by rw [← hV, ← hW]
  exact_mod_cast this

end CharField

/-- A finite-group representation of the specified dimension is isomorphic to a representation whose morphism-space dimensions agree for every simple source. -/
theorem nonempty_iso_of_finrank_eq_of_finrank_hom_simple_eq :
    ∀ (n : ℕ) (V W : FDRep ℂ G), finrank ℂ (V : Type) = n →
      (∀ S : FDRep ℂ G, Simple S → finrank ℂ (S ⟶ V) = finrank ℂ (S ⟶ W)) →
      Nonempty (V ≅ W) := by
  haveI : NeZero (Nat.card G : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V W hVn hhom
    by_cases hVz : IsZero V
    · refine ⟨hVz.iso ?_⟩
      by_contra hWz
      set S₀ := simpleSubobject hWz with hS₀
      have hιne : simpleSubobjectArrow hWz ≠ 0 := ne_zero_of_mono_of_simple _
      have hpos : 0 < finrank ℂ (S₀ ⟶ W) :=
        finrank_pos_iff_exists_ne_zero.mpr ⟨simpleSubobjectArrow hWz, hιne⟩
      have := hhom S₀ inferInstance
      rw [finrank_hom_eq_zero_of_isZero hVz] at this
      omega
    · set S₀ := simpleSubobject hVz with hS₀
      haveI : Simple S₀ := inferInstance
      set ι : S₀ ⟶ V := simpleSubobjectArrow hVz with hι
      haveI : Mono ι := inferInstance
      haveI : IsSplitMono ι :=
        ⟨⟨Injective.factorThru (𝟙 S₀) ι, Injective.comp_factorThru (𝟙 S₀) ι⟩⟩
      obtain ⟨Q, eV⟩ := auxiliaryDefinition ι
      have hS₀pos : 0 < finrank ℂ (S₀ : Type) :=
        finrank_pos_of_not_isZero (Simple.not_isZero S₀)
      have hVeq : finrank ℂ (V : Type) = finrank ℂ (S₀ : Type) +
          finrank ℂ (Q : Type) := by
        rw [(FDRep.isoToLinearEquiv eV).finrank_eq, finrank_biprod]
      have hQlt : finrank ℂ (Q : Type) < n := by rw [← hVn, hVeq]; omega
      have hendo : finrank ℂ (S₀ ⟶ S₀) = 1 := finrank_endomorphism_simple_eq_one ℂ S₀
      have hWpos : 0 < finrank ℂ (S₀ ⟶ W) := by
        have h1 := hhom S₀ inferInstance
        rw [finrank_hom_eq_of_iso S₀ eV, finrank_hom_biprod, hendo] at h1
        omega
      obtain ⟨j, hj⟩ := finrank_pos_iff_exists_ne_zero.mp hWpos
      haveI : Mono j := mono_of_nonzero_from_simple hj
      haveI : IsSplitMono j :=
        ⟨⟨Injective.factorThru (𝟙 S₀) j, Injective.comp_factorThru (𝟙 S₀) j⟩⟩
      obtain ⟨Q', eW⟩ := auxiliaryDefinition j
      have hQhom : ∀ S : FDRep ℂ G, Simple S →
          finrank ℂ (S ⟶ Q) = finrank ℂ (S ⟶ Q') := by
        intro S hS
        have hSV := hhom S hS
        rw [finrank_hom_eq_of_iso S eV, finrank_hom_biprod,
          finrank_hom_eq_of_iso S eW, finrank_hom_biprod] at hSV
        omega
      obtain ⟨eQ⟩ := ih (finrank ℂ (Q : Type)) hQlt Q Q' rfl hQhom
      exact ⟨eV ≪≫ biprod.mapIso (Iso.refl S₀) eQ ≪≫ eW.symm⟩

/-- Finite-group representations over the complex numbers with equal characters are isomorphic. -/
theorem nonempty_iso_of_character_eq {G : Type} [Group G] [Finite G] (V W : FDRep ℂ G)
    (h : V.character = W.character) : Nonempty (V ≅ W) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  exact nonempty_iso_of_finrank_eq_of_finrank_hom_simple_eq (finrank ℂ (V : Type)) V W rfl
    (fun S _ => finrank_hom_eq_of_character_eq S V W h)

end RepresentationTheory.FiniteGroups.CharacterRigidity
