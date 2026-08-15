/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Character-based comparison of finite-dimensional representations

This file develops dimension and biproduct tools for finite-dimensional group representations and
uses them to construct isomorphisms between representations whose characters agree.
-/

open FDRep CategoryTheory CategoryTheory.Limits Module

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

namespace RepresentationTheory.Group.CharacterAuxiliary

/-! ## Dimension and biproduct tools -/

omit [IsAlgClosed k] in
/-- Equal characters imply equality of the displayed morphism-space dimensions. -/
lemma finrank_hom_eq_of_character_eq
    {G : Type} [Group G] [Finite G]
    (V W : FDRep k G)
    (h : FDRep.character V = FDRep.character W)
    (S : FDRep k G) :
    finrank k (S ⟶ V) = finrank k (S ⟶ W) := by
  letI := Fintype.ofFinite G
  have : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have h1 := scalar_product_char_eq_finrank_equivariant S V
  have h2 := scalar_product_char_eq_finrank_equivariant S W
  rw [h] at h1
  exact_mod_cast h1.symm.trans h2

omit [IsAlgClosed k] in
/-- Representations with equal characters have equal dimensions. -/
lemma finrank_eq_of_character_eq
    {G : Type} [Group G] [Finite G]
    (V W : FDRep k G)
    (h : FDRep.character V = FDRep.character W) :
    finrank k V = finrank k W := by
  have h1 := FDRep.char_one V
  have h2 := FDRep.char_one W
  have h3 := congr_fun h 1
  exact_mod_cast h1.symm.trans (h3.trans h2)

/-- A linear equivalence for morphisms to the displayed biproduct. -/
noncomputable def homBiproductLinearEquiv
    {G : Type} [Group G] [Finite G]
    (T X Y : FDRep k G) [HasBinaryBiproduct X Y] :
    (T ⟶ X ⊞ Y) ≃ₗ[k] (T ⟶ X) × (T ⟶ Y) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  map_add' f g := by simp
  map_smul' r f := by simp
  invFun p := biprod.lift p.1 p.2
  left_inv f := by
    dsimp
    rw [biprod.lift_eq]
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, biprod.total, Category.comp_id]
  right_inv p := by simp

omit [IsAlgClosed k] [CharZero k] in
/-- The dimension of morphisms into the displayed biproduct is the stated sum. -/
lemma finrank_hom_biproduct
    {G : Type} [Group G] [Finite G]
    (T X Y : FDRep k G) [HasBinaryBiproduct X Y] :
    finrank k (T ⟶ X ⊞ Y) = finrank k (T ⟶ X) + finrank k (T ⟶ Y) := by
  rw [← finrank_prod]
  exact LinearEquiv.finrank_eq (homBiproductLinearEquiv T X Y)

omit [IsAlgClosed k] [CharZero k] in
/-- An isomorphism preserves the displayed morphism-space dimension. -/
lemma finrank_hom_eq_of_iso
    {G : Type} [Group G] [Finite G]
    (T V W : FDRep k G) (φ : V ≅ W) :
    finrank k (T ⟶ V) = finrank k (T ⟶ W) :=
  LinearEquiv.finrank_eq
    { toFun := fun f => f ≫ φ.hom
      map_add' := fun f g => by simp
      map_smul' := fun r f => by simp
      invFun := fun f => f ≫ φ.inv
      left_inv := fun f => by simp
      right_inv := fun f => by simp }

omit [IsAlgClosed k] [CharZero k] in
/-- An isomorphism preserves representation dimension. -/
lemma finrank_eq_of_iso
    {G : Type} [Group G] [Finite G]
    (V W : FDRep k G) (φ : V ≅ W) :
    finrank k V = finrank k W :=
  LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv φ)

omit [IsAlgClosed k] [CharZero k] in
/-- The dimension of the displayed biproduct is the stated sum of dimensions. -/
lemma finrank_biproduct
    {G : Type} [Group G] [Finite G]
    (X Y : FDRep k G) [HasBinaryBiproduct X Y] :
    finrank k (X ⊞ Y : FDRep k G) = finrank k X + finrank k Y := by
  rw [← finrank_prod]
  apply LinearEquiv.finrank_eq
  refine {
    toFun := fun v => ((biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom v,
                        (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom v)
    map_add' := fun a b => Prod.ext (map_add _ _ _) (map_add _ _ _)
    map_smul' := fun r a => Prod.ext (map_smul _ _ _) (map_smul _ _ _)
    invFun := fun p => (biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
                        (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2
    left_inv := fun v => by
      change ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
        (X ⊞ Y : FDRep k G) ⟶ (X ⊞ Y))).hom.hom.hom v = v
      rw [biprod.total]; rfl
    right_inv := fun p => by
      have hzero : ∀ (A B : FDRep k G) (x : A.V), (0 : A ⟶ B).hom.hom.hom x = 0 := by
        intro A B x
        change (0 : A.V.obj ⟶ B.V.obj).hom x = 0
        change (0 : A.V.obj →ₗ[k] B.V.obj) x = 0
        exact LinearMap.zero_apply x
      have hid : ∀ (A : FDRep k G) (x : A.V), (𝟙 A : A ⟶ A).hom.hom.hom x = x :=
        fun _ _ => rfl
      ext <;> dsimp only
      · change ((biprod.fst : X ⊞ Y ⟶ X)).hom.hom.hom
            ((biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
             (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2) = p.1
        rw [map_add]
        change ((biprod.inl ≫ biprod.fst : X ⟶ X)).hom.hom.hom p.1 +
             ((biprod.inr ≫ biprod.fst : Y ⟶ X)).hom.hom.hom p.2 = p.1
        rw [biprod.inl_fst, biprod.inr_fst, hid, hzero, add_zero]
      · change ((biprod.snd : X ⊞ Y ⟶ Y)).hom.hom.hom
            ((biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
             (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2) = p.2
        rw [map_add]
        change ((biprod.inl ≫ biprod.snd : X ⟶ Y)).hom.hom.hom p.1 +
             ((biprod.inr ≫ biprod.snd : Y ⟶ Y)).hom.hom.hom p.2 = p.2
        rw [biprod.inl_snd, biprod.inr_snd, hzero, hid, zero_add] }

omit [IsAlgClosed k] [CharZero k] in
/-- If one representation is zero and all incoming morphism spaces have the same dimension for
two representations, then the representations are isomorphic. -/
lemma iso_of_isZero_of_hom_finrank_eq
    {G : Type} [Group G] [Finite G]
    (V W : FDRep k G)
    (hV0 : IsZero V)
    (h : ∀ S : FDRep k G, finrank k (S ⟶ V) = finrank k (S ⟶ W)) :
    Nonempty (V ≅ W) := by
  have hWV : Subsingleton (W ⟶ V) := ⟨fun f g => hV0.eq_of_tgt f g⟩
  have h1 : finrank k (W ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
  have h2 : finrank k (W ⟶ W) = 0 := by rw [← h W]; exact h1
  have hWW : Subsingleton (W ⟶ W) := Module.finrank_zero_iff.mp h2
  have hW : IsZero W := by
    rw [IsZero.iff_id_eq_zero]
    exact Subsingleton.eq_zero _
  exact ⟨hV0.iso hW⟩

omit [CharZero k] in
/-- A simple representation has positive dimension. -/
lemma finrank_pos_of_simple
    {G : Type} [Group G] [Finite G]
    (S : FDRep k G) [Simple S] : 0 < finrank k S := by
  by_contra h
  push Not at h
  have h0 : finrank k S = 0 := Nat.eq_zero_of_le_zero h
  have hSS : finrank k (S ⟶ S) = 1 := by
    rw [FDRep.finrank_hom_simple_simple]; simp
  have hsub : Subsingleton S := Module.finrank_zero_iff.mp h0
  have hsub2 : Subsingleton (S ⟶ S) := by
    constructor; intro f g
    exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))
  have : finrank k (S ⟶ S) = 0 := Module.finrank_zero_of_subsingleton
  omega

omit [IsAlgClosed k] in
/-- A nonzero morphism from a simple representation exhibits its target as a biproduct of that
representation and another representation. -/
lemma exists_iso_biprod_of_ne_zero_from_simple
    {G : Type} [Group G] [Finite G]
    (S W : FDRep k G) [Simple S] (f : S ⟶ W) (hf : f ≠ 0) :
    ∃ (W' : FDRep k G), Nonempty (W ≅ S ⊞ W') := by
  haveI : Mono f := mono_of_nonzero_from_simple hf
  haveI : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  haveI : Injective S := inferInstance
  haveI : IsSplitMono f := IsSplitMono.mk'
    ⟨Injective.factorThru (𝟙 S) f, Injective.comp_factorThru (𝟙 S) f⟩
  have hcok := cokernelIsCokernel f
  let bc := binaryBiconeOfIsSplitMonoOfCokernel hcok
  have hbl := isBilimitBinaryBiconeOfIsSplitMonoOfCokernel hcok
  haveI : HasBinaryBiproduct S (cokernel f) :=
    HasBinaryBiproduct.mk ⟨bc, hbl⟩
  exact ⟨cokernel f, ⟨biprod.uniqueUpToIso S (cokernel f) hbl⟩⟩

omit [IsAlgClosed k] [CharZero k] in
/-- The target of a split monomorphism is isomorphic to the biproduct of its source and cokernel. -/
lemma iso_biprod_cokernel_of_splitMono
    {G : Type} [Group G] [Finite G]
    (Y V : FDRep k G) (f : Y ⟶ V) [Mono f] [IsSplitMono f] :
    Nonempty (V ≅ Y ⊞ cokernel f) := by
  have hcok := cokernelIsCokernel f
  let bc := binaryBiconeOfIsSplitMonoOfCokernel hcok
  have hbl := isBilimitBinaryBiconeOfIsSplitMonoOfCokernel hcok
  haveI : HasBinaryBiproduct Y (cokernel f) :=
    HasBinaryBiproduct.mk ⟨bc, hbl⟩
  exact ⟨biprod.uniqueUpToIso Y (cokernel f) hbl⟩

omit [IsAlgClosed k] [CharZero k] in
/-- A representation of zero dimension is zero. -/
lemma isZero_of_finrank_eq_zero
    {G : Type} [Group G] [Finite G]
    (W : FDRep k G) (h0 : finrank k W = 0) : IsZero W := by
  rw [IsZero.iff_id_eq_zero]
  have hsub : Subsingleton W := Module.finrank_zero_iff.mp h0
  exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))

omit [IsAlgClosed k] in
/-- A nonzero representation is isomorphic to a biproduct of a simple representation and another
representation. -/
lemma exists_simple_biprod
    {G : Type} [Group G] [Finite G]
    (V : FDRep k G) (hV : ¬IsZero V) :
    ∃ (S V' : FDRep k G), Simple S ∧ Nonempty (V ≅ S ⊞ V') := by
  haveI : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  suffices key : ∀ (n : ℕ) (V : FDRep k G), ¬IsZero V → finrank k V ≤ n →
      ∃ (S V' : FDRep k G), Simple S ∧ Nonempty (V ≅ S ⊞ V') from
    key _ V hV le_rfl
  intro n
  induction n with
  | zero =>
    intro V hV hfr
    exact absurd (isZero_of_finrank_eq_zero V (Nat.eq_zero_of_le_zero hfr)) hV
  | succ n ih =>
    intro V hV hfr
    by_cases hS : Simple V
    · haveI := hS
      have hid : (𝟙 V : V ⟶ V) ≠ 0 := by
        intro h; apply hV; rwa [IsZero.iff_id_eq_zero]
      obtain ⟨V', ⟨φ⟩⟩ := exists_iso_biprod_of_ne_zero_from_simple V V (𝟙 V) hid
      exact ⟨V, V', hS, ⟨φ⟩⟩
    · have h_exists : ∃ (Y : FDRep k G) (f : Y ⟶ V), Mono f ∧ f ≠ 0 ∧ ¬IsIso f := by
        by_contra h_all
        apply hS
        refine ⟨fun {Y} f _ => ⟨?_, ?_⟩⟩
        · intro hi habs
          haveI := hi
          apply hV; rw [IsZero.iff_id_eq_zero]
          have key := IsIso.inv_hom_id (f := f)
          simp only [habs, comp_zero] at key
          exact key.symm
        · intro hne
          by_contra hni
          exact h_all ⟨Y, f, ‹Mono f›, hne, hni⟩
      obtain ⟨Y, f, hfm, hfne, hfni⟩ := h_exists
      haveI := hfm
      haveI : IsSplitMono f :=
        IsSplitMono.mk' ⟨Injective.factorThru (𝟙 Y) f, Injective.comp_factorThru (𝟙 Y) f⟩
      obtain ⟨iso_V⟩ := iso_biprod_cokernel_of_splitMono Y V f
      have hY : ¬IsZero Y := fun hY0 => hfne (hY0.eq_of_src f 0)
      have hcok_nz : ¬IsZero (cokernel f : FDRep k G) := by
        intro hcok0
        haveI : Epi f := (Preadditive.epi_iff_isZero_cokernel f).mpr hcok0
        exact hfni (isIso_of_mono_of_epi f)
      have hfr_eq : finrank k V = finrank k Y + finrank k (cokernel f : FDRep k G) :=
        by rw [finrank_eq_of_iso V (Y ⊞ cokernel f) iso_V, finrank_biproduct]
      have hcok_pos : 0 < finrank k (cokernel f : FDRep k G) := by
        by_contra h
        push Not at h
        exact hcok_nz (isZero_of_finrank_eq_zero _ (Nat.eq_zero_of_le_zero h))
      have hY_le : finrank k Y ≤ n := by omega
      obtain ⟨S, Y', hSS, ⟨ψ⟩⟩ := ih Y hY hY_le
      exact ⟨S, Y' ⊞ cokernel f, hSS,
        ⟨iso_V.trans ((biprod.mapIso ψ (Iso.refl _)).trans
          (biprod.associator S Y' (cokernel f)))⟩⟩

/-! ## Isomorphisms from dimension data -/

/-- The displayed equality of morphism-space dimensions yields an isomorphism. -/
lemma iso_of_hom_finrank_eq
    {G : Type} [Group G] [Finite G]
    (V W : FDRep k G)
    (h : ∀ S : FDRep k G, finrank k (S ⟶ V) = finrank k (S ⟶ W)) :
    Nonempty (V ≅ W) := by
  suffices key : ∀ (n : ℕ) (V W : FDRep k G),
      finrank k V ≤ n →
      (∀ S : FDRep k G, finrank k (S ⟶ V) = finrank k (S ⟶ W)) →
      Nonempty (V ≅ W) from
    key _ V W le_rfl h
  intro n
  induction n with
  | zero =>
    intro V W hVn h
    by_cases hV : IsZero V
    · exact iso_of_isZero_of_hom_finrank_eq V W hV h
    · obtain ⟨S, V', hS, ⟨φ⟩⟩ := exists_simple_biprod V hV
      haveI := hS
      have : finrank k V = 0 := Nat.eq_zero_of_le_zero hVn
      have : 0 < finrank k S := finrank_pos_of_simple S
      have : finrank k S ≤ finrank k V := by
        rw [finrank_eq_of_iso V (S ⊞ V') φ, finrank_biproduct]
        omega
      omega
  | succ n ih =>
    intro V W hVn h
    by_cases hV : IsZero V
    · exact iso_of_isZero_of_hom_finrank_eq V W hV h
    · obtain ⟨S, V', hS, ⟨φ⟩⟩ := exists_simple_biprod V hV
      haveI : Simple S := hS
      have hV_decomp : ∀ T, finrank k (T ⟶ V) = finrank k (T ⟶ S) + finrank k (T ⟶ V') := by
        intro T
        rw [finrank_hom_eq_of_iso T V (S ⊞ V') φ, finrank_hom_biproduct]
      have hSS : finrank k (S ⟶ S) = 1 := by
        rw [FDRep.finrank_hom_simple_simple]; simp
      have hSV_pos : 0 < finrank k (S ⟶ V) := by
        rw [hV_decomp S]; omega
      have hSW_pos : 0 < finrank k (S ⟶ W) := by rw [← h S]; exact hSV_pos
      have : Nontrivial (S ⟶ W) := by
        rw [nontrivial_iff]
        exact (finrank_pos_iff.mp hSW_pos).exists_pair_ne
      obtain ⟨f, hf⟩ := exists_ne (0 : S ⟶ W)
      obtain ⟨W', ⟨ψ⟩⟩ := exists_iso_biprod_of_ne_zero_from_simple S W f hf
      have hW_decomp : ∀ T, finrank k (T ⟶ W) = finrank k (T ⟶ S) + finrank k (T ⟶ W') := by
        intro T
        rw [finrank_hom_eq_of_iso T W (S ⊞ W') ψ, finrank_hom_biproduct]
      have hV'W' : ∀ T, finrank k (T ⟶ V') = finrank k (T ⟶ W') := by
        intro T
        have hv := hV_decomp T
        have hw := hW_decomp T
        have := h T
        omega
      have hV'_le : finrank k V' ≤ n := by
        have hfr : finrank k V = finrank k S + finrank k V' := by
          rw [finrank_eq_of_iso V (S ⊞ V') φ, finrank_biproduct]
        have hS_pos : 0 < finrank k S := finrank_pos_of_simple S
        omega
      obtain ⟨θ⟩ := ih V' W' hV'_le hV'W'
      exact ⟨φ.trans ((biprod.mapIso (Iso.refl S) θ).trans ψ.symm)⟩

/-! ## Character comparison -/

/-- Finite-dimensional representations with equal characters are isomorphic under the displayed
hypotheses. -/
@[source_ref "Chapter4/Corollary4.2.4" (role := primary)]
theorem iso_of_character_eq
    (G : Type) [Group G] [Finite G]
    (V W : FDRep k G)
    (h : FDRep.character V = FDRep.character W) :
    Nonempty (V ≅ W) :=
  iso_of_hom_finrank_eq V W (finrank_hom_eq_of_character_eq V W h)

/-- Complex finite-dimensional representations with equal characters are isomorphic. -/
@[source_ref "Chapter4/Corollary4.2.4" (role := primary)]
theorem complex_iso_of_character_eq
    (G : Type) [Group G] [Finite G]
    (V W : FDRep ℂ G)
    (h : FDRep.character V = FDRep.character W) :
    Nonempty (V ≅ W) :=
  iso_of_character_eq G V W h

end RepresentationTheory.Group.CharacterAuxiliary
