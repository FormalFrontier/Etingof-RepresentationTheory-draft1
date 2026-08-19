/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace RepresentationTheory.HomologicalAlgebra.AcyclicComplexDecomposition

variable {k : Type u} [Field k] (K : CochainComplex (ModuleCat.{u} k) ℤ)

/-- The complementary selected submodule inside a complex term. -/
noncomputable def chosenComplementComplement (n : ℤ) : Submodule k (K.X n) := LinearMap.ker (K.d n (n + 1)).hom

/-- A selected submodule complement inside a complex term. -/
noncomputable def chosenComplement (n : ℤ) : Submodule k (K.X n) :=
  (Submodule.exists_isCompl (chosenComplementComplement K n)).choose

/-- The two selected submodules form complementary submodules of each complex term. -/
lemma isCompl_chosenComplementComplement_chosenComplement (n : ℤ) : IsCompl (chosenComplementComplement K n) (chosenComplement K n) :=
  (Submodule.exists_isCompl (chosenComplementComplement K n)).choose_spec

/-- The linear map from a selected complement into the next complex term. -/
noncomputable def chosenComplementToNext (n : ℤ) : chosenComplement K n →ₗ[k] K.X (n + 1) :=
  (K.d n (n + 1)).hom ∘ₗ (chosenComplement K n).subtype

/-- Every element of a complex term is a sum of elements from the two selected complements. -/
lemma chosenComplementComplement_add_chosenComplement (n : ℤ) (x : K.X n) :
    ∃ z ∈ chosenComplementComplement K n, ∃ w ∈ chosenComplement K n, z + w = x := by
  have hsup := (isCompl_chosenComplementComplement_chosenComplement K n).sup_eq_top
  have hx : x ∈ (⊤ : Submodule k (K.X n)) := Submodule.mem_top
  rw [← hsup, Submodule.mem_sup] at hx
  obtain ⟨z, hz, w, hw, hzw⟩ := hx
  exact ⟨z, hz, w, hw, hzw⟩

variable {K} in
/-- Under acyclicity, the differential has the prescribed selected range. -/
lemma range_d_eq_chosenComplementComplement_succ (hK : K.Acyclic) (n : ℤ) :
    LinearMap.range (K.d n (n + 1)).hom = chosenComplementComplement K (n + 1) := by
  have h := hK (n + 1)
  rw [K.exactAt_iff' n (n + 1) (n + 1 + 1)
      ((ComplexShape.up ℤ).prev_eq' (by simp))
      ((ComplexShape.up ℤ).next_eq' (by simp))] at h
  have hrk := h.moduleCat_range_eq_ker
  simpa [chosenComplementComplement] using hrk

/-- The map from a selected complement into the next term is injective. -/
lemma chosenComplementToNext_injective (n : ℤ) : Function.Injective (chosenComplementToNext K n) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  simp only [LinearMap.mem_ker, chosenComplementToNext, LinearMap.comp_apply, Submodule.subtype_apply] at hw
  have hwZ : (w : K.X n) ∈ chosenComplementComplement K n := hw
  have hwW : (w : K.X n) ∈ chosenComplement K n := w.2
  have hmem : (w : K.X n) ∈ chosenComplementComplement K n ⊓ chosenComplement K n := ⟨hwZ, hwW⟩
  rw [(isCompl_chosenComplementComplement_chosenComplement K n).inf_eq_bot] at hmem
  simpa using hmem

variable {K} in
/-- Under acyclicity, the complement map has the prescribed range. -/
lemma range_chosenComplementToNext_eq (hK : K.Acyclic) (n : ℤ) :
    LinearMap.range (chosenComplementToNext K n) = chosenComplementComplement K (n + 1) := by
  rw [← range_d_eq_chosenComplementComplement_succ hK n]
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact ⟨(chosenComplement K n).subtype w, rfl⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz, w, hw, rfl⟩ := chosenComplementComplement_add_chosenComplement K n x
    rw [map_add]
    have hz0 : (K.d n (n + 1)).hom z = 0 := hz
    rw [hz0, zero_add]
    exact ⟨⟨w, hw⟩, rfl⟩

variable {K} in
/-- Under acyclicity, the image of the complement map has the stated complementary submodule. -/
lemma isCompl_range_chosenComplementToNext_chosenComplement_succ (hK : K.Acyclic) (n : ℤ) :
    IsCompl (LinearMap.range (chosenComplementToNext K n)) (chosenComplement K (n + 1)) := by
  rw [range_chosenComplementToNext_eq hK n]
  exact isCompl_chosenComplementComplement_chosenComplement K (n + 1)

variable {K} in
/-- A linear contracting homomorphism obtained from acyclicity. -/
noncomputable def acyclicContractingHom (hK : K.Acyclic) (n : ℤ) : K.X (n + 1) →ₗ[k] K.X n :=
  (chosenComplement K n).subtype ∘ₗ
    LinearMap.linearProjOfIsCompl (chosenComplement K (n + 1)) (chosenComplementToNext K n) (chosenComplementToNext_injective K n)
      (isCompl_range_chosenComplementToNext_chosenComplement_succ hK n)

variable {K} in
/-- Adjacent contracting homomorphisms satisfy the contracting identity. -/
lemma acyclicContractingHom_add_d_comp_acyclicContractingHom (hK : K.Acyclic) (n : ℤ) (x : K.X (n + 1)) :
    acyclicContractingHom hK (n + 1) ((K.d (n + 1) (n + 1 + 1)).hom x)
      + (K.d n (n + 1)).hom (acyclicContractingHom hK n x) = x := by
  obtain ⟨z, hz, w, hw, rfl⟩ := chosenComplementComplement_add_chosenComplement K (n + 1) x
  have hzrange : z ∈ LinearMap.range (chosenComplementToNext K n) := by rw [range_chosenComplementToNext_eq hK n]; exact hz
  obtain ⟨w0, hw0⟩ := hzrange
  have hproj2 : (LinearMap.linearProjOfIsCompl (chosenComplement K (n + 1)) (chosenComplementToNext K n)
      (chosenComplementToNext_injective K n) (isCompl_range_chosenComplementToNext_chosenComplement_succ hK n)) (z + w) = w0 := by
    rw [map_add, ← hw0, LinearMap.linearProjOfIsCompl_apply_left,
      LinearMap.linearProjOfIsCompl_apply_right' (chosenComplement K (n + 1)) (chosenComplementToNext K n)
        (chosenComplementToNext_injective K n) (isCompl_range_chosenComplementToNext_chosenComplement_succ hK n) w hw, add_zero]
  have hsecond : (K.d n (n + 1)).hom (acyclicContractingHom hK n (z + w)) = z := by
    rw [acyclicContractingHom, LinearMap.comp_apply, hproj2, ← hw0]
    rfl
  have hzker : (K.d (n + 1) (n + 1 + 1)).hom z = 0 := hz
  have hwd : (K.d (n + 1) (n + 1 + 1)).hom w = chosenComplementToNext K (n + 1) ⟨w, hw⟩ := by
    rw [chosenComplementToNext, LinearMap.comp_apply, Submodule.subtype_apply]
  have hproj1 : (LinearMap.linearProjOfIsCompl (chosenComplement K (n + 1 + 1)) (chosenComplementToNext K (n + 1))
      (chosenComplementToNext_injective K (n + 1)) (isCompl_range_chosenComplementToNext_chosenComplement_succ hK (n + 1)))
      ((K.d (n + 1) (n + 1 + 1)).hom (z + w)) = ⟨w, hw⟩ := by
    rw [map_add, hzker, zero_add, hwd, LinearMap.linearProjOfIsCompl_apply_left]
  have hfirst : acyclicContractingHom hK (n + 1) ((K.d (n + 1) (n + 1 + 1)).hom (z + w)) = w := by
    rw [acyclicContractingHom, LinearMap.comp_apply, hproj1, Submodule.subtype_apply]
  rw [hfirst, hsecond]
  abel

variable {K} in
/-- A degreewise map provided by acyclicity between terms of a complex. -/
noncomputable def acyclicContractingMap (hK : K.Acyclic) (i j : ℤ) : K.X i ⟶ K.X j :=
  if h : i = j + 1 then eqToHom (congrArg K.X h) ≫ ModuleCat.ofHom (acyclicContractingHom hK j) else 0

variable {K} in
/-- The adjacent component of the acyclic contracting map is the specified linear map. -/
@[simp] lemma acyclicContractingMap_succ_eq (hK : K.Acyclic) (j : ℤ) :
    acyclicContractingMap hK (j + 1) j = ModuleCat.ofHom (acyclicContractingHom hK j) := by
  rw [acyclicContractingMap, dif_pos rfl]; simp

variable {K} in
/-- The acyclic contracting map vanishes away from adjacent degrees. -/
lemma acyclicContractingMap_eq_zero (hK : K.Acyclic) {i j : ℤ} (h : ¬ i = j + 1) :
    acyclicContractingMap hK i j = 0 := dif_neg h

section Disk

open CategoryTheory.Limits
open scoped ZeroObject

/-- The object occurring in a specified degree of a two-term complex. -/
noncomputable def twoTermComponentObject (V : ModuleCat.{u} k) (i n : ℤ) : ModuleCat.{u} k :=
  if n = i ∨ n = i + 1 then V else 0

/-- The two-term component object agrees with its prescribed module in its supported degrees. -/
lemma twoTermComponentObject_eq {V : ModuleCat.{u} k} {i n : ℤ} (h : n = i ∨ n = i + 1) :
    twoTermComponentObject V i n = V := if_pos h

/-- The two-term component object is zero outside its two supported degrees. -/
lemma twoTermComponentObject_eq_zero {V : ModuleCat.{u} k} {i n : ℤ} (h : ¬(n = i ∨ n = i + 1)) :
    twoTermComponentObject V i n = 0 := if_neg h

/-- A two-term component object is zero away from its support. -/
lemma isZero_twoTermComponentObject {V : ModuleCat.{u} k} {i n : ℤ} (h : ¬(n = i ∨ n = i + 1)) :
    IsZero (twoTermComponentObject V i n) :=
  (isZero_zero _).of_iso (eqToIso (twoTermComponentObject_eq_zero h))

/-- The cochain complex supported in two consecutive degrees with a prescribed module. -/
noncomputable def twoTermComplex (V : ModuleCat.{u} k) (i : ℤ) : CochainComplex (ModuleCat.{u} k) ℤ where
  X n := twoTermComponentObject V i n
  d m n :=
    if h : m = i ∧ n = i + 1 then
      eqToHom (twoTermComponentObject_eq (Or.inl h.1)) ≫ eqToHom (twoTermComponentObject_eq (Or.inr h.2)).symm
    else 0
  shape _ _ hmn := dif_neg fun h => hmn (by simp [ComplexShape.up_Rel, h.1, h.2])
  d_comp_d' m n p _ _ := by
    by_cases h : m = i ∧ n = i + 1
    · have h2 : ¬(n = i ∧ p = i + 1) := by rintro ⟨hn, -⟩; rw [h.2] at hn; omega
      rw [dif_neg h2, comp_zero]
    · rw [dif_neg h, zero_comp]

/-- Identifies a term of the two-term complex with its component object. -/
@[simp] lemma twoTermComplex_X_eq (V : ModuleCat.{u} k) (i n : ℤ) : (twoTermComplex V i).X n = twoTermComponentObject V i n := rfl

/-- A term of the two-term complex is zero away from its two supporting degrees. -/
lemma isZero_twoTermComplex_X {V : ModuleCat.{u} k} {i n : ℤ} (h : ¬(n = i ∨ n = i + 1)) :
    IsZero ((twoTermComplex V i).X n) := isZero_twoTermComponentObject h

/-- Describes the designated differential of a two-term complex. -/
lemma twoTermComplex_d_eq (V : ModuleCat.{u} k) (i : ℤ) :
    (twoTermComplex V i).d i (i + 1) = eqToHom (twoTermComponentObject_eq (Or.inl rfl)) ≫
      eqToHom (twoTermComponentObject_eq (V := V) (i := i) (Or.inr rfl)).symm :=
  dif_pos ⟨rfl, rfl⟩

/-- All differentials except the designated consecutive one vanish in a two-term complex. -/
lemma twoTermComplex_d_eq_zero (V : ModuleCat.{u} k) (i : ℤ) {m n : ℤ} (h : ¬(m = i ∧ n = i + 1)) :
    (twoTermComplex V i).d m n = 0 := dif_neg h

/-- The designated differential of the two-term complex is an isomorphism. -/
instance twoTermComplex_d_isIso (V : ModuleCat.{u} k) (i : ℤ) : IsIso ((twoTermComplex V i).d i (i + 1)) := by
  have h : (twoTermComplex V i).d i (i + 1) =
      eqToHom ((twoTermComponentObject_eq (V := V) (i := i) (Or.inl rfl)).trans
        (twoTermComponentObject_eq (V := V) (i := i) (Or.inr rfl)).symm) := by
    rw [twoTermComplex_d_eq, eqToHom_trans]
  rw [h]; infer_instance

/-- Extends a map into one term of a complex to a morphism from a two-term complex. -/
noncomputable def twoTermComplexHom {V : ModuleCat.{u} k} {i : ℤ}
    {L : CochainComplex (ModuleCat.{u} k) ℤ} (f : V ⟶ L.X i) : twoTermComplex V i ⟶ L where
  f n :=
    if h : n = i then
      eqToHom (twoTermComponentObject_eq (Or.inl h)) ≫ f ≫ eqToHom (congrArg L.X h.symm)
    else if h' : n = i + 1 then
      eqToHom (twoTermComponentObject_eq (Or.inr h')) ≫ f ≫ L.d i (i + 1) ≫ eqToHom (congrArg L.X h'.symm)
    else 0
  comm' m n hmn := by
    rw [ComplexShape.up_Rel] at hmn
    by_cases hm : m = i
    · subst hm
      obtain rfl : n = m + 1 := hmn.symm
      rw [twoTermComplex_d_eq, dif_pos rfl, dif_neg (by omega), dif_pos rfl]
      simp
    · rw [twoTermComplex_d_eq_zero V i (by tauto), zero_comp, dif_neg hm]
      by_cases hm' : m = i + 1
      · subst hm'
        obtain rfl : n = i + 1 + 1 := hmn.symm
        rw [dif_pos rfl]
        simp only [Category.assoc, eqToHom_refl, Category.comp_id,
          HomologicalComplex.d_comp_d, comp_zero]
      · rw [dif_neg hm', zero_comp]

/-- Describes the first nonzero component of a morphism from a two-term complex. -/
lemma twoTermComplexHom_f_eq {V : ModuleCat.{u} k} {i n : ℤ}
    {L : CochainComplex (ModuleCat.{u} k) ℤ} (f : V ⟶ L.X i) (h : n = i) :
    (twoTermComplexHom f).f n = eqToHom (twoTermComponentObject_eq (Or.inl h)) ≫ f ≫ eqToHom (congrArg L.X h.symm) :=
  dif_pos h

/-- Describes the second nonzero component of a morphism from a two-term complex. -/
lemma twoTermComplexHom_f_succ_eq {V : ModuleCat.{u} k} {i n : ℤ}
    {L : CochainComplex (ModuleCat.{u} k) ℤ} (f : V ⟶ L.X i) (h : n = i + 1) :
    (twoTermComplexHom f).f n = eqToHom (twoTermComponentObject_eq (Or.inr h)) ≫ f ≫ L.d i (i + 1) ≫
      eqToHom (congrArg L.X h.symm) :=
  (dif_neg (show ¬(n = i) by omega)).trans (dif_pos h)

/-- Morphisms from a two-term complex are determined by their two supported components. -/
lemma twoTermComplex_hom_ext {V : ModuleCat.{u} k} {i : ℤ} {L : CochainComplex (ModuleCat.{u} k) ℤ}
    (α β : twoTermComplex V i ⟶ L) (h0 : α.f i = β.f i) (h1 : α.f (i + 1) = β.f (i + 1)) : α = β := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases h : n = i
  · subst h; exact h0
  · by_cases h' : n = i + 1
    · subst h'; exact h1
    · exact (isZero_twoTermComponentObject (V := V) (i := i) (n := n) (by tauto)).eq_of_src _ _

end Disk

section DirectSum

open CategoryTheory.Limits

/-- An auxiliary module associated to a term of a cochain complex. -/
noncomputable def componentObject (n : ℤ) : ModuleCat.{u} k := ModuleCat.of k (chosenComplement K n)

/-- The chosen section from the auxiliary component object into a complex term. -/
noncomputable def componentSection (n : ℤ) : componentObject K n ⟶ K.X n := ModuleCat.ofHom (chosenComplement K n).subtype

/-- The linear projection of a complex term onto its selected complement. -/
noncomputable def chosenComplementProjection (n : ℤ) : K.X n →ₗ[k] chosenComplement K n :=
  (chosenComplement K n).projectionOnto (chosenComplementComplement K n) (isCompl_chosenComplementComplement_chosenComplement K n).symm

/-- The chosen retraction from a complex term onto its auxiliary component object. -/
noncomputable def componentRetraction (n : ℤ) : K.X n ⟶ componentObject K n := ModuleCat.ofHom (chosenComplementProjection K n)

/-- The complement projection restricts to the identity on the selected complement. -/
lemma chosenComplementProjection_subtype (n : ℤ) (w : chosenComplement K n) : chosenComplementProjection K n (w : K.X n) = w :=
  Submodule.projectionOnto_apply_left _ w

/-- The complement projection vanishes on the complementary selected submodule. -/
lemma chosenComplementProjection_eq_zero (n : ℤ) {z : K.X n} (hz : z ∈ chosenComplementComplement K n) : chosenComplementProjection K n z = 0 :=
  Submodule.projectionOnto_apply_right _ ⟨z, hz⟩

/-- The next complement projection kills the image of the differential. -/
lemma chosenComplementProjection_succ_comp_d (n : ℤ) (x : K.X n) : chosenComplementProjection K (n + 1) ((K.d n (n + 1)).hom x) = 0 := by
  refine chosenComplementProjection_eq_zero K (n + 1) ?_
  have h := congrArg (fun f : K.X n ⟶ K.X (n + 1 + 1) => f.hom x)
    (K.d_comp_d n (n + 1) (n + 1 + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  exact h

/-- The chosen section followed by its retraction is the identity. -/
@[reassoc]
lemma componentSection_comp_componentRetraction (n : ℤ) : componentSection K n ≫ componentRetraction K n = 𝟙 (componentObject K n) := by
  apply ModuleCat.hom_ext
  ext w
  exact chosenComplementProjection_subtype K n w

/-- The differential followed by the next component retraction vanishes. -/
@[reassoc]
lemma d_comp_componentRetraction_succ (n : ℤ) : K.d n (n + 1) ≫ componentRetraction K (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  ext x
  exact chosenComplementProjection_succ_comp_d K n x

variable {K}

/-- The acyclicity lift into the selected complement. -/
noncomputable def acyclicLift (hK : K.Acyclic) (n : ℤ) : K.X (n + 1) →ₗ[k] chosenComplement K n :=
  LinearMap.linearProjOfIsCompl (chosenComplement K (n + 1)) (chosenComplementToNext K n) (chosenComplementToNext_injective K n)
    (isCompl_range_chosenComplementToNext_chosenComplement_succ hK n)

/-- A map to the preceding auxiliary component supplied by acyclicity. -/
noncomputable def acyclicComponentMap (hK : K.Acyclic) (n : ℤ) : K.X (n + 1) ⟶ componentObject K n :=
  ModuleCat.ofHom (acyclicLift hK n)

/-- The acyclicity lift is a left inverse to the complement map. -/
lemma acyclicLift_comp_chosenComplementToNext (hK : K.Acyclic) (n : ℤ) (w : chosenComplement K n) : acyclicLift hK n (chosenComplementToNext K n w) = w :=
  LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ w

/-- The acyclicity lift vanishes on the next selected complement. -/
lemma acyclicLift_eq_zero (hK : K.Acyclic) (n : ℤ) {x : K.X (n + 1)} (hx : x ∈ chosenComplement K (n + 1)) :
    acyclicLift hK n x = 0 :=
  LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ x hx

/-- Lifting after the differential equals the selected complement projection. -/
lemma acyclicLift_comp_d_eq_chosenComplementProjection (hK : K.Acyclic) (n : ℤ) (x : K.X n) :
    acyclicLift hK n ((K.d n (n + 1)).hom x) = chosenComplementProjection K n x := by
  obtain ⟨z, hz, w, hw, rfl⟩ := chosenComplementComplement_add_chosenComplement K n x
  have hz0 : (K.d n (n + 1)).hom z = 0 := hz
  have hwd : (K.d n (n + 1)).hom w = chosenComplementToNext K n ⟨w, hw⟩ := rfl
  rw [map_add, hz0, hwd, zero_add, acyclicLift_comp_chosenComplementToNext, map_add, chosenComplementProjection_eq_zero K n hz, zero_add]
  exact (chosenComplementProjection_subtype K n ⟨w, hw⟩).symm

/-- Composing the differential with the acyclic component map gives the component retraction. -/
@[reassoc]
lemma d_comp_acyclicComponentMap (hK : K.Acyclic) (n : ℤ) : K.d n (n + 1) ≫ acyclicComponentMap hK n = componentRetraction K n := by
  apply ModuleCat.hom_ext
  ext x
  exact acyclicLift_comp_d_eq_chosenComplementProjection hK n x

/-- The acyclic component map has zero composite with the next chosen section. -/
@[reassoc]
lemma componentSection_succ_comp_acyclicComponentMap (hK : K.Acyclic) (n : ℤ) : componentSection K (n + 1) ≫ acyclicComponentMap hK n = 0 := by
  apply ModuleCat.hom_ext
  ext w
  exact acyclicLift_eq_zero hK n w.2

/-- The section--retraction identity remains valid after postcomposition. -/
add_decl_doc componentSection_comp_componentRetraction_assoc

/-- The zero composite for the acyclic component map remains valid after postcomposition. -/
add_decl_doc componentSection_succ_comp_acyclicComponentMap_assoc

/-- The vanishing differential--retraction composite is stable under postcomposition. -/
add_decl_doc d_comp_componentRetraction_succ_assoc

/-- The differential identity for the acyclic component map is stable under postcomposition. -/
add_decl_doc d_comp_acyclicComponentMap_assoc

/-- The complement projection and a differential correction reconstruct an element. -/
lemma chosenComplementProjection_add_d_comp_acyclicLift (hK : K.Acyclic) (n : ℤ) (x : K.X (n + 1)) :
    ((chosenComplementProjection K (n + 1) x : K.X (n + 1))) + (K.d n (n + 1)).hom ((acyclicLift hK n x : K.X n)) = x := by
  obtain ⟨z, hz, w, hw, rfl⟩ := chosenComplementComplement_add_chosenComplement K (n + 1) x
  have hzr : z ∈ LinearMap.range (chosenComplementToNext K n) := by rw [range_chosenComplementToNext_eq hK n]; exact hz
  obtain ⟨w0, rfl⟩ := hzr
  have hfirst : chosenComplementProjection K (n + 1) (chosenComplementToNext K n w0 + w) = ⟨w, hw⟩ := by
    rw [map_add, chosenComplementProjection_eq_zero K (n + 1) hz, zero_add]
    exact chosenComplementProjection_subtype K (n + 1) ⟨w, hw⟩
  have hsecond : acyclicLift hK n (chosenComplementToNext K n w0 + w) = w0 := by
    rw [map_add, acyclicLift_comp_chosenComplementToNext, acyclicLift_eq_zero hK n hw, add_zero]
  rw [hfirst, hsecond]
  change (w : K.X (n + 1)) + chosenComplementToNext K n w0 = _
  exact add_comm _ _

variable (K)

/-- The two-term complex associated to a chosen degree of a cochain complex. -/
noncomputable def twoTermComponent (i : ℤ) : CochainComplex (ModuleCat.{u} k) ℤ := twoTermComplex (componentObject K i) i

/-- The canonical morphism from a two-term component into the original complex. -/
noncomputable def twoTermComponentToComplex (i : ℤ) : twoTermComponent K i ⟶ K := twoTermComplexHom (componentSection K i)

/-- The morphism from the coproduct of two-term components to the original complex. -/
noncomputable def sigmaTwoTermComponentToComplex : (∐ twoTermComponent K) ⟶ K := Sigma.desc (twoTermComponentToComplex K)

/-- Composing a coproduct inclusion with the component morphism recovers the two-term map. -/
lemma sigmaInclusion_comp_sigmaTwoTermComponentToComplex_f (i n : ℤ) :
    (Sigma.ι (twoTermComponent K) i).f n ≫ (sigmaTwoTermComponentToComplex K).f n = (twoTermComponentToComplex K i).f n := by
  rw [← HomologicalComplex.comp_f, sigmaTwoTermComponentToComplex, Sigma.ι_desc]

/-- The map from a complex term to the corresponding term of the coproduct of two-term components. -/
noncomputable def sigmaComponentMap (n : ℤ) : K.X n ⟶ (∐ twoTermComponent K).X n :=
  componentRetraction K n ≫ eqToHom (twoTermComponentObject_eq (V := componentObject K n) (i := n) (Or.inl rfl)).symm ≫
    (Sigma.ι (twoTermComponent K) n).f n

variable {K}

/-- A componentwise map into the coproduct complex constructed from acyclicity. -/
noncomputable def acyclicSigmaComponentMap (hK : K.Acyclic) (m n : ℤ) : K.X n ⟶ (∐ twoTermComponent K).X n :=
  if h : n = m + 1 then
    eqToHom (congrArg K.X h) ≫ acyclicComponentMap hK m ≫
      eqToHom (twoTermComponentObject_eq (V := componentObject K m) (i := m) (Or.inr h)).symm ≫
      (Sigma.ι (twoTermComponent K) m).f n
  else 0

/-- The acyclic coproduct component map vanishes away from adjacent degrees. -/
lemma acyclicSigmaComponentMap_eq_zero (hK : K.Acyclic) {m n : ℤ} (h : ¬n = m + 1) : acyclicSigmaComponentMap hK m n = 0 :=
  dif_neg h

/-- Describes the adjacent component of the acyclic coproduct map. -/
lemma acyclicSigmaComponentMap_succ_eq (hK : K.Acyclic) (m : ℤ) :
    acyclicSigmaComponentMap hK m (m + 1) = acyclicComponentMap hK m ≫
      eqToHom (twoTermComponentObject_eq (V := componentObject K m) (i := m) (Or.inr rfl)).symm ≫
      (Sigma.ι (twoTermComponent K) m).f (m + 1) := by
  rw [acyclicSigmaComponentMap, dif_pos rfl]
  simp

/-- Relates the component map to the differential of the coproduct complex. -/
lemma sigmaComponentMap_comp_d (m : ℤ) :
    sigmaComponentMap K m ≫ (∐ twoTermComponent K).d m (m + 1) = componentRetraction K m ≫
      eqToHom (twoTermComponentObject_eq (V := componentObject K m) (i := m) (Or.inr rfl)).symm ≫
      (Sigma.ι (twoTermComponent K) m).f (m + 1) := by
  rw [sigmaComponentMap, Category.assoc, Category.assoc, (Sigma.ι (twoTermComponent K) m).comm m (m + 1)]
  simp only [twoTermComponent, twoTermComplex_d_eq]
  simp

/-- A specified consecutive composite involving the acyclic coproduct map vanishes. -/
lemma acyclicSigmaComponentMap_pred_comp_d (hK : K.Acyclic) (m : ℤ) :
    acyclicSigmaComponentMap hK (m - 1) m ≫ (∐ twoTermComponent K).d m (m + 1) = 0 := by
  rw [acyclicSigmaComponentMap, dif_pos (show m = m - 1 + 1 by omega), Category.assoc, Category.assoc,
    Category.assoc, (Sigma.ι (twoTermComponent K) (m - 1)).comm m (m + 1)]
  simp only [twoTermComponent, twoTermComplex_d_eq_zero _ _ (show ¬(m = m - 1 ∧ m + 1 = m - 1 + 1) by omega)]
  simp

/-- A morphism from an acyclic complex into the coproduct of its two-term components. -/
noncomputable def acyclicInverse (hK : K.Acyclic) : K ⟶ (∐ twoTermComponent K) where
  f n := sigmaComponentMap K n + acyclicSigmaComponentMap hK (n - 1) n
  comm' m n hmn := by
    rw [ComplexShape.up_Rel] at hmn
    subst hmn
    simp only [show m + 1 - 1 = m from by omega, Preadditive.comp_add, Preadditive.add_comp]
    rw [sigmaComponentMap_comp_d, acyclicSigmaComponentMap_pred_comp_d, add_zero]
    simp only [sigmaComponentMap, acyclicSigmaComponentMap_succ_eq, d_comp_componentRetraction_succ_assoc, d_comp_acyclicComponentMap_assoc,
      zero_comp, zero_add]

/-- Describes a component of the morphism into the coproduct of two-term components. -/
lemma acyclicInverse_f_eq (hK : K.Acyclic) (n : ℤ) :
    (acyclicInverse hK).f n = sigmaComponentMap K n + acyclicSigmaComponentMap hK (n - 1) n := rfl

/-- The acyclic inverse followed by the coproduct-to-complex morphism is the identity. -/
lemma acyclicInverse_comp_sigmaTwoTermComponentToComplex (hK : K.Acyclic) : acyclicInverse hK ≫ sigmaTwoTermComponentToComplex K = 𝟙 K := by
  apply HomologicalComplex.hom_ext
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [HomologicalComplex.comp_f, acyclicInverse_f_eq, show m + 1 - 1 = m from by omega,
    Preadditive.add_comp, sigmaComponentMap, acyclicSigmaComponentMap_succ_eq, Category.assoc, sigmaInclusion_comp_sigmaTwoTermComponentToComplex_f,
    twoTermComponentToComplex, HomologicalComplex.id_f]
  rw [twoTermComplexHom_f_eq (componentSection K (m + 1)) rfl, twoTermComplexHom_f_succ_eq (componentSection K m) rfl]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, eqToHom_trans_assoc]
  apply ModuleCat.hom_ext
  ext x
  exact chosenComplementProjection_add_d_comp_acyclicLift hK m x

/-- The coproduct-to-complex morphism composed with the acyclic inverse is the identity. -/
lemma sigmaTwoTermComponentToComplex_comp_acyclicInverse (hK : K.Acyclic) :
    sigmaTwoTermComponentToComplex K ≫ acyclicInverse hK = 𝟙 (∐ twoTermComponent K) := by
  refine Sigma.hom_ext _ _ fun i => ?_
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [← Category.assoc, sigmaTwoTermComponentToComplex, Sigma.ι_desc, Category.comp_id]
  refine twoTermComplex_hom_ext _ _ ?_ ?_
  · rw [HomologicalComplex.comp_f, acyclicInverse_f_eq, show m + 1 - 1 = m from by omega]
    simp only [twoTermComponentToComplex, twoTermComplexHom_f_eq (componentSection K (m + 1)) rfl, Preadditive.comp_add, sigmaComponentMap,
      acyclicSigmaComponentMap_succ_eq, Category.assoc, eqToHom_refl, Category.comp_id,
      componentSection_comp_componentRetraction_assoc, componentSection_succ_comp_acyclicComponentMap_assoc, Category.id_comp, zero_comp, comp_zero,
      add_zero, eqToHom_trans_assoc]
  · rw [HomologicalComplex.comp_f, acyclicInverse_f_eq, show m + 1 + 1 - 1 = m + 1 from by omega]
    simp only [twoTermComponentToComplex, twoTermComplexHom_f_succ_eq (componentSection K (m + 1)) rfl, Preadditive.comp_add,
      sigmaComponentMap, acyclicSigmaComponentMap_succ_eq, Category.assoc, eqToHom_refl, Category.comp_id,
      d_comp_componentRetraction_succ_assoc, d_comp_acyclicComponentMap_assoc, componentSection_comp_componentRetraction_assoc, Category.id_comp,
      zero_comp, comp_zero, zero_add, eqToHom_trans_assoc]

/-- An acyclic complex is isomorphic to the coproduct of its two-term components. -/
noncomputable def acyclicComplexIsoSigmaTwoTermComponent (hK : K.Acyclic) : K ≅ (∐ twoTermComponent K) where
  hom := acyclicInverse hK
  inv := sigmaTwoTermComponentToComplex K
  hom_inv_id := acyclicInverse_comp_sigmaTwoTermComponentToComplex hK
  inv_hom_id := sigmaTwoTermComponentToComplex_comp_acyclicInverse hK

end DirectSum

open CategoryTheory.Limits in
/-- Every acyclic cochain complex over a field has a decomposition into two-term complexes with invertible differentials. -/
@[source_ref "Chapter7/Exercise7.8.4" (role := supporting)]
theorem exists_acyclicComplexIso_sigmaTwoTermComplex {k : Type u} [Field k]
    (K : CochainComplex (ModuleCat.{u} k) ℤ) (hK : K.Acyclic) :
    ∃ (V : ℤ → ModuleCat.{u} k) (D : ℤ → CochainComplex (ModuleCat.{u} k) ℤ),
      (∀ i, (D i).X i = V i) ∧ (∀ i, (D i).X (i + 1) = V i) ∧
      (∀ i n, ¬(n = i ∨ n = i + 1) → IsZero ((D i).X n)) ∧
      (∀ i, IsIso ((D i).d i (i + 1))) ∧
      Nonempty (K ≅ ∐ D) := by
  refine ⟨componentObject K, twoTermComponent K,
    fun i => twoTermComponentObject_eq (Or.inl rfl),
    fun i => twoTermComponentObject_eq (Or.inr rfl),
    fun i n h => isZero_twoTermComplex_X h,
    fun i => twoTermComplex_d_isIso _ _,
    ⟨acyclicComplexIsoSigmaTwoTermComponent hK⟩⟩

/-- An acyclic cochain complex over a field admits a homotopy from its identity to zero. -/
theorem acyclic_homotopy_id_zero {k : Type u} [Field k]
    (K : CochainComplex (ModuleCat.{u} k) ℤ) (hK : K.Acyclic) :
    Nonempty (Homotopy (𝟙 K) 0) := by
  refine ⟨{ hom := acyclicContractingMap hK, zero := ?_, comm := ?_ }⟩
  · -- the homotopy vanishes off the relation `j + 1 = i`
    intro i j hij
    refine acyclicContractingMap_eq_zero hK (fun h => hij ?_)
    rw [ComplexShape.up_Rel]; exact h.symm
  · -- the homotopy relation, checked degreewise
    intro i
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, i = m + 1 := ⟨i - 1, by ring⟩
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (m + 1) (m + 1 + 1) by simp),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel m (m + 1) by simp),
        acyclicContractingMap_succ_eq, acyclicContractingMap_succ_eq]
    apply ModuleCat.hom_ext
    ext x
    simp only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply,
      HomologicalComplex.zero_f, add_zero]
    exact (acyclicContractingHom_add_d_comp_acyclicContractingHom hK m x).symm

/-- Every short exact complex of vector spaces admits a splitting. -/
@[source_ref "Chapter7/Exercise7.8.4" (role := primary)]
theorem ShortComplex.nonempty_splitting_of_shortExact {k : Type u} [Field k]
    (S : ShortComplex (ModuleCat.{u} k)) (hS : S.ShortExact) :
    Nonempty S.Splitting :=
  ⟨hS.splittingOfProjective⟩

/-- There exists a short exact complex with no splitting. -/
@[source_ref "Chapter7/Exercise7.8.4" (role := supporting)]
theorem exists_shortExact_isEmpty_splitting :
    ∃ S : ShortComplex (ModuleCat.{0} ℤ), S.ShortExact ∧ IsEmpty S.Splitting := by
  let f : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id
  let g : ℤ →ₗ[ℤ] ZMod 2 := (Int.castAddHom (ZMod 2)).toIntLinearMap
  have hf : ∀ x : ℤ, f x = 2 * x := fun x => by simp [f]
  have hg : ∀ x : ℤ, g x = (x : ZMod 2) := fun x => by simp [g, AddMonoidHom.coe_toIntLinearMap]
  have hcomp : g.comp f = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hf, hg, LinearMap.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨x, by push_cast; ring⟩
  refine ⟨ShortComplex.moduleCatMk f g hcomp, ?_, ?_⟩
  · -- Short exactness.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · -- Exactness: `ker g = range f`, i.e. the kernel of `ℤ → ℤ/2` is the even integers.
      rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
      change LinearMap.ker g ≤ LinearMap.range f
      intro x hx
      rw [LinearMap.mem_ker, hg, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, ?_⟩
      rw [hf]
      push_cast at hc
      omega
    · -- `·2` is injective on `ℤ`.
      change Mono (ModuleCat.ofHom f)
      rw [ModuleCat.mono_iff_injective]
      have hinj : Function.Injective f := by
        intro a b hab; rw [hf, hf] at hab; omega
      exact fun a b hab => hinj hab
    · -- `ℤ → ℤ/2` is surjective.
      change Epi (ModuleCat.ofHom g)
      rw [ModuleCat.epi_iff_surjective]
      have hsurj : Function.Surjective g := by
        intro y
        refine ⟨(y.val : ℤ), ?_⟩
        rw [hg]; push_cast; exact ZMod.natCast_zmod_val y
      intro y
      obtain ⟨x, hx⟩ := hsurj y
      exact ⟨x, hx⟩
  · -- No splitting: a retraction `r` of `·2` would give `2 * r 1 = 1` in `ℤ`.
    refine ⟨fun sp => ?_⟩
    let ρ : ℤ →ₗ[ℤ] ℤ := sp.r.hom
    have hr : ρ.comp f = LinearMap.id := by
      have h := ModuleCat.hom_ext_iff.mp sp.f_r
      rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
      exact h
    have key := DFunLike.congr_fun hr (1 : ℤ)
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, mul_one] at key
    have hlin : ρ (2 : ℤ) = 2 * ρ (1 : ℤ) := by
      have h := map_smul ρ (2 : ℤ) (1 : ℤ)
      simpa using h
    rw [hlin] at key
    omega

end RepresentationTheory.HomologicalAlgebra.AcyclicComplexDecomposition
