/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Algebra.Homology.CochainComplex.HomologyComplex
import RepresentationTheory.HomologicalComplex.TensorHomology


set_option backward.isDefEq.respectTransparency false


open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing

universe u

variable {k : Type u} [Field k]

/-- Homology of the negatively extended complex in degree `-n` is isomorphic to the original homology in degree `n`. -/
noncomputable def extendedHomologyIso (C : ChainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (C.extend ComplexShape.embeddingDownNat).homology (-(n : ℤ)) ≅ C.homology n :=
  C.extendHomologyIso ComplexShape.embeddingDownNat (by simp)

/-- The homology isomorphism for negative extension is natural in chain-complex morphisms. -/
@[reassoc]
lemma extendedHomologyIso_naturality {C D : ChainComplex (ModuleCat.{u} k) ℕ} (φ : C ⟶ D)
    (n : ℕ) :
    homologyMap (extendMap φ ComplexShape.embeddingDownNat) (-(n : ℤ)) ≫
        (extendedHomologyIso D n).hom =
      (extendedHomologyIso C n).hom ≫ homologyMap φ n :=
  HomologicalComplex.extendHomologyIso_hom_naturality (φ := φ)
    (e := ComplexShape.embeddingDownNat) (hj' := by simp)

/-- Naturality of the negative-extension homology isomorphism remains valid after postcomposition. -/
add_decl_doc extendedHomologyIso_naturality_assoc

/-- The homology of a negatively extended chain complex vanishes in every positive integer degree. -/
theorem extendedHomology_isZero_of_pos (C : ChainComplex (ModuleCat.{u} k) ℕ) (j' : ℤ) (hj' : 0 < j') :
    IsZero ((C.extend ComplexShape.embeddingDownNat).homology j') := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine HomologicalComplex.extend_exactAt _ _ j' (fun j => ?_)
  simp only [ComplexShape.embeddingDownNat_f]
  omega



/-- Embeds nonnegative chain degrees into integer cochain degrees by sending each degree to its negative. -/
noncomputable abbrev negDegreeEmbedding : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingDownNat

/-- A tensor product is zero when its left factor is zero in a monoidal preadditive category. -/
lemma tensorObj_isZero_of_left {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] {X Y : C} (hX : IsZero X) : IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id, hX.eq_of_src (𝟙 X) 0]
  simp

/-- A tensor product is zero when its right factor is zero in a monoidal preadditive category. -/
lemma tensorObj_isZero_of_right {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] {X Y : C} (hY : IsZero Y) : IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id, hY.eq_of_src (𝟙 Y) 0]
  simp

variable (C D : ChainComplex (ModuleCat.{u} k) ℕ)

/-- Maps the tensor of components in degrees `p` and `q` into degree `n` when their displayed tensor-shape index is `n`. -/
noncomputable abbrev tensorSummandInclusion (p q n : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
    ((curriedTensor (ModuleCat.{u} k)).obj (C.X p)).obj (D.X q) ⟶
      (HomologicalComplex.tensorObj C D).X n :=
  HomologicalComplex.ιMapBifunctor C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ)
    p q n h

/-- Maps a tensor of components of two extended complexes into the component selected by their displayed tensor-shape index. -/
noncomputable abbrev extendedTensorSummandInclusion (a b j : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = j) :
    ((curriedTensor (ModuleCat.{u} k)).obj ((C.extend negDegreeEmbedding).X a)).obj ((D.extend negDegreeEmbedding).X b) ⟶
      (HomologicalComplex.tensorObj (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding)).X j :=
  HomologicalComplex.ιMapBifunctor (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding) (curriedTensor (ModuleCat.{u} k))
    (ComplexShape.up ℤ) a b j h

/-- Maps a summand indexed by integer degrees adding to `-n` into degree `n` of the original tensor complex. -/
noncomputable def extendedTensorSummandToTensorComponent (n : ℕ) (a b : ℤ) (h : a + b = -(n : ℤ)) :
    (C.extend negDegreeEmbedding).X a ⊗ (D.extend negDegreeEmbedding).X b ⟶ (HomologicalComplex.tensorObj C D).X n :=
  match ha : negDegreeEmbedding.r a, hb : negDegreeEmbedding.r b with
  | some p, some q =>
      ((C.extendXIso negDegreeEmbedding (negDegreeEmbedding.f_eq_of_r_eq_some ha)).hom ⊗ₘ
        (D.extendXIso negDegreeEmbedding (negDegreeEmbedding.f_eq_of_r_eq_some hb)).hom) ≫
        tensorSummandInclusion C D p q n (by
          have hp := negDegreeEmbedding.f_eq_of_r_eq_some ha
          have hq := negDegreeEmbedding.f_eq_of_r_eq_some hb
          simp only [ComplexShape.embeddingDownNat_f] at hp hq
          have : p + q = n := by omega
          simpa using this)
  | _, _ => 0

/-- The displayed summand map factors through two extension-component maps and a tensor-summand map. -/
lemma auxiliaryExtendedTensorSummandMapEq (n : ℕ) {a b : ℤ} (h : a + b = -(n : ℤ)) {p q : ℕ}
    (ha : negDegreeEmbedding.r a = some p) (hb : negDegreeEmbedding.r b = some q)
    (hpq : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
    extendedTensorSummandToTensorComponent C D n a b h =
      ((C.extendXIso negDegreeEmbedding (show negDegreeEmbedding.f p = a from negDegreeEmbedding.f_eq_of_r_eq_some ha)).hom ⊗ₘ
        (D.extendXIso negDegreeEmbedding (show negDegreeEmbedding.f q = b from negDegreeEmbedding.f_eq_of_r_eq_some hb)).hom) ≫ tensorSummandInclusion C D p q n hpq := by
  rw [extendedTensorSummandToTensorComponent]
  split
  next p' q' hh1 hh2 =>
    obtain rfl : p' = p := Option.some.inj (hh1 ▸ ha)
    obtain rfl : q' = q := Option.some.inj (hh2 ▸ hb)
    rfl
  next hh => exact (hh p q ha hb).elim

/-- Maps an original tensor summand into the matching negative-degree component of the tensor of extended complexes. -/
noncomputable def tensorSummandToExtendedTensorComponent (n : ℕ) (p q : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
    C.X p ⊗ D.X q ⟶ (HomologicalComplex.tensorObj (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding)).X (-(n : ℤ)) :=
  ((C.extendXIso negDegreeEmbedding (show negDegreeEmbedding.f p = -(p : ℤ) by simp)).inv ⊗ₘ
    (D.extendXIso negDegreeEmbedding (show negDegreeEmbedding.f q = -(q : ℤ) by simp)).inv) ≫
    extendedTensorSummandInclusion C D (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by
      have hpq : p + q = n := by simpa using h
      have : (p : ℤ) + q = n := by exact_mod_cast hpq
      simpa using by omega)

/-- The comparison from the negative-degree component of the tensor of two extended complexes to the corresponding tensor component. -/
noncomputable def extendedTensorComponentToTensorComponent (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding)).X (-(n : ℤ)) ⟶
      (HomologicalComplex.tensorObj C D).X n :=
  HomologicalComplex.mapBifunctorDesc (fun a b h => extendedTensorSummandToTensorComponent C D n a b h)

/-- The comparison from a tensor component to the matching negative-degree component of the tensor of the extended complexes. -/
noncomputable def tensorComponentToExtendedTensorComponent (n : ℕ) :
    (HomologicalComplex.tensorObj C D).X n ⟶
      (HomologicalComplex.tensorObj (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding)).X (-(n : ℤ)) :=
  HomologicalComplex.mapBifunctorDesc (fun p q h => tensorSummandToExtendedTensorComponent C D n p q h)

/-- The partial inverse of the negative-degree embedding sends `-p` back to `p`. -/
lemma negDegreeEmbedding_r_neg (p : ℕ) : negDegreeEmbedding.r (-(p : ℤ)) = some p :=
  negDegreeEmbedding.r_eq_some (show negDegreeEmbedding.f p = -(p : ℤ) by simp)

/-- An extended tensor-summand inclusion followed by the forward comparison gives the associated map to the original tensor component. -/
lemma extendedTensorSummandInclusion_comp_forward (n : ℕ) (a b : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = -(n : ℤ)) :
    extendedTensorSummandInclusion C D a b (-(n : ℤ)) h ≫ extendedTensorComponentToTensorComponent C D n = extendedTensorSummandToTensorComponent C D n a b h := by
  simp only [extendedTensorSummandInclusion, extendedTensorComponentToTensorComponent, ι_mapBifunctorDesc]

/-- The tensor-summand inclusion followed by the reverse comparison is the corresponding inclusion into the extended tensor component. -/
lemma tensorSummandInclusion_comp_reverse (n : ℕ) (p q : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
    tensorSummandInclusion C D p q n h ≫ tensorComponentToExtendedTensorComponent C D n = tensorSummandToExtendedTensorComponent C D n p q h := by
  simp only [tensorSummandInclusion, tensorComponentToExtendedTensorComponent, ι_mapBifunctorDesc]

set_option backward.isDefEq.respectTransparency false in
/-- The extended tensor summand map followed by the forward component comparison is the original tensor-summand inclusion. -/
lemma tensorSummandToExtendedTensorComponent_comp_forward (n p q : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
    tensorSummandToExtendedTensorComponent C D n p q h ≫ extendedTensorComponentToTensorComponent C D n = tensorSummandInclusion C D p q n h := by
  rw [tensorSummandToExtendedTensorComponent, Category.assoc, extendedTensorSummandInclusion_comp_forward, auxiliaryExtendedTensorSummandMapEq C D n _ (negDegreeEmbedding_r_neg p) (negDegreeEmbedding_r_neg q) h]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Composing an extended summand map with the reverse component comparison gives the corresponding extended tensor inclusion. -/
lemma extendedTensorSummandToTensorComponent_comp_reverse (n : ℕ) (a b : ℤ) (h : a + b = -(n : ℤ)) {p q : ℕ}
    (ha : negDegreeEmbedding.r a = some p) (hb : negDegreeEmbedding.r b = some q)
    (hpq : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
    extendedTensorSummandToTensorComponent C D n a b h ≫ tensorComponentToExtendedTensorComponent C D n = extendedTensorSummandInclusion C D a b (-(n : ℤ)) h := by
  obtain rfl : a = -(p : ℤ) := by have := negDegreeEmbedding.f_eq_of_r_eq_some ha; simpa using this.symm
  obtain rfl : b = -(q : ℤ) := by have := negDegreeEmbedding.f_eq_of_r_eq_some hb; simpa using this.symm
  rw [auxiliaryExtendedTensorSummandMapEq C D n _ (negDegreeEmbedding_r_neg p) (negDegreeEmbedding_r_neg q) hpq, Category.assoc, tensorSummandInclusion_comp_reverse, tensorSummandToExtendedTensorComponent]
  simp

/-- The negative-degree component of the tensor of two extended complexes is isomorphic to the corresponding tensor component. -/
noncomputable def extendedTensorComponentIsoTensorComponent (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding)).X (-(n : ℤ)) ≅
      (HomologicalComplex.tensorObj C D).X n where
  hom := extendedTensorComponentToTensorComponent C D n
  inv := tensorComponentToExtendedTensorComponent C D n
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h'
    rw [Category.comp_id, ← Category.assoc,
      show HomologicalComplex.ιMapBifunctor C D _ _ p q n h' = tensorSummandInclusion C D p q n h' from rfl,
      tensorSummandInclusion_comp_reverse]
    exact tensorSummandToExtendedTensorComponent_comp_forward C D n p q h'
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b h'
    rcases ha : negDegreeEmbedding.r a with _ | p
    · exact (tensorObj_isZero_of_left (C.isZero_extend_X' negDegreeEmbedding a ha)).eq_of_src _ _
    rcases hb : negDegreeEmbedding.r b with _ | q
    · exact (tensorObj_isZero_of_right (D.isZero_extend_X' negDegreeEmbedding b hb)).eq_of_src _ _
    have hpq : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n := by
      have hpa := negDegreeEmbedding.f_eq_of_r_eq_some ha
      have hqb := negDegreeEmbedding.f_eq_of_r_eq_some hb
      simp only [ComplexShape.embeddingDownNat_f] at hpa hqb
      have h2 : a + b = -(n : ℤ) := h'
      have : p + q = n := by omega
      simpa using this
    rw [Category.comp_id, ← Category.assoc,
      show HomologicalComplex.ιMapBifunctor (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding) _ _ a b (-(n : ℤ)) h'
        = extendedTensorSummandInclusion C D a b (-(n : ℤ)) h' from rfl,
      extendedTensorSummandInclusion_comp_forward]
    exact extendedTensorSummandToTensorComponent_comp_reverse C D n a b h' ha hb hpq

/-- Positive-degree components of the tensor of two negatively extended chain complexes are zero. -/
lemma extendedTensorComponent_isZero_of_pos (j' : ℤ) (hj' : 0 < j') :
    IsZero ((HomologicalComplex.tensorObj (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding)).X j') := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  have hab' : a + b = j' := hab
  rw [Category.comp_id, comp_zero]
  refine (?_ : IsZero _).eq_of_src _ _
  by_cases ha : a ≤ 0
  · have hb : 0 < b := by omega
    exact tensorObj_isZero_of_right
      (D.isZero_extend_X negDegreeEmbedding b (fun i => by simp only [ComplexShape.embeddingDownNat_f]; omega))
  · exact tensorObj_isZero_of_left
      (C.isZero_extend_X negDegreeEmbedding a (fun i => by simp only [ComplexShape.embeddingDownNat_f]; omega))

/-- The degree map of the negative-degree embedding sends `n` to `-n`. -/
lemma negDegreeEmbedding_f (n : ℕ) : negDegreeEmbedding.f n = -(n : ℤ) := by simp

/-- The negative-degree tensor component of the extended factors is isomorphic to the corresponding component of the extended tensor product. -/
noncomputable def extendedTensorComponentIsoExtendedTensorComponent (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding)).X (-(n : ℤ)) ≅
      ((HomologicalComplex.tensorObj C D).extend negDegreeEmbedding).X (-(n : ℤ)) :=
  extendedTensorComponentIsoTensorComponent C D n ≪≫
    (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) negDegreeEmbedding (negDegreeEmbedding_f n)).symm

/-- At every integer degree, tensoring two extended complexes is isomorphic to extending their tensor product. -/
noncomputable def extendedTensorComponentIso (j' : ℤ) :
    (HomologicalComplex.tensorObj (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding)).X j' ≅
      ((HomologicalComplex.tensorObj C D).extend negDegreeEmbedding).X j' :=
  match hj : negDegreeEmbedding.r j' with
  | some n =>
      eqToIso (congrArg (HomologicalComplex.tensorObj (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding)).X
        (show j' = -(n : ℤ) by
          have := negDegreeEmbedding.f_eq_of_r_eq_some hj
          simp only [ComplexShape.embeddingDownNat_f] at this; omega)) ≪≫
      extendedTensorComponentIsoExtendedTensorComponent C D n ≪≫
      eqToIso (congrArg ((HomologicalComplex.tensorObj C D).extend negDegreeEmbedding).X
        (show -(n : ℤ) = j' by
          have := negDegreeEmbedding.f_eq_of_r_eq_some hj
          simp only [ComplexShape.embeddingDownNat_f] at this; omega))
  | none =>
      IsZero.iso
        (extendedTensorComponent_isZero_of_pos C D j' (by
          by_contra hle
          have hr : negDegreeEmbedding.r j' = some ((-j').toNat) :=
            negDegreeEmbedding.r_eq_some (by simp only [ComplexShape.embeddingDownNat_f]; omega)
          rw [hr] at hj
          simp at hj))
        (HomologicalComplex.isZero_extend_X' _ negDegreeEmbedding j' hj)

/-- The general component isomorphism at degree `-n` agrees with the designated negative-degree isomorphism. -/
lemma extendedTensorComponentIso_neg (n : ℕ) :
    extendedTensorComponentIso C D (-(n : ℤ)) = extendedTensorComponentIsoExtendedTensorComponent C D n := by
  rw [extendedTensorComponentIso]
  split
  next m hm =>
    obtain rfl : m = n := (Option.some.inj ((negDegreeEmbedding_r_neg n).symm.trans hm)).symm
    apply Iso.ext
    simp
  next hm => rw [negDegreeEmbedding_r_neg] at hm; simp at hm

set_option backward.isDefEq.respectTransparency false in
/-- The displayed component-isomorphism composite agrees with the forward tensor comparison at a negative degree. -/
@[simp]
lemma auxiliaryExtendedTensorComponentComparisonEq (n : ℕ) :
    (extendedTensorComponentIso C D (-(n : ℤ))).hom ≫
        (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) negDegreeEmbedding (negDegreeEmbedding_f n)).hom =
      extendedTensorComponentToTensorComponent C D n := by
  rw [extendedTensorComponentIso_neg, extendedTensorComponentIsoExtendedTensorComponent]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The displayed tensor-component map is the composite of two inverse comparison maps. -/
@[simp]
lemma auxiliaryTensorComponentComparisonEq (n : ℕ) :
    (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) negDegreeEmbedding (negDegreeEmbedding_f n)).inv ≫
        (extendedTensorComponentIso C D (-(n : ℤ))).inv = tensorComponentToExtendedTensorComponent C D n := by
  rw [extendedTensorComponentIso_neg, extendedTensorComponentIsoExtendedTensorComponent]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.inv_hom_id_assoc]
  rfl


/-- An auxiliary assertion whose formal type was unavailable in the packet. -/
lemma auxiliaryAssertion (p : ℕ) : Int.negOnePow (-(p : ℤ)) = (-1 : ℤˣ) ^ p := by
  rw [Int.negOnePow_neg]
  simp [Int.negOnePow, zpow_natCast]

/-- The component comparison intertwines the differentials of the extended and original tensor complexes. -/
@[reassoc]
lemma extendedTensorComponentToTensorComponent_comm_d (n : ℕ) :
    extendedTensorComponentToTensorComponent C D (n + 1) ≫ (HomologicalComplex.tensorObj C D).d (n + 1) n =
      (HomologicalComplex.tensorObj (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding)).d (-(↑(n + 1) : ℤ)) (-(n : ℤ)) ≫
        extendedTensorComponentToTensorComponent C D n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  rcases ha : negDegreeEmbedding.r a with _ | p
  · exact (tensorObj_isZero_of_left (C.isZero_extend_X' negDegreeEmbedding a ha)).eq_of_src _ _
  rcases hb : negDegreeEmbedding.r b with _ | q
  · exact (tensorObj_isZero_of_right (D.isZero_extend_X' negDegreeEmbedding b hb)).eq_of_src _ _
  obtain rfl : a = -(p : ℤ) := by
    have := negDegreeEmbedding.f_eq_of_r_eq_some ha
    simp only [ComplexShape.embeddingDownNat_f] at this; omega
  obtain rfl : b = -(q : ℤ) := by
    have := negDegreeEmbedding.f_eq_of_r_eq_some hb
    simp only [ComplexShape.embeddingDownNat_f] at this; omega
  have hpq : p + q = n + 1 := by
    have h2 : (-(p : ℤ)) + (-(q : ℤ)) = -(↑(n + 1) : ℤ) := hab
    omega
  rw [← Category.assoc, extendedTensorSummandInclusion_comp_forward C D (n + 1) (-(p : ℤ)) (-(q : ℤ)) hab,
      auxiliaryExtendedTensorSummandMapEq C D (n + 1) hab (negDegreeEmbedding_r_neg p) (negDegreeEmbedding_r_neg q) hpq, Category.assoc]
  simp only [mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
  refine congr_arg₂ (· + ·) ?_ ?_
  · -- d₁ part (factor 1 differential)
    rcases p with _ | p
    · -- p = 0: both sides vanish (no `down ℕ` relation resp. zero extended differential)
      have h0 : (C.extend negDegreeEmbedding).d 0 1 = 0 :=
        (C.isZero_extend_X negDegreeEmbedding 1
          (fun i => by simp only [ComplexShape.embeddingDownNat_f]; omega)).eq_of_tgt _ _
      rw [mapBifunctor.d₁_eq_zero C D _ (ComplexShape.down ℕ) 0 q n
            (by intro h; rw [ComplexShape.down_Rel] at h; omega), comp_zero,
          show (-(↑(0 : ℕ)) : ℤ) = 0 by simp,
          mapBifunctor.d₁_eq (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding) _ (ComplexShape.up ℤ)
            (show (ComplexShape.up ℤ).Rel 0 1 by simp) (-(q : ℤ)) (-(n : ℤ))
            (by omega : (1 : ℤ) + (-(q : ℤ)) = -(n : ℤ))]
      simp [h0]
    · -- p = p' + 1
      have hpn : p + q = n := by omega
      rw [mapBifunctor.d₁_eq C D _ (ComplexShape.down ℕ)
            (show (ComplexShape.down ℕ).Rel (p + 1) p by rw [ComplexShape.down_Rel]) q n hpn,
          mapBifunctor.d₁_eq (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding) _ (ComplexShape.up ℤ)
            (show (ComplexShape.up ℤ).Rel (-(↑(p + 1) : ℤ)) (-(p : ℤ)) by
              rw [ComplexShape.up_Rel]; push_cast; ring) (-(q : ℤ)) (-(n : ℤ))
            (by omega : (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)),
          extend_d_eq C negDegreeEmbedding (show negDegreeEmbedding.f (p + 1) = -(↑(p + 1) : ℤ) by simp)
            (show negDegreeEmbedding.f p = -(p : ℤ) by simp)]
      dsimp
      simp only [one_smul, Category.assoc]
      rw [extendedTensorSummandInclusion_comp_forward C D n (-(p : ℤ)) (-(q : ℤ))
            (by omega : (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)),
          auxiliaryExtendedTensorSummandMapEq C D n _ (negDegreeEmbedding_r_neg p) (negDegreeEmbedding_r_neg q) hpn]
      simp only [Functor.map_comp, NatTrans.comp_app, curriedTensor_map_app,
        Category.assoc, MonoidalCategory.tensorHom_def, whisker_exchange_assoc,
        ← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id,
        MonoidalCategory.id_whiskerRight, Category.id_comp]
  · -- d₂ part (factor 2 differential)
    rcases q with _ | q
    · -- q = 0: both sides vanish
      have h0 : (D.extend negDegreeEmbedding).d 0 1 = 0 :=
        (D.isZero_extend_X negDegreeEmbedding 1
          (fun i => by simp only [ComplexShape.embeddingDownNat_f]; omega)).eq_of_tgt _ _
      rw [mapBifunctor.d₂_eq_zero C D _ (ComplexShape.down ℕ) p 0 n
            (by intro h; rw [ComplexShape.down_Rel] at h; omega), comp_zero,
          show (-(↑(0 : ℕ)) : ℤ) = 0 by simp,
          mapBifunctor.d₂_eq (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding) _ (ComplexShape.up ℤ) (-(p : ℤ))
            (show (ComplexShape.up ℤ).Rel 0 1 by simp) (-(n : ℤ))
            (by omega : (-(p : ℤ)) + (1 : ℤ) = -(n : ℤ))]
      simp [h0]
    · -- q = q' + 1
      have hpn : p + q = n := by omega
      rw [mapBifunctor.d₂_eq C D _ (ComplexShape.down ℕ) p
            (show (ComplexShape.down ℕ).Rel (q + 1) q by rw [ComplexShape.down_Rel]) n hpn,
          mapBifunctor.d₂_eq (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding) _ (ComplexShape.up ℤ) (-(p : ℤ))
            (show (ComplexShape.up ℤ).Rel (-(↑(q + 1) : ℤ)) (-(q : ℤ)) by
              rw [ComplexShape.up_Rel]; push_cast; ring) (-(n : ℤ))
            (by omega : (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)),
          extend_d_eq D negDegreeEmbedding (show negDegreeEmbedding.f (q + 1) = -(↑(q + 1) : ℤ) by simp)
            (show negDegreeEmbedding.f q = -(q : ℤ) by simp)]
      dsimp
      simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
      rw [extendedTensorSummandInclusion_comp_forward C D n (-(p : ℤ)) (-(q : ℤ))
            (by omega : (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)),
          auxiliaryExtendedTensorSummandMapEq C D n _ (negDegreeEmbedding_r_neg p) (negDegreeEmbedding_r_neg q) hpn, auxiliaryAssertion]
      congr 1
      simp only [curriedTensor_obj_map, Category.assoc,
        MonoidalCategory.tensorHom_def, ← whisker_exchange_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The differential compatibility of the component comparison remains valid after postcomposition. -/
add_decl_doc extendedTensorComponentToTensorComponent_comm_d_assoc

/-- Tensoring two negatively extended chain complexes is isomorphic to negatively extending their tensor product. -/
noncomputable def tensorExtendIsoExtendTensor :
    HomologicalComplex.tensorObj (C.extend negDegreeEmbedding) (D.extend negDegreeEmbedding) ≅
      (HomologicalComplex.tensorObj C D).extend negDegreeEmbedding :=
  HomologicalComplex.Hom.isoOfComponents (fun j' => extendedTensorComponentIso C D j') (by
    intro i j hij
    by_cases hj : 0 < j
    · exact (HomologicalComplex.isZero_extend_X _ negDegreeEmbedding j
        (fun m => by simp only [ComplexShape.embeddingDownNat_f]; omega)).eq_of_tgt _ _
    · rw [not_lt] at hj
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
      obtain rfl : i = -(↑(n + 1) : ℤ) := by
        have : i + 1 = -(n : ℤ) := hij
        push_cast; omega
      rw [HomologicalComplex.extend_d_eq (HomologicalComplex.tensorObj C D) negDegreeEmbedding
            (negDegreeEmbedding_f (n + 1)) (negDegreeEmbedding_f n),
          ← Category.assoc, auxiliaryExtendedTensorComponentComparisonEq C D (n + 1),
          extendedTensorComponentToTensorComponent_comm_d_assoc C D n]
      congr 1
      rw [← auxiliaryExtendedTensorComponentComparisonEq C D n, Category.assoc, Iso.hom_inv_id,
        Category.comp_id])


section Naturality

variable {C₁ C₂ D₁ D₂ : ChainComplex (ModuleCat.{u} k) ℕ}

/-- The component comparison is natural in morphisms of both chain complexes. -/
lemma extendedTensorComponentToTensorComponent_naturality (f : C₁ ⟶ C₂) (g : D₁ ⟶ D₂) (n : ℕ) :
    (HomologicalComplex.tensorHom (HomologicalComplex.extendMap f negDegreeEmbedding)
          (HomologicalComplex.extendMap g negDegreeEmbedding)).f (-(n : ℤ)) ≫ extendedTensorComponentToTensorComponent C₂ D₂ n =
      extendedTensorComponentToTensorComponent C₁ D₁ n ≫ (HomologicalComplex.tensorHom f g).f n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  rcases ha : negDegreeEmbedding.r a with _ | p
  · exact (tensorObj_isZero_of_left (C₁.isZero_extend_X' negDegreeEmbedding a ha)).eq_of_src _ _
  rcases hb : negDegreeEmbedding.r b with _ | q
  · exact (tensorObj_isZero_of_right (D₁.isZero_extend_X' negDegreeEmbedding b hb)).eq_of_src _ _
  obtain rfl : a = -(p : ℤ) := by have := negDegreeEmbedding.f_eq_of_r_eq_some ha; simpa using this.symm
  obtain rfl : b = -(q : ℤ) := by have := negDegreeEmbedding.f_eq_of_r_eq_some hb; simpa using this.symm
  have hab' : (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ) := hab
  have hpq : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n := by
    have : p + q = n := by omega
    simpa using this
  rw [show HomologicalComplex.ιMapBifunctor (C₁.extend negDegreeEmbedding) (D₁.extend negDegreeEmbedding)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
        (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) hab = extendedTensorSummandInclusion C₁ D₁ _ _ _ hab from rfl]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, extendedTensorSummandInclusion_comp_forward,
    auxiliaryExtendedTensorSummandMapEq C₂ D₂ n _ (negDegreeEmbedding_r_neg p) (negDegreeEmbedding_r_neg q) hpq,
    ← Category.assoc (extendedTensorSummandInclusion C₁ D₁ _ _ _ hab), extendedTensorSummandInclusion_comp_forward,
    auxiliaryExtendedTensorSummandMapEq C₁ D₁ n _ (negDegreeEmbedding_r_neg p) (negDegreeEmbedding_r_neg q) hpq,
    Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.extendMap_f f negDegreeEmbedding (negDegreeEmbedding_f p),
    HomologicalComplex.extendMap_f g negDegreeEmbedding (negDegreeEmbedding_f q)]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp,
    Iso.inv_hom_id]

-- The reassociated form of `auxiliaryExtendedTensorComponentComparisonEq`, used to strip the extend
-- transport off the middle of a composite in `tensorExtendIsoExtendTensor_naturality`.
attribute [reassoc] auxiliaryExtendedTensorComponentComparisonEq

/-- The displayed component-isomorphism identity remains valid after postcomposition. -/
add_decl_doc auxiliaryExtendedTensorComponentComparisonEq_assoc

namespace Auxiliary

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias statement016350 := auxiliaryExtendedTensorComponentComparisonEq

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias statement016351 := auxiliaryExtendedTensorComponentComparisonEq_assoc

end Auxiliary

/-- The tensor-extension isomorphism is natural in morphisms of both chain complexes. -/
theorem tensorExtendIsoExtendTensor_naturality (f : C₁ ⟶ C₂) (g : D₁ ⟶ D₂) :
    HomologicalComplex.tensorHom (HomologicalComplex.extendMap f negDegreeEmbedding)
          (HomologicalComplex.extendMap g negDegreeEmbedding) ≫ (tensorExtendIsoExtendTensor C₂ D₂).hom =
      (tensorExtendIsoExtendTensor C₁ D₁).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom f g) negDegreeEmbedding := by
  ext j' : 1
  by_cases hj : 0 < j'
  · exact (HomologicalComplex.isZero_extend_X (HomologicalComplex.tensorObj C₂ D₂) negDegreeEmbedding j'
      (fun m => by simp only [ComplexShape.embeddingDownNat_f]; omega)).eq_of_tgt _ _
  · rw [not_lt] at hj
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j' = -(n : ℤ) := ⟨(-j').toNat, by omega⟩
    rw [← cancel_mono (HomologicalComplex.extendXIso
      (HomologicalComplex.tensorObj C₂ D₂) negDegreeEmbedding (negDegreeEmbedding_f n)).hom,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
      show (tensorExtendIsoExtendTensor C₂ D₂).hom.f (-(n : ℤ)) = (extendedTensorComponentIso C₂ D₂ (-(n : ℤ))).hom
        from rfl,
      show (tensorExtendIsoExtendTensor C₁ D₁).hom.f (-(n : ℤ)) = (extendedTensorComponentIso C₁ D₁ (-(n : ℤ))).hom
        from rfl,
      auxiliaryExtendedTensorComponentComparisonEq,
      HomologicalComplex.extendMap_f (HomologicalComplex.tensorHom f g) negDegreeEmbedding (negDegreeEmbedding_f n),
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      auxiliaryExtendedTensorComponentComparisonEq_assoc]
    exact extendedTensorComponentToTensorComponent_naturality f g n

/-- The tensor-extension isomorphism is natural in a morphism of the left chain complex. -/
theorem tensorExtendIsoExtendTensor_naturality_left (f : C₁ ⟶ C₂)
    (D : ChainComplex (ModuleCat.{u} k) ℕ) :
    HomologicalComplex.tensorHom (HomologicalComplex.extendMap f negDegreeEmbedding) (𝟙 (D.extend negDegreeEmbedding)) ≫
        (tensorExtendIsoExtendTensor C₂ D).hom =
      (tensorExtendIsoExtendTensor C₁ D).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom f (𝟙 D)) negDegreeEmbedding := by
  simpa using tensorExtendIsoExtendTensor_naturality f (𝟙 D)

/-- The tensor-extension isomorphism is natural in a morphism of the right chain complex. -/
theorem tensorExtendIsoExtendTensor_naturality_right (C : ChainComplex (ModuleCat.{u} k) ℕ)
    (g : D₁ ⟶ D₂) :
    HomologicalComplex.tensorHom (𝟙 (C.extend negDegreeEmbedding)) (HomologicalComplex.extendMap g negDegreeEmbedding) ≫
        (tensorExtendIsoExtendTensor C D₂).hom =
      (tensorExtendIsoExtendTensor C D₁).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom (𝟙 C) g) negDegreeEmbedding := by
  simpa using tensorExtendIsoExtendTensor_naturality (𝟙 C) g

end Naturality

section Bifunctor

/-- An auxiliary curried endofunctor-valued functor on integer-graded cochain complexes over a field. -/
noncomputable abbrev auxiliaryCochainComplexBifunctor :
    CochainComplex (ModuleCat.{u} k) ℤ ⥤ CochainComplex (ModuleCat.{u} k) ℤ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  (curriedTensor (ModuleCat.{u} k)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- An auxiliary curried endofunctor-valued functor on nonnegatively graded chain complexes over a field. -/
noncomputable abbrev auxiliaryChainComplexBifunctor :
    ChainComplex (ModuleCat.{u} k) ℕ ⥤ ChainComplex (ModuleCat.{u} k) ℕ ⥤
      ChainComplex (ModuleCat.{u} k) ℕ :=
  (curriedTensor (ModuleCat.{u} k)).map₂HomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)

/-- The functor from nonnegatively graded chain complexes to integer-graded cochain complexes. -/
noncomputable abbrev chainToCochainFunctor :
    ChainComplex (ModuleCat.{u} k) ℕ ⥤ CochainComplex (ModuleCat.{u} k) ℤ :=
  negDegreeEmbedding.extendFunctor (ModuleCat.{u} k)

/-- An auxiliary functor assigning to each chain complex a functor from chain complexes to cochain complexes. -/
noncomputable abbrev auxiliaryChainToCochainBifunctorSource :
    ChainComplex (ModuleCat.{u} k) ℕ ⥤ ChainComplex (ModuleCat.{u} k) ℕ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  (chainToCochainFunctor ⋙ auxiliaryCochainComplexBifunctor) ⋙
    (CategoryTheory.Functor.whiskeringLeft (ChainComplex (ModuleCat.{u} k) ℕ)
      (CochainComplex (ModuleCat.{u} k) ℤ)
      (CochainComplex (ModuleCat.{u} k) ℤ)).obj chainToCochainFunctor

/-- An auxiliary functor assigning to each chain complex a functor from chain complexes to cochain complexes. -/
noncomputable abbrev auxiliaryChainToCochainBifunctorTarget :
    ChainComplex (ModuleCat.{u} k) ℕ ⥤ ChainComplex (ModuleCat.{u} k) ℕ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  auxiliaryChainComplexBifunctor ⋙
    (CategoryTheory.Functor.whiskeringRight (ChainComplex (ModuleCat.{u} k) ℕ)
      (ChainComplex (ModuleCat.{u} k) ℕ)
      (CochainComplex (ModuleCat.{u} k) ℤ)).obj chainToCochainFunctor

/-- An isomorphism between the two displayed auxiliary chain-to-cochain bifunctors. -/
noncomputable def auxiliaryChainToCochainBifunctorIso :
    auxiliaryChainToCochainBifunctorSource (k := k) ≅ auxiliaryChainToCochainBifunctorTarget (k := k) :=
  NatIso.ofComponents
    (fun C => NatIso.ofComponents (fun D => tensorExtendIsoExtendTensor C D) (fun {D₁ D₂} g => by
      have h := tensorExtendIsoExtendTensor_naturality (𝟙 C) g
      rw [HomologicalComplex.extendMap_id] at h
      exact h))
    (fun {C₁ C₂} f => by
      ext D : 2
      simp only [NatTrans.comp_app]
      have h := tensorExtendIsoExtendTensor_naturality f (𝟙 D)
      rw [HomologicalComplex.extendMap_id] at h
      exact h)

/-- Each component of the auxiliary bifunctor isomorphism agrees with the tensor-extension isomorphism. -/
@[simp]
lemma auxiliaryChainToCochainBifunctorIso_app (C D : ChainComplex (ModuleCat.{u} k) ℕ) :
    (auxiliaryChainToCochainBifunctorIso.app C).app D = tensorExtendIsoExtendTensor C D :=
  rfl

end Bifunctor


section CoproductSupport

open Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {J I : Type*} {F : J → C} {G : I → C} [HasCoproduct F] [HasCoproduct G]

open Classical in
/-- Maps one coproduct to another using a reindexing and isomorphisms between the selected summands. -/
noncomputable def sigmaMapOfReindex (ι : I → J) (iso : ∀ a, F (ι a) ≅ G a) : (∐ F) ⟶ (∐ G) :=
  Sigma.desc fun j =>
    if h : ∃ a, ι a = j then
      eqToHom (congrArg F h.choose_spec.symm) ≫ (iso h.choose).hom ≫ Sigma.ι G h.choose
    else 0

/-- Maps the reindexed coproduct back to the original coproduct using the inverse summand isomorphisms. -/
noncomputable def sigmaMapOfReindexInv (ι : I → J) (iso : ∀ a, F (ι a) ≅ G a) : (∐ G) ⟶ (∐ F) :=
  Sigma.desc fun a => (iso a).inv ≫ Sigma.ι F (ι a)

omit [HasZeroMorphisms C] [HasZeroObject C] in
/-- The reverse coproduct map carries each injection through the inverse of its summand isomorphism. -/
@[reassoc]
lemma sigmaInclusion_comp_sigmaMapOfReindexInv (ι : I → J) (iso : ∀ a, F (ι a) ≅ G a) (a : I) :
    Sigma.ι G a ≫ sigmaMapOfReindexInv ι iso = (iso a).inv ≫ Sigma.ι F (ι a) := by
  rw [sigmaMapOfReindexInv, Sigma.ι_desc]

/-- The formula for the reverse coproduct map on injections remains valid after postcomposition. -/
add_decl_doc sigmaInclusion_comp_sigmaMapOfReindexInv_assoc

omit [HasZeroObject C] in
/-- For an injective reindexing, the forward coproduct map carries each selected injection through its summand isomorphism. -/
@[reassoc]
lemma sigmaInclusion_comp_sigmaMapOfReindex (ι : I → J) (hι : Function.Injective ι) (iso : ∀ a, F (ι a) ≅ G a) (a : I) :
    Sigma.ι F (ι a) ≫ sigmaMapOfReindex ι iso = (iso a).hom ≫ Sigma.ι G a := by
  rw [sigmaMapOfReindex, Sigma.ι_desc, dif_pos ⟨a, rfl⟩]
  suffices H : ∀ (c : I) (hc : ι c = ι a),
      eqToHom (congrArg F hc.symm) ≫ (iso c).hom ≫ Sigma.ι G c = (iso a).hom ≫ Sigma.ι G a by
    exact H _ (Exists.choose_spec (⟨a, rfl⟩ : ∃ a', ι a' = ι a))
  intro c hc
  obtain rfl : c = a := hι hc
  simp

/-- The formula for the forward coproduct map on selected injections remains valid after postcomposition. -/
add_decl_doc sigmaInclusion_comp_sigmaMapOfReindex_assoc

/-- Constructs an isomorphism of coproducts from an injective reindexing, isomorphisms on its image, and vanishing of the remaining summands. -/
noncomputable def sigmaIsoOfInjective (ι : I → J) (hι : Function.Injective ι)
    (iso : ∀ a, F (ι a) ≅ G a) (hz : ∀ j, (∀ a, ι a ≠ j) → IsZero (F j)) :
    (∐ F) ≅ (∐ G) where
  hom := sigmaMapOfReindex ι iso
  inv := sigmaMapOfReindexInv ι iso
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Category.comp_id]
    by_cases h : ∃ a, ι a = j
    · obtain ⟨a, rfl⟩ := h
      rw [sigmaInclusion_comp_sigmaMapOfReindex_assoc ι hι iso, sigmaInclusion_comp_sigmaMapOfReindexInv, Iso.hom_inv_id_assoc]
    · have hj : ∀ a, ι a ≠ j := fun a ha => h ⟨a, ha⟩
      rw [(hz j hj).eq_of_src (Sigma.ι F j) 0, zero_comp]
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun a => ?_
    rw [Category.comp_id, sigmaInclusion_comp_sigmaMapOfReindexInv_assoc, sigmaInclusion_comp_sigmaMapOfReindex ι hι iso, Iso.inv_hom_id_assoc]

end CoproductSupport

/-- There exists an isomorphism between the tensor of two negatively extended complexes and the negative extension of their tensor product. -/
theorem nonempty_tensorExtendIsoExtendTensor (C D : ChainComplex (ModuleCat.{u} k) ℕ) :
    Nonempty (HomologicalComplex.tensorObj (C.extend ComplexShape.embeddingDownNat)
        (D.extend ComplexShape.embeddingDownNat) ≅
      (HomologicalComplex.tensorObj C D).extend ComplexShape.embeddingDownNat) :=
  ⟨tensorExtendIsoExtendTensor C D⟩

/-- An isomorphism from tensor-product homology to the displayed coproduct of tensor products of homology objects. -/
noncomputable def homologyTensorIsoSigma (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (HomologicalComplex.tensorObj C D).homology i ≅
      ∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) =>
        C.homology p.1.1 ⊗ D.homology p.1.2 := by
  let e := ComplexShape.embeddingDownNat
  -- Step 1: `Hᵢ(C ⊗ D) ≅ H_{-i}(extend (C ⊗ D))`.
  let α₁ : (HomologicalComplex.tensorObj C D).homology i ≅
      ((HomologicalComplex.tensorObj C D).extend e).homology (-(i : ℤ)) :=
    (extendedHomologyIso (HomologicalComplex.tensorObj C D) i).symm
  -- Step 2: apply `H_{-i}` to the compatibility iso `extend (C ⊗ D) ≅ extend C ⊗ extend D`.
  let φ : (HomologicalComplex.tensorObj C D).extend e ≅
      HomologicalComplex.tensorObj (C.extend e) (D.extend e) :=
    (tensorExtendIsoExtendTensor C D).symm
  let α₂ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ)
    (-(i : ℤ))).mapIso φ
  -- Step 3: Chapter 7's universe-general Künneth at degree `-i`, as the honest isomorphism
  -- inverse to the natural cross product `kunnethMap`.
  let α₃ := _root_.RepresentationTheory.HomologicalComplex.TensorHomology.homologyTensorToSigmaIso
      (C.extend e) (D.extend e) (-(i : ℤ))
  -- Step 4: reindex the `ℤ`-coproduct `⨁_{a+b=-i}` onto the `ℕ`-antidiagonal `⨁_{p+q=i}`;
  -- the summands with `a > 0` or `b > 0` vanish by `extendedHomology_isZero_of_pos`.
  let ι : {p : ℕ × ℕ // p.1 + p.2 = i} → {p : ℤ × ℤ // p.1 + p.2 = -(i : ℤ)} :=
    fun p => ⟨(-(p.1.1 : ℤ), -(p.1.2 : ℤ)), by
      have h2 : (p.1.1 : ℤ) + (p.1.2 : ℤ) = (i : ℤ) := by exact_mod_cast p.2
      change -(p.1.1 : ℤ) + -(p.1.2 : ℤ) = -(i : ℤ); omega⟩
  have hι : Function.Injective ι := by
    intro p p' hpp
    apply Subtype.ext
    have hv : (ι p).1 = (ι p').1 := congrArg Subtype.val hpp
    have h1 : (p.1.1 : ℤ) = (p'.1.1 : ℤ) := neg_injective (congrArg Prod.fst hv)
    have h2 : (p.1.2 : ℤ) = (p'.1.2 : ℤ) := neg_injective (congrArg Prod.snd hv)
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  let α₄ : (∐ fun (p : {p : ℤ × ℤ // p.1 + p.2 = -(i : ℤ)}) =>
        (C.extend e).homology p.1.1 ⊗ (D.extend e).homology p.1.2) ≅
      (∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) => C.homology p.1.1 ⊗ D.homology p.1.2) :=
    sigmaIsoOfInjective ι hι
      (fun a => tensorIso (extendedHomologyIso C a.1.1) (extendedHomologyIso D a.1.2))
      (by
        rintro ⟨⟨a, b⟩, hab⟩ hj
        by_cases ha : 0 < a
        · exact tensorObj_isZero_of_left (extendedHomology_isZero_of_pos C a ha)
        by_cases hb : 0 < b
        · exact tensorObj_isZero_of_right (extendedHomology_isZero_of_pos D b hb)
        rw [not_lt] at ha hb
        exfalso
        have hp : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
        have hq : ((-b).toNat : ℤ) = -b := Int.toNat_of_nonneg (by omega)
        have hpq : (-a).toNat + (-b).toNat = i := by
          have : ((-a).toNat : ℤ) + ((-b).toNat : ℤ) = (i : ℤ) := by rw [hp, hq]; omega
          exact_mod_cast this
        refine hj ⟨((-a).toNat, (-b).toNat), hpq⟩ (Subtype.ext ?_)
        change (-(((-a).toNat : ℕ) : ℤ), -(((-b).toNat : ℕ) : ℤ)) = (a, b)
        rw [Prod.mk.injEq]
        exact ⟨by rw [hp]; ring, by rw [hq]; ring⟩)
  exact α₁ ≪≫ α₂ ≪≫ α₃ ≪≫ α₄

/-- There exists an isomorphism from tensor-product homology to the displayed coproduct of tensor products of homology objects. -/
theorem nonempty_homologyTensorIsoSigma (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    Nonempty ((HomologicalComplex.tensorObj C D).homology i ≅
      ∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) =>
        C.homology p.1.1 ⊗ D.homology p.1.2) :=
  ⟨homologyTensorIsoSigma C D i⟩

end RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing
