/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Algebra.Homology.CochainComplex.HomologyComplex
import RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing

set_option backward.isDefEq.respectTransparency false



open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace RepresentationTheory.HomologicalComplex.TensorExtension

universe u

variable {k : Type u} [Field k]


/-- The tensor sign convention for the upward complex shape indexed by natural numbers. -/
instance natTensorSigns : (ComplexShape.up ℕ).TensorSigns where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by simp only [ComplexShape.up_Rel]; omega
  add_rel p q r (hpq : p + 1 = q) := by simp only [ComplexShape.up_Rel]; omega
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ) ^ (p + 1) = -(-1 : ℤˣ) ^ p
    rw [pow_add, pow_one, mul_neg, mul_one]

/-- An auxiliary theorem depending on the tensor signs for natural cochain degrees whose proposition is unavailable in the packet. -/
@[simp]
lemma natTensorSigns_opaqueAuxiliary (n : ℕ) : (ComplexShape.up ℕ).ε n = (-1 : ℤˣ) ^ n := rfl


/-- Homology after extension at a cast natural degree is isomorphic to homology of the original complex. -/
noncomputable def homologyExtendIso (C : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (C.extend ComplexShape.embeddingUpNat).homology (n : ℤ) ≅ C.homology n :=
  C.extendHomologyIso ComplexShape.embeddingUpNat (by simp)


/-- The homology extension isomorphism is natural with respect to a cochain map. -/
@[reassoc]
lemma homologyExtendIso_naturality {C D : CochainComplex (ModuleCat.{u} k) ℕ} (φ : C ⟶ D)
    (n : ℕ) :
    homologyMap (extendMap φ ComplexShape.embeddingUpNat) (n : ℤ) ≫
        (homologyExtendIso D n).hom =
      (homologyExtendIso C n).hom ≫ homologyMap φ n :=
  HomologicalComplex.extendHomologyIso_hom_naturality (φ := φ)
    (e := ComplexShape.embeddingUpNat) (hj' := by simp)


/-- Naturality of the homology extension isomorphism remains valid after postcomposition. -/
add_decl_doc homologyExtendIso_naturality_assoc

/-- The homology of a natural-graded cochain complex extended to a negative integer degree is zero. -/
theorem isZero_homology_extend_of_neg (C : CochainComplex (ModuleCat.{u} k) ℕ) (j' : ℤ) (hj' : j' < 0) :
    IsZero ((C.extend ComplexShape.embeddingUpNat).homology j') := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine HomologicalComplex.extend_exactAt _ _ j' (fun j => ?_)
  simp only [ComplexShape.embeddingUpNat_f]
  omega





/-- The embedding of the upward natural-number complex shape into the upward integer complex shape. -/
noncomputable abbrev natToIntEmbedding : ComplexShape.Embedding (ComplexShape.up ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpNat


/-- Tensoring a zero object on the left in a monoidal preadditive category produces a zero object. -/
lemma isZero_tensorObj_of_left {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] {X Y : C} (hX : IsZero X) : IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id, hX.eq_of_src (𝟙 X) 0]
  simp


/-- Tensoring a zero object on the right in a monoidal preadditive category produces a zero object. -/
lemma isZero_tensorObj_of_right {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] {X Y : C} (hY : IsZero Y) : IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id, hY.eq_of_src (𝟙 Y) 0]
  simp

variable (C D : CochainComplex (ModuleCat.{u} k) ℕ)


/-- The tensor of two natural-degree components maps to the component of their tensor complex in the summed degree. -/
noncomputable abbrev tensorSummandToTensorComponent (p q n : ℕ)
    (h : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    ((curriedTensor (ModuleCat.{u} k)).obj (C.X p)).obj (D.X q) ⟶
      (HomologicalComplex.tensorObj C D).X n :=
  HomologicalComplex.ιMapBifunctor C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)
    p q n h


/-- The tensor of two components of extended complexes maps to the component of their integer-graded tensor product in the summed degree. -/
noncomputable abbrev extendedTensorSummandMap (a b j : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = j) :
    ((curriedTensor (ModuleCat.{u} k)).obj ((C.extend natToIntEmbedding).X a)).obj ((D.extend natToIntEmbedding).X b) ⟶
      (HomologicalComplex.tensorObj (C.extend natToIntEmbedding) (D.extend natToIntEmbedding)).X j :=
  HomologicalComplex.ιMapBifunctor (C.extend natToIntEmbedding) (D.extend natToIntEmbedding) (curriedTensor (ModuleCat.{u} k))
    (ComplexShape.up ℤ) a b j h


/-- A summand in complementary integer degrees maps from the tensor of extensions to the corresponding natural tensor component. -/
noncomputable def extendedTensorSummandToTensorComponent (n : ℕ) (a b : ℤ) (h : a + b = (n : ℤ)) :
    (C.extend natToIntEmbedding).X a ⊗ (D.extend natToIntEmbedding).X b ⟶ (HomologicalComplex.tensorObj C D).X n :=
  match ha : natToIntEmbedding.r a, hb : natToIntEmbedding.r b with
  | some p, some q =>
      ((C.extendXIso natToIntEmbedding (natToIntEmbedding.f_eq_of_r_eq_some ha)).hom ⊗ₘ
        (D.extendXIso natToIntEmbedding (natToIntEmbedding.f_eq_of_r_eq_some hb)).hom) ≫
        tensorSummandToTensorComponent C D p q n (by
          have hp := natToIntEmbedding.f_eq_of_r_eq_some ha
          have hq := natToIntEmbedding.f_eq_of_r_eq_some hb
          simp only [ComplexShape.embeddingUpNat_f] at hp hq
          have : p + q = n := by omega
          simpa using this)
  | _, _ => 0


/-- The summand map agrees with tensoring the extension component isomorphisms and then applying the natural-graded tensor summand map. -/
lemma extendedTensorSummandToTensorComponent_eq (n : ℕ) {a b : ℤ} (h : a + b = (n : ℤ)) {p q : ℕ}
    (ha : natToIntEmbedding.r a = some p) (hb : natToIntEmbedding.r b = some q)
    (hpq : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    extendedTensorSummandToTensorComponent C D n a b h =
      ((C.extendXIso natToIntEmbedding (show natToIntEmbedding.f p = a from natToIntEmbedding.f_eq_of_r_eq_some ha)).hom ⊗ₘ
        (D.extendXIso natToIntEmbedding (show natToIntEmbedding.f q = b from natToIntEmbedding.f_eq_of_r_eq_some hb)).hom) ≫ tensorSummandToTensorComponent C D p q n hpq := by
  rw [extendedTensorSummandToTensorComponent]
  split
  next p' q' hh1 hh2 =>
    obtain rfl : p' = p := Option.some.inj (hh1 ▸ ha)
    obtain rfl : q' = q := Option.some.inj (hh2 ▸ hb)
    rfl
  next hh => exact (hh p q ha hb).elim


/-- A tensor of components in two natural degrees maps to the cast degree of the tensor of their integer extensions. -/
noncomputable def tensorSummandToExtendedTensorComponent (n : ℕ) (p q : ℕ)
    (h : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    C.X p ⊗ D.X q ⟶ (HomologicalComplex.tensorObj (C.extend natToIntEmbedding) (D.extend natToIntEmbedding)).X (n : ℤ) :=
  ((C.extendXIso natToIntEmbedding (show natToIntEmbedding.f p = (p : ℤ) by simp)).inv ⊗ₘ
    (D.extendXIso natToIntEmbedding (show natToIntEmbedding.f q = (q : ℤ) by simp)).inv) ≫
    extendedTensorSummandMap C D (p : ℤ) (q : ℤ) (n : ℤ) (by
      have hpq : p + q = n := by simpa using h
      have : (p : ℤ) + q = n := by exact_mod_cast hpq
      simpa using this)


/-- The component map from the tensor of two integer extensions to the tensor of the original complexes at a natural degree. -/
noncomputable def extendedTensorToTensorComponent (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend natToIntEmbedding) (D.extend natToIntEmbedding)).X (n : ℤ) ⟶
      (HomologicalComplex.tensorObj C D).X n :=
  HomologicalComplex.mapBifunctorDesc (fun a b h => extendedTensorSummandToTensorComponent C D n a b h)


/-- The component map from the tensor of the original complexes to the tensor of their integer extensions. -/
noncomputable def tensorToExtendedTensorComponent (n : ℕ) :
    (HomologicalComplex.tensorObj C D).X n ⟶
      (HomologicalComplex.tensorObj (C.extend natToIntEmbedding) (D.extend natToIntEmbedding)).X (n : ℤ) :=
  HomologicalComplex.mapBifunctorDesc (fun p q h => tensorSummandToExtendedTensorComponent C D n p q h)


/-- The reverse degree map of the natural-to-integer embedding recovers a natural number from its integer cast. -/
lemma natToIntEmbedding_reverse_apply (p : ℕ) : natToIntEmbedding.r (p : ℤ) = some p :=
  natToIntEmbedding.r_eq_some (show natToIntEmbedding.f p = (p : ℤ) by simp)


/-- At a cast natural degree, the integer tensor summand map followed by the component comparison is the corresponding map to the natural tensor component. -/
lemma extendedTensorSummandMap_toTensor (n : ℕ) (a b : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = (n : ℤ)) :
    extendedTensorSummandMap C D a b (n : ℤ) h ≫ extendedTensorToTensorComponent C D n = extendedTensorSummandToTensorComponent C D n a b h := by
  simp only [extendedTensorSummandMap, extendedTensorToTensorComponent, ι_mapBifunctorDesc]


/-- The natural tensor summand map followed by the reverse component comparison is the map into the tensor of extensions. -/
lemma tensorSummandToTensorComponent_toExtended (n : ℕ) (p q : ℕ)
    (h : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    tensorSummandToTensorComponent C D p q n h ≫ tensorToExtendedTensorComponent C D n = tensorSummandToExtendedTensorComponent C D n p q h := by
  simp only [tensorSummandToTensorComponent, tensorToExtendedTensorComponent, ι_mapBifunctorDesc]

set_option backward.isDefEq.respectTransparency false in

/-- The map into the tensor of extensions followed by the component comparison is the ordinary tensor summand map. -/
lemma tensorSummandToExtendedTensorComponent_toTensor (n p q : ℕ)
    (h : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    tensorSummandToExtendedTensorComponent C D n p q h ≫ extendedTensorToTensorComponent C D n = tensorSummandToTensorComponent C D p q n h := by
  rw [tensorSummandToExtendedTensorComponent, Category.assoc, extendedTensorSummandMap_toTensor, extendedTensorSummandToTensorComponent_eq C D n _ (natToIntEmbedding_reverse_apply p) (natToIntEmbedding_reverse_apply q) h]
  simp

set_option backward.isDefEq.respectTransparency false in

/-- After identifying integer degrees with natural degrees, the summand map followed by the reverse component comparison is the integer-graded tensor summand map. -/
lemma extendedTensorSummandToTensorComponent_toExtended (n : ℕ) (a b : ℤ) (h : a + b = (n : ℤ)) {p q : ℕ}
    (ha : natToIntEmbedding.r a = some p) (hb : natToIntEmbedding.r b = some q)
    (hpq : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    extendedTensorSummandToTensorComponent C D n a b h ≫ tensorToExtendedTensorComponent C D n = extendedTensorSummandMap C D a b (n : ℤ) h := by
  obtain rfl : a = (p : ℤ) := by have := natToIntEmbedding.f_eq_of_r_eq_some ha; simpa using this.symm
  obtain rfl : b = (q : ℤ) := by have := natToIntEmbedding.f_eq_of_r_eq_some hb; simpa using this.symm
  rw [extendedTensorSummandToTensorComponent_eq C D n _ (natToIntEmbedding_reverse_apply p) (natToIntEmbedding_reverse_apply q) hpq, Category.assoc, tensorSummandToTensorComponent_toExtended, tensorSummandToExtendedTensorComponent]
  simp


/-- At a natural degree, the tensor of the integer extensions is isomorphic to the tensor of the original complexes. -/
noncomputable def extendedTensorXIso (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend natToIntEmbedding) (D.extend natToIntEmbedding)).X (n : ℤ) ≅
      (HomologicalComplex.tensorObj C D).X n where
  hom := extendedTensorToTensorComponent C D n
  inv := tensorToExtendedTensorComponent C D n
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h'
    rw [Category.comp_id, ← Category.assoc,
      show HomologicalComplex.ιMapBifunctor C D _ _ p q n h' = tensorSummandToTensorComponent C D p q n h' from rfl,
      tensorSummandToTensorComponent_toExtended]
    exact tensorSummandToExtendedTensorComponent_toTensor C D n p q h'
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b h'
    rcases ha : natToIntEmbedding.r a with _ | p
    · exact (isZero_tensorObj_of_left (C.isZero_extend_X' natToIntEmbedding a ha)).eq_of_src _ _
    rcases hb : natToIntEmbedding.r b with _ | q
    · exact (isZero_tensorObj_of_right (D.isZero_extend_X' natToIntEmbedding b hb)).eq_of_src _ _
    have hpq : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n := by
      have hpa := natToIntEmbedding.f_eq_of_r_eq_some ha
      have hqb := natToIntEmbedding.f_eq_of_r_eq_some hb
      simp only [ComplexShape.embeddingUpNat_f] at hpa hqb
      have h2 : a + b = (n : ℤ) := h'
      have : p + q = n := by omega
      simpa using this
    rw [Category.comp_id, ← Category.assoc,
      show HomologicalComplex.ιMapBifunctor (C.extend natToIntEmbedding) (D.extend natToIntEmbedding) _ _ a b (n : ℤ) h'
        = extendedTensorSummandMap C D a b (n : ℤ) h' from rfl,
      extendedTensorSummandMap_toTensor]
    exact extendedTensorSummandToTensorComponent_toExtended C D n a b h' ha hb hpq


/-- A negative component of the tensor of two natural complexes extended to integer degrees is zero. -/
lemma isZero_extendedTensor_X_of_neg (j' : ℤ) (hj' : j' < 0) :
    IsZero ((HomologicalComplex.tensorObj (C.extend natToIntEmbedding) (D.extend natToIntEmbedding)).X j') := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  have hab' : a + b = j' := hab
  rw [Category.comp_id, comp_zero]
  refine (?_ : IsZero _).eq_of_src _ _
  by_cases ha : 0 ≤ a
  · have hb : b < 0 := by omega
    exact isZero_tensorObj_of_right
      (D.isZero_extend_X natToIntEmbedding b (fun i => by simp only [ComplexShape.embeddingUpNat_f]; omega))
  · exact isZero_tensorObj_of_left
      (C.isZero_extend_X natToIntEmbedding a (fun i => by simp only [ComplexShape.embeddingUpNat_f]; omega))


/-- The degree map of the natural-to-integer embedding sends a natural number to its integer cast. -/
lemma natToIntEmbedding_apply (n : ℕ) : natToIntEmbedding.f n = (n : ℤ) := by simp


/-- At a cast natural degree, tensoring after extension is isomorphic to extending the tensor product. -/
noncomputable def extendTensorXIsoAtNat (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend natToIntEmbedding) (D.extend natToIntEmbedding)).X (n : ℤ) ≅
      ((HomologicalComplex.tensorObj C D).extend natToIntEmbedding).X (n : ℤ) :=
  extendedTensorXIso C D n ≪≫
    (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) natToIntEmbedding (natToIntEmbedding_apply n)).symm


/-- In every integer degree, tensoring two extensions is isomorphic to extending their tensor product. -/
noncomputable def extendTensorXIso (j' : ℤ) :
    (HomologicalComplex.tensorObj (C.extend natToIntEmbedding) (D.extend natToIntEmbedding)).X j' ≅
      ((HomologicalComplex.tensorObj C D).extend natToIntEmbedding).X j' :=
  match hj : natToIntEmbedding.r j' with
  | some n =>
      eqToIso (congrArg (HomologicalComplex.tensorObj (C.extend natToIntEmbedding) (D.extend natToIntEmbedding)).X
        (show j' = (n : ℤ) by
          have := natToIntEmbedding.f_eq_of_r_eq_some hj
          simp only [ComplexShape.embeddingUpNat_f] at this; omega)) ≪≫
      extendTensorXIsoAtNat C D n ≪≫
      eqToIso (congrArg ((HomologicalComplex.tensorObj C D).extend natToIntEmbedding).X
        (show (n : ℤ) = j' by
          have := natToIntEmbedding.f_eq_of_r_eq_some hj
          simp only [ComplexShape.embeddingUpNat_f] at this; omega))
  | none =>
      IsZero.iso
        (isZero_extendedTensor_X_of_neg C D j' (by
          by_contra hle
          have hr : natToIntEmbedding.r j' = some (j'.toNat) :=
            natToIntEmbedding.r_eq_some (by simp only [ComplexShape.embeddingUpNat_f]; omega)
          rw [hr] at hj
          simp at hj))
        (HomologicalComplex.isZero_extend_X' _ natToIntEmbedding j' hj)


/-- The degreewise tensor-extension isomorphism at a cast natural degree is the specialized natural-degree isomorphism. -/
lemma extendTensorXIso_natCast (n : ℕ) :
    extendTensorXIso C D (n : ℤ) = extendTensorXIsoAtNat C D n := by
  rw [extendTensorXIso]
  split
  next m hm =>
    obtain rfl : m = n := (Option.some.inj ((natToIntEmbedding_reverse_apply n).symm.trans hm)).symm
    apply Iso.ext
    simp
  next hm => rw [natToIntEmbedding_reverse_apply] at hm; simp at hm

set_option backward.isDefEq.respectTransparency false in

/-- At a natural degree, the forward tensor-extension comparison followed by the extension component map is the canonical component map. -/
@[simp]
lemma extendTensorXIso_hom_app (n : ℕ) :
    (extendTensorXIso C D (n : ℤ)).hom ≫
        (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) natToIntEmbedding (natToIntEmbedding_apply n)).hom =
      extendedTensorToTensorComponent C D n := by
  rw [extendTensorXIso_natCast, extendTensorXIsoAtNat]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in

/-- At a natural degree, the two inverse extension comparisons compose to the map from the original tensor component to the tensor of extensions. -/
@[simp]
lemma tensorToExtendedTensorComponent_eq_inv_comp (n : ℕ) :
    (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) natToIntEmbedding (natToIntEmbedding_apply n)).inv ≫
        (extendTensorXIso C D (n : ℤ)).inv = tensorToExtendedTensorComponent C D n := by
  rw [extendTensorXIso_natCast, extendTensorXIsoAtNat]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.inv_hom_id_assoc]
  rfl




/-- An auxiliary theorem whose proposition is unavailable in the packet. -/
lemma opaqueAuxiliary (p : ℕ) : Int.negOnePow (p : ℤ) = (-1 : ℤˣ) ^ p := by
  simp [Int.negOnePow, zpow_natCast]


/-- The component map from the tensor of extensions commutes with the differentials in consecutive natural degrees. -/
@[reassoc]
lemma extendedTensorToTensorComponent_d (n : ℕ) :
    extendedTensorToTensorComponent C D n ≫ (HomologicalComplex.tensorObj C D).d n (n + 1) =
      (HomologicalComplex.tensorObj (C.extend natToIntEmbedding) (D.extend natToIntEmbedding)).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫
        extendedTensorToTensorComponent C D (n + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  rcases ha : natToIntEmbedding.r a with _ | p
  · exact (isZero_tensorObj_of_left (C.isZero_extend_X' natToIntEmbedding a ha)).eq_of_src _ _
  rcases hb : natToIntEmbedding.r b with _ | q
  · exact (isZero_tensorObj_of_right (D.isZero_extend_X' natToIntEmbedding b hb)).eq_of_src _ _
  obtain rfl : a = (p : ℤ) := by
    have := natToIntEmbedding.f_eq_of_r_eq_some ha
    simp only [ComplexShape.embeddingUpNat_f] at this; omega
  obtain rfl : b = (q : ℤ) := by
    have := natToIntEmbedding.f_eq_of_r_eq_some hb
    simp only [ComplexShape.embeddingUpNat_f] at this; omega
  have hpq : p + q = n := by
    have h2 : (p : ℤ) + (q : ℤ) = (n : ℤ) := hab
    omega
  rw [← Category.assoc, extendedTensorSummandMap_toTensor C D n (p : ℤ) (q : ℤ) hab,
      extendedTensorSummandToTensorComponent_eq C D n hab (natToIntEmbedding_reverse_apply p) (natToIntEmbedding_reverse_apply q) hpq, Category.assoc]
  simp only [mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
  refine congr_arg₂ (· + ·) ?_ ?_
  · -- d₁ part (factor 1 differential): C.d p (p+1); sign ε₁ = 1
    have hpn : (p + 1) + q = n + 1 := by omega
    rw [mapBifunctor.d₁_eq C D _ (ComplexShape.up ℕ)
          (show (ComplexShape.up ℕ).Rel p (p + 1) by rw [ComplexShape.up_Rel]) q (n + 1) hpn,
        mapBifunctor.d₁_eq (C.extend natToIntEmbedding) (D.extend natToIntEmbedding) _ (ComplexShape.up ℤ)
          (show (ComplexShape.up ℤ).Rel (p : ℤ) ((p + 1 : ℕ) : ℤ) by
            rw [ComplexShape.up_Rel]; push_cast; ring) (q : ℤ) ((n + 1 : ℕ) : ℤ)
          (by push_cast; omega : ((p + 1 : ℕ) : ℤ) + (q : ℤ) = ((n + 1 : ℕ) : ℤ)),
        extend_d_eq C natToIntEmbedding (natToIntEmbedding_apply p) (natToIntEmbedding_apply (p + 1)),
        show ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q)
          = (1 : ℤˣ) from rfl,
        show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              ((p : ℤ), (q : ℤ)) = (1 : ℤˣ) from rfl]
    simp only [one_smul, Category.assoc]
    rw [extendedTensorSummandMap_toTensor C D (n + 1) ((p + 1 : ℕ) : ℤ) (q : ℤ)
          (by push_cast; omega : ((p + 1 : ℕ) : ℤ) + (q : ℤ) = ((n + 1 : ℕ) : ℤ)),
        extendedTensorSummandToTensorComponent_eq C D (n + 1) _ (natToIntEmbedding_reverse_apply (p + 1)) (natToIntEmbedding_reverse_apply q) (by simpa using hpn)]
    simp only [Functor.map_comp, NatTrans.comp_app, curriedTensor_map_app,
      Category.assoc, MonoidalCategory.tensorHom_def, whisker_exchange_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id,
      MonoidalCategory.id_whiskerRight, Category.id_comp]
  · -- d₂ part (factor 2 differential): D.d q (q+1); sign ε₂ = (-1)^p
    have hpn : p + (q + 1) = n + 1 := by omega
    rw [mapBifunctor.d₂_eq C D _ (ComplexShape.up ℕ) p
          (show (ComplexShape.up ℕ).Rel q (q + 1) by rw [ComplexShape.up_Rel]) (n + 1) hpn,
        mapBifunctor.d₂_eq (C.extend natToIntEmbedding) (D.extend natToIntEmbedding) _ (ComplexShape.up ℤ) (p : ℤ)
          (show (ComplexShape.up ℤ).Rel (q : ℤ) ((q + 1 : ℕ) : ℤ) by
            rw [ComplexShape.up_Rel]; push_cast; ring) ((n + 1 : ℕ) : ℤ)
          (by push_cast; omega : (p : ℤ) + ((q + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ)),
        extend_d_eq D natToIntEmbedding (natToIntEmbedding_apply q) (natToIntEmbedding_apply (q + 1)),
        show ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q)
          = Int.negOnePow (p : ℤ) from (opaqueAuxiliary p).symm,
        show ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              ((p : ℤ), (q : ℤ)) = Int.negOnePow (p : ℤ) from rfl]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
    rw [extendedTensorSummandMap_toTensor C D (n + 1) (p : ℤ) ((q + 1 : ℕ) : ℤ)
          (by push_cast; omega : (p : ℤ) + ((q + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ)),
        extendedTensorSummandToTensorComponent_eq C D (n + 1) _ (natToIntEmbedding_reverse_apply p) (natToIntEmbedding_reverse_apply (q + 1)) (by simpa using hpn)]
    congr 1
    simp only [curriedTensor_obj_map, Category.assoc,
      MonoidalCategory.tensorHom_def, ← whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id, Category.comp_id]


/-- The differential compatibility of the component map remains valid after postcomposition. -/
add_decl_doc extendedTensorToTensorComponent_d_assoc

/-- Tensoring two integer extensions is isomorphic to extending the tensor product of the original complexes. -/
noncomputable def extendTensorIso :
    HomologicalComplex.tensorObj (C.extend natToIntEmbedding) (D.extend natToIntEmbedding) ≅
      (HomologicalComplex.tensorObj C D).extend natToIntEmbedding :=
  HomologicalComplex.Hom.isoOfComponents (fun j' => extendTensorXIso C D j') (by
    intro i j hij
    by_cases hi : i < 0
    · exact (isZero_extendedTensor_X_of_neg C D i hi).eq_of_src _ _
    · rw [not_lt] at hi
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
      obtain rfl : j = ((n + 1 : ℕ) : ℤ) := by
        have : (n : ℤ) + 1 = j := hij
        push_cast; omega
      rw [HomologicalComplex.extend_d_eq (HomologicalComplex.tensorObj C D) natToIntEmbedding
            (natToIntEmbedding_apply n) (natToIntEmbedding_apply (n + 1)),
          ← Category.assoc, extendTensorXIso_hom_app C D n,
          extendedTensorToTensorComponent_d_assoc C D n]
      congr 1
      rw [← extendTensorXIso_hom_app C D (n + 1), Category.assoc, Iso.hom_inv_id,
        Category.comp_id])



section Naturality

variable {C₁ C₂ D₁ D₂ : CochainComplex (ModuleCat.{u} k) ℕ}


/-- The component map from the tensor of extensions is natural in maps of both cochain complexes. -/
lemma extendedTensorToTensorComponent_naturality (f : C₁ ⟶ C₂) (g : D₁ ⟶ D₂) (n : ℕ) :
    (HomologicalComplex.tensorHom (HomologicalComplex.extendMap f natToIntEmbedding)
          (HomologicalComplex.extendMap g natToIntEmbedding)).f (n : ℤ) ≫ extendedTensorToTensorComponent C₂ D₂ n =
      extendedTensorToTensorComponent C₁ D₁ n ≫ (HomologicalComplex.tensorHom f g).f n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  rcases ha : natToIntEmbedding.r a with _ | p
  · exact (isZero_tensorObj_of_left (C₁.isZero_extend_X' natToIntEmbedding a ha)).eq_of_src _ _
  rcases hb : natToIntEmbedding.r b with _ | q
  · exact (isZero_tensorObj_of_right (D₁.isZero_extend_X' natToIntEmbedding b hb)).eq_of_src _ _
  obtain rfl : a = (p : ℤ) := by have := natToIntEmbedding.f_eq_of_r_eq_some ha; simpa using this.symm
  obtain rfl : b = (q : ℤ) := by have := natToIntEmbedding.f_eq_of_r_eq_some hb; simpa using this.symm
  have hab' : (p : ℤ) + (q : ℤ) = (n : ℤ) := hab
  have hpq : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n := by
    have : p + q = n := by omega
    simpa using this
  rw [show HomologicalComplex.ιMapBifunctor (C₁.extend natToIntEmbedding) (D₁.extend natToIntEmbedding)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
        (p : ℤ) (q : ℤ) (n : ℤ) hab = extendedTensorSummandMap C₁ D₁ _ _ _ hab from rfl]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, extendedTensorSummandMap_toTensor,
    extendedTensorSummandToTensorComponent_eq C₂ D₂ n _ (natToIntEmbedding_reverse_apply p) (natToIntEmbedding_reverse_apply q) hpq,
    ← Category.assoc (extendedTensorSummandMap C₁ D₁ _ _ _ hab), extendedTensorSummandMap_toTensor,
    extendedTensorSummandToTensorComponent_eq C₁ D₁ n _ (natToIntEmbedding_reverse_apply p) (natToIntEmbedding_reverse_apply q) hpq,
    Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.extendMap_f f natToIntEmbedding (natToIntEmbedding_apply p),
    HomologicalComplex.extendMap_f g natToIntEmbedding (natToIntEmbedding_apply q)]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp,
    Iso.inv_hom_id]

-- The reassociated form of `extendTensorXIso_hom_app`, used to strip the extend
-- transport off the middle of a composite in `extendTensorIso_naturality`.
attribute [reassoc] extendTensorXIso_hom_app

/-- The forward component formula for the tensor-extension comparison remains valid after postcomposition. -/
add_decl_doc extendTensorXIso_hom_app_assoc


/-- The tensor-extension isomorphism is natural in simultaneous maps of both complexes. -/
theorem extendTensorIso_naturality (f : C₁ ⟶ C₂) (g : D₁ ⟶ D₂) :
    HomologicalComplex.tensorHom (HomologicalComplex.extendMap f natToIntEmbedding)
          (HomologicalComplex.extendMap g natToIntEmbedding) ≫ (extendTensorIso C₂ D₂).hom =
      (extendTensorIso C₁ D₁).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom f g) natToIntEmbedding := by
  ext j' : 1
  by_cases hj : j' < 0
  · exact (HomologicalComplex.isZero_extend_X (HomologicalComplex.tensorObj C₂ D₂) natToIntEmbedding j'
      (fun m => by simp only [ComplexShape.embeddingUpNat_f]; omega)).eq_of_tgt _ _
  · rw [not_lt] at hj
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j' = (n : ℤ) := ⟨j'.toNat, by omega⟩
    rw [← cancel_mono (HomologicalComplex.extendXIso
      (HomologicalComplex.tensorObj C₂ D₂) natToIntEmbedding (natToIntEmbedding_apply n)).hom,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
      show (extendTensorIso C₂ D₂).hom.f (n : ℤ) = (extendTensorXIso C₂ D₂ (n : ℤ)).hom
        from rfl,
      show (extendTensorIso C₁ D₁).hom.f (n : ℤ) = (extendTensorXIso C₁ D₁ (n : ℤ)).hom
        from rfl,
      extendTensorXIso_hom_app,
      HomologicalComplex.extendMap_f (HomologicalComplex.tensorHom f g) natToIntEmbedding (natToIntEmbedding_apply n),
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      extendTensorXIso_hom_app_assoc]
    exact extendedTensorToTensorComponent_naturality f g n


/-- The tensor-extension isomorphism is natural in a map of the left complex. -/
theorem extendTensorIso_naturality_left (f : C₁ ⟶ C₂)
    (D : CochainComplex (ModuleCat.{u} k) ℕ) :
    HomologicalComplex.tensorHom (HomologicalComplex.extendMap f natToIntEmbedding) (𝟙 (D.extend natToIntEmbedding)) ≫
        (extendTensorIso C₂ D).hom =
      (extendTensorIso C₁ D).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom f (𝟙 D)) natToIntEmbedding := by
  simpa using extendTensorIso_naturality f (𝟙 D)


/-- The tensor-extension isomorphism is natural in a map of the right complex. -/
theorem extendTensorIso_naturality_right (C : CochainComplex (ModuleCat.{u} k) ℕ)
    (g : D₁ ⟶ D₂) :
    HomologicalComplex.tensorHom (𝟙 (C.extend natToIntEmbedding)) (HomologicalComplex.extendMap g natToIntEmbedding) ≫
        (extendTensorIso C D₂).hom =
      (extendTensorIso C D₁).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom (𝟙 C) g) natToIntEmbedding := by
  simpa using extendTensorIso_naturality (𝟙 C) g

end Naturality

section Bifunctor


/-- The curried tensor-product functor on natural-graded cochain complexes of modules. -/
noncomputable abbrev tensorProductFunctor :
    CochainComplex (ModuleCat.{u} k) ℕ ⥤ CochainComplex (ModuleCat.{u} k) ℕ ⥤
      CochainComplex (ModuleCat.{u} k) ℕ :=
  (curriedTensor (ModuleCat.{u} k)).map₂HomologicalComplex
    (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)


/-- The functor from natural-graded cochain complexes of modules to integer-graded cochain complexes. -/
noncomputable abbrev extendNatToIntFunctor :
    CochainComplex (ModuleCat.{u} k) ℕ ⥤ CochainComplex (ModuleCat.{u} k) ℤ :=
  natToIntEmbedding.extendFunctor (ModuleCat.{u} k)


/-- The bifunctor from natural-graded complexes to an integer-graded complex obtained by extending both inputs before tensoring. -/
noncomputable abbrev extendThenTensorFunctor :
    CochainComplex (ModuleCat.{u} k) ℕ ⥤ CochainComplex (ModuleCat.{u} k) ℕ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  (extendNatToIntFunctor ⋙ _root_.RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing.auxiliaryCochainComplexBifunctor) ⋙
    (CategoryTheory.Functor.whiskeringLeft (CochainComplex (ModuleCat.{u} k) ℕ)
      (CochainComplex (ModuleCat.{u} k) ℤ)
      (CochainComplex (ModuleCat.{u} k) ℤ)).obj extendNatToIntFunctor


/-- The bifunctor from natural-graded complexes to an integer-graded complex obtained by extending their tensor product. -/
noncomputable abbrev tensorThenExtendFunctor :
    CochainComplex (ModuleCat.{u} k) ℕ ⥤ CochainComplex (ModuleCat.{u} k) ℕ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  tensorProductFunctor ⋙
    (CategoryTheory.Functor.whiskeringRight (CochainComplex (ModuleCat.{u} k) ℕ)
      (CochainComplex (ModuleCat.{u} k) ℕ)
      (CochainComplex (ModuleCat.{u} k) ℤ)).obj extendNatToIntFunctor


/-- The bifunctor that extends before tensoring is naturally isomorphic to the bifunctor that tensors before extending. -/
noncomputable def extendTensorFunctorIso :
    extendThenTensorFunctor (k := k) ≅ tensorThenExtendFunctor (k := k) :=
  NatIso.ofComponents
    (fun C => NatIso.ofComponents (fun D => extendTensorIso C D) (fun {D₁ D₂} g => by
      have h := extendTensorIso_naturality (𝟙 C) g
      rw [HomologicalComplex.extendMap_id] at h
      exact h))
    (fun {C₁ C₂} f => by
      ext D : 2
      simp only [NatTrans.comp_app]
      have h := extendTensorIso_naturality f (𝟙 D)
      rw [HomologicalComplex.extendMap_id] at h
      exact h)


/-- The component of the bifunctor isomorphism at two complexes is the tensor-extension isomorphism. -/
@[simp]
lemma extendTensorFunctorIso_app (C D : CochainComplex (ModuleCat.{u} k) ℕ) :
    (extendTensorFunctorIso.app C).app D = extendTensorIso C D :=
  rfl

end Bifunctor



/-- There exists an isomorphism between tensoring two integer extensions and extending their natural-graded tensor product. -/
theorem nonempty_extendTensorIso (C D : CochainComplex (ModuleCat.{u} k) ℕ) :
    Nonempty (HomologicalComplex.tensorObj (C.extend ComplexShape.embeddingUpNat)
        (D.extend ComplexShape.embeddingUpNat) ≅
      (HomologicalComplex.tensorObj C D).extend ComplexShape.embeddingUpNat) :=
  ⟨extendTensorIso C D⟩


/-- An isomorphism from the homology of a tensor complex to the sigma object of tensor products of the input homologies in paired degrees. -/
noncomputable def homologyTensorIsoSigma (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (HomologicalComplex.tensorObj C D).homology i ≅
      ∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) =>
        C.homology p.1.1 ⊗ D.homology p.1.2 := by
  let e := ComplexShape.embeddingUpNat
  -- Step 1: `Hⁱ(C ⊗ D) ≅ Hⁱ(extend (C ⊗ D))`.
  let α₁ : (HomologicalComplex.tensorObj C D).homology i ≅
      ((HomologicalComplex.tensorObj C D).extend e).homology (i : ℤ) :=
    (homologyExtendIso (HomologicalComplex.tensorObj C D) i).symm
  -- Step 2: apply `Hⁱ` to the compatibility iso `extend (C ⊗ D) ≅ extend C ⊗ extend D`.
  let φ : (HomologicalComplex.tensorObj C D).extend e ≅
      HomologicalComplex.tensorObj (C.extend e) (D.extend e) :=
    (extendTensorIso C D).symm
  let α₂ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ)
    (i : ℤ)).mapIso φ
  -- Step 3: Chapter 7's universe-general Künneth at degree `i`, as the honest isomorphism
  -- inverse to the natural cross product `totalHomologyTensorToTensorHomology`.
  let α₃ := _root_.RepresentationTheory.HomologicalComplex.TensorHomology.homologyTensorToSigmaIso (C.extend e) (D.extend e) (i : ℤ)
  -- Step 4: reindex the `ℤ`-coproduct `⨁_{a+b=i}` onto the `ℕ`-antidiagonal `⨁_{p+q=i}`;
  -- the summands with `a < 0` or `b < 0` vanish by `isZero_homology_extend_of_neg`.
  let ι : {p : ℕ × ℕ // p.1 + p.2 = i} → {p : ℤ × ℤ // p.1 + p.2 = (i : ℤ)} :=
    fun p => ⟨((p.1.1 : ℤ), (p.1.2 : ℤ)), by
      have h2 : (p.1.1 : ℤ) + (p.1.2 : ℤ) = (i : ℤ) := by exact_mod_cast p.2
      exact h2⟩
  have hι : Function.Injective ι := by
    intro p p' hpp
    apply Subtype.ext
    have hv : (ι p).1 = (ι p').1 := congrArg Subtype.val hpp
    have h1 : (p.1.1 : ℤ) = (p'.1.1 : ℤ) := congrArg Prod.fst hv
    have h2 : (p.1.2 : ℤ) = (p'.1.2 : ℤ) := congrArg Prod.snd hv
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  let α₄ : (∐ fun (p : {p : ℤ × ℤ // p.1 + p.2 = (i : ℤ)}) =>
        (C.extend e).homology p.1.1 ⊗ (D.extend e).homology p.1.2) ≅
      (∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) => C.homology p.1.1 ⊗ D.homology p.1.2) :=
    _root_.RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing.sigmaIsoOfInjective ι hι
      (fun a => tensorIso (homologyExtendIso C a.1.1) (homologyExtendIso D a.1.2))
      (by
        rintro ⟨⟨a, b⟩, hab⟩ hj
        by_cases ha : a < 0
        · exact isZero_tensorObj_of_left (isZero_homology_extend_of_neg C a ha)
        by_cases hb : b < 0
        · exact isZero_tensorObj_of_right (isZero_homology_extend_of_neg D b hb)
        rw [not_lt] at ha hb
        exfalso
        have hp : ((a.toNat) : ℤ) = a := Int.toNat_of_nonneg ha
        have hq : ((b.toNat) : ℤ) = b := Int.toNat_of_nonneg hb
        have hpq : a.toNat + b.toNat = i := by
          have : ((a.toNat) : ℤ) + ((b.toNat) : ℤ) = (i : ℤ) := by rw [hp, hq]; exact hab
          exact_mod_cast this
        refine hj ⟨(a.toNat, b.toNat), hpq⟩ (Subtype.ext ?_)
        change (((a.toNat : ℕ) : ℤ), ((b.toNat : ℕ) : ℤ)) = (a, b)
        rw [Prod.mk.injEq]
        exact ⟨hp, hq⟩)
  exact α₁ ≪≫ α₂ ≪≫ α₃ ≪≫ α₄


/-- The homology of a tensor complex admits an isomorphism to the sigma object of tensor products of the input homologies in paired degrees. -/
theorem nonempty_homologyTensorIsoSigma (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    Nonempty ((HomologicalComplex.tensorObj C D).homology i ≅
      ∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) =>
        C.homology p.1.1 ⊗ D.homology p.1.2) :=
  ⟨homologyTensorIsoSigma C D i⟩

end RepresentationTheory.HomologicalComplex.TensorExtension
