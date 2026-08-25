/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.HomologicalAlgebra.AcyclicComplexDecomposition
import RepresentationTheory.Mathlib.Algebra.Homology.CochainComplex.Monoidal

set_option backward.isDefEq.respectTransparency false

/-!
# Homology complexes and tensor products

This module constructs the zero-differential complex of homology objects, splits cochain
complexes over a field into acyclic and homology summands, and identifies the homology of a
tensor product with the corresponding indexed sum of tensor products of homology objects.
-/

open CategoryTheory Limits MonoidalCategory
open RepresentationTheory.Mathlib.Algebra.Homology.CochainComplex.Monoidal.CochainComplex

namespace RepresentationTheory.Algebra.Homology.CochainComplex.HomologyComplex

universe u

variable {k : Type u} [Field k]

/-- The cochain complex formed from the homology objects of a cochain complex. -/
noncomputable def homologyComplex (C : CochainComplex (ModuleCat.{u} k) ℤ) :
    CochainComplex (ModuleCat.{u} k) ℤ where
  X i := C.homology i
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

section SplitField

variable (C : CochainComplex (ModuleCat.{u} k) ℤ)

/-! ### Splittings for homology complexes -/

private lemma exists_rho (i : ℤ) :
    ∃ g : (C.homology i) →ₗ[k] (C.cycles i), (C.homologyπ i).hom ∘ₗ g = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _
    ((ModuleCat.epi_iff_range_eq_top _).mp inferInstance)

/-- The linear map underlying a chosen section from homology to cycles. -/
noncomputable def homologySectionLinear (i : ℤ) : (C.homology i) →ₗ[k] (C.cycles i) := (exists_rho C i).choose

/-- The homology projection composed with the chosen linear section is the identity. -/
lemma homologyPi_comp_homologySectionLinear (i : ℤ) : (C.homologyπ i).hom ∘ₗ homologySectionLinear C i = LinearMap.id :=
  (exists_rho C i).choose_spec

/-- A chosen morphism from homology to cycles. -/
noncomputable def homologySection (i : ℤ) : C.homology i ⟶ C.cycles i := ModuleCat.ofHom (homologySectionLinear C i)

/-- The chosen section followed by the homology projection is the identity. -/
@[reassoc]
lemma homologySection_comp_homologyPi (i : ℤ) : homologySection C i ≫ C.homologyπ i = 𝟙 (C.homology i) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, homologySection, ModuleCat.hom_ofHom, ModuleCat.hom_id]
  exact homologyPi_comp_homologySectionLinear C i

/-- Precomposing a map from homology with its projection and chosen section leaves it unchanged. -/
add_decl_doc homologySection_comp_homologyPi_assoc

private lemma exists_tau (i : ℤ) :
    ∃ g : (C.X i) →ₗ[k] (C.cycles i), g ∘ₗ (C.iCycles i).hom = LinearMap.id :=
  LinearMap.exists_leftInverse_of_injective _
    ((ModuleCat.mono_iff_ker_eq_bot _).mp inferInstance)

/-- The linear map underlying the chosen projection onto cycles. -/
noncomputable def cyclesProjectionLinear (i : ℤ) : (C.X i) →ₗ[k] (C.cycles i) := (exists_tau C i).choose

/-- The cycle projection composed with the cycle inclusion is the identity linear map. -/
lemma cyclesProjectionLinear_comp_iCycles (i : ℤ) : cyclesProjectionLinear C i ∘ₗ (C.iCycles i).hom = LinearMap.id :=
  (exists_tau C i).choose_spec

/-- A chosen projection from a component of a complex onto its cycles. -/
noncomputable def cyclesProjection (i : ℤ) : C.X i ⟶ C.cycles i := ModuleCat.ofHom (cyclesProjectionLinear C i)

/-- Including cycles and then projecting back to cycles gives the identity. -/
@[reassoc]
lemma iCycles_comp_cyclesProjection (i : ℤ) : C.iCycles i ≫ cyclesProjection C i = 𝟙 (C.cycles i) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, cyclesProjection, ModuleCat.hom_ofHom, ModuleCat.hom_id]
  exact cyclesProjectionLinear_comp_iCycles C i

/-- Inserting the cycle projection after the inclusion does not change a map out of cycles. -/
add_decl_doc iCycles_comp_cyclesProjection_assoc

/-- A morphism from the homology complex back to the original cochain complex. -/
noncomputable def fromHomologyComplex : homologyComplex C ⟶ C where
  f i := homologySection C i ≫ C.iCycles i
  comm' i j hij := by
    have hd : (homologyComplex C).d i j = 0 := rfl
    rw [hd, zero_comp, Category.assoc, C.iCycles_d, comp_zero]

/-- The morphism from a cochain complex to its homology complex. -/
noncomputable def toHomologyComplex : C ⟶ homologyComplex C where
  f i := cyclesProjection C i ≫ C.homologyπ i
  comm' i j hij := by
    have hd : (homologyComplex C).d i j = 0 := rfl
    rw [hd, comp_zero, ← C.toCycles_i i j]
    simp only [Category.assoc, iCycles_comp_cyclesProjection_assoc,
      HomologicalComplex.toCycles_comp_homologyπ]

/-- The morphisms between a homology complex and its original complex compose to the identity on the homology complex. -/
lemma fromHomologyComplex_comp_toHomologyComplex : fromHomologyComplex C ≫ toHomologyComplex C = 𝟙 (homologyComplex C) := by
  apply HomologicalComplex.hom_ext
  intro i
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  change (homologySection C i ≫ C.iCycles i) ≫ (cyclesProjection C i ≫ C.homologyπ i) = 𝟙 _
  rw [Category.assoc, ← Category.assoc (C.iCycles i), iCycles_comp_cyclesProjection, Category.id_comp,
    homologySection_comp_homologyPi]

/-- The comparison from a complex through its homology complex induces the identity on homology. -/
lemma homologyMap_toHomologyComplex_comp_fromHomologyComplex (i : ℤ) :
    HomologicalComplex.homologyMap (toHomologyComplex C ≫ fromHomologyComplex C) i = 𝟙 (C.homology i) := by
  have hcyc : HomologicalComplex.cyclesMap (toHomologyComplex C ≫ fromHomologyComplex C) i = C.homologyπ i ≫ homologySection C i := by
    rw [← cancel_mono (C.iCycles i), HomologicalComplex.cyclesMap_i, HomologicalComplex.comp_f]
    change C.iCycles i ≫ ((cyclesProjection C i ≫ C.homologyπ i) ≫ (homologySection C i ≫ C.iCycles i))
      = (C.homologyπ i ≫ homologySection C i) ≫ C.iCycles i
    simp only [Category.assoc, iCycles_comp_cyclesProjection_assoc]
  have hnat := HomologicalComplex.homologyπ_naturality (toHomologyComplex C ≫ fromHomologyComplex C) i
  rw [hcyc, Category.assoc, homologySection_comp_homologyPi, Category.comp_id] at hnat
  rw [← cancel_epi (C.homologyπ i), Category.comp_id]
  exact hnat

end SplitField

/-- The composite of two differentials in the tensor product complex is zero. -/
@[source_ref "Chapter7/Problem7.8.7" (role := supporting)]
theorem tensorProduct_d_comp_d (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i j l : ℤ) :
    (binaryOperation C D).d i j ≫ (binaryOperation C D).d j l = 0 :=
  (binaryOperation C D).d_comp_d i j l

private lemma acyclic_of_homotopy_id_zero {X : CochainComplex (ModuleCat.{u} k) ℤ}
    (H : Homotopy (𝟙 X) 0) : X.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have h := H.homologyMap_eq i
  rwa [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at h

/-- The tensor product complex is acyclic when either input complex is acyclic. -/
@[source_ref "Chapter7/Problem7.8.7" (role := primary)]
theorem tensorProduct_acyclic_of_acyclic (C D : CochainComplex (ModuleCat.{u} k) ℤ)
    (h : C.Acyclic ∨ D.Acyclic) :
    (binaryOperation C D).Acyclic := by
  -- Over a field an acyclic complex is contractible: its identity is null-homotopic.
  -- Whiskering that contracting homotopy through the tensor bifunctor makes `𝟙 (C ⊗ D)`
  -- null-homotopic, hence `C ⊗ D` acyclic.
  -- `tensorHom (𝟙) (𝟙) = 𝟙`: the tensor bifunctor sends `𝟙` to `𝟙`, so the induced
  -- morphism on total complexes is `total.map (𝟙) = 𝟙`.
  have hid : HomologicalComplex.mapBifunctorMap (𝟙 C) (𝟙 D)
      (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) = 𝟙 (binaryOperation C D) := by
    rw [HomologicalComplex.mapBifunctorMap, CategoryTheory.Functor.map_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, HomologicalComplex₂.total.map_id]
    rfl
  -- `Acyclic` is a `Prop`, so split the disjunction first, then build the null-homotopy of
  -- `𝟙 (C ⊗ D)` in each branch by whiskering the contracting homotopy of the acyclic factor.
  rcases h with hC | hD
  · obtain ⟨hCH⟩ := RepresentationTheory.HomologicalAlgebra.AcyclicComplexDecomposition.acyclic_homotopy_id_zero C hC
    -- `tensorHom 0 (𝟙 D) = 0`: the bifunctor sends `0` to `0`, so each injection composes to `0`.
    have hz : HomologicalComplex.mapBifunctorMap (0 : C ⟶ C) (𝟙 D)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) = 0 := by
      apply HomologicalComplex.hom_ext
      intro j
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro i₁ i₂ hji
      simp
    have Hmap := HomologicalComplex.mapBifunctorMapHomotopy₁ hCH (𝟙 D)
      (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
    exact acyclic_of_homotopy_id_zero
      ((Homotopy.ofEq hid.symm).trans (Hmap.trans (Homotopy.ofEq hz)))
  · obtain ⟨hDH⟩ := RepresentationTheory.HomologicalAlgebra.AcyclicComplexDecomposition.acyclic_homotopy_id_zero D hD
    have hz : HomologicalComplex.mapBifunctorMap (𝟙 C) (0 : D ⟶ D)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) = 0 := by
      apply HomologicalComplex.hom_ext
      intro j
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro i₁ i₂ hji
      simp
    have Hmap := HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 C) hDH
      (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
    exact acyclic_of_homotopy_id_zero
      ((Homotopy.ofEq hid.symm).trans (Hmap.trans (Homotopy.ofEq hz)))

/-- There exist data and an isomorphism such that, in every degree, the map on homology induced by the second biproduct inclusion followed by the inverse isomorphism is an isomorphism. -/
@[source_ref "Chapter7/Problem7.8.7" (role := supporting)]
theorem exists_biprod_inr_comp_iso_inv_homologyMap_isIso (C : CochainComplex (ModuleCat.{u} k) ℤ) :
    ∃ (E : CochainComplex (ModuleCat.{u} k) ℤ) (_ : E.Acyclic)
      (iso : C ≅ E ⊞ homologyComplex C),
      ∀ i : ℤ, IsIso (HomologicalComplex.homologyMap
        ((biprod.inr : homologyComplex C ⟶ E ⊞ homologyComplex C) ≫ iso.inv) i) := by
  -- `fromHomologyComplex ≫ toHomologyComplex = 𝟙`, so `toHomologyComplex ≫ fromHomologyComplex` is idempotent; `𝟙 - toHomologyComplex ≫ fromHomologyComplex` is the
  -- complementary idempotent, which splits (abelian ⇒ idempotent complete) into `E`.
  have hXX : (toHomologyComplex C ≫ fromHomologyComplex C) ≫ (toHomologyComplex C ≫ fromHomologyComplex C) = toHomologyComplex C ≫ fromHomologyComplex C := by
    rw [Category.assoc, ← Category.assoc (fromHomologyComplex C), fromHomologyComplex_comp_toHomologyComplex C, Category.id_comp]
  obtain ⟨E, ι, r, hιr, hrι⟩ :=
    IsIdempotentComplete.idempotents_split C (𝟙 C - toHomologyComplex C ≫ fromHomologyComplex C) (by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
        Category.comp_id, hXX]
      abel)
  -- `hιr : ι ≫ r = 𝟙 E`, `hrι : r ≫ ι = 𝟙 C - toHomologyComplex C ≫ fromHomologyComplex C`.
  have hqp : (𝟙 C - toHomologyComplex C ≫ fromHomologyComplex C) ≫ toHomologyComplex C = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, fromHomologyComplex_comp_toHomologyComplex C, Category.comp_id,
      sub_self]
  have hsq : fromHomologyComplex C ≫ (𝟙 C - toHomologyComplex C ≫ fromHomologyComplex C) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, fromHomologyComplex_comp_toHomologyComplex C, Category.id_comp,
      sub_self]
  haveI : IsSplitEpi r := ⟨⟨ι, hιr⟩⟩
  haveI : IsSplitMono ι := ⟨⟨r, hιr⟩⟩
  have hιp : ι ≫ toHomologyComplex C = 0 := by
    rw [← cancel_epi r, comp_zero, ← Category.assoc, hrι, hqp]
  have hsr : fromHomologyComplex C ≫ r = 0 := by
    rw [← cancel_mono ι, zero_comp, Category.assoc, hrι, hsq]
  -- The isomorphism `C ≅ E ⊞ homologyComplex C`.
  let iso : C ≅ E ⊞ homologyComplex C :=
    { hom := biprod.lift r (toHomologyComplex C)
      inv := biprod.desc ι (fromHomologyComplex C)
      hom_inv_id := by rw [biprod.lift_desc, hrι]; abel
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
          simp [hιr, fromHomologyComplex_comp_toHomologyComplex C, hιp, hsr] }
  -- `E` is acyclic: `homologyMap (𝟙 - toHomologyComplex ≫ fromHomologyComplex) = 0`, and `𝟙_E` factors through it.
  have hqhom : ∀ i, HomologicalComplex.homologyMap (𝟙 C - toHomologyComplex C ≫ fromHomologyComplex C) i = 0 := by
    intro i
    rw [HomologicalComplex.homologyMap_sub, HomologicalComplex.homologyMap_id,
      homologyMap_toHomologyComplex_comp_fromHomologyComplex C i, sub_self]
  have hAc : E.Acyclic := by
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
    have hid : 𝟙 (E.homology i)
        = HomologicalComplex.homologyMap ι i ≫ HomologicalComplex.homologyMap r i := by
      rw [← HomologicalComplex.homologyMap_comp, hιr, HomologicalComplex.homologyMap_id]
    have he0 : HomologicalComplex.homologyMap r i ≫ HomologicalComplex.homologyMap ι i = 0 := by
      rw [← HomologicalComplex.homologyMap_comp, hrι, hqhom i]
    calc 𝟙 (E.homology i)
        = (HomologicalComplex.homologyMap ι i ≫ HomologicalComplex.homologyMap r i)
            ≫ (HomologicalComplex.homologyMap ι i ≫ HomologicalComplex.homologyMap r i) := by
          rw [← hid, Category.comp_id]
      _ = HomologicalComplex.homologyMap ι i
            ≫ (HomologicalComplex.homologyMap r i ≫ HomologicalComplex.homologyMap ι i)
            ≫ HomologicalComplex.homologyMap r i := by simp only [Category.assoc]
      _ = 0 := by rw [he0, zero_comp, comp_zero]
  refine ⟨E, hAc, iso, ?_⟩
  intro i
  have hbi : (biprod.inr : homologyComplex C ⟶ E ⊞ homologyComplex C) ≫ iso.inv
      = fromHomologyComplex C := by
    change biprod.inr ≫ biprod.desc ι (fromHomologyComplex C) = fromHomologyComplex C
    rw [biprod.inr_desc]
  rw [hbi]
  -- `homologyMap (fromHomologyComplex C) i` is iso, with inverse `homologyMap (toHomologyComplex C) i`.
  refine ⟨HomologicalComplex.homologyMap (toHomologyComplex C) i, ?_, ?_⟩
  · rw [← HomologicalComplex.homologyMap_comp, fromHomologyComplex_comp_toHomologyComplex C, HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp]; exact homologyMap_toHomologyComplex_comp_fromHomologyComplex C i

/-! ### Tensor products of homology complexes -/

/-- Identify a degree of a tensor product complex with the indexed sum of tensor products of its input degrees. -/
noncomputable def tensorObjXIsoSigma
    (K₁ K₂ : CochainComplex (ModuleCat.{u} k) ℤ) [HomologicalComplex.HasTensor K₁ K₂] (i : ℤ) :
    (HomologicalComplex.tensorObj K₁ K₂).X i ≅
      ∐ fun (p : {p : ℤ × ℤ // p.1 + p.2 = i}) => K₁.X p.1.1 ⊗ K₂.X p.1.2 where
  hom := HomologicalComplex.mapBifunctorDesc
    (fun i₁ i₂ h => Sigma.ι (fun p : {p : ℤ × ℤ // p.1 + p.2 = i} => K₁.X p.1.1 ⊗ K₂.X p.1.2)
      ⟨(i₁, i₂), h⟩)
  inv := Sigma.desc (fun p => HomologicalComplex.ιTensorObj K₁ K₂ p.1.1 p.1.2 i p.2)
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    simp [HomologicalComplex.ιTensorObj]
  inv_hom_id := by
    apply Sigma.hom_ext
    rintro ⟨⟨i₁, i₂⟩, h⟩
    simp [HomologicalComplex.ιTensorObj]

/-- All differentials of the homology complex are zero. -/
@[simp] lemma homologyComplex_d (C : CochainComplex (ModuleCat.{u} k) ℤ) (i j : ℤ) :
    (homologyComplex C).d i j = 0 := rfl

/-- The tensor product of two homology complexes has zero differentials. -/
lemma tensorObj_homologyComplex_d (C D : CochainComplex (ModuleCat.{u} k) ℤ) (j j' : ℤ) :
    (HomologicalComplex.tensorObj (homologyComplex C) (homologyComplex D)).d j j' = 0 := by
  have hd₁ : ∀ i₁ i₂ : ℤ,
      HomologicalComplex.mapBifunctor.d₁ (homologyComplex C) (homologyComplex D)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) i₁ i₂ j' = 0 := by
    intro i₁ i₂
    by_cases hrel : (ComplexShape.up ℤ).Rel i₁ ((ComplexShape.up ℤ).next i₁)
    · rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ hrel i₂ j']
      simp
    · apply HomologicalComplex.mapBifunctor.d₁_eq_zero
      exact hrel
  have hd₂ : ∀ i₁ i₂ : ℤ,
      HomologicalComplex.mapBifunctor.d₂ (homologyComplex C) (homologyComplex D)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) i₁ i₂ j' = 0 := by
    intro i₁ i₂
    by_cases hrel : (ComplexShape.up ℤ).Rel i₂ ((ComplexShape.up ℤ).next i₂)
    · rw [HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ i₁ hrel j']
      simp
    · apply HomologicalComplex.mapBifunctor.d₂_eq_zero
      exact hrel
  have hD₁ : HomologicalComplex.mapBifunctor.D₁ (homologyComplex C) (homologyComplex D)
      (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j j' = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    rw [HomologicalComplex.mapBifunctor.ι_D₁, comp_zero, hd₁]
  have hD₂ : HomologicalComplex.mapBifunctor.D₂ (homologyComplex C) (homologyComplex D)
      (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) j j' = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    rw [HomologicalComplex.mapBifunctor.ι_D₂, comp_zero, hd₂]
  rw [HomologicalComplex.mapBifunctor.d_eq, hD₁, hD₂, add_zero]

/-- The tensor product of homology complexes has homology given by the indexed sum of tensor products of the original homology objects. -/
noncomputable def homologyTensorProductHomologyIso
    (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) :
    (binaryOperation (homologyComplex C) (homologyComplex D)).homology i ≅
      ∐ fun (p : {p : ℤ × ℤ // p.1 + p.2 = i}) => C.homology p.1.1 ⊗ D.homology p.1.2 :=
  let K := HomologicalComplex.tensorObj (homologyComplex C) (homologyComplex D)
  ((K.isoHomologyπ (i - 1) i (by simp) (tensorObj_homologyComplex_d C D (i - 1) i)).symm ≪≫
    K.iCyclesIso i (i + 1) (by simp) (tensorObj_homologyComplex_d C D i (i + 1))) ≪≫
    tensorObjXIsoSigma (homologyComplex C) (homologyComplex D) i

/-- There exists an isomorphism between the homology of the tensor product complex and the indexed sum of tensor products of the input homology objects. -/
theorem tensorProduct_homologyIso_nonempty (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) :
    Nonempty ((binaryOperation C D).homology i ≅
      ∐ fun (p : {p : ℤ × ℤ // p.1 + p.2 = i}) => C.homology p.1.1 ⊗ D.homology p.1.2) := by
  -- Decompose each factor into an acyclic complex and its zero-differential homology complex.
  obtain ⟨E, hE, iC, -⟩ := exists_biprod_inr_comp_iso_inv_homologyMap_isIso C
  obtain ⟨F, hF, iD, -⟩ := exists_biprod_inr_comp_iso_inv_homologyMap_isIso D
  -- The homology functor `Hⁱ` at degree `i`; it is additive, so it preserves biproducts.
  let Hi := HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ) i
  haveI : Limits.PreservesBinaryBiproducts Hi :=
    Limits.preservesBinaryBiproducts_of_preservesBiproducts Hi
  -- Functoriality of `⊗` plus binary distributivity split `C ⊗ D` into the four Künneth
  -- summands `E⊗F ⊞ H_C⊗F ⊞ E⊗H_D ⊞ H_C⊗H_D`.
  let Θ : binaryOperation C D ≅
      (binaryOperation E F ⊞ binaryOperation (homologyComplex C) F)
        ⊞ (binaryOperation E (homologyComplex D)
            ⊞ binaryOperation (homologyComplex C) (homologyComplex D)) :=
    tensorIso iC iD ≪≫
      binaryOperation_biprod_right (E ⊞ homologyComplex C) F (homologyComplex D) ≪≫
      biprod.mapIso
        (binaryOperation_biprod_left E (homologyComplex C) F)
        (binaryOperation_biprod_left E (homologyComplex C) (homologyComplex D))
  -- Three of the four summands are acyclic, so their `Hⁱ` is a zero object.
  have hzEF : IsZero (Hi.obj (binaryOperation E F)) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (tensorProduct_acyclic_of_acyclic E F (Or.inl hE) i)
  have hzHCF : IsZero (Hi.obj (binaryOperation (homologyComplex C) F)) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (tensorProduct_acyclic_of_acyclic (homologyComplex C) F (Or.inr hF) i)
  have hzEHD : IsZero (Hi.obj (binaryOperation E (homologyComplex D))) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (tensorProduct_acyclic_of_acyclic E (homologyComplex D) (Or.inl hE) i)
  -- Collapse `Hⁱ(four-way biprod)` down to `Hⁱ(H_C ⊗ H_D)` by killing the three zero summands.
  let collapse : Hi.obj ((binaryOperation E F ⊞ binaryOperation (homologyComplex C) F)
        ⊞ (binaryOperation E (homologyComplex D)
            ⊞ binaryOperation (homologyComplex C) (homologyComplex D))) ≅
      Hi.obj (binaryOperation (homologyComplex C) (homologyComplex D)) :=
    Hi.mapBiprod _ _ ≪≫
      biprod.mapIso (Hi.mapBiprod _ _) (Hi.mapBiprod _ _) ≪≫
      (Limits.isoZeroBiprod ((Limits.biprod_isZero_iff _ _).mpr ⟨hzEF, hzHCF⟩)).symm ≪≫
      (Limits.isoZeroBiprod hzEHD).symm
  -- Assemble: `Hⁱ(C⊗D) ≅ Hⁱ(four-way) ≅ Hⁱ(H_C⊗H_D) ≅ ∐ Hʲ(C) ⊗ Hᵐ(D)`.
  exact ⟨Hi.mapIso Θ ≪≫ collapse ≪≫ homologyTensorProductHomologyIso C D i⟩

end RepresentationTheory.Algebra.Homology.CochainComplex.HomologyComplex
