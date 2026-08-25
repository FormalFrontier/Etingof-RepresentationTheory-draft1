/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Homology.TensorProduct
import RepresentationTheory.Algebra.CategoryTheory.FreeModuleTensorProduct
import RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution
import RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

set_option backward.isDefEq.respectTransparency false



open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct MulOpposite

namespace RepresentationTheory.Algebra.Homology.TensorResolution

universe u

variable {k : Type u} [Field k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable {M₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {M₂ : ModuleCat.{u} A₂ᵐᵒᵖ}



attribute [local instance] RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.leftRestrictionModule RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.rightRestrictionModule RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.leftRestrictionModule_isScalarTower RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.rightRestrictionModule_isScalarTower RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductModule


private theorem extTensorComplex_X_eq (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (n : ℕ) :
    (RepresentationTheory.Algebra.Homology.TensorProduct.tensorProductComplex (k := k) P₁ P₂).X n
      = (((((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).mapBifunctorHomologicalComplex
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
          P₂.complex).toGradedObject.mapObj
          (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ))) n :=
  rfl


/-- Each term of the tensor-resolution complex is projective. -/
theorem projective_tensorResolution_X (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (n : ℕ) : Projective ((RepresentationTheory.Algebra.Homology.TensorProduct.tensorProductComplex (k := k) P₁ P₂).X n) := by
  rw [extTensorComplex_X_eq]
  set g := ((((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
    P₂.complex).toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n with hg
  
  haveI hsummand : ∀ i, Projective (g i) := by
    rw [hg]; rintro ⟨⟨i₁, i₂⟩, h⟩
    exact RepresentationTheory.Algebra.CategoryTheory.FreeModuleTensorProduct.projective_binaryFunctor_obj k A₁ A₂ (P₁.complex.X i₁) (P₂.complex.X i₂)
  haveI hcop : HasCoproduct g := by rw [hg]; infer_instance
  change Projective (∐ g)
  refine ⟨fun {E X} f e he => ⟨Sigma.desc fun b => Projective.factorThru (Sigma.ι g b ≫ f) e, ?_⟩⟩
  apply Sigma.hom_ext
  intro b
  rw [Sigma.ι_desc_assoc]
  exact Projective.factorThru_comp _ e


/-- Restriction of scalars preserves homology for any ring homomorphism. -/
theorem restrictScalars_preservesHomology {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars.{u} f).PreservesHomology := by
  haveI : Limits.PreservesColimits (ModuleCat.restrictScalars.{u} f) :=
    (ModuleCat.restrictCoextendScalarsAdj f).leftAdjoint_preservesColimits
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _


/-- The positive-degree homology after mapping a projective resolution is zero. -/
theorem isZero_homology_mapProjectiveResolution_succ
    {R : Type u} [Ring R] {N : ModuleCat.{u} R} (Q : ProjectiveResolution N)
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} k) [F.Additive] [F.PreservesHomology] (n : ℕ) :
    IsZero (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).homology (n + 1)) := by
  have hqi : QuasiIsoAt ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π) (n + 1) :=
    inferInstance
  rw [quasiIsoAt_iff_isIso_homologyMap] at hqi
  refine IsZero.of_iso ?_ (asIso (HomologicalComplex.homologyMap
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π) (n + 1)))
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ)
    (n + 1)).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).app N))
  exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 (F.obj N) (n + 1)
    (by simp)


/-- The positive-degree homology of the tensor-resolution complex vanishes. -/
theorem isZero_homology_tensorProjectiveResolution_succ
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    IsZero ((HomologicalComplex.tensorObj (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFirstProjectiveResolution (k := k) P₁)
      (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsSecondProjectiveResolution (k := k) P₂)).homology (n + 1)) := by
  haveI : (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromFirstAlgebra k A₁).PreservesHomology := restrictScalars_preservesHomology _
  haveI : (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromSecondAlgebra k A₂).PreservesHomology := restrictScalars_preservesHomology _
  refine IsZero.of_iso ?_
    (RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing.homologyTensorIsoSigma (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFirstProjectiveResolution (k := k) P₁) (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsSecondProjectiveResolution (k := k) P₂) (n + 1))
  rw [IsZero.iff_id_eq_zero]
  apply Limits.Sigma.hom_ext
  intro a
  rw [Category.comp_id, comp_zero]
  obtain ⟨⟨p, q⟩, hpq⟩ := a
  have hpq' : p + q = n + 1 := hpq
  refine IsZero.eq_zero_of_src ?_ _
  rcases p with _ | p'
  · have hq : q = n + 1 := by omega
    subst hq
    exact RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing.tensorObj_isZero_of_right
      (isZero_homology_mapProjectiveResolution_succ P₂ (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromSecondAlgebra k A₂) n)
  · exact RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing.tensorObj_isZero_of_left
      (isZero_homology_mapProjectiveResolution_succ P₁ (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromFirstAlgebra k A₁) p')


/-- A complex morphism into a degree-zero complex is a quasi-isomorphism at zero under the stated cokernel condition. -/
theorem quasiIsoAt_zero_of_isColimitCokernel {V : Type*} [Category V] [Abelian V]
    {K : ChainComplex V ℕ} {N : V} (φ : K ⟶ (ChainComplex.single₀ V).obj N)
    (hc : IsColimit (CokernelCofork.ofπ (φ.f 0)
      (show K.d 1 0 ≫ φ.f 0 = 0 by
        rw [← φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]))) :
    QuasiIsoAt φ 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  
  have hcompare : K.pOpcycles 0 ≫
      (IsColimit.coconePointUniqueUpToIso (K.opcyclesIsCokernel 1 0 (by simp)) hc).hom = φ.f 0 := by
    have := IsColimit.comp_coconePointUniqueUpToIso_hom
      (K.opcyclesIsCokernel 1 0 (by simp)) hc WalkingParallelPair.one
    simpa only [Cofork.app_one_eq_π, CokernelCofork.π_ofπ] using this
  
  haveI : IsIso (((ChainComplex.single₀ V).obj N).pOpcycles 0) :=
    ((ChainComplex.single₀ V).obj N).isIso_pOpcycles 1 0 (by simp)
      (by rw [HomologicalComplex.single_obj_d])
  
  haveI : IsIso (HomologicalComplex.opcyclesMap φ 0) := by
    have hmap : HomologicalComplex.opcyclesMap φ 0 =
        (IsColimit.coconePointUniqueUpToIso (K.opcyclesIsCokernel 1 0 (by simp)) hc).hom ≫
          ((ChainComplex.single₀ V).obj N).pOpcycles 0 := by
      rw [← cancel_epi (K.pOpcycles 0), HomologicalComplex.p_opcyclesMap, ← Category.assoc,
        hcompare]
    rw [hmap]; infer_instance
  
  have key : HomologicalComplex.homologyMap φ 0 =
      K.isoHomologyι₀.hom ≫ HomologicalComplex.opcyclesMap φ 0 ≫
        ((ChainComplex.single₀ V).obj N).isoHomologyι₀.inv := by
    rw [← ChainComplex.isoHomologyι₀_inv_naturality, Iso.hom_inv_id_assoc]
  rw [key]; infer_instance


/-- Provides a cokernel colimit for a compatible tensor-product map. -/
noncomputable def isColimit_cokernelCofork_tensor
    {C₁ C₂ : ChainComplex (ModuleCat.{u} k) ℕ} [HomologicalComplex.HasTensor C₁ C₂]
    {N₁ N₂ : ModuleCat.{u} k} {p₁ : C₁.X 0 ⟶ N₁} {p₂ : C₂.X 0 ⟶ N₂}
    (hp₁comm : C₁.d 1 0 ≫ p₁ = 0) (hp₂comm : C₂.d 1 0 ≫ p₂ = 0)
    (hc₁ : IsColimit (CokernelCofork.ofπ p₁ hp₁comm))
    (hc₂ : IsColimit (CokernelCofork.ofπ p₂ hp₂comm))
    {q : (HomologicalComplex.tensorObj C₁ C₂).X 0 ⟶ N₁ ⊗ N₂}
    (hqcomm : (HomologicalComplex.tensorObj C₁ C₂).d 1 0 ≫ q = 0)
    (hq : HomologicalComplex.ιTensorObj C₁ C₂ 0 0 0 rfl ≫ q = MonoidalCategory.tensorHom p₁ p₂) :
    IsColimit (CokernelCofork.ofπ q hqcomm) := by
  have htensor := CokernelCofork.isColimitTensor hc₁ hc₂
  have hππ : Cofork.π (CokernelCofork.tensor (CokernelCofork.ofπ p₁ hp₁comm)
      (CokernelCofork.ofπ p₂ hp₂comm)) = MonoidalCategory.tensorHom p₁ p₂ := by
    rw [CokernelCofork.π_ofπ, CokernelCofork.π_ofπ, CokernelCofork.π_ofπ]
  have hrel1 : HomologicalComplex.ιTensorObj C₁ C₂ 1 0 1 rfl ≫
      (HomologicalComplex.tensorObj C₁ C₂).d 1 0
      = (C₁.d 1 0 ▷ C₂.X 0) ≫ HomologicalComplex.ιTensorObj C₁ C₂ 0 0 0 rfl := by
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₂_eq_zero (K₁ := C₁) (K₂ := C₂)
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.down ℕ)
        (i₁ := 1) (i₂ := 0) (j := 0) (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]),
      HomologicalComplex.mapBifunctor.d₁_eq (K₁ := C₁) (K₂ := C₂)
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.down ℕ)
        (i₁ := 1) (i₁' := 0) (i₂ := 0) (j := 0) (by simp [ComplexShape.down_Rel])
        (by simp ),
      show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (1, 0) = 1 from rfl, one_smul, add_zero]
    rfl
  have hrel2 : HomologicalComplex.ιTensorObj C₁ C₂ 0 1 1 rfl ≫
      (HomologicalComplex.tensorObj C₁ C₂).d 1 0
      = (C₁.X 0 ◁ C₂.d 1 0) ≫ HomologicalComplex.ιTensorObj C₁ C₂ 0 0 0 rfl := by
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq_zero (K₁ := C₁) (K₂ := C₂)
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.down ℕ)
        (i₁ := 0) (i₂ := 1) (j := 0) (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]),
      HomologicalComplex.mapBifunctor.d₂_eq (K₁ := C₁) (K₂ := C₂)
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.down ℕ)
        (i₁ := 0) (i₂ := 1) (i₂' := 0) (j := 0) (by simp [ComplexShape.down_Rel])
        (by simp ),
      show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (0, 1) = 1 from by simp [ComplexShape.ε₂, ComplexShape.ε],
      one_smul, zero_add]
    rfl
  refine Cofork.IsColimit.mk _
    (fun s => htensor.desc (CokernelCofork.ofπ
      (HomologicalComplex.ιTensorObj C₁ C₂ 0 0 0 rfl ≫ Cofork.π s) ?_)) ?_ ?_
  · apply Limits.coprod.hom_ext
    · rw [Limits.coprod.inl_desc_assoc, comp_zero, ← Category.assoc, ← hrel1, Category.assoc,
        CokernelCofork.condition s, comp_zero]
    · rw [Limits.coprod.inr_desc_assoc, comp_zero, ← Category.assoc, ← hrel2, Category.assoc,
        CokernelCofork.condition s, comp_zero]
  · intro s
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    obtain ⟨rfl, rfl⟩ : i₁ = 0 ∧ i₂ = 0 := by
      have : i₁ + i₂ = 0 := h
      omega
    rw [← Category.assoc, CokernelCofork.π_ofπ, hq, ← hππ, Cofork.IsColimit.π_desc,
      CokernelCofork.π_ofπ]
  · intro s m hm
    rw [CokernelCofork.π_ofπ] at hm
    apply Cofork.IsColimit.hom_ext htensor
    rw [Cofork.IsColimit.π_desc, hππ, CokernelCofork.π_ofπ, ← hq, Category.assoc, hm]


/-- Constructs a projective resolution for the tensor product of two modules. -/
noncomputable def tensorProjectiveResolution
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    ProjectiveResolution (ModuleCat.of (A₁ ⊗[k] A₂)ᵐᵒᵖ (M₁ ⊗[k] M₂)) where
  complex := RepresentationTheory.Algebra.Homology.TensorProduct.tensorProductComplex P₁ P₂
  projective := projective_tensorResolution_X P₁ P₂
  π := RepresentationTheory.Algebra.Homology.TensorProduct.complexToSingleZero P₁ P₂
  quasiIso := by
    haveI : (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromTensorProductAlgebra k A₁ A₂).PreservesHomology :=
      restrictScalars_preservesHomology (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ)
    rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology (RepresentationTheory.Algebra.Homology.TensorProduct.complexToSingleZero P₁ P₂)
      (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromTensorProductAlgebra k A₁ A₂)]
    set sIso := RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsTensorResolutionIso (k := k) P₁ P₂ with hsIso
    set tIso := (HomologicalComplex.singleMapHomologicalComplex (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromTensorProductAlgebra k A₁ A₂)
        (ComplexShape.down ℕ) 0).app (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ M₁ M₂) ≪≫
      (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
        (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsExternalTensorProductIso (k := k) M₁ M₂) with htIso
    set Φ := sIso.inv ≫ ((RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromTensorProductAlgebra k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (RepresentationTheory.Algebra.Homology.TensorProduct.complexToSingleZero P₁ P₂) ≫ tIso.hom with hΦ
    suffices hQ : QuasiIso Φ by
      have heq : ((RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromTensorProductAlgebra k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (RepresentationTheory.Algebra.Homology.TensorProduct.complexToSingleZero P₁ P₂) = sIso.hom ≫ Φ ≫ tIso.inv := by
        rw [hΦ]; simp
      rw [heq]; infer_instance
    rw [quasiIso_iff]
    rintro (_ | n)
    · 
      refine quasiIsoAt_zero_of_isColimitCokernel Φ ?_
      
      set p₁ : (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFirstProjectiveResolution P₁).X 0 ⟶ (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromFirstAlgebra k A₁).obj M₁ :=
        (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromFirstAlgebra k A₁).map ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1 with hp₁def
      set p₂ : (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsSecondProjectiveResolution P₂).X 0 ⟶ (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromSecondAlgebra k A₂).obj M₂ :=
        (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromSecondAlgebra k A₂).map ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 with hp₂def
      
      haveI : Limits.PreservesColimits (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromFirstAlgebra k A₁) :=
        (ModuleCat.restrictCoextendScalarsAdj (algebraMap k A₁ᵐᵒᵖ)).leftAdjoint_preservesColimits
      haveI : Limits.PreservesColimits (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromSecondAlgebra k A₂) :=
        (ModuleCat.restrictCoextendScalarsAdj (algebraMap k A₂ᵐᵒᵖ)).leftAdjoint_preservesColimits
      have hp₁comm : (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFirstProjectiveResolution P₁).d 1 0 ≫ p₁ = 0 := by
        have h : (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFirstProjectiveResolution P₁).d 1 0 ≫ p₁ = (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromFirstAlgebra k A₁).map (P₁.complex.d 1 0 ≫ P₁.π.f 0) := by
          rw [Functor.map_comp]; rfl
        rw [h, ProjectiveResolution.complex_d_comp_π_f_zero, Functor.map_zero]
      have hp₂comm : (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsSecondProjectiveResolution P₂).d 1 0 ≫ p₂ = 0 := by
        have h : (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsSecondProjectiveResolution P₂).d 1 0 ≫ p₂ = (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromSecondAlgebra k A₂).map (P₂.complex.d 1 0 ≫ P₂.π.f 0) := by
          rw [Functor.map_comp]; rfl
        rw [h, ProjectiveResolution.complex_d_comp_π_f_zero, Functor.map_zero]
      have hc₁ : IsColimit (CokernelCofork.ofπ p₁ hp₁comm) :=
        P₁.cokernelCofork.mapIsColimit P₁.isColimitCokernelCofork (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromFirstAlgebra k A₁)
      have hc₂ : IsColimit (CokernelCofork.ofπ p₂ hp₂comm) :=
        P₂.cokernelCofork.mapIsColimit P₂.isColimitCokernelCofork (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromSecondAlgebra k A₂)
      
      have h₀ : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (0, 0) = 0 := rfl
      have hgapA : HomologicalComplex.ιTensorObj (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFirstProjectiveResolution P₁) (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsSecondProjectiveResolution P₂) 0 0 0 rfl ≫
          Φ.f 0 = MonoidalCategory.tensorHom p₁ p₂ := by
        have hs0 : sIso.inv.f 0 = (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsTensorResolutionXIso P₁ P₂ 0).inv := by rw [hsIso]; rfl
        have hmid0 : (((RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromTensorProductAlgebra k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
            (RepresentationTheory.Algebra.Homology.TensorProduct.complexToSingleZero P₁ P₂)).f 0 = (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromTensorProductAlgebra k A₁ A₂).map (RepresentationTheory.Algebra.Homology.TensorProduct.zeroComponentToTarget P₁ P₂) := by
          change (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFromTensorProductAlgebra k A₁ A₂).map ((RepresentationTheory.Algebra.Homology.TensorProduct.complexToSingleZero P₁ P₂).f 0) = _
          congr 1
        have ht0 : tIso.hom.f 0 = (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsExternalTensorProductIso M₁ M₂).hom := by
          rw [htIso, Iso.trans_hom, HomologicalComplex.comp_f, Iso.app_hom,
            HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
          simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, CategoryTheory.Functor.map_id,
            Iso.refl_inv, Category.id_comp,
            CategoryTheory.Functor.mapIso_hom, ChainComplex.single₀_map_f_zero]
          exact Category.id_comp _
        rw [hΦ]
        simp only [HomologicalComplex.comp_f]
        rw [hs0, hmid0, ht0, ← Category.assoc,
          RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsTensorResolutionXIso_inv_iota (k := k) P₁ P₂ 0 0 0 h₀, Category.assoc,
          RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsTensorResolutionIso_zero_augmentation (k := k) P₁ P₂ h₀, Iso.inv_hom_id_assoc]
      
      exact isColimit_cokernelCofork_tensor hp₁comm hp₂comm hc₁ hc₂
        (show (HomologicalComplex.tensorObj (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsFirstProjectiveResolution P₁) (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution.restrictScalarsSecondProjectiveResolution P₂)).d 1 0 ≫ Φ.f 0 = 0 by
          rw [← Φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]) hgapA
    · 
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff_isZero_homology]
      exact isZero_homology_tensorProjectiveResolution_succ P₁ P₂ n

end RepresentationTheory.Algebra.Homology.TensorResolution
