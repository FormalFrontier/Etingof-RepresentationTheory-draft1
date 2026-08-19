/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import RepresentationTheory.Algebra.Homology.LinearYoneda
import RepresentationTheory.CategoryTheory.Preadditive.IsoHomEquiv
import RepresentationTheory.CategoryTheory.Abelian.ObjectData
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.Grp.Zero

set_option backward.isDefEq.respectTransparency false



universe u

open CategoryTheory Limits CochainComplex.HomComplex

namespace RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.LinearYonedaComparison

variable (k : Type u) [Field k]
variable {A : Type u} [Ring A] [Algebra k A]
variable {M : ModuleCat.{u} A} (N : ModuleCat.{u} A)
  (P : RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData M)


/-- The additive cochain complex of morphisms from a projective resolution to a module concentrated in degree zero. -/
noncomputable abbrev CategoryTheory.ProjectiveResolution.homCochainComplex : CochainComplex AddCommGrpCat.{u} ℤ :=
  CochainComplex.HomComplex P.cochainComplex
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)


/-- Cochains in nonnegative degree are additively equivalent to morphisms from the corresponding resolution object to the coefficient module. -/
noncomputable def CategoryTheory.ProjectiveResolution.homCochainEquiv (i : ℕ) :
    Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) (i : ℤ)
      ≃+ (P.complex.X i ⟶ N) :=
  (Cochain.toSingleEquiv (K := P.cochainComplex) (X := N)
      (p := -(i : ℤ)) (q := 0) (n := (i : ℤ)) (by ring)).trans
    (RepresentationTheory.CategoryTheory.Preadditive.IsoHomEquiv.homPrecomposeIsoAddEquiv (P.cochainComplexXIso (-(i : ℤ)) i (by ring)))

/-- The cochain equivalence is computed using the inverse of the projective-resolution component isomorphism and the single-complex equivalence. -/
lemma CategoryTheory.ProjectiveResolution.homCochainEquiv_apply (i : ℕ)
    (z : Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)
      (i : ℤ)) :
    CategoryTheory.ProjectiveResolution.homCochainEquiv N P i z =
      (P.cochainComplexXIso (-(i : ℤ)) i (by ring)).inv ≫
        Cochain.toSingleEquiv (K := P.cochainComplex) (X := N)
          (p := -(i : ℤ)) (q := 0) (n := (i : ℤ)) (by ring) z := rfl


/-- Under the cochain equivalence, the coboundary is the signed composite with the differential of the projective resolution. -/
lemma CategoryTheory.ProjectiveResolution.homCochainEquiv_delta (i : ℕ)
    (z : Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)
      (i : ℤ)) :
    CategoryTheory.ProjectiveResolution.homCochainEquiv N P (i + 1) (δ (i : ℤ) (↑(i + 1)) z) =
      ((↑(i + 1) : ℤ)).negOnePow • (P.complex.d (i + 1) i ≫ CategoryTheory.ProjectiveResolution.homCochainEquiv N P i z) := by
  obtain ⟨g, rfl⟩ := Cochain.toSingleMk_surjective z (-(i : ℤ)) (by ring)
  rw [CategoryTheory.ProjectiveResolution.homCochainEquiv_apply, CategoryTheory.ProjectiveResolution.homCochainEquiv_apply,
    Cochain.δ_toSingleMk g (by ring) (↑(i + 1)) (-(↑(i + 1) : ℤ)) (by ring),
    Units.smul_def, map_zsmul, Cochain.toSingleEquiv_toSingleMk, Cochain.toSingleEquiv_toSingleMk,
    ProjectiveResolution.cochainComplex_d P (-(↑(i + 1) : ℤ)) (-(i : ℤ)) (i + 1) i
      (by ring) (by ring)]


  simp only [Units.smul_def, Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id_assoc]




/-- The functor sending a module over a field to its underlying additive commutative group. -/
noncomputable abbrev ModuleCat.forgetToAddCommGrp : ModuleCat.{u} k ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} k) AddCommGrpCat


/-- A unit of the integers parametrizes an additive equivalence from Hom-complex cochains to morphisms out of a resolution object. -/
noncomputable def CategoryTheory.ProjectiveResolution.signedHomCochainEquiv (i : ℕ) (u : ℤˣ) :
    Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) (i : ℤ)
      ≃+ (P.complex.X i ⟶ N) := (CategoryTheory.ProjectiveResolution.homCochainEquiv N P i).trans (DistribMulAction.toAddEquiv _ u)


/-- A signed isomorphism compares each object of the additive Hom complex with the underlying object of the linear Yoneda complex. -/
noncomputable def CategoryTheory.ProjectiveResolution.signedHomCochainIso (i : ℕ) (u : ℤˣ) :
    (CategoryTheory.ProjectiveResolution.homCochainComplex N P).X (i : ℤ) ≅ (ModuleCat.forgetToAddCommGrp k).obj ((P.complex.linearYonedaObj k N).X i) :=
  (CategoryTheory.ProjectiveResolution.signedHomCochainEquiv N P i u).toAddCommGrpIso

/-- The forward signed comparison sends an element to its cochain-equivalence image multiplied by the chosen integer unit. -/
@[simp] lemma CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_apply (i : ℕ) (u : ℤˣ) (z : (CategoryTheory.ProjectiveResolution.homCochainComplex N P).X (i : ℤ)) :
    (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P i u).hom z = (u : ℤ) • (CategoryTheory.ProjectiveResolution.homCochainEquiv N P i z) := by
  simp only [CategoryTheory.ProjectiveResolution.signedHomCochainIso, AddEquiv.toAddCommGrpIso_hom]; rfl


/-- Signed comparison isomorphisms intertwine consecutive differentials after twisting the target sign by the parity of the next degree. -/
lemma CategoryTheory.ProjectiveResolution.signedHomCochainIso_d (m : ℕ) (u : ℤˣ) :
    (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P m u).hom ≫ (ModuleCat.forgetToAddCommGrp k).map ((P.complex.linearYonedaObj k N).d m (m+1))
      = (CategoryTheory.ProjectiveResolution.homCochainComplex N P).d ↑m ↑(m+1)
        ≫ (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P (m+1) (u * (↑(m+1):ℤ).negOnePow)).hom := by
  ext z
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_apply, CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_apply]
  rw [show (ConcreteCategory.hom ((CategoryTheory.ProjectiveResolution.homCochainComplex N P).d (↑m) (↑(m+1)))) z
        = δ (↑m : ℤ) (↑(m+1)) z from rfl, CategoryTheory.ProjectiveResolution.homCochainEquiv_delta N P m z]
  rw [← Units.smul_def, ← Units.smul_def, smul_smul, mul_assoc, Int.units_mul_self, mul_one]
  simp only [ChainComplex.linearYonedaObj_d, ModuleCat.forget₂_map, ConcreteCategory.hom_ofHom]
  rfl


/-- The three consecutive terms of the additive Hom complex are isomorphic to the image under forgetting of the corresponding linear Yoneda short complex. -/
noncomputable def CategoryTheory.ProjectiveResolution.homShortComplexIso (m : ℕ) :
    (CategoryTheory.ProjectiveResolution.homCochainComplex N P).sc' (↑m) (↑(m+1)) (↑(m+2))
      ≅ ((P.complex.linearYonedaObj k N).sc' m (m+1) (m+2)).map (ModuleCat.forgetToAddCommGrp k) :=
  ShortComplex.isoMk (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P m 1) (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P (m+1) (1 * (↑(m+1):ℤ).negOnePow))
    (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P (m+2) (1 * (↑(m+1):ℤ).negOnePow * (↑(m+2):ℤ).negOnePow))
    (CategoryTheory.ProjectiveResolution.signedHomCochainIso_d k N P m 1) (CategoryTheory.ProjectiveResolution.signedHomCochainIso_d k N P (m+1) (1 * (↑(m+1):ℤ).negOnePow))


/-- Positive-degree Hom-complex homology is isomorphic to the underlying additive group of the corresponding linear Yoneda homology. -/
noncomputable def CategoryTheory.ProjectiveResolution.homCochainComplexSuccHomologyIso (m : ℕ) :
    (CategoryTheory.ProjectiveResolution.homCochainComplex N P).homology (↑(m+1))
      ≅ (ModuleCat.forgetToAddCommGrp k).obj ((P.complex.linearYonedaObj k N).homology (m+1)) := by
  have hprevL : (ComplexShape.up ℤ).prev (↑(m+1)) = ↑m := by simp
  have hnextL : (ComplexShape.up ℤ).next (↑(m+1)) = ↑(m+2) := by
    have h : (ComplexShape.up ℤ).Rel (↑(m+1)) (↑(m+2)) := by
      simp only [ComplexShape.up_Rel]; omega
    rw [ComplexShape.next_eq' _ h]
  have hprevR : (ComplexShape.up ℕ).prev (m+1) = m := by simp
  have hnextR : (ComplexShape.up ℕ).next (m+1) = m+2 := by simp
  exact ShortComplex.homologyMapIso
      ((CategoryTheory.ProjectiveResolution.homCochainComplex N P).isoSc' (↑m) (↑(m+1)) (↑(m+2)) hprevL hnextL) ≪≫
    ShortComplex.homologyMapIso (CategoryTheory.ProjectiveResolution.homShortComplexIso k N P m) ≪≫
    ((P.complex.linearYonedaObj k N).sc' m (m+1) (m+2)).mapHomologyIso (ModuleCat.forgetToAddCommGrp k) ≪≫
    (ModuleCat.forgetToAddCommGrp k).mapIso (ShortComplex.homologyMapIso
      ((P.complex.linearYonedaObj k N).isoSc' m (m+1) (m+2) hprevR hnextR)).symm


/-- A theorem whose formal expression could not be rendered. -/
lemma CategoryTheory.ProjectiveResolution.homCochainComplex_homology_aux : IsZero ((CategoryTheory.ProjectiveResolution.homCochainComplex N P).X (-1)) := by
  have hz1 : IsZero (P.cochainComplex.X 1) :=
    P.cochainComplex.isZero_of_isStrictlyLE 0 1 (by norm_num)
  have e := (Cochain.toSingleEquiv (K := P.cochainComplex) (X := N)
    (p := (1:ℤ)) (q := 0) (n := -1) (by ring))
  haveI : Subsingleton (P.cochainComplex.X 1 ⟶ N) := ⟨fun f g => (hz1.eq_of_src f g)⟩
  haveI : Subsingleton ↑((CategoryTheory.ProjectiveResolution.homCochainComplex N P).X (-1)) := e.toEquiv.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _


/-- A definition whose formal expression could not be rendered. -/
noncomputable def CategoryTheory.ProjectiveResolution.signedHomologyComparison :
    ((P.complex.linearYonedaObj k N).sc' 0 0 (0+1)).map (ModuleCat.forgetToAddCommGrp k)
      ⟶ (CategoryTheory.ProjectiveResolution.homCochainComplex N P).sc' (-1) (↑(0:ℕ)) (↑(0+1:ℕ)) where
  τ₁ := 0
  τ₂ := (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P 0 1).inv
  τ₃ := (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P (0+1) (1 * (↑(0+1):ℤ).negOnePow)).inv
  comm₁₂ := by
    have hf : (((P.complex.linearYonedaObj k N).sc' 0 0 (0+1)).map (ModuleCat.forgetToAddCommGrp k)).f = 0 := by
      change (ModuleCat.forgetToAddCommGrp k).map ((P.complex.linearYonedaObj k N).d 0 0) = 0
      rw [(P.complex.linearYonedaObj k N).shape 0 0 (by simp), Functor.map_zero]
    rw [hf, zero_comp, zero_comp]
  comm₂₃ := by
    simp only [ShortComplex.map_g, HomologicalComplex.shortComplexFunctor'_obj_g]
    refine (Iso.inv_comp_eq _).mpr ?_
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).mpr (CategoryTheory.ProjectiveResolution.signedHomCochainIso_d k N P 0 1).symm


/-- Degree-zero Hom-complex homology is isomorphic to the underlying additive group of degree-zero linear Yoneda homology. -/
noncomputable def CategoryTheory.ProjectiveResolution.homCochainComplexZeroHomologyIso :
    (CategoryTheory.ProjectiveResolution.homCochainComplex N P).homology (↑(0:ℕ))
      ≅ (ModuleCat.forgetToAddCommGrp k).obj ((P.complex.linearYonedaObj k N).homology 0) := by
  have hprevL : (ComplexShape.up ℤ).prev (↑(0:ℕ)) = -1 := by simp
  have hnextL : (ComplexShape.up ℤ).next (↑(0:ℕ)) = ↑(0+1:ℕ) := by
    have h : (ComplexShape.up ℤ).Rel (↑(0:ℕ)) (↑(0+1:ℕ)) := by
      simp only [ComplexShape.up_Rel]; omega
    rw [ComplexShape.next_eq' _ h]
  have hprevR : (ComplexShape.up ℕ).prev 0 = 0 := by simp
  have hnextR : (ComplexShape.up ℕ).next 0 = 0+1 := by simp
  haveI : Epi (CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P).τ₁ := (CategoryTheory.ProjectiveResolution.homCochainComplex_homology_aux N P).epi _
  haveI : IsIso (CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P).τ₂ := inferInstanceAs (IsIso (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P 0 1).inv)
  haveI : Mono (CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P).τ₃ :=
    inferInstanceAs (Mono (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P (0+1) (1 * (↑(0+1):ℤ).negOnePow)).inv)
  exact ShortComplex.homologyMapIso
      ((CategoryTheory.ProjectiveResolution.homCochainComplex N P).isoSc' (-1) (↑(0:ℕ)) (↑(0+1:ℕ)) hprevL hnextL) ≪≫
    (asIso (ShortComplex.homologyMap (CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P))).symm ≪≫
    ((P.complex.linearYonedaObj k N).sc' 0 0 (0+1)).mapHomologyIso (ModuleCat.forgetToAddCommGrp k) ≪≫
    (ModuleCat.forgetToAddCommGrp k).mapIso (ShortComplex.homologyMapIso
      ((P.complex.linearYonedaObj k N).isoSc' 0 0 (0+1) hprevR hnextR)).symm


/-- Homology of the additive Hom cochain complex is isomorphic to the underlying additive group of linear Yoneda homology. -/
noncomputable def CategoryTheory.ProjectiveResolution.homCochainComplexHomologyIso (n : ℕ) :
    (CategoryTheory.ProjectiveResolution.homCochainComplex N P).homology (↑n)
      ≅ (ModuleCat.forgetToAddCommGrp k).obj ((P.complex.linearYonedaObj k N).homology n) := by
  cases n with
  | zero => exact CategoryTheory.ProjectiveResolution.homCochainComplexZeroHomologyIso k N P
  | succ m => exact CategoryTheory.ProjectiveResolution.homCochainComplexSuccHomologyIso k N P m


/-- Homology of the additive Hom cochain complex is additively equivalent to the underlying homology of the linear Yoneda complex. -/
noncomputable def CategoryTheory.ProjectiveResolution.homCochainComplexHomologyAddEquiv (n : ℕ) :
    (CategoryTheory.ProjectiveResolution.homCochainComplex N P).homology (↑n)
      ≃+ (P.complex.linearYonedaObj k N).homology n :=
  (CategoryTheory.ProjectiveResolution.homCochainComplexHomologyIso k N P n).addCommGroupIsoToAddEquiv



variable {N' : ModuleCat.{u} A}


/-- The additive map on Hom-complex cochains induced by postcomposition with a module morphism. -/
noncomputable def CategoryTheory.ProjectiveResolution.homCochainMap (g : N ⟶ N') (i : ℤ) :
    Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) i →+
      Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') i where
  toFun z := z.comp (Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g))
    (add_zero i)
  map_zero' := Cochain.zero_comp _ _
  map_add' z z' := Cochain.add_comp z z' _ _


/-- A coefficient-module morphism induces a morphism between the associated additive Hom cochain complexes. -/
noncomputable def CategoryTheory.ProjectiveResolution.homCochainComplexMap (g : N ⟶ N') :
    CategoryTheory.ProjectiveResolution.homCochainComplex N P ⟶ CategoryTheory.ProjectiveResolution.homCochainComplex N' P where
  f i := AddCommGrpCat.ofHom (CategoryTheory.ProjectiveResolution.homCochainMap N P g i)
  comm' i j _ := by
    ext z
    rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply]
    exact CochainComplex.HomComplex.δ_comp_ofHom z _ j

/-- A component of the induced Hom-complex morphism acts by composing a cochain with the coefficient morphism in the single complex. -/
@[simp] lemma CategoryTheory.ProjectiveResolution.homCochainComplexMap_f_apply (g : N ⟶ N') (i : ℤ)
    (z : (CategoryTheory.ProjectiveResolution.homCochainComplex N P).X i) :
    (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P g).f i z =
      z.comp (Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g))
        (add_zero i) := rfl



variable (g : N ⟶ N')


/-- The additive map on Hom-complex cocycles induced by a morphism of coefficient modules. -/
noncomputable def CategoryTheory.ProjectiveResolution.homCocycleMap (n : ℤ) :
    Cocycle P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n →+
      Cocycle P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n where
  toFun z := z.postcomp ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g)
  map_zero' := by
    apply Cocycle.ext
    simp only [Cocycle.postcomp, Cocycle.mk_coe, Cocycle.coe_zero, Cochain.zero_comp]
  map_add' z z' := by
    apply Cocycle.ext
    simp only [Cocycle.postcomp, Cocycle.mk_coe, Cocycle.coe_add, Cochain.add_comp]

/-- The induced cocycle map is postcomposition by the image of the coefficient morphism in the single complex. -/
@[simp] lemma CategoryTheory.ProjectiveResolution.homCocycleMap_apply (n : ℤ)
    (z : Cocycle P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n) :
    CategoryTheory.ProjectiveResolution.homCocycleMap N P g n z =
      z.postcomp ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g) := rfl


/-- Coboundaries lie in the kernel of the composite from cochains to target cohomology classes. -/
lemma CategoryTheory.ProjectiveResolution.homCocycleMap_coboundaries_le_ker (n : ℤ) :
    coboundaries P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n ≤
      ((CohomologyClass.mkAddMonoidHom P.cochainComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n).comp
        (CategoryTheory.ProjectiveResolution.homCocycleMap N P g n)).ker := by
  rintro α ⟨m, hm, β, hβ⟩
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
    CategoryTheory.ProjectiveResolution.homCocycleMap_apply, CohomologyClass.mkAddMonoidHom_apply, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  refine ⟨β.comp (Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g))
    (add_zero m), ?_⟩
  rw [δ_comp_ofHom, hβ]
  rfl


/-- The additive map on Hom-complex cohomology classes induced by a coefficient-module morphism. -/
noncomputable def CategoryTheory.ProjectiveResolution.homCohomologyClassMap (n : ℤ) :
    CohomologyClass P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n →+
      CohomologyClass P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n).comp
      (CategoryTheory.ProjectiveResolution.homCocycleMap N P g n))
    (CategoryTheory.ProjectiveResolution.homCocycleMap_coboundaries_le_ker N P g n)

/-- The induced cohomology-class map sends a represented cocycle to the class of its postcomposition. -/
@[simp] lemma CategoryTheory.ProjectiveResolution.homCohomologyClassMap_mk (n : ℤ)
    (c : Cocycle P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n) :
    CategoryTheory.ProjectiveResolution.homCohomologyClassMap N P g n (CohomologyClass.mk c) =
      CohomologyClass.mk
        (c.postcomp ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g)) := rfl


/-- Left-homology map data for the short-complex map induced by a morphism of coefficient modules. -/
noncomputable def CategoryTheory.ProjectiveResolution.homLeftHomologyMapData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).map
        (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P g))
      (CochainComplex.HomComplex.leftHomologyData P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n)
      (CochainComplex.HomComplex.leftHomologyData P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n) := by
  set h₂ := CochainComplex.HomComplex.leftHomologyData P.cochainComplex
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n with hh₂
  have hcommi :
      AddCommGrpCat.ofHom (CategoryTheory.ProjectiveResolution.homCocycleMap N P g n) ≫ h₂.i
        = (CochainComplex.HomComplex.leftHomologyData P.cochainComplex
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n).i
          ≫ ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).map
              (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P g)).τ₂ := by
    ext c
    rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply]
    rfl
  haveI : Mono h₂.i := by
    rw [AddCommGrpCat.mono_iff_injective]
    exact fun a b hab => Subtype.ext hab
  exact
  { φK := AddCommGrpCat.ofHom (CategoryTheory.ProjectiveResolution.homCocycleMap N P g n)
    φH := AddCommGrpCat.ofHom (CategoryTheory.ProjectiveResolution.homCohomologyClassMap N P g n)
    commi := hcommi
    commπ := by
      ext c
      rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply]
      rfl
    commf' := by
      rw [← cancel_mono h₂.i]
      simp only [Category.assoc, hcommi]
      rw [h₂.f'_i, ← Category.assoc,
        (CochainComplex.HomComplex.leftHomologyData P.cochainComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n).f'_i]
      exact (((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).map
        (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P g)).comm₁₂).symm }

/-- The homology morphism in the induced left-homology map data is the additive-group morphism of the cohomology-class map. -/
@[simp] lemma CategoryTheory.ProjectiveResolution.homLeftHomologyMapData_phiH (n : ℤ) :
    (CategoryTheory.ProjectiveResolution.homLeftHomologyMapData N P g n).φH
      = AddCommGrpCat.ofHom (CategoryTheory.ProjectiveResolution.homCohomologyClassMap N P g n) := rfl


/-- The Hom-complex homology additive equivalence agrees pointwise with the morphism of its left-homology isomorphism. -/
lemma CategoryTheory.ProjectiveResolution.homComplex_homologyAddEquiv_eq_homologyIso_hom (L : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (y : (P.cochainComplex.HomComplex L).homology n) :
    CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex L n y
      = (CochainComplex.HomComplex.leftHomologyData P.cochainComplex L n).homologyIso.hom y := rfl


/-- The Hom-complex homology equivalence commutes with the maps induced by a coefficient-module morphism. -/
lemma CategoryTheory.ProjectiveResolution.homComplex_homologyAddEquiv_naturality (n : ℤ)
    (y : (CategoryTheory.ProjectiveResolution.homCochainComplex N P).homology n) :
    CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n
        ((HomologicalComplex.homologyMap (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P g) n) y)
      = CategoryTheory.ProjectiveResolution.homCohomologyClassMap N P g n
          (CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n y) := by
  have h := ConcreteCategory.congr_hom
    (CategoryTheory.ProjectiveResolution.homLeftHomologyMapData N P g n).homologyMap_comm y
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at h
  exact h


/-- The inverse homology equivalence carries the class of a postcomposed cocycle to the homology map of the original class. -/
lemma CategoryTheory.ProjectiveResolution.homComplex_homologyAddEquiv_symm_mk_naturality (n : ℤ)
    (c : Cocycle P.cochainComplex
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n) :
    (CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N') n).symm
        (CohomologyClass.mk
          (c.postcomp ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map g)))
      = (HomologicalComplex.homologyMap (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P g) n)
          ((CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) n).symm
            (CohomologyClass.mk c)) := by
  rw [AddEquiv.symm_apply_eq, CategoryTheory.ProjectiveResolution.homComplex_homologyAddEquiv_naturality, AddEquiv.apply_symm_apply,
    CategoryTheory.ProjectiveResolution.homCohomologyClassMap_mk]




/-- The cochain equivalence carries the induced coefficient map to postcomposition by that coefficient morphism. -/
lemma CategoryTheory.ProjectiveResolution.homCochainEquiv_map_apply (g : N ⟶ N') (i : ℕ)
    (z : (CategoryTheory.ProjectiveResolution.homCochainComplex N P).X (i : ℤ)) :
    CategoryTheory.ProjectiveResolution.homCochainEquiv N' P i ((CategoryTheory.ProjectiveResolution.homCochainComplexMap N P g).f (i : ℤ) z)
      = CategoryTheory.ProjectiveResolution.homCochainEquiv N P i z ≫ g := by
  rw [CategoryTheory.ProjectiveResolution.homCochainComplexMap_f_apply, CategoryTheory.ProjectiveResolution.homCochainEquiv_apply, CategoryTheory.ProjectiveResolution.homCochainEquiv_apply, Category.assoc]
  congr 1
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-(i : ℤ)) (by ring)
  rw [← Cochain.toSingleMk_postcomp, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk]


/-- Forgetting the scalar multiple of an identity morphism sends an element to its scalar multiple. -/
lemma ModuleCat.forgetToAddCommGrp_map_smul_id_apply (r : k) (X : ModuleCat.{u} k) (w : X) :
    (ModuleCat.forgetToAddCommGrp k).map (r • 𝟙 X) w = r • w := by
  rw [ModuleCat.forget₂_map]
  simp only [ModuleCat.hom_smul, ModuleCat.hom_id]
  rfl


/-- The forward signed comparison intertwines scalar multiplication on the additive and linear Yoneda Hom complexes pointwise. -/
lemma CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_map_smul_apply (r : k) (i : ℕ) (u : ℤˣ)
    (z : (CategoryTheory.ProjectiveResolution.homCochainComplex N P).X (i : ℤ)) :
    (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P i u).hom ((CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N)).f (i : ℤ) z)
      = (ModuleCat.forgetToAddCommGrp k).map (r • 𝟙 ((P.complex.linearYonedaObj k N).X i)) ((CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P i u).hom z) := by
  rw [CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_apply, CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_apply, ModuleCat.forgetToAddCommGrp_map_smul_id_apply,
    CategoryTheory.ProjectiveResolution.homCochainEquiv_map_apply, Linear.comp_smul, Category.comp_id, smul_comm]


/-- The canonical comparison between homology of a complex and homology of its associated short complex is natural for endomorphisms. -/
lemma HomologicalComplex.homologyMapIso_naturality
    {C : Type*} [Category C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
    [CategoryWithHomology C] {K : HomologicalComplex C c} (α : K ⟶ K) (i j l : ι)
    (hi : c.prev j = i) (hl : c.next j = l) :
    HomologicalComplex.homologyMap α j
        ≫ (ShortComplex.homologyMapIso (K.isoSc' i j l hi hl)).hom
      = (ShortComplex.homologyMapIso (K.isoSc' i j l hi hl)).hom
          ≫ ShortComplex.homologyMap
              ((HomologicalComplex.shortComplexFunctor' C c i j l).map α) := by
  simp only [ShortComplex.homologyMapIso_hom]
  rw [show HomologicalComplex.homologyMap α j
        = ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor C c j).map α) from rfl,
    ← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  exact (HomologicalComplex.natIsoSc' C c i j l hi hl).hom.naturality α


/-- The forward signed comparison is natural with respect to scalar multiplication endomorphisms. -/
lemma CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_naturality_smul (r : k) (i : ℕ) (u : ℤˣ) :
    (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N)).f (i : ℤ) ≫ (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P i u).hom
      = (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P i u).hom ≫ (ModuleCat.forgetToAddCommGrp k).map (r • 𝟙 ((P.complex.linearYonedaObj k N).X i)) := by
  ext z
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply]
  exact CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_map_smul_apply k N P r i u z


/-- The short-complex comparison isomorphism commutes with the maps induced by scalar multiplication. -/
lemma CategoryTheory.ProjectiveResolution.homShortComplexIso_naturality_smul (r : k) (m : ℕ) :
    (HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (ComplexShape.up ℤ)
        ↑m ↑(m+1) ↑(m+2)).map (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N))
        ≫ (CategoryTheory.ProjectiveResolution.homShortComplexIso k N P m).hom
      = (CategoryTheory.ProjectiveResolution.homShortComplexIso k N P m).hom
          ≫ (ModuleCat.forgetToAddCommGrp k).mapShortComplex.map
              ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
                  m (m+1) (m+2)).map (r • 𝟙 (P.complex.linearYonedaObj k N))) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  · exact CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_naturality_smul k N P r m 1
  · exact CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_naturality_smul k N P r (m+1) (1 * (↑(m+1):ℤ).negOnePow)
  · exact CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_naturality_smul k N P r (m+2)
      (1 * (↑(m+1):ℤ).negOnePow * (↑(m+2):ℤ).negOnePow)


/-- The positive-degree homology comparison isomorphism commutes with scalar multiplication maps. -/
lemma CategoryTheory.ProjectiveResolution.homCochainComplexSuccHomologyIso_naturality_smul (r : k) (m : ℕ) :
    HomologicalComplex.homologyMap (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N)) (↑(m+1))
        ≫ (CategoryTheory.ProjectiveResolution.homCochainComplexSuccHomologyIso k N P m).hom
      = (CategoryTheory.ProjectiveResolution.homCochainComplexSuccHomologyIso k N P m).hom
          ≫ (ModuleCat.forgetToAddCommGrp k).map (HomologicalComplex.homologyMap
              (r • 𝟙 (P.complex.linearYonedaObj k N)) (m+1)) := by
  set φ := CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N) with hφ
  set ψ := r • 𝟙 (P.complex.linearYonedaObj k N) with hψ
  have hprevL : (ComplexShape.up ℤ).prev (↑(m+1)) = ↑m := by simp
  have hnextL : (ComplexShape.up ℤ).next (↑(m+1)) = ↑(m+2) := by
    rw [ComplexShape.next_eq' _ (by simp only [ComplexShape.up_Rel]; omega :
      (ComplexShape.up ℤ).Rel (↑(m+1)) (↑(m+2)))]
  have hprevR : (ComplexShape.up ℕ).prev (m+1) = m := by simp
  have hnextR : (ComplexShape.up ℕ).next (m+1) = m+2 := by simp
  have hA := HomologicalComplex.homologyMapIso_naturality φ (↑m) (↑(m+1)) (↑(m+2)) hprevL hnextL
  have hB : ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (ComplexShape.up ℤ)
          ↑m ↑(m+1) ↑(m+2)).map φ)
        ≫ (ShortComplex.homologyMapIso (CategoryTheory.ProjectiveResolution.homShortComplexIso k N P m)).hom
      = (ShortComplex.homologyMapIso (CategoryTheory.ProjectiveResolution.homShortComplexIso k N P m)).hom
          ≫ ShortComplex.homologyMap ((ModuleCat.forgetToAddCommGrp k).mapShortComplex.map
              ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
                  m (m+1) (m+2)).map ψ)) := by
    rw [ShortComplex.homologyMapIso_hom,
      ← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
      CategoryTheory.ProjectiveResolution.homShortComplexIso_naturality_smul]
  have hC := ShortComplex.mapHomologyIso_hom_naturality (F := ModuleCat.forgetToAddCommGrp k)
    (φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
      m (m+1) (m+2)).map ψ)
  have hR := HomologicalComplex.homologyMapIso_naturality ψ m (m+1) (m+2) hprevR hnextR
  have hDinner : ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          m (m+1) (m+2)).map ψ)
        ≫ (ShortComplex.homologyMapIso
            ((P.complex.linearYonedaObj k N).isoSc' m (m+1) (m+2) hprevR hnextR)).inv
      = (ShortComplex.homologyMapIso
          ((P.complex.linearYonedaObj k N).isoSc' m (m+1) (m+2) hprevR hnextR)).inv
          ≫ HomologicalComplex.homologyMap ψ (m+1) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hR.symm
  have hD : (ModuleCat.forgetToAddCommGrp k).map (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          m (m+1) (m+2)).map ψ))
        ≫ (ModuleCat.forgetToAddCommGrp k).map (ShortComplex.homologyMapIso
            ((P.complex.linearYonedaObj k N).isoSc' m (m+1) (m+2) hprevR hnextR)).inv
      = (ModuleCat.forgetToAddCommGrp k).map (ShortComplex.homologyMapIso
          ((P.complex.linearYonedaObj k N).isoSc' m (m+1) (m+2) hprevR hnextR)).inv
          ≫ (ModuleCat.forgetToAddCommGrp k).map (HomologicalComplex.homologyMap ψ (m+1)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hDinner]
  simp only [CategoryTheory.ProjectiveResolution.homCochainComplexSuccHomologyIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [reassoc_of% hA, reassoc_of% hB, reassoc_of% hC, hD]
  simp only [Category.assoc]


/-- The inverse signed comparison is natural with respect to scalar multiplication endomorphisms. -/
lemma CategoryTheory.ProjectiveResolution.signedHomCochainIso_inv_naturality_smul (r : k) (i : ℕ) (u : ℤˣ) :
    (ModuleCat.forgetToAddCommGrp k).map (r • 𝟙 ((P.complex.linearYonedaObj k N).X i)) ≫ (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P i u).inv
      = (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P i u).inv ≫ (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N)).f (i : ℤ) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, CategoryTheory.ProjectiveResolution.signedHomCochainIso_hom_naturality_smul]


/-- A theorem whose formal expression could not be rendered. -/
lemma CategoryTheory.ProjectiveResolution.signedHomologyComparison_naturality_smul (r : k) :
    (ModuleCat.forgetToAddCommGrp k).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          0 0 (0+1)).map (r • 𝟙 (P.complex.linearYonedaObj k N)))
        ≫ CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P
      = CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P
          ≫ (HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (ComplexShape.up ℤ)
              (-1) (↑(0:ℕ)) (↑(0+1:ℕ))).map (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N)) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  · simp only [CategoryTheory.ProjectiveResolution.signedHomologyComparison, ShortComplex.comp_τ₁, comp_zero, zero_comp]
  · exact CategoryTheory.ProjectiveResolution.signedHomCochainIso_inv_naturality_smul k N P r 0 1
  · exact CategoryTheory.ProjectiveResolution.signedHomCochainIso_inv_naturality_smul k N P r (0+1) (1 * (↑(0+1):ℤ).negOnePow)


/-- The degree-zero homology comparison isomorphism commutes with scalar multiplication maps. -/
lemma CategoryTheory.ProjectiveResolution.homCochainComplexZeroHomologyIso_naturality_smul (r : k) :
    HomologicalComplex.homologyMap (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N)) (↑(0:ℕ))
        ≫ (CategoryTheory.ProjectiveResolution.homCochainComplexZeroHomologyIso k N P).hom
      = (CategoryTheory.ProjectiveResolution.homCochainComplexZeroHomologyIso k N P).hom
          ≫ (ModuleCat.forgetToAddCommGrp k).map (HomologicalComplex.homologyMap
              (r • 𝟙 (P.complex.linearYonedaObj k N)) 0) := by
  set φ := CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N) with hφ
  set ψ := r • 𝟙 (P.complex.linearYonedaObj k N) with hψ
  have hprevL : (ComplexShape.up ℤ).prev (↑(0:ℕ)) = -1 := by simp
  have hnextL : (ComplexShape.up ℤ).next (↑(0:ℕ)) = ↑(0+1:ℕ) := by
    rw [ComplexShape.next_eq' _ (by simp only [ComplexShape.up_Rel]; omega :
      (ComplexShape.up ℤ).Rel (↑(0:ℕ)) (↑(0+1:ℕ)))]
  have hprevR : (ComplexShape.up ℕ).prev 0 = 0 := by simp
  have hnextR : (ComplexShape.up ℕ).next 0 = 0+1 := by simp
  haveI : Epi (CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P).τ₁ := (CategoryTheory.ProjectiveResolution.homCochainComplex_homology_aux N P).epi _
  haveI : IsIso (CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P).τ₂ := inferInstanceAs (IsIso (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P 0 1).inv)
  haveI : Mono (CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P).τ₃ :=
    inferInstanceAs (Mono (CategoryTheory.ProjectiveResolution.signedHomCochainIso k N P (0+1) (1 * (↑(0+1):ℤ).negOnePow)).inv)
  have hA := HomologicalComplex.homologyMapIso_naturality φ (-1) (↑(0:ℕ)) (↑(0+1:ℕ)) hprevL hnextL
  have hSmap : ShortComplex.homologyMap ((ModuleCat.forgetToAddCommGrp k).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          0 0 (0+1)).map ψ)) ≫ ShortComplex.homologyMap (CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P)
      = ShortComplex.homologyMap (CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P) ≫ ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (ComplexShape.up ℤ)
            (-1) (↑(0:ℕ)) (↑(0+1:ℕ))).map φ) := by
    rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp, CategoryTheory.ProjectiveResolution.signedHomologyComparison_naturality_smul]
  have hB : ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (ComplexShape.up ℤ)
          (-1) (↑(0:ℕ)) (↑(0+1:ℕ))).map φ) ≫ inv (ShortComplex.homologyMap (CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P))
      = inv (ShortComplex.homologyMap (CategoryTheory.ProjectiveResolution.signedHomologyComparison k N P))
          ≫ ShortComplex.homologyMap ((ModuleCat.forgetToAddCommGrp k).mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
            0 0 (0+1)).map ψ)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hSmap.symm
  have hC := ShortComplex.mapHomologyIso_hom_naturality (F := ModuleCat.forgetToAddCommGrp k)
    (φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
      0 0 (0+1)).map ψ)
  have hR := HomologicalComplex.homologyMapIso_naturality ψ 0 0 (0+1) hprevR hnextR
  have hDinner : ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          0 0 (0+1)).map ψ)
        ≫ (ShortComplex.homologyMapIso
            ((P.complex.linearYonedaObj k N).isoSc' 0 0 (0+1) hprevR hnextR)).inv
      = (ShortComplex.homologyMapIso
          ((P.complex.linearYonedaObj k N).isoSc' 0 0 (0+1) hprevR hnextR)).inv
          ≫ HomologicalComplex.homologyMap ψ 0 := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hR.symm
  have hD : (ModuleCat.forgetToAddCommGrp k).map (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℕ)
          0 0 (0+1)).map ψ))
        ≫ (ModuleCat.forgetToAddCommGrp k).map (ShortComplex.homologyMapIso
            ((P.complex.linearYonedaObj k N).isoSc' 0 0 (0+1) hprevR hnextR)).inv
      = (ModuleCat.forgetToAddCommGrp k).map (ShortComplex.homologyMapIso
          ((P.complex.linearYonedaObj k N).isoSc' 0 0 (0+1) hprevR hnextR)).inv
          ≫ (ModuleCat.forgetToAddCommGrp k).map (HomologicalComplex.homologyMap ψ 0) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hDinner]
  simp only [CategoryTheory.ProjectiveResolution.homCochainComplexZeroHomologyIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv]
  rw [reassoc_of% hA, reassoc_of% hB, reassoc_of% hC, hD]
  simp only [Category.assoc]


/-- The homology additive equivalence intertwines scalar multiplication maps on the two Hom complexes. -/
lemma CategoryTheory.ProjectiveResolution.homCochainComplexHomologyAddEquiv_map_smul (r : k) (n : ℕ)
    (z : (CategoryTheory.ProjectiveResolution.homCochainComplex N P).homology (↑n)) :
    CategoryTheory.ProjectiveResolution.homCochainComplexHomologyAddEquiv k N P n
        (HomologicalComplex.homologyMap (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N)) (↑n) z)
      = (HomologicalComplex.homologyMap
            (r • 𝟙 (P.complex.linearYonedaObj k N)) n).hom
          (CategoryTheory.ProjectiveResolution.homCochainComplexHomologyAddEquiv k N P n z) := by
  have hmor : HomologicalComplex.homologyMap (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N)) (↑n)
        ≫ (CategoryTheory.ProjectiveResolution.homCochainComplexHomologyIso k N P n).hom
      = (CategoryTheory.ProjectiveResolution.homCochainComplexHomologyIso k N P n).hom ≫ (ModuleCat.forgetToAddCommGrp k).map (HomologicalComplex.homologyMap
          (r • 𝟙 (P.complex.linearYonedaObj k N)) n) := by
    cases n with
    | zero => exact CategoryTheory.ProjectiveResolution.homCochainComplexZeroHomologyIso_naturality_smul k N P r
    | succ m => exact CategoryTheory.ProjectiveResolution.homCochainComplexSuccHomologyIso_naturality_smul k N P r m
  have key := ConcreteCategory.congr_hom hmor z
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at key
  exact key

end RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.LinearYonedaComparison
