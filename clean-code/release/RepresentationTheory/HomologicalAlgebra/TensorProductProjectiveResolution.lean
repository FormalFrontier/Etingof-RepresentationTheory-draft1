/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.TensorProduct.LinearMapModuleEquiv
import RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct
import RepresentationTheory.Algebra.Homology.LinearYoneda
import RepresentationTheory.HomologicalComplex.TensorExtension

/-!
# Degreewise linear Yoneda comparison for tensor products of projective resolutions

This module constructs the degreewise comparison between linear Yoneda applied to a tensor-product
projective resolution and the tensor product of the corresponding linear Yoneda complexes.
-/

open CategoryTheory Limits MonoidalCategory TensorProduct HomologicalComplex

namespace RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution

universe u

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
  [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
variable
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))

/-- The module-category object over the tensor product algebra carried by the tensor product of two modules. -/
noncomputable abbrev TensorProductProjectiveResolution.tensorProductModuleObject : ModuleCat.{u} (A₁ ⊗[k] A₂) := ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)

attribute [local instance] RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTower RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTowerAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductModule

section Summand

variable {A₁ A₂}

include hN in
/-- For finite projective modules, morphisms from their tensor product into the tensor product coefficient module are isomorphic to the tensor product of the two morphism modules. -/
noncomputable def TensorProductProjectiveResolution.homTensorProductIsoTensorHom (X₁ : ModuleCat.{u} A₁) (X₂ : ModuleCat.{u} A₂)
    [Module.Finite A₁ X₁] [Module.Projective A₁ X₁]
    [Module.Finite A₂ X₂] [Module.Projective A₂ X₂] :
    ModuleCat.of k (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ X₁ X₂ ⟶ TensorProductProjectiveResolution.tensorProductModuleObject k A₁ A₂ N₁ N₂) ≅
      (ModuleCat.of k (X₁ ⟶ ModuleCat.of A₁ N₁)) ⊗ (ModuleCat.of k (X₂ ⟶ ModuleCat.of A₂ N₂)) :=
  ModuleCat.homLinearEquiv.toModuleIso ≪≫
    RepresentationTheory.TensorProduct.LinearMapModuleEquiv.tensorProductLinearMapIso k N₁ N₂ hN X₁ X₂ ≪≫
    (tensorIso
      (ModuleCat.homLinearEquiv (M := X₁) (N := ModuleCat.of A₁ N₁) (S := k)).toModuleIso
      (ModuleCat.homLinearEquiv (M := X₂) (N := ModuleCat.of A₂ N₂) (S := k)).toModuleIso).symm

end Summand

/-! ## Reconciling the two `k`-module structures

The degreewise objects of the source/target cochain complexes appear in `linearYoneda` form
(`((linearYoneda k _).obj Y).obj (op Z)`), whose `k`-module structure comes through the categorical
`Linear.homModule`. The per-summand `TensorProductProjectiveResolution.homTensorProductIsoTensorHom` and the target tensor factors, by contrast, are
spelled `ModuleCat.of k (Z ⟶ Y)`, whose `k`-module structure is `ModuleCat.Hom.instModule`, picking
the external `Module k` on the codomain `N` (`TensorProduct` on `N₁ ⊗ N₂`, and the ambient one on
each `Nᵢ`). These two `k`-module structures are not definitionally equal; they agree only
through the scalar tower (`algebraMap_smul`). The two lemmas below record the resulting object
equalities so that `eqToIso` can relate the two spellings. -/

/-- A component of the linear Yoneda complex is the module of morphisms from the corresponding component of the original complex. -/
theorem TensorProductProjectiveResolution.linearYonedaObjComponent (A : Type u) [Ring A] [Algebra k A] (N : Type u)
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    (C : ChainComplex (ModuleCat.{u} A) ℕ) (j : ℕ) :
    (C.linearYonedaObj k (ModuleCat.of A N)).X j = ModuleCat.of k (C.X j ⟶ ModuleCat.of A N) := by
  rw [ChainComplex.linearYonedaObj_X]
  dsimp only [linearYoneda]
  congr 1
  refine Module.ext' _ _ (fun r f => ?_)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact algebraMap_smul A r ((ModuleCat.Hom.hom f) z)

section Assembly

variable {A₁ A₂}
variable {M₁ : ModuleCat.{u} A₁} {M₂ : ModuleCat.{u} A₂}
variable (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
variable [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
variable [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)]

include hN in
/-- Linear Yoneda evaluated on a tensor-product object agrees with the module of morphisms into the tensor product coefficient object. -/
theorem TensorProductProjectiveResolution.linearYonedaTensorObjectComponent (j m : ℕ) :
    ((linearYoneda k (ModuleCat.{u} (A₁ ⊗[k] A₂))).obj (TensorProductProjectiveResolution.tensorProductModuleObject k A₁ A₂ N₁ N₂)).obj (Opposite.op
        (((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj (P₁.complex.X j)).obj (P₂.complex.X m))) =
      ModuleCat.of k (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ (P₁.complex.X j) (P₂.complex.X m) ⟶
        TensorProductProjectiveResolution.tensorProductModuleObject k A₁ A₂ N₁ N₂) := by
  dsimp only [linearYoneda]
  congr 1
  refine Module.ext' _ _ (fun r f => ?_)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact algebraMap_smul (A₁ ⊗[k] A₂) r ((ModuleCat.Hom.hom f) z)

include hN in
/-- A degreewise isomorphism from linear Yoneda on a tensor-product object to the tensor product of the two linear Yoneda components. -/
noncomputable def TensorProductProjectiveResolution.linearYonedaTensorObjectIso (j m : ℕ) :
    ((linearYoneda k (ModuleCat.{u} (A₁ ⊗[k] A₂))).obj (TensorProductProjectiveResolution.tensorProductModuleObject k A₁ A₂ N₁ N₂)).obj (Opposite.op
        (((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj (P₁.complex.X j)).obj (P₂.complex.X m))) ≅
      ((curriedTensor (ModuleCat.{u} k)).obj
          ((P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁)).X j)).obj
        ((P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)).X m) :=
  eqToIso (TensorProductProjectiveResolution.linearYonedaTensorObjectComponent k N₁ N₂ hN P₁ P₂ j m) ≪≫
    TensorProductProjectiveResolution.homTensorProductIsoTensorHom k N₁ N₂ hN (P₁.complex.X j) (P₂.complex.X m) ≪≫
    tensorIso (eqToIso (TensorProductProjectiveResolution.linearYonedaObjComponent k A₁ N₁ P₁.complex j).symm)
      (eqToIso (TensorProductProjectiveResolution.linearYonedaObjComponent k A₂ N₂ P₂.complex m).symm)

/-- The contravariant module-valued functor obtained from the tensor product of two coefficient modules. -/
noncomputable abbrev TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor : (ModuleCat.{u} (A₁ ⊗[k] A₂))ᵒᵖ ⥤ ModuleCat.{u} k :=
  (linearYoneda k (ModuleCat.{u} (A₁ ⊗[k] A₂))).obj (TensorProductProjectiveResolution.tensorProductModuleObject k A₁ A₂ N₁ N₂)

/-- The morphism from a tensor-product summand indexed by two degrees to the component in their total degree. -/
noncomputable abbrev TensorProductProjectiveResolution.summandToTotalComponent (i j m : ℕ) (h : j + m = i) :
    ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj (P₁.complex.X j)).obj (P₂.complex.X m) ⟶
      (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).X i :=
  ιMapBifunctor P₁.complex P₂.complex (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂) (ComplexShape.down ℕ) j m i h

/-- The morphism from a component in total degree to the tensor-product summand indexed by two degrees with that sum. -/
noncomputable def TensorProductProjectiveResolution.totalComponentToSummand (i j m : ℕ) (_h : j + m = i) :
    (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).X i ⟶
      ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj (P₁.complex.X j)).obj (P₂.complex.X m) :=
  mapBifunctorDesc (j := i) (fun a b _ =>
    if hjm : a = j ∧ b = m then eqToHom (by rw [hjm.1, hjm.2]) else 0)

/-- An auxiliary theorem whose formal type was unavailable for inspection. -/
@[reassoc]
theorem TensorProductProjectiveResolution.Auxiliary.auxiliaryTheoremOne (i j m j' m' : ℕ) (h : j + m = i) (h' : j' + m' = i) :
    TensorProductProjectiveResolution.summandToTotalComponent k P₁ P₂ i j m h ≫ TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i j' m' h' =
      if hjm : j = j' ∧ m = m' then eqToHom (by rw [hjm.1, hjm.2]) else 0 := by
  rw [TensorProductProjectiveResolution.summandToTotalComponent, TensorProductProjectiveResolution.totalComponentToSummand, ι_mapBifunctorDesc]

/-- A second auxiliary theorem whose formal type was unavailable for inspection. -/
add_decl_doc TensorProductProjectiveResolution.Auxiliary.auxiliaryTheoremOne_assoc

/-- The finite type of pairs of natural numbers whose sum is a prescribed degree. -/
noncomputable instance TensorProductProjectiveResolution.fintypeDegreePairs (i : ℕ) : Fintype {p : ℕ × ℕ // p.1 + p.2 = i} := by
  apply Fintype.ofInjective (β := Fin (i + 1)) (fun q => ⟨q.1.1, by have := q.2; omega⟩)
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ hh
  simp only [Fin.mk.injEq] at hh
  apply Subtype.ext
  simp only [Prod.mk.injEq]
  exact ⟨hh, by omega⟩

/-- Summing the projection-inclusion composites over all degree pairs gives the identity on the corresponding total component. -/
theorem TensorProductProjectiveResolution.sum_totalComponentToSummand_comp_summandToTotalComponent (i : ℕ) :
    (∑ p : {p : ℕ × ℕ // p.1 + p.2 = i},
      TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i p.1.1 p.1.2 p.2 ≫ TensorProductProjectiveResolution.summandToTotalComponent k P₁ P₂ i p.1.1 p.1.2 p.2) =
      𝟙 ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).X i) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  rw [Preadditive.comp_sum, Category.comp_id]
  rw [Finset.sum_eq_single (⟨(a, b), hab⟩ : {p : ℕ × ℕ // p.1 + p.2 = i})]
  · change TensorProductProjectiveResolution.summandToTotalComponent k P₁ P₂ i a b hab ≫ TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i a b hab ≫
        TensorProductProjectiveResolution.summandToTotalComponent k P₁ P₂ i a b hab = _
    rw [← Category.assoc, TensorProductProjectiveResolution.Auxiliary.auxiliaryTheoremOne]
    simp
  · intro q _ hq
    rw [← Category.assoc]
    change (TensorProductProjectiveResolution.summandToTotalComponent k P₁ P₂ i a b hab ≫ TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i q.1.1 q.1.2 q.2) ≫ _ = 0
    rw [TensorProductProjectiveResolution.Auxiliary.auxiliaryTheoremOne, dif_neg (by rintro ⟨rfl, rfl⟩; exact hq (Subtype.ext (by simp))), zero_comp]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- The cochain complex over the base field associated to two projective resolutions and their coefficient modules. -/
noncomputable abbrev TensorProductProjectiveResolution.tensorLinearYonedaComplex : CochainComplex (ModuleCat.{u} k) ℕ :=
  HomologicalComplex.tensorObj
    (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
    (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂))

/-- The morphism from a pair-indexed tensor product of linear Yoneda components into the associated total-degree component. -/
noncomputable abbrev TensorProductProjectiveResolution.tensorLinearYonedaSummandToTotal (i j m : ℕ) (h : j + m = i) :
    ((curriedTensor (ModuleCat.{u} k)).obj
        ((P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁)).X j)).obj
      ((P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)).X m) ⟶
      (TensorProductProjectiveResolution.tensorLinearYonedaComplex k N₁ N₂ P₁ P₂).X i :=
  ιMapBifunctor (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
    (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)) (curriedTensor (ModuleCat.{u} k))
    (ComplexShape.up ℕ) j m i h

include hN in
/-- The degreewise morphism from linear Yoneda applied to the total tensor-product resolution to the tensor complex. -/
noncomputable def TensorProductProjectiveResolution.linearYonedaTotalToTensorComplex (i : ℕ) :
    (TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).obj (Opposite.op ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).X i)) ⟶
      (TensorProductProjectiveResolution.tensorLinearYonedaComplex k N₁ N₂ P₁ P₂).X i :=
  ∑ p : {p : ℕ × ℕ // p.1 + p.2 = i},
    (TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map (TensorProductProjectiveResolution.summandToTotalComponent k P₁ P₂ i p.1.1 p.1.2 p.2).op ≫
      (TensorProductProjectiveResolution.linearYonedaTensorObjectIso k N₁ N₂ hN P₁ P₂ p.1.1 p.1.2).hom ≫
        TensorProductProjectiveResolution.tensorLinearYonedaSummandToTotal k N₁ N₂ P₁ P₂ i p.1.1 p.1.2 p.2

include hN in
/-- The degreewise morphism from the tensor complex to linear Yoneda applied to the total tensor-product resolution. -/
noncomputable def TensorProductProjectiveResolution.tensorComplexToLinearYonedaTotal (i : ℕ) :
    (TensorProductProjectiveResolution.tensorLinearYonedaComplex k N₁ N₂ P₁ P₂).X i ⟶
      (TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).obj (Opposite.op ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).X i)) :=
  mapBifunctorDesc (j := i) (fun j m _ =>
    (TensorProductProjectiveResolution.linearYonedaTensorObjectIso k N₁ N₂ hN P₁ P₂ j m).inv ≫
      (TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map (TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i j m (by assumption)).op)

include hN in
/-- The degreewise isomorphism between linear Yoneda on the total tensor-product resolution and the associated tensor complex. -/
noncomputable def TensorProductProjectiveResolution.linearYonedaTotalIsoTensorComplex (i : ℕ) :
    (TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).obj (Opposite.op ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).X i)) ≅
      (TensorProductProjectiveResolution.tensorLinearYonedaComplex k N₁ N₂ P₁ P₂).X i where
  hom := TensorProductProjectiveResolution.linearYonedaTotalToTensorComplex k N₁ N₂ hN P₁ P₂ i
  inv := TensorProductProjectiveResolution.tensorComplexToLinearYonedaTotal k N₁ N₂ hN P₁ P₂ i
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    rw [TensorProductProjectiveResolution.tensorComplexToLinearYonedaTotal, ← Category.assoc, ι_mapBifunctorDesc, Category.comp_id, TensorProductProjectiveResolution.linearYonedaTotalToTensorComplex,
      Preadditive.comp_sum]
    rw [Finset.sum_eq_single (⟨(a, b), hab⟩ : {p : ℕ × ℕ // p.1 + p.2 = i})]
    · simp only [Category.assoc]
      rw [← Functor.map_comp_assoc, ← op_comp, TensorProductProjectiveResolution.Auxiliary.auxiliaryTheoremOne, dif_pos ⟨rfl, rfl⟩]
      simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.inv_hom_id_assoc]
    · intro q _ hq
      simp only [Category.assoc]
      rw [← Functor.map_comp_assoc, ← op_comp, TensorProductProjectiveResolution.Auxiliary.auxiliaryTheoremOne,
        dif_neg (by rintro ⟨rfl, rfl⟩; exact hq (Subtype.ext (by simp)))]
      simp only [op_zero, Functor.map_zero, zero_comp, comp_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  hom_inv_id := by
    rw [TensorProductProjectiveResolution.linearYonedaTotalToTensorComplex, TensorProductProjectiveResolution.tensorComplexToLinearYonedaTotal, Preadditive.sum_comp]
    have h1 : ∀ p : {p : ℕ × ℕ // p.1 + p.2 = i},
        ((TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map (TensorProductProjectiveResolution.summandToTotalComponent k P₁ P₂ i p.1.1 p.1.2 p.2).op ≫
          (TensorProductProjectiveResolution.linearYonedaTensorObjectIso k N₁ N₂ hN P₁ P₂ p.1.1 p.1.2).hom ≫
            TensorProductProjectiveResolution.tensorLinearYonedaSummandToTotal k N₁ N₂ P₁ P₂ i p.1.1 p.1.2 p.2) ≫
              mapBifunctorDesc (j := i) (fun j m _ =>
                (TensorProductProjectiveResolution.linearYonedaTensorObjectIso k N₁ N₂ hN P₁ P₂ j m).inv ≫
                  (TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map (TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i j m (by assumption)).op) =
          (TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map (TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i p.1.1 p.1.2 p.2 ≫
            TensorProductProjectiveResolution.summandToTotalComponent k P₁ P₂ i p.1.1 p.1.2 p.2).op := by
      intro p
      simp only [Category.assoc, TensorProductProjectiveResolution.tensorLinearYonedaSummandToTotal, ι_mapBifunctorDesc]
      rw [Iso.hom_inv_id_assoc, ← Functor.map_comp, ← op_comp]
    rw [Finset.sum_congr rfl (fun p _ => h1 p), ← Functor.map_sum (TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂),
      ← CategoryTheory.op_sum, TensorProductProjectiveResolution.sum_totalComponentToSummand_comp_summandToTotalComponent, op_id, CategoryTheory.Functor.map_id]

include hN in
/-- The componentwise isomorphism between linear Yoneda on the total tensor resolution and the tensor object of the two linear Yoneda complexes. -/
noncomputable def TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent (i : ℕ) :
    ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).linearYonedaObj k
        (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).X i ≅
      (HomologicalComplex.tensorObj
        (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂))).X i :=
  eqToIso (ChainComplex.linearYonedaObj_X _ _ _ _) ≪≫ TensorProductProjectiveResolution.linearYonedaTotalIsoTensorComplex k N₁ N₂ hN P₁ P₂ i

include hN in
/-- The summand inclusion followed by the inverse total-complex comparison equals the corresponding tensor-Hom comparison and mapped projection composite. -/
@[reassoc]
theorem TensorProductProjectiveResolution.summandInclusion_comp_linearYonedaTotalIso_inv (i j m : ℕ) (h : j + m = i) :
    ιMapBifunctor (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)) (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℕ) j m i h ≫ (TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ i).inv =
      (TensorProductProjectiveResolution.linearYonedaTensorObjectIso k N₁ N₂ hN P₁ P₂ j m).inv ≫
        (TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map (TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i j m h).op ≫
          eqToHom (ChainComplex.linearYonedaObj_X _ _ _ _).symm := by
  have h1 : ιMapBifunctor (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)) (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℕ) j m i h ≫ (TensorProductProjectiveResolution.linearYonedaTotalIsoTensorComplex k N₁ N₂ hN P₁ P₂ i).inv =
      (TensorProductProjectiveResolution.linearYonedaTensorObjectIso k N₁ N₂ hN P₁ P₂ j m).inv ≫
        (TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map (TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i j m h).op := by
    change _ ≫ TensorProductProjectiveResolution.tensorComplexToLinearYonedaTotal k N₁ N₂ hN P₁ P₂ i = _
    simp only [TensorProductProjectiveResolution.tensorComplexToLinearYonedaTotal, ι_mapBifunctorDesc]
  rw [TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent, Iso.trans_inv, eqToIso.inv, ← Category.assoc, h1, Category.assoc]

/-- The summand comparison identity remains valid after postcomposition with a morphism from the total linear Yoneda component. -/
add_decl_doc TensorProductProjectiveResolution.summandInclusion_comp_linearYonedaTotalIso_inv_assoc

end Assembly

end RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution
