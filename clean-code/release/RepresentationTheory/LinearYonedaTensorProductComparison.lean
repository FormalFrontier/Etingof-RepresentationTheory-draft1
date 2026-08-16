/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution

set_option backward.isDefEq.respectTransparency false

/-!
# The complex-level rearrangement isomorphism for the `Ext` Künneth formula

This file constructs the complex-level rearrangement isomorphism for the `Ext` half of
Problem 8.2.8. This is the `Hom`-cochain twin of `RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolutionComplexComparison.mappedComplexIsoTensorMappedProjectiveResolutionComplexes`
(`RepresentationTheory/HomologicalAlgebra/TensorProduct/ProjectiveResolutionComplexComparison.lean`), but built via `HomologicalComplex.Hom.isoOfComponents`
(assembled degreewise from the object iso) rather than `total.mapIso`, because the source
`Hom(mapBifunctor …, N)` is a product over the finite fiber, not a `mapBifunctor` bicomplex.

Combining the degreewise object iso `RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent` with the two
naturality lemmas `RepresentationTheory.TensorProduct.LinearMapModuleEquiv.tensorProductLinearMap_comp_map_left`/`RepresentationTheory.TensorProduct.LinearMapModuleEquiv.tensorProductLinearMap_comp_map_right` (discharging the two
differential-commutation squares), this file assembles the isomorphism of
`CochainComplex (ModuleCat k) ℕ`

```
linearYonedaTensorProductComplexIso :
  (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).linearYonedaObj k (N₁ ⊗ₖ N₂)
    ≅ HomologicalComplex.tensorObj
        (P₁.complex.linearYonedaObj k N₁)
        (P₂.complex.linearYonedaObj k N₂)
```

used by the Künneth `Ext` assembler.

## Construction

The degreewise components are `RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent`. The differential-commutation obligation for
`isoOfComponents` is discharged summand-by-summand on the target coproduct (via
`mapBifunctor.hom_ext`), reducing, through the `ι`/inv reduction
`RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.summandInclusion_comp_linearYonedaTotalIso_inv` and the source biproduct relations `RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.Auxiliary.auxiliaryTheoremOne`, to
the two naturality lemmas. The source differential
`(X.linearYonedaObj k Y).d i j = ofHom (Linear.leftComp k Y (X.d j i))` is precomposition by the
source chain differential; contravariance flips the fiber index from degree `i+1` (source) to `i`
(target).
-/

open CategoryTheory Limits MonoidalCategory TensorProduct HomologicalComplex

namespace RepresentationTheory.LinearYonedaTensorProductComparison

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

attribute [local instance] RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTower RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTowerAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductModule RepresentationTheory.TensorProduct.LinearMapModuleEquiv.tensorProductModuleIsScalarTower

variable {A₁ A₂}
variable {M₁ : ModuleCat.{u} A₁} {M₂ : ModuleCat.{u} A₂}
variable (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
variable [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
variable [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)]

/-- Applying a `ModuleCat k` `eqToHom` to an element is the `▸` transport of the element. Since the
`eqToHom` object equalities appearing in `RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectIso` (`RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectComponent`, `RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaObjComponent`) are
between `ModuleCat.of k T` objects sharing the same carrier `T`, the resulting `h ▸ x` is defeq to
`x`. -/
private lemma eqToHom_moduleCat_apply {X Y : ModuleCat.{u} k} (h : X = Y) (x : X) :
    (eqToHom h) x = h ▸ x := by cases h; rfl

/-- Applying a `ModuleCat k` `eqToHom` to an element yields a heterogeneously-equal element. When
the two objects share a carrier (the `RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectComponent`/`RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaObjComponent` object equalities of
`RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectIso`), this upgrades to an honest equation via `eq_of_heq`. -/
private lemma eqToHom_hom_apply_heq {X Y : ModuleCat.{u} k} (h : X = Y) (w : X) :
    HEq (ModuleCat.Hom.hom (eqToHom h) w) w := by subst h; rfl

include hN in
/-- Closed form of `RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.homTensorProductIsoTensorHom.inv` on a simple tensor `a₁ ⊗ₜ a₂` (plain morphisms, no `eqToHom`
transport), evaluated at `y₁ ⊗ₜ y₂`: it is `a₁ y₁ ⊗ₜ a₂ y₂`. The `eqToHom`-free core of
`fullSummandIso_inv_tmul_apply`. -/
private lemma summandIso_inv_tmul_apply (X₁ : ModuleCat.{u} A₁) (X₂ : ModuleCat.{u} A₂)
    [Module.Finite A₁ X₁] [Module.Projective A₁ X₁]
    [Module.Finite A₂ X₂] [Module.Projective A₂ X₂]
    (a₁ : X₁ ⟶ ModuleCat.of A₁ N₁) (a₂ : X₂ ⟶ ModuleCat.of A₂ N₂) (y₁ : X₁) (y₂ : X₂) :
    (ModuleCat.Hom.hom ((RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.homTensorProductIsoTensorHom k N₁ N₂ hN X₁ X₂).inv (a₁ ⊗ₜ[k] a₂))) (y₁ ⊗ₜ[k] y₂)
      = a₁.hom y₁ ⊗ₜ[k] a₂.hom y₂ := by
  simp only [RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.homTensorProductIsoTensorHom, RepresentationTheory.TensorProduct.LinearMapModuleEquiv.tensorProductLinearMapIso, Iso.trans_inv, Iso.symm_inv,
    LinearEquiv.toModuleIso_inv, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

set_option maxHeartbeats 1000000 in
include hN in
/-- Closed form of `RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectIso.inv` on a simple tensor `ψ₁ ⊗ₜ ψ₂`, evaluated at a simple tensor
`y₁ ⊗ₜ y₂`: it is `ψ₁ y₁ ⊗ₜ ψ₂ y₂` (`RepresentationTheory.TensorProduct.LinearMap.TensorProduct.linearMapTensor`). This is the pointwise reduction that both
naturality lemmas share; the `eqToHom` transports in `RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectIso` act as the identity on the
shared underlying `↦` map, discharged by `eqToHom_moduleCat_apply`. -/
private lemma fullSummandIso_inv_tmul_apply (j m : ℕ)
    (ψ₁ : ↥((P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁)).X j))
    (ψ₂ : ↥((P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)).X m))
    (y₁ : P₁.complex.X j) (y₂ : P₂.complex.X m) :
    (ModuleCat.Hom.hom (ModuleCat.Hom.hom (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectIso k N₁ N₂ hN P₁ P₂ j m).inv (ψ₁ ⊗ₜ[k] ψ₂)))
        (y₁ ⊗ₜ[k] y₂) = ψ₁.hom y₁ ⊗ₜ[k] ψ₂.hom y₂ := by
  have e0 := fun w => eq_of_heq (eqToHom_hom_apply_heq k (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectComponent k N₁ N₂ hN P₁ P₂ j m).symm w)
  have e1 := fun w => eq_of_heq (eqToHom_hom_apply_heq k (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaObjComponent k A₁ N₁ P₁.complex j) w)
  have e2 := fun w => eq_of_heq (eqToHom_hom_apply_heq k (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaObjComponent k A₂ N₂ P₂.complex m) w)
  simp only [RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectIso, Iso.trans_inv, tensorIso_inv, eqToIso.inv, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_tensorHom, e0]
  erw [TensorProduct.map_tmul]
  rw [e1, e2]
  rfl

set_option maxHeartbeats 1000000 in
include hN in
/-- The inverse degreewise comparison intertwines the differential in the first projective resolution with the corresponding mapped morphism. -/
@[reassoc]
theorem linearYonedaTensorDegreewiseIso_inv_naturality_fst (p q : ℕ) :
    ((curriedTensor (ModuleCat.{u} k)).map
          ((P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁)).d p (p + 1))).app
        ((P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)).X q) ≫
        (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectIso k N₁ N₂ hN P₁ P₂ (p + 1) q).inv =
      (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectIso k N₁ N₂ hN P₁ P₂ p q).inv ≫
        (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map
          (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap k (P₁.complex.d (p + 1) p) (𝟙 (P₂.complex.X q))).op := by
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' fun φ₁ φ₂ => ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, curriedTensor_map_app,
    ChainComplex.linearYonedaObj_d, ModuleCat.hom_whiskerRight, ModuleCat.hom_ofHom,
    linearYoneda_obj_map]
  erw [LinearMap.rTensor_tmul]
  apply ModuleCat.hom_ext
  refine RepresentationTheory.TensorProduct.LinearMap.LinearMap.ext_tmul k A₁ A₂ _ _ N₁ N₂ (fun x₁ x₂ => ?_)
  refine (fullSummandIso_inv_tmul_apply k N₁ N₂ hN P₁ P₂ (p + 1) q
      (Linear.leftComp k (ModuleCat.of A₁ N₁) (P₁.complex.d (p + 1) p) φ₁) φ₂ x₁ x₂).trans
    (Eq.trans ?_ (fullSummandIso_inv_tmul_apply k N₁ N₂ hN P₁ P₂ p q φ₁ φ₂
      ((P₁.complex.d (p + 1) p).hom x₁) x₂).symm)
  rfl

/-- The first-variable naturality identity for the inverse degreewise comparison remains valid after composition with a further morphism. -/
add_decl_doc linearYonedaTensorDegreewiseIso_inv_naturality_fst_assoc

include hN in
/-- The inverse degreewise comparison intertwines the differential in the second projective resolution with the corresponding mapped morphism. -/
@[reassoc]
theorem linearYonedaTensorDegreewiseIso_inv_naturality_snd (p q : ℕ) :
    ((curriedTensor (ModuleCat.{u} k)).obj
          ((P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁)).X p)).map
        ((P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)).d q (q + 1)) ≫
        (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectIso k N₁ N₂ hN P₁ P₂ p (q + 1)).inv =
      (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTensorObjectIso k N₁ N₂ hN P₁ P₂ p q).inv ≫
        (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map
          (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap k (𝟙 (P₁.complex.X p)) (P₂.complex.d (q + 1) q)).op := by
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' fun φ₁ φ₂ => ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, curriedTensor_obj_map,
    ChainComplex.linearYonedaObj_d, ModuleCat.hom_whiskerLeft, ModuleCat.hom_ofHom,
    linearYoneda_obj_map]
  erw [LinearMap.lTensor_tmul]
  apply ModuleCat.hom_ext
  refine RepresentationTheory.TensorProduct.LinearMap.LinearMap.ext_tmul k A₁ A₂ _ _ N₁ N₂ (fun x₁ x₂ => ?_)
  refine (fullSummandIso_inv_tmul_apply k N₁ N₂ hN P₁ P₂ p (q + 1)
      φ₁ (Linear.leftComp k (ModuleCat.of A₂ N₂) (P₂.complex.d (q + 1) q) φ₂) x₁ x₂).trans
    (Eq.trans ?_ (fullSummandIso_inv_tmul_apply k N₁ N₂ hN P₁ P₂ p q φ₁ φ₂
      x₁ ((P₂.complex.d (q + 1) q).hom x₂)).symm)
  rfl

/-- The second-variable naturality identity for the inverse degreewise comparison remains valid after composition with a further morphism. -/
add_decl_doc linearYonedaTensorDegreewiseIso_inv_naturality_snd_assoc

omit [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
  [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)] in
/-- Auxiliary result retained because its formal type could not be pretty printed. -/
theorem Auxiliary.opaqueResultB (i x y p q : ℕ) (hx : x + y = i) (hpq : p + q = i) :
    ιMapBifunctor P₁.complex P₂.complex (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (ComplexShape.down ℕ) x y i hx ≫ RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i p q hpq =
      if h : x = p ∧ y = q then eqToHom (by rw [h.1, h.2]) else 0 := by
  simp only [RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.totalComponentToSummand, ι_mapBifunctorDesc]

omit [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
  [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)] in
/-- Auxiliary result retained because its formal type could not be pretty printed. -/
theorem Auxiliary.opaqueResultA (i p q : ℕ) (hpq : p + q = i) :
    RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ (i + 1) (p + 1) q (by omega) ≫
        ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).map (P₁.complex.d (p + 1) p)).app (P₂.complex.X q) +
      (-1 : ℤˣ) ^ p • (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ (i + 1) p (q + 1) (by omega) ≫
        ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj (P₁.complex.X p)).map (P₂.complex.d (q + 1) q)) =
      (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).d (i + 1) i ≫ RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i p q hpq := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  have hab' : a + b = i + 1 := hab
  rw [Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc, ← Category.assoc,
    Auxiliary.opaqueResultB, Auxiliary.opaqueResultB, mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
  refine congr_arg₂ (· + ·) ?_ ?_
  · -- d₁ term: first-factor differential, sign 1
    rcases a with _ | a'
    · rw [mapBifunctor.d₁_eq_zero (K₁ := P₁.complex) (K₂ := P₂.complex)
          (F := RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂) (c := ComplexShape.down ℕ) 0 b i
          (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]), zero_comp,
        dif_neg (by rintro ⟨hcon, _⟩; exact Nat.succ_ne_zero p hcon.symm), zero_comp]
    · rw [mapBifunctor.d₁_eq (K₁ := P₁.complex) (K₂ := P₂.complex)
          (F := RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂) (c := ComplexShape.down ℕ)
          (show (ComplexShape.down ℕ).Rel (a' + 1) a' by simp [ComplexShape.down_Rel]) b i
          (show a' + b = i by omega), Linear.units_smul_comp, Category.assoc, Auxiliary.opaqueResultB,
        show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (a' + 1, b) = 1 from rfl, one_smul]
      by_cases hc : a' = p ∧ b = q
      · obtain ⟨rfl, rfl⟩ := hc
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      · rw [dif_neg (fun hcon => hc ⟨by omega, hcon.2⟩), dif_neg hc, comp_zero, zero_comp]
  · -- d₂ term: second-factor differential, sign (-1)^p
    rcases b with _ | b'
    · rw [mapBifunctor.d₂_eq_zero (K₁ := P₁.complex) (K₂ := P₂.complex)
          (F := RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂) (c := ComplexShape.down ℕ) a 0 i
          (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]), zero_comp,
        dif_neg (by rintro ⟨_, hcon⟩; exact Nat.succ_ne_zero q hcon.symm), zero_comp, smul_zero]
    · rw [mapBifunctor.d₂_eq (K₁ := P₁.complex) (K₂ := P₂.complex)
          (F := RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂) (c := ComplexShape.down ℕ) a
          (show (ComplexShape.down ℕ).Rel (b' + 1) b' by simp [ComplexShape.down_Rel]) i
          (show a + b' = i by omega), Linear.units_smul_comp, Category.assoc, Auxiliary.opaqueResultB]
      by_cases hc : a = p ∧ b' = q
      · obtain ⟨rfl, rfl⟩ := hc
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩,
          show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) (a, b' + 1) = (-1 : ℤˣ) ^ a from rfl]
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      · rw [dif_neg (fun hcon => hc ⟨hcon.1, by omega⟩), dif_neg hc]
        simp only [zero_comp, comp_zero, smul_zero]

include hN in
/-- The inverse maps of the componentwise comparison isomorphisms commute with the differentials. -/
theorem linearYonedaTensorProductComponentIso_inv_naturality (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.tensorLinearYonedaComplex k N₁ N₂ P₁ P₂).d i j ≫
        (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ j).inv =
      (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ i).inv ≫
        ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).linearYonedaObj k
          (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).d i j := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  obtain rfl : j = i + 1 := by rw [ComplexShape.up_Rel] at hij; omega
  have hpq' : p + q = i := hpq
  rw [RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.summandInclusion_comp_linearYonedaTotalIso_inv_assoc, ChainComplex.linearYonedaObj_d]
  simp only [mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
    mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
  rw [mapBifunctor.d₁_eq (K₁ := P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (K₂ := P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂))
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.up ℕ)
        (show (ComplexShape.up ℕ).Rel p (p + 1) by simp [ComplexShape.up_Rel]) q (i + 1)
        (show p + 1 + q = i + 1 by omega),
      mapBifunctor.d₂_eq (K₁ := P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (K₂ := P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂))
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.up ℕ) p
        (show (ComplexShape.up ℕ).Rel q (q + 1) by simp [ComplexShape.up_Rel]) (i + 1)
        (show p + (q + 1) = i + 1 by omega),
      Linear.units_smul_comp, Linear.units_smul_comp, Category.assoc, Category.assoc,
      RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.summandInclusion_comp_linearYonedaTotalIso_inv, RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.summandInclusion_comp_linearYonedaTotalIso_inv,
      linearYonedaTensorDegreewiseIso_inv_naturality_fst_assoc, linearYonedaTensorDegreewiseIso_inv_naturality_snd_assoc,
      show RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap k (P₁.complex.d (p + 1) p) (𝟙 (P₂.complex.X q))
          = ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).map (P₁.complex.d (p + 1) p)).app (P₂.complex.X q)
        from rfl,
      show RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap k (𝟙 (P₁.complex.X p)) (P₂.complex.d (q + 1) q)
          = ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj (P₁.complex.X p)).map (P₂.complex.d (q + 1) q)
        from rfl]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← op_comp, ← op_comp,
      show ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = 1
        from rfl, one_smul,
      show ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q)
        = (-1 : ℤˣ) ^ p from RepresentationTheory.HomologicalComplex.TensorExtension.opaqueAuxiliary p]
  rw [← Linear.comp_units_smul, ← Preadditive.comp_add]
  congr 1
  rw [← Linear.units_smul_comp, ← Preadditive.add_comp]
  have key : (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ (i + 1) (p + 1) q (by omega) ≫
        ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).map (P₁.complex.d (p + 1) p)).app (P₂.complex.X q)).op +
      (-1 : ℤˣ) ^ p • (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ (i + 1) p (q + 1) (by omega) ≫
        ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj (P₁.complex.X p)).map (P₂.complex.d (q + 1) q)).op =
      (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.totalComponentToSummand k P₁ P₂ i p q hpq).op ≫
        (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.tensorProductLinearYonedaFunctor k N₁ N₂).map ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).d (i + 1) i).op := by
    rw [← Functor.map_comp, ← op_comp, ← Auxiliary.opaqueResultA k P₁ P₂ i p q hpq', op_add, Functor.map_add]
    congr 1
    simp only [Units.smul_def, op_zsmul, Functor.map_zsmul]
  rw [key, Category.assoc]
  congr 1

include hN in
/-- The forward maps of the componentwise comparison isomorphisms commute with the differentials. -/
theorem linearYonedaTensorProductComponentIso_hom_naturality (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ i).hom ≫
        (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.tensorLinearYonedaComplex k N₁ N₂ P₁ P₂).d i j =
      ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).linearYonedaObj k
          (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).d i j ≫
        (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ j).hom := by
  have key := linearYonedaTensorProductComponentIso_inv_naturality k N₁ N₂ hN P₁ P₂ i j hij
  calc
    (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ i).hom ≫ (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.tensorLinearYonedaComplex k N₁ N₂ P₁ P₂).d i j
        = (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ i).hom ≫
            ((RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.tensorLinearYonedaComplex k N₁ N₂ P₁ P₂).d i j ≫
              (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ j).inv) ≫
            (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ j).hom := by simp
      _ = (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ i).hom ≫
            ((RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ i).inv ≫
              ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).linearYonedaObj k
                (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).d i j) ≫
            (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ j).hom := by rw [key]
      _ = ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).linearYonedaObj k
              (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).d i j ≫
            (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ j).hom := by
          rw [Category.assoc, Iso.hom_inv_id_assoc]

include hN in
/-- The linear Yoneda complex of the tensor product resolution is isomorphic to the tensor product of the two linear Yoneda complexes. -/
noncomputable def linearYonedaTensorProductComplexIso :
    (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂).linearYonedaObj k
        (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) ≅
      HomologicalComplex.tensorObj
        (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ i)
    (fun i j hij => linearYonedaTensorProductComponentIso_hom_naturality k N₁ N₂ hN P₁ P₂ i j hij)

include hN in
/-- Each component of the forward map of the complex comparison is the forward map of the corresponding componentwise isomorphism. -/
@[simp]
theorem linearYonedaTensorProductComplexIso_hom_f (i : ℕ) :
    (linearYonedaTensorProductComplexIso k N₁ N₂ hN P₁ P₂).hom.f i =
      (RepresentationTheory.HomologicalAlgebra.TensorProductProjectiveResolution.TensorProductProjectiveResolution.linearYonedaTotalIsoTensorObjComponent k N₁ N₂ hN P₁ P₂ i).hom := rfl

end RepresentationTheory.LinearYonedaTensorProductComparison
