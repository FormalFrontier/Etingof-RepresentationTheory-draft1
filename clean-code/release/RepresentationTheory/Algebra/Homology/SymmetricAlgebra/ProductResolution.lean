/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.SymmetricAlgebra.ProductTensorProduct
import RepresentationTheory.HomologicalAlgebra.TensorProduct
import RepresentationTheory.SymmetricAlgebra.ProjectiveResolution

/-!
# The Koszul resolution of a complementary symmetric algebra

For finite-dimensional vector spaces `U` and `W`, this file constructs the resolution in Problem
8.2.10(ii).  We tensor the Koszul resolution of the trivial `S(U)`-module with the degree-zero
resolution of the regular `S(W)`-module.  The external tensor product is a resolution over
`S(U) ⊗ S(W)`; restriction along `S(U ⊕ W) ≃ S(U) ⊗ S(W)` transports it to `S(U ⊕ W)`.

The resolved object `productSymmetricAlgebraModule k U W` has underlying vector space
`k ⊗[k] S(W)`, canonically equivalent to `S(W)`.  Its action is the requested one: the `U`
generators act through the augmentation of `S(U)`, hence by zero, while the `W` generators act
regularly on the second factor.
-/

open scoped TensorProduct
open CategoryTheory Limits HomologicalComplex

namespace RepresentationTheory.Algebra.Homology.SymmetricAlgebra.ProductResolution

universe u

variable (k U W : Type u) [Field k]
  [AddCommGroup U] [Module k U] [FiniteDimensional k U]
  [AddCommGroup W] [Module k W]

/-- A projective resolution of the regular module over the symmetric algebra on W. -/
noncomputable def regularModuleProjectiveResolution :
    ProjectiveResolution
      (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) :=
  ProjectiveResolution.self
    (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))

/-- An isomorphism from degree zero of the regular-module projective resolution to the regular module. -/
noncomputable def regularModuleProjectiveResolutionDegreeZeroIso :
    (regularModuleProjectiveResolution k W).complex.X 0 ≅
      ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W) :=
  HomologicalComplex.singleObjXIsoOfEq (ComplexShape.down ℕ) 0
    (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) 0 rfl

attribute [local instance] RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTower RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTowerAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductModule

/-- The morphism from a pair of projective-resolution degrees to degree n determined by the displayed complex-shape equality. -/
noncomputable def projectiveResolutionTensorTotalComponent
    {M : ModuleCat.{u} (SymmetricAlgebra k U)} (P : ProjectiveResolution M)
    (n i₁ i₂ : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = n) :
    ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
        (P.complex.X i₁)).obj ((regularModuleProjectiveResolution k W).complex.X i₂) ⟶
      ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
        (P.complex.X n)).obj
          (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) := by
  rcases i₂ with _ | i₂
  · have hi : i₁ = n := by simpa using h
    subst i₁
    exact ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
      (P.complex.X n)).map (regularModuleProjectiveResolutionDegreeZeroIso k W).hom
  · exact 0

omit [FiniteDimensional k U] in
/-- At bidegree (n, 0), the total component morphism is the image of the degree-zero component isomorphism. -/
@[simp]
theorem projectiveResolutionTensorTotalComponent_eq_mapDegreeZeroIso
    {M : ModuleCat.{u} (SymmetricAlgebra k U)} (P : ProjectiveResolution M) (n : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (n, 0) = n) :
    projectiveResolutionTensorTotalComponent k U W P n n 0 h =
      ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
        (P.complex.X n)).map (regularModuleProjectiveResolutionDegreeZeroIso k W).hom := by
  simp [projectiveResolutionTensorTotalComponent]

/-- An isomorphism between degree n of the displayed complex and the corresponding iterated functor value. -/
noncomputable def tensorProjectiveResolutionComponentIso
    {M : ModuleCat.{u} (SymmetricAlgebra k U)} (P : ProjectiveResolution M) (n : ℕ) :
    (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct (k := k) P (regularModuleProjectiveResolution k W)).X n ≅
      ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
        (P.complex.X n)).obj
          (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) where
  hom := HomologicalComplex.mapBifunctorDesc (j := n)
    (projectiveResolutionTensorTotalComponent k U W P n)
  inv := ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
      (P.complex.X n)).map (regularModuleProjectiveResolutionDegreeZeroIso k W).inv ≫
    HomologicalComplex.ιMapBifunctor P.complex (regularModuleProjectiveResolution k W).complex
      (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (SymmetricAlgebra k U) (SymmetricAlgebra k W))
      (ComplexShape.down ℕ) n 0 n (by simp)
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    rcases i₂ with _ | i₂
    · have hi : i₁ = n := by simpa using h
      subst i₁
      rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
        projectiveResolutionTensorTotalComponent_eq_mapDegreeZeroIso, ← Category.assoc, ← Functor.map_comp]
      simp
    · have hz : IsZero ((regularModuleProjectiveResolution k W).complex.X (i₂ + 1)) := by
        change IsZero (((ChainComplex.single₀ (ModuleCat.{u} (SymmetricAlgebra k W))).obj
          (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))).X (i₂ + 1))
        apply HomologicalComplex.isZero_single_obj_X
        simp
      exact (((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k (SymmetricAlgebra k U) (SymmetricAlgebra k W)).obj
        (P.complex.X i₁)).map_isZero hz).eq_of_src _ _
  inv_hom_id := by
    rw [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
      projectiveResolutionTensorTotalComponent_eq_mapDegreeZeroIso, ← Functor.map_comp]
    simp

/-- A projective resolution of the module obtained from the displayed pair of symmetric-algebra module objects. -/
noncomputable def tensorModuleProjectiveResolution :
    ProjectiveResolution
      (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
        (ModuleCat.of (SymmetricAlgebra k U) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k U))
        (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))) :=
  RepresentationTheory.HomologicalAlgebra.TensorProduct.tensorProduct
    (RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfFiniteDimensional k U)
    (regularModuleProjectiveResolution k W)

/-- A functor from modules over the tensor product of two symmetric algebras to modules over the symmetric algebra on the product. -/
noncomputable abbrev tensorAlgebraModulesToProductAlgebraModules :
    ModuleCat (SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W) ⥤
      ModuleCat (SymmetricAlgebra k (U × W)) :=
  ModuleCat.restrictScalars
    (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).toRingEquiv.toRingHom

/-- A module over the symmetric algebra on the product of U and W. -/
noncomputable def productSymmetricAlgebraModule : ModuleCat (SymmetricAlgebra k (U × W)) :=
  (tensorAlgebraModulesToProductAlgebraModules k U W).obj
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
      (ModuleCat.of (SymmetricAlgebra k U) (RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k U))
      (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)))

/-- A projective resolution of the specified module over the symmetric algebra on the product of U and W. -/
noncomputable def productSymmetricAlgebraProjectiveResolution :
    ProjectiveResolution (productSymmetricAlgebraModule k U W) :=
  (tensorAlgebraModulesToProductAlgebraModules k U W).mapProjectiveResolution
    (tensorModuleProjectiveResolution k U W)

/-- The complex of the specified product resolution equals the image of the displayed projective-resolution complex under the given functor. -/
@[simp]
theorem productResolutionComplex_eq_mapTensorResolution :
    (productSymmetricAlgebraProjectiveResolution k U W).complex =
      ((tensorAlgebraModulesToProductAlgebraModules k U W).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (tensorModuleProjectiveResolution k U W).complex :=
  rfl

/-- Each component of the specified product resolution is a projective object. -/
theorem productResolutionComponent_projective (i : ℕ) :
    Projective ((productSymmetricAlgebraProjectiveResolution k U W).complex.X i) :=
  (productSymmetricAlgebraProjectiveResolution k U W).projective i

/-- The augmentation of the specified product projective resolution is a quasi-isomorphism. -/
theorem productResolution_augmentation_quasiIso :
    QuasiIso (productSymmetricAlgebraProjectiveResolution k U W).π :=
  (productSymmetricAlgebraProjectiveResolution k U W).quasiIso

/-! ## The literal free terms -/

/-- A degree-indexed module over the tensor product of the symmetric algebras on U and W. -/
noncomputable abbrev tensorResolutionTerm (i : ℕ) :=
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
    (ModuleCat.of (SymmetricAlgebra k U) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i))
    (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))

/-- A degree-indexed type associated with a field and two modules over it. -/
abbrev productResolutionTerm (i : ℕ) :=
  SymmetricAlgebra k (U × W) ⊗[k] (⋀[k]^i U)

/-- A k-linear equivalence from the carrier obtained by applying the displayed functor to the degree-i module back to that module. -/
noncomputable def restrictScalarsTensorResolutionTermLinearEquiv (i : ℕ) :
    (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsLeft k (SymmetricAlgebra k U)).obj
        (ModuleCat.of (SymmetricAlgebra k U) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i)) ≃ₗ[k]
      RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by simp

/-- A k-linear equivalence from the carrier obtained by applying the displayed functor to the regular module back to its symmetric algebra. -/
noncomputable def restrictScalarsRegularModuleLinearEquiv :
    (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsRight k (SymmetricAlgebra k W)).obj
        (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) ≃ₗ[k]
      SymmetricAlgebra k W where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A k-linear equivalence from the carrier of the degree-i module to the tensor product of the displayed degree-i space with the symmetric algebra on W. -/
noncomputable def tensorResolutionTermLinearEquiv (i : ℕ) :
    letI : Module k (tensorResolutionTerm k U W i) :=
      Module.compHom _ (algebraMap k
        (SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W))
    tensorResolutionTerm k U W i ≃ₗ[k]
      (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i ⊗[k] SymmetricAlgebra k W) :=
  RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsTensorProductLinearEquiv
      (ModuleCat.of (SymmetricAlgebra k U) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i))
      (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) ≪≫ₗ
    TensorProduct.congr (restrictScalarsTensorResolutionTermLinearEquiv k U i)
      (restrictScalarsRegularModuleLinearEquiv k W)

/-- A k-linear equivalence between the displayed tensor products involving degree i and the i-th exterior power of U. -/
noncomputable def tensorExteriorPowerReassociation (i : ℕ) :
    (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i ⊗[k] SymmetricAlgebra k W) ≃ₗ[k]
      ((SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W) ⊗[k] (⋀[k]^i U)) :=
  TensorProduct.assoc k (SymmetricAlgebra k U) (⋀[k]^i U)
      (SymmetricAlgebra k W) ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl k (SymmetricAlgebra k U))
      (TensorProduct.comm k (⋀[k]^i U) (SymmetricAlgebra k W)) ≪≫ₗ
    (TensorProduct.assoc k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
      (⋀[k]^i U)).symm

/-- A k-linear equivalence from the carrier of the degree-i tensor-product module to the displayed product-resolution term. -/
noncomputable def productResolutionTermLinearEquiv (i : ℕ) :
    letI : Module k (tensorResolutionTerm k U W i) :=
      Module.compHom _ (algebraMap k
        (SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W))
    tensorResolutionTerm k U W i ≃ₗ[k] productResolutionTerm k U W i :=
  tensorResolutionTermLinearEquiv k U W i ≪≫ₗ
    tensorExteriorPowerReassociation k U W i ≪≫ₗ
    TensorProduct.congr
      (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm.toLinearEquiv
      (LinearEquiv.refl k (⋀[k]^i U))

/-- The element of the degree-i module determined by an element of the first factor and an element of the symmetric algebra on W. -/
noncomputable def tensorResolutionElement (i : ℕ) (x : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i)
    (t : SymmetricAlgebra k W) : tensorResolutionTerm k U W i :=
  @TensorProduct.tmul k _
    (ModuleCat.of (SymmetricAlgebra k U) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i))
    (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) _ _
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier k (SymmetricAlgebra k U)
      (ModuleCat.of (SymmetricAlgebra k U) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i)))
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux k (SymmetricAlgebra k W)
      (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W))) x t

omit [FiniteDimensional k U] in
/-- The degree-i element construction sends zero in its first argument to zero. -/
@[simp]
theorem tensorResolutionElement_zero_left (i : ℕ) (t : SymmetricAlgebra k W) :
    tensorResolutionElement k U W i 0 t = 0 :=
  TensorProduct.zero_tmul
    (ModuleCat.of (SymmetricAlgebra k U) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i)) t

omit [FiniteDimensional k U] in
/-- The degree-i element construction preserves addition in its first argument. -/
theorem tensorResolutionElement_add_left (i : ℕ) (x y : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i)
    (t : SymmetricAlgebra k W) :
    tensorResolutionElement k U W i (x + y) t =
      tensorResolutionElement k U W i x t + tensorResolutionElement k U W i y t :=
  TensorProduct.add_tmul _ _ _

omit [FiniteDimensional k U] in
/-- The term equivalence sends the displayed element built from a pure tensor to the corresponding reassociated pure tensor. -/
@[simp]
theorem productResolutionTermLinearEquiv_apply_tmul (i : ℕ)
    (s : SymmetricAlgebra k U) (x : ⋀[k]^i U) (t : SymmetricAlgebra k W) :
    productResolutionTermLinearEquiv k U W i
      (tensorResolutionElement k U W i (s ⊗ₜ[k] x) t) =
        (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm (s ⊗ₜ[k] t) ⊗ₜ[k] x := by
  rfl

/-- The ring homomorphisms underlying the inverse algebra equivalence and the algebra equivalence form an inverse pair. -/
noncomputable local instance symmetricProductAlgEquiv_symm_toRingHom_invPair :
    RingHomInvPair
      (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm.toRingEquiv.toRingHom
      (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).toRingEquiv.toRingHom where
  comp_eq := by
    apply DFunLike.ext _ _
    exact (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).toRingEquiv.apply_symm_apply
  comp_eq₂ := by
    apply DFunLike.ext _ _
    exact (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).toRingEquiv.symm_apply_apply

/-- The ring homomorphisms underlying the algebra equivalence and its inverse form an inverse pair. -/
noncomputable local instance symmetricProductAlgEquiv_toRingHom_invPair :
    RingHomInvPair
      (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).toRingEquiv.toRingHom
      (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm.toRingEquiv.toRingHom where
  comp_eq := by
    apply DFunLike.ext _ _
    exact (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).toRingEquiv.symm_apply_apply
  comp_eq₂ := by
    apply DFunLike.ext _ _
    exact (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).toRingEquiv.apply_symm_apply

omit [FiniteDimensional k U] in
/-- A pure tensor acts on a constructed degree-i element by acting on its two inputs separately. -/
theorem tensorResolutionElement_smul_tmul (i : ℕ)
    (a : SymmetricAlgebra k U) (b : SymmetricAlgebra k W)
    (q : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i) (t : SymmetricAlgebra k W) :
    (tensorResolutionTerm k U W i).isModule.toSMul.smul (a ⊗ₜ[k] b)
        (tensorResolutionElement k U W i q t) =
      tensorResolutionElement k U W i (a • q) (b * t) :=
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.smul_tmul k (SymmetricAlgebra k U) (SymmetricAlgebra k W)
    (ModuleCat.of (SymmetricAlgebra k U) (RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i))
    (ModuleCat.of (SymmetricAlgebra k W) (SymmetricAlgebra k W)) a b q t

omit [FiniteDimensional k U] in
/-- The term equivalence transports the action of a pure tensor to scalar multiplication through the inverse algebra equivalence. -/
theorem productResolutionTermLinearEquiv_map_smul_tmul (i : ℕ)
    (a : SymmetricAlgebra k U) (b : SymmetricAlgebra k W)
    (q : RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k U i) (t : SymmetricAlgebra k W) :
    productResolutionTermLinearEquiv k U W i
        (tensorResolutionElement k U W i (a • q) (b * t)) =
      (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm (a ⊗ₜ[k] b) •
        productResolutionTermLinearEquiv k U W i
          (tensorResolutionElement k U W i q t) := by
  induction q using TensorProduct.induction_on with
  | zero =>
      rw [smul_zero, tensorResolutionElement_zero_left, tensorResolutionElement_zero_left]
      simp only [map_zero, smul_zero]
  | add x y hx hy =>
      simp only [smul_add]
      change productResolutionTermLinearEquiv k U W i
          (tensorResolutionElement k U W i (a • x + a • y) (b * t)) = _
      rw [tensorResolutionElement_add_left, tensorResolutionElement_add_left, map_add, map_add, hx, hy, smul_add]
  | tmul s x =>
      rw [TensorProduct.smul_tmul']
      rw [productResolutionTermLinearEquiv_apply_tmul,
        productResolutionTermLinearEquiv_apply_tmul]
      rw [TensorProduct.smul_tmul']
      congr 1
      change (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm
          ((a * s) ⊗ₜ[k] (b * t)) =
        (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm (a ⊗ₜ[k] b) *
          (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm (s ⊗ₜ[k] t)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul]

omit [FiniteDimensional k U] in
/-- The term equivalence transports scalar multiplication through the inverse algebra equivalence. -/
theorem productResolutionTermLinearEquiv_map_smul (i : ℕ)
    (r : SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W)
    (z : tensorResolutionTerm k U W i) :
    productResolutionTermLinearEquiv k U W i
        ((tensorResolutionTerm k U W i).isModule.toSMul.smul r z) =
      (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm r •
        productResolutionTermLinearEquiv k U W i z := by
  induction r using TensorProduct.induction_on with
  | zero =>
      calc
        productResolutionTermLinearEquiv k U W i
            ((tensorResolutionTerm k U W i).isModule.toSMul.smul 0 z) =
          productResolutionTermLinearEquiv k U W i 0 :=
            congrArg (productResolutionTermLinearEquiv k U W i)
              ((tensorResolutionTerm k U W i).isModule.zero_smul z)
        _ = 0 := map_zero _
        _ = _ := (zero_smul _ _).symm
  | add r t hr ht =>
      calc
        productResolutionTermLinearEquiv k U W i
            ((tensorResolutionTerm k U W i).isModule.toSMul.smul (r + t) z) =
          productResolutionTermLinearEquiv k U W i
            ((tensorResolutionTerm k U W i).isModule.toSMul.smul r z +
              (tensorResolutionTerm k U W i).isModule.toSMul.smul t z) :=
                congrArg (productResolutionTermLinearEquiv k U W i)
                  ((tensorResolutionTerm k U W i).isModule.add_smul r t z)
        _ = productResolutionTermLinearEquiv k U W i
              ((tensorResolutionTerm k U W i).isModule.toSMul.smul r z) +
            productResolutionTermLinearEquiv k U W i
              ((tensorResolutionTerm k U W i).isModule.toSMul.smul t z) := map_add _ _ _
        _ = _ := by rw [hr, ht, map_add, add_smul]
  | tmul a b =>
      induction z using TensorProduct.induction_on with
      | zero =>
          calc
            productResolutionTermLinearEquiv k U W i
                ((tensorResolutionTerm k U W i).isModule.toSMul.smul
                  (a ⊗ₜ[k] b) 0) =
              productResolutionTermLinearEquiv k U W i 0 :=
                congrArg (productResolutionTermLinearEquiv k U W i)
                  ((tensorResolutionTerm k U W i).isModule.smul_zero (a ⊗ₜ[k] b))
            _ = 0 := map_zero _
            _ = _ := (smul_zero _).symm
      | add x y hx hy =>
          calc
            productResolutionTermLinearEquiv k U W i
                ((tensorResolutionTerm k U W i).isModule.toSMul.smul
                  (a ⊗ₜ[k] b) (x + y)) =
              productResolutionTermLinearEquiv k U W i
                ((tensorResolutionTerm k U W i).isModule.toSMul.smul
                    (a ⊗ₜ[k] b) x +
                  (tensorResolutionTerm k U W i).isModule.toSMul.smul
                    (a ⊗ₜ[k] b) y) :=
                      congrArg (productResolutionTermLinearEquiv k U W i)
                        ((tensorResolutionTerm k U W i).isModule.smul_add
                          (a ⊗ₜ[k] b) x y)
            _ = productResolutionTermLinearEquiv k U W i
                  ((tensorResolutionTerm k U W i).isModule.toSMul.smul
                    (a ⊗ₜ[k] b) x) +
                productResolutionTermLinearEquiv k U W i
                  ((tensorResolutionTerm k U W i).isModule.toSMul.smul
                    (a ⊗ₜ[k] b) y) := map_add _ _ _
            _ = _ := by
              rw [hx, hy]
              calc
                (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm (a ⊗ₜ[k] b) •
                      productResolutionTermLinearEquiv k U W i
                        (show tensorResolutionTerm k U W i from x) +
                    (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm (a ⊗ₜ[k] b) •
                      productResolutionTermLinearEquiv k U W i
                        (show tensorResolutionTerm k U W i from y) =
                  (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm (a ⊗ₜ[k] b) •
                    (productResolutionTermLinearEquiv k U W i
                        (show tensorResolutionTerm k U W i from x) +
                      productResolutionTermLinearEquiv k U W i
                        (show tensorResolutionTerm k U W i from y)) :=
                          (smul_add _ _ _).symm
                _ = _ := congrArg
                  ((RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm (a ⊗ₜ[k] b) • ·)
                  (map_add (productResolutionTermLinearEquiv k U W i)
                    (show tensorResolutionTerm k U W i from x)
                    (show tensorResolutionTerm k U W i from y)).symm
      | tmul q t =>
          change productResolutionTermLinearEquiv k U W i
              ((tensorResolutionTerm k U W i).isModule.toSMul.smul
                (a ⊗ₜ[k] b) (tensorResolutionElement k U W i q t)) =
            (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm (a ⊗ₜ[k] b) •
              productResolutionTermLinearEquiv k U W i (tensorResolutionElement k U W i q t)
          rw [tensorResolutionElement_smul_tmul,
            productResolutionTermLinearEquiv_map_smul_tmul]

/-- A semilinear equivalence from the degree-i tensor-product module carrier to the displayed product-resolution term, using the inverse algebra equivalence. -/
noncomputable def productResolutionTermSemilinearEquiv (i : ℕ) :
    @LinearEquiv
      (SymmetricAlgebra k U ⊗[k] SymmetricAlgebra k W)
      (SymmetricAlgebra k (U × W)) _ _
      (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).symm.toRingEquiv.toRingHom
      (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W).toRingEquiv.toRingHom
      (by infer_instance) (by infer_instance)
      (tensorResolutionTerm k U W i) (productResolutionTerm k U W i)
      _ _ (tensorResolutionTerm k U W i).isModule inferInstance where
  toFun := productResolutionTermLinearEquiv k U W i
  invFun := (productResolutionTermLinearEquiv k U W i).symm
  left_inv := (productResolutionTermLinearEquiv k U W i).left_inv
  right_inv := (productResolutionTermLinearEquiv k U W i).right_inv
  map_add' := (productResolutionTermLinearEquiv k U W i).map_add
  map_smul' := productResolutionTermLinearEquiv_map_smul k U W i

/-- An isomorphism between the functorial scalar transport of the degree-i module and the displayed target module. -/
noncomputable def scalarTransportTermIso (i : ℕ) :
    (tensorAlgebraModulesToProductAlgebraModules k U W).obj (tensorResolutionTerm k U W i) ≅
      ModuleCat.of (SymmetricAlgebra k (U × W)) (productResolutionTerm k U W i) := by
  let X := (tensorAlgebraModulesToProductAlgebraModules k U W).obj (tensorResolutionTerm k U W i)
  change X ≅ _
  letI : Module (SymmetricAlgebra k (U × W)) X := X.isModule
  let eₛ := productResolutionTermSemilinearEquiv k U W i
  let e : X ≃ₗ[SymmetricAlgebra k (U × W)] productResolutionTerm k U W i :=
    { toFun := eₛ
      invFun := eₛ.symm
      left_inv := eₛ.left_inv
      right_inv := eₛ.right_inv
      map_add' := eₛ.map_add
      map_smul' := by
        intro r z
        change productResolutionTermLinearEquiv k U W i
            ((tensorResolutionTerm k U W i).isModule.toSMul.smul
              (RepresentationTheory.SymmetricAlgebra.ProductTensorProduct.SymmetricAlgebra.prodAlgEquivTensorProduct k U W r)
              (show tensorResolutionTerm k U W i from z)) =
          r • productResolutionTermLinearEquiv k U W i
            (show tensorResolutionTerm k U W i from z)
        rw [productResolutionTermLinearEquiv_map_smul]
        simp }
  exact e.toModuleIso

/-- An isomorphism from degree i of the specified projective resolution to the corresponding displayed module. -/
noncomputable def productResolutionComponentIso (i : ℕ) :
    (productSymmetricAlgebraProjectiveResolution k U W).complex.X i ≅
      ModuleCat.of (SymmetricAlgebra k (U × W)) (productResolutionTerm k U W i) :=
  (tensorAlgebraModulesToProductAlgebraModules k U W).mapIso
      (tensorProjectiveResolutionComponentIso k U W (RepresentationTheory.SymmetricAlgebra.ProjectiveResolution.projectiveResolutionOfFiniteDimensional k U) i) ≪≫
    scalarTransportTermIso k U W i

/-- Each component carrier of the specified product resolution is free over the symmetric algebra on the product. -/
theorem productResolutionComponent_free (i : ℕ) :
    Module.Free (SymmetricAlgebra k (U × W))
      ((productSymmetricAlgebraProjectiveResolution k U W).complex.X i) := by
  letI : Module.Free k (⋀[k]^i U) := inferInstance
  letI : Module.Free (SymmetricAlgebra k (U × W)) (productResolutionTerm k U W i) :=
    inferInstance
  exact Module.Free.of_equiv (productResolutionComponentIso k U W i).symm.toLinearEquiv

end RepresentationTheory.Algebra.Homology.SymmetricAlgebra.ProductResolution
